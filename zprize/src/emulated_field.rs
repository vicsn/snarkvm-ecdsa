use std::borrow::Borrow;
use std::ops::{Add, BitAnd, BitOr, Deref, Div, Mul, Not, Sub};
use snarkvm_circuit_environment::{prelude::PrimeField, Eject, Environment, Inject, Mode, Compare, Zero, Equal, Assignment, Circuit, One, ToBits};
use snarkvm_console_network::{prelude::Itertools, SizeInBytes, Testnet3};
use snarkvm_utilities::biginteger::BigInteger;

use snarkvm_circuit::{Boolean, Circuit as Env, Field};
use snarkvm_utilities::{ToBytes, FromBytes};

use snarkvm_circuit_environment::{FromBits};

use num_bigint::*;
use snarkvm_circuit_environment::Mode::{Constant, Private};
use std::str::FromStr;
use ecdsa::elliptic_curve::generic_array::typenum::private::IsLessOrEqualPrivate;
use k256::elliptic_curve::weierstrass::add;
use snarkvm_circuit::prelude::num_traits::{Num, FromPrimitive, ToPrimitive};

use log;
use log::warn;
use num_integer::*;
use rand::random;
use sha3::digest::typenum::private::IsGreaterOrEqualPrivate;
use snarkvm_circuit::environment::FromBoolean;
use snarkvm_circuit::prelude::{Double, NumOne};
use snarkvm_console::types::boolean::Ternary;

use crate::utils;

//
// Aliases
// =======
//

type F = Field<Env>;


/*
    The main idea of emulated filed is from https://hackmd.io/@arielg/B13JoihA8.

    The Fp field is emulated using BLS12_377's Fr field.

    p = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F //115792089237316195423570985008687907853269984665640564039457584007908834671663
    n = 0x12ab655e9a2ca55660b44d1e5c37b00159aa76fed00000010a11800000000001 //8444461749428370424248824938781546531375899335154063827935233455917409239041
    p'= 0xff00000000000000000000000000000000000000000000000000000001000003d1 //29526982755515629833010601177215416502583846089738343830061683922017852353151953
    t = 261 (minimum 260, maximum (252-3)/2*3 = 373)
    b = 261/3 = 87

    Those parameters is set to make sure:
    p*p + p < 2**t * n

    That's to say, one Fp field is composed by 3 limbs, which is 87 bits.

    Multiplication algorithm:
    a*b = q*p + r

    1. Compute witness q and r such that ab-qp-r=0
    2. Apply range constraints on the limbs of q,r such that they are all < 2**b
    3. Apply multiplication gates and addition gates to evaluate t he following intermediate products mod 2**t
       *) t_0 = a_0b_0 + q_0p'_0 - bits [0, 2b+1]
       *) t_1 = a_0b_1 + a_1b_0 + q_0p'_1 + q_1p'_0 - bits [b, 3b+2]
       *) t_2 = a_0b_2 + a_1b_1 + a_2_b0 + q_0p'_2 + q_1p'_1 + q_2p'_0 [2b, 4b+3]
    4. Compute u_0 = t_0 + 2**b t_1 - r_0 - 2**b*r_1 and u_1 = t_2 - r_2
       Both u_0 and u_1 should be in the range [0, 3b] (plus some overflow bits). Moreover, the first 2b bits of
       u_0 should be zero because we have subtracted from them the low 2b-bits of the remainder term using r_0, r_1.
       Same holds for the first b bits of u_0/(2**2b) + u_1.
    5. Compute v_0 such that u_0 = v_0 * 2**2b
    6. Validate v_0 is in the range [0, b]
    7. Compute v_1 such that u_1 + v_0 = v_1 * 2**2b
    8. Validate v_1 is in the range [0, b] plus some overflow bits
    9. Finally, check also that ab-pq-r=0 (mod n)
    10. Range constrain q so that q*p + r < 2**t * n.
 */

#[derive(Clone, Debug, PartialEq)]
pub struct FieldParameters {
    pub LIMBS_NUM: usize,
    pub LIMB_BITS_NUM: usize,
    pub LIMB_BYTES_NUM: usize,

    pub FN: &'static [u8], //n
    pub FP: &'static [u8], //p
    pub FPNt: &'static [u8], // -p % 2**t
}

pub const secp256k1_Fp: &'static FieldParameters = &FieldParameters {
    LIMBS_NUM: 3,
    LIMB_BITS_NUM: 88,
    LIMB_BYTES_NUM: 11,

    FN: b"12ab655e9a2ca55660b44d1e5c37b00159aa76fed00000010a1180000000001",
    FP: b"FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F",
    FPNt: b"FF00000000000000000000000000000000000000000000000000000001000003D1",
};

pub const secp256k1_Fr: &'static FieldParameters = &FieldParameters {
    LIMBS_NUM: 3,
    LIMB_BITS_NUM: 88,
    LIMB_BYTES_NUM: 11,

    FN: b"12ab655e9a2ca55660b44d1e5c37b00159aa76fed00000010a1180000000001",
    FP: b"FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141",
    FPNt: b"ff000000000000000000000000000000014551231950b75fc4402da1732fc9bebf",
};

enum FieldType {
    secp256k1_Fp,
    secp256k1_Fr,
}

#[derive(Clone, Debug)]
pub struct EmulatedField {
    pub limb_size: usize,      //in bytes
    pub limbs: Vec<F>,
    pub overflow: bool, //whether limb may be larger than limb_size by one bit
    pub value: Option<BigUint>,
    pub parameters: &'static FieldParameters,
}

impl EmulatedField {
    // init to be zero
    pub fn zero(p: &'static FieldParameters) -> EmulatedField {
        let mut f = Vec::with_capacity(p.LIMBS_NUM);
        for i in 0..p.LIMBS_NUM {
            f.push(F::zero());
        }

        EmulatedField {
            limb_size: p.LIMB_BYTES_NUM,
            limbs: f,
            value: Some(BigUint::from_u8(0).unwrap()),
            overflow: false,
            parameters: p,
        }
    }

    // init to be one
    pub fn one(p: &'static FieldParameters) -> EmulatedField {
        let mut f = Vec::with_capacity(p.LIMBS_NUM);
        f.push(F::one());
        for i in 1..p.LIMBS_NUM {
            f.push(F::zero());
        }

        EmulatedField {
            limb_size: p.LIMB_BYTES_NUM,
            limbs: f,
            value: Some(BigUint::from_u8(1).unwrap()),
            overflow: false,
            parameters: p,
        }
    }

    pub fn is_zero(&self) -> Boolean<Circuit> {
        let result = self.limbs.iter().fold(Boolean::constant(true), |is_zero, limb| {
            log::trace!("is_zero: {:?}, limb: {:?}", is_zero, limb);
            is_zero.bitand(limb.is_zero())
        });

        result
    }

    pub fn is_equal(&self, other: &EmulatedField) -> Boolean<Circuit> {
        let result = self.limbs.iter().zip(other.limbs.iter()).fold(Boolean::constant(true), |is_equal, (limb_a, limb_b)| {
            is_equal.bitand(limb_a.is_equal(limb_b))
        });

        result
    }

    pub fn ternary(condition: &Boolean<Circuit>, a: &EmulatedField, b: &EmulatedField) -> EmulatedField {
        assert_eq!(a.parameters, b.parameters);
        assert_eq!(a.limb_size, b.limb_size);

        let mut limbs = Vec::with_capacity(a.parameters.LIMBS_NUM);
        for i in 0..a.parameters.LIMBS_NUM {
            let limb = F::ternary(condition, &a.limbs[i].clone(), &b.limbs[i].clone());
            limbs.push(limb);
        }

        let mut value = b.value.clone();
        if condition.eject_value() {
           value = a.value.clone();
        }

        EmulatedField {
            limb_size: a.limb_size,
            limbs: limbs,
            value: value,
            overflow: false,
            parameters: a.parameters,
        }
    }

    pub fn enforce_eq(a: &EmulatedField, b: &EmulatedField) {
        for i in 0..a.limbs.len() {
            Env::assert_eq(a.limbs[i].clone(), b.limbs[i].clone());
        }
    }

    /* consider overflow flag */
    fn limb_size(&self, other: &EmulatedField) -> usize {
        log::trace!("limb size: {:?} {:?}", self.limb_size, other.limb_size);

        assert!(self.limb_size == other.limb_size);

        let mut ls = self.limb_size;
        if self.overflow || other.overflow {
            ls = ls+1;
        }

        ls
    }

    /* assume data len is 32 */
    pub fn from_F(data: &[F], p: &'static FieldParameters) -> EmulatedField {
        assert_eq!(data.len(), 32);
        let ls = p.LIMB_BYTES_NUM;
        let mut f = Vec::with_capacity(4);

        let mut bytes = Vec::with_capacity(data.len());
        for i in 0..data.len() {
            bytes.push(data[i].eject_value().to_bytes_le().unwrap()[0]);
        }
        let v_sum = BigUint::from_bytes_le(&bytes);

        for j in 0..3 {
            let mut fsum = Env::zero();
            for i in 0..ls {
                if j*ls+i < 32 {
                    fsum += &data[j * ls + i].linear_combination * utils::COEFFS[8*i].deref();
                }
            }
            f.push(F::from(fsum));
        }

        EmulatedField {
            limb_size: ls,
            limbs: f,
            value: Some(v_sum),
            overflow: false,
            parameters: p,
        }
    }

    pub fn from_BigUint(data: &BigUint, ls: usize, mode: Mode, p: &'static FieldParameters) -> EmulatedField {
        let limb_max = BigUint::from_u128(2u128.pow(p.LIMB_BITS_NUM as u32)-1).unwrap();
        let data0 = data & &limb_max;
        let data1 = (data >> p.LIMB_BITS_NUM) & &limb_max;
        let data2 = (data >> (p.LIMB_BITS_NUM*2)) & &limb_max;
        log::trace!("data: {:?} {:?} {:?} {:?}", &data, &data0, &data1, &data2);

        let mut limbs = Vec::with_capacity(3);
        if mode == Constant {
            limbs.push(F::from(Env::one() * snarkvm_console::types::Field::<Testnet3>::from_u128(data0.to_u128().unwrap()).deref()));
            limbs.push(F::from(Env::one() * snarkvm_console::types::Field::<Testnet3>::from_u128(data1.to_u128().unwrap()).deref()));
            limbs.push(F::from(Env::one() * snarkvm_console::types::Field::<Testnet3>::from_u128(data2.to_u128().unwrap()).deref()));
        } else {
            limbs.push(F::new(mode, snarkvm_console::types::Field::from_u128(data0.to_u128().unwrap())));
            limbs.push(F::new(mode, snarkvm_console::types::Field::from_u128(data1.to_u128().unwrap())));
            limbs.push(F::new(mode, snarkvm_console::types::Field::from_u128(data2.to_u128().unwrap())));
        }

        EmulatedField {
            limb_size: ls,
            limbs: limbs,
            value: Some(data.clone()),
            overflow: false,
            parameters: p,
        }
    }

    pub fn is_less_than_constant(data: &EmulatedField, other: &EmulatedField) -> Boolean<Circuit>{
        log::trace!("is less than constant: {:?}, {:?}", data.value.clone().unwrap(), other.value.clone().unwrap());
        let ls = EmulatedField::limb_size(data, other);
        log::trace!("ls: {:?}", ls);

        let mut isless = Vec::with_capacity(data.parameters.LIMBS_NUM);
        let mut isequal = Vec::with_capacity(data.parameters.LIMBS_NUM);
        for i in 0..data.parameters.LIMBS_NUM {
            let limb = &data.limbs[i];
            isless.push(utils::is_less_than_constant(&limb, &other.limbs[i], ls));
            let iseq = limb.is_equal(&other.limbs[i]);
            isequal.push(iseq);
        }

        let result = isequal
            .iter()
            .zip_eq(isless)
            .fold(Boolean::constant(false), |is_less_than, (e, l)| {
                log::trace!("e: {:?}, l: {:?}", e.eject_value(), l.eject_value());
                l.bitor(e.bitand(is_less_than))
            });

        log::trace!("less result: {:?}", result.eject_value());

        result
    }

    pub fn is_less_than(data: &EmulatedField, other: &EmulatedField) -> Boolean<Circuit>{
        log::trace!("is less than: {:?}, {:?}", data.value.clone().unwrap(), other.value.clone().unwrap());
        let ls = EmulatedField::limb_size(data, other);
        log::trace!("ls: {:?}", ls);

        let mut isless = Vec::with_capacity(data.parameters.LIMBS_NUM);
        let mut isequal = Vec::with_capacity(data.parameters.LIMBS_NUM);
        for i in 0..data.parameters.LIMBS_NUM {
            let limb = &data.limbs[i];
            isless.push(utils::is_less_than(&limb, &other.limbs[i], ls));
            let iseq = limb.is_equal(&other.limbs[i]);
            isequal.push(iseq);
        }

        let result = isequal
            .iter()
            .zip_eq(isless)
            .fold(Boolean::constant(false), |is_less_than, (e, l)| {
                log::trace!("e: {:?}, l: {:?}", e.eject_value(), l.eject_value());
                l.bitor(e.bitand(is_less_than))
            });

        log::trace!("less result: {:?}", result.eject_value());

        result
    }

    pub fn mul(&self, other: &EmulatedField) -> EmulatedField {
        let p_value = BigUint::parse_bytes(self.parameters.FP, 16).unwrap();
        let np_value = BigUint::parse_bytes(self.parameters.FPNt, 16).unwrap();

        let pF = EmulatedField::from_BigUint(&p_value, self.parameters.LIMB_BYTES_NUM, Constant, self.parameters);
        let npF = EmulatedField::from_BigUint(&np_value, self.parameters.LIMB_BYTES_NUM, Constant, self.parameters);
        let p = &pF.limbs;
        let np = &npF.limbs;

        /* 1. Compute witness q and r such that ab-qp-r = 0 */
        assert!(self.value != None);
        assert!(other.value != None);
        let a = &self.limbs;
        let b = &other.limbs;
        let a_value = self.value.clone().unwrap();
        let b_value = other.value.clone().unwrap();
        let ab_value = &a_value * &b_value;
        let q = &ab_value / &p_value;
        let r = &ab_value % &p_value;
        log::debug!("mul - a: {:?} b: {:?}", &a_value, &b_value);
        log::debug!("q: {:?}, r: {:?}", &q, &r);

        /* 2. Apply range constraints on the limbs of q,r such that they are all < 2**b */
        let EFq = EmulatedField::from_BigUint(&q, self.parameters.LIMB_BYTES_NUM, Private, self.parameters);
        let EFr = EmulatedField::from_BigUint(&r, self.parameters.LIMB_BYTES_NUM, Private, self.parameters);
        let q = &EFq.limbs;
        let r = &EFr.limbs;

        log::debug!("a: {:?} {:?} {:?}", a[0].eject_value(),a[1].eject_value(),a[2].eject_value());
        log::debug!("b: {:?} {:?} {:?}", b[0].eject_value(),b[1].eject_value(),b[2].eject_value());
        log::debug!("q: {:?} {:?} {:?}", q[0].eject_value(),q[1].eject_value(),q[2].eject_value());
        log::debug!("r: {:?} {:?} {:?}", r[0].eject_value(),r[1].eject_value(),r[2].eject_value());

        let qlp = EmulatedField::is_less_than_constant(&EFq, &pF);
        let rlp = EmulatedField::is_less_than_constant(&EFr, &pF);
        Env::assert_eq(&qlp, &F::one());
        Env::assert_eq(&rlp, &F::one());

        /*
        3. Apply multiplication gates and addition gates to evaluate t he following intermediate products mod 2**t
            *) t_0 = a_0b_0 + q_0p'_0 - bits [0, 2b+1]
            *) t_1 = a_0b_1 + a_1b_0 + q_0p'_1 + q_1p'_0 - bits [b, 3b+2]
            *) t_2 = a_0b_2 + a_1b_1 + a_2_b0 + q_0p'_2 + q_1p'_1 + q_2p'_0 [2b, 4b+3]
        */
        let a_0 = a.get(0).unwrap();
        let a_1 = a.get(1).unwrap();
        let a_2 = a.get(2).unwrap();

        let b_0 = b.get(0).unwrap();
        let b_1 = b.get(1).unwrap();
        let b_2 = b.get(2).unwrap();

        let np_0 = np.get(0).unwrap();
        let np_1 = np.get(1).unwrap();
        let np_2 = np.get(2).unwrap();

        let q_0 = q.get(0).unwrap();
        let q_1 = q.get(1).unwrap();
        let q_2 = q.get(2).unwrap();

        let t0 = a_0 * b_0 + q_0 * np_0;
        let t1 = a_0 * b_1 + a_1 * b_0 + q_0 * np_1 + q_1 * np_0;
        let t2 = a_0 * b_2 + a_1 * b_1 + a_2 * b_0 + q_0 * np_2 + q_1 * np_1 + q_2 * np_0;

        /*
        4. Compute u_0 = t_0 + 2**b t_1 - r_0 - 2**b*r_1 and u_1 = t_2 - r_2
        Both u_0 and u_1 should be in the range [0, 3b] (plus some overflow bits). Moreover, the first 2b bits of
        u_0 should be zero because we have subtracted from them the low 2b-bits of the remainder term using r_0, r_1.
            Same holds for the first b bits of u_0/(2**2b) + u_1.
        */
        let limb = F::new(Constant, snarkvm_console::types::Field::from_u128(2u128.pow((self.parameters.LIMB_BITS_NUM) as u32)));

        let (t0_l, t0_h) = utils::splitField(&t0.clone(), self.parameters.LIMB_BYTES_NUM, self.parameters.LIMB_BYTES_NUM+1);

        let r_0 = r.get(0).unwrap();
        let r_1 = r.get(1).unwrap();
        let r_2 = r.get(2).unwrap();
        //low b-bits are zero
        Env::assert_eq(&t0_l, r_0);

        let u0b = &t0_h + &t1 - r_1;

        //2nd low b-bits are zero
        let (u0b_0, v0) = utils::splitField(&u0b.clone(), self.parameters.LIMB_BYTES_NUM, self.parameters.LIMB_BYTES_NUM+1);
        log::trace!("4 done: {:?} {:?}", &t0_l.eject_value(), &u0b_0.eject_value());
        Env::assert_eq(&u0b_0, &F::zero());

        //5. Compute v_0 such that u_0 = v_0 * 2**2b
        //6. Validate v_0 is in the range [0, b]
        let v0c = utils::is_less_than_limb(&v0, self.parameters.LIMB_BYTES_NUM+1, 2);
        log::trace!("6 done: {:?} {:?}", &v0.eject_value(), &v0c.eject_value());
        //assert!(v0c.clone().eject_value() == true);
        Env::assert_eq(&v0c, &F::one());

        //7. Compute v_1 such that u_1 + v_0 = v_1 * 2**b
        //8. Validate v_1 is in the range [0, b] plus some overflow bits
        let u1pv0 = &t2 + &v0 - r_2;
        let (u1pv0_b, v1) = utils::splitField(&u1pv0, self.parameters.LIMB_BYTES_NUM, self.parameters.LIMB_BYTES_NUM+1);
        //assert!(u1pv0_b.clone().eject_value() == snarkvm_console::types::Field::from_u8(0));
        Env::assert_eq(&u1pv0_b, &F::zero());
        let v1c = utils::is_less_than_limb(&v1, self.parameters.LIMB_BYTES_NUM+1, 3);
        //assert!(v1c.clone().eject_value() == true);
        Env::assert_eq(&v1c, &F::one());

        //9. Finally, check also that ab-pq-r=0 (mod n)
        let ab0 = a_0 * b_0;
        let ab1 = a_0 * b_1 + a_1 * b_0;
        let ab2 = a_0 * b_2 + a_1 * b_1 + a_2 * b_0;
        let ab3 = a_1 * b_2 + a_2 * b_1;
        let ab4 = a_2 * b_2;

        let p_0 = p.get(0).unwrap();
        let p_1 = p.get(1).unwrap();
        let p_2 = p.get(2).unwrap();

        let pq0 = p_0 * q_0;
        let pq1 = p_0 * q_1 + p_1 * q_0;
        let pq2 = p_0 * q_2 + p_1 * q_1 + p_2 * q_0;
        let pq3 = p_1 * q_2 + p_2 * q_1;
        let pq4 = p_2 * q_2;

        log::trace!("ab: {:?} {:?} {:?} {:?} {:?}", &ab0.eject_value(),&ab1.eject_value(),&ab2.eject_value(),&ab3.eject_value(),&ab4.eject_value());
        log::trace!("pq: {:?} {:?} {:?} {:?} {:?}", &pq0.eject_value(),&pq1.eject_value(),&pq2.eject_value(),&pq3.eject_value(),&pq4.eject_value());
        log::trace!("r: {:?} {:?} {:?}", r_0.eject_value(), r_1.eject_value(), r_2.eject_value());

        let (pq0r0_l, pq0r0_h)  = utils::splitField(&(&pq0 + r_0), self.parameters.LIMB_BYTES_NUM, self.parameters.LIMB_BYTES_NUM);
        let (ab0_l, ab0_h) = utils::splitField(&ab0, self.parameters.LIMB_BYTES_NUM, self.parameters.LIMB_BYTES_NUM);
        let diff0_l = &ab0_l- &pq0r0_l;

        let (pq1r1_l, pq1r1_h)  = utils::splitField(&(&pq1 + (r_1 + &pq0r0_h)), self.parameters.LIMB_BYTES_NUM, self.parameters.LIMB_BYTES_NUM+1);
        let diff1 = &ab1 + &ab0_h - &pq1r1_l;
        let (diff1_l, diff1_h) = utils::splitField(&diff1, self.parameters.LIMB_BYTES_NUM, self.parameters.LIMB_BYTES_NUM+1);

        let (pq2r2_l, pq2r2_h)  = utils::splitField(&(&pq2 + (r_2 + &pq1r1_h)), self.parameters.LIMB_BYTES_NUM, self.parameters.LIMB_BYTES_NUM+1);
        let diff2 = &ab2 + &diff1_h - &pq2r2_l;
        let (diff2_l, diff2_h) = utils::splitField(&diff2, self.parameters.LIMB_BYTES_NUM, self.parameters.LIMB_BYTES_NUM+1);

        let (pq3_l, pq3_h)  = utils::splitField(&(&pq3 + &pq2r2_h), self.parameters.LIMB_BYTES_NUM, self.parameters.LIMB_BYTES_NUM+1);
        let diff3 = &ab3 + &diff2_h - &pq3_l;
        let (diff3_l, diff3_h) = utils::splitField(&diff3, self.parameters.LIMB_BYTES_NUM, self.parameters.LIMB_BYTES_NUM+1);

        let diff4 = &ab4 + &diff3_h - (&pq3_h + &pq4);

        log::trace!("diff: {:?},{:?},{:?},{:?},{:?}", &diff0_l.eject_value(), &diff1_l.eject_value(), &diff2_l.eject_value(), &diff3_l.eject_value(), &diff4.eject_value());

        //assert!(diff.clone().eject_value() == snarkvm_console::types::Field::from_u8(0));
        Env::assert_eq(&diff0_l, &F::zero());
        Env::assert_eq(&diff1_l, &F::zero());
        Env::assert_eq(&diff2_l, &F::zero());
        Env::assert_eq(&diff3_l, &F::zero());
        Env::assert_eq(&diff4, &F::zero());

        //10. Range constrain q so that q*p + r < 2**t * n.
        // t = 88*3 = 264 bits, n > 252 bits
        // p = 256
        // if q and r less than p, it's certain.

        EFr
    }

    pub fn div(&self, other: &EmulatedField) -> EmulatedField {
        let p_value = BigUint::parse_bytes(self.parameters.FP, 16).unwrap();
        let pm2_value = &p_value- &BigUint::from_str_radix("2", 16).unwrap();

        let otheri = other.value.clone().unwrap().modpow(&pm2_value, &p_value);
        let div_result = self.value.clone().unwrap().mul(&otheri).mod_floor(&p_value);
        let result = EmulatedField::from_BigUint(&div_result, self.parameters.LIMB_BYTES_NUM, Private, self.parameters);

        let mul_result = result.mul(&other);
        for i in 0..self.parameters.LIMBS_NUM {
            Env::assert_eq(self.limbs[i].clone(), mul_result.limbs[i].clone());
        }

        result
    }

    /* a >  P ==> a - P
       a <= P ==> a

       And use the default limb size.
     */
    pub fn reduce(&self) -> EmulatedField {
        /*
             check Range of a
        */
        let p_value = BigUint::parse_bytes(self.parameters.FP, 16).unwrap();
        let p = EmulatedField::from_BigUint(&p_value, self.parameters.LIMB_BYTES_NUM, Constant, self.parameters);

        let mut reduce_result = self.value.clone().unwrap();
        if &reduce_result >= &p_value {
            reduce_result -= &p_value;
        }

        log::debug!("reduce from: {:?} to {:?}", self.value.clone().unwrap(), reduce_result);

        let result = EmulatedField::from_BigUint(&reduce_result, self.parameters.LIMB_BYTES_NUM, Private, self.parameters);
        log::debug!("result: {:?}", result.value.clone().unwrap());

        /* equal a? */
        let a0 = self.limbs.get(0).unwrap();
        let a1 = self.limbs.get(1).unwrap();
        let a2 = self.limbs.get(2).unwrap();
        log::trace!("a: {:?}, {:?}, {:?}", a0.eject_value(), a1.eject_value(), a2.eject_value());

        let r0 = result.limbs.get(0).unwrap();
        let r1 = result.limbs.get(1).unwrap();
        let r2 = result.limbs.get(2).unwrap();
        log::trace!("r: {:?}, {:?}, {:?}", r0.eject_value(), r1.eject_value(), r2.eject_value());

        let (ar0_l, ar0_h) = utils::splitField(a0, self.parameters.LIMB_BYTES_NUM, 1);
        let (ar1_l, ar1_h) = utils::splitField(&(a1 + &ar0_h), self.parameters.LIMB_BYTES_NUM, 1);
        let (ar2_l, ar2_h) = utils::splitField(&(a2 + &ar1_h), self.parameters.LIMB_BYTES_NUM, 1);
        log::trace!("ar0: {:?}, {:?}", ar0_l.eject_value(), ar0_h.eject_value());
        log::trace!("ar1: {:?}, {:?}", ar1_l.eject_value(), ar1_h.eject_value());
        log::trace!("ar2: {:?}, {:?}", ar2_l.eject_value(), ar2_h.eject_value());

        let a0e = ar0_l.is_equal(&r0);
        let a1e = ar1_l.is_equal(&r1);
        let a2e = ar2_l.is_equal(&r2);
        log::trace!("ae: {:?}, {:?}, {:?}", a0e.eject_value(), a1e.eject_value(), a2e.eject_value());

        let equala = a0e.bitand(&a1e).bitand(&a2e).bitand(&ar2_h.is_zero());
        log::trace!("equala: {:?}", equala.eject_value());

        /* equal a == r+p? */
        let p0 = p.limbs.get(0).unwrap();
        let p1 = p.limbs.get(1).unwrap();
        let p2 = p.limbs.get(2).unwrap();
        log::trace!("p: {:?} {:?} {:?}", p0.eject_value(), p1.eject_value(), p2.eject_value());

        let (rap0_l, rap0_h) = utils::splitField(&(r0 + p0), self.parameters.LIMB_BYTES_NUM, 1);
        let (rap1_l, rap1_h) = utils::splitField(&(r1 + p1 + &rap0_h), self.parameters.LIMB_BYTES_NUM, 1);
        let (rap2_l, rap2_h) = utils::splitField(&(r2 + p2 + &rap1_h), self.parameters.LIMB_BYTES_NUM, 1);
        log::trace!("rap0: {:?}, {:?}", rap0_l.eject_value(), rap0_h.eject_value());
        log::trace!("rap1: {:?}, {:?}", rap1_l.eject_value(), rap1_h.eject_value());
        log::trace!("rap2: {:?}, {:?}", rap2_l.eject_value(), rap2_h.eject_value());

        let a0ep = ar0_l.is_equal(&rap0_l);
        let a1ep = ar1_l.is_equal(&rap1_l);
        let a2ep = ar2_l.is_equal(&rap2_l);
        log::trace!("aep: {:?}, {:?}, {:?}", a0ep.eject_value(), a1ep.eject_value(), a2ep.eject_value());

        let equalp = a0ep.bitand(&a1ep).bitand(&a2ep).bitand(&rap2_h.is_zero().bitand(&ar2_h.is_zero()));
        log::trace!("equalp: {:?}", equalp.eject_value());

        let less = EmulatedField::is_less_than_constant(self, &p);
        log::trace!("is_less: {:?}", less.eject_value());

        let less_than = Boolean::ternary(&less, &equala, &equalp);
        Env::assert(&less_than);

        assert!(less_than.eject_value());

        result
    }

    pub fn add_wo_reduce(&self, other: &EmulatedField) -> EmulatedField {
        let ls = self.parameters.LIMB_BYTES_NUM;

        let p_value = BigUint::parse_bytes(self.parameters.FP, 16).unwrap();
        let mut add_result = self.value.clone().unwrap().add(other.value.clone().unwrap());

        let mut limbs = Vec::with_capacity(self.parameters.LIMBS_NUM);
        for i in 0..self.parameters.LIMBS_NUM {
            limbs.push(self.limbs.get(i).unwrap() + other.limbs.get(i).unwrap());
        }

        EmulatedField {
            limb_size: ls,
            limbs: limbs,
            value: Some(add_result),
            overflow: true,
            parameters: self.parameters,
        }
    }

    pub fn add(&self, other: &EmulatedField) -> EmulatedField {
        let ls = self.parameters.LIMB_BYTES_NUM;

        let p_value = BigUint::parse_bytes(self.parameters.FP, 16).unwrap();
        let mut add_result = self.value.clone().unwrap().add(other.value.clone().unwrap());

        let mut limbs = Vec::with_capacity(self.parameters.LIMBS_NUM);
        for i in 0..self.parameters.LIMBS_NUM {
            limbs.push(self.limbs.get(i).unwrap() + other.limbs.get(i).unwrap());
        }

        let temp = EmulatedField {
            limb_size: ls,
            limbs: limbs,
            value: Some(add_result),
            overflow: true,
            parameters: self.parameters,
        };

        temp.reduce()
    }

    /* make sure self and other are less than p */
    pub fn sub(&self, other: &EmulatedField) -> EmulatedField {
        let ls = self.parameters.LIMB_BYTES_NUM;

        log::debug!("sub: {:?} {:?}", self, other);
        log::debug!("sub: {:?} {:?}", self.value.clone().unwrap(), other.value.clone().unwrap());
        //check range
        let p_value = BigUint::parse_bytes(self.parameters.FP, 16).unwrap();

        let mut sub_result = self.value.clone().unwrap().add(p_value.clone()).sub(other.value.clone().unwrap());
        if &sub_result >= &p_value {
            sub_result -= &p_value;
        }
        log::debug!("result: {:?}", sub_result);
        let result = EmulatedField::from_BigUint(&sub_result, ls, Private, self.parameters);

        let mut add_result = result.add_wo_reduce(&other);
        add_result = add_result.reduce();

        for i in 0..self.parameters.LIMBS_NUM {
            log::trace!("--> {:?} : {:?} {:?}", i, self.limbs[i].clone().eject_value(), add_result.limbs[i].clone().eject_value());
            Env::assert_eq(self.limbs.get(i).unwrap(), add_result.limbs.get(i).unwrap());
        }

        result
    }
}

#[test]
fn test_is_zero() {
    env_logger::init();

    let p_value = BigUint::parse_bytes(secp256k1_Fp.FP, 16).unwrap();
    Circuit::reset();

    let is_zero = rand::random::<u8>() > 128;

    const bytes_num: usize = secp256k1_Fp.LIMB_BYTES_NUM;
    let mut bytes: [u8; bytes_num*3] = [0; bytes_num*3];
    for i in 0..bytes_num*3 {
        if is_zero {
            bytes[i] = 0;
        } else {
            bytes[i] = rand::random::<u8>();
        }
    }
    let mut a_value = BigUint::from_bytes_le(&bytes) % p_value.clone();
    let a = EmulatedField::from_BigUint(&a_value, bytes_num, Private, secp256k1_Fp);
    println!("a: {:?}", a.value.clone().unwrap());

    let mut result = a.is_zero();
    println!("is_zero result: {:?}", result.eject_value());

    if a_value == BigUint::from_u8(0).unwrap() {
        assert_eq!(result.eject_value(), true);
    } else {
        assert_eq!(result.eject_value(), false);
    }
    assert_eq!(Circuit::is_satisfied(), true);
}

#[test]
fn test_mul() {
    env_logger::init();
    let before = utils::getMemState(false);

    let p_value = BigUint::parse_bytes(secp256k1_Fp.FP, 16).unwrap();
    Circuit::reset();

    const bytes_num: usize = secp256k1_Fp.LIMB_BYTES_NUM;
    let mut bytes: [u8; bytes_num*3] = [0; bytes_num*3];
    for i in 0..bytes_num*3 {
        bytes[i] = rand::random::<u8>();
    }
    let mut a_value = BigUint::from_bytes_le(&bytes) % p_value.clone();
    let a = EmulatedField::from_BigUint(&a_value, bytes_num, Private, secp256k1_Fp);

    for i in 0..bytes_num*3 {
        bytes[i] = rand::random::<u8>();
    }
    let mut b_value = BigUint::from_bytes_le(&bytes) % p_value.clone();
    let b = EmulatedField::from_BigUint(&b_value, bytes_num, Private, secp256k1_Fp);
    println!("a: {:?}, b: {:?}", a.value.clone().unwrap(), b.value.clone().unwrap());

    let mut result = a.mul(&b);
    println!("mul result: {:?}", result.value.clone().unwrap());

    let mut br = a_value * b_value;
    br = br % p_value;

    assert_eq!(result.value.unwrap(), br);
    assert_eq!(Circuit::is_satisfied(), true);

    let circuit = Circuit::eject_assignment_and_reset();
    println!("num constraints: {}", circuit.num_constraints());
    println!("num public: {}", circuit.num_public());
    println!("num private: {}", circuit.num_private());
    println!("num non-zeros: {:?}", circuit.num_nonzeros());

    utils::printMemDiff(&before);
}

#[test]
fn test_div() {
    env_logger::init();

    let p_value = BigUint::parse_bytes(secp256k1_Fp.FP, 16).unwrap();
    Circuit::reset();

    const bytes_num: usize = secp256k1_Fp.LIMB_BYTES_NUM;
    let mut bytes: [u8; bytes_num*3] = [0; bytes_num*3];
    for i in 0..bytes_num*3 {
        bytes[i] = rand::random::<u8>();
    }
    let mut a_value = BigUint::from_bytes_le(&bytes) % p_value.clone();
    let a = EmulatedField::from_BigUint(&a_value, bytes_num, Private, secp256k1_Fp);

    for i in 0..bytes_num*3 {
        bytes[i] = rand::random::<u8>();
    }
    let mut b_value = BigUint::from_bytes_le(&bytes) % p_value.clone();
    let b = EmulatedField::from_BigUint(&b_value, bytes_num, Private, secp256k1_Fp);
    println!("a: {:?}, b: {:?}", a.value.clone().unwrap(), b.value.clone().unwrap());

    let mut result = a.div(&b);
    println!("div result: {:?}", result.value.clone().unwrap());

    let pm2_value = p_value.clone().sub(BigUint::one()).sub(BigUint::one());
    let bi = b_value.clone().modpow(&pm2_value, &p_value);
    log::debug!("b inverse: {:?}", bi.clone());
    let div_result = a_value.clone().mul(&bi).mod_floor(&p_value);

    assert_eq!(result.value.unwrap(), div_result);
    assert_eq!(Circuit::is_satisfied(), true);

    let circuit = Circuit::eject_assignment_and_reset();
    println!("num constraints: {}", circuit.num_constraints());
    println!("num public: {}", circuit.num_public());
    println!("num private: {}", circuit.num_private());
    println!("num non-zeros: {:?}", circuit.num_nonzeros());
}

#[test]
fn test_add() {
    env_logger::init();
    let before = utils::getMemState(false);

    let p_value = BigUint::parse_bytes(secp256k1_Fp.FP, 16).unwrap();
    Circuit::reset();

    const bytes_num: usize = secp256k1_Fp.LIMB_BYTES_NUM;
    let mut bytes: [u8; bytes_num*3] = [0; bytes_num*3];
    for i in 0..bytes_num*3 {
        bytes[i] = rand::random::<u8>();
    }
    let mut a_value = BigUint::from_bytes_le(&bytes) % p_value.clone();
    let a = EmulatedField::from_BigUint(&a_value, bytes_num, Private, secp256k1_Fp);

    for i in 0..bytes_num*3 {
        bytes[i] = rand::random::<u8>();
    }
    let mut b_value = BigUint::from_bytes_le(&bytes) % p_value.clone();
    let b = EmulatedField::from_BigUint(&b_value, bytes_num, Private, secp256k1_Fp);
    println!("a: {:?}, b: {:?}", a.value.clone().unwrap(), b.value.clone().unwrap());

    let mut result = a.add_wo_reduce(&b);
    result = result.reduce();
    println!("add result: {:?}", result.value.clone().unwrap());

    let mut br = a_value + b_value;
    if br > p_value {
        br = br - p_value;
    }
    assert_eq!(result.value.unwrap(), br);
    assert_eq!(Circuit::is_satisfied(), true);

    let circuit = Circuit::eject_assignment_and_reset();
    println!("num constraints: {}", circuit.num_constraints());
    println!("num public: {}", circuit.num_public());
    println!("num private: {}", circuit.num_private());
    println!("num non-zeros: {:?}", circuit.num_nonzeros());

    utils::printMemDiff(&before);
}

#[test]
fn test_sub() {
    env_logger::init();
    let before = utils::getMemState(false);

    let p_value = BigUint::parse_bytes(secp256k1_Fp.FP, 16).unwrap();
    Circuit::reset();

    const bytes_num: usize = secp256k1_Fp.LIMB_BYTES_NUM;
    let mut bytes: [u8; bytes_num*3] = [0; bytes_num*3];
    for i in 0..bytes_num*3 {
        bytes[i] = rand::random::<u8>();
    }
    let mut a_value = BigUint::from_bytes_le(&bytes) % p_value.clone();
    let a = EmulatedField::from_BigUint(&a_value, bytes_num, Private, secp256k1_Fp);

    for i in 0..bytes_num*3 {
        bytes[i] = rand::random::<u8>();
    }
    let mut b_value = BigUint::from_bytes_le(&bytes) % p_value.clone();
    let b = EmulatedField::from_BigUint(&b_value, bytes_num, Private, secp256k1_Fp);
    println!("a: {:?}, b: {:?}", a.value.clone().unwrap(), b.value.clone().unwrap());

    let result = a.sub(&b);
    println!("sub result: {:?}", result.value.clone().unwrap());

    if a_value.clone() >= b_value.clone() {
        assert_eq!(result.value.unwrap(), a_value.sub(&b_value));
    } else {
        assert_eq!(result.value.unwrap(), a_value.add(&p_value).sub(&b_value));
    }
    assert_eq!(Circuit::is_satisfied(), true);

    let circuit = Circuit::eject_assignment_and_reset();
    println!("num constraints: {}", circuit.num_constraints());
    println!("num public: {}", circuit.num_public());
    println!("num private: {}", circuit.num_private());
    println!("num non-zeros: {:?}", circuit.num_nonzeros());

    utils::printMemDiff(&before);
}

#[test]
fn test_reduce() {
    env_logger::init();
    let before = utils::getMemState(false);

    let p_value = BigUint::parse_bytes(secp256k1_Fp.FP, 16).unwrap();
    Circuit::reset();

    const bytes_num: usize = secp256k1_Fp.LIMB_BYTES_NUM;
    let mut bytes: [u8; bytes_num*3] = [0; bytes_num*3];
    for i in 0..bytes_num*3 {
        bytes[i] = rand::random::<u8>();
    }
    let mut a_value = BigUint::from_bytes_le(&bytes) % p_value.clone();
    if rand::random::<bool>() == true {
        a_value += p_value.clone();
    }

    //a_value = BigUint::from_u8(0).unwrap();
    //a_value = p_value.clone();
    let a = EmulatedField::from_BigUint(&a_value, bytes_num, Private, secp256k1_Fp);

    println!("a: {:?}", a.value.clone().unwrap());

    let result = a.reduce();
    println!("reduce result: {:?}", result.value.clone().unwrap());

    if a_value.clone() >= p_value.clone() {
        assert_eq!(result.value.unwrap(), a_value - p_value);
    } else {
        assert_eq!(result.value.unwrap(), a_value);
    }
    assert_eq!(Circuit::is_satisfied(), true);

    let circuit = Circuit::eject_assignment_and_reset();
    println!("num constraints: {}", circuit.num_constraints());
    println!("num public: {}", circuit.num_public());
    println!("num private: {}", circuit.num_private());
    println!("num non-zeros: {:?}", circuit.num_nonzeros());

    utils::printMemDiff(&before);
}
