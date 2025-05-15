use crate::emulated_field::*;
use k256::elliptic_curve::PrimeField;
use log::*;
use num_bigint::*;
use snarkvm_circuit::environment::prelude::num_traits::FromPrimitive;
use snarkvm_circuit::prelude::num_traits::Num;
use snarkvm_circuit::Boolean;
use snarkvm_circuit::Environment;
use snarkvm_circuit_environment::Mode::{Constant, Private, Public};
use snarkvm_circuit_environment::{Circuit, Eject, Inject, Mode, Ternary};
use std::ops::{Add, BitAnd, BitOr, Div, Mul, Not};

use crate::utils;
/*
    Point 0 - x,y = 0
*/
#[derive(Clone, Debug)]
pub struct Point {
    pub x: EmulatedField,
    pub y: EmulatedField,
    pub z: EmulatedField,
}

// thread_local! {
//     pub static AFFINE_INF: Affine = Affine::
// }

#[derive(Clone, Debug)]
pub struct Affine {
    pub x: EmulatedField,
    pub y: EmulatedField,
    pub inf: Boolean<Circuit>,
}

impl Affine {
    pub fn zero() -> Self {
        Self {
            x: EmulatedField::zero(secp256k1_Fp),
            y: EmulatedField::zero(secp256k1_Fp),
            inf: Boolean::<Circuit>::new(Mode::Constant, true),
        }
    }

    pub fn from_xy(x: &BigUint, y: &BigUint, mode: Mode, p: &'static FieldParameters) -> Self {
        let fgx = EmulatedField::from_BigUint(&x, p.LIMB_BYTES_NUM, mode, p);
        let fgy = EmulatedField::from_BigUint(&y, p.LIMB_BYTES_NUM, mode, p);

        Self {
            x: fgx.clone(),
            y: fgy.clone(),
            inf: Boolean::<Circuit>::new(Mode::Private, false),
        }
    }

    pub fn from_xy_f(
        x: &EmulatedField,
        y: &EmulatedField,
        mode: Mode,
        p: &'static FieldParameters,
    ) -> Self {
        Self {
            x: x.clone(),
            y: y.clone(),
            inf: Boolean::<Circuit>::new(Mode::Private, false),
        }
    }

    pub fn G() -> Self {
        let gx = BigUint::from_str_radix(
            "79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798",
            16,
        )
        .unwrap();
        let fgx =
            EmulatedField::from_BigUint(&gx, secp256k1_Fp.LIMB_BYTES_NUM, Constant, secp256k1_Fp);
        let gy = BigUint::from_str_radix(
            "483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8",
            16,
        )
        .unwrap();
        let fgy =
            EmulatedField::from_BigUint(&gy, secp256k1_Fp.LIMB_BYTES_NUM, Constant, secp256k1_Fp);

        Self {
            x: fgx.clone(),
            y: fgy.clone(),
            inf: Boolean::<Circuit>::new(Mode::Constant, false),
        }
    }

    pub fn is_inf(&self) -> &Boolean<Circuit> {
        &self.inf
    }

    pub fn ternary(condition: &Boolean<Circuit>, a: &Affine, b: &Affine) -> Self {
        Self {
            x: EmulatedField::ternary(condition, &a.x, &b.x),
            y: EmulatedField::ternary(condition, &a.y, &b.y),
            inf: Boolean::ternary(condition, &a.inf, &b.inf),
        }
    }

    //https://www.hyperelliptic.org/EFD/g1p/auto-shortw.html
    pub fn add(&self, other: &Affine) -> Self {
        /*
        x3 = (y2-y1)^2/(x2-x1)^2-x1-x2
        y3 = (2*x1+x2)*(y2-y1)/(x2-x1)-(y2-y1)^3/(x2-x1)^3-y1
        */
        let a_is_inf = self.is_inf();
        let b_is_inf = other.is_inf();

        let x2_eq_x1 = self.x.is_equal(&other.x);
        let y2_add_y1 = self.y.add(&other.y);
        let result_is_inf = x2_eq_x1.clone().bitand(y2_add_y1.is_zero());
        let a_is_b = x2_eq_x1.bitand(self.y.is_equal(&other.y));

        let y2sy1 = other.y.sub(&self.y);
        let x2sx1 = other.x.sub(&self.x);
        let y2y1dx2x1 = EmulatedField::ternary(
            &result_is_inf,
            &EmulatedField::zero(&secp256k1_Fp),
            &y2sy1.div(&x2sx1),
        );
        let y2y1dx2x1_2 = y2y1dx2x1.mul(&y2y1dx2x1);
        let y2y1dx2x1_3 = y2y1dx2x1_2.mul(&y2y1dx2x1);

        let x1ax2 = self.x.add(&other.x);
        let x3 = y2y1dx2x1_2.sub(&x1ax2);

        let x1_2ax2 = x1ax2.add(&self.x);
        let y3 = x1_2ax2.mul(&y2y1dx2x1).sub(&y2y1dx2x1_3).sub(&self.y);

        let result = Affine::ternary(
            &result_is_inf,
            &Affine::zero(),
            &Affine::ternary(
                &a_is_b,
                &self.double(),
                &Affine {
                    x: x3,
                    y: y3,
                    inf: Boolean::<Circuit>::new(Mode::Private, false),
                },
            ),
        );

        Self::ternary(
            &a_is_inf,
            &other,
            &Affine::ternary(&b_is_inf, &self, &result),
        )
    }

    pub fn double(&self) -> Self {
        /*
        a = 0
        x3 = (3*x1^2+a)^2/(2*y1)^2-x1-x1
        y3 = (2*x1+x1)*(3*x1^2+a)/(2*y1)-(3*x1^2+a)^3/(2*y1)^3-y1

        x3 = (3*x1^2)^2/(2*y1)^2-2*x1 =
        y3 = (3*x1)*(3*x1^2)/(2*y1)-(3*x1^2)^3/(2*y1)^3-y1

         */
        //let x1s = self.x.mul(&self.x);
        let x1d = self.x.add(&self.x);
        let x1t = x1d.add(&self.x);
        let y1d = self.y.add(&self.y);

        let x1s_3 = x1t.mul(&self.x);
        //let x1s_2 = x1s.add(&x1s);
        //let x1s_3 = x1s_2.add(&x1s);

        let x1s_3dy1d = x1s_3.div(&y1d);
        let x1s_3dy1d = EmulatedField::ternary(
            &self.is_inf(),
            &EmulatedField::zero(&secp256k1_Fp),
            &x1s_3.div(&y1d),
        );
        let x1s_3dy1d_2 = x1s_3dy1d.mul(&x1s_3dy1d);
        let x1s_3dy1d_3 = x1s_3dy1d_2.mul(&x1s_3dy1d);

        let x3 = x1s_3dy1d_2.sub(&x1d);
        let y3 = x1t.mul(&x1s_3dy1d).sub(&x1s_3dy1d_3).sub(&self.y);

        let is_inf = self.is_inf();

        let result = Affine {
            x: x3,
            y: y3,
            inf: Boolean::<Circuit>::new(Mode::Private, false),
        };

        Self::ternary(&is_inf, &Affine::zero(), &result)
    }

    /* s1G1 + s2G2
       assume window bits = n, total bits = 256
       Num of add is: (2^{2n}-3)+256/n

       n=1, 257
       n=2, 141
       n=3, 147
       n=4, 317

       n=2 is the best choice.
    */
    pub fn scalarMulExp_win(
        s1: &EmulatedField,
        G1: &Affine,
        s2: &EmulatedField,
        G2: &Affine,
    ) -> Affine {
        /* double and add */
        let mut sum = Affine::zero();
        let window_bits = 2;

        let G1_2 = G1.double();
        let G1_3 = G1_2.add(&G1);
        let G2_2 = G2.double();
        let G2_3 = G2_2.add(&G2);
        /*
          s2[1] s1[1] s2[0] s1[0]
        */
        let mut g = Vec::with_capacity(2u32.pow(window_bits * 2) as usize);
        let zero = Affine::zero();
        g.push(zero.clone());
        g.push(G1.clone());
        g.push(G2.clone());
        for i in 3..2u32.pow(window_bits * 2) {
            let s0_0 = i & 0x01;
            let s0_1 = (i >> 2) & 0x01;
            let s1_0 = (i >> 1) & 0x01;
            let s1_1 = (i >> 3) & 0x01;

            let s0 = s0_1 * 2 + s0_0;
            let s1 = s1_1 * 2 + s1_0;

            let mut p0 = &zero;
            if s0 == 1 {
                p0 = G1;
            }
            if s0 == 2 {
                p0 = &G1_2;
            }
            if s0 == 3 {
                p0 = &G1_3;
            }

            let mut p1 = &zero;
            if s1 == 1 {
                p1 = G2;
            }
            if s1 == 2 {
                p1 = &G2_2;
            }
            if s1 == 3 {
                p1 = &G2_3;
            }

            g.push(p0.add(p1));
        }

        let mut bits1 = Vec::with_capacity(s1.parameters.LIMBS_NUM);
        let mut bits2 = Vec::with_capacity(s1.parameters.LIMBS_NUM);
        for i in 0..s1.parameters.LIMBS_NUM {
            let bs1 = utils::to_bits(&s1.limbs[i], s1.limb_size);
            let bs2 = utils::to_bits(&s2.limbs[i], s2.limb_size);
            for j in 0..bs1.len() {
                let bs1j = bs1.get(j).unwrap();
                bits1.push(bs1j.clone());
            }
            for j in 0..bs2.len() {
                let bs2j = bs2.get(j).unwrap();
                bits2.push(bs2j.clone());
            }
        }

        bits1.truncate(256);
        bits2.truncate(256);
        bits1.reverse();
        bits2.reverse();

        for i in (0..bits1.len()).step_by(2) {
            let bits1_i = bits1.get(i).unwrap();
            let bits1_ip1 = bits1.get(i + 1).unwrap();
            let bits2_i = bits2.get(i).unwrap();
            let bits2_ip1 = bits2.get(i + 1).unwrap();

            /* select p */
            let p = Affine::ternary(
                bits2_i,
                &Affine::ternary(
                    bits1_i,
                    &Affine::ternary(
                        bits2_ip1,
                        &Affine::ternary(bits1_ip1, g.get(15).unwrap(), g.get(14).unwrap()),
                        &Affine::ternary(bits1_ip1, g.get(13).unwrap(), g.get(12).unwrap()),
                    ),
                    &Affine::ternary(
                        bits2_ip1,
                        &Affine::ternary(bits1_ip1, g.get(11).unwrap(), g.get(10).unwrap()),
                        &Affine::ternary(bits1_ip1, g.get(9).unwrap(), g.get(8).unwrap()),
                    ),
                ),
                &Affine::ternary(
                    bits1_i,
                    &Affine::ternary(
                        bits2_ip1,
                        &Affine::ternary(bits1_ip1, g.get(7).unwrap(), g.get(6).unwrap()),
                        &Affine::ternary(bits1_ip1, g.get(5).unwrap(), g.get(4).unwrap()),
                    ),
                    &Affine::ternary(
                        bits2_ip1,
                        &Affine::ternary(bits1_ip1, g.get(3).unwrap(), g.get(2).unwrap()),
                        &Affine::ternary(bits1_ip1, g.get(1).unwrap(), g.get(0).unwrap()),
                    ),
                ),
            );

            sum = sum.double().double();
            sum = sum.add(&p);
        }

        sum
    }
}

impl Point {
    pub fn zero() -> Point {
        Point {
            x: EmulatedField::zero(secp256k1_Fp),
            y: EmulatedField::zero(secp256k1_Fp),
            z: EmulatedField::one(secp256k1_Fp),
        }
    }

    pub fn from_xy(x: &BigUint, y: &BigUint, mode: Mode, p: &'static FieldParameters) -> Point {
        let fgx = EmulatedField::from_BigUint(&x, p.LIMB_BYTES_NUM, mode, p);
        let fgy = EmulatedField::from_BigUint(&y, p.LIMB_BYTES_NUM, mode, p);
        let one_value = BigUint::from_str_radix("1", 16).unwrap();
        let one = EmulatedField::from_BigUint(
            &one_value,
            secp256k1_Fp.LIMB_BYTES_NUM,
            Constant,
            secp256k1_Fp,
        );

        Point {
            x: fgx.clone(),
            y: fgy.clone(),
            z: one.clone(),
        }
    }

    pub fn from_xy_f(
        x: &EmulatedField,
        y: &EmulatedField,
        mode: Mode,
        p: &'static FieldParameters,
    ) -> Point {
        let one_value = BigUint::from_str_radix("1", 16).unwrap();
        let one = EmulatedField::from_BigUint(
            &one_value,
            secp256k1_Fp.LIMB_BYTES_NUM,
            Constant,
            secp256k1_Fp,
        );

        Point {
            x: x.clone(),
            y: y.clone(),
            z: one.clone(),
        }
    }

    pub fn G() -> Point {
        let gx = BigUint::from_str_radix(
            "79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798",
            16,
        )
        .unwrap();
        let fgx =
            EmulatedField::from_BigUint(&gx, secp256k1_Fp.LIMB_BYTES_NUM, Constant, secp256k1_Fp);
        let gy = BigUint::from_str_radix(
            "483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8",
            16,
        )
        .unwrap();
        let fgy =
            EmulatedField::from_BigUint(&gy, secp256k1_Fp.LIMB_BYTES_NUM, Constant, secp256k1_Fp);

        let one_value = BigUint::from_str_radix("1", 16).unwrap();
        let one = EmulatedField::from_BigUint(
            &one_value,
            secp256k1_Fp.LIMB_BYTES_NUM,
            Constant,
            secp256k1_Fp,
        );

        Point {
            x: fgx.clone(),
            y: fgy.clone(),
            z: one.clone(),
        }
    }

    pub fn is_zero(&self) -> Boolean<Circuit> {
        let is_x_zero = self.x.is_zero();
        let is_y_zero = self.y.is_zero();

        is_x_zero.bitand(is_y_zero)
    }

    pub fn ternary(condition: &Boolean<Circuit>, a: &Point, b: &Point) -> Point {
        Point {
            x: EmulatedField::ternary(condition, &a.x, &b.x),
            y: EmulatedField::ternary(condition, &a.y, &b.y),
            z: EmulatedField::ternary(condition, &a.z, &b.z),
        }
    }

    pub fn to_affine(&self) -> Point {
        let zz = self.z.clone().mul(&self.z);
        let zzz = zz.clone().mul(&self.z);
        Point {
            x: self.x.div(&zz),
            y: self.y.div(&zzz),
            z: EmulatedField::one(self.z.parameters),
        }
    }

    //https://www.hyperelliptic.org/EFD/g1p/auto-shortw-jacobian.html#addition-mmadd-2007-bl
    //z1=1, z2=1
    pub fn add1(&self, other: &Point) -> Point {
        trace!("self: {:?} {:?}", &self.x, &self.y);
        trace!("other: {:?} {:?}", &other.x, &other.y);
        let is_self_zero = self.is_zero();
        let is_other_zero = other.is_zero();
        let is_zero = is_self_zero.clone().bitor(is_other_zero);

        let zero_result = Point::ternary(&is_self_zero, &other, &self);

        let H = other.x.sub(&self.x);
        trace!("H: {:?}", H.clone());
        let HH = H.mul(&H);
        trace!("HH: {:?}", HH.clone());

        let HH2 = HH.add(&HH);
        let I = HH2.add(&HH2);
        trace!("I: {:?}", I.clone());
        let J = H.mul(&I);
        trace!("J: {:?}", J.clone());
        let mut r = other.y.sub(&self.y);
        r = r.add(&r);
        let V = self.x.mul(&I);
        trace!("V: {:?}", V.clone());
        let V2 = V.add(&V);
        let X3 = r.mul(&r).sub(&J).sub(&V2);
        trace!("X3: {:?}", X3.clone());
        let Y1J = self.y.mul(&J);
        let Y1J2 = Y1J.add(&Y1J);
        let Y3 = r.mul(&(V.sub(&X3))).sub(&Y1J2);
        trace!("Y3: {:?}", Y3.clone());
        let Z3 = H.add(&H);
        trace!("Z3: {:?}", Z3.clone());

        Point {
            x: EmulatedField::ternary(&is_zero, &zero_result.x, &X3),
            y: EmulatedField::ternary(&is_zero, &zero_result.y, &Y3),
            z: EmulatedField::ternary(&is_zero, &zero_result.z, &Z3),
        }
    }

    //https://www.hyperelliptic.org/EFD/g1p/auto-shortw-jacobian.html#doubling-mdbl-2007-bl
    //z = 1
    pub fn double1(&self) -> Point {
        let eight_big = BigUint::from_str_radix("8", 16).unwrap();
        let eight = EmulatedField::from_BigUint(
            &eight_big,
            self.x.parameters.LIMB_BYTES_NUM,
            Constant,
            self.x.parameters,
        );

        let is_zero = self.is_zero();

        let XX = self.x.mul(&self.x);
        trace!("XX: {:?}", XX);
        let YY = self.y.mul(&self.y);
        trace!("YY: {:?}", YY);

        let YYYY = YY.mul(&YY);
        let X1YY = self.x.add(&YY);
        let X1YY2 = X1YY.mul(&X1YY);
        let XXYYYY = XX.add(&YYYY);

        let X1YY2_XXYYYY = X1YY2.sub(&XXYYYY);
        let S = X1YY2_XXYYYY.add(&X1YY2_XXYYYY.clone());
        trace!("S: {:?}", S);
        let M = XX.add(&XX).add(&XX); //a = 0
        trace!("M: {:?}", M);
        let T = M.mul(&M).sub(&(S.add(&S)));
        trace!("T: {:?}", T);
        let X3 = T.clone();
        let Y3 = M.mul(&(S.sub(&T))).sub(&(YYYY.mul(&eight)));
        let Z3 = self.y.add(&self.y);
        trace!("X/Y/Z: {:?} {:?} {:?}", X3, Y3, Z3);

        Point {
            x: EmulatedField::ternary(&is_zero, &self.x, &X3),
            y: EmulatedField::ternary(&is_zero, &self.y, &Y3),
            z: EmulatedField::ternary(&is_zero, &self.z, &Z3),
        }
    }

    //https://www.hyperelliptic.org/EFD/g1p/auto-shortw-jacobian.html#addition-madd-2007-bl
    // Z2=1
    pub fn add(&self, other: &Point) -> Point {
        trace!("self: {:?} {:?}", &self.x, &self.y);
        trace!("other: {:?} {:?}", &other.x, &other.y);
        let is_self_zero = self.is_zero();
        let is_other_zero = other.is_zero();
        let is_zero = is_self_zero.clone().bitor(is_other_zero);

        let zero_result = Point::ternary(&is_self_zero, &other, &self);

        let Z1Z1 = self.z.mul(&self.z);
        let U2 = other.x.mul(&Z1Z1);
        let S2 = other.y.mul(&self.z).mul(&Z1Z1);

        let H = U2.sub(&self.x);
        trace!("H: {:?}", H.clone());
        let HH = H.mul(&H);
        trace!("HH: {:?}", HH.clone());

        let HH2 = HH.add(&HH);
        let I = HH2.add(&HH2);
        trace!("I: {:?}", I.clone());
        let J = H.mul(&I);
        trace!("J: {:?}", J.clone());
        let mut r = S2.sub(&self.y);
        r = r.add(&r);
        let V = self.x.mul(&I);
        trace!("V: {:?}", V.clone());
        let V2 = V.add(&V);
        let X3 = r.mul(&r).sub(&J).sub(&V2);
        trace!("X3: {:?}", X3.clone());
        let Y1J = self.y.mul(&J);
        let Y1J2 = Y1J.add(&Y1J);
        let Y3 = r.mul(&(V.sub(&X3))).sub(&Y1J2);
        trace!("Y3: {:?}", Y3.clone());
        let Z1H = self.z.add(&H);
        let Z1H2 = Z1H.mul(&Z1H);
        let Z3 = Z1H2.sub(&Z1Z1).sub(&HH);
        trace!("Z3: {:?}", Z3.clone());

        Point {
            x: EmulatedField::ternary(&is_zero, &zero_result.x, &X3),
            y: EmulatedField::ternary(&is_zero, &zero_result.y, &Y3),
            z: EmulatedField::ternary(&is_zero, &zero_result.z, &Z3),
        }
    }

    //https://www.hyperelliptic.org/EFD/g1p/auto-shortw-jacobian.html#doubling-dbl-2007-bl
    pub fn double(&self) -> Point {
        let eight_big = BigUint::from_str_radix("8", 16).unwrap();
        let eight = EmulatedField::from_BigUint(
            &eight_big,
            self.x.parameters.LIMB_BYTES_NUM,
            Constant,
            self.x.parameters,
        );

        let is_zero = self.is_zero();

        let XX = self.x.mul(&self.x);
        trace!("XX: {:?}", XX);
        let YY = self.y.mul(&self.y);
        trace!("YY: {:?}", YY);
        //let ZZ = self.z.mul(&self.z);
        //trace!("ZZ: {:?}", ZZ);

        let X1YY = self.x.mul(&YY);
        let X1YY2 = X1YY.add(&X1YY);
        let S = X1YY2.add(&X1YY2);
        trace!("S: {:?}", S);

        let XX2 = XX.add(&XX);
        let M = XX2.add(&XX);
        trace!("M: {:?}", M);

        let T = M.mul(&M).sub(&S.add(&S));
        trace!("T: {:?}", T);
        let X3 = T.clone();
        let Y3 = M.mul(&(S.sub(&T))).sub(&(YY.mul(&YY).mul(&eight)));
        let Y1Z1 = self.y.mul(&self.z);
        let Z3 = Y1Z1.add(&Y1Z1);
        trace!("X/Y/Z: {:?} {:?} {:?}", X3, Y3, Z3);

        Point {
            x: EmulatedField::ternary(&is_zero, &self.x, &X3),
            y: EmulatedField::ternary(&is_zero, &self.y, &Y3),
            z: EmulatedField::ternary(&is_zero, &self.z, &Z3),
        }
    }

    pub fn scalarMul(&self, scalar: &EmulatedField) -> Point {
        /* double and add */
        let mut sum = Point::zero();
        log::trace!("scalar mul: {:?} {:?} {:?}", sum.x, sum.y, sum.z);

        let mut bits = Vec::with_capacity(scalar.parameters.LIMBS_NUM);
        for i in 0..scalar.parameters.LIMBS_NUM {
            let bs = utils::to_bits(&scalar.limbs[i].clone(), scalar.clone().limb_size);
            for j in 0..bs.len() {
                bits.push(bs[j].clone());
            }
        }

        bits.truncate(256);
        bits.reverse();

        for i in 0..bits.len() {
            sum = sum.double().to_affine();
            sum = sum.add1(&Point::ternary(&bits[i].clone(), self, &Point::zero()));
            /*
            sum = sum.double();
            sum = sum.add(&Point::ternary(&bits[i].clone(), self, &Point::zero()));
            */
        }

        sum
    }

    /* s1G1 + s2G2 */
    pub fn scalarMulExp(s1: &EmulatedField, G1: &Point, s2: &EmulatedField, G2: &Point) -> Point {
        /* double and add */
        let mut sum = Point::zero();
        log::trace!("scalar mul: {:?} {:?} {:?}", sum.x, sum.y, sum.z);

        /* G1 is different with G2 */
        let G1G2 = G1.add1(&G2).to_affine();

        let mut bits1 = Vec::with_capacity(s1.parameters.LIMBS_NUM);
        let mut bits2 = Vec::with_capacity(s1.parameters.LIMBS_NUM);
        for i in 0..s1.parameters.LIMBS_NUM {
            let bs1 = utils::to_bits(&s1.limbs[i].clone(), s1.clone().limb_size);
            let bs2 = utils::to_bits(&s2.limbs[i].clone(), s2.clone().limb_size);
            for j in 0..bs1.len() {
                bits1.push(bs1[j].clone());
            }
            for j in 0..bs2.len() {
                bits2.push(bs2[j].clone());
            }
        }

        bits1.truncate(256);
        bits2.truncate(256);
        bits1.reverse();
        bits2.reverse();

        for i in 0..bits1.len() {
            let bita = bits1[i].clone().bitand(bits2[i].clone());
            let bito = bits1[i].clone().bitor(bits2[i].clone());

            let G1orG2 = Point::ternary(&bits1[i], &G1, &G2);
            let zeroCheck = Point::ternary(&bito, &G1orG2, &Point::zero());
            let p = Point::ternary(&bita, &G1G2, &zeroCheck);

            sum = sum.double().to_affine();
            sum = sum.add1(&p);
        }

        sum
    }

    /* s1G1 + s2G2
       assume window bits = n, total bits = 256
       Num of add is: (2^{2n}-3)+256/n

       n=1, 257
       n=2, 141
       n=3, 147
       n=4, 317

       n=2 is the best choice.
    */
    pub fn scalarMulExp_win(
        s1: &EmulatedField,
        G1: &Point,
        s2: &EmulatedField,
        G2: &Point,
    ) -> Point {
        /* double and add */
        let mut sum = Point::zero();
        let window_bits = 2;

        let G1_2 = G1.double1().to_affine();
        let G1_3 = G1_2.add1(&G1).to_affine();
        let G2_2 = G2.double1().to_affine();
        let G2_3 = G2_2.add1(&G2).to_affine();
        /*
          s2[1] s1[1] s2[0] s1[0]
        */
        let mut g = Vec::with_capacity(2u32.pow(window_bits * 2) as usize);
        g.push(Point::zero());
        g.push(G1.clone());
        g.push(G2.clone());
        for i in 3..2u32.pow(window_bits * 2) {
            let s0_0 = i & 0x01;
            let s0_1 = (i >> 2) & 0x01;
            let s1_0 = (i >> 1) & 0x01;
            let s1_1 = (i >> 3) & 0x01;

            let s0 = s0_1 * 2 + s0_0;
            let s1 = s1_1 * 2 + s1_0;

            let mut p0 = Point::zero();
            if s0 == 1 {
                p0 = G1.clone();
            }
            if s0 == 2 {
                p0 = G1_2.clone();
            }
            if s0 == 3 {
                p0 = G1_3.clone();
            }

            let mut p1 = Point::zero();
            if s1 == 1 {
                p1 = G2.clone();
            }
            if s1 == 2 {
                p1 = G2_2.clone();
            }
            if s1 == 3 {
                p1 = G2_3.clone();
            }
            g.push(p0.add(&p1).to_affine());
        }

        let mut bits1 = Vec::with_capacity(s1.parameters.LIMBS_NUM);
        let mut bits2 = Vec::with_capacity(s1.parameters.LIMBS_NUM);
        for i in 0..s1.parameters.LIMBS_NUM {
            let bs1 = utils::to_bits(&s1.limbs[i].clone(), s1.clone().limb_size);
            let bs2 = utils::to_bits(&s2.limbs[i].clone(), s2.clone().limb_size);
            for j in 0..bs1.len() {
                bits1.push(bs1[j].clone());
            }
            for j in 0..bs2.len() {
                bits2.push(bs2[j].clone());
            }
        }

        bits1.truncate(256);
        bits2.truncate(256);
        bits1.reverse();
        bits2.reverse();

        for i in (0..bits1.len()).step_by(2) {
            /* select p */
            let p = Point::ternary(
                &bits2[i],
                &Point::ternary(
                    &bits1[i],
                    &Point::ternary(
                        &bits2[i + 1],
                        &Point::ternary(&bits1[i + 1], &g[15].clone(), &g[14].clone()),
                        &Point::ternary(&bits1[i + 1], &g[13].clone(), &g[12].clone()),
                    ),
                    &Point::ternary(
                        &bits2[i + 1],
                        &Point::ternary(&bits1[i + 1], &g[11].clone(), &g[10].clone()),
                        &Point::ternary(&bits1[i + 1], &g[9].clone(), &g[8].clone()),
                    ),
                ),
                &Point::ternary(
                    &bits1[i],
                    &Point::ternary(
                        &bits2[i + 1],
                        &Point::ternary(&bits1[i + 1], &g[7].clone(), &g[6].clone()),
                        &Point::ternary(&bits1[i + 1], &g[5].clone(), &g[4].clone()),
                    ),
                    &Point::ternary(
                        &bits2[i + 1],
                        &Point::ternary(&bits1[i + 1], &g[3].clone(), &g[2].clone()),
                        &Point::ternary(&bits1[i + 1], &g[1].clone(), &g[0].clone()),
                    ),
                ),
            );

            sum = sum.double().double().to_affine();
            sum = sum.add1(&p);
        }

        sum
    }
}

#[test]
fn test_point_g() {
    use k256::elliptic_curve::group::prime::PrimeCurveAffine;
    use k256::elliptic_curve::point::AffineCoordinates;
    use k256::*;

    let g: ProjectivePoint = ProjectivePoint::generator();

    let g2 = g.double();
    let a = AffinePoint::from(g2);
    let mut ax = a.x().to_vec();
    let xb = BigUint::from_bytes_be(&ax);
    let g3 = g.add(&g2);

    println!("g: {:?}", g);
    println!("g2: {:?}", g2);
    println!("g2 affine: {:?}", a);
    println!("g2 affine x: {:?}", xb);
    println!("g3 affine: {:?}", g3.to_affine());
}

#[test]
fn test_point_add() {
    env_logger::init();

    Circuit::reset();
    use k256::elliptic_curve::group::prime::PrimeCurveAffine;
    use k256::elliptic_curve::point::AffineCoordinates;
    use k256::*;

    let p_value = BigUint::parse_bytes(secp256k1_Fp.FP, 16).unwrap();

    //G generator
    let gx1 = BigUint::from_str_radix(
        "79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798",
        16,
    )
    .unwrap();
    let fgx1 =
        EmulatedField::from_BigUint(&gx1, secp256k1_Fp.LIMB_BYTES_NUM, Constant, secp256k1_Fp);
    let gy1 = BigUint::from_str_radix(
        "483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8",
        16,
    )
    .unwrap();
    let fgy1 =
        EmulatedField::from_BigUint(&gy1, secp256k1_Fp.LIMB_BYTES_NUM, Constant, secp256k1_Fp);
    let gz1 = BigUint::from_str_radix("1", 16).unwrap();
    let fgz1 =
        EmulatedField::from_BigUint(&gz1, secp256k1_Fp.LIMB_BYTES_NUM, Constant, secp256k1_Fp);

    log::debug!("x: {:?}, y: {:?}, z: {:?}", fgx1, fgy1, fgz1);
    let G1 = Point {
        x: fgx1.clone(),
        y: fgy1.clone(),
        z: fgz1.clone(),
    };

    //G generator
    let gx2 = BigUint::from_str_radix(
        "c6047f9441ed7d6d3045406e95c07cd85c778e4b8cef3ca7abac09b95c709ee5",
        16,
    )
    .unwrap();
    let fgx2 =
        EmulatedField::from_BigUint(&gx2, secp256k1_Fp.LIMB_BYTES_NUM, Constant, secp256k1_Fp);
    let gy2 = BigUint::from_str_radix(
        "1ae168fea63dc339a3c58419466ceaeef7f632653266d0e1236431a950cfe52a",
        16,
    )
    .unwrap();
    let fgy2 =
        EmulatedField::from_BigUint(&gy2, secp256k1_Fp.LIMB_BYTES_NUM, Constant, secp256k1_Fp);
    let gz2 = BigUint::from_str_radix("1", 16).unwrap();
    let fgz2 =
        EmulatedField::from_BigUint(&gz2, secp256k1_Fp.LIMB_BYTES_NUM, Constant, secp256k1_Fp);

    log::debug!("x: {:?}, y: {:?}, z: {:?}", fgx2, fgy2, fgz2);
    let G2 = Point {
        x: fgx2.clone(),
        y: fgy2.clone(),
        z: fgz2.clone(),
    };

    //0xf9308a019258c31049344f85f89d5229b531c845836f99b08601f113bce036f9, 0x388f7b0f632de8140fe337e62a37f3566500a99934c2231b6cb9fd7584b8e672
    let before = utils::getMemState(false);
    let G3 = G1.add(&G2);
    utils::printMemDiff(&before);
    println!("G3 affine: {:?}", G3.to_affine());

    let og: ProjectivePoint = ProjectivePoint::generator();
    println!("1G - {:?}", &og.to_affine());
    println!("2G - {:?}", &og.double().to_affine());
    println!("3G - {:?}", &og.double().add(&og).to_affine());

    let og3 = og.double().add(&og).to_affine();
    let bog3x = BigUint::from_bytes_be(&og3.x());

    assert_eq!(
        bog3x * G3.z.value.clone().unwrap() * G3.z.value.clone().unwrap() % p_value.clone(),
        G3.x.value.clone().unwrap()
    );

    assert_eq!(Circuit::is_satisfied(), true);

    let circuit = Circuit::eject_assignment_and_reset();
    println!("num constraints: {}", circuit.num_constraints());
    println!("num public: {}", circuit.num_public());
    println!("num private: {}", circuit.num_private());
    println!("num non-zeros: {:?}", circuit.num_nonzeros());
}

#[test]
fn test_point_double() {
    env_logger::init();
    Circuit::reset();
    use k256::elliptic_curve::group::prime::PrimeCurveAffine;
    use k256::elliptic_curve::point::AffineCoordinates;
    use k256::*;

    let p_value = BigUint::from_str_radix(
        "fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f",
        16,
    )
    .unwrap();

    let gx = BigUint::from_str_radix(
        "79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798",
        16,
    )
    .unwrap();
    let fgx = EmulatedField::from_BigUint(&gx, secp256k1_Fp.LIMB_BYTES_NUM, Constant, secp256k1_Fp);
    let gy = BigUint::from_str_radix(
        "483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8",
        16,
    )
    .unwrap();
    let fgy = EmulatedField::from_BigUint(&gy, secp256k1_Fp.LIMB_BYTES_NUM, Constant, secp256k1_Fp);

    let one_value = BigUint::from_str_radix("1", 16).unwrap();
    let one = EmulatedField::from_BigUint(
        &one_value,
        secp256k1_Fp.LIMB_BYTES_NUM,
        Constant,
        secp256k1_Fp,
    );

    let G = Point {
        x: fgx.clone(),
        y: fgy.clone(),
        z: one.clone(),
    };

    let og: ProjectivePoint = ProjectivePoint::generator();
    let ogx = og.to_affine().x();
    let bogx = BigUint::from_bytes_be(&ogx);
    assert_eq!(G.x.value.clone().unwrap(), bogx);

    let og2 = og.double().to_affine();
    let bog2x = BigUint::from_bytes_be(&og2.x());

    let G2 = G.double();
    println!(
        "G2 - {:?}, {:?}",
        G2.x.value.clone().unwrap(),
        G2.y.value.clone().unwrap()
    );
    assert_eq!(
        bog2x * G2.z.value.clone().unwrap() * G2.z.value.clone().unwrap() % p_value.clone(),
        G2.x.value.clone().unwrap()
    );

    assert_eq!(Circuit::is_satisfied(), true);

    let circuit = Circuit::eject_assignment_and_reset();
    println!("num constraints: {}", circuit.num_constraints());
    println!("num public: {}", circuit.num_public());
    println!("num private: {}", circuit.num_private());
    println!("num non-zeros: {:?}", circuit.num_nonzeros());
}

#[test]
fn test_scalar_mul() {
    env_logger::init();
    Circuit::reset();
    use k256::elliptic_curve::group::prime::PrimeCurveAffine;
    use k256::elliptic_curve::point::AffineCoordinates;
    use k256::*;

    let p_value = BigUint::parse_bytes(secp256k1_Fp.FP, 16).unwrap();

    //G generator
    let gx = BigUint::from_str_radix(
        "79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798",
        16,
    )
    .unwrap();
    let fgx = EmulatedField::from_BigUint(&gx, secp256k1_Fp.LIMB_BYTES_NUM, Constant, secp256k1_Fp);
    let gy = BigUint::from_str_radix(
        "483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8",
        16,
    )
    .unwrap();
    let fgy = EmulatedField::from_BigUint(&gy, secp256k1_Fp.LIMB_BYTES_NUM, Constant, secp256k1_Fp);

    let one_value = BigUint::from_str_radix("1", 16).unwrap();
    let one = EmulatedField::from_BigUint(
        &one_value,
        secp256k1_Fp.LIMB_BYTES_NUM,
        Constant,
        secp256k1_Fp,
    );

    log::debug!("x: {:?}, y: {:?}, z: {:?}", fgx, fgy, one);
    let G = Point {
        x: fgx.clone(),
        y: fgy.clone(),
        z: one.clone(),
    };

    let fr_p_value = BigUint::parse_bytes(secp256k1_Fr.FP, 16).unwrap();
    const bytes_num: usize = secp256k1_Fr.LIMB_BYTES_NUM;
    let mut bytes: [u8; bytes_num * 3] = [0; bytes_num * 3];
    for i in 0..bytes_num * 3 {
        bytes[i] = rand::random::<u8>();
    }
    let mut fr_value = BigUint::from_bytes_le(&bytes) % fr_p_value.clone();
    //fr_value = BigUint::from_u128(5).unwrap();
    let fr = EmulatedField::from_BigUint(&fr_value, bytes_num, Private, secp256k1_Fp);

    let result = G.scalarMul(&fr);

    println!(
        "scalar mul result: {:?} -> {:?}",
        fr_value.clone(),
        result.clone()
    );

    let og: ProjectivePoint = ProjectivePoint::generator();
    let mut sbytes: [u8; 32] = [0; 32];
    let fr_bytes = fr_value.to_bytes_le();
    for i in 0..fr_bytes.len() {
        sbytes[31 - i] = fr_bytes[i].clone();
    }

    let scalar = Scalar::from_repr(sbytes.into()).unwrap();
    println!("scalar: {:?}", scalar);
    println!(
        "double - {:?}",
        BigUint::from_bytes_be(&og.double().to_affine().x())
    );
    println!(
        "3G - {:?}",
        BigUint::from_bytes_be(&og.double().add(&og).to_affine().x())
    );
    let sm_result = og.mul(scalar);
    let result_x = sm_result.to_affine().x();
    let bx = BigUint::from_bytes_be(&result_x);
    println!("bx: {:?}, z: {:?}", bx.clone(), result.z.value.clone());

    assert_eq!(
        bx * result.z.value.clone().unwrap() * result.z.value.clone().unwrap() % p_value.clone(),
        result.x.value.clone().unwrap()
    );

    assert_eq!(Circuit::is_satisfied(), true);

    let circuit = Circuit::eject_assignment_and_reset();
    println!("num constraints: {}", circuit.num_constraints());
    println!("num public: {}", circuit.num_public());
    println!("num private: {}", circuit.num_private());
    println!("num non-zeros: {:?}", circuit.num_nonzeros());
}

#[test]
fn test_scalar_mul_exp() {
    env_logger::init();
    let before = utils::getMemState(false);

    Circuit::reset();
    use k256::elliptic_curve::group::prime::PrimeCurveAffine;
    use k256::elliptic_curve::point::AffineCoordinates;
    use k256::*;

    let p_value = BigUint::parse_bytes(secp256k1_Fp.FP, 16).unwrap();

    //G generator
    let gx1 = BigUint::from_str_radix(
        "79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798",
        16,
    )
    .unwrap();
    let fgx1 =
        EmulatedField::from_BigUint(&gx1, secp256k1_Fp.LIMB_BYTES_NUM, Constant, secp256k1_Fp);
    let gy1 = BigUint::from_str_radix(
        "483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8",
        16,
    )
    .unwrap();
    let fgy1 =
        EmulatedField::from_BigUint(&gy1, secp256k1_Fp.LIMB_BYTES_NUM, Constant, secp256k1_Fp);
    let gz1 = BigUint::from_str_radix("1", 16).unwrap();
    let fgz1 =
        EmulatedField::from_BigUint(&gz1, secp256k1_Fp.LIMB_BYTES_NUM, Constant, secp256k1_Fp);

    log::debug!("x: {:?}, y: {:?}, z: {:?}", fgx1, fgy1, fgz1);
    let G1 = Point {
        x: fgx1.clone(),
        y: fgy1.clone(),
        z: fgz1.clone(),
    };

    //4G
    let gx2 = BigUint::from_str_radix(
        "e493dbf1c10d80f3581e4904930b1404cc6c13900ee0758474fa94abe8c4cd13",
        16,
    )
    .unwrap();
    let fgx2 =
        EmulatedField::from_BigUint(&gx2, secp256k1_Fp.LIMB_BYTES_NUM, Constant, secp256k1_Fp);
    let gy2 = BigUint::from_str_radix(
        "51ed993ea0d455b75642e2098ea51448d967ae33bfbdfe40cfe97bdc47739922",
        16,
    )
    .unwrap();
    let fgy2 =
        EmulatedField::from_BigUint(&gy2, secp256k1_Fp.LIMB_BYTES_NUM, Constant, secp256k1_Fp);
    let gz2 = BigUint::from_str_radix("1", 16).unwrap();
    let fgz2 =
        EmulatedField::from_BigUint(&gz2, secp256k1_Fp.LIMB_BYTES_NUM, Constant, secp256k1_Fp);

    log::debug!("x: {:?}, y: {:?}, z: {:?}", fgx2, fgy2, fgz2);
    let G2 = Point {
        x: fgx2.clone(),
        y: fgy2.clone(),
        z: fgz2.clone(),
    };

    let fr_p_value = BigUint::parse_bytes(secp256k1_Fr.FP, 16).unwrap();
    const bytes_num: usize = secp256k1_Fr.LIMB_BYTES_NUM;
    let mut bytes: [u8; bytes_num * 3] = [0; bytes_num * 3];
    for i in 0..bytes_num * 3 {
        bytes[i] = rand::random::<u8>();
    }
    let mut s1_value = BigUint::from_bytes_le(&bytes) % fr_p_value.clone();
    //s1_value = BigUint::from_u128(0x123456789a11112233445).unwrap();
    let s1 = EmulatedField::from_BigUint(&s1_value, bytes_num, Private, secp256k1_Fp);

    for i in 0..bytes_num * 3 {
        bytes[i] = rand::random::<u8>();
    }
    let mut s2_value = BigUint::from_bytes_le(&bytes) % fr_p_value.clone();
    //s2_value = BigUint::from_u128(0x23456789ab232456677).unwrap();
    let s2 = EmulatedField::from_BigUint(&s2_value, bytes_num, Private, secp256k1_Fp);

    let GX = Point::scalarMulExp_win(&s1, &G1, &s2, &G2);

    let og: ProjectivePoint = ProjectivePoint::generator();
    println!("og: {:?}", &og);
    let g4 = og.double().double();
    println!("g4: {:?}", &g4.to_affine());

    let mut s1s: [u8; 32] = [0; 32];
    let s1_bytes = s1_value.to_bytes_le();
    for i in 0..s1_bytes.len() {
        s1s[31 - i] = s1_bytes[i].clone();
    }
    let os1 = Scalar::from_repr(s1s.into()).unwrap();
    println!("scalar 1: {:?}", os1);
    let ogx = og.mul(os1);

    let mut s2s: [u8; 32] = [0; 32];
    let s2_bytes = s2_value.to_bytes_le();
    for i in 0..s2_bytes.len() {
        s2s[31 - i] = s2_bytes[i].clone();
    }
    let os2 = Scalar::from_repr(s2s.into()).unwrap();
    println!("scalar 2: {:?}", os2);
    let og2x = g4.mul(os2);

    let og3 = ogx.add(og2x).to_affine();
    let og3x = BigUint::from_bytes_be(&og3.x());

    println!("checking circuit calcuation result");
    assert_eq!(
        og3x * GX.z.value.clone().unwrap() * GX.z.value.clone().unwrap() % p_value.clone(),
        GX.x.value.clone().unwrap()
    );

    println!("check circuit is satisfied");
    assert_eq!(Circuit::is_satisfied(), true);

    println!("eject assignments");
    let circuit = Circuit::eject_assignment_and_reset();
    println!("num constraints: {}", circuit.num_constraints());
    println!("num public: {}", circuit.num_public());
    println!("num private: {}", circuit.num_private());
    println!("num non-zeros: {:?}", circuit.num_nonzeros());

    utils::printMemDiff(&before);
}

#[test]
fn test_affine_add() {
    env_logger::init();
    let before = utils::getMemState(false);

    Circuit::reset();
    use k256::elliptic_curve::group::prime::PrimeCurveAffine;
    use k256::elliptic_curve::point::AffineCoordinates;
    use k256::*;

    let p_value = BigUint::parse_bytes(secp256k1_Fp.FP, 16).unwrap();

    //G generator
    let gx1 = BigUint::from_str_radix(
        "79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798",
        16,
    )
    .unwrap();
    let fgx1 =
        EmulatedField::from_BigUint(&gx1, secp256k1_Fp.LIMB_BYTES_NUM, Constant, secp256k1_Fp);
    let gy1 = BigUint::from_str_radix(
        "483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8",
        16,
    )
    .unwrap();
    let fgy1 =
        EmulatedField::from_BigUint(&gy1, secp256k1_Fp.LIMB_BYTES_NUM, Constant, secp256k1_Fp);

    log::debug!("x: {:?}, y: {:?}", fgx1, fgy1);
    let G1 = Affine {
        x: fgx1.clone(),
        y: fgy1.clone(),
        inf: Boolean::constant(false),
    };

    //G generator
    let gx2 = BigUint::from_str_radix(
        "c6047f9441ed7d6d3045406e95c07cd85c778e4b8cef3ca7abac09b95c709ee5",
        16,
    )
    .unwrap();
    let fgx2 =
        EmulatedField::from_BigUint(&gx2, secp256k1_Fp.LIMB_BYTES_NUM, Constant, secp256k1_Fp);
    let gy2 = BigUint::from_str_radix(
        "1ae168fea63dc339a3c58419466ceaeef7f632653266d0e1236431a950cfe52a",
        16,
    )
    .unwrap();
    let fgy2 =
        EmulatedField::from_BigUint(&gy2, secp256k1_Fp.LIMB_BYTES_NUM, Constant, secp256k1_Fp);

    log::debug!("x: {:?}, y: {:?}", fgx2, fgy2);
    let G2 = Affine {
        x: fgx2.clone(),
        y: fgy2.clone(),
        inf: Boolean::constant(false),
    };

    //0xf9308a019258c31049344f85f89d5229b531c845836f99b08601f113bce036f9, 0x388f7b0f632de8140fe337e62a37f3566500a99934c2231b6cb9fd7584b8e672
    let before = utils::getMemState(false);
    let G3 = G1.add(&G2);
    utils::printMemDiff(&before);
    println!("G3 affine: {:?}", G3);

    let og: ProjectivePoint = ProjectivePoint::generator();
    println!("1G - {:?}", &og.to_affine());
    println!("2G - {:?}", &og.double().to_affine());
    println!("3G - {:?}", &og.double().add(&og).to_affine());

    let og3 = og.double().add(&og).to_affine();
    let bog3x = BigUint::from_bytes_be(&og3.x());

    assert_eq!(bog3x, G3.x.value.clone().unwrap());

    assert_eq!(Circuit::is_satisfied(), true);
    utils::printMemDiff(&before);

    let circuit = Circuit::eject_assignment_and_reset();
    println!("num constraints: {}", circuit.num_constraints());
    println!("num public: {}", circuit.num_public());
    println!("num private: {}", circuit.num_private());
    println!("num non-zeros: {:?}", circuit.num_nonzeros());

    utils::printMemDiff(&before);
}

#[test]
fn test_affine_double() {
    env_logger::init();
    Circuit::reset();
    use k256::elliptic_curve::group::prime::PrimeCurveAffine;
    use k256::elliptic_curve::point::AffineCoordinates;
    use k256::*;

    let p_value = BigUint::from_str_radix(
        "fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f",
        16,
    )
    .unwrap();

    let gx = BigUint::from_str_radix(
        "79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798",
        16,
    )
    .unwrap();
    let fgx = EmulatedField::from_BigUint(&gx, secp256k1_Fp.LIMB_BYTES_NUM, Constant, secp256k1_Fp);
    let gy = BigUint::from_str_radix(
        "483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8",
        16,
    )
    .unwrap();
    let fgy = EmulatedField::from_BigUint(&gy, secp256k1_Fp.LIMB_BYTES_NUM, Constant, secp256k1_Fp);

    let G = Affine {
        x: fgx.clone(),
        y: fgy.clone(),
        inf: Boolean::constant(false),
    };

    let og: ProjectivePoint = ProjectivePoint::generator();
    let ogx = og.to_affine().x();
    let bogx = BigUint::from_bytes_be(&ogx);
    assert_eq!(G.x.value.clone().unwrap(), bogx);

    let og2 = og.double().to_affine();
    let bog2x = BigUint::from_bytes_be(&og2.x());

    let before = utils::getMemState(false);
    let G2 = G.double();
    utils::printMemDiff(&before);
    println!(
        "G2 - {:?}, {:?}",
        G2.x.value.clone().unwrap(),
        G2.y.value.clone().unwrap()
    );
    assert_eq!(bog2x, G2.x.value.clone().unwrap());

    assert_eq!(Circuit::is_satisfied(), true);

    let circuit = Circuit::eject_assignment_and_reset();
    println!("num constraints: {}", circuit.num_constraints());
    println!("num public: {}", circuit.num_public());
    println!("num private: {}", circuit.num_private());
    println!("num non-zeros: {:?}", circuit.num_nonzeros());
}

#[test]
fn test_affine_scalar_mul_exp() {
    env_logger::init();
    let before = utils::getMemState(false);

    Circuit::reset();
    use k256::elliptic_curve::group::prime::PrimeCurveAffine;
    use k256::elliptic_curve::point::AffineCoordinates;
    use k256::*;

    let p_value = BigUint::parse_bytes(secp256k1_Fp.FP, 16).unwrap();

    //G generator
    let gx1 = BigUint::from_str_radix(
        "79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798",
        16,
    )
    .unwrap();
    let fgx1 =
        EmulatedField::from_BigUint(&gx1, secp256k1_Fp.LIMB_BYTES_NUM, Constant, secp256k1_Fp);
    let gy1 = BigUint::from_str_radix(
        "483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8",
        16,
    )
    .unwrap();
    let fgy1 =
        EmulatedField::from_BigUint(&gy1, secp256k1_Fp.LIMB_BYTES_NUM, Constant, secp256k1_Fp);

    log::debug!("x: {:?}, y: {:?}", fgx1, fgy1);
    let G1 = Affine {
        x: fgx1.clone(),
        y: fgy1.clone(),
        inf: Boolean::constant(false),
    };

    //4G
    let gx2 = BigUint::from_str_radix(
        "e493dbf1c10d80f3581e4904930b1404cc6c13900ee0758474fa94abe8c4cd13",
        16,
    )
    .unwrap();
    let fgx2 =
        EmulatedField::from_BigUint(&gx2, secp256k1_Fp.LIMB_BYTES_NUM, Constant, secp256k1_Fp);
    let gy2 = BigUint::from_str_radix(
        "51ed993ea0d455b75642e2098ea51448d967ae33bfbdfe40cfe97bdc47739922",
        16,
    )
    .unwrap();
    let fgy2 =
        EmulatedField::from_BigUint(&gy2, secp256k1_Fp.LIMB_BYTES_NUM, Constant, secp256k1_Fp);

    log::debug!("x: {:?}, y: {:?}", fgx2, fgy2);
    let G2 = Affine {
        x: fgx2.clone(),
        y: fgy2.clone(),
        inf: Boolean::constant(false),
    };

    let fr_p_value = BigUint::parse_bytes(secp256k1_Fr.FP, 16).unwrap();
    const bytes_num: usize = secp256k1_Fr.LIMB_BYTES_NUM;
    let mut bytes: [u8; bytes_num * 3] = [0; bytes_num * 3];
    for i in 0..bytes_num * 3 {
        bytes[i] = rand::random::<u8>();
    }
    let mut s1_value = BigUint::from_bytes_le(&bytes) % fr_p_value.clone();
    //s1_value = BigUint::from_u128(0x123456789a11112233445).unwrap();
    let s1 = EmulatedField::from_BigUint(&s1_value, bytes_num, Private, secp256k1_Fp);

    for i in 0..bytes_num * 3 {
        bytes[i] = rand::random::<u8>();
    }
    let mut s2_value = BigUint::from_bytes_le(&bytes) % fr_p_value.clone();
    //s2_value = BigUint::from_u128(0x23456789ab232456677).unwrap();
    let s2 = EmulatedField::from_BigUint(&s2_value, bytes_num, Private, secp256k1_Fp);

    let GX = Affine::scalarMulExp_win(&s1, &G1, &s2, &G2);

    let og: ProjectivePoint = ProjectivePoint::generator();
    println!("og: {:?}", &og);
    let g4 = og.double().double();
    println!("g4: {:?}", &g4.to_affine());

    let mut s1s: [u8; 32] = [0; 32];
    let s1_bytes = s1_value.to_bytes_le();
    for i in 0..s1_bytes.len() {
        s1s[31 - i] = s1_bytes[i].clone();
    }
    let os1 = Scalar::from_repr(s1s.into()).unwrap();
    println!("scalar 1: {:?}", os1);
    let ogx = og.mul(os1);

    let mut s2s: [u8; 32] = [0; 32];
    let s2_bytes = s2_value.to_bytes_le();
    for i in 0..s2_bytes.len() {
        s2s[31 - i] = s2_bytes[i].clone();
    }
    let os2 = Scalar::from_repr(s2s.into()).unwrap();
    println!("scalar 2: {:?}", os2);
    let og2x = g4.mul(os2);

    let og3 = ogx.add(og2x).to_affine();
    let og3x = BigUint::from_bytes_be(&og3.x());

    println!("checking circuit calcuation result");
    assert_eq!(og3x, GX.x.value.clone().unwrap());

    println!("check circuit is satisfied");
    assert_eq!(Circuit::is_satisfied(), true);

    utils::printMemDiff(&before);
    println!("eject assignments");
    let circuit = Circuit::eject_assignment_and_reset();
    println!("num constraints: {}", circuit.num_constraints());
    println!("num public: {}", circuit.num_public());
    println!("num private: {}", circuit.num_private());
    println!("num non-zeros: {:?}", circuit.num_nonzeros());
    utils::printMemDiff(&before);
}
