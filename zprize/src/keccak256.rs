use snarkvm_circuit_environment::{prelude::PrimeField, Eject, Environment, Inject, Mode, Zero};
use snarkvm_console_network::prelude::Itertools;
use snarkvm_utilities::biginteger::BigInteger;

// TODO: better to use AleoV0 or Circuit?
use snarkvm_circuit::{Boolean, Circuit as Env, Field};
use snarkvm_circuit_environment::*;
use snarkvm_circuit_environment::Mode::{Constant, Private};
//use snarkvm_circuit::{AleoV0 as Env, Field};

use crate::utils;
use std::cmp;
use std::io;
use std::io::Write;
use snarkvm_utilities::ToBytes;

use snarkvm_console_network::MainnetV0;

//
// Aliases
// =======
//

type F = Field<Env>;

/* Keccark Parameters */
const B: usize = 200;
const NROUNDS: usize = 24;
const RC: [u64; 24] = [
    0x0000000000000001,
    0x0000000000008082,
    0x800000000000808a,
    0x8000000080008000,
    0x000000000000808b,
    0x0000000080000001,
    0x8000000080008081,
    0x8000000000008009,
    0x000000000000008a,
    0x0000000000000088,
    0x0000000080008009,
    0x000000008000000a,
    0x000000008000808b,
    0x800000000000008b,
    0x8000000000008089,
    0x8000000000008003,
    0x8000000000008002,
    0x8000000000000080,
    0x000000000000800a,
    0x800000008000000a,
    0x8000000080008081,
    0x8000000000008080,
    0x0000000080000001,
    0x8000000080008008
];
const ROTC: [usize; 24] = [
    1, 3, 6, 10, 15, 21, 28, 36,
    45, 55, 2, 14, 27, 41, 56, 8,
    25, 43, 62, 18, 39, 61, 20, 44
];
const PIL: [usize; 24] = [
    10, 7, 11, 17, 18, 3, 5, 16,
    8, 21, 24, 4, 15, 23, 19, 13,
    12, 2, 20, 14, 22, 9, 6, 1
];
const M5: [usize; 10] = [
    0, 1, 2, 3, 4, 0, 1, 2, 3, 4
];

thread_local! {
    /*
    pub(super) static F_RC: Vec<F64> = {
        let mut rcs = Vec::with_capacity(RC.len());
        for i in 0..RC.len() {
            let mut rc = F64::zero();
            rc.data.clear();
            for j in 0..8 {
                rc.data.push(F::from(Env::one() * snarkvm_console::types::Field::<MainnetV0>::from_u64((RC[i] >> (8*j)) & 0xff).deref()));
            }
            rc.value = RC[i];
            assert!(rc.checkValue());
            rcs.push(rc);
        }
        rcs
    };
    */
}

/* s: [u64; 25]
 */
#[derive(Clone, Debug)]
pub struct Keccak256 {
    pub state: Vec<F>,
    pub offset: usize,
    can_absorb: bool,  // Can absorb
    can_squeeze: bool,  // Can squeeze
}

/* 64 bits */
#[derive(Clone)]
pub struct F64 {
    pub data: Vec<F>,
    pub value: u64,
}

use std::fmt;
use std::ops::{Add, Deref, Mul};

impl fmt::Debug for F64 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        /*
        write!(f, "F64 :");
        for i in 0..8 {
            let di = self.data[i].eject_value().to_bytes_le().unwrap()[0].clone();
            write!(f, "{:?} ", di);
        }
        */
        write!(f, "{:?}", self.value)
    }
}

impl F64 {
    fn zero() -> F64 {
        let mut data = Vec::with_capacity(8);
        for i in 0..8 {
            data.push(F::zero());
        }

        F64 {
            data,
            value: 0 as u64
        }
    }

    fn from_u64(mode: Mode, value: u64) -> F64 {
        let mut data = Vec::with_capacity(8);
        for i in 0..8 {
            if mode == Constant {
                data.push(F::from(Env::one() * snarkvm_console::types::Field::<MainnetV0>::from_u64((value >> (i * 8)) & 0xff).deref()));
            } else {
                data.push(F::new(mode, snarkvm_console::types::Field::from_u8(((value >> i * 8) & 0xff) as u8)));
            }
        }

        F64 {
            data,
            value: value as u64
        }
    }

    fn checkValue(&self) -> bool {
        log::debug!("check value: {:?} {:?}", &self, &self.data);
        let mut sum: u64 = 0;
        for j in 0..8 {
            let v = (self.data[j].eject_value().to_bytes_le().unwrap()[0] as u64)*2u64.pow(8*j as u32);
            sum += v;
        }

        let mut result = sum == self.value;

        result
    }

    /*
    bytes -> u64
    */
    pub fn read_u64v_le(output: &mut[F64], bytes: &[F], size: usize) {
        log::debug!("read u64: {:?}, len: {:?}", bytes, bytes.len());
        for i in 0..size {
            output[i].data.clear();
            let mut sum: u64 = 0;
            for j in 0..8 {
                output[i].data.push(bytes[i*8+j].clone());
                let data = (bytes[i*8+j].eject_value().to_bytes_le().unwrap()[0] as u64)*2u64.pow(8*j as u32);
                sum += data;
            }
            output[i].value = sum;
        }
        log::debug!("output: {:?}", output);
    }

    /*
    u64 -> bytes
    */
    pub fn write_u64v_le(output: &mut[F], value: &[F64], size: usize) {
        for i in 0..size {
            for j in 0..8 {
                output[i*8+j] = value[i].data[j].clone();
            }
        }
    }

    pub fn xor_F8(a: &F, b: &F) -> F {
        let mut c = F::zero();

        //log::debug!("xor f8: {:?} {:?} {:?} {:?}", a, b, a.eject_value().to_bytes_le().unwrap()[0], b.eject_value().to_bytes_le().unwrap()[0]);

        let table_index = 1usize;
        let fv = F::new(Private, snarkvm_console::types::Field::from_u8(a.eject_value().to_bytes_le().unwrap()[0] ^ b.eject_value().to_bytes_le().unwrap()[0]));
        // Env::enforce_lookup(|| (a, b, &fv, table_index));
        //log::debug!("xor result: {:?}", fv.eject_value());

        fv
    }

    /*
         if key is 8bits, the table size is 16bits. xor_F64 needs 8 constrains.
     */
    pub fn xor_F64(a: &F64, b: &F64) -> F64 {
        let mut c = F64::zero();

        //log::debug!("xor f64: {:?} {:?}", a, b);

        let table_index = 1usize;
        for i in 0..8 {
            let fv = F::new(Private, snarkvm_console::types::Field::from_u8((((a.value >> (i*8))&0xff) ^ ((b.value >> (i*8))&0xff)) as u8));
            // Env::enforce_lookup(|| (a.data.get(i).unwrap(), b.data.get(i).unwrap(), &fv, table_index));
            c.data[i] = fv;
        }
        c.value = a.value ^ b.value;
        //log::debug!("xor result: {:?}", c.value);

        c
    }

    pub fn and_F64(a: &F64, b: &F64) -> F64 {
        let mut c = F64::zero();

        let table_index = 2usize;
        for i in 0..8 {
            let fv = F::new(Private, snarkvm_console::types::Field::from_u8((((a.value >> (i*8))&0xff) & ((b.value >> (i*8))&0xff)) as u8));
            // Env::enforce_lookup(|| (a.data.get(i).unwrap(), b.data.get(i).unwrap(), &fv, table_index));
            c.data[i] = fv;
        }
        c.value = a.value & b.value;

        c
    }

    pub fn inv_F64(a: &F64) -> F64 {
        let mut c = F64::zero();

        let zero = F::zero();
        let table_index = 3usize;
        for i in 0..8 {
            let fv = F::new(Private, snarkvm_console::types::Field::from_u8(!(((a.value >> (i*8))&0xff) as u8)));
            // Env::enforce_lookup(|| (a.data.get(i).unwrap(), &zero, &fv, table_index));
            c.data[i] = fv;
        }
        c.value = !a.value;

        c
    }

    pub fn add_lookup_tables() {
        for offset in 0..4 {
            for i in 0..RC.len() {
                // utils::add_rotl_tables(ROTC[i], offset);
            }
        }
    }

    /*
        use lookup table for rotl
    */
    pub fn rotl_F64(a: &F64, n: usize, rc_index: usize) -> F64 {
        //log::debug!("rotl64: {:?} {:?} {:?}", a, a.data, n);
        let exp_result = ((a.value.clone() << (n % 64)) & 0xffffffffffffffff) ^ (a.value.clone() >> (64 - (n % 64)));
        let result = F64::from_u64(Private, exp_result);

        //check table
        let mut sum = F::zero();
        for i in 0..4 {
            let v16 = utils::rotl_16((a.value >> (i*16)) as u16, i, n);
            let fv = F::new(Private, snarkvm_console::types::Field::from_u64(v16));
            let table_index = 4+i*RC.len()+rc_index;
            // Env::enforce_lookup(|| (a.data.get(i*2).unwrap(), a.data.get(i*2+1).unwrap(), &fv, table_index));
            sum += &fv;
        }

        let mut fsum = Env::zero();

        for i in 0..8 {
            fsum += &result.data.get(i).unwrap().linear_combination * utils::COEFFS[8*i].deref();;
        }

        Env::assert_eq(sum, fsum);

        result
    }

    pub fn rotl_F64_native(a: &F64, n: usize) -> F64 {
        //log::debug!("rotl64: {:?} {:?} {:?}", a, a.data, n);
        //let exp_result = ((a.value.clone() << (n % 64)) & 0xffffffffffffffff) ^ (a.value.clone() >> (64 - (n % 64)));

        let mut bits = Vec::with_capacity(a.data.len());
        for i in 0..a.data.len() {
            let mut bbits = utils::to_bits(&a.data[i], 1);
            bits.append(&mut bbits);
        }

        bits.truncate(64);
        let mut obits = Vec::with_capacity(8);
        let mut result = F64::zero();
        result.data.clear();
        let mut sum: u64  = 0;
        for t in 0..64 {
            let i = (t + 64 - n) % 64;
            obits.push(bits[i].clone());

            if bits[i].clone().eject_value() {
               sum += 2u64.pow(t as u32);
            }
            if (t+1) % 8 == 0 {
                //log::debug!("t: {:?} -> {:?}", t, &obits);
                result.data.push(F::from_bits_le(&obits));
                obits.clear();
            }
        }
        result.value = sum;

        //assert_eq!(sum, exp_result);
        //assert!(result.checkValue());

        //log::debug!("rotl64 result: {:?}", result);
        result
    }
}

/*
impl Inject for Keccark256 {
    type Primitive = Vec<Vec<bool>>;

    fn new(mode: Mode, state: Self::Primitive) -> Self {
        Keccark256 {
           state: state.iter().map( | s| {
                F::(mode, f)
              }).collect_vec()
        }
    }
}

impl Eject for Keccark256 {
    type Primitive = Vec<u8>;

    fn eject_mode(&self) -> Mode {
        self.state[0].eject_mode()
    }

    fn eject_value(&self) -> Self::Primitive {
        self.state
            .iter()
            .map(|s| {
                let f = s.eject_value();
                let big = f.to_bigint();
                let res = big.to_biguint().to_bytes_le();
                assert_eq!(res.len(), 1);
                res[0]
            })
            .collect_vec()
    }
}
*/

impl Keccak256 {
    pub fn new() -> Keccak256 {
        let mut s = Vec::with_capacity(B);
        let mut fz = F::zero();
        for i in 0..B {
            s.push(fz.clone());
        }
        Keccak256{
            state: s,
            offset: 0,
            can_absorb: true,
            can_squeeze: true,
        }
    }

    /* keccark f function */
    pub fn keccak_f(&mut self) {
        let mut sv = vec![F64::zero(); 25];
        let mut tv = vec![F64::zero(); 1];
        let mut cv = vec![F64::zero(); 5];
        let mut s = sv.as_mut_slice();  // [u64; 25]
        let mut t = tv.as_mut_slice();  // [u64; 1]
        let mut c = cv.as_mut_slice();  // [u64; 5]

        log::debug!("-> state: {:?}, len: {:?}", &self.state, &self.state.len());

        F64::read_u64v_le(&mut s, &self.state, B/8);

        log::debug!("->s: {:?}", s);
        log::debug!("->t: {:?}", t);
        log::debug!("->c: {:?}", c);

        for round in 0..NROUNDS {
            // Theta
            for x in 0..5 {
                //c[x] = s[x] ^ s[5 + x] ^ s[10 + x] ^ s[15 + x] ^ s[20 + x];
                c[x] = F64::xor_F64(&F64::xor_F64(&F64::xor_F64(&F64::xor_F64(&s[x], &s[x + 5]), &s[x + 10]), &s[x + 15]), &s[x + 20]);
            }
            for x in 0..5 {
                //t[0] = c[M5[x + 4]] ^ rotl64(c[M5[x + 1]], 1);
                t[0] = F64::xor_F64(&c[M5[x + 4]], &F64::rotl_F64(&c[M5[x + 1]], 1, 0));
                for y in 0..5 {
                    s[y*5 + x] = F64::xor_F64(&s[y*5 + x], &t[0]);
                }
            }

            log::debug!("round: {:?} ->t: {:?}", round, t);
            log::debug!("round: {:?} ->c: {:?}", round, c);

            // Rho Pi
            t[0] = s[1].clone();
            for x in 0..24 {
                c[0] = s[PIL[x]].clone();
                s[PIL[x]] = F64::rotl_F64(&t[0], ROTC[x], x);
                t[0] = c[0].clone();
            }

            // Chi
            for y in 0..5 {
                for x in 0..5 {
                    c[x] = s[y*5+x].clone();
                }
                for x in 0..5 {
                    s[y * 5 + x] = F64::xor_F64(&c[x], &F64::and_F64(&F64::inv_F64(&c[M5[x + 1]]), &c[M5[x + 2]]));
                }
            }

            // Iota
            let rc = F64::from_u64(Constant, RC[round]);
            s[0] = F64::xor_F64(&s[0], &rc);

            log::debug!("round: {:?} ->s: {:?}", round, s);
        }

        log::debug!("<-s: {:?}", &s);
        F64::write_u64v_le(&mut self.state, &s,  B/8);
    }

    fn rate(&self) -> usize {
        B - 64
    }

    pub fn input(&mut self, data: &Vec<F>) {
        if !self.can_absorb {
            panic!("Invalid state, absorb phase already finalized.");
        }

        let r = self.rate();
        assert!(self.offset < r);

        let in_len = data.len();
        let mut in_pos: usize = 0;

        // Absorb
        while in_pos < in_len {
            let offset = self.offset;
            let nread = cmp::min(r - offset, in_len - in_pos);
            for i in 0..nread {
                //self.state[offset + i] = self.state[offset + i] ^ data[in_pos + i];
                self.state[offset + i] = F64::xor_F8(&self.state[offset + i], &data[in_pos + i]);
            }
            in_pos += nread;

            if offset + nread != r {
                self.offset += nread;
                break;
            }

            self.offset = 0;
            self.keccak_f();
        }
    }

    pub fn digest_length(&self) -> usize {
        32
    }

    pub fn output_bits(&self) -> usize {
        self.digest_length()* 8
    }

    fn finalize(&mut self) {
        assert!(self.can_absorb);

        let ds_len = 0;

        fn set_domain_sep(out_len: usize, buf: &mut [u8]) {
            assert!(buf.len() > 0);
            if out_len != 0 {
                // 01...
                buf[0] &= 0xfe;
                buf[0] |= 0x2;
            } else {
                // 1111...
                buf[0] |= 0xf;
            }
        }

        // All parameters are expected to be in bits.
        fn pad_len(ds_len: usize, offset: usize, rate: usize) -> usize {
            assert!(rate % 8 == 0 && offset % 8 == 0);
            let r: i64 = rate as i64;
            let m: i64 = (offset + ds_len) as i64;
            let zeros = (((-m - 2) + 2 * r) % r) as usize;
            assert!((m as usize + zeros + 2) % 8 == 0);
            (ds_len as usize + zeros + 2) / 8
        }

        fn set_pad(offset: usize, buf: &mut [u8]) {
            assert!(buf.len() as f32 >= ((offset + 2) as f32 / 8.0).ceil());
            let s = offset / 8;
            let buflen = buf.len();
            buf[s] |= 1 << (offset % 8);
            for i in (offset % 8) + 1..8 {
                buf[s] &= !(1 << i);
            }
            for i in s + 1..buf.len() {
                buf[i] = 0;
            }
            buf[buflen - 1] |= 0x80;
        }

        let p_len = pad_len(ds_len, self.offset * 8, self.rate() * 8);

        let mut p: Vec<u8> = vec![0; p_len];

        if ds_len != 0 {
            set_domain_sep(self.output_bits(), &mut p);
        }

        set_pad(ds_len, &mut p);

        let mut fp: Vec<F> = Vec::with_capacity(p.len());
        for i in 0..p.len() {
            fp.push(F::from(Env::one() * snarkvm_console::types::Field::<MainnetV0>::from_u8(p[i].clone()).deref()));
        }

        self.input(&fp);
        self.can_absorb = false;
    }

    pub fn result(&mut self, out: &mut [F]) {
        if !self.can_squeeze {
            panic!("Nothing left to squeeze.");
        }

        if self.can_absorb {
            self.finalize();
        }

        let r = self.rate();
        let out_len = self.digest_length();
        if out_len != 0 {
            assert!(self.offset < out_len);
        } else {
            assert!(self.offset < r);
        }

        let in_len = out_len;
        let mut in_pos: usize = 0;

        // Squeeze
        while in_pos < in_len {
            let offset = self.offset % r;
            let mut nread = cmp::min(r - offset, in_len - in_pos);
            if out_len != 0 {
                nread = cmp::min(nread, out_len - self.offset);
            }

            for i in 0..nread {
                out[in_pos + i] = self.state[offset + i].clone();
            }
            in_pos += nread;

            if offset + nread != r {
                self.offset += nread;
                break;
            }

            if out_len == 0 {
                self.offset = 0;
            } else {
                self.offset += nread;
            }

            self.keccak_f();
        }

        if out_len != 0 && out_len == self.offset {
            self.can_squeeze = false;
        }
    }
}

#[test]
fn test_keccak256_hash() {
    env_logger::init();
    let before = utils::getMemState(false);

    Circuit::reset();

    extern crate crypto;
    use crypto::digest::Digest;
    use crypto::sha3::Sha3;

    const msg_len: usize = 10000;
    let mut msg = vec![0u8; msg_len];
    for i in 0..msg_len {
        msg[i] = rand::random::<u8>();
    }

    let mut hasher = Sha3::keccak256();
    hasher.input(&msg);
    let mut hex_bytes: [u8; 32] = [0; 32];
    //let hex = hasher.result_str();
    //println!("hash hex: {:?}", hex);
    hasher.result(&mut hex_bytes);
    println!("hash bytes: {:?}", hex_bytes);

    let mut fmsg = Vec::with_capacity(msg_len);
    for i in 0..msg_len {
        fmsg.push(F::new(Private, snarkvm_console::types::Field::from_u128(msg[i] as u128)));
    }
    let mut kk = Keccak256::new();
    kk.input(&fmsg);

    let mut hash=  vec![F::zero(); 32];
    kk.result(&mut hash.as_mut_slice());
    println!("circuit hash: {:?}", hash);

    //check hash result
    for i in 0..32 {
        assert_eq!(snarkvm_console::types::Field::from_u8(hex_bytes[i] as u8), hash[i].eject_value());
    }

    utils::printMemDiff(&before);

    assert_eq!(Circuit::is_satisfied(), true);

    let circuit = Circuit::eject_assignment_and_reset();
    println!("num constraints: {}", circuit.num_constraints());
    println!("num public: {}", circuit.num_public());
    println!("num private: {}", circuit.num_private());
    println!("num non-zeros: {:?}", circuit.num_nonzeros());

    use snarkvm_circuit::prelude::snarkvm_fields::Zero;
    //check number of private variable with 0
    let mut num = 0;
    circuit.private_inputs().iter().for_each(|v| {if v.value().is_zero() {num += 1}});
    // for k in keys {
    //     let v = circuit.private_inputs().get(k).unwrap();
    //     //println!("key: {:?}, value: {:?}", k, v);
    //    if v.0.is_zero() {
    //        num += 1;
    //    }
    // }
    println!("num of 0 in privates: {:?}", num);

    utils::printMemDiff(&before);
}

#[test]
fn test_verify_rotl() {
    let mut value: u64 = 0;
    for i in 0..8 {
       let bv = rand::random::<u8>();
        value += bv as u64 *2u64.pow(i*8);
    }

    for i in 0..64 {
        let n = i;

        let exp_result = ((value << (n % 64)) & 0xffffffffffffffff) ^ (value >> (64 - (n % 64)));

        let mut sum: u128 = 0;
        for j in 0..4 {
            let v16 = (value >> (j*16)) & 0xffff;
            sum += utils::rotl_16(v16 as u16, j, n) as u128;
        }

        if exp_result as u128 != sum {
            println!("value: {:?}, n: {:?}, sum: {:?}, expected: {:?}", value, n, sum, exp_result);
        }

        assert_eq!(exp_result as u128, sum);
    }
}
