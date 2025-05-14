use std::fs::File;
use std::ops::{Add, BitAnd, BitOr, Deref, Mul, Shr};
use snarkvm_circuit_environment::{prelude::PrimeField, Eject, Environment, Inject, Mode, ToBits};
use snarkvm_console_network::prelude::Itertools;
use snarkvm_utilities::biginteger::BigInteger;

// TODO: better to use AleoV0 or Circuit?
use snarkvm_circuit::{Boolean, Circuit, Field};
use snarkvm_circuit_environment::*;
use snarkvm_circuit_environment::Mode::{Constant, Private};
use snarkvm_utilities::{ToBytes};

use num_bigint::*;
use snarkvm_circuit::prelude::num_traits::{Num, FromPrimitive, ToPrimitive};
use snarkvm_console::account::FromBytes;

use rayon::iter::{IntoParallelIterator, ParallelIterator};

use std::time::{Duration, Instant};

type F = Field<Circuit>;

use core::{cell::RefCell};
use std::rc::Rc;
use snarkvm_console_network::MainnetV0;

use lazy_static::*;

lazy_static! {
    pub static ref COEFFS: Vec<snarkvm_console::types::Field::<MainnetV0>> = {
        let mut coeffs = Vec::with_capacity(256);
        for i in 0..256 {
           let coeff = snarkvm_console::types::Field::<MainnetV0>::from_u128(2u128.pow(i as u32));
           coeffs.push(coeff);
        }
        coeffs
    };
}

pub fn to_bits(v: &F, len: usize) -> Vec<Boolean<Circuit>> {
    use snarkvm_utilities::ToBits;

    let mut bbits = Vec::with_capacity(len*8);

    let value = BigUint::from_bytes_le(&v.eject_value().to_bytes_le().unwrap());
    log::trace!("to bits: {:?} -> {:?} with len: {:?}", v.eject_value(), value, len);

    let bv = v.eject_value().to_bytes_le().unwrap();
    let mut sum = Circuit::zero();

    for i in 0..len {
        let bv_bits = bv[i].to_bits_le();
        for j in 0..8 {
            let bB = Boolean::new(v.eject_mode(), bv_bits[j].clone());
            let bF = Field::from_boolean(&bB);
            sum += (&bF.linear_combination) * COEFFS[8*i+j].deref();;

            bbits.push(bB);
        }
    }

    Circuit::assert_eq(sum, v);

    bbits
}

pub fn to_bytes_withv(v: &F, len: usize) -> (Vec<F>, Vec<u8>) {
    let mut bytes = Vec::with_capacity(len);
    let bv = v.eject_value().to_bytes_le().unwrap();

    let mut sum = Circuit::zero();
    for i in 0..len {
        let bF = F::new(v.eject_mode(), snarkvm_console::types::Field::from_u8(bv[i] as u8));
        sum += (&bF.linear_combination) * COEFFS[8*i].deref();
        bytes.push(bF);
    }

    Circuit::assert_eq(sum, v);

    (bytes, bv)
}

pub fn to_bytes(v: &F, len: usize) -> Vec<F> {
    let mut bytes = Vec::with_capacity(len);
    let bv = v.eject_value().to_bytes_le().unwrap();

    let mut sum = Circuit::zero();
    for i in 0..len {
        let bF = F::new(v.eject_mode(), snarkvm_console::types::Field::from_u16(bv[i].clone() as u16));
        sum += (&bF.linear_combination) * COEFFS[8*i].deref();
        bytes.push(bF);
    }

    Circuit::assert_eq(sum, v);

    bytes
}

/* using lookup table to do the comparison */
pub fn is_less_than(a: &F, b: &F, num_bytes: usize) -> Boolean<Circuit>{
    to_bytes_withv(a, num_bytes);
    to_bytes_withv(b, num_bytes);
    a.is_less_than(b)
}

/* use overflow to check less than logic */
pub fn is_less_than_constant(a: &F, b: &F, len: usize) -> Boolean<Circuit> {
    let limb_max = Circuit::one() * COEFFS[8*len].deref();
    let add_result = a + F::from(limb_max) - b;

    let (_, high) = splitField(&add_result, len, 1);

    let highv = high.eject_value().to_bytes_le().unwrap();

    let high_bit = F::new(high.eject_mode(), snarkvm_console::types::Field::from_u8(highv[0]));
    high_bit.is_equal(&F::zero())
}

pub fn is_less_than_limb(a: &F, len: usize, pown: usize) -> Boolean<Circuit> {
    let (a_bytes, _) = to_bytes_withv(a, len);

    // Ensure the max byte is less than b.
    let b = F::new(Private, snarkvm_console::types::Field::from_u8(2u8.pow(pown as u32)));
    a_bytes[len-1].is_less_than(&b)
}

pub fn splitField(v: &F, pos: usize, extra: usize) -> (F, F) {
    let bv = v.eject_value().to_bytes_le().unwrap();
    let mut lowV = 0u128;
    let mut highV = 0u128;

    for i in 0..pos {
        lowV += (bv[i] as u128) * 2u128.pow((8*i) as u32);
    }
    for i in 0..extra {
        highV += (bv[pos+i] as u128) * 2u128.pow((8*i) as u32);
    }

    let  lowF = F::new(v.eject_mode(), snarkvm_console::types::Field::from_u128(lowV));
    let  highF = F::new(v.eject_mode(), snarkvm_console::types::Field::from_u128(highV));

    let mut sum = Circuit::zero();
    sum += &lowF.linear_combination;
    sum += &highF.linear_combination * COEFFS[8*pos].deref();
    Circuit::assert_eq(sum, v);

    (lowF, highF)
}

// use snarkvm_algorithms::r1cs::LookupTable;
// use snarkvm_console::account::de::Unexpected::Bool;
// pub fn add_comp_table() {
//     /* less comparsion table */
//     let mut lookup_table = LookupTable::default();

//     for i in 0..256 {
//         for j in 0..256 {
//             let key0 =  snarkvm_console::types::Field::<MainnetV0>::from_u16(i as u16);
//             let key1 =  snarkvm_console::types::Field::<MainnetV0>::from_u16(j as u16);
//             if i < j {
//                 lookup_table.fill([key0.deref().clone(), key1.deref().clone()], Circuit::one().value());
//             } else {
//                 lookup_table.fill([key0.deref().clone(), key1.deref().clone()], Circuit::zero().value());
//             }
//         }
//     }
//     Circuit::add_lookup_table(lookup_table);
// }

// pub fn add_xor_table() {
//     /* less comparsion table */
//     let mut lookup_table = LookupTable::default();

//     for i in 0..256 {
//         for j in 0..256 {
//             let key0 = snarkvm_console::types::Field::<MainnetV0>::from_u16(i as u16);
//             let key1 =  snarkvm_console::types::Field::<MainnetV0>::from_u16(j as u16);
//             let result = snarkvm_console::types::Field::<MainnetV0>::from_u8((i ^ j) as u8);
//             lookup_table.fill([key0.deref().clone(), key1.deref().clone()], result.deref().clone());
//         }
//     }
//     Circuit::add_lookup_table(lookup_table);
// }

// pub fn add_and_table() {
//     /* less comparsion table */
//     let mut lookup_table = LookupTable::default();

//     for i in 0..256 {
//         for j in 0..256 {
//             let key0 = snarkvm_console::types::Field::<MainnetV0>::from_u16(i as u16);
//             let key1 =snarkvm_console::types::Field::<MainnetV0>::from_u16(j as u16);
//             let result = snarkvm_console::types::Field::<MainnetV0>::from_u8((i & j) as u8);
//             lookup_table.fill([key0.deref().clone(), key1.deref().clone()], result.deref().clone());
//         }
//     }
//     Circuit::add_lookup_table(lookup_table);
// }

// pub fn add_inv_table() {
//     /* less comparsion table */
//     let mut lookup_table = LookupTable::default();

//     for i in 0..256 {
//         for j in 0..256 {
//             let key0 = snarkvm_console::types::Field::<MainnetV0>::from_u16(i as u16);
//             let result = snarkvm_console::types::Field::<MainnetV0>::from_u8((!i) as u8);
//             lookup_table.fill([key0.deref().clone(), Circuit::zero().value()], result.deref().clone());
//         }
//     }
//     Circuit::add_lookup_table(lookup_table);
// }


pub fn rotl_16(data: u16, offset: usize, n: usize) -> u64 {
    let value = data as u64 * 2u64.pow((offset*16) as u32);
    ((value << (n % 64)) & 0xffffffffffffffff) ^ (value >> (64 - (n % 64)))
}

/* offset: 0~3 */
// pub fn add_rotl_tables(n: usize, offset: usize) {
//     let mut lookup_table = LookupTable::default();

//     for i in 0..256 {
//         for j in 0..256 {
//             let key0 = snarkvm_console::types::Field::<MainnetV0>::from_u8(i as u8);
//             let key1 = snarkvm_console::types::Field::<MainnetV0>::from_u8(j as u8);
//             let result = snarkvm_console::types::Field::<MainnetV0>::from_u64(rotl_16(i+j<<8, offset, n));
//             lookup_table.fill([key0.deref().clone(), key1.deref().clone()], result.deref().clone());
//         }
//     }
//     Circuit::add_lookup_table(lookup_table);
// }

/* add all tables */
pub fn add_tables() {
    // add_comp_table(); //0
    // add_xor_table();  //1
    // add_and_table();  //2
    // add_inv_table();  //3
}

use memory_stats::{memory_stats, MemoryStats};
pub fn getMemState(display: bool) -> Option<MemoryStats> {
    let state = memory_stats();

    if display {
        let mem = state.unwrap();
        println!("Current physical memory usage: {}K", (mem.physical_mem)/1024);
        println!("Current virtual memory usage: {}K", (mem.virtual_mem)/1024);
    }
    state
}

pub fn printMemDiff(stat: &Option<MemoryStats>) {
    let usage_before = stat.unwrap();

    let usage_after = memory_stats().unwrap();
    println!("Physical memory usage: {}K", (usage_after.physical_mem - usage_before.physical_mem)/1024);
    //println!("Current virtual memory usage: {}K", (usage_after.virtual_mem - usage_before.virtual_mem)/1024);
}

#[test]
fn test_to_bits() {
    env_logger::init();

    Circuit::reset();

    let p_value = BigUint::from_str_radix("fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f", 16).unwrap();

    let mut bytes: [u8; 11] = [0; 11];
    for i in 0..11 {
        bytes[i] = rand::random::<u8>();
    }
    let mut a_value = BigUint::from_bytes_le(&bytes);

    //a_value = BigUint::from_u128(10).unwrap();
    println!("a: {:?}", a_value);

    let aF = F::new(Private, snarkvm_console::types::Field::from_u128(a_value.to_u128().unwrap()));
    let result = to_bits(&aF, 11);

    for i in 0..result.len() {
        let bit = a_value.bit(i as u64);
        assert_eq!(bit, result[i].eject_value());
    }
    println!("to bits result: {:?}", result);

    assert_eq!(Circuit::is_satisfied(), true);

    let circuit = Circuit::eject_assignment_and_reset();
    println!("num constraints: {}", circuit.num_constraints());
    println!("num public: {}", circuit.num_public());
    println!("num private: {}", circuit.num_private());
    println!("num non-zeros: {:?}", circuit.num_nonzeros());
}

#[test]
fn test_less_than() {
    env_logger::init();
    let start = getMemState(false);

    Circuit::reset();

    let p_value = BigUint::from_str_radix("fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f", 16).unwrap();

    let mut bytes: [u8; 11] = [0; 11];
    for i in 0..11 {
        bytes[i] = rand::random::<u8>();
    }
    let mut a_value = BigUint::from_bytes_le(&bytes);
    //let a_value = BigUint::from_str_radix("123456", 16).unwrap();

    for i in 0..11 {
        bytes[i] = rand::random::<u8>();
    }
    let mut b_value = BigUint::from_bytes_le(&bytes);
    //let b_value = BigUint::from_str_radix("123457", 16).unwrap();

    println!("a: {:?}, b: {:?}, is_less: {:?}", a_value, b_value, a_value < b_value);

    let aF = F::new(Private, snarkvm_console::types::Field::from_u128(a_value.to_u128().unwrap()));
    let bF = F::new(Private, snarkvm_console::types::Field::from_u128(b_value.to_u128().unwrap()));
    let result = is_less_than(&aF, &bF, 11);
    println!("less result: {:?}", result.eject_value());

    assert_eq!(result.eject_value(), (a_value < b_value));

    assert_eq!(Circuit::is_satisfied(), true);

    printMemDiff(&start);

    let circuit = Circuit::eject_assignment_and_reset();
    println!("num constraints: {}", circuit.num_constraints());
    println!("num public: {}", circuit.num_public());
    println!("num private: {}", circuit.num_private());
    println!("num non-zeros: {:?}", circuit.num_nonzeros());
}

#[test]
fn test_split_field() {
    env_logger::init();

    Circuit::reset();

    const len: u8 = 15;
    let mut bytes: [u8; len as usize] = [0; len as usize];
    for i in 0..len {
        bytes[i as usize] = rand::random::<u8>();
    }
    let mut a_value = BigUint::from_bytes_le(&bytes);

    println!("a: {:?}", a_value);

    let aF = F::new(Private, snarkvm_console::types::Field::from_u128(a_value.to_u128().unwrap()));

    let (low, high) = splitField(&aF, 11, (len-11) as usize);
    println!("split result: {:?} {:?}", low.eject_value(), high.eject_value());

    let coeff = BigUint::from_u128(256u128.pow(11 as u32)).unwrap();
    let lowb = BigUint::from_bytes_le(&low.eject_value().to_bytes_le().unwrap());
    let highb = BigUint::from_bytes_le(&high.eject_value().to_bytes_le().unwrap());
    assert_eq!(lowb + highb*coeff, a_value);

    assert_eq!(Circuit::is_satisfied(), true);

    let circuit = Circuit::eject_assignment_and_reset();
    println!("num constraints: {}", circuit.num_constraints());
    println!("num public: {}", circuit.num_public());
    println!("num private: {}", circuit.num_private());
    println!("num non-zeros: {:?}", circuit.num_nonzeros());
}
