use num_bigint::BigUint;
use snarkvm_circuit_environment::{prelude::PrimeField, Eject, Environment, Inject, Mode, Zero};
use snarkvm_console_network::prelude::Itertools;
use snarkvm_utilities::biginteger::BigInteger;
use std::ops::{Add, Deref, Sub};

// TODO: better to use AleoV0 or Circuit?
use snarkvm_circuit::environment::prelude::num_traits::One;
use snarkvm_circuit::{Circuit as Env, Field, sha2::Sha2_256, ripemd160::Ripemd160, Boolean, Hash};
use snarkvm_utilities::{FromBits, ToBits, ToBytes};
//use snarkvm_circuit::{AleoV0 as Env, Field};

use crate::ecc_secp256k1::Affine;
use crate::emulated_field::{secp256k1_Fp, secp256k1_Fr, EmulatedField};
use snarkvm_circuit_environment::Mode::Private;

use snarkvm_circuit::prelude::num_traits::FromPrimitive;
use snarkvm_console_network::Network;
//
// Aliases
// =======
//

type F = Field<Env>;

type Bool = Boolean<Env>;

//
// Data structures
// ===============
//
// We use the Bls12_377 curve to instantiate Varuna.
// This means that the circuit field (Fr) is modulo the following prime:
//
// 8444461749428370424248824938781546531375899335154063827935233455917409239041
//
// To verify ECDSA signatures with the secp256k1 curve,
// we have to handle scalar field and base field elements:
//
// - scalar field: 115792089237316195423570985008687907852837564279074904382605163141518161494337
// - base field: 115792089237316195423570985008687907853269984665640564039457584007908834671663
//
// Both of these are larger than our circuit field.
// While both the secp256k1 fields are 256 bits, the Bls12_377 circuit field is 253 bits.
// So this means we'll have to cut things up.
//
// Since the job is really on you to figure out how to optimize sutff,
// we use a super naive way to encode things: 1 field = 1 byte.
//

///
#[derive(Debug, Clone)]
pub struct ECDSAPublicKey {
    pub bytes: Vec<F>,
}

/// The signature to be signed in byte representation.
#[derive(Debug, Clone)]
pub struct ECDSASignature {
    bytes: Vec<F>,
}

/// The message to be signed in circuit BE bit representation (so that it can be hashed by the Sha256 gadget).
#[derive(Debug, Clone)]
pub struct Message {
    pub bits: Vec<Bool>,
}

impl Deref for Message {
    type Target = Vec<Bool>;

    fn deref(&self) -> &Self::Target {
        &self.bits
    }
}

//
// Trait implementations
// =====================
//

impl Inject for Message {
    type Primitive = Vec<u8>;

    fn new(mode: Mode, message: Self::Primitive) -> Self {
        match mode {
            // we'd have to constrain things to be bytes
            Mode::Private => unimplemented!(),
            Mode::Constant | Mode::Public => Message {
                bits: message
                    .iter()
                    .flat_map(|b| {
                        b.to_bits_be().into_iter().map(|b| {
                            Bool::new(mode, b)
                        })
                    })
                    .collect_vec(),
            },
        }
    }
}

impl Eject for Message {
    type Primitive = Vec<u8>;

    fn eject_mode(&self) -> Mode {
        self.bits[0].eject_mode()
    }

    fn eject_value(&self) -> Self::Primitive {
        self.bits
            .iter()
            .chunks(8)
            .into_iter()
            .map(|b| {
                let bits = b.into_iter().map(|b| {
                    b.eject_value()
                }).collect::<Vec<bool>>();
                u8::from_bits_be(&bits).unwrap()
            })
            .collect_vec()
    }
}

impl Inject for ECDSAPublicKey {
    type Primitive = super::console::ECDSAPublicKey;

    fn new(mode: Mode, public_key: Self::Primitive) -> Self {
        match mode {
            // might have to check point size
            Mode::Private => unimplemented!(),
            Mode::Constant | Mode::Public => {
                let public_key = public_key
                    .public_key
                    .to_encoded_point(false)
                    .as_bytes()
                    .iter()
                    .skip(1) //skip tag
                    .map(|b| {
                        let f = snarkvm_console::types::Field::from_u8(*b);
                        F::new(mode, f)
                    })
                    .collect_vec();
                Self { bytes: public_key }
            }
        }
    }
}

impl Eject for ECDSAPublicKey {
    type Primitive = super::console::ECDSAPublicKey;

    fn eject_mode(&self) -> Mode {
        self.bytes[0].eject_mode()
    }

    fn eject_value(&self) -> Self::Primitive {
        let mut res = self
            .bytes
            .iter()
            .map(|b| {
                let f = b.eject_value();
                let big = f.to_bigint();
                let res = big.to_biguint().to_bytes_le();
                assert_eq!(res.len(), 1);
                res[0]
            })
            .collect_vec();
        res.insert(0, 0x04); //add tag
        let encoded_pubkey = k256::EncodedPoint::from_bytes(res).unwrap();
        let public_key = k256::ecdsa::VerifyingKey::from_encoded_point(&encoded_pubkey).unwrap();
        Self::Primitive { public_key }
    }
}

impl Inject for ECDSASignature {
    type Primitive = super::console::ECDSASignature;

    fn new(mode: Mode, signature: Self::Primitive) -> Self {
        match mode {
            // might have to check point size
            Mode::Private => unimplemented!(),
            Mode::Constant | Mode::Public => {
                let signature = signature
                    .signature
                    .to_bytes()
                    .iter()
                    .map(|b| {
                        let f = snarkvm_console::types::Field::from_u8(*b);
                        F::new(mode, f)
                    })
                    .collect_vec();
                Self { bytes: signature }
            }
        }
    }
}

impl Eject for ECDSASignature {
    type Primitive = super::console::ECDSASignature;

    fn eject_mode(&self) -> Mode {
        self.bytes[0].eject_mode()
    }

    fn eject_value(&self) -> Self::Primitive {
        let bytes = self
            .bytes
            .iter()
            .map(|b| {
                let f = b.eject_value();
                let big = f.to_bigint();
                let res = big.to_biguint().to_bytes_le();
                assert_eq!(res.len(), 1);
                res[0]
            })
            .collect_vec();
        let signature = k256::ecdsa::Signature::from_slice(&bytes).unwrap();
        Self::Primitive { signature }
    }
}

//
// Functions
// =========
//
/// Verifies a single ECDSA signature on a message.
pub fn verify_one(_public_key: ECDSAPublicKey, _signature: ECDSASignature, msg: Message, compile_mode: bool) {
    // Instantiate the sha2_256 hash function and hash the message.
    let sha2 = Sha2_256::new();
    let ripemd160 = Ripemd160::new();

    let intermediate_bits = sha2.hash(&msg);
    let bits = sha2.hash(&intermediate_bits);

    // Get the public key to bytes.
    let public_key_bytes = _public_key
        .bytes
        .iter()
        .map(|b| {
            let f = b.eject_value();
            let big = f.to_bigint();
            let res = big.to_biguint().to_bytes_le();
            assert_eq!(res.len(), 1);
            res[0]
        })
        .collect_vec();

    // Create bits based message from the bytes. - TODO: Assert public key bits matches external public key bits.
    // let message = Message::new(Mode::Public, public_key_bytes);
    // let public_key_intermediate_bits = sha2.hash(&message);
    // let public_key_bits = ripemd160.hash(&public_key_intermediate_bits);

    // Get the hash as a BigUint so the emulated field can be created from all 256 bytes
    // (SnarkVM fields would truncate the hash).
    let (mode, z) = Message { bits }.eject();
    println!("z: {:?}", z);

    let hash = BigUint::from_bytes_be(z.as_slice());

    // Create the emulated Fr field element from the hash.
    let h = EmulatedField::from_BigUint(&hash, secp256k1_Fr.LIMB_BYTES_NUM, mode, secp256k1_Fr);

    //r,s
    let vr = _signature
        .eject_value()
        .signature
        .r()
        .to_bytes()
        .iter()
        .map(|b| *b)
        .collect_vec();
    let br = BigUint::from_bytes_be(vr.as_slice());

    let vs = _signature
        .eject_value()
        .signature
        .s()
        .to_bytes()
        .iter()
        .map(|b| *b)
        .collect_vec();
    let bs = BigUint::from_bytes_be(vs.as_slice());
    let fr_value = BigUint::parse_bytes(secp256k1_Fr.FP, 16).unwrap();
    let frm2_value = fr_value.clone().sub(BigUint::one()).sub(BigUint::one());
    let bsi = bs.clone().modpow(&frm2_value, &fr_value);

    let mut sig_fs = _signature.bytes.clone();
    let (rfs, sfs) = sig_fs.split_at_mut(32);
    rfs.reverse();
    sfs.reverse();

    let r = EmulatedField::from_F(rfs, secp256k1_Fr);
    //assert_eq!(r.value.clone().unwrap(), br);
    let s = EmulatedField::from_F(sfs, secp256k1_Fr);
    //assert_eq!(s.value.clone().unwrap(), bs);

    let si = EmulatedField::from_BigUint(&bsi, secp256k1_Fr.LIMB_BYTES_NUM, Private, secp256k1_Fr);
    let smul = s.mul(&si);
    EmulatedField::enforce_eq(&smul, &EmulatedField::one(&secp256k1_Fr));

    //pk
    let vxy = _public_key
        .eject_value()
        .public_key
        .to_encoded_point(false)
        .to_bytes()
        .iter()
        .skip(1)
        .map(|b| *b)
        .collect_vec();
    let bx = BigUint::from_bytes_be(&vxy.as_slice()[0..32]);
    let by = BigUint::from_bytes_be(&vxy.as_slice()[32..]);

    let mut pk_fs = _public_key.bytes.clone();
    let (xfs, yfs) = pk_fs.split_at_mut(32);
    xfs.reverse();
    yfs.reverse();

    let x = EmulatedField::from_F(xfs, secp256k1_Fp);
    //assert_eq!(x.value.clone().unwrap(), bx);
    let y = EmulatedField::from_F(yfs, secp256k1_Fp);
    //assert_eq!(y.value.clone().unwrap(), by);

    let pk = Affine::from_xy_f(&x, &y, Private, secp256k1_Fp);

    // assert public key is valid
    let lhs = y.mul(&y);
    let x_cubic = x.mul(&x.mul(&x));
    let b = BigUint::from_u8(7).unwrap();
    let coeff_b =
        EmulatedField::from_BigUint(&b, secp256k1_Fp.LIMB_BYTES_NUM, Mode::Private, secp256k1_Fp);
    let rhs = x_cubic.add(&coeff_b);
    EmulatedField::enforce_eq(&lhs, &rhs);

    //G generator
    let G = Affine::G();

    //h*s1*G + r*s1*pk
    let mexp = Affine::scalarMulExp_win(&h.mul(&si), &G, &r.mul(&si), &pk);

    assert_eq!(mexp.x.value, r.value);
    EmulatedField::enforce_eq(&mexp.x, &r);
}

#[cfg(test)]
mod tests {
    use snarkvm_utilities::{TestRng, Uniform};
    use super::*;

    #[test]
    fn test_msg_injection_and_ejection() {
        // Generate 100 random 256-bit messages and test injection and ejection.
        // This optimally should have deterministic test vectors.
        for i in 0..100 {
            let mut rng = TestRng::default();
            let msg = (0..256)
                .map(|_| u8::rand(&mut rng))
                .collect::<Vec<u8>>();
            let message = Message::new(Mode::Public, msg.clone());
            assert_eq!(msg, message.eject_value());
        }
    }

    #[test]
    fn test_msg_layout() {
        let mut rng = TestRng::default();
        let msg = (0..256)
            .map(|_| u8::rand(&mut rng))
            .collect::<Vec<u8>>();
        let message = Message::new(Mode::Public, msg.clone());
    }
}