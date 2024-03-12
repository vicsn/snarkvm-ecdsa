// Copyright (C) 2019-2023 Aleo Systems Inc.
// This file is part of the snarkVM library.

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at:
// http://www.apache.org/licenses/LICENSE-2.0

// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use k256::ecdsa::{Signature, VerifyingKey};
use snarkvm_algorithms::{
    polycommit::kzg10::UniversalParams,
    snark::varuna::{CircuitProvingKey, CircuitVerifyingKey, VarunaHidingMode},
};
use snarkvm_curves::bls12_377::Bls12_377;

pub mod api;
pub mod circuit;
pub mod console;
pub mod ecc_secp256k1;
pub mod emulated_field;
pub mod keccak256;
pub mod utils;

#[cfg(not(target_env = "msvc"))]
#[global_allocator]
static ALLOC: tikv_jemallocator::Jemalloc = tikv_jemallocator::Jemalloc;

pub type Tuples = Vec<(VerifyingKey, Vec<u8>, Signature)>;

pub fn prove_and_verify(
    urs: &UniversalParams<Bls12_377>,
    pk: &CircuitProvingKey<Bls12_377, VarunaHidingMode>,
    vk: &CircuitVerifyingKey<Bls12_377>,
    tuples: &Tuples,
    max_concurrent: usize,
) {
    let mut message_num = 0;
    // TODO: test could be adjusted to pass references and clone less
    let proofs = tuples
        .chunks(max_concurrent)
        .map(|tuple| {
            message_num += 1;

            println!("processing message batch #{message_num}");

            let t = tuple.clone().to_vec();
            let proof = api::prove(urs, pk, t);

            proof
        })
        .collect::<Vec<_>>();

    // Note: proof verification should take negligible time,
    tuples
        .chunks(max_concurrent)
        .zip(proofs.iter())
        .for_each(|(tuple, proof)| {
            let t = tuple.clone().to_vec();
            api::verify_proof(urs, vk, &t, &proof);
        });
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_works() {
        // generate `num` (pubkey, msg, signature)
        // with messages of length `msg_len`
        let num = 10;
        let msg_len = 100;
        let tuples = console::generate_signatures(msg_len, num);

        // setup
        let urs = api::setup(1000, 1000, 1000);

        let (pk, vk) = api::compile(&urs, msg_len);

        // prove and verify
        // prove_and_verify(&urs, &pk, &vk, &tuples, 10);

        for i in 0..10 {
            println!("prove iter #{i}");
            prove_and_verify(&urs, &pk, &vk, &tuples, 10);

            println!("sleeping");
            std::thread::sleep(std::time::Duration::new(5, 0));
            println!("sleeping done");
        }
    }
}
