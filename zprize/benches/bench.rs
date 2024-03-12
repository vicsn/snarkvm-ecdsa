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

use criterion::{black_box, criterion_group, criterion_main, Criterion};

fn criterion_benchmark(c: &mut Criterion) {
    let mut group = c.benchmark_group("Proof creation");
    group
        .sample_size(10)
        .sampling_mode(criterion::SamplingMode::Flat); // for slow benchmarks

    // setup
    let urs = zprize::api::setup(1000, 1000, 1000);


    // we generate 50 tuples for each bench
    // tuple = (public key, message, signature)
    let num = 50;

    // 100 bytes
    let msg_len = 100;
    let small_tuples = zprize::console::generate_signatures(msg_len, num);
    let (small_pk, small_vk) = zprize::api::compile(&urs, msg_len);

    // 1,000 bytes
    let msg_len = 1000;
    let medium_tuples = zprize::console::generate_signatures(msg_len, num);
    let (medium_pk, medium_vk) = zprize::api::compile(&urs, msg_len);

    // 50,000 bytes
    let msg_len = 50000;
    let large_tuples = zprize::console::generate_signatures(msg_len, num);
    let (large_pk, large_vk) = zprize::api::compile(&urs, msg_len);

    //
    // WARNING
    // =======
    //
    // Do not modify anything above this line.
    // Everything after this line should be fairgame,
    // as long as proofs verify.
    //

    let max_concurrency = match std::env::var("MAX_CON") {
        Ok(num) => match num.parse::<usize>() {
            Ok(num) => num,
            Err(e) => {
                println!("Parse max concurrency error {:?}, use default 10", e);
                10usize
            }
        },
        Err(e) => {
            10usize
        }
    };

    let mut idx = 0;
    group.bench_function("small message", |b| {
        b.iter(|| {
            println!("==============   small message #{idx}  ===============");
            // prove all tuples
            zprize::prove_and_verify(&urs, &small_pk, &small_vk, black_box(&small_tuples), max_concurrency);
            idx += 1;
        })
    });

    let mut idx = 0;
    group.bench_function("medium message", |b| {
        b.iter(|| {
            println!("==============   medium message #{idx}  ===============");
            // prove all tuples
            zprize::prove_and_verify(&urs, &medium_pk, &medium_vk, black_box(&medium_tuples), max_concurrency);
            idx += 1;
        })
    });

    let mut idx = 0;
    group.bench_function("large message", |b| {
        b.iter(|| {
         println!("==============   large message #{idx}  ===============");
            // prove all tuples
            zprize::prove_and_verify(&urs, &large_pk, &large_vk, black_box(&large_tuples), max_concurrency);
           idx += 1;

        })
    });
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
