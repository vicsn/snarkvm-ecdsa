# ZPrize - High Throughput Signature Verification

## How to Run
You can run the benchmark with the following command:

```
git clone https://github.com/Trapdoor-Tech/Trapdoortech_zprize-ecdsa-varuna.git
git clone Thttps://github.com/Trapdoor-Tech/rapdoortech_zprize-varuna-snarkVM.git
cd Trapdoortech_zprize-ecdsa-varuna/zprize/
cargo bench -- --nocapture
```

The bench contains 3 test groups, each group are repeated 10 times to get a time profile:

1. 50 signatures on 50 messages of 100 bytes

2. 50 signatures on 50 messages of 1,000 bytes

3. 50 signatures on 50 messages of 50,000 bytes




## Proving Performance
The default concurrent threads for circuit constraints generation is __10__, which means there will be __5__ proofs for one iteration of one test group.

Depends on the target machine memory capacity, you can increase or decrease the concurrency by setting environment variable `MAX_CON=X`, here `X` means the number of concurrent threads you want. Depends on `X`, the number of generated proofs will vary.

We ran the bench under several conditions, below is a list of test results:

| Message Length (Bytes) | Num of Messages | Concurrent Instances | Memory (GB) | Prove time (s)|
|---|---|---|---|---|
|100|50|1|5.35|635|
|100|50|5|7.26|177|
|100|50|10|10.9|124|
|100|50|25| 20.8 | 96 |
|100|50|50| 37.7 | 86.7 |
|1000|50|1|5.23|645|
|1000|50|5|7.4|180|
|1000|50|10|12|136|
|1000|50|25| 25.9 | 102 |
|1000|50|50| 37.3 | 93 |
|50000|50|1|54|5950|
|50000|50|5|76.6|2040|
|50000|50|10|128|1650|
|50000|50|25| 291.7 | 1352 |

All tests are done on a Intel Xeon Server with following specs:
- CPU: Intel(R) Xeon(R) Gold 6254 CPU @ 3.10GHz
- Cores: 36 physical cores, 72 virtual cores
- Memory: 512 GB
- Memory Speed: 2933 MT/s



## Circuit Size

The ECDSA circuit is composed mainly by two sub circuits: 1/ Keccak256 hash 2/ ECDSA verifier.
The XOR/AND/INV operation(dimension size 8x8) in Keccak256 hash is implemented by lookup tables. Due to the fact the rotate offsets in Keccark256 hash algorithm are fixed, several lookup tables are used to support ROTL operations - one table is used for one fixed rotation offset (the table key size is 16).
In order to support ECDSA verifier, ADD/SUB/MUL/DIV/Reduce operations of Fp/Fr on curve `secp256k1` are emulated. And based on that, point add/double and mulexp operations are implemented.

The circuit sizes for different input message sizes are summaried in the following table:
 | Message Length (Bytes) | Constraints Num | Public Num | Private Num | Non-Zeros Num|
 |---|---|---|---|---|
 |100|490692|229|598374|(919920, 622003, 536022)|
 |1000|495564|1129|827134|(939408, 626875, 574998)|
 |50000|746124|50129|12591934|(1941648, 877435, 2579478)|



## Various Improvements of Our Verification Solution

Here we list some general implemented improvements to ECDSA verification proving.

### a. Use Emulated Field Arithmatic
Since ECDSA are on curve `secp256k1` and SnarkVM are on curve `BLS12-377`, we cannot directly do elliptic curve arithmetic using SnarkVM  `Fr` field. Instead, we have to break coordinates of points on `secp256k1` into several limbs, each represented by a SnarkVM `Fr` element., which is called _Emulation_.

Details can be found on Ariel Gabizon's manuscript https://hackmd.io/@arielg/B13JoihA8 .

### b. Make use of Varuna Lookup Table
Varuna extends Marlin proving system in several aspects. One handy aspect is lookup table constraints. They enable representing non-arithmetic operations in R1CS circuit. To be more precise, lookup constraints in Varuna looks like:

```
[F, F] -> [F]
```

where `F` represents a field element in R1CS.

Our lookup constraints are mainly used for round functions in Keccak256 hash, in particular, the byte-wise `and`, `xor` and `inv` operations, and specific `rotl` functions in addition. For a message of 50,000 bytes length, we managed to limit the witnesses and constraits within 13M, which means ~200 constraints per byte.

### c. Use Rust `Vector` instead of `BTreeMap/IndexMap`
In SnarkVM, many of the data structures are of type `BTreeMap` or `IndexMap`. Although these data structures are very convenient to use and have low time complexity, their memory usage is too large. This results in the prover running with hundreds of GBs of memory overhead when the message length is 50,000 bytes.

We replaced most of the BTreeMaps and IndexMaps in the code with Vecs. This kept our memory usage at an acceptable level, under 100GB.

### d. Parallelising Circuit Generation
After reducing memory usage, we handled the generation of multiple circuit instances at once. This greatly saved the prover's running time, thanks to Varuna's out-of-the-box batch proving method.

### e. Use Jemalloc as Memory Allocator
We found that during the prover's execution, although we replaced the existing circuit instance with a new empty instance each time, the memory did not seem to be released accordingly. Specifically, even after the `Circuit::eject_assignment_and_reset()` function was called, we still observed that a huge amount of memory was not freed. This issue was resolved after we replaced the default system allocator used by Rust with `jemalloc`.
