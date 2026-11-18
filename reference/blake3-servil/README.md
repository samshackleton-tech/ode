# Reference material from BLAKE3-Servil

Files of BLAKE3-Servil's repository that the BLAKE3 example is compared with. Nothing here is Ode's own, and
no verification loads any of it.

| file | from | used by |
|---|---|---|
| `c/blake3_avx512_32.S` | BLAKE3-Servil's 32-lane and 16-lane AVX-512 kernels | `wide/test_*.py`: the kernels written in Ode (`wide/k32.ode`, `wide/p16.ode`) assemble to the same bytes; `kcheck/test_kloop.py` and `kcheck/test_kdecode.py` read and verify the library's own |
| `c/blake3_avx512_x86-64_unix.S`, `c/blake3_sse41_x86-64_unix.S` | its one-block kernels | the same, for `wide/one.ode` |
| `c/blake3_output16.S` | a kernel with no Ode source yet | nothing now; it is what `output16` written in Ode is to be compared with |
| `test_vectors/test_vectors.json` | the official BLAKE3 test vectors | `kcheck/test_ode.py`: the specification `kcheck/blake3.spec`, evaluated, gives all 105 |

Taken unchanged from `samshackleton-tech/BLAKE3` at commit `dca7275f6c4817b7ebe0a985fd7024b6f7aea17f`.
BLAKE3-Servil's licence applies to them: CC0-1.0, or Apache-2.0, or Apache-2.0 with LLVM exception, at the
user's choice (`LICENSE_CC0`, `LICENSE_A2`, `LICENSE_A2LLVM` here).
