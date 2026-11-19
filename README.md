# Vectorized base64 for PHP, with a Lean 4 proof of its store bounds

This repository holds the code of the php-src pull request
[php/php-src#25476](https://github.com/php/php-src/pull/25476), which ports the
simdutf base64 decoders (SSSE3, AVX2, AVX-512 VBMI, NEON) to
`ext/standard/base64.c`, and a Lean 4 proof that the encoders and decoders
never write outside their buffers.

| path | content |
|---|---|
| `ext/standard/base64.c`, `ext/standard/base64.h` | the code, as in the pull request |
| `ext/standard/tests/url/base64_decode_blocks.phpt` | the new test |
| `Zend/zend_cpuinfo.h`, `Zend/zend_portability.h`, `build/php.m4` | build support (AVX-512 VBMI detection) |
| `php-src-pr25476.patch` | the full diff against php-src `master` at 90628d5ab3f |
| `formal/base64_safety/` | the Lean 4 development; see its README |

The files under `ext/`, `Zend/` and `build/` are full copies of the php-src
files at the pull request's head (9aa3add42f2). To build PHP with them, apply
the patch to php-src at the base commit:

```sh
git clone https://github.com/php/php-src.git
cd php-src
git checkout 90628d5ab3f8cf91eb8099b8690018637df3f3b4
git apply ../phpbase64/php-src-pr25476.patch
```

To check the proof:

```sh
cd formal/base64_safety
lake build
```

The PHP code is under the PHP license (Modified BSD, see `LICENSE`).
