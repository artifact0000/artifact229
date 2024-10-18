#ifndef JADE_SCALARMULT_curve25519_amd64_ref5_inline_API_H
#define JADE_SCALARMULT_curve25519_amd64_ref5_inline_API_H

#define JADE_SCALARMULT_curve25519_amd64_ref5_inline_BYTES 32
#define JADE_SCALARMULT_curve25519_amd64_ref5_inline_SCALARBYTES 32

#define JADE_SCALARMULT_curve25519_amd64_ref5_inline_ALGNAME "Curve25519"
#define JADE_SCALARMULT_curve25519_amd64_ref5_inline_ARCH    "amd64"
#define JADE_SCALARMULT_curve25519_amd64_ref5_inline_IMPL    "ref5_inline"

#include <stdint.h>

int jade_scalarmult_curve25519_amd64_ref5_inline(
 uint8_t *q,
 const uint8_t *n,
 const uint8_t *p
);

int jade_scalarmult_curve25519_amd64_ref5_inline_base(
 uint8_t *q,
 const uint8_t *n
);

// TODO : to be replaced for opt. Jasmin implementation
int jade_scalarmult_curve25519_amd64_ref5_inline_base(
 uint8_t *q,
 const uint8_t *n
)
{
  uint8_t basepoint[32] = {9};
  int res = jade_scalarmult_curve25519_amd64_ref5_inline(q,n,basepoint);
  return res;
}

#endif
