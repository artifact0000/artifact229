#include <stdint.h>
#include <string.h>
#include <assert.h>
#include <stdio.h>
#include <inttypes.h>

#include "randombytes.h"
#include "api.h"

#include "jade_kem.h"
#include "print.h"

int main(void)
{
  int r;
  uint8_t public_key[JADE_KEM_PUBLICKEYBYTES];
  uint8_t secret_key[JADE_KEM_SECRETKEYBYTES];

  uint8_t shared_secret_a[JADE_KEM_BYTES];
  uint8_t ciphertext[JADE_KEM_CIPHERTEXTBYTES];
  uint8_t shared_secret_b[JADE_KEM_BYTES];

  // create key pair
  r = jade_kem_keypair(public_key, secret_key);
    assert(r == 0);

  // encapsulate
  r = jade_kem_enc(ciphertext, shared_secret_a, public_key);
    assert(r == 0);

  // decapsulate
  r = jade_kem_dec(shared_secret_b, ciphertext, secret_key);
    assert(r == 0);
    assert(memcmp(shared_secret_a, shared_secret_b, JADE_KEM_BYTES) == 0);

  print_info(JADE_KEM_ALGNAME, JADE_KEM_ARCH, JADE_KEM_IMPL);
  print_str_u8("secret_key", secret_key, JADE_KEM_SECRETKEYBYTES);
  print_str_u8("public_key", public_key, JADE_KEM_PUBLICKEYBYTES);
  print_str_u8("ciphertext", ciphertext, JADE_KEM_CIPHERTEXTBYTES);
  print_str_u8("shared_secret", shared_secret_a, JADE_KEM_BYTES);

  return 0;
}

