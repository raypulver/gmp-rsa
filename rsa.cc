#include <memory>
#include <string>
#include <cstdlib>
#include <cstring>
#include <ctime>
#include <algorithm>
#include <vector>
#include <openssl/rsa.h>
#include <openssl/engine.h>
#include <openssl/pem.h>
#include <iostream>
#include <gmp.h>

using namespace std;

namespace {
  gmp_randstate_t state;
  constexpr size_t DEFAULT_KEY_LENGTH = 2048;
  RSA *rsa_keys;
  BIGNUM *e;
/*
  constexpr size_t KEY_GENERATION_ITERATIONS = 1;
  constexpr size_t ENCRYPTION_ITERATIONS = 1;
  constexpr size_t DECRYPTION_ITERATIONS = 1;
*/
  constexpr size_t KEY_GENERATION_ITERATIONS = 50;
  constexpr size_t ENCRYPTION_ITERATIONS = 500000;
  constexpr size_t DECRYPTION_ITERATIONS = 5000;
}

struct Error : public exception {
  const char *pwhat;
  Error(const char *what) : exception(), pwhat(what) {}
  virtual const char *what() { return pwhat; }
};

BIGNUM *mpz_to_bn(mpz_t n) {
  size_t sz = ceil(mpz_sizeinbase(n, 2)/8);
  unsigned char bytes[sz];
  mpz_export(bytes, &sz, 1, 1, 0, 0, n);
  BIGNUM *ret;
  ret = BN_new();
  return BN_bin2bn(bytes, sz, ret);
}


struct PrivateKey {
  typedef unique_ptr<PrivateKey> Ptr;
  template<typename... Types> static Ptr New(Types ...args) { return Ptr(new PrivateKey(args...)); }
  PrivateKey(mpz_t pn, mpz_t pd, mpz_t pp, mpz_t pq, mpz_t pdmp1, mpz_t pdmq1, mpz_t piqmp) {
    n[0] = pn[0];
    d[0] = pd[0];
    p[0] = pp[0];
    q[0] = pq[0];
    dmp1[0] = pdmp1[0];
    dmq1[0] = pdmq1[0];
    iqmp[0] = piqmp[0];
  }
  ~PrivateKey() {}
  mpz_t n, d, p, q, dmq1, dmp1, iqmp;
};

struct PublicKey {
  typedef unique_ptr<PublicKey> Ptr;
  template<typename... Types> static Ptr New(Types ...args) { return Ptr(new PublicKey(args...)); }
  PublicKey(mpz_t pn, mpz_t pe) {
    n[0] = pn[0];
    e[0] = pe[0];
  }
  ~PublicKey() {}
  mpz_t n, e;
};

struct KeyPair {
  typedef unique_ptr<KeyPair> Ptr;
  template <typename... Types> static Ptr New(Types ...args) { return Ptr(new KeyPair(args...)); }
  KeyPair(mpz_t pn, mpz_t pe, mpz_t pd, mpz_t pp, mpz_t pq, mpz_t pdmp1, mpz_t pdmq1, mpz_t piqmp) {
    n[0] = pn[0];
    e[0] = pe[0];
    d[0] = pd[0];
    p[0] = pp[0];
    q[0] = pq[0];
    dmp1[0] = pdmp1[0];
    dmq1[0] = pdmq1[0];
    iqmp[0] = piqmp[0];
  }
  ~KeyPair() { mpz_clear(n), mpz_clear(e), mpz_clear(d); mpz_clear(p); mpz_clear(q); mpz_clear(dmp1); mpz_clear(dmq1); mpz_clear(iqmp); }
  PublicKey::Ptr GetPublicKey() { return PublicKey::New(n, e); }
  PrivateKey::Ptr GetPrivateKey() { return PrivateKey::New(n, d, p, q, dmp1, dmq1, iqmp); }
  mpz_t n, e, d, p, q, dmp1, dmq1, iqmp;
};

static KeyPair::Ptr gmp_keys;

RSA *keypair_to_rsa(KeyPair::Ptr &keys) {
  RSA *ret = RSA_new();
  ret->n = mpz_to_bn(keys->n);
  ret->e = mpz_to_bn(keys->e);
  ret->d = mpz_to_bn(keys->d);
  ret->p = mpz_to_bn(keys->p);
  ret->q = mpz_to_bn(keys->q);
  ret->dmp1 = mpz_to_bn(keys->dmp1);
  ret->dmq1 = mpz_to_bn(keys->dmq1);
  ret->iqmp = mpz_to_bn(keys->iqmp);
  return ret;
} 

void get_random_prime(mpz_t rop, unsigned bits) {
  mpz_urandomb(rop, state, bits - 1);
  mpz_t base;
  mpz_init_set_str(base, "1", 2);
  mpz_mul_2exp(base, base, bits - 1);
  mpz_add(rop, rop, base);
  mpz_clear(base);
  mpz_nextprime(rop, rop);
}

void mpz_totient(mpz_t rop, mpz_t *pm, mpz_t *qm, mpz_t p, mpz_t q) {
  mpz_clear(rop);
  mpz_init_set_str(rop, "1", 2);
  mpz_init(*pm);
  mpz_init(*qm);
  mpz_sub(*pm, p, rop);
  mpz_sub(*qm, q, rop);
  mpz_mul(rop, *pm, *qm);
}

KeyPair::Ptr generate_keys(unsigned bits) {
  auto half = bits / 2;
  mpz_t p, q, n, totient, e, d;
  mpz_init(p);
  mpz_init(q);
  mpz_init(n);
  mpz_init(totient);
  get_random_prime(p, half + 2);
  get_random_prime(q, half - 2);
  mpz_mul(n, p, q);
  if (mpz_sizeinbase(n, 2) < bits) {
    mpz_clear(p);
    mpz_clear(q);
    mpz_clear(n);
    mpz_clear(totient);
    return generate_keys(bits);
  }
  mpz_t pm1, qm1;
  mpz_totient(totient, &pm1, &qm1, p, q);
  mpz_t term, gcd;
  mpz_init(gcd);
  mpz_init_set_str(term, "1", 2);
  mpz_init_set_str(e, "65537", 10);
  while (1) {
    mpz_gcd(gcd, e, totient);
    if (!mpz_cmp(gcd, term)) {
      break;
    }
    mpz_add(e, e, term);
  }
  mpz_init(d);
  mpz_invert(d, e, totient);
  mpz_clear(term);
  mpz_clear(totient); 
  mpz_t dmp1, dmq1, iqmp;
  mpz_init(dmp1);
  mpz_init(dmq1);
  mpz_init(iqmp);
  mpz_mod(dmp1, d, pm1);
  mpz_mod(dmq1, d, qm1);
  mpz_invert(iqmp, q, p);
  mpz_clear(pm1);
  mpz_clear(qm1);
  return KeyPair::New(n, e, d, p, q, dmp1, dmq1, iqmp);
}

string rsa_encrypt(PublicKey::Ptr key, const string& msg) {
  size_t sz = msg.size();
  const char *str = msg.c_str();
  string out;
  size_t len = mpz_sizeinbase(key->n, 2);
  size_t blksz = ceil((double) len/8) - 1;
  size_t blks = ceil((double) sz/blksz);
  size_t instr_len = blks*blksz;
  char *instr = new char[instr_len];
  memset(instr, 0, instr_len);
  memcpy(instr, str, sz);
  size_t out_cstr_len = blks*(blksz + 1);
  char *out_cstr = new char[out_cstr_len];
  memset(out_cstr, 0, out_cstr_len);
  mpz_t z;
  mpz_init(z);
  size_t minn;
  size_t minout = blksz + 1;
  size_t last_minout = minout;
  for (uint8_t i = 0; i < blks; i++) {
    if (sz - blksz*i < blksz) {
      minn = sz - blksz*i;
    } else {
      minn = blksz;
    }
    mpz_import(z, minn, 1, 1, 0, 0, instr + i*blksz);
    mpz_powm(z, z, key->e, key->n);
    mpz_export(out_cstr + i*minout + minout - (size_t) ceil((double) mpz_sizeinbase(z, 2)/8), &minout, 1, 1, 0, 0, z);
    minout = last_minout;
  }
  mpz_clear(z);
  out.append(out_cstr, out_cstr_len);
  delete[] instr;
  delete[] out_cstr;
  return out;
}

string rsa_decrypt(PrivateKey::Ptr key, const string msg) throw() {
  size_t sz = msg.size();
  const char *str = msg.c_str();
  string *out = new string();
  size_t len = mpz_sizeinbase(key->n, 2);
  size_t blksz = ceil((double) len/8) - 1;
  size_t inblksz = blksz + 1;
  size_t blks = ceil((double) sz/inblksz);
  size_t instr_len = blks*inblksz;
  char *instr = new char[instr_len];
  memset(instr, 0, instr_len);
  memcpy(instr, str, sz);
  size_t out_cstr_len = blks*blksz;
  char *out_cstr = new char[out_cstr_len];
  memset(out_cstr, 0, out_cstr_len);
  mpz_t z, m1, m2;
  mpz_init(z);
  mpz_init(m1);
  mpz_init(m2);
  size_t minn;
  size_t last_blksz = blksz;
  for (uint8_t i = 0; i < blks; i++) {
    mpz_import(z, inblksz, 1, 1, 0, 0, instr + i*inblksz);
    mpz_powm(m1, z, key->dmp1, key->p);
    mpz_powm(m2, z, key->dmq1, key->q);
    mpz_sub(m1, m1, m2);
    mpz_mul(m1, key->iqmp, m1);
    mpz_mod(m1, m1, key->p);
    mpz_mul(m1, m1, key->q);
    mpz_add(z, m1, m2);
    if (blksz - ceil((double) mpz_sizeinbase(z, 2)/8) < 0) throw Error("Invalid private key.");
    mpz_export(out_cstr + i*blksz + blksz - (size_t) ceil((double) mpz_sizeinbase(z, 2)/8), &blksz, 1, 1, 0, 0, z);
    blksz = last_blksz;
  }
  mpz_clear(z);
  mpz_clear(m1);
  mpz_clear(m2);
  out->append(out_cstr, out_cstr_len);
  delete[] out_cstr;
  size_t last = out->find_last_not_of('\0');
  delete[] instr;
  string ret = out->substr(0, last + 1);
  delete out;
  return ret;
}

size_t encrypted_size(size_t len, size_t bits) {
  size_t bytes = ceil((double) bits/8);
  size_t inblksz = bytes - 1;
  size_t blks = ceil((double) len/inblksz);
  return blks*bytes;
}

size_t decrypted_size(size_t len, size_t bits) {
  size_t bytes = ceil((double) bits/8);
  size_t inblksz = bytes;
  size_t blks = ceil((double) len/inblksz);
  return blks*(bytes - 1);
}

template<size_t iterations> double benchmark(function<void(void)> fn) {
  time_t start, end;
  time(&start);
  for (size_t i = 0; i < iterations; ++i) {
    fn();
  }
  time(&end);
  return abs(difftime(start, end));
}

const char msg_cstr[] = "\0Lorem ipsum dolor sit amet";

int main(int argc, char **argv) {
  srand(time(0));
  gmp_randinit_default(state);
  cout << "Benchmarking key generation..." << endl;
  gmp_randseed_ui(state, rand());
  double key_generation_time_libgmp = benchmark<KEY_GENERATION_ITERATIONS>([] {
    gmp_keys = generate_keys(DEFAULT_KEY_LENGTH);
  });
  e = BN_new();
  BN_dec2bn(&e, "65537");
  rsa_keys = RSA_new();
  double key_generation_time_openssl = benchmark<KEY_GENERATION_ITERATIONS>([] {
    RSA_generate_key_ex(rsa_keys, DEFAULT_KEY_LENGTH, e, 0);
  });
  RSA_free(rsa_keys);
  rsa_keys = keypair_to_rsa(gmp_keys);
  //BN_print_fp(stdout, rsa_keys->n);
  gmp_printf("n: %Zd\ne: %Zd\nd: %Zd\n", gmp_keys->n, gmp_keys->e, gmp_keys->d);
  string msg;
  msg.append(msg_cstr, sizeof(msg_cstr));
  cout << "Key generation benchmark results:" << endl << "libgmp: " << key_generation_time_libgmp << endl << "openssl: " << key_generation_time_openssl << endl;
  cout << "Benchmarking encryption..." << endl;
  cout << "libgmp: " << benchmark<ENCRYPTION_ITERATIONS>([msg] {
    rsa_encrypt(gmp_keys->GetPublicKey(), msg);
  }) << endl;
  string ciphertext = rsa_encrypt(gmp_keys->GetPublicKey(), msg);
  size_t encsz = encrypted_size(msg.size(), DEFAULT_KEY_LENGTH);
  size_t blksz = ceil((double) msg.size()/(DEFAULT_KEY_LENGTH/8))*(DEFAULT_KEY_LENGTH/8);
  unsigned char plaintext[blksz];
  memset(plaintext, 0, sizeof(plaintext));
  memcpy(plaintext, msg.c_str(), msg.size());
  unsigned char encrypted[encsz];
  size_t decsz = decrypted_size(encsz, DEFAULT_KEY_LENGTH);
  unsigned char decrypted[decsz];
  cout << "openssl: " << benchmark<ENCRYPTION_ITERATIONS>([&encrypted, &plaintext, &msg, blksz] {
    RSA_public_encrypt(blksz, plaintext, encrypted, rsa_keys, RSA_NO_PADDING);
    ERR_print_errors_fp(stdout);
/*
    unsigned long err = ERR_get_error();
    cout << err << endl;
    const char *mesg = ERR_reason_error_string(err);
    cout << mesg << endl; */
  }) << endl;
  cout << "Benchmarking decryption..." << endl;
  cout << "libgmp: " << benchmark<DECRYPTION_ITERATIONS>([ciphertext] {
    rsa_decrypt(gmp_keys->GetPrivateKey(), ciphertext);
  }) << endl;
  cout << "openssl: " << benchmark<DECRYPTION_ITERATIONS>([&encsz, &encrypted, &decrypted] {
    RSA_private_decrypt(encsz, encrypted, decrypted, rsa_keys, RSA_NO_PADDING);
  }) << endl;
  //string plaintext = rsa_decrypt(gmp_keys->GetPrivateKey(), ciphertext);
  gmp_randclear(state);
  return 0;
}
