#include <memory>
#include <string>
#include <cstdlib>
#include <cstring>
#include <ctime>
#include <algorithm>
#include <iostream>
#include <gmp.h>

using namespace std;

namespace {
  gmp_randstate_t state;
}

struct Error : public exception {
  const char *pwhat;
  Error(const char *what) : exception(), pwhat(what) {}
  virtual const char *what() { return pwhat; }
};

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

string rsa_decrypt(PrivateKey::Ptr key, const string& msg) throw() {
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

int main(int argc, char **argv) {
  srand(time(0));
  gmp_randinit_default(state);
  gmp_randseed_ui(state, rand());
  KeyPair::Ptr keys = generate_keys(512);
  gmp_printf("n: %Zd\ne: %Zd\nd: %Zd\n", keys->n, keys->e, keys->d);
  string msg = "Lorem ipsum dolor sit amet, consectetur adipiscing elit. Etiam bibendum dolor eget leo aliquet interdum. Etiam a viverra mauris. Nullam sed magna lobortis, rutrum quam ut, imperdiet ligula. Etiam et neque semper, malesuada enim vitae, bibendum dui. Cras eget purus at ipsum mollis fringilla at eget nisl. Etiam sem nisl, ornare sit amet tellus ut, malesuada imperdiet purus. Nunc luctus cursus vulputate. Sed maximus odio mauris, accumsan commodo nisi porttitor sed. Nunc venenatis tortor augue, ac viverra nunc vehicula in. Morbi a est et lorem molestie vehicula. Phasellus sollicitudin, ante quis dapibus pellentesque, nibh augue cursus felis, auctor eleifend velit risus sit amet turpis.";
  string ciphertext = rsa_encrypt(keys->GetPublicKey(), msg);
  string plaintext = rsa_decrypt(keys->GetPrivateKey(), ciphertext);
  cout << plaintext << endl;
  gmp_randclear(state);
  return 0;
}

