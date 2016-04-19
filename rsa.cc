#include <memory>
#include <future>
#include <string>
#include <cstdlib>
#include <cstring>
#include <ctime>
#include <unistd.h>
#include <algorithm>
#include <openssl/rsa.h>
#include <openssl/engine.h>
#include <openssl/pem.h>
#include <iostream>
#include <fstream>
#include <streambuf>
#include <iomanip>
#include <thread>
#include <mutex>
#include <getopt.h>
#include <libgen.h>
#include <gmp.h>

using namespace std;


namespace {
  gmp_randstate_t state;
  constexpr size_t DEFAULT_KEY_LENGTH = 2048;
  BIGNUM *e;
  constexpr int BENCHMARK_ITERATIONS = 10;
}

static inline string& ltrim(string &s, char c) {
  s.erase(s.begin(), find_if(s.begin(), s.end(), [c] (int ch) -> int {
    return c != ch;
  }));
  return s;
}

static int key_size = DEFAULT_KEY_LENGTH;

static struct option long_options[] = {
  {"size", optional_argument, 0, 's'},
  {"out", optional_argument, 0, 'o'},
  {"key", optional_argument, 0, 'k'},
  {"input", optional_argument, 0, 'i'},
  {"silent", optional_argument, 0, 'x'},
  {"iterations", optional_argument, 0, 'n'},
  {0, 0, 0, 0}
};

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

void bn_to_mpz(BIGNUM *n, mpz_t m) {
  if (n) {
    size_t sz = BN_num_bytes(n);
    unsigned char bytes[sz];
    BN_bn2bin(n, bytes);
    mpz_init(m);
    mpz_import(m, sz, 1, 1, 0, 0, bytes);
  }
}


struct GMPPrivateKey {
  typedef shared_ptr<GMPPrivateKey> Ptr;
  template<typename... Types> static Ptr New(Types ...args) { return Ptr(new GMPPrivateKey(args...)); }
  GMPPrivateKey(mpz_t pn, mpz_t pd, mpz_t pp, mpz_t pq, mpz_t pdmp1, mpz_t pdmq1, mpz_t piqmp) {
    n[0] = pn[0];
    d[0] = pd[0];
    p[0] = pp[0];
    q[0] = pq[0];
    dmp1[0] = pdmp1[0];
    dmq1[0] = pdmq1[0];
    iqmp[0] = piqmp[0];
  }
  ~GMPPrivateKey() {}
  mpz_t n, d, p, q, dmq1, dmp1, iqmp;
};

struct GMPPublicKey {
  typedef shared_ptr<GMPPublicKey> Ptr;
  template<typename... Types> static Ptr New(Types ...args) { return Ptr(new GMPPublicKey(args...)); }
  GMPPublicKey(mpz_t pn, mpz_t pe) {
    n[0] = pn[0];
    e[0] = pe[0];
  }
  ~GMPPublicKey() {}
  mpz_t n, e;
};

struct GMPKeyPair {
  typedef shared_ptr<GMPKeyPair> Ptr;
  template <typename... Types> static Ptr New(Types ...args) { return Ptr(new GMPKeyPair(args...)); }
  GMPKeyPair(mpz_t pn, mpz_t pe, mpz_t pd, mpz_t pp, mpz_t pq, mpz_t pdmp1, mpz_t pdmq1, mpz_t piqmp) {
    n[0] = pn[0];
    e[0] = pe[0];
    d[0] = pd[0];
    p[0] = pp[0];
    q[0] = pq[0];
    dmp1[0] = pdmp1[0];
    dmq1[0] = pdmq1[0];
    iqmp[0] = piqmp[0];
  }
  ~GMPKeyPair() { mpz_clear(n), mpz_clear(e), mpz_clear(d); mpz_clear(p); mpz_clear(q); mpz_clear(dmp1); mpz_clear(dmq1); mpz_clear(iqmp); }
  GMPPublicKey::Ptr GetPublicKey() { return GMPPublicKey::New(n, e); }
  GMPPrivateKey::Ptr GetPrivateKey() { return GMPPrivateKey::New(n, d, p, q, dmp1, dmq1, iqmp); }
  mpz_t n, e, d, p, q, dmp1, dmq1, iqmp;
};

GMPKeyPair::Ptr rsa_to_gmp(RSA *r) {
  mpz_t n, e, d, p, q, dmp1, dmq1, iqmp;
  bn_to_mpz(r->n, n);
  bn_to_mpz(r->e, e);
  bn_to_mpz(r->d, d);
  bn_to_mpz(r->p, p);
  bn_to_mpz(r->q, q);
  bn_to_mpz(r->dmp1, dmp1);
  bn_to_mpz(r->dmq1, dmq1);
  bn_to_mpz(r->iqmp, iqmp);
  return GMPKeyPair::New(n, e, d, p, q, dmp1, dmq1, iqmp);
}

static GMPKeyPair::Ptr gmp_keys;

RSA *gmp_to_rsa(GMPKeyPair::Ptr keys) {
  BIGNUM *n = mpz_to_bn(keys->n),
         *e = mpz_to_bn(keys->e),
         *d = mpz_to_bn(keys->d),
         *p = mpz_to_bn(keys->p),
         *q = mpz_to_bn(keys->q),
         *dmp1 = mpz_to_bn(keys->dmp1),
         *dmq1 = mpz_to_bn(keys->dmq1),
         *iqmp = mpz_to_bn(keys->iqmp);
  RSA *ret = RSA_new();
  ret->n = n;
  ret->e = e;
  ret->d = d;
  ret->p = p;
  ret->q = q;
  ret->dmp1 = dmp1;
  ret->dmq1 = dmq1;
  ret->iqmp = iqmp;
  return ret;
} 

void get_random_prime(mpz_t rop, unsigned bits) {
  mpz_urandomb(rop, state, bits - 2);
  mpz_t base;
  mpz_init_set_str(base, "11", 2);
  mpz_mul_2exp(base, base, bits - 2);
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

GMPKeyPair::Ptr generate_keys(unsigned bits) {
  auto half = bits / 2;
  mpz_t p, q, n, totient, e, d;
  mpz_init(p);
  mpz_init(q);
  mpz_init(n);
  mpz_init(totient);
  get_random_prime(p, half + 2);
  get_random_prime(q, half - 2);
  mpz_mul(n, p, q);
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
  return GMPKeyPair::New(n, e, d, p, q, dmp1, dmq1, iqmp);
}

static BN_CTX *ctx;

size_t openssl_rsa_encrypt(size_t blksz, unsigned char *plaintext, unsigned char *encrypted, RSA *keys) {
  size_t pad;
  BIGNUM *m = BN_new();
  BN_bin2bn(plaintext, blksz, m);
  ctx = BN_CTX_new();
  BN_mod_exp(m, m, keys->e, keys->n, ctx);
  pad = blksz - BN_num_bytes(m);
  memset(encrypted, 0, pad); 
  BN_bn2bin(m, plaintext + pad);
  return blksz;
}

size_t openssl_rsa_decrypt(size_t blksz, unsigned char *ciphertext, unsigned char *plaintext, RSA *keys) {

  size_t pad;
  BIGNUM *m = BN_new(), *m1 = BN_new(), *m2 = BN_new();
  BN_bin2bn(ciphertext, blksz, m);
  BN_mod_exp(m1, m, keys->dmp1, keys->p, ctx);
  BN_mod_exp(m2, m, keys->dmq1, keys->q, ctx);
  BN_sub(m1, m1, m2);
  BN_mod_mul(m1, m1, keys->iqmp, keys->p, ctx);
  BN_mul(m1, m1, keys->q, ctx);
  BN_add(m, m1, m2);
  pad = blksz - BN_num_bytes(m);
  memset(plaintext, 0, pad); 
  BN_bn2bin(m, plaintext + pad);
  return blksz;
}

string rsa_encrypt(GMPPublicKey::Ptr key, const string& msg) {
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

string rsa_decrypt(GMPPrivateKey::Ptr key, const string msg) throw() {
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
  return ltrim(ret, '\0');
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

template<typename Callable> double benchmark(int iterations, Callable fn) {
  clock_t start, end;
  start = clock();
  for (size_t i = 0; i < iterations; ++i) {
    fn();
  }
  end = clock();
  return abs(end - start);
}

const char msg_cstr[] = "\0Lorem ipsum dolor sit amet";

static RSA *rsa_keys;

typedef enum {
  ENCRYPT = 0x01,
  DECRYPT,
  GENERATE,
  BENCHMARK
} rsa_mode_t;

static rsa_mode_t mode;

static int passwd_callback(char *, int, int, void *) { return 0; }

static char *base;


#define MAX_ERROR_FORMAT_STRING_SIZE (1 << 16)


void Die(const char *fmt) {
  string out = base;
  out += ": ";
  out += fmt;
  cerr << out << endl;
  exit(1);
}

template <typename... T> void Die(const char *fmt, T... args) {
  char buf[MAX_ERROR_FORMAT_STRING_SIZE];
  sprintf(buf, fmt, args...);
  string out = base;
  out += ": ";
  out += buf;
  cerr << out << endl;
  exit(1);
}

static int iterations = BENCHMARK_ITERATIONS;
  
static mutex global_mutex;

static char nonsense_char;
static char char_before_last;
static char char_before_that;

static thread *thread_ptr;

void PrintNonsense() {
  double c = (double) rand()/RAND_MAX;
  char_before_that = char_before_last;
  char_before_last = nonsense_char;
  if (!nonsense_char) nonsense_char = '$';
  if (nonsense_char == '-' && char_before_that == '.') {
    cout << (nonsense_char = '*');
  } else if (nonsense_char == '-' && char_before_that == '*') { cout << (nonsense_char = '.'); }
  else if (nonsense_char == '.' || nonsense_char == '*') {
    if (c < 0.9) cout << (nonsense_char = '-');
    else if (c < 0.95) cout << (nonsense_char = '%');
    else if (c < 0.975) cout << (nonsense_char = '$');
    else if (c < 0.985) cout << (nonsense_char = '@');
    else cout << (nonsense_char = '#');
  } else {
    if (c < 0.5) {
      cout << nonsense_char;
    } else if (c < 0.7) {
      cout << (nonsense_char = '%');
    } else if (c < 0.8) {
      cout << (nonsense_char = '#');
    } else if (c < 0.95) {
      cout << (nonsense_char = '@');
    } else if (c < 0.97) {
      cout << (nonsense_char = '.');
    } else cout << (char_before_last = '.', nonsense_char = '-');
  }
  cout.flush();
}

int main(int argc, char **argv) {
  base = basename(argv[0]);
  ctx = BN_CTX_new();
  srand(time(0));
  gmp_randinit_default(state);
  int c, option_index;
  char *key_filename;
  char *output_filename;
  char *input_filename;
  bool silent;
  opterr = 0;
  while ((c = getopt_long(argc, argv, "i:o:s:n:x", long_options, &option_index)) != -1) {
    switch (c) {
      case 'n':
        iterations = atoi(optarg);
        break;
      case 's':
        key_size = atoi(optarg);
        break;
      case 'i':
        key_filename = optarg;
        break;
      case 'o':
        output_filename = optarg;
        break;
      case 'x':
        silent = true;
        break;
      case '?':
        Die("invalid option -%c", optopt);
        break;
    }
  }
  gmp_randseed_ui(state, rand());
  while (optind != argc) {
    if (!mode) {
      if (!strcmp(argv[optind], "encrypt")) { mode = ENCRYPT; }
      else if (!strcmp(argv[optind], "verify")) mode = ENCRYPT;
      else if (!strcmp(argv[optind], "decrypt") || !strcmp(argv[optind], "sign")) mode = DECRYPT;
      else if (!strcmp(argv[optind], "generate")) mode = GENERATE;
      else if (!strcmp(argv[optind], "benchmark")) mode = BENCHMARK;
    } else input_filename = argv[optind];
    optind++;
  }
  if (!mode) Die("no mode selected");
  if (mode == BENCHMARK) {
		double key_generation_time_libgmp = benchmark(iterations, [] {
			gmp_keys = generate_keys(key_size);
		});
		e = BN_new();
		BN_dec2bn(&e, "65537");
		RSA *tmp = RSA_new();
		double key_generation_time_openssl = benchmark(iterations, [tmp] {
			RSA_generate_key_ex(tmp, key_size, e, 0);
		});
		RSA_free(tmp);
		rsa_keys = gmp_to_rsa(gmp_keys);
		RSA_print_fp(stdout, rsa_keys, 0);
		string msg;
		msg.append(msg_cstr, sizeof(msg_cstr));
		cout << "== KEY GENERATION" << endl << "\tlibgmp: " << std::fixed << setprecision(0) << key_generation_time_libgmp << " cycles" << endl << "\topenssl: " << key_generation_time_openssl << " cycles" << endl;
		cout << "== ENCRYPTION" << endl;
		cout << "\tlibgmp: " << benchmark(iterations, [msg] {
			rsa_encrypt(gmp_keys->GetPublicKey(), msg);
		}) << " cycles" << endl;
		string ciphertext = rsa_encrypt(gmp_keys->GetPublicKey(), msg);
		size_t encsz = encrypted_size(msg.size(), key_size);
		size_t blksz = ceil((double) msg.size()/(key_size/8))*(key_size/8);
		unsigned char plaintext[blksz];
		memset(plaintext, 0, sizeof(plaintext));
		memcpy(plaintext, msg.c_str(), msg.size());
		unsigned char encrypted[encsz];
		size_t decsz = decrypted_size(encsz, DEFAULT_KEY_LENGTH);
		unsigned char decrypted[decsz];
		cout << "\topenssl: " << benchmark(iterations, [&] {
			RSA_public_encrypt(blksz, plaintext, encrypted, rsa_keys, RSA_NO_PADDING);
      ERR_print_errors_fp(stdout);
		}) << " cycles" << endl;
		cout << "== DECRYPTION" << endl;
		cout << "\tlibgmp: " << benchmark(iterations, [&] {
			rsa_decrypt(gmp_keys->GetPrivateKey(), ciphertext);
		}) << " cycles" << endl;
		cout << "\topenssl: " << benchmark(iterations, [&encsz, &encrypted, &decrypted] {
			RSA_private_decrypt(encsz, encrypted, decrypted, rsa_keys, RSA_NO_PADDING);
		}) << " cycles" << endl;
	} else if (mode == GENERATE) {
    future<GMPKeyPair::Ptr> keypair_future = async(launch::async, [] () -> GMPKeyPair::Ptr { GMPKeyPair::Ptr keys = generate_keys(key_size); return keys; });
    while (keypair_future.wait_for(chrono::milliseconds(50)) != future_status::ready) {
      PrintNonsense();
    }
    cout << endl;
    GMPKeyPair::Ptr keypair = keypair_future.get();
    rsa_keys = gmp_to_rsa(keypair);
    if (!silent) RSA_print_fp(stdout, rsa_keys, 0);
    FILE *fppriv = fopen(output_filename, "wt");
    FILE *fppub = fopen((string(output_filename) + ".pub").c_str(), "wt");
    PEM_write_RSAPrivateKey(fppriv, rsa_keys, NULL, NULL, 0, NULL, NULL);
    PEM_write_RSAPublicKey(fppub, rsa_keys);
    RSA_free(rsa_keys);
    fclose(fppub);
    fclose(fppriv);
  } else if (mode == ENCRYPT) {
    rsa_keys = RSA_new();
    FILE *fp = fopen(key_filename, "r");
    PEM_read_RSAPublicKey(fp, &rsa_keys, NULL, NULL); //PublicKey(fp, &rsa_keys, passwd_callback, buf);
    //PEM_read_RSAPrivateKey(fp, &rsa_keys, passwd_callback, buf);
    //PEM_read_RSAPrivateKey(fp, &rsa_keys, NULL, NULL);
    //ERR_print_errors_fp(stdout);
    fclose(fp);
    mpz_t n, e;
    bn_to_mpz(rsa_keys->n, n);
    bn_to_mpz(rsa_keys->e, e);
    GMPPublicKey::Ptr key = GMPPublicKey::New(n, e);
    RSA_free(rsa_keys);
    ifstream t(input_filename);
    string plaintext ((istreambuf_iterator<char>(t)), istreambuf_iterator<char>());
    if (output_filename) {
      ofstream out(output_filename);
      out << rsa_encrypt(key, plaintext);
    } else {
      cout << rsa_encrypt(key, plaintext);
    }
  } else if (mode == DECRYPT) {
    rsa_keys = RSA_new();
    FILE *fp = fopen(key_filename, "r");
    PEM_read_RSAPrivateKey(fp, &rsa_keys, NULL, NULL);
    fclose(fp);
    GMPKeyPair::Ptr keypair = rsa_to_gmp(rsa_keys);
    RSA_free(rsa_keys);
    ifstream t(input_filename);
    string plaintext ((istreambuf_iterator<char>(t)), istreambuf_iterator<char>());
    if (output_filename) {
      ofstream out(output_filename);
      out << rsa_decrypt(keypair->GetPrivateKey(), plaintext);
    } else cout << rsa_decrypt(keypair->GetPrivateKey(), plaintext);
  }
  gmp_randclear(state);
  BN_CTX_free(ctx);
	return 0;
}
