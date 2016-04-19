bin_PROGRAMS = rsa
libgmp_LIBS = -lgmp
AM_CXXFLAGS = $(openssl_CFLAGS) $(libgmp_CFLAGS) $(CFLAGS) -std=c++0x -pthread
rsa_SOURCES = rsa.cc
rsa_LDADD = $(openssl_LIBS) $(libgmp_LIBS) $(LDFLAGS)
