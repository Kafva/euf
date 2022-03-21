#!/usr/bin/env bash
cd ~/.cache/euf/openssl-29f178bd

make -j15 CC=goto-cc  build_generated



goto-cc -E -I. -Iinclude -Iproviders/common/include -Iproviders/implementations/include -Icrypto/include -DAES_ASM -DBSAES_ASM -DCMLL_ASM -DECP_NISTZ256_ASM -DGHASH_ASM -DKECCAK1600_ASM -DMD5_ASM -DOPENSSL_BN_ASM_GF2m -DOPENSSL_BN_ASM_MONT -DOPENSSL_BN_ASM_MONT5 -DOPENSSL_CPUID_OBJ -DOPENSSL_IA32_SSE2 -DPOLY1305_ASM -DSHA1_ASM -DSHA256_ASM -DSHA512_ASM -DVPAES_ASM -DWHIRLPOOL_ASM -DX25519_ASM -fPIC -pthread -m64 -Wa,--noexecstack -Wall -O3 -DOPENSSL_USE_NODELETE -DL_ENDIAN -DOPENSSL_BUILDING_OPENSSL -DOPENSSL_PIC -DOPENSSLDIR="/usr/local/ssl" -DENGINESDIR="/usr/local/lib/engines-3" -DMODULESDIR="/usr/local/lib/ossl-modules" \
	-DOPENSSL_API_COMPAT=0x10200000 \
	-DNDEBUG /home/jonas/.cache/euf/openssl-29f178bd/crypto/asn1/f_int.c -o /tmp/E_f_int.c

