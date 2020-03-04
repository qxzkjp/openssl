/*
 * Copyright 2006-2018 The OpenSSL Project Authors. All Rights Reserved.
 *
 * Licensed under the Apache License 2.0 (the "License").  You may not use
 * this file except in compliance with the License.  You can obtain a copy
 * in the file LICENSE in the source distribution or at
 * https://www.openssl.org/source/license.html
 */

/*
 * ECDH and ECDSA low level APIs are deprecated for public use, but still ok
 * for internal use.
 */
#include "internal/deprecated.h"

#include <openssl/core_names.h>
#include <stdio.h>
#include "internal/cryptlib.h"
#include <openssl/asn1t.h>
#include <openssl/x509.h>
#include <openssl/ec.h>
#include "ec_local.h"
#include <openssl/evp.h>
#include "crypto/evp.h"
#include <openssl/hmac.h>
#include <openssl/crypto.h>

/* EC pkey context structure */

typedef struct {
    /* Key and paramgen group */
    EC_GROUP *gen_group;
    /* message digest */
    const EVP_MD *md;
    /* Duplicate key if custom cofactor needed */
    EC_KEY *co_key;
    /* Cofactor mode */
    signed char cofactor_mode;
    /* KDF (if any) to use for ECDH */
    char kdf_type;
    /* Message digest to use for key derivation */
    const EVP_MD *kdf_md;
    /* User key material */
    unsigned char *kdf_ukm;
    size_t kdf_ukmlen;
    /* KDF output length */
    size_t kdf_outlen;
} EC_PKEY_CTX;

const int block_sizes[4] = {
	sizeof(long long int),
	sizeof(int),
	sizeof(short int),
	1 //sizeof(char)
};

void memxor(void* dst, const void* src, size_t n) {
    unsigned char *dst_c;
    short int *dst_s;
    int *dst_i;
    long long int *dst_ll;

    const unsigned char *src_c;
    const short int *src_s;
    const int *src_i;
    const long long int *src_ll;

    size_t remaining;

	dst_c     = dst;
	src_c     = src;
	remaining = n;

	for (size_t i = 0; i < sizeof(block_sizes); ++i) {
		int block_size = block_sizes[i];
		int dst_offset = (uintptr_t)dst % block_size;
		int src_offset = (uintptr_t)src % block_size;
		size_t blocks;
		size_t remainder;
		
		if (dst_offset != src_offset) {
			continue;
		}

		for (int j = 0; j < dst_offset; ++j) {
			dst_c[j] ^= src_c[j];
		}

		remaining -= dst_offset;

		blocks = remaining / block_size;
		remainder = remaining % block_size;

		switch (block_sizes[i]) {
				case sizeof(long long int):
					dst_ll = (long long int*)(dst_c + dst_offset);
					src_ll = (long long int*)(src_c + dst_offset);
				break;
				case sizeof(int):
					dst_i = (int*)(dst_c + dst_offset);
					src_i = (int*)(src_c + dst_offset);
				break;
				case sizeof(short):
					dst_s = (short int*)(dst_c + dst_offset);
					src_s = (short int*)(src_c + dst_offset);
				break;
				case 1:
					dst_c += dst_offset;
					src_c += dst_offset;
				break;
				default:
				exit(1);
			}

		for (size_t j = 0; j < blocks; ++j) {
			switch (block_size) {
				case sizeof(long long int):
					dst_ll[j] ^= src_ll[j];
				break;
				case sizeof(int):
					dst_i[j] ^= src_i[j];
				break;
				case sizeof(short):
					dst_s[j] ^= src_s[j];
				break;
				case 1:
					dst_c[j] ^= src_c[j];
				break;
				default:
				exit(1);
			}
		}

		dst_c = (unsigned char*)dst + (remaining - remainder);
		src_c = (unsigned char*)src + (remaining - remainder);

		for (size_t j = 0; j < remainder; ++j) {
			dst_c[j] ^= src_c[j];
		}

		break;
	}
}

static int pkey_ec_init(EVP_PKEY_CTX *ctx)
{
    EC_PKEY_CTX *dctx;

    if ((dctx = OPENSSL_zalloc(sizeof(*dctx))) == NULL) {
        ECerr(EC_F_PKEY_EC_INIT, ERR_R_MALLOC_FAILURE);
        return 0;
    }

    dctx->cofactor_mode = -1;
    dctx->kdf_type = EVP_PKEY_ECDH_KDF_NONE;
    ctx->data = dctx;
    return 1;
}

static int pkey_ec_copy(EVP_PKEY_CTX *dst, const EVP_PKEY_CTX *src)
{
    EC_PKEY_CTX *dctx, *sctx;
    if (!pkey_ec_init(dst))
        return 0;
    sctx = src->data;
    dctx = dst->data;
    if (sctx->gen_group) {
        dctx->gen_group = EC_GROUP_dup(sctx->gen_group);
        if (!dctx->gen_group)
            return 0;
    }
    dctx->md = sctx->md;

    if (sctx->co_key) {
        dctx->co_key = EC_KEY_dup(sctx->co_key);
        if (!dctx->co_key)
            return 0;
    }
    dctx->kdf_type = sctx->kdf_type;
    dctx->kdf_md = sctx->kdf_md;
    dctx->kdf_outlen = sctx->kdf_outlen;
    if (sctx->kdf_ukm) {
        dctx->kdf_ukm = OPENSSL_memdup(sctx->kdf_ukm, sctx->kdf_ukmlen);
        if (!dctx->kdf_ukm)
            return 0;
    } else
        dctx->kdf_ukm = NULL;
    dctx->kdf_ukmlen = sctx->kdf_ukmlen;
    return 1;
}

static void pkey_ec_cleanup(EVP_PKEY_CTX *ctx)
{
    EC_PKEY_CTX *dctx = ctx->data;
    if (dctx != NULL) {
        EC_GROUP_free(dctx->gen_group);
        EC_KEY_free(dctx->co_key);
        OPENSSL_free(dctx->kdf_ukm);
        OPENSSL_free(dctx);
        ctx->data = NULL;
    }
}

static int pkey_ec_sign(EVP_PKEY_CTX *ctx, unsigned char *sig, size_t *siglen,
                        const unsigned char *tbs, size_t tbslen)
{
    int ret, type;
    unsigned int sltmp;
    EC_PKEY_CTX *dctx = ctx->data;
    EC_KEY *ec = ctx->pkey->pkey.ec;
    const int sig_sz = ECDSA_size(ec);

    /* ensure cast to size_t is safe */
    if (!ossl_assert(sig_sz > 0))
        return 0;

    if (sig == NULL) {
        *siglen = (size_t)sig_sz;
        return 1;
    }

    if (*siglen < (size_t)sig_sz) {
        ECerr(EC_F_PKEY_EC_SIGN, EC_R_BUFFER_TOO_SMALL);
        return 0;
    }

    type = (dctx->md != NULL) ? EVP_MD_type(dctx->md) : NID_sha1;

    ret = ECDSA_sign(type, tbs, tbslen, sig, &sltmp, ec);

    if (ret <= 0)
        return ret;
    *siglen = (size_t)sltmp;
    return 1;
}

static int pkey_ec_verify(EVP_PKEY_CTX *ctx,
                          const unsigned char *sig, size_t siglen,
                          const unsigned char *tbs, size_t tbslen)
{
    int ret, type;
    EC_PKEY_CTX *dctx = ctx->data;
    EC_KEY *ec = ctx->pkey->pkey.ec;

    if (dctx->md)
        type = EVP_MD_type(dctx->md);
    else
        type = NID_sha1;

    ret = ECDSA_verify(type, tbs, tbslen, sig, siglen, ec);

    return ret;
}

#ifndef OPENSSL_NO_EC
static int pkey_ec_derive(EVP_PKEY_CTX *ctx, unsigned char *key, size_t *keylen)
{
    int ret;
    size_t outlen;
    const EC_POINT *pubkey = NULL;
    EC_KEY *eckey;
    EC_PKEY_CTX *dctx = ctx->data;
    if (!ctx->pkey || !ctx->peerkey) {
        ECerr(EC_F_PKEY_EC_DERIVE, EC_R_KEYS_NOT_SET);
        return 0;
    }

    eckey = dctx->co_key ? dctx->co_key : ctx->pkey->pkey.ec;

    if (!key) {
        const EC_GROUP *group;
        group = EC_KEY_get0_group(eckey);
        *keylen = (EC_GROUP_get_degree(group) + 7) / 8;
        return 1;
    }
    pubkey = EC_KEY_get0_public_key(ctx->peerkey->pkey.ec);

    /*
     * NB: unlike PKCS#3 DH, if *outlen is less than maximum size this is not
     * an error, the result is truncated.
     */

    outlen = *keylen;

    ret = ECDH_compute_key(key, outlen, pubkey, eckey, 0);
    if (ret <= 0)
        return 0;
    *keylen = ret;
    return 1;
}

static int pkey_ec_kdf_derive(EVP_PKEY_CTX *ctx,
                              unsigned char *key, size_t *keylen)
{
    EC_PKEY_CTX *dctx = ctx->data;
    unsigned char *ktmp = NULL;
    size_t ktmplen;
    int rv = 0;
    if (dctx->kdf_type == EVP_PKEY_ECDH_KDF_NONE)
        return pkey_ec_derive(ctx, key, keylen);
    if (!key) {
        *keylen = dctx->kdf_outlen;
        return 1;
    }
    if (*keylen != dctx->kdf_outlen)
        return 0;
    if (!pkey_ec_derive(ctx, NULL, &ktmplen))
        return 0;
    if ((ktmp = OPENSSL_malloc(ktmplen)) == NULL) {
        ECerr(EC_F_PKEY_EC_KDF_DERIVE, ERR_R_MALLOC_FAILURE);
        return 0;
    }
    if (!pkey_ec_derive(ctx, ktmp, &ktmplen))
        goto err;
    /* Do KDF stuff */
    if (!ecdh_KDF_X9_63(key, *keylen, ktmp, ktmplen,
                        dctx->kdf_ukm, dctx->kdf_ukmlen, dctx->kdf_md))
        goto err;
    rv = 1;

 err:
    OPENSSL_clear_free(ktmp, ktmplen);
    return rv;
}
#endif

static int pkey_ec_ctrl(EVP_PKEY_CTX *ctx, int type, int p1, void *p2)
{
    EC_PKEY_CTX *dctx = ctx->data;
    EC_GROUP *group;
    switch (type) {
    case EVP_PKEY_CTRL_EC_PARAMGEN_CURVE_NID:
        group = EC_GROUP_new_by_curve_name(p1);
        if (group == NULL) {
            ECerr(EC_F_PKEY_EC_CTRL, EC_R_INVALID_CURVE);
            return 0;
        }
        EC_GROUP_free(dctx->gen_group);
        dctx->gen_group = group;
        return 1;

    case EVP_PKEY_CTRL_EC_PARAM_ENC:
        if (!dctx->gen_group) {
            ECerr(EC_F_PKEY_EC_CTRL, EC_R_NO_PARAMETERS_SET);
            return 0;
        }
        EC_GROUP_set_asn1_flag(dctx->gen_group, p1);
        return 1;

#ifndef OPENSSL_NO_EC
    case EVP_PKEY_CTRL_EC_ECDH_COFACTOR:
        if (p1 == -2) {
            if (dctx->cofactor_mode != -1)
                return dctx->cofactor_mode;
            else {
                EC_KEY *ec_key = ctx->pkey->pkey.ec;
                return EC_KEY_get_flags(ec_key) & EC_FLAG_COFACTOR_ECDH ? 1 : 0;
            }
        } else if (p1 < -1 || p1 > 1)
            return -2;
        dctx->cofactor_mode = p1;
        if (p1 != -1) {
            EC_KEY *ec_key = ctx->pkey->pkey.ec;
            if (!ec_key->group)
                return -2;
            /* If cofactor is 1 cofactor mode does nothing */
            if (BN_is_one(ec_key->group->cofactor))
                return 1;
            if (!dctx->co_key) {
                dctx->co_key = EC_KEY_dup(ec_key);
                if (!dctx->co_key)
                    return 0;
            }
            if (p1)
                EC_KEY_set_flags(dctx->co_key, EC_FLAG_COFACTOR_ECDH);
            else
                EC_KEY_clear_flags(dctx->co_key, EC_FLAG_COFACTOR_ECDH);
        } else {
            EC_KEY_free(dctx->co_key);
            dctx->co_key = NULL;
        }
        return 1;
#endif

    case EVP_PKEY_CTRL_EC_KDF_TYPE:
        if (p1 == -2)
            return dctx->kdf_type;
        if (p1 != EVP_PKEY_ECDH_KDF_NONE && p1 != EVP_PKEY_ECDH_KDF_X9_63)
            return -2;
        dctx->kdf_type = p1;
        return 1;

    case EVP_PKEY_CTRL_EC_KDF_MD:
        dctx->kdf_md = p2;
        return 1;

    case EVP_PKEY_CTRL_GET_EC_KDF_MD:
        *(const EVP_MD **)p2 = dctx->kdf_md;
        return 1;

    case EVP_PKEY_CTRL_EC_KDF_OUTLEN:
        if (p1 <= 0)
            return -2;
        dctx->kdf_outlen = (size_t)p1;
        return 1;

    case EVP_PKEY_CTRL_GET_EC_KDF_OUTLEN:
        *(int *)p2 = dctx->kdf_outlen;
        return 1;

    case EVP_PKEY_CTRL_EC_KDF_UKM:
        OPENSSL_free(dctx->kdf_ukm);
        dctx->kdf_ukm = p2;
        if (p2)
            dctx->kdf_ukmlen = p1;
        else
            dctx->kdf_ukmlen = 0;
        return 1;

    case EVP_PKEY_CTRL_GET_EC_KDF_UKM:
        *(unsigned char **)p2 = dctx->kdf_ukm;
        return dctx->kdf_ukmlen;

    case EVP_PKEY_CTRL_MD:
        if (EVP_MD_type((const EVP_MD *)p2) != NID_sha1 &&
            EVP_MD_type((const EVP_MD *)p2) != NID_ecdsa_with_SHA1 &&
            EVP_MD_type((const EVP_MD *)p2) != NID_sha224 &&
            EVP_MD_type((const EVP_MD *)p2) != NID_sha256 &&
            EVP_MD_type((const EVP_MD *)p2) != NID_sha384 &&
            EVP_MD_type((const EVP_MD *)p2) != NID_sha512 &&
            EVP_MD_type((const EVP_MD *)p2) != NID_sha3_224 &&
            EVP_MD_type((const EVP_MD *)p2) != NID_sha3_256 &&
            EVP_MD_type((const EVP_MD *)p2) != NID_sha3_384 &&
            EVP_MD_type((const EVP_MD *)p2) != NID_sha3_512 &&
            EVP_MD_type((const EVP_MD *)p2) != NID_sm3) {
            ECerr(EC_F_PKEY_EC_CTRL, EC_R_INVALID_DIGEST_TYPE);
            return 0;
        }
        dctx->md = p2;
        return 1;

    case EVP_PKEY_CTRL_GET_MD:
        *(const EVP_MD **)p2 = dctx->md;
        return 1;

    case EVP_PKEY_CTRL_PEER_KEY:
        /* Default behaviour is OK */
    case EVP_PKEY_CTRL_DIGESTINIT:
    case EVP_PKEY_CTRL_PKCS7_SIGN:
    case EVP_PKEY_CTRL_CMS_SIGN:
        return 1;

    default:
        return -2;

    }
}

static int pkey_ec_ctrl_str(EVP_PKEY_CTX *ctx,
                            const char *type, const char *value)
{
    if (strcmp(type, "ec_paramgen_curve") == 0) {
        int nid;
        nid = EC_curve_nist2nid(value);
        if (nid == NID_undef)
            nid = OBJ_sn2nid(value);
        if (nid == NID_undef)
            nid = OBJ_ln2nid(value);
        if (nid == NID_undef) {
            ECerr(EC_F_PKEY_EC_CTRL_STR, EC_R_INVALID_CURVE);
            return 0;
        }
        return EVP_PKEY_CTX_set_ec_paramgen_curve_nid(ctx, nid);
    } else if (strcmp(type, "ec_param_enc") == 0) {
        int param_enc;
        if (strcmp(value, "explicit") == 0)
            param_enc = 0;
        else if (strcmp(value, "named_curve") == 0)
            param_enc = OPENSSL_EC_NAMED_CURVE;
        else
            return -2;
        return EVP_PKEY_CTX_set_ec_param_enc(ctx, param_enc);
    } else if (strcmp(type, "ecdh_kdf_md") == 0) {
        const EVP_MD *md;
        if ((md = EVP_get_digestbyname(value)) == NULL) {
            ECerr(EC_F_PKEY_EC_CTRL_STR, EC_R_INVALID_DIGEST);
            return 0;
        }
        return EVP_PKEY_CTX_set_ecdh_kdf_md(ctx, md);
    } else if (strcmp(type, "ecdh_cofactor_mode") == 0) {
        int co_mode;
        co_mode = atoi(value);
        return EVP_PKEY_CTX_set_ecdh_cofactor_mode(ctx, co_mode);
    }

    return -2;
}

static int pkey_ec_paramgen(EVP_PKEY_CTX *ctx, EVP_PKEY *pkey)
{
    EC_KEY *ec = NULL;
    EC_PKEY_CTX *dctx = ctx->data;
    int ret;

    if (dctx->gen_group == NULL) {
        ECerr(EC_F_PKEY_EC_PARAMGEN, EC_R_NO_PARAMETERS_SET);
        return 0;
    }
    ec = EC_KEY_new();
    if (ec == NULL)
        return 0;
    if (!(ret = EC_KEY_set_group(ec, dctx->gen_group))
        || !ossl_assert(ret = EVP_PKEY_assign_EC_KEY(pkey, ec)))
        EC_KEY_free(ec);
    return ret;
}

static int pkey_ec_keygen(EVP_PKEY_CTX *ctx, EVP_PKEY *pkey)
{
    EC_KEY *ec = NULL;
    EC_PKEY_CTX *dctx = ctx->data;
    int ret;

    if (ctx->pkey == NULL && dctx->gen_group == NULL) {
        ECerr(EC_F_PKEY_EC_KEYGEN, EC_R_NO_PARAMETERS_SET);
        return 0;
    }
    ec = EC_KEY_new();
    if (ec == NULL)
        return 0;
    if (!ossl_assert(EVP_PKEY_assign_EC_KEY(pkey, ec))) {
        EC_KEY_free(ec);
        return 0;
    }
    /* Note: if error is returned, we count on caller to free pkey->pkey.ec */
    if (ctx->pkey != NULL)
        ret = EVP_PKEY_copy_parameters(pkey, ctx->pkey);
    else
        ret = EC_KEY_set_group(ec, dctx->gen_group);

    return ret ? EC_KEY_generate_key(ec) : 0;
}

int pkey_ec_asym_encrypt_init(EVP_PKEY_CTX *ctx) {
	EC_PKEY_CTX *dctx = ctx->data;
	EC_KEY *ec_peerkey = EC_KEY_new();
	EVP_PKEY* peerkey = EVP_PKEY_new();
    int ret = 1;

    if (ctx->pkey == NULL && dctx->gen_group == NULL) {
        ECerr(EC_F_PKEY_EC_ENCRYPT, EC_R_NO_PARAMETERS_SET);
        ret = 0;
        goto cleanup;
    }

    if (EVP_PKEY_derive_init(ctx) <= 0) {
		ret = 0;
		goto cleanup;
	}

    dctx->kdf_type = EVP_PKEY_ECDH_KDF_X9_63;
	dctx->kdf_md = EVP_sha256();
	dctx->kdf_outlen = 32;

	if (!ec_peerkey) {
		ret = 0;
		goto cleanup;
	}

	if (!EVP_PKEY_assign_EC_KEY(peerkey, ec_peerkey)) {
        EC_KEY_free(ec_peerkey);
		ret = 0;
		goto cleanup;
	}

    if (ctx->pkey != NULL)
        ret = EVP_PKEY_copy_parameters(peerkey, ctx->pkey);
    else
        ret = EC_KEY_set_group(ec_peerkey, dctx->gen_group);

    if (!EC_KEY_generate_key(ec_peerkey)) {
		ret = 0;
		goto cleanup;
	}

    if (EVP_PKEY_derive_set_peer(ctx, peerkey) <= 0) {
		ret = 0;
		goto cleanup;
	}

    ctx->operation = EVP_PKEY_OP_ENCRYPT;

	cleanup:
    //EVP_PKEY_CTX has a copy of this key, so it's OK to delete the original
	EVP_PKEY_free(peerkey);
	return ret;
}

int pkey_ec_asym_encrypt(EVP_PKEY_CTX *ctx,
                     unsigned char *out, size_t *outlen,
                     const unsigned char *in, size_t inlen) {
	EC_PKEY_CTX *dctx = ctx->data;
	EVP_PKEY *tmp = NULL;
	int bufSz = 0;
	unsigned char *buf = NULL;
	int ret = 0;
	unsigned char *derived = NULL;
	size_t derivedlen = 0;
    int hmac_keylen = 32;
    int hashlen = 0;
    size_t actual_hashlen = 0;
    EVP_MAC *hmac = NULL;
    EVP_MAC_CTX *hmac_ctx = NULL;
    OSSL_PARAM params[3], *p = params;

    hmac = EVP_MAC_fetch(NULL, "HMAC", NULL);
	derivedlen = inlen + hmac_keylen;
	dctx->kdf_outlen = derivedlen;
	derived = OPENSSL_malloc(derivedlen);
	bufSz = i2d_PublicKey(ctx->peerkey, &buf);

    if (!hmac) {
        ECerr(EC_F_PKEY_EC_ENCRYPT, EC_R_INVALID_DIGEST_TYPE);
        ret = 0;
        goto cleanup;
    }

    hmac_ctx = EVP_MAC_CTX_new(hmac);

    // we have to set parameters before we can get the MAC size
    // the key we set here is a dummy, because we need the MAC size before we can generate the real key
    *p++ = OSSL_PARAM_construct_utf8_string(OSSL_MAC_PARAM_DIGEST, "SHA256", 0);
    *p++ = OSSL_PARAM_construct_octet_string(OSSL_MAC_PARAM_KEY, "dummy", 5);
    *p = OSSL_PARAM_construct_end();
    EVP_MAC_CTX_set_params(hmac_ctx, params);
    p = params;

    hashlen = EVP_MAC_size(hmac_ctx);

    if (!ctx->pkey || !ctx->peerkey) {
        ECerr(EC_F_PKEY_EC_ENCRYPT, EC_R_KEYS_NOT_SET);
        ret = 0;
        goto cleanup;
    }

    if (bufSz + inlen + hashlen > *outlen) {
        ECerr(EC_F_PKEY_EC_DECRYPT, EC_R_BUFFER_TOO_SMALL);
		ret = 0;
		goto cleanup;
	}
    
	/* Do a switcharoo here so that the peer key's private key is used */
	tmp = ctx->pkey;
	ctx->pkey = ctx->peerkey;
	ctx->peerkey = tmp;
	if (!pkey_ec_kdf_derive(ctx, derived, &derivedlen)) {
		ret = 0;
		goto cleanup;
	}

	if (derivedlen != inlen + hmac_keylen) {
		ret = 0;
		goto cleanup;
	}

	*outlen = bufSz + inlen + hashlen;

	// encrypt given payload
	memxor(derived, in, inlen);
    memcpy(out, buf, bufSz);
	memcpy(out + bufSz, derived, inlen);

    //Now we set the real MAC parameters
    *p++ = OSSL_PARAM_construct_utf8_string(OSSL_MAC_PARAM_DIGEST, "SHA256", 0);
    *p++ = OSSL_PARAM_construct_octet_string(
        OSSL_MAC_PARAM_KEY,
        derived + inlen,
        hmac_keylen
        );
    *p = OSSL_PARAM_construct_end();
    EVP_MAC_CTX_set_params(hmac_ctx, params);
    // calculate HMAC of plaintext, placing it directly into the output buffer
    EVP_MAC_init(hmac_ctx);
    EVP_MAC_update(hmac_ctx, in, inlen);
    EVP_MAC_final(hmac_ctx, out + bufSz + inlen, &actual_hashlen, hashlen);

    OPENSSL_assert(hashlen == actual_hashlen);

	ret = 1;

	cleanup:
    if (hmac)
        EVP_MAC_free(hmac);
    
    if (hmac_ctx)
        EVP_MAC_CTX_free(hmac_ctx);

    OPENSSL_free(derived);
    OPENSSL_free(buf);
    
    /* undo switcharoo */
	tmp = ctx->pkey;
	ctx->pkey = ctx->peerkey;
	ctx->peerkey = tmp;

	return ret;
}

int pkey_ec_asym_decrypt_init(EVP_PKEY_CTX *ctx) {
	EC_PKEY_CTX *dctx = ctx->data;
    int ret = 1;

    if (EVP_PKEY_derive_init(ctx) <= 0) {
		ret = 0;
		goto cleanup;
	}

    dctx->kdf_type = EVP_PKEY_ECDH_KDF_X9_63;
	dctx->kdf_md = EVP_sha256();
	dctx->kdf_outlen = 32;

    ctx->operation = EVP_PKEY_OP_DECRYPT;

	cleanup:
	return ret;
}

int pkey_ec_asym_decrypt(EVP_PKEY_CTX *ctx,
                     unsigned char *out, size_t *outlen,
                     const unsigned char *in, size_t inlen) {
    int ret = 0;
    EVP_PKEY *peerkey = NULL;
    EVP_PKEY *tmp = NULL;
    EC_PKEY_CTX *dctx = ctx->data;
    EVP_MAC *hmac = NULL;
    EVP_MAC_CTX *hmac_ctx = NULL;
    OSSL_PARAM params[3], *p = params;
    unsigned char *derived = NULL;
    unsigned char* md;
    size_t derivedlen = 0;
    int hmac_keylen = 32;
    size_t md_len = 0;
    int hashlen = 0;

    hmac = EVP_MAC_fetch(NULL, "HMAC", NULL);
	derivedlen = inlen + hmac_keylen;
	dctx->kdf_outlen = derivedlen;
	derived = OPENSSL_malloc(derivedlen);

    if (!hmac) {
        ECerr(EC_F_PKEY_EC_ENCRYPT, EC_R_INVALID_DIGEST_TYPE);
        ret = 0;
        goto cleanup;
    }

    hmac_ctx = EVP_MAC_CTX_new(hmac);

    // we have to set parameters before we can get the MAC size
    // the key we set here is a dummy, because we need the MAC size 
    // before we can generate the real key
    *p++ = OSSL_PARAM_construct_utf8_string(OSSL_MAC_PARAM_DIGEST, "SHA256", 0);
    *p++ = OSSL_PARAM_construct_octet_string(OSSL_MAC_PARAM_KEY, "dummy", 5);
    *p = OSSL_PARAM_construct_end();
    EVP_MAC_CTX_set_params(hmac_ctx, params);
    p = params;

    hashlen = EVP_MAC_size(hmac_ctx);
    md = OPENSSL_malloc(hashlen);

    if (ctx->pkey == NULL) {
        ECerr(EC_F_PKEY_EC_DECRYPT, EC_R_NO_PARAMETERS_SET);
        ret = 0;
        goto cleanup;
    }

    EC_KEY* ec_key = ctx->pkey->pkey.ec;
    int keysize = EC_POINT_point2oct(ec_key->group, ec_key->pub_key,
                                 ec_key->conv_form, NULL, 0, NULL);

    // this call moves the "in" pointer to the end of the key
    peerkey = d2i_PublicKey(EVP_PKEY_EC, &ctx->pkey, &in, keysize);

    if (!peerkey) {
        ret = 0;
        goto cleanup;
    }

    derivedlen = inlen - keysize;
    dctx->kdf_outlen = derivedlen;
    derived = OPENSSL_malloc(derivedlen);

    if (*outlen < derivedlen - hashlen) {
        ECerr(EC_F_PKEY_EC_DECRYPT, EC_R_BUFFER_TOO_SMALL);
        ret = 0;
        goto cleanup;
    }

    *outlen = derivedlen - hashlen;

    if (EVP_PKEY_derive_set_peer(ctx, peerkey) <= 0) {
		ret = 0;
		goto cleanup;
	}

    /* Do a switcharoo here so that the peer key's private key is used */
	tmp = ctx->pkey;
	ctx->pkey = ctx->peerkey;
	ctx->peerkey = tmp;

    if (!pkey_ec_kdf_derive(ctx, derived, &derivedlen)) {
		ret = 0;
		goto cleanup;
	}

    if (derivedlen != *outlen + hmac_keylen) {
        ECerr(EC_F_PKEY_EC_DECRYPT, EC_R_SHARED_INFO_ERROR);
        ret = 0;
        goto cleanup;
    }

    // decrypt data
    memcpy(out, in, *outlen);
    memxor(out, derived, *outlen);

    //Now we set the real MAC parameters
    *p++ = OSSL_PARAM_construct_utf8_string(OSSL_MAC_PARAM_DIGEST, "SHA256", 0);
    *p++ = OSSL_PARAM_construct_octet_string(
        OSSL_MAC_PARAM_KEY,
        derived + *outlen,
        hmac_keylen
        );
    *p = OSSL_PARAM_construct_end();
    EVP_MAC_CTX_set_params(hmac_ctx, params);
    // calculate HMAC of plaintext, placing it directly into the output buffer
    EVP_MAC_init(hmac_ctx);
    EVP_MAC_update(hmac_ctx, out, *outlen);
    EVP_MAC_final(hmac_ctx, md, &md_len, hashlen);

    OPENSSL_assert(md_len == hashlen);

    if (CRYPTO_memcmp(in + *outlen, md, hashlen) != 0)
    {
        ECerr(EC_F_PKEY_EC_DECRYPT, EC_R_INVALID_DIGEST);
        memset(out, 0, *outlen);
        ret = 0;
        goto cleanup;
    }

    ret = 1;

    cleanup:
    if (tmp) {
        /* undo switcharoo */
        tmp = ctx->pkey;
        ctx->pkey = ctx->peerkey;
        ctx->peerkey = tmp;
    }
    if (hmac)
        EVP_MAC_free(hmac); 
    if (hmac_ctx)
        EVP_MAC_CTX_free(hmac_ctx);
    if (derived)
        OPENSSL_free(derived);
    if (peerkey)
        EVP_PKEY_free(peerkey);
    if (md)
        OPENSSL_free(md);
    return ret;
}

static const EVP_PKEY_METHOD ec_pkey_meth = {
    EVP_PKEY_EC,
    0,
    pkey_ec_init,
    pkey_ec_copy,
    pkey_ec_cleanup,

    0,
    pkey_ec_paramgen,

    0,
    pkey_ec_keygen,

    0,
    pkey_ec_sign,

    0,
    pkey_ec_verify,

    0, 0,

    0, 0, 0, 0,

    pkey_ec_asym_encrypt_init,
    pkey_ec_asym_encrypt,

    pkey_ec_asym_decrypt_init,
    pkey_ec_asym_decrypt,

    0,
#ifndef OPENSSL_NO_EC
    pkey_ec_kdf_derive,
#else
    0,
#endif
    pkey_ec_ctrl,
    pkey_ec_ctrl_str
};

const EVP_PKEY_METHOD *ec_pkey_method(void)
{
    return &ec_pkey_meth;
}
