typedef unsigned int WORD;

#define ROTLEFT(a,b) (((a) << (b)) | ((a) >> (32-(b))))
#define ROTRIGHT(a,b) (((a) >> (b)) | ((a) << (32-(b))))

#define CH(x,y,z) (((x) & (y)) ^ (~(x) & (z)))
#define MAJ(x,y,z) (((x) & (y)) ^ ((x) & (z)) ^ ((y) & (z)))
#define EP0(x) (ROTRIGHT(x,2) ^ ROTRIGHT(x,13) ^ ROTRIGHT(x,22))
#define EP1(x) (ROTRIGHT(x,6) ^ ROTRIGHT(x,11) ^ ROTRIGHT(x,25))
#define SIG0(x) (ROTRIGHT(x,7) ^ ROTRIGHT(x,18) ^ ((x) >> 3))
#define SIG1(x) (ROTRIGHT(x,17) ^ ROTRIGHT(x,19) ^ ((x) >> 10))

void sha256(
    WORD * restrict hash, // output hash
    const WORD * restrict data, // assuming data is 64-word aligned, and has a size of num_chunks * 64 * WORD
    int num_chunks,
    const WORD * restrict k, // some magic values, 64 * WORD
    WORD * restrict m, // scratch pad, 64 * WORD
    WORD zero // should be exactly 0; used for avoiding a compilation bug
)
{
	WORD a, b, c, d, e, f, g, h, i, j, t1, t2;
    WORD s0, s1, s2, s3, s4, s5, s6, s7;

    s0 = 0x6a09e667;
	s1 = 0xbb67ae85;
    s2 = 0x3c6ef372;
	s3 = 0xa54ff53a;
	s4 = 0x510e527f;
	s5 = 0x9b05688c;
	s6 = 0x1f83d9ab;
	s7 = 0x5be0cd19;

    for (j = 0; j < num_chunks; j++) {
        a = s0;
        b = s1;
        c = s2;
        d = s3;
        e = s4;
        f = s5;
        g = s6;
        h = s7;

        for (i = 0; i < 64; ++i) {
            if (i < 16) {
                m[i] = data[j * 64 + i];
            } else {
                m[i] = SIG1(m[i - 2]) + m[i - 7] + SIG0(m[i - 15]) + m[i - 16];
            }

            t1 = h + EP1(e) + CH(e,f,g) + k[i] + m[i];
            t2 = EP0(a) + MAJ(a,b,c);
            h = g + zero;
            g = f + zero;
            f = e + zero;
            e = d + t1;
            d = c + zero;
            c = b + zero;
            b = a + zero;
            a = t1 + t2;
        }

        s0 += a;
        s1 += b;
        s2 += c;
        s3 += d;
        s4 += e;
        s5 += f;
        s6 += g;
        s7 += h;
    }

    hash[0] = s0;
    hash[1] = s1;
    hash[2] = s2;
    hash[3] = s3;
    hash[4] = s4;
    hash[5] = s5;
    hash[6] = s6;
    hash[7] = s7;
}
