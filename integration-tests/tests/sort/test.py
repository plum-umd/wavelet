import random
from sim import reference

@reference(
    # Even count may not be correct, but the behavior
    # should still match the reference
    ([0], [0], 0, 0),
    ([random.randint(-20, 20) for _ in range(3)], [0] * 3, 2, 3),
    ([random.randint(-20, 20) for _ in range(6)], [0] * 6, 3, 6),
)
def sort(a, z, even_count, N):
    def cond_read(j, odd):
        return z[j] if odd else a[j]

    def cond_write(j, odd, v):
        if odd:
            a[j] = v
        else:
            z[j] = v

    def compute_next_count(zero_flag, next_count):
        if zero_flag:
            next_count2 = next_count + 1
            return next_count2
        else:
            return next_count

    def sel1(cond, aa, bb):
        return aa if cond else bb

    def sel2(cond, aa, bb):
        return aa if cond else bb

    def sel3(cond, aa, bb):
        return aa if cond else bb

    def pass_aux(j, bit, idx0, idx1, next_count, odd):
        cond = j < N
        if cond:
            v = cond_read(j, odd)
            u = v & 0xFFFFFFFF
            v_shifted = u >> bit
            v_masked = v_shifted & 0x1
            zero = 0
            o = v_masked != zero

            bit_plus_one = bit + 1
            if bit_plus_one >= 32:
                next_mask = 0
            else:
                next_mask = (1 << bit_plus_one) & 0xFFFFFFFF

            v_mask = u & next_mask
            mask_is_zero = (v_mask == 0)

            next_count2 = compute_next_count(mask_is_zero, next_count)
            j1 = j + 1

            idx = sel1(o, idx1, idx0)
            idx1b = idx1 + 1
            idx0b = idx0 + 1

            idx0n = sel2(o, idx0, idx0b)
            idx1n = sel3(o, idx1b, idx1)

            # Write to the chosen destination buffer
            safe = idx < N
            if safe:
                cond_write(idx, odd, v)
                return pass_aux(j1, bit, idx0n, idx1n, next_count2, odd)
            else:
                return next_count2
        else:
            return next_count

    def sort_bits_aux(bit, count):
        cond = bit < 32
        if cond:
            zero = 0
            bit_mask = bit & 0x1
            odd = bit_mask != zero

            next_count = pass_aux(0, bit, 0, count, 0, odd)

            bitp1 = bit + 1
            sort_bits_aux(bitp1, next_count)
        else:
            return

    sort_bits_aux(0, even_count)
