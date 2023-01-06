from sage.all import matrix, identity_matrix, lcm, CRT_list, randrange, seed
from aer import AER
from time import time

def find_dlog(base, target):
    return target.log(base)


gens = [
    # rank, log2('matrix period'), matrix_order, matrix
    (3, 24, 16777215, [
        158, 215, 6,
        216, 221, 53,
        45, 119, 206]),
    (4, 32, 4294967295, [
        210, 72, 68, 31,
        156, 225, 86, 224,
        75, 171, 53, 252,
        38, 22, 171, 109]),
    (7, 96, 282578783239935, [
        147, 65, 106, 219, 36, 20, 37,
        125, 14, 216, 138, 90, 186, 10,
        67, 90, 56, 25, 234, 130, 86,
        156, 242, 122, 74, 146, 218, 128,
        19, 55, 159, 189, 5, 142, 114,
        236, 247, 81, 75, 124, 61, 121,
        119, 15, 112, 21, 195, 25, 118]),
    (10, 112, 18518801667747479295, [
        222, 179, 28, 115, 147, 20, 69, 102, 39, 46,
        233, 103, 227, 60, 170, 63, 13, 0, 203, 20,
        70, 52, 2, 77, 155, 51, 203, 221, 185, 27,
        234, 69, 0, 3, 113, 112, 137, 237, 143, 140,
        92, 243, 15, 70, 59, 75, 141, 157, 213, 251,
        75, 208, 88, 243, 83, 17, 130, 10, 129, 4,
        241, 97, 241, 224, 192, 213, 105, 53, 232, 226,
        41, 15, 123, 22, 144, 73, 111, 228, 191, 15,
        83, 131, 155, 183, 158, 84, 183, 144, 189, 78,
        126, 35, 224, 17, 157, 124, 32, 140, 118, 226]),
    (12, 160, 1208925819614629174706175, [255, 21, 43, 199, 233, 44, 168, 110, 205, 105, 190, 140,
        254, 241, 192, 46, 189, 239, 112, 129, 236, 114, 30, 162,
        78, 182, 117, 99, 1, 213, 173, 144, 178, 105, 22, 104,
        235, 237, 38, 152, 100, 43, 160, 194, 10, 230, 22, 237,
        29, 127, 72, 1, 236, 4, 152, 37, 13, 125, 205, 108,
        55, 159, 168, 196, 238, 6, 139, 43, 155, 146, 100, 112,
        133, 25, 117, 59, 130, 198, 212, 87, 109, 42, 105, 147,
        147, 254, 177, 199, 205, 140, 60, 115, 72, 225, 7, 45,
        198, 136, 42, 71, 13, 95, 115, 146, 195, 245, 68, 31,
        239, 56, 211, 16, 19, 67, 207, 229, 203, 155, 94, 105,
        41, 182, 182, 57, 223, 173, 161, 246, 32, 71, 233, 120,
        17, 43, 171, 195, 86, 58, 255, 237, 158, 65, 84, 9])
]


def algorithm_2(dim, g0, g):
    """ Algorithm 2 from https://www.math.uwaterloo.ca/~ajmeneze/publications/glnq.pdf
    """
    # Step 1
    pA = g0.charpoly()

    # Step 2
    f = []
    m = []
    for f_i, e_i in list(pA.factor()):
        assert(f_i.is_irreducible())
        f.append(f_i)
        m.append(f[-1].degree())
    s = len(f)

    alpha = []
    Fqm = []
    for i in range(s):
        # Let Sage build F_{q^{m_i}}, this results in easier computation of kernels later
        Fqmi = f[i].splitting_field('alpha_%d_var' % i)
        alpha.append(list(r[0] for r in f[i].change_ring(Fqmi).roots()))

        # check they are roots
        for root in alpha[-1]:
            assert(f[i](root) == 0)

        # store how you build F_{q^{m_i}}
        Fqm.append(Fqmi)

    # Step 3
    c = []
    mu = []
    Q = []
    D = []
    order_alpha = []
    alpha_dlog_pairs = []
    for i in range(s):
        # Step 3.1
        mat = g0.change_ring(Fqm[i]) - alpha[i][0] * identity_matrix(dim)
        l = 1
        matl = mat
        rl = matl.rank()
        while True:
            matlp1 = matl*mat
            rlp1 = (matlp1).rank()
            if rl == rlp1:
                c.append(l)
                break
            l += 1
            rl = rlp1
            matl = matlp1

        # Step 3.2
        ker = mat.right_kernel()
        mu_i = ker.basis_matrix()[0]
        mu.append(mu_i)

        # Step 3.3
        Q_i = matrix(mu_i, nrows=dim, ncols=1).augment(identity_matrix(Fqm[i], dim)[1:].transpose())
        assert(Q_i.is_invertible())
        Q.append(Q_i)

        # Step 3.4
        D_i = Q_i.inverse() * g.change_ring(Fqm[i]) * Q_i
        D.append(D_i)

        # Step 3.5
        alpha_l = D_i[0][0]
        alpha_dlog_pairs.append((alpha[i][0], alpha_l))

        # find the order of alpha[i][0]
        for ord_al in (alpha[i][0].parent().cardinality()-1).divisors():
            pow_al = alpha[i][0]**ord_al
            if pow_al == 1:
                break
        assert(alpha[i][0] ** ord_al == 1)
        order_alpha.append(ord_al)

    dlogs = []
    for i in range(s):
        alpha, alpha_l = alpha_dlog_pairs[i]
        dlog_al_al_l = find_dlog(alpha, alpha_l)
        dlogs.append(dlog_al_al_l)
        ord_al = order_alpha[i]
        # print(f"({alpha})^({dlog_al_al_l}) = ({alpha**dlog_al_al_l}) == ({alpha_l})")
        # print(f"l mod ({ord_al}) = ({dlog_al_al_l})")

    # Step 4
    t = max(c)
    if t > 1:
        raise NotImplementedError()
    else:
        p_t = 1

    ord_A = p_t * lcm(order_alpha)
    assert(g0**(ord_A) == identity_matrix(dim))

    l = CRT_list(dlogs, order_alpha)
    return l, ord_A


def main(tries=128, prng_seed=0xdeadbeef, verbose=False):
    runtime = {}
    with seed(prng_seed):
        print('| {:>2} | {:>6} | {:>15} |'.format(*("k", "tries", "avg runtime (s)")))
        for dim, log_period, _, generator in gens:
            aer = AER(rank=dim)
            aes_field = aer.base_field
            g0 = aer.space(map(aes_field.from_integer, generator))
            runtime[dim] = 0
            for t in range(tries):
                if verbose:
                    print(f"rank {dim} try {t+1}/{tries}")
                else:
                    print(f"\rrank {dim} try {t+1}/{tries}", end='    ')
                r = randrange(1, 2**log_period)
                g = g0 ** r

                dt = time()
                l, ord_g0 = algorithm_2(dim, g0, g)
                dt = time() - dt
                runtime[dim] += dt
                assert(g0**l == g)
                assert(g0**ord_g0 == identity_matrix(dim))
                if verbose:
                    print("        ord(g0) =", ord_g0)
                    print("matrix 'period' =", 2**log_period)
                    print("              r =", r)
                    print("  r mod ord(g0) =", r % ord_g0)
                    print("              l =", l)
                    print()
            runtime[dim] /= tries
            print('\r| {:>2} | {:>6} | {:>15} |'.format(*(dim, tries, "%.6f" % runtime[dim])))

if __name__ == "__main__":
    import argparse
    parser = argparse.ArgumentParser()
    parser.add_argument('-v', '--verbose', action='store_true', help='print element orders')
    parser.add_argument('-t', '--tries', type=int, default=128, help='number of tries')
    parser.add_argument('-s', '--seed', type=int, default=0xdeadbeef, help='prng seed')
    args = parser.parse_args()
    main(tries=args.tries, prng_seed=args.seed, verbose=args.verbose)