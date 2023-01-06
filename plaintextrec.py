import sys
from time import time
from sage.all import GF, matrix, vector, identity_matrix, block_diagonal_matrix
from sage.all import seed, randrange
from sage.all import log
from sage.all import log
from aer import AER
from dlp import algorithm_2


def Gen(prng_seed, rank, poly_degree, exponent_range=(2, 2**30), pk_product="matrix", same_m_n=False):
    aer = AER(rank=rank)
    aes_field = aer.base_field

    with seed(prng_seed):
        m = randrange(*exponent_range)
        n = randrange(*exponent_range)

        A = aer.space(map(aes_field.from_integer, [randrange(256) for x in range(rank**2)]))
        B = aer.space(map(aes_field.from_integer, [randrange(256) for x in range(rank**2)]))

        f_coeffs = [randrange(256) for x in range(poly_degree)]


    fA = aer.field_el_coeff_poly(A, f_coeffs)
    if pk_product == "matrix":
        r = fA**m * B * fA**n
    elif pk_product == "coefficient-wise":
        r = aer.M3(fA**m, B, fA**n)
    else:
        raise ValueError("pk_product must be 'matrix' or 'coefficient-wise'")

    if same_m_n:
        pk = { 'm': m, 'n': n, 'A': A, 'B': B, "r": r, "poly_degree": poly_degree, "rank": rank}
    else:
        pk = { 'A': A, 'B': B, "r": r, "poly_degree": poly_degree, "rank": rank, "exponent_range": exponent_range}
    sk = { "fA": fA }

    return sk, pk


def Encaps(prng_seed, pk, pk_product="matrix", same_m_n=False):
    """ For simplicity of implementation, we replace the PKE Enc function into a KEM Encaps function.
        The attacks against both the PKE and KEM are the same: recover the shared secret.
    """
    aer = AER(rank=pk["rank"])
    with seed(prng_seed):
        h_not_found = True
        while h_not_found:
            h_coeffs = [randrange(256) for x in range(pk["poly_degree"])]
            hA = aer.field_el_coeff_poly(pk["A"], h_coeffs)
            h_not_found = hA.is_zero()
        if same_m_n:
            m = pk["m"]
            n = pk["n"]
        else:
            m = randrange(*pk["exponent_range"])
            n = randrange(*pk["exponent_range"])

    if pk_product == "matrix":
        c1 = hA**m * pk["B"] * hA**n
        ss = hA**m * pk["r"] * hA**n
    elif pk_product == "coefficient-wise":
        c1 = aer.M3(hA**m, pk["B"], hA**n)
        ss = aer.M3(hA**m, pk["r"], hA**n)
    else:
        raise ValueError("pk_product must be 'matrix' or 'coefficient-wise'")

    c = { "c1": c1, "ss": ss }
    return c


def warmup_attack(keygen_prng_seed, encaps_prng_seed, rank=20, poly_degree=40, exponent_range=(2, 2**30), same_m_n=False, verbose=False):
    aer = AER(rank=rank)

    if verbose:
        print(f"k: {rank}, poly_degree: {poly_degree}")
        print("finite field: GF[2,{%s}]" % aer.base_field.modulus)

    if verbose:
        print("Keygen... ", end="")
        sys.stdout.flush()

    _, pk = Gen(keygen_prng_seed, rank, poly_degree, exponent_range=exponent_range, same_m_n=same_m_n, pk_product="coefficient-wise")

    if verbose:
        print("Encaps... ", end="")
        sys.stdout.flush()

    c = Encaps(encaps_prng_seed, pk, same_m_n=same_m_n, pk_product="coefficient-wise")
    r = pk["r"]
    B = pk["B"]
    c1 = c['c1']

    Binv = aer.space([0 if x == 0 else x**-1 for x in vector(B)])
    fAmn = aer.space(vector(r).pairwise_product(vector(Binv)))

    zz = aer.space(vector(fAmn).pairwise_product(vector(c1)))
    if (c["ss"]-zz).is_zero():
        print("recovered the shared secret.")
    else:
        raise Exception("attack failed")


def invertible_fA_attack(rank, pk, c, verbose=False, debug=False, sparse=False):
    aer = AER(rank=rank)

    A = pk["A"]
    B = pk["B"]
    c1 = c["c1"]
    r = pk["r"]

    A = matrix(A, sparse=sparse)
    B = matrix(B, sparse=sparse)
    r = matrix(r, sparse=sparse)

    # we want to solve rA X = Y B with extra constraints that AX = XA and A Y = Y A
    # we turn this into a problem of the form M Z = 0, where M is a constant matrix depending on A, rA, B
    # and Z contains the entries of X and Y
    M = matrix(3 * rank**2, 2 * rank**2, sparse=sparse)
    # first we construct the part of M related to rA X = Y B
    M += matrix(3,2,[[0,1],[0,0],[0,0]], sparse=sparse).tensor_product(identity_matrix(rank, sparse=sparse).tensor_product(-B.transpose()))
    for ind in range(rank):
        M += matrix(3,2,[[1,0],[0,0],[0,0]], sparse=sparse).tensor_product(
            matrix(rank, 1, [int(_ == ind) for _ in range(rank)], sparse=sparse).tensor_product(
                identity_matrix(rank, sparse=sparse).tensor_product(matrix(1, rank, r[ind], sparse=sparse))
            )
        )

    if debug:
        aer.print(M, "M")

    # then the part related to A X = X A and A Y = Y A
    AX_XA = matrix(rank**2, rank**2, sparse=sparse)
    for _r in range(rank):
        AX_XA += matrix(rank, 1, [int(_ == _r) for _ in range(rank)], sparse=sparse).tensor_product(identity_matrix(rank, sparse=sparse).tensor_product(matrix(1, rank, A[_r], sparse=sparse)))

    if debug:
        aer.print(AX_XA, "AX_XA")

    AtXt = matrix(rank**2, rank**2)
    for _r in range(rank):
        AtXt += matrix(rank, 1, [int(_ == _r) for _ in range(rank)], sparse=sparse).tensor_product(identity_matrix(rank, sparse=sparse).tensor_product(matrix(1, rank, A.transpose()[_r], sparse=sparse)))

    if debug:
        aer.print(AtXt, "AtXt")

    P_X_to_Xt = matrix(GF(2), rank**2, rank**2, sparse=sparse)
    for item_row in range(rank**2):
        item_col = ((item_row * rank) % rank**2) + item_row//rank
        P_X_to_Xt.add_to_entry(item_row, item_col, 1)

    if debug:
        aer.print(P_X_to_Xt, "P_X_to_Xt")

    AX_XA = AX_XA - P_X_to_Xt * AtXt * P_X_to_Xt

    if debug:
        aer.print(AX_XA, "AX_XA")

    AY_YA =  AX_XA.transpose() * P_X_to_Xt
    if debug:
        aer.print(AY_YA, "AY_YA")

    M += matrix(3,2,[[0,0],[1,0],[0,0]], sparse=sparse).tensor_product(AX_XA)
    M += matrix(3,2,[[0,0],[0,0],[0,1]], sparse=sparse).tensor_product(AY_YA)

    if debug:
        aer.print(M, "M")

    if debug:
        aer.print(M.echelon_form(), "RowReduce[M]")

    right_kernel = M.right_kernel()
    if debug:
        print("kernel size:", right_kernel.cardinality())
        print()
    cnt = 0
    candidate_zz = []
    for el in right_kernel:
        if el.is_zero():
            continue
        cnt += 1

        if debug:
            aer.print(matrix(list(el)), "sol")

        Y = matrix(rank, list(el)[rank**2:])

        if debug:
            aer.print(Y, "Y")

        X = matrix(rank, list(el)[:rank**2]).transpose()

        if debug:
            aer.print(X, "X")

        if not X.is_invertible():
            if debug:
                print(cnt, "X is not invertible")
            continue
        X_inv = X.inverse()

        # verify they are a solution to the three equations
        assert (r * X - Y * B).is_zero()
        assert (A * X - X * A).is_zero()
        assert (A * Y - Y * A).is_zero()

        zz = Y * c1 * X_inv
        candidate_zz.append(zz)
        break # could search for more

    if debug:
        for zz in candidate_zz:
            aer.print(zz, "candidate encapsulated secret:")

    return candidate_zz[0]


def diagonalisable_A_attack(rank, pk, c, verbose=False, debug=False, sparse=True):
    aer = AER(rank=rank)

    A = pk["A"]
    B = pk["B"]
    r = pk["r"]
    c1 = c['c1']

    sf = A.charpoly().splitting_field('x')
    D, P = A.change_ring(sf).diagonalization()
    D = matrix(D, sparse=sparse)
    P = matrix(P, sparse=sparse)

    r_ = P.inverse() * r * P
    r_ = matrix(r_, sparse=sparse)
    zero_indices = []
    for i in range(rank):
        if vector(r_[i]).is_zero() and vector(r_.transpose()[i]).is_zero():
            zero_indices.append(i)

    pseudo_identity = matrix([identity_matrix(rank)[j] if j not in zero_indices else [0] * rank for j in range(rank)])
    pseudo_identity = matrix(pseudo_identity, sparse=sparse)

    B_ = P.inverse() * B * P * pseudo_identity
    B_ = matrix(B_, sparse=sparse)

    # general sbox
    sbox = lambda x, K: 0 if K(x).is_zero() else 1/K(x)

    if verbose:
        print("building the linear system")
    M = matrix(1 * rank**2, 2 * rank**2, sparse=sparse)

    if verbose:
        print("  main relation")
    M += matrix(1,2,[[0,1]], sparse=sparse).tensor_product(identity_matrix(rank, sparse=sparse).tensor_product(-B_.transpose()))
    for ind in range(rank):
        if verbose:
            print(f"    ind {ind}")
        M += matrix(1,2,[[1,0]], sparse=sparse).tensor_product(
            matrix(rank, 1, [int(_ == ind) for _ in range(rank)], sparse=sparse).tensor_product(
                identity_matrix(rank, sparse=sparse).tensor_product(matrix(1, rank, r_[ind], sparse=sparse))
            )
        )

    # impose X and Y to be diagonal
    if verbose:
        print("  diagonal solutions + zero indices")
    for _r in range(rank):
        for _c in range(rank):
            if _r == _c and _r not in zero_indices:
                continue
            l = [0]*(_r * rank + _c) + [1] + [0]*(rank**2-(_r * rank + _c) - 1)
            M = M.stack(matrix(1, 2 * rank**2, [0]*rank**2 + l, sparse=sparse)) # Y
            M = M.stack(matrix(1, 2 * rank**2, l + [0]*rank**2, sparse=sparse)) # X

    if verbose:
        print("finding the kernel")
    right_kernel = M.right_kernel()

    # decompose an element of the kernel into unknowns
    if verbose:
        print("kernel size:", right_kernel.cardinality())
        print("kernel rank", right_kernel.rank())
    cnt = 0
    candidate_zz = []
    with seed(1):
        for el in right_kernel:
            if el.is_zero():
                continue
            cnt += 1
            found_fDn_inv = matrix(rank, list(el)[:rank**2]).transpose()

            if debug:
                print(found_fDn_inv)
                print()
                if not found_fDn_inv.is_invertible():
                    print(cnt, "X is not invertible")

            found_fDm = matrix(rank, list(el)[rank**2:])

            # rA * u_fAn_inv - u_fAm * B
            assert (r_ * found_fDn_inv - found_fDm * B_).is_zero()
            assert(found_fDm.is_diagonal())
            assert(found_fDn_inv.is_diagonal())

            found_fDn = matrix(sf, [[sbox(x, sf) for x in found_fDn_inv[i]] for i in range(rank)])
            assert(found_fDn.is_diagonal())

            if found_fDm.is_zero() or found_fDn_inv.is_zero():
                continue

            # potentially can speed up checks by getting rid of false attempts early
            if found_fDm[0][0] not in [0, 1] and found_fDn[0][0] not in [0, 1] and found_fDm[1][1] not in [0, 1] and found_fDn[1][1] not in [0, 1]:
                try:
                    dlog = found_fDm[0][0].log(found_fDn[0][0])
                    if found_fDm[1][1] != found_fDn[1][1]*dlog:
                        continue
                except:
                    pass

            found_fAm = P * found_fDm * P.inverse()
            found_fAn = P * found_fDn * P.inverse()

            zz = found_fAm * c1 * found_fAn
            candidate_zz.append(zz)
            if verbose:
                print("   recovered secret:", list(aer.to_integer(zz)))
                print()

            break # could try to check for more candidates
    return candidate_zz[0]


def non_diagonalisable_A_attack(rank, pk, c, verbose=False, debug=False, sparse=True):
    aer = AER(rank=rank)

    A = pk["A"]
    B = pk["B"]
    r = pk["r"]
    c1 = c['c1']

    sf = A.charpoly().splitting_field('x')
    J, P = A.change_ring(sf).jordan_form(transformation=True, sparse=sparse)
    J_blocks = J.get_subdivisions()
    P = matrix(P, sparse=sparse)

    r_ = P.inverse() * r * P
    r_ = matrix(r_, sparse=sparse)

    zero_indices = []
    for i in range(rank):
        if vector(r_[i]).is_zero() and vector(r_.transpose()[i]).is_zero():
            zero_indices.append(i)

    pseudo_identity = matrix([identity_matrix(rank)[j] if j not in zero_indices else [0] * rank for j in range(rank)])
    pseudo_identity = matrix(pseudo_identity, sparse=sparse)

    B_ = P.inverse() * B * P * pseudo_identity
    B_ = matrix(B_, sparse=sparse)

    if verbose:
        print("building the linear system")
    M = matrix(1 * rank**2, 2 * rank**2, sparse=sparse)

    if verbose:
        print("  main relation")
    M += matrix(1,2,[[0,1]], sparse=sparse).tensor_product(identity_matrix(rank, sparse=sparse).tensor_product(-B_.transpose()))
    for ind in range(rank):
        if verbose:
            print(f"    ind {ind}")
        M += matrix(1,2,[[1,0]], sparse=sparse).tensor_product(
            matrix(rank, 1, [int(_ == ind) for _ in range(rank)], sparse=sparse).tensor_product(
                identity_matrix(rank, sparse=sparse).tensor_product(matrix(1, rank, r_[ind], sparse=sparse))
            )
        )

    # impose J and X, and J and Y, to commute
    my_AX_XA = matrix(rank**2, rank**2, sparse=sparse)
    for _r in range(rank):
        my_AX_XA += matrix(rank, 1, [int(_ == _r) for _ in range(rank)], sparse=sparse).tensor_product(identity_matrix(rank, sparse=sparse).tensor_product(matrix(1, rank, J[_r], sparse=sparse)))

    my_AtXt = matrix(rank**2, rank**2, sparse=sparse)
    for _r in range(rank):
        my_AtXt += matrix(rank, 1, [int(_ == _r) for _ in range(rank)], sparse=sparse).tensor_product(identity_matrix(rank, sparse=sparse).tensor_product(matrix(1, rank, J.transpose()[_r], sparse=sparse)))

    my_P_X_to_Xt = matrix(GF(2), rank**2, rank**2, sparse=sparse)
    for item_row in range(rank**2):
        item_col = ((item_row * rank) % rank**2) + item_row//rank
        my_P_X_to_Xt.add_to_entry(item_row, item_col, 1)

    my_AX_XA = my_AX_XA - my_P_X_to_Xt * my_AtXt * my_P_X_to_Xt
    my_AY_YA =  my_AX_XA.transpose() * my_P_X_to_Xt

    M = M.stack(matrix(1,2,[[0,1]], sparse=sparse).tensor_product(my_AX_XA))
    M = M.stack(matrix(1,2,[[0,1]], sparse=sparse).tensor_product(my_AY_YA))

    # impose X and Y to be block-diagonal
    J_blocks = J.get_subdivisions()[0]
    zero_J_indices = []
    for r in range(rank):
        zero_J_indices.append([0] * rank)
    for block in J_blocks:
        for r in range(block, rank):
            for c in range(rank):
                if c < block:
                    zero_J_indices[r][c] = 1
                    zero_J_indices[c][r] = 1

    # impose them to be upper-triangular too
    for r in range(rank):
        for c in range(r):
            zero_J_indices[r][c] = 1

    if verbose:
        print("  diagonal solutions + zero indices")
    for _r in range(rank):
        for _c in range(rank):
            if zero_J_indices[_r][_c] == 0:
                continue
            ly = [0]*(_r * rank + _c) + [1] + [0]*(rank**2-(_r * rank + _c) - 1)
            lx = [0]*(_c * rank + _r) + [1] + [0]*(rank**2-(_c * rank + _r) - 1)
            M = M.stack(matrix(1, 2 * rank**2, [0]*rank**2 + ly, sparse=sparse)) # Y
            M = M.stack(matrix(1, 2 * rank**2, lx + [0]*rank**2, sparse=sparse)) # X

    def get_blocks(m, J_blocks):
        rank = m.dimensions()[0]
        blocks = []
        for i in range(len(J_blocks)+1):
            min_i = 0 if i == 0 else J_blocks[i-1]
            max_i = rank if i == len(J_blocks) else J_blocks[i]
            b = matrix([[m[r][c] for c in range(min_i, max_i)] for r in range(min_i, max_i)])
            blocks.append(b)
        return blocks

    if verbose:
        print("finding the kernel")
    right_kernel = M.right_kernel()

    # decompose an element of the kernel into unknowns
    if verbose:
        print("kernel size:", right_kernel.cardinality())
        print("kernel rank", right_kernel.rank())
    cnt = 0
    candidate_zz = []
    # print()
    with seed(1):
        for el in right_kernel:
            if el.is_zero():
                continue
            cnt += 1
            # print("\r", cnt, end="")
            found_fDn_inv = matrix(rank, list(el)[:rank**2]).transpose()

            if debug:
                print(found_fDn_inv)
                print()
                if not found_fDn_inv.is_invertible():
                    print(cnt, "X is not invertible")

            found_fDm = matrix(rank, list(el)[rank**2:])

            # rA * u_fAn_inv - u_fAm * B
            assert (r_ * found_fDn_inv - found_fDm * B_).is_zero()

            fDn_inv_blocks = get_blocks(found_fDn_inv, J_blocks)
            found_fDn = block_diagonal_matrix([m.inverse() if m.determinant() != 0 else matrix(*m.dimensions()) for m in fDn_inv_blocks])

            if found_fDm.is_zero() or found_fDn_inv.is_zero():
                continue

            # potentially can speed up checks by getting rid of false attempts early
            found_fDn_blocks = get_blocks(found_fDn, J_blocks)
            found_fDm_blocks = get_blocks(found_fDm, J_blocks)
            if found_fDn_blocks[0] not in [matrix(rank), identity_matrix(rank)]\
                and found_fDn_blocks[1] not in [matrix(rank), identity_matrix(rank)]\
                and found_fDm_blocks[0] not in [matrix(rank), identity_matrix(rank)]\
                and found_fDm_blocks[1] not in [matrix(rank), identity_matrix(rank)]\
                and 0 not in [found_fDn_blocks[0].determinant(), found_fDn_blocks[1].determinant(),\
                    found_fDm_blocks[0], found_fDm_blocks[1]]:
                try:
                    dlog, _ = algorithm_2(rank, found_fDn_blocks[0], found_fDm_blocks[0])
                    if found_fDm_blocks[0] != found_fDn_blocks[1]*dlog:
                        continue
                except:
                    pass

            found_fAm = P * found_fDm * P.inverse()
            found_fAn = P * found_fDn * P.inverse()

            zz = found_fAm * c1 * found_fAn
            candidate_zz.append(zz)
            if verbose:
                print("   recovered secret:", list(aer.to_integer(zz)))
                print()
            break # could try to check for more candidates
    return candidate_zz[0]


def full_attack(rank, poly_degree, exponent_range, keygen_prng_seed, encaps_prng_seed, same_m_n=False, verbose=False):
    aer = AER(rank=rank)

    if verbose:
        print(f"k: {rank}, poly_degree: {poly_degree}")
        print("finite field: GF[2,{%s}]" % aer.base_field.modulus)

    _, pk = Gen(keygen_prng_seed, rank, poly_degree, exponent_range=exponent_range, same_m_n=same_m_n, pk_product="matrix")
    c = Encaps(encaps_prng_seed, pk, same_m_n=same_m_n, pk_product="matrix")

    r = pk['r']
    A = pk['A']
    if r.determinant() != 0:
        atk_type = 1
        dt = time()
        zz = invertible_fA_attack(rank, pk, c, verbose=verbose)
        dt = time() - dt
    elif A.change_ring(A.charpoly().splitting_field('x')).is_diagonalizable():
        atk_type = 2
        dt = time()
        zz = diagonalisable_A_attack(rank, pk, c, verbose=verbose)
        dt = time() - dt
    else:
        # A not diagonalizable
        atk_type = 3
        dt = time()
        zz = non_diagonalisable_A_attack(rank, pk, c, verbose=verbose)
        dt = time() - dt

    ss = c['ss']
    return bool(ss == zz), dt, atk_type


experiments = [
    # k, d, u, trials
    (2,  7, 2**32, 200),
    (2, 15, 2**32, 200),
    (2, 23, 2**32, 200),
    (2, 31, 2**32, 200),

    (2,  7, 2**64, 200),
    (2, 15, 2**64, 200),
    (2, 23, 2**64, 200),
    (2, 31, 2**64, 200),

    (3,  7, 2**32, 200),
    (3, 15, 2**32, 200),
    (3, 23, 2**32, 200),
    (3, 31, 2**32, 200),

    (3,  7, 2**64, 200),
    (3, 15, 2**64, 200),
    (3, 23, 2**64, 200),
    (3, 31, 2**64, 200),

    (10, 40, 2**64, 20),
    (15, 40, 2**64, 20),
    (20, 40, 2**64, 20),
    (24, 40, 2**64, 20),

    (100, 40, 2**64, 2),
]


def main(warmup=False, same_m_n=False, prng_seed=0xdeadbeef, verbose=False):
    if warmup:
        with seed(prng_seed):
            keygen_prng_seed = randrange(100000000)
            encaps_prng_seed = randrange(100000000)
        if verbose:
            print("We run the warmup attack only once.")
        warmup_attack(keygen_prng_seed, encaps_prng_seed, same_m_n=same_m_n, verbose=verbose)
    else:
        print('| {:>3} | {:>3} | {:>7} | {:>6} | {:>10} | {:>15} | {:>10} | {:>10} | {:>10} |'.format(*("k", "d", "log2(u)", "tries", "succ prob", "avg runtime (s)", "atk type 1", "atk type 2", "atk type 3")))
        with seed(prng_seed):
            for k, d, u, tries in experiments:
                successes = 0
                tot_runtime = 0
                attack_types = {1: 0, 2: 0, 3: 0}
                successful_attack_types = {1: 0, 2: 0, 3: 0}
                for t in range(tries):
                    print(f"\rAttacking instance {t+1}/{tries}", end="    ")
                    keygen_prng_seed = randrange(100000000)
                    encaps_prng_seed = randrange(100000000)
                    exponent_range = (2, u)
                    success, runtime, atk_type = full_attack(k, d, exponent_range, keygen_prng_seed, encaps_prng_seed, verbose=verbose)
                    attack_types[atk_type] += 1
                    if success:
                        successes += 1
                        tot_runtime += runtime
                        successful_attack_types[atk_type] += 1

                succ_prob = successes / tries
                avg_runtime = tot_runtime / successes
                print('\r| {:>3} | {:>3} | {:>7} | {:>6} | {:>10} | {:>15} | {:>10} | {:>10} | {:>10} |'.format(*(
                    k,
                    d,
                    log(u,2),
                    tries,
                    succ_prob,
                    "%.2f" % avg_runtime,
                    "%d / %d" % (successful_attack_types[1], attack_types[1]),
                    "%d / %d" % (successful_attack_types[2], attack_types[2]),
                    "%d / %d" % (successful_attack_types[3], attack_types[3])
                )))


if __name__ == "__main__":
    import argparse
    parser = argparse.ArgumentParser()
    parser.add_argument('-w', '--warmup', action='store_true', help='run the warm-up attack against the scheme when using coefficient-wise products')
    parser.add_argument('-v', '--verbose', action='store_true', help='print element orders')
    parser.add_argument('-s', '--seed', type=int, default=0xdeadbeef, help='prng seed')
    parser.add_argument('-smn', '--same-m-n', action='store_true', help='if set, alice and bob use the same values for m and n (m_f = m_h, n_f = n_h)')
    args = parser.parse_args()
    main(warmup=args.warmup, same_m_n=args.same_m_n, prng_seed=args.seed, verbose=args.verbose)

