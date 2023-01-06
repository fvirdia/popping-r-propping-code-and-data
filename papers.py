from aer import AER


def arxiv_2022_08343():
    print("ArXiv 2022.08343")
    aer = AER(rank=2)
    aes_field = aer.base_field
    K, a = aes_field.field, aes_field.var
    print()
    print("Table 1")
    mat = aer.space(map(aes_field.from_integer, [183, 62, 77, 50]))
    print(mat)
    print()
    print("Table 2")
    mat2 = aer.space(map(aes_field.from_integer, [165, 182, 199, 138]))
    m = mat2
    print(aer.to_integer(m))
    print()
    found = False
    while not found:
        m *= mat2
        found = bool(m == mat2)
        print(aer.to_integer(m))
        print()
    print("--------------------------")
    print()


def eprint_2020_1102():
    print("IACR eprint 2020/1102")
    dim = 2
    deg = 5
    m, n = 3, 5

    aer = AER(rank=dim)
    aes_field = aer.base_field
    K, a = aes_field.field, aes_field.var

    A = aer.space(map(aes_field.from_integer, [2, 5, 7, 4]))
    B = aer.space(map(aes_field.from_integer, [1, 9, 3, 2]))
    
    print("A")
    print(aer.to_integer(A))
    
    print("B")
    print(aer.to_integer(B))

    f_coeffs = [6, 5, 4, 3, 0, 0]
    print("coefficient list of f(x):", f_coeffs)
    
    # print("tensor A power set:")
    # pset = aer.power_set(A, deg + 1)
    # for _m in pset:
    #     print(aer.to_integer(_m))
    #     print()

    f_A = aer.field_el_coeff_poly(A, f_coeffs)
    print("f(A)")
    print(aer.to_integer(f_A))
    print()

    rA = aer.M3(f_A**m, B, f_A**n)
    print("rA")
    print(aer.to_integer(rA))
    print()

    h_coeffs = [1, 5, 0, 0, 0, 1]
    print("coefficients of h(x):", h_coeffs)
    print()

    h_A = aer.field_el_coeff_poly(A, h_coeffs)
    print("h(A)")
    print(aer.to_integer(h_A))
    print()

    rB = aer.M3(h_A**m, B, h_A**n)
    print("rB")
    print(aer.to_integer(rB))
    print()

    KA = aer.M3(f_A**m, rB, f_A**n)
    print("Alice's session key, KA")
    print(aer.to_integer(KA))
    print()

    KB = aer.M3(h_A**m, rA, h_A**n)
    print("Bob's session key, KB")
    print(aer.to_integer(KB))
    print()
    print("--------------------------")
    print()


def eprint_2020_1217():
    print("IACR eprint 2020/1217")
    dim = 3
    deg = 31
    m, n = 1793503137, 2694910638

    aer = AER(rank=dim)
    aes_field = aer.base_field
    K, a = aes_field.field, aes_field.var

    A = aer.space(map(aes_field.from_integer, [60, 167, 194, 168, 131, 56, 66, 16, 91]))
    B = aer.space(map(aes_field.from_integer, [155, 112, 101, 168, 204, 104, 90, 28, 232]))
    
    print("A")
    print(aer.to_integer(A))
    print()
    
    print("B")
    print(aer.to_integer(B))
    print()

    f_coeffs = [171, 8, 136, 70, 254, 55, 170, 138, 47, 98, 87, 184, 92, 48, 143, 246, 202, 210, 44, 79, 240, 129, 240, 145, 0, 92, 197, 52, 207, 134, 60, 36]
    print("coefficient list of f(x):", f_coeffs)
    print()
    
    # print("tensor A power set:")
    # pset = aer.power_set(A, deg + 1)
    # for _m in pset:
    #     print(aer.to_integer(_m))
    #     print()

    f_A = aer.field_el_coeff_poly(A, f_coeffs)
    print("f(A)")
    print(aer.to_integer(f_A))
    print()

    rA = aer.M3(f_A**m, B, f_A**n)
    print("rA")
    print(aer.to_integer(rA))
    print()
    
    r, s = 3791045539, 4075263003

    h_coeffs = [174, 13, 217, 229, 100, 171, 120, 190, 79, 192, 190, 25, 83, 11, 173, 223, 221, 106, 216, 174, 41, 67, 176, 207, 53, 4, 139, 135, 220, 228, 136, 217]
    print("coefficients of h(x):", h_coeffs)
    print()

    h_A = aer.field_el_coeff_poly(A, h_coeffs)
    print("h(A)")
    print(aer.to_integer(h_A))
    print()

    rB = aer.M3(h_A**r, B, h_A**s)
    print("rB")
    print(aer.to_integer(rB))
    print()

    KA = aer.M3(f_A**m, rB, f_A**n)
    print("Alice's session key, KA")
    print(aer.to_integer(KA))
    print()

    KB = aer.M3(h_A**r, rA, h_A**s)
    print("Bob's session key, KB")
    print(aer.to_integer(KB))
    print()
    print("--------------------------")
    print()


def eprint_2021_270():
    print("IACR eprint 2021/270")
    dim = 3

    aer = AER(rank=dim)
    aes_field = aer.base_field

    g0 = aer.space(map(aes_field.from_integer, [158, 215, 6, 216, 221, 53, 45, 119, 206]))
    r = 15410182
    g = g0 ** r
    invg = g.inverse()
    sk = a = 13481815
    pk = s0 = g**a

    # sign
    k = 6686110
    h = 5011236 # message hash
    s1 = s0 * invg ** (k*h)
    s2 = g**k
    s3 = s2 ** h
    
    aer.print(g0, "G0")

    aer.print(g, "G")

    print("sk", sk)
    print()

    aer.print(pk, "pk")

    aer.print(s1, "sig s1")
    aer.print(s2, "sig s2")

    aer.print(s3, "s3 = s2^h")

    print("verifies:", s1 * s3 == s0)
    print("--------------------------")
    print()
    return g0, g


def eprint_2021_270_with_our_syntax():
    print("IACR eprint 2021/270, using our syntax")
    dim = 3

    aer = AER(rank=dim)
    aes_field = aer.base_field

    # Gen
    g0 = aer.space(map(aes_field.from_integer, [158, 215, 6, 216, 221, 53, 45, 119, 206]))
    ord_G = 16777215
    r = 15410182
    a = 13481815
    g = g0 ** r
    g_a = g**a

    aer.print(g0, "G0")
    aer.print(g, "G")
    aer.print(g_a, "pk")

    # Sign
    h = 5011236 # message hash
    n = 6686110
    s1 = g_a * g**(-n*h)
    s2 = g**n

    aer.print(s1, "sig s1")
    aer.print(s2, "sig s2")

    # Verify
    print("verifies:", s1 * s2**h == g_a)
    print("--------------------------")
    print()


if __name__ == "__main__":
    arxiv_2022_08343()
    eprint_2020_1102()
    eprint_2020_1217()
    eprint_2021_270()
    eprint_2021_270_with_our_syntax()
