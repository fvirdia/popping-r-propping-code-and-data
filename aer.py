from sage.all import ZZ, GF, PolynomialRing, MatrixSpace, matrix, vector, Infinity

def extend_list(l, entries):
    l = l + [0] * (entries - len(l))
    return l

AES_MODULUS = [1, 1, 0, 1, 1, 0, 0, 0, 1]

class AESField:
    """
    EXAMPLE:
        >>> aes_field = AESField()
        >>> K, a = aes_field.field, aes_field.var
        >>> print(a)
            a
        >>> print(K(aes_field.modulus))
            0
    """

    def __init__(self, modulus=AES_MODULUS):
        self.GF2PolyRing, self.GF2PolyVar = PolynomialRing(GF(2), "x").objgen()
        x = self.GF2PolyVar
        self.modulus = modulus
        self.field, self.var = GF(2**8, name="a", modulus=self.modulus).objgen()

    def from_integer(self, val):
        return self.from_binary(ZZ(val).bits())

    def from_binary(self, bits):
        bits = extend_list(bits, 8)[:8]
        field_element = 0
        for bit in range(8):
            field_element += int(bits[bit]) * self.var ** bit
        return field_element

    def to_integer(self, val):
        return self.field(val).integer_representation()

    def to_binary(self, val):
        bits = list(map(int, ZZ(self.to_integer(val)).bits()))
        bits = (bits + [0] * (8-len(bits)))[:8]
        return bits

    def poly_to_mat(self, poly):
        """
        TESTS:
            >>> aes = AESField()
            >>> from itertools import product
            >>> for x, y in product(range(256), range(256)):
            >>>     print(x, y, "    ", end="\r")
            >>>     px = aes.from_integer(x)
            >>>     py = aes.from_integer(y)
            >>>     mx = aes.poly_to_mat(px)
            >>>     my = aes.poly_to_mat(py)
            >>>     pz = px * py
            >>>     mz = aes.poly_to_mat(pz)
            >>>     assert (mz - mx * my).is_zero()
            >>> print()
            >>> print("All products check")
        """
        coeffs = []
        for power in range(8):
            coeffs.append(extend_list(list((poly * self.var ** power).polynomial()), 8))
        mat = matrix(GF(2), coeffs).transpose()
        return mat

    def mat_to_poly(self, mat, proof=False):
        """
        TEST:
            >>> from sage.all import randrange
            >>> trials = 50
            >>> for __ in range(trials):
            >>>     x1 = randrange(256)
            >>>     x2 = randrange(256)
            >>>     p1 = aes_field.from_integer(x1)
            >>>     p2 = aes_field.from_integer(x2)
            >>>     m1 = aes_field.poly_to_mat(p1)
            >>>     m2 = aes_field.poly_to_mat(p2)
            >>>     res = p1 * p2
            >>>     mres = m1 * m2
            >>>     resp = aes_field.mat_to_poly(mres)
            >>>     assert res == resp
        """
        coeffs = list(mat.transpose()[0])
        poly = self.from_binary(coeffs)
        if proof:
            assert self.poly_to_mat(poly) == mat
        return poly


class AER:

    def __init__(self, rank, modulus=AES_MODULUS):
        self.base_field = AESField(modulus)
        self.rank = rank
        self.space = MatrixSpace(self.base_field.field, self.rank)

    def power_set(self, mat, count=Infinity):
        pset = [self.one(), mat]
        found = 2
        while found < count:
            m = pset[-1] * mat
            if m == mat:
                break
            pset.append(m)
            found += 1
        return pset

    def to_integer(self, mat):
        return matrix(ZZ, self.rank, list(map(self.base_field.to_integer, mat.list())))

    def zero(self):
        return self.space()

    def one(self):
        return self.space.identity_matrix()

    def field_el_coeff_poly(self, tensor, coeffs):
        fecp = self.zero()
        for power in range(len(coeffs)):
            fecp += self.base_field.from_integer(coeffs[power]) * tensor ** power
        return fecp

    def M3(self, m1, m2, m3):
        # NOTE: the HK17+ paper suggests in Equation 5 that this should be matrix multiplication rather than coefficient-wise multiplication
        #       however all the examples use coefficient-wise multiplication
        return self.space(vector(m1).pairwise_product(vector(m2).pairwise_product(vector(m3))))

    def print(self, mat, mat_name=None):
        if mat_name:
            print(mat_name)
        print(self.to_integer(mat))
        print()