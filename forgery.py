from aer import AER
from dlp import gens
from sage.all import randint, seed


def Gen(pp):
    g0, ord_G = pp
    r = randint(2, ord_G-2)
    a = randint(2, ord_G-2)
    g = g0**r
    pk = g**a
    sk = (r, g**a)
    return pk, sk


def Sign(pp, sk, h):
    """ Sign function. For simplicity, we take as input the hash of the message directly.
    """
    g0, ord_G = pp
    r, g_a = sk
    g = g0**r
    assert(2 <= h)
    assert(h <= ord_G - 2)
    n = randint(2, ord_G-2)
    s1 = g_a * g **(-n*h)
    s2 = g**n
    sigma = (s1, s2)
    return sigma


def Verify(pp, pk, sigma, hp):
    """ Verify function. For simplicity, we take as input the hash of the message directly.
    In order to check the range of the hash, we add the public parameters as an input.
    """
    _, ord_G = pp
    s1, s2 = sigma
    assert(2 <= hp)
    assert(hp <= ord_G - 2)
    return bool(s1 * s2**hp == pk)


def Forge(pp, pk, h):
    """ Verify function. For simplicity, we take as input the hash of the message directly.
    In order to check the range of the hash, we add the public parameters as an input.
    """
    _, ord_G = pp
    assert(2 <= h)
    assert(h <= ord_G - 2)
    t = randint(1, ord_G)
    s2 = pk**t
    s1 = pk*s2**(-h)
    sigma = (s1, s2)
    return sigma


def main(tries=128, prng_seed=0xdeadbeef):
    with seed(prng_seed):
        for rank, _, ord_G, g0_int_repr in gens:
            aer = AER(rank)
            g0 = aer.space(map(aer.base_field.from_integer, g0_int_repr))
            for t in range(tries):
                print(f"\rTesting k = {rank}... {t+1}/{tries}", end=" ")
                pp = (g0, ord_G)
                pk, sk = Gen(pp)
                h = randint(1, ord_G)
                sigma = Sign(pp, sk, h)
                assert(Verify(pp, pk, sigma, h) == True)
                assert(Verify(pp, pk, sigma, h+1) == False)
                hp = randint(1, ord_G)
                forged_sigma = Forge(pp, pk, hp)
                assert(Verify(pp, pk, forged_sigma, hp) == True)
                assert(Verify(pp, pk, forged_sigma, hp+1) == False)
            print("done.")
    print("All attempted forgeries were successful.")

if __name__ == "__main__":
    import argparse
    parser = argparse.ArgumentParser()
    parser.add_argument('-t', '--tries', type=int, default=128, help='number of tries')
    parser.add_argument('-s', '--seed', type=int, default=0xdeadbeef, help='prng seed')
    args = parser.parse_args()
    main(tries=args.tries)