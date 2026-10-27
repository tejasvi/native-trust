import PrattCert
open PrattCert

-- P0 (positive control): the BabyBear certificate.
example : checkTop 2013265921
    [(3, 2, [(2, 1)]), (5, 2, [(2, 2)]), (2013265921, 31, [(2, 27), (3, 1), (5, 1)])] = true := by
  decide +kernel
-- C1: wrong witness (2 is a square mod BabyBear).
example : checkTop 2013265921
    [(3, 2, [(2, 1)]), (5, 2, [(2, 2)]), (2013265921, 2, [(2, 27), (3, 1), (5, 1)])] = true := by
  decide +kernel
-- C2: wrong exponent (product mismatch).
example : checkTop 2013265921
    [(3, 2, [(2, 1)]), (5, 2, [(2, 2)]), (2013265921, 31, [(2, 26), (3, 1), (5, 1)])] = true := by
  decide +kernel
-- C3: no node for the factor 3.
example : checkTop 2013265921
    [(5, 2, [(2, 2)]), (2013265921, 31, [(2, 27), (3, 1), (5, 1)])] = true := by
  decide +kernel
-- C4: target not a node.
example : checkTop 2013265923
    [(3, 2, [(2, 1)]), (5, 2, [(2, 2)]), (2013265921, 31, [(2, 27), (3, 1), (5, 1)])] = true := by
  decide +kernel
-- C5: composite 2047 = 23 * 89 (base-2 Fermat pseudoprime), full factorization of 2046.
example : checkTop 2047
    [(3, 2, [(2, 1)]), (5, 2, [(2, 2)]), (11, 2, [(2, 1), (5, 1)]), (31, 3, [(2, 1), (3, 1), (5, 1)]),
     (2047, 2, [(2, 1), (3, 1), (11, 1), (31, 1)])] = true := by
  decide +kernel
-- C6: node used before it is established (order matters).
example : checkTop 2013265921
    [(2013265921, 31, [(2, 27), (3, 1), (5, 1)]), (3, 2, [(2, 1)]), (5, 2, [(2, 2)])] = true := by
  decide +kernel
-- C7: composite factor 15 listed as a "prime" with exponent 1 (15 has no node).
example : checkTop 2013265921
    [(2013265921, 31, [(2, 27), (15, 1)])] = true := by
  decide +kernel
-- C8: 1 is not prime (2 ≤ p check), empty factor list.
example : checkTop 1 [(1, 1, [])] = true := by
  decide +kernel
