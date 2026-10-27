#!/usr/bin/env python3
"""Pratt certificate (PrattCert.Cert format: nodes (p, a, [(q, e), ...]), children before parents, factor 2
implicit) for the primes given on the command line; re-checks every node (Lucas test) before printing.
Trial-division factoring (p - 1 up to ~1e14 is fine)."""
import sys

def factor(n):
    fs, d = {}, 2
    while d * d <= n:
        while n % d == 0:
            fs[d] = fs.get(d, 0) + 1; n //= d
        d += 1 if d == 2 else 2
    if n > 1: fs[n] = fs.get(n, 0) + 1
    return sorted(fs.items())

def is_prime(n):
    return n >= 2 and all(n % d for d in range(2, int(n ** 0.5) + 1))

nodes = {}
def cert(p):
    if p == 2 or p in nodes: return
    fs = factor(p - 1)
    for q, _ in fs: cert(q)
    a = next(a for a in range(2, p) if pow(a, p - 1, p) == 1 and all(pow(a, (p - 1) // q, p) != 1 for q, _ in fs))
    prod = 1
    for q, e in fs: prod *= q ** e
    assert prod == p - 1 and pow(a, p - 1, p) == 1 and all(pow(a, (p - 1) // q, p) != 1 for q, _ in fs)
    nodes[p] = (a, fs)

order = []
def emit(p):
    if p == 2 or p in order: return
    for q, _ in nodes[p][1]: emit(q)
    order.append(p)

for s in sys.argv[1:]:
    p = int(s); cert(p); emit(p)
for p in order:
    a, fs = nodes[p]
    print(f"({p}, {a}, [{', '.join(f'({q}, {e})' for q, e in fs)}])")
