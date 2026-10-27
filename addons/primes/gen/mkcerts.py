#!/usr/bin/env python3
"""Build self-contained Pratt certificates from PARI output (NODE p a q1 e1 ...) and emit PrimeCerts.lean.
Every node is re-verified here with Python integers; Lean re-verifies everything in the kernel."""
import sys, os, glob

HERE = os.path.dirname(os.path.abspath(__file__))
nodes = {}
for fn in sorted(glob.glob(os.path.join(HERE, "*.out"))):  # PARI outputs of pratt.gp
    for line in open(fn):
        t = line.split()
        if not t or t[0] != "NODE":
            continue
        p, a = int(t[1]), int(t[2])
        fs = [(int(t[i]), int(t[i + 1])) for i in range(3, len(t), 2)]
        if p in nodes and nodes[p] != (a, fs):
            sys.exit(f"conflicting nodes for {p}")
        nodes[p] = (a, fs)

def check_node(p, a, fs, known):
    prod = 1
    for q, e in fs:
        prod *= q ** e
        assert q == 2 or q in known, (p, q)
    assert prod == p - 1, p
    assert p >= 2 and pow(a, p - 1, p) == 1, p
    for q, _ in fs:
        assert pow(a, (p - 1) // q, p) != 1, (p, q)

def cert_for(target):
    order, done = [], set()
    def visit(p):
        if p == 2 or p in done:
            return
        a, fs = nodes[p]
        for q, _ in fs:
            visit(q)
        done.add(p)
        order.append(p)
    visit(target)
    known = set()
    for p in order:
        a, fs = nodes[p]
        check_node(p, a, fs, known)
        known.add(p)
    assert order[-1] == target
    return order

# (lean suffix, cert def name, description, value, power form or None)
TARGETS = [
    ("babybear", "certBabyBear", "BabyBear prime `15 * 2 ^ 27 + 1`", 15 * 2**27 + 1, "15 * 2 ^ 27 + 1"),
    ("koalabear", "certKoalaBear", "KoalaBear prime `2 ^ 31 - 2 ^ 24 + 1`", 2**31 - 2**24 + 1, "2 ^ 31 - 2 ^ 24 + 1"),
    ("mersenne31", "certMersenne31", "Mersenne31 prime `2 ^ 31 - 1`", 2**31 - 1, "2 ^ 31 - 1"),
    ("goldilocks", "certGoldilocks", "Goldilocks prime `2 ^ 64 - 2 ^ 32 + 1`", 2**64 - 2**32 + 1, "2 ^ 64 - 2 ^ 32 + 1"),
    ("bn254_r", "certBn254R", "BN254 scalar field prime `r`",
     21888242871839275222246405745257275088548364400416034343698204186575808495617, None),
    ("bn254_q", "certBn254Q", "BN254 base field prime `q`",
     21888242871839275222246405745257275088696311157297823662689037894645226208583, None),
    ("secp256k1_p", "certSecp256k1P", "secp256k1 base field prime `2 ^ 256 - 2 ^ 32 - 977`",
     2**256 - 2**32 - 977, "2 ^ 256 - 2 ^ 32 - 977"),
    ("secp256k1_n", "certSecp256k1N", "secp256k1 group order `n`",
     115792089237316195423570985008687907852837564279074904382605163141518161494337, None),
    ("bls12_381_r", "certBls12381R", "BLS12-381 scalar field prime `r`",
     52435875175126190479447740508185965837690552500527637822603658699938581184513, None),
    ("curve25519_p", "certCurve25519P", "Curve25519 base field prime `2 ^ 255 - 19`",
     2**255 - 19, "2 ^ 255 - 19"),
]

def lean_cert(name, desc, order):
    lines = [f"/-- Pratt certificate for the {desc} ({len(order)} nodes). -/", f"def {name} : Cert := ["]
    for i, p in enumerate(order):
        a, fs = nodes[p]
        end = "," if i + 1 < len(order) else "]"
        items = [f"({q}, {e})" for q, e in fs]
        one = f"  ({p}, {a}, [{', '.join(items)}])" + end
        if len(one) <= 100:
            lines.append(one)
            continue
        # wrap: node head on its own line, factor list wrapped at 100 columns
        lines.append(f"  ({p}, {a},")
        cur = "    ["
        for j, it in enumerate(items):
            piece = it + (", " if j + 1 < len(items) else "])" + end)
            if len(cur) + len(piece.rstrip()) > 100 and cur.strip() not in ("[", ""):
                lines.append(cur.rstrip())
                cur = "     "
            cur += piece
        lines.append(cur.rstrip())
    return "\n".join(lines)

def main():
    which = sys.argv[1:]  # optional subset of suffixes
    out = []
    summary = []
    for suf, cname, desc, val, form in TARGETS:
        if which and suf not in which:
            continue
        order = cert_for(val)
        summary.append((suf, len(order), val.bit_length()))
        out.append(lean_cert(cname, desc, order))
        out.append("")
        out.append(f"/-- Primality of the {desc}. -/")
        out.append(f"theorem prime_{suf} :\n    Nat.Prime {val} :=\n  prime_of_checkTop (c := {cname}) (by decide +kernel)")
        out.append("")
        out.append(f"theorem fact_prime_{suf} : Fact (Nat.Prime\n    {val}) :=\n  ⟨prime_{suf}⟩")
        out.append("")
        if form:
            out.append(f"theorem prime_{suf}_pow : Nat.Prime ({form}) :=\n  prime_of_checkTop (c := {cname}) (by decide +kernel)")
            out.append("")
            out.append(f"theorem fact_prime_{suf}_pow : Fact (Nat.Prime ({form})) :=\n  ⟨prime_{suf}_pow⟩")
            out.append("")
    header = open(os.path.join(HERE, "header.lean")).read()
    sys.stdout.write(header + "\n".join(out) + "\nend PrimeCerts\n")
    for s in summary:
        sys.stderr.write("%s nodes=%d bits=%d\n" % s)

main()
