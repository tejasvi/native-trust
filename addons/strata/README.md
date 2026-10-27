# Strata add-on (`Lambda.Factory` lookups)

Proved replacements that let NativeTrust convert the 34 facts of `StrataTest.DL.Lambda.Denote.Tautologies`.
They ask about the `IntBoolFactory`: membership, `concreteEval`, names, input and output types of the
`Bool` operators. A `Factory` keeps its functions in an array (`toArray`) plus a private
`Std.HashMap String Nat` from names to indices (`nameMap`). Membership and `Factory.get` read the hash map,
and `String.hash` has no kernel definition, so on v13 these facts are blocked
on `String.hash` and `System.Platform.getNumBits`. The add-on uses toolchain `v4.31.0`, the version the package
pins; the module imports `NativeTrust` and `Strata.DL.Lambda.Factory`.

| file | contents |
|---|---|
| `NTStrataFactory.lean` | everything below; both theorems depend only on `propext`, `Classical.choice` and `Quot.sound` |

- `instMemDecidable_eq` (`@[kernel_replace_retry]`): membership is decided by `toArray.any (·.name.name == name)`.
  `Decidable` is a subsingleton, so the equation is `Subsingleton.elim`. That the array test is a decision
  procedure follows from the factory's invariants (every element's name maps to its index; every key maps
  to an element with that name).
- `get_eq` (`@[kernel_replace_retry]`): `Factory.get f name p` is `(f.toArray.find? (·.name.name == name)).get _`.
  The invariants make names unique, so the first element with that name is the one the hash map points to.
- `Factory.push` (hence `ofArray`) still builds the hash map, but in a field that evaluation never projects,
  so the kernel never computes a hash.
- Under the `module` system, `nameMap` and the invariant fields are private to Strata's module. They are
  aliased here with `run_meta` and `addDecl`, so the aliases are the same kernel constants.

To use the add-on, compile `NTStrataFactory.lean` to an olean in Strata's environment,
then run the driver with `--extra-path <this directory> --extra-import NTStrataFactory`.

On library v13 with the iterator-strings patch of v14, in the driver run `v8s-r4-strata-taut-a1`, all 34 facts
are PROVED, each in 1-15 s and 1.7 GB, with 0 accessibility-generator fallbacks. On the build with the word-size
case split, all 34 are PROVED again in the driver run `v8s-r4b3-strata-taut-p13c`.
