# Infinite Dyck Paths Algebra for Unbounded Interval Temporal Logic

Ferrari's Dyck lattices D_n read a finite Dyck path in three ways: as a path,
as a down-set of intervals of the chain [n−1], and as the antichain of its
maximal intervals. In this reading D_n is the algebra of the logic of
subintervals ITL_n on the bounded time line T_n = {t_1, …, t_n}, through its
persistent fragment [Θ_n]. Following a suggestion of Ferrari, we let the time
line run off to the right, to T_ω = {t_1, t_2, …}. An infinite Dyck path is then
a down-set of the finite intervals of T_ω, that is, a hereditary proposition
about an unbounded future, and we ask which connectives such paths still
support. The infinite paths form a frame 𝒟_ω, whose logic is
ℒ_ω = {⊥, ⊤, ∧, ∨, ⇝, ∼, ⋁, ⋀}. 𝒟_ω splits into two models. Model 1, 𝒟_fs, is
the paths of finite support, the limit of the D_n: a distributive lattice with
⊥ but no ⊤, with logic ℒ_1 = {⊥, ∧, ∨}. Model 2, 𝒟_∞, is the paths of infinite
support: a join-semilattice with ⊤ but no ⊥ and no meet, with logic
ℒ_2 = {⊤, ∨, ⇝}. The paper is [main.typ](main.typ) ([main.pdf](main.pdf)), and
the Rocq development in [theories/](theories/) checks it.

Legend for the tables below:

- ✓ : in Rocq (an instance, a constructor or a notation)
- ✗ : proved absent or not closed in Rocq
- ✗ (paper) : absent according to the paper, with no Rocq proof yet
- todo : holds in the paper, not yet in Rocq
- – : not part of that carrier's signature, nothing to prove

# Dyck Lattices

| Carrier | Bundle                                    | Where                                           | What it is                                                                                                          |
| ------- | ----------------------------------------- | ----------------------------------------------- | ------------------------------------------------------------------------------------------------------------------- |
| D_n     | `Dyck_Lattice n`, `Dyck_HeytingAlgebra n` | [HeytingDyck.v](theories/Algebra/HeytingDyck.v) | Dyck paths with n up-steps, ordered by height at every time; ⊥ = (ud)ⁿ, ⊤ = uⁿdⁿ                                    |
| [Θ_n]   | `Θcls_Lattice n`, `Θcls_HeytingAlgebra n` | [ITLn.v](theories/Logic/ITLn.v)                 | Classes [φ] (type `Θcls n`) of the persistent ITL_n formulas (φ → □φ valid on T_n) under ≊_n, ordered by entailment |
| 𝒟_ω     | `Dyckω_Lattice`                           | [DyckOmega.v](theories/Algebra/DyckOmega.v)     | Infinite paths whose every prefix is a Dyck prefix, ordered by height at every time; ⊥ = (ud)^ω, ⊤ = u^ω            |
| 𝒟_fs    | `Dyck_fs_Lattice`                         | [DyckFs.v](theories/Algebra/DyckFs.v)           | Paths of 𝒟_ω that differ from (ud)^ω at finitely many times (finite support); ≅ colim D_n                           |
| 𝒟_∞     | `Dyck_inf_JoinSemilattice`                | [DyckInf.v](theories/Algebra/DyckInf.v)         | Paths of 𝒟_ω that differ from (ud)^ω at infinitely many times (infinite support)                                    |

| Carrier        | ≤   | ⊓   | ⊔   | ⊥   | ⊤   | Distrib. | ⟿      | ¬         | ⋁, ⋀ | Class                             |
| -------------- | --- | --- | --- | --- | --- | -------- | ------ | --------- | ---- | --------------------------------- |
| D_n            | ✓   | ✓   | ✓   | ✓   | ✓   | ✓        | ✓      | ✓         | –    | Heyting algebra                   |
| [Θ_n]          | ✓   | ✓   | ✓   | ✓   | ✓   | ✓        | ✓ (⇝)  | ✓ (∼)     | –    | Heyting algebra                   |
| 𝒟_ω            | ✓   | ✓   | ✓   | ✓   | ✓   | ✓        | todo   | todo      | todo | bounded distributive lattice      |
| 𝒟_fs (Model 1) | ✓   | ✓   | ✓   | ✓   | ✗   | ✓        | ✗      | ✗ (paper) | –    | distributive lattice with ⊥, no ⊤ |
| 𝒟_∞ (Model 2)  | ✓   | ✗   | ✓   | ✗   | ✓   | –        | todo ¹ | ✗ (paper) | –    | join-semilattice with ⊤           |

# Logics

| Logic | Formulas | Semantics | Where                               |
| ----- | -------- | --------- | ----------------------------------- |
| ITL_n | `form`   | `val`     | [ITLn.v](theories/Logic/ITLn.v)     |
| ℒ_ω   | `formω`  | `valω`    | [ITLω.v](theories/Logic/ITLω.v)     |
| ℒ_1   | `form1`  | `val1`    | [ITLfs.v](theories/Logic/ITLfs.v)   |
| ℒ_2   | `form2`  | `val2`    | [ITLinf.v](theories/Logic/ITLinf.v) |


| Logic         | ⊥   | ⊤   | ε_i | ∧   | ∨   | →   | ¬   | ⇝   | ∼   | □    | ◇   | ⋁   | ⋀   |
| ------------- | --- | --- | --- | --- | --- | --- | --- | --- | --- | ---- | --- | --- | --- |
| ITL_n         | ✓   | ✓   | ✓   | ✓   | ✓   | ✓ † | ✓ † | ✓   | ✓   | ✓    | ✓ † | –   | –   |
| ℒ_ω           | ✓   | ✓   | ✓   | ✓   | ✓   | –   | –   | ✓   | ✓   | = id | ✗   | ✓   | ✓   |
| ℒ_1 (Model 1) | ✓   | ✗   | ✓   | ✓   | ✓   | –   | –   | ✗   | ✗   | = id | ✗   | –   | –   |
| ℒ_2 (Model 2) | ✗   | ✓   | ✓ ‡ | ✗   | ✓   | –   | –   | ✓   | ✗   | = id | ✗   | ✓   | –   |

- ITL_n: † means in `form`, but Θ_n is not closed under it.
- ‡ ε_i is a constructor of `form2`, but its truth set is bounded, so it is not
  a formula of Model 2 (`Theta2`) on its own.

# Layout

The Rocq development uses only Rocq and its standard library. It is built with
`make` inside `nix-shell`.

| File                                                    | Contents                                                                                                                                                                                                                                                                                          |
| ------------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| [Lattice.v](theories/Lattice.v)                         | Order-theoretic interface: `Poset`, `Meet`, `Join`, `Bot`, `Top`, `Distributive`, `RelPseudoComplement` (⟿), `PseudoComplement` (¬); the bundles `JoinSemilattice`, `MeetSemilattice`, `Lattice` (both semilattices over one order) and `HeytingAlgebra`; joins of sets (`is_sup`) and basic laws |
| [Interval.v](theories/Interval.v)                       | Intervals [t_i, t_j] of the time line, the subinterval order ⊆, intervals of T_n and T_ω, bounded and unbounded truth sets, down-sets (↓), interior and closure (□, ◇)                                                                                                                            |
| [Algebra/Dyck.v](theories/Algebra/Dyck.v)               | Finite Dyck paths D_n from the grammar P ::= ε \| u P d P, with heights, (ud)ⁿ and uⁿdⁿ; infinite paths 𝒟_ω as coherent towers of finite stages, (ud)^ω and u^ω, the support, and the set 𝒟_∞                                                                                                     |
| [Algebra/Words.v](theories/Algebra/Words.v)             | Dyck paths as words over {u, d}, height profiles, meet and join of D_n as pointwise min and max of heights (`meetD`, `joinD`), the enumeration `enumD` of D_n                                                                                                                                     |
| [Algebra/HeytingDyck.v](theories/Algebra/HeytingDyck.v) | D_n as a Heyting algebra, with ⟿ a finite join over `enumD`; the example D₄                                                                                                                                                                                                                       |
| [Algebra/DyckOmega.v](theories/Algebra/DyckOmega.v)     | 𝒟_ω as a bounded distributive lattice; the support of a meet and of a join; prepending ud or uudd to a path, to build the witnesses of the two models                                                                                                                                             |
| [Algebra/DyckFs.v](theories/Algebra/DyckFs.v)           | Model 1, 𝒟_fs: a distributive lattice with ⊥; no ⊤ and no Heyting implication                                                                                                                                                                                                                     |
| [Algebra/DyckInf.v](theories/Algebra/DyckInf.v)         | Model 2, 𝒟_∞: a join-semilattice with ⊤; the paths O = (uudd)^ω and E = ud·O show that ∧ is not closed; no ⊥                                                                                                                                                                                      |
| [Logic/ITLn.v](theories/Logic/ITLn.v)                   | The logic of subintervals ITL_n on T_n, its persistent fragment Θ_n, Propositions 3.1–3.6, the equivalence ≊_n and the Heyting algebra [Θ_n] of its classes                                                                                                                                       |
| [Logic/ITLω.v](theories/Logic/ITLω.v)                   | ℒ_ω on T_ω: ⊥, ⊤, ε_i, ∧, ∨, ⇝ and countable ⋁, ⋀; every formula is persistent; ⇝ is adjoint to ∧                                                                                                                                                                                                 |
| [Logic/ITLfs.v](theories/Logic/ITLfs.v)                 | ℒ_1 of Model 1: ⊥, ∧, ∨; every formula has a bounded truth set, hence no ⊤, ⇝ or ∼                                                                                                                                                                                                                |
| [Logic/ITLinf.v](theories/Logic/ITLinf.v)               | ℒ_2 of Model 2: ⊤, ∨, ⋁, ⇝; no ⊥, ∧ or ∼                                                                                                                                                                                                                                                          |
