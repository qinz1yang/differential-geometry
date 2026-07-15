# Lemma45Intrinsic.lean — the F4 intrinsic-lift kernel (green 2026-06-11)

The two lemmas that close F4's remaining frontier (lifting the component
`lemma45_F3` to the intrinsic `hF3` that `lemma45_cor_II_of_intrinsic` consumes).
Focus-checked green; imports only `Lemma45Engine` + `Comparison` (committed).

## `compL2_tower_eq_gen` — the decoupled tower-norm identity (generalized B5)

At a point where the frame is **g**-orthonormal (`hinv`), the frame-component
`compL2` of the order-`j` **gC**-Levi-Civita tower of a `(0,r)` field `T` equals
the intrinsic **g**-norm of the `iterCov gC` tower:
`compL2 (∇_{gC}^j T)_frame = √normSq0S g (iterCov gC r T j)`.

KEY: the norm/ON metric `g` is **decoupled** from the connection metric `gC`.
The parallel session's `B5` (`compL2_tower_eq`, Claim1Wiring) is the matched case
`gC = g`; F4's `hF3` needs the g-norm of the *gRef*-tower (`gC = gRef`), which
only the decoupled form expresses. Proof = `compL2_tower_eq`'s verbatim
(`normSq0S_identity_eq_sum_sq` Parseval at the g-ON basis + `iterCovComp_eq_iterCov`
for the gC tower), with the two metrics separated.

## `hF3_term` — the lift atom (component Lemma I → intrinsic Lemma I)

At a g-ON frame point `x`, a single-order `compL2` Lemma-I inequality (the per-`r`
content of `lemma45_F3`'s output for the bundled field `T`) lifts to the intrinsic
`normSq0S g` form `hF3`:
`|∇_g^r T|_g ≤ |∇_gRef^r T|_g + ε·Cc·Σ_{k<r}|∇_gRef^k T|_g`.
Proof: `rw [← compL2_tower_eq_gen g g …, ← compL2_tower_eq_gen g gRef …]` for the
LHS / leading RHS, a `Finset.sum_congr` of `compL2_tower_eq_gen g gRef … k` under
the Σ, then `exact hineq`. The decoupled norm metric stays `g` throughout.

## F4 status & what remains (assembly, gated on the lake lock + parallel session)

F4 = MSM135 Cor II (`lbl370`). Chain, all at the lemma level now:
`lemma45_F3` (compL2, Lemma45Engine) → per-`r` `hF3_term` (this file) → `hF3`
(∀ r) → `lemma45_cor_II_of_intrinsic` (Lemma45Covariant) → **Cor II**.

REMAINING (mechanical, not a frontier):
1. a **g-ON frame** at `x` — apply the parallel session's `exists_goodFrame_compBound`
   (RicBoundGoodFrame.lean, committed) with `gRef := g` (it is metric-generic;
   gives the gram-`1` field at the centre `x` = the `MetricInverseInBasis g x`
   that `hF3_term`/`compL2_tower_eq_gen` need). NOTE the good-frame bound holds on
   a nbhd with a `2^s` factor, but AT the centre `x` the frame is *exactly* g-ON,
   so the equality form (`compL2_tower_eq_gen`) applies pointwise.
2. the ∃-collection: `lemma45_F3` gives one `C`; build `hF3` as `∀ r` from
   `hF3_term` at that `C`; feed `lemma45_cor_II_of_intrinsic` (needs
   `Lemma45Covariant.olean`, a quick targeted build once the lake lock frees).

Both are gated on the lake lock / the live parallel session (token `d7e36cce`,
working `RicBoundGoodFrame`/`Comparison`/`KroneckerQuadForm`). Do the assembly
when that settles — it imports `RicBoundGoodFrame` (then-stable) + this file +
`Lemma45Covariant`.

**Honest %:** F4 (Cor II) theorem stated-with-`hF3`-hyp; the lift frontier (the
genuine remaining math) is now SOLVED at the lemma level (`compL2_tower_eq_gen` +
`hF3_term`). F4 ~80-85% (was ~60-70%); remaining = mechanical frame-producer
application + ∃-assembly. Thm 3.9 endpoint still ~0-5%.
