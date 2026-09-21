# Digest — external review of the A1 skeleton, seventh iteration (snapshot `09bd2715`)

Marks: **[V]** checked by the lead; **[–]** not independently verified.
Docstring claim still wrong: "exempted frozen degeneracies are handled by equality-retention" —
**mixed germs do not satisfy whole-block fibre equality, and the present free-germ predicate
misses preimages outside `R`.**

| Leaf | Verdict | Reason |
|---|---|---|
| `exists_transitionSubdivisionOnOverlap` | **OK — freeze** | covers a whole neighbourhood now |
| `hasPLNormalDoubleCrossingAt_of_isStableCrossingBlock` | **OK — freeze** | source-neighbourhood and PL-homeomorphic projection clauses exclude the fake re-pairing |
| `exists_protectedSubdivision_in_adaptedChart` | **OK — freeze** | the strengthened block protects the current chart; `R → τ` is right |
| `exists_genericVertexMap_in_adaptedChart` | **FALSE [V]** | an unmoved sheet outside `R` is classified as a *free* germ, making `hwallfold` unsatisfiable |
| `exists_normalCrossings_of_gluedCell` | **FALSE [V for the boundary model]** | neither the free boundary layer nor the mixed layer guarantees the later-chart margin of the *new* map |

## 1. Block shape and `H₂` — the lead was right, no second block shape
At a qualified edge–triangle point (as recognised by guard, local injectivity and two-point fibres):
fold edge direction `e`, flat sheet `P`; the guard gives `e ∉ P`; projecting along `e` onto `P`, the
two transverse rays of the folded sheet cannot coincide positively (local injectivity), so choose a
linear coordinate `t` on `P` with opposite signs on them, `v|_P = 0`, `u(e) = t(e) = 0`:
`A : u = a(v,t)` = `c₊ t` for `t ≥ 0`, `c₋ t` for `t ≤ 0`; `B : v = 0`. In fact `La = Lb = 0`,
`η = 1`; after shrinking the block the genuine-sheet clauses hold. `blockHalfPlane` is correct: both
projections are `(v,t)` and `(u,t)`, so `H₂ = ℝ²` for `tlo = −r` and `ℝ × [0,∞)` for `tlo = 0` — the
half-plane restricts the common parameter `t`.

## 2. Generic leaf: an unmoved sheet counted as free [V]
`ec = ecw = id`, `ℓ = t`, `Ac = Lc = ∅`, `Rc = R` an interior source triangle with an edge whose image
runs from `(−1,0,2)` to `(1,0,2)`; outside `R` an unmoved rectangle `{x = 0, |y| ≤ 1, 1 ≤ t ≤ 3}`;
a wall triangle `F ⊆ {x = 0}` of `Qw` with `(0,0,2) ∈ relint F`. For every `τ < 1/10` the edge still
crosses the rectangle: a double point `y ∈ F`. With `Ac = ∅` the present `IsFreeDoubleGerm` holds —
the other preimage is outside `R` and the universal check over simplices containing it is empty —
and `hwallfold` demands `y ∉ |Qw^(2)|`. (Lead checked the predicate: it quantifies over `R`-simplices
containing fibre points only.) **Repair:**
`FreeSourceGerm R Ac g S y := ∀ x ∈ S ∩ g ⁻¹' {y}, R.space ∈ 𝓝[S] x ∧ ∀ σ ∈ R.faces, x ∈ |σ| → ∀ v ∈ σ, v ∉ Ac.space`,
`IsFreeDoubleGerm := y ∉ BdM ∧ FreeSourceGerm …`. "No frozen vertex" is not enough.

## 3. Crossing leaf: boundary and mixed layers
**Free boundary counterexample [V]** (lead checked the rays): later chart
`H(x,y,t) = (x,y,t)` for `y ≤ 3x`, `(y/3, −2x + 5y/3, t)` for `y ≥ 3x` (equal on the wall,
determinant `2/3`); near the origin `A : y = t`, `B : y = x + t`, `t ≥ 0`; `D' = D`,
`Z = O = Ac = ∅`, `Nw = Pw = {0}`. Old stability is vacuous, the origin is in `BdM` so no wall
condition fires; in the later chart the boundary rays are `A : e₁, e₂`, `B : e₁+e₂, e₂−e₁`; any
genuine graph coordinates force `La·Lb ≥ 1` (the third coordinate of a boundary block is `t`, no
tilting). **Mixed germs belong to the protection layer, not to equality-retention:** `hprot` gives
normality only, `hpersist` the current chart's margin only, `hlater` concerns the old map only —
none gives the later margin of the new map. **Two interfaces to add, supplied by a stratified
producer:**
* `hboundaryAffine` — near every fully free boundary double point the transition is affine on the
  physical half-neighbourhood; suppliable by avoiding the **1-skeleton of the boundary-induced
  complex** (not the physical boundary 2-faces);
* `hmixedLater` — every affected non-free double point has a genuine margin block in every
  relevant later chart; **this needs an independent relative construction proof**; equality-retention
  does not replace it.
`hwalltrans` itself is *not* too strong on the fully free triangle–triangle interior layer (the
local double set is a segment; two-sidedness should stay). The defect is the missing strata.

## 4. `HasStableCrossingBlocksIn`
Recommended for the induction, but recording one fixed open `N` is not enough. Either keep the
present invariant and add the **compact localisation lemma**
`(h : HasStableCrossingBlocks ⇑D D.domain ec ℓ BdM Q η) (hκ : 0 < κ) (hinj : UniformInjectivityScale D.domain ⇑D κ) (hQ' : IsCompact Q') (hsub : Q' ⊆ Q) (hN : IsOpen N) (hQN : Q' ⊆ N) : HasStableCrossingBlocksIn ⇑D D.domain ec ℓ BdM Q' N η`,
and use it with `K ⊆ int K⁺ ⊆ V`, `Q_out = Z ∩ P_m \ int K⁺` (compact), `N = M \ K` — never ask a
finite block cover of the possibly non-compact `Z ∩ P_m \ K`.

**Missing obligations:** the free source germ correction; the later-margin producer for the
boundary and mixed layers; the compact localisation lemma. **Fixture:** two transverse half-disks
joined by a PL band off the intersection line, frozen outer ring, a non-identity affine shear as
later chart, a non-zero interior perturbation. **Biggest surprise:** "a preimage is not in `R`" was
read by an empty universal as "free" instead of "unmoved".
