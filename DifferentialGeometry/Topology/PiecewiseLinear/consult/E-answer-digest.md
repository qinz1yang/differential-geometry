# Digest of the answer to prompt E (closed branches) — 2026-09-20

The consultant read the branch at `3d6255da71f1`. ✔ marks what the lead re-checked in the tree.

**Verdict.** Take the *orientable* restriction of the descent route; prove a direct PL sign
exclusion of Case 1; do 2a with no push-off; do 2b through an *adapted* clean-cap neighbourhood.
Two corrections to our prompt: the solid Klein bottle is a valid local tube but cannot contain a
whole Case 1 disk (a genuine example lives in `ℝP² × I`); and in 2b smallness of an arbitrary
regular neighbourhood does **not** give the three-circle trace. Boundaries of balls and disks are
intrinsic PL boundaries throughout (`∂_M N`, not an ambient frontier).

## 1. Orientability deletes Case 1

* **Proposition.** `f : P → M` locally injective PL from a PL disk, `Γ ⊂ Int M` a transverse
  double curve whose complete preimage is one PL circle `J ⊂ Int P` with `f|J` the connected
  double cover ⇒ the orientation character of `M` is nontrivial on `Γ`. The source hypothesis
  actually used: `J` is **cooriented** in the source (automatic for a polygon in a disk).
* **The sign.** Orient `Γ`. At `y ∈ Γ` with preimages `a, b` mark the four rays
  `a_in, a_out, b_in, b_out` (from the source collar). `σ(a,b) = +1` iff
  `(a_in, b_in, a_out, b_out)` is positively cyclically ordered in the transverse disk.
  `σ` is locally constant, `σ(b,a) = −σ(a,b)`, and one circuit exchanges `a, b`. An unmarked
  "axes" argument is insufficient: an orientation-preserving quarter turn exchanges the axes but
  not the in/out markings.
* Also `g² = 1` and `w_M(g) = −1` for `g = [Γ]` (since `J` bounds a disk). The solid Klein bottle
  has `π₁ = ℤ`, so no whole Case 1 disk exists in it.
* **Cheapest PL form** = marked-link sign, no tube, no homology: a continuous
  `s : J → {±1}` with `s (τ a) = −s a` (`τ` the deck involution) contradicts connectedness of `J`.
  Three compatibility statements:
  1. *Oriented transverse-link transport*: for a PL homeomorphism of crossing germs preserving
     the double-curve germ, `ε_⊥ = ε_M · ε_Γ` (prove after a common subdivision making the map
     simplicial; the link of an oriented edge is oriented by the coherent orientations of the
     incident tetrahedra).
  2. *Marked overlap invariance*: on a connected overlap the transition transports ambient
     orientation, oriented branch direction, ordered source sheets **and each sheet's in/out
     marking** (from the actual source collar — page labels, not just a sheet `Bool`).
  3. *Passage through a branch vertex*: the vertex link is a PL 2-sphere with two poles and four
     meridian arcs whose sheet assignment alternates; the sphere orientation induces opposite
     conventions at the two poles and the in/out branch direction contributes the other reversal.
  Chain: coherent tetrahedron orientations ⇒ oriented marked-link transport ⇒ continuous
  antisymmetric sign on `J` ⇒ Case 1 impossible. Finitely many crossing charts and common
  subdivisions suffice.
* **Preservation (i)–(iii) are true** and ✔ largely already in the tree: `IsOrientable.of_le`,
  `IsOrientable.of_space_subset`, `IsOrientable.derivedNeighborhood`,
  `IsOrientable.barycentricSubdivision`, `IsOrientable.double` (`Orientation.lean:5185`),
  `isOrientable_coveringComplex_orientationCocycle` (`CoveringOrientation.lean:871`). The new
  system in the tower is a regular neighbourhood **inside** `coveringComplex K p`, so the chain is
  `Or K ⇒ Or (coveringComplex) ⇒ Or (new neighbourhood)`. (iv) holds provided orientability is
  propagated **upward from the original base** — it is false read downward
  (`S² × I → ℝP² × I`).
* **Recommendation A, with new named variants.** Keep the general definitions; add orientable
  variants of the descent statement, the buffered Lemma 2, the tower induction motive and its
  cover producer, the initial normal system and the final `Moise252` assembly. The induction
  quantifies over arbitrary normal systems, so **its motive must change**; adding orientability
  only at the final call is insufficient. Only `Or S` is needed for the one-step surgery; the
  induction needs `Or T` for its recursive call. General position need not be restricted. Option B
  (keep the universal statement, leave non-orientable Case 1 open) does not close the orientable
  consumer. Nothing downstream on the named route (`Moise304`, `Moise305`, §34–35) needs the
  non-orientable loop theorem; but the unrestricted `Moise251`, `Moise264` are then **not**
  proved.

## 2. Case 2a — confirmed

No push-off; the corner violates no field of `NormalSingularCellData` and nothing later reruns
general position. `g = (f|J)⁻¹ ∘ (f|T)`, `k : E₂ → Q` any PL extension. Exact singular set
`Σ_G = ⊔ { Γ_b : b ≠ c, P ∩ f⁻¹ Γ_b ⊂ R }`, `R = P \ Int E₂`, by whole-or-nothing (each preimage
component maps **onto** the old branch, so the retained preimage count is constant along it).
Boundary branches are preserved. Consumers ✔: `injective_branchOrigin_of_subset_or_disjoint`,
`DescendingSurgery.ofBranchInjection`. Invariants inherited literally; `G(P) ⊂ f(P)`.

## 3. Case 2b — adapted clean cap

* Exact identity `P ∩ f⁻¹(f Q) = Q ∪ T`. Compactness lemma: a locally injective continuous map on
  a compact metric space that is injective on a compact `A` is injective on a neighbourhood of
  `A`. Hence disjoint embedded neighbourhoods `Q⁺ ⊃ Q`, `A_T ⊃ T`, and a target neighbourhood
  excluding every other sheet.
* **Smallness alone fails**: corrugate the boundary of a standard regular neighbourhood near the
  boundary circle (`(ε,0), (−ε,ε), (ε,2ε), (−2ε,3ε)` in normal coordinates) — still a regular
  neighbourhood ball, arbitrarily small, and `Y_out` meets its boundary in three circles. The
  producer must be **existential and pair-adapted**:
  `∂_M N ∩ f(P) = c₊ ⊔ c₀ ⊔ c₋` (`Y_out`, `X_out`, `Y_in`), complement two disks and two annuli,
  the caps adjacent to `c₊`, `c₋`; and `P ∩ f⁻¹ N = Q_N ⊔ A_N`.
* **Transversality is not a separate requirement**: once `Δ' ∩ f(P) = ∂Δ' = f(T')`, compact PL
  gluing of the retained half-collar and the new half-disk gives local injectivity at `T'`.
* Choose the collar with `A_T ∩ Σ̃_f = T`, so `(E₂' \ E₂) ∩ Σ̃_f = ∅`; whole-or-nothing with
  `R = P \ Int E₂'`. Side: ✔ `NormalSingularCellData.preimage_boundary_eq_frontier`
  (`LoopTheorem/NormalCellProperness.lean:44`) gives `f(Q) ∩ BdM = ∅`, so `f(Q) ⊂ Int_M C` and
  `N` is chosen inside.
* **Consumer contract (neighbourhood-free).** For every small open `U ⊃ f(Q)`, `U ⊂ Int_M C`:
  produce `E₂'`, `T' = ∂E₂'`, a PL disk `P' ⊂ U` with `E₂ ⊂ Int E₂'`, `E₂' ⊂ Int P`,
  `Q ∩ E₂' = ∅`, `(E₂' \ E₂) ∩ Σ̃_f = ∅`, `f|T' : T' ≅ ∂P'`, `P' ∩ f(P) = ∂P'`. The surgery,
  normality, the branch injection, the complexity drop and the three invariants are consequences.
  The producer returns the **geometric cap data**, never the normal surgery.
* **Reuse point** ✔: `IsCombinatorialManifoldWithBoundary.exists_isPLBall_derivedNeighborhood_disk`
  (`SurfaceSplitDiskNeighborhood.lean:213`) — a derived-neighbourhood 3-ball of an embedded PL
  disk, no closed surface and no `finrank = 3` needed. New work: its small, marked-pair trace
  refinement. Not usable: `BicollarEmbedding` (wrong objects), the spanning-disk theorem (needs a
  closed surface and `finrank ℝ E = 3`; `Y ∩ N₀` does not fix the mismatch),
  `LoopTheorem/DiskPushOff.lean` (same boundary: the retained `X` sheet still meets the
  replacement along `Γ` — the moved seam `T'` is the repair).
* **2b cannot be selected away**: the 2b fixture has exactly one closed branch and no boundary
  branch, and exchanging the roles still gives disjoint disks.

## 4. Fixtures (complexity exactly one each)

* **2a, folded cup.** `P₀ = [−1,1]²`, source `6P₀` in concentric polygonal rings `j = 0..6`,
  meridian `(r_j, z_j) = (0,0),(2,0),(2,2),(1,2),(1,−1),(3,−1),(3,3)`, ring `j ↦ (r_j ∂P₀) × {z_j}`.
  One double curve `∂P₀ × {0}`, `J = ½∂P₀`, `T = (11/3)∂P₀`, `Q = ½P₀ ⊂ Int E₂ = (11/3)P₀`.
  `M₀ = [−4,4]² × [−2,3]`.
* **2b, two boxes joined outside.** `A = [−2,1] × [−2,2]²`, `B = [−1,2] × [−1,1]²`,
  `∂A ∩ ∂B = {1} × ∂[−1,1]²`; puncture the faces `x = −2` of `∂A` and `x = 2` of `∂B`, join by a
  thin tube along `(−2,0,0),(−3,0,0),(−3,3,0),(3,3,0),(3,0,0),(2,0,0)`, puncture a flat tube face.
  Adapted `N = [1−ε, 1+ε] × [−1−ε, 1+ε]²`, `c₊ = {1+ε} × ∂[−1,1]²`,
  `c₀ = {1} × ∂[−1−ε,1+ε]²`, `c₋ = {1−ε} × ∂[−1,1]²`, cap `Δ' = {1+ε} × [−1,1]²`.
* **Case 1, in `ℝP² × I`.** Möbius band `𝓜_ε`, source annulus `(ℝ/2ℤ) × [−ε,ε]` capped by the
  disk `F`, `f([s],v) = ([s,v], v)`, `f|F = (·, ε)`; `Γ = L × {0}`, `J = (ℝ/2ℤ) × {0}`; in
  `x = (z+u)/2`, `y = (z−u)/2` the Möbius identification is exactly `(x,y) ↦ (y,x)`.
* Full tuple for each: triangulate, take a small relative derived neighbourhood `K` of the image,
  `B` a small annular neighbourhood of `f(∂P)` in `∂K`, `H = {1} ≤ π₁(B)`, constant connector —
  the normal-system group is `π₁` of the boundary **neighbourhood**. These are fixtures for the
  descent interfaces, not for the stronger `Moise252` input.

## 5. Implementation cut

Three producers: (1) orientable marked-link sign exclusion for connected preimage circles;
(2) nested PL disk replacement with whole-or-nothing branch preservation; (3) disjoint clean-cap
producer with moved boundary and protected collar. 2a is ready for direct assembly; 2b cannot be
selected away; the Case 1 mapping-torus construction is unnecessary on the orientable route.
