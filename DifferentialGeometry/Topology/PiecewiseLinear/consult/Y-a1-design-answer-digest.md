# Digest — answer to design consult X (the multi-chart core of A1), 2026-09-21

Marks: **[V]** checked by the lead; **[–]** not independently verified. The consultant stresses
that this is a proposed mathematical package, not a verified Lean proof.

**Verdict.** Keep the chart-by-chart perturbation and all eight frozen leaves; change the invariant
to **wall-adapted stable blocks on one fixed common wall complex**. Do not keep a separate margin
for every later chart, and do not make general-position conditions ("fold lines miss walls", …)
part of the induction invariant. The lead's doubt about the "common protection layer" of W is
confirmed (fibre retention cannot protect mixed double points with a moved fibre point); W's
counterexample does refute "old later margin + current margin + one sheet frozen".

**The key idea [V].** In a block that crosses a wall, take the wall's normal coordinate as the
*common parameter `t`* of both graphs. A transition that is affine on both sides of the wall and
agrees on it becomes, in affine coordinates matching on the wall,
`H(u,v,t) = (u + α₋t, v + β₋t, c₋t)` for `t ≤ 0`, `(u + α₊t, v + β₊t, c₊t)` for `t ≥ 0`, `c± > 0` (*)
— an affine map fixing the plane `t = 0` pointwise has exactly this form (lead checked). With
`s = t'/c±` the transported graph is `a'(v',t') = a(v' − β± s, s) + α± s`: **for fixed `t'` a
translation, so `La`, `Lb` are unchanged**; the graph projections correspond by PL homeomorphisms;
shrinking the outer block restores the box shape and the full-preimage clause. Inside an open
3-cell there is one affine transition; at the physical boundary one affine branch on the physical
side. W's counterexample has its old double line *inside* the wall, so the wall normal cannot be
the common parameter there: it is not such a block.

## 1. Fixed wall system and the invariant
After the finite cover, before the induction: compact polyhedra
`closure V_j ⊆ int E_j ⊆ E_j ⊆ (ec_j).source` and **one finite common subdivision `𝒬` of `M`** with `C`,
`BdM`, `E_j` subpolyhedra and every `ec_j|E_j` affine on the simplices of `𝒬` (common subdivision of
finite PL data; no affine neighbourhoods of wall points are claimed;
`exists_transitionSubdivisionOnOverlap` is a local input, the pieces must be unified).
`WallProductBlock` := `IsStableCrossingBlock` with all its clauses (genuine source sheets, PL
homeomorphic projections, full preimage, inner/outer buffers) **plus a support type**:
* *3-cell interior*: outer block inside one open 3-simplex of `𝒬`;
* *interior wall*: outer block meets only one open 2-face `F` and its two adjacent 3-simplices, and
  the common parameter `t` is the affine defining function of `F`;
* *physical boundary*: on the physical side only one open boundary 2-face and its 3-simplex;
  `t = ℓ_j ∘ ec_j`, half block.
So outer blocks avoid `|𝒬^(1)|`. `A : u = a(v,t)`, `B : v = b(u,t)`, `La·Lb ≤ 1 − η`, genuine sheets.
`WP(D, Z)` := finitely many such blocks whose inner blocks cover `Σ(D) ∩ Z`.
**`Inv_k(D) := Global(D) ∧ WP(D, ⋃_{j<k} closure W_j)`** — one certificate over all of `Z_k`; the
per-chart `HasStableCrossingBlocks` over `Z_k ∩ P_m` become corollaries. No transversality of all
sheets to all strata is required; fold lines at double points on walls are allowed. Constants
belong to the current `D`; e.g. with `t`-slopes `A_t, B_t` the double curve has
`Lip_t u ≤ (A_t + La·B_t)/η`, `Lip_t v ≤ (B_t + Lb·A_t)/η` — a positive angle with the wall for free.

## 2. The step theorem and the order of choices
`Inv_k(D) ⟹ ∃ R τ K_t K_p, (∀ φ ∈ Adm(R,τ), Global(g_φ) ∧ WP(g_φ, Z_k)) ∧ (∃ φ ∈ Adm(R,τ), WP(g_φ, closure W_k))`
(the second part holds on a relatively open dense set). Order:
`𝒬, cover → Rc, Lc, Ac → T, κ, δ, ε → (R, τ₀, K_t)` [the frozen protected-subdivision leaf]
`→ K_t ⋐ K_p ⋐ V_k, localise old blocks → 0 < τ ≤ τ₀ → φ → new blocks and their constants`.
**No subdivision after `τ`.** Protection needs no genericity: transport old wall blocks to the
current chart by (*); for the old sheet's graph projection `q`, the final finite mesh gives
`Lip ((p_φ − p₀) ∘ q⁻¹) ≤ C_{R,𝓑} ‖φ − φ₀‖_∞`, zero off `Rc`, continuous across the seam; for small
`τ` the projections stay invertible, the margin stays `≥ η/2`, buffers hold; transport back. This
protects *the designated wall-adapted structure*, not merely "some block".

## 3. The four kinds of points
* **Free interior.** Finite conditions on free source faces that can form different fibres:
  `Σ(g) ∩ |𝒬^(1)| = ∅`, `det (n_σ, n_τ, n_F) ≠ 0`, "source edge – other triangle – wall 2-face not
  concurrent", plus the four-point guard. Free vertices range over `ℝ³` (boundary ones over
  `ker ℓ_k`), parameters of different sheets are independent, fake double points inside one source
  star are excluded by `StarInj T`: each polynomial is not identically zero on the constrained
  parameter space. A double point on a wall then lies in two triangle interiors, the curve crosses
  the wall; with `t` the wall normal the sheets are `u = a₀t`, `v = b₀t` — a wall block. Off the
  walls ordinary triangle–triangle and edge–triangle blocks; no second block shape.
* **Free boundary.** Inside `ker ℓ_k`: the two boundary traces cross, the crossing avoids the
  boundary 1-skeleton of `𝒬`; third vertices at positive height give two half-sheets. What is
  forbidden is degeneracy on boundary wall *lines*, not boundary double points on physical 2-faces.
* **Mixed interface.** Over `Z_k` everything goes through the openness of §2; no determinant for
  frozen sheets. By complete source neighbourhoods and `hsep`, the double points over `closure W_k`
  needing treatment are free source germs; mixed points off `Z_k ∪ closure W_k` need nothing this
  round.
* **Untouched part.** Fibre equality on `K_tᶜ`; localise blocks there and transport.
* One cannot exclude all new interface double points, only those **outside the old buffered
  blocks**: if arbitrarily small perturbations produced double points over `Z_k ∩ K_p` outside the
  old blocks, a limit of source pairs (distinct by `κ`) is an old double point not covered —
  contradiction. New double points inside an old block are handled by the two complete graphs with
  strict margin (unique intersection curve).

## 4. Base case, end, and the alternatives
`Z₀ = ∅`, empty block family; nothing is imposed on never-moved parts. `Z_n = M`: blocks give normal
crossings everywhere. Candidate (i) (one common wall system) is adopted, *without* restricting
moves to open 3-simplices (images may cross walls; (*) handles it). Candidate (ii) alone fails:
`F = {z = 0}`, `A = {y = 0}`, `B = {y = |x|}` — both sheets product-transverse to `F`, the double line
crosses `F`, yet the sheets are tangent; a first stage would already have to normalise the wall
traces, which is the wall-block work.

## 5. Minimal obligations (replace the four unfrozen leaves and the false mixed-layer leaf)
| Interface | Content |
|---|---|
| `exists_commonWallComplex` | one finite common linear subdivision for the fixed finite atlas and the physical boundary |
| `wallProductBlock_transport` | prove (*), transport genuine sheets and margin, localise |
| `wallProductBlocks_stable_on_fixedSubdivision` | on the final `R`, all sufficiently small admissible parameters keep the old blocks, incl. localisation of new double points |
| `exists_wallGenericVertexMap` | relative density of the finite polynomial conditions, for **free germs only** |
| `wallProductBlocks_of_wallGenericity` | recognition of the four free models: 3-cell interior, source fold edge, interior wall, physical boundary |
`Step` is their assembly with the existing gluing. All eight frozen leaves stay verbatim:
`exists_adaptedHalfSpaceChart_in_double`, `SingularTwoCell.exists_cutOutPiece_of_closure_subset`,
`exists_gluedCell_of_vertexMap_in_adaptedChart`, `exists_globalInvariants_of_gluedCell`,
`exists_normalizationPreparation_on_prescribedRegion`, `exists_transitionSubdivisionOnOverlap`,
`hasPLNormalDoubleCrossingAt_of_isStableCrossingBlock`, `exists_protectedSubdivision_in_adaptedChart`.
**Core difference:** general position only *produces* new blocks; the induction *keeps* a
wall-adapted graph structure that transports across charts, not a set of general-position
equalities and inequalities to be re-established at every step.
