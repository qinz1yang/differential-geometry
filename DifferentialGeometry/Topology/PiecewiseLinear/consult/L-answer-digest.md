# Digest — answer to consult L (does the pairing seed exist?), 2026-09-21

**Verdict of the consultant: `NEEDS_PROOF`.** Proved: the seed exists *under an added quantitative
transversality condition*. For an arbitrary PL normal crossing relative to an arbitrary `Ac`: no
complete proof, no counterexample. Not FALSE, and not to be frozen as verified. (The fourth
review's counterexample only excluded balls centred at the *old* map; the fifth review's
distinction stands.)

Status of this digest: **not independently verified by the lead**; items marked ✔ were checked.

## 1. "Relative straightening" is not a proof
One must keep `Ac`, keep the full-preimage pairing, and get an open ball in **all** independent
vertex parameters of the **final** `R` at once; local straightening charts plus one good translate
of one bent model prove none of this. ✔ Moreover "both sheets flat along the whole protected
double curve" cannot be the goal: around a closed double branch it would make the curve locally
straight everywhere, hence contained in one line. The target is a *stable graph form*.

## 2. A sufficient condition that survives the final subdivision
Near every double point over the protected compact set, in an **affine** change of the `ec`
coordinates, the two complete local source sheets are graphs
`A = {u = a(v,t)}`, `B = {v = b(u,t)}` with PL `a, b` whose graph projections parametrise the source
sheets, and a uniform margin `Lip_v(a) · Lip_u(b) ≤ 1 − η`, `η > 0` (only the transverse variables
are controlled; slopes along `t` may be large); only these two sheets meet the shrunk block, the
rest of the source stays at positive distance. Then **`φ_* = ec ∘ D` works**: finish *all*
subdivision first (facewise affine, `Ac`, `Lc`, the control complex `T`, the local blocks, the
frozen-star separation), **then** choose `ρ` from the constant `C_R` of the fixed finite `R`
(`max_σ ‖D(p_φ − p_{φ_*})|_σ‖ ≤ C_R · max_v |φ v − φ_* v|`): projections stay invertible, the margin
is halved at most; for fixed `t` the fixed-point equation `u = a(b(u,t),t)` has a unique solution,
so exactly one PL intersection arc persists, no small loops; connect along the old curve, extend
PL over the four sectors to get `χ`, lift on the sheets to get `ψ`; positive separation makes it a
certificate on the **full** preimage. Shrink `ρ` again for height, `K`, frozen stars, `StarInj T`.
This answers the fifth review's trap: *choose the final `R` first, then `ρ` from `C_R`* — no
relation between radii before and after subdivision is needed.
What is **not** done: producing the margin condition from an arbitrary
`HasPLNormalDoubleCrossingAt` relative to a given `Ac`.

## 3. Recommended: change the induction invariant, not the seed
Do not let later steps receive an arbitrary "topologically normal" old region; make each step
**output** a normal region that is *stable in the later charts as well*. Concretely: fix the finite
chart family and a common target subdivision `𝒬` on the relevant compact overlaps on whose top
simplices the chart transitions are affine; for the *new* double curves require, beyond the present
guard, `Σ(g) ∩ |𝒬^(1)| = ∅`, `Σ(g) ⋔ relint F` for `F ∈ 𝒬^(2)`, and exclude compound degeneracies
(a fold edge of one sheet meeting the other sheet on a wall of `𝒬`, …) — finitely many
cross-simplex transversality conditions, **not** consequences of the four-vertex guard, needing
their own density and recognition proofs. Then near a new double point, in a later chart, either
both sheets are planes, or one sheet has a fold edge, or only the transition crosses one wall (the
curve crossing it transversally): in each case an affine coordinate choice gives the graph model
with margin. No closed branch needs to be flat. The induction starts with no protected region; each
step first uses the old region's margin to pick a safe open ball on the final subdivision, then
chooses inside it a vertex map satisfying the new finite transversality conditions. The fifth
review's analysis of the relative parameter space and of the algebraic bad set is the basis.

## 4. What does not work
* **Enlarging the frozen region** is not a drop-in replacement: when `Σ(D) ∩ Z ∩ closure W ≠ ∅`,
  freezing the full source preimage there violates `Disjoint Ac.space (D ⁻¹' closure W)`; mixed
  simplices at the edge of the frozen region still need crossing recognition.
* ✔ **A single target ambient isotopy** cannot normalise: `g = H ∘ D` has the same double points
  and the same local intersection types as `D`. Different source sheets must move differently.

## 5. Boundary models
No extra obstruction for the strengthened version: take `t = ℓ`, restrict the model to `t ≥ 0`; the
two boundary traces on `t = 0` must themselves satisfy the strict margin — zero and positive
heights alone do not replace it. `Lc` vertices in `ker ℓ` and the others at positive height keep the
arc ending exactly on the boundary; the PL extension is done preserving `t = 0`, giving
`χ (U ∩ BdM) = U' ∩ BdM`.

## Consequence for the skeleton (lead's note)
Adopting §3 changes the **induction invariant** of `Skeleton/GeneralPositionInDouble.lean`: the
crossing leaf must output *stable* normality (a new predicate: the graph model with margin in every
chart of the fixed finite family), the seed leaf then receives it and becomes provable by §2, and
the endpoint extraction forgets stability. That touches two frozen leaves
(`exists_normalCrossings_of_gluedCell`, `exists_normalizationPreparation_on_prescribedRegion`) and
adds the new transversality conditions to the generic-choice leaf. **Not started**: to be designed
after the due-diligence pass on the frozen leaves (`consult/M-…`) returns, with lane H.
