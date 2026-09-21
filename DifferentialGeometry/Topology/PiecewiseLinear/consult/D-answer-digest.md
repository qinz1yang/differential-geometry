# Digest of the answer to prompt D (vacuity audit) — 2026-09-20

The consultant read the branch at `5361892728f0`. **All four vacuity claims are confirmed**, two
of them in a stronger form than we stated. Three statements of ours were corrected. What follows
is the digest, with what the lead re-checked marked ✔.

## Corrections to our prompt

1. *Separate injectivity ⇒ theta graph* is not a consequence; a theta graph is a counterexample
   configuration, which is all the argument needs. Moreover `τσφ` and `φστ` become `xy`, `yx`,
   which **are** freely homotopic, so that pair refutes the *path*-homotopy step only. A
   range-only counterexample that survives closing the loop: `P = τσφ`, `P' = τστσφ`, closed by
   `σ`: `xy` versus `x²y`, different abelianisations.
2. `param = e ∨ param = e ∘ (θ ↦ −θ)` is false as a statement about an *arbitrary* boundary
   parametrisation (`param θ = e (θ + θ₀)`). ✔ Ours is existential (`∃ W, W.param = e ∨ …`, the
   witness is constructed), so the Lean statement stands; the prompt's wording did not say so.
   Simpler still: `Nonempty (BoundaryWordWitness G ρ w) ↔ Nonempty (… (w ∘ r))` by precomposing
   parametrisation, loop and homotopy with the reflection `r` — this does not claim `w ≃ w⁻¹`.
3. **Q2.2 had the quantifiers backwards**: the tower depends on `η`, so the two points must be
   fixed *before* `η`. ✔ The ruling in the lanes file had the same slip and is corrected.

## Part 1 — boundary words

* ✔ The word table is right, including the directions in the cross rows (walk-through given for
  both cases). In the preserving case it is the *normalised* cross word that is freely homotopic
  to `w⁻¹` when `d = 1`; the as-walked word is freely homotopic to `w`. For descent modulo a
  normal subgroup `N` run the same calculation in the quotient (`d ∈ N`).
* ✔ Both `hlong` hypotheses are impossible (`L 0 = L (3/4) = b`; preserving: `L 0 = L (1/2) = a`).
* ✔ The letters need not be injective in `X`. A model: `ℓ` a polygonal immersed interval,
  `D (s, t) = (ℓ s, t)`; add a small transverse curl before the first preimage of the chosen
  crossing — both chords of the extra branch lie in the first cap. Neither `IsBoundaryBranchCut`
  nor the branch theorem has an innermostness hypothesis.
* **A stronger single-arc lemma.** `Q` Hausdorff, `P₀ : p → q` injective, `P₁ : p → q` *any* path
  with `range P₁ ⊆ range P₀` ⇒ `f ∘ P₁ ≃ f ∘ P₀` rel end points, for every continuous `f`.
  Reverse version: `P₁ : q → p` ⇒ `f ∘ P₁ ≃ (f ∘ P₀)⁻¹`. Neither range equality nor injectivity of
  `P₁` is needed: `P₁ = P₀ ∘ r` with `r : I → I` fixing `0, 1`, and
  `H (s, t) = P₀ ((1 − s) r t + s t)`. ✔
* **Typing rule.** `τ₀ : q → u` and `σ₀ : p → q` cannot be concatenated in the source circle
  (`u ≠ p`); compare arc by arc in the source, push through `f`, and only then concatenate in `X`.
  A candidate's certificate records, per boundary arc: its lift into one named source arc, the
  ordered pair of source end points (the sign), and the literal equality of the candidate with
  `ρ ∘ f` on the lifted arc. The long cross arc needs the two seam subdivisions.
* The original and the cross word are not equal even up to inversion and conjugacy (they can
  abelianise to `(1,1,1)` and `(−1,1,−1)` in a rank-three graph), so the rejected preserving
  theorem's conclusion was a different statement, not a harmless variant.

## Part 2 — §34

* **Frozen-stage lemma** ✔: under the quoted `extend`, *every* admitted stage map equals `h` on
  its stage (hold `ε i = E`, let `ε (i+1) = δ → 0`). So the contract fails even for `h = id`
  (`g x = x + v`, `ε i = 2‖v‖`, `ε (i+1) = ‖v‖`), without using `initial`. The independent
  extension obstruction (unknotted solid torus sent to a trefoil neighbourhood) is also confirmed.
  Reordering one quantifier fixes neither defect alone.
* **The stage-indexed carriers are impossible for every `η`** ✔: `x ∈ K_k` lies in all later
  stages, so `h x ∈ carrier i` for all `i ≥ k`, contradicting `LocallyFinite carrier`
  (point-finiteness) — before smallness is used, and also for local finiteness in `h(U)`.
* **Replacement.** No tower. P0 indexes carriers by **simplices** `α` of a locally finite
  triangulation, with compact control support `S_α = ⋃_{v ∈ α} |St̄ v|`:
  (C0a) `h(S_α) ⊂ Int H_α`, `H_α ⊂ h(U)`; (C0b) `(H_α)` locally finite in the subspace `h(U)`;
  (C0c) `∀ x ∈ S_α, ∀ y z ∈ H_α, dist y z < η x` (no extrema needed).
  **P0 must not freeze `N`**: P0 fixes triangulation, carriers, buffers and *constraints* on the
  source neighbourhood; P1 jointly chooses the cut diagram and `f₁` (or merge P0 and P1).
* **Outputs of P0–P8 are pieces and incidences, never maps**; the table of outputs is in the
  answer (P1 adapted cut diagram + `f₁`, `V_v = f₁ C_v`, `E_e = f₁ D_e`; P2 generator certificate;
  P3 face balls with (F), (Ext); P4a/P4b single-label replacements with rank inequalities; P5
  normal family; P6 `Δ_σ`, `p''_{σe}`, `a''_{vσ}`; P7 `R_t`, `X''_{tv}`, `I''_{te}` with the
  no-other-marked-point clause and `R_t ⊂ H_t`; P8 the complete labelled target cell diagram).
  `h σ ⊂ Int C_σ` is *not* retained after compression.
* **Terminal assembly — locally finite labelled PL-cell assembly.** Two families `(P_λ)`,
  `(P'_λ)` over the same graded face poset, dimension ≤ 3, each a compact PL ball, boundary =
  union of proper faces, `P_λ ∩ P_μ = ⋃_{ν ≤ λ, μ} P_ν` on both sides, locally finite in their
  unions ⇒ a PL homeomorphism of the unions carrying `P_λ` onto `P'_λ` (induct over dimensions
  1, 2, 3, choosing each ball extension once; exact intersections give compatibility and
  injectivity; locally finite closed pasting gives the map **and its inverse**).
  `Section34FinalDiagram D η` := this source/target cell data with source union `U`, plus
  (C1) `h(C_v) ∪ V_v ⊂ H_v`, `h(Q_t) ∪ R_t ⊂ H_t`. It has **no field asserting a map**. Then
  `(∀ D η, Nonempty (Section34FinalDiagram D η)) → Moise352Open 3`, the estimate from (C0c)+(C1).
  E1–E7 are the rows of that induction, each acting once on its whole locally finite family.
* No properness into `M₂` is needed; isolate *locally finite closed PL pasting including the
  inverse*. The target pieces must lie in carriers inside `h(U)` for relative local finiteness to
  be usable. P5 needs a countable label set and a fair schedule, not an exhaustion.

## Part 3 — audit of the chain, and discipline

* No vacuity found in `NormalSingularCellData`, `IsBoundaryBranchCut`, `IsCrossRegluedCell`,
  `IsBoundarySurgeryCell`, `CrossSeamTubeData` (the open/compact mismatch is repaired at head),
  `GeneralPositionInDoubleBufferedStatement`, `LemmaTwoBufferedStatement`, `DescentStepStatement`,
  `Moise352Open`, `Moise351`; each with a mathematical inhabitant or a non-PL positive-error test
  (`h (x,y,z) = (x³,y,z)`, `f = id`, `φ ≡ 1`). Two positive-complexity normal-cell **models** are
  given: *preserving* — `ℓ` through `(2,0), (−1,0), (−2,−2), (0,−1), (0,2)`,
  `D (s,t) = (ℓ s, t)`, one double point `ℓ (2/3) = ℓ (10/3)` ✔; *reversing* — in
  `ℝ³ / ((x,y,z) ∼ (x+1, y, 1−z))`, `D (s,t) = [s, |s − 1/2|, t]`, `D (0,t) = D (1, 1−t)`.
* `IsBoundarySurgeryCell.pullback` is a set-theoretic selector, **not continuous** — adding
  continuity would obstruct the construction; the source-side word repair must use the continuous
  PL maps on the individual retained boundary arcs.
* **Conclusion-strength gap** ✔ (checked: `BoundarySurgeryCellPredicate.lean:339` versus
  `LemmaTwoSpine.lean:124`): the boundary-case assemblies return the surgery and subgroup
  avoidance, but `DescentStepStatement` also asks `MapsTo Sg.cell … C` (side) and the boundary
  buffer. The tube producer must supply `closed cylinder ⊂ C` and
  `end disks ⊂ Int_{BdM} B`, and the assemblies' conclusions must be extended.
* `IsCrossSeamTubeProducer` has no `[T2Space M]`; state it on the actual double.
* `exists_of_twoArcMatch_self` is an identity specialisation keeping the hypotheses — not an
  inhabitant.
* Discipline to add: test the **full conjunction on one shared tuple** with a `Nondegenerate`
  clause exercising the defect the theorem handles; permanent lemma
  `∀ γ : Path x x, ¬ Function.Injective γ`; tolerance probes (hold the current bound, drive the
  next to zero; coarse tolerance with a non-extendible embedding); local-finiteness probes (index
  type, ambient/subspace, point-finiteness against increasing families); keep `∃ d, H d`,
  `∀ d, H d → ∃ o, C d o` and `∃ o, C d₀ o` apart — none is another.
* **The next decisive non-vacuity test**: one theorem instantiating a genuine normal boundary
  branch, its actual direct and cross candidates, a boundary-relative PL tube, the PL reading and
  both boundary-word witnesses *simultaneously*. The existing model witnesses establish
  components, not that joint theorem.
