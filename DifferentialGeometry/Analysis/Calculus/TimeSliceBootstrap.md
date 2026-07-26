# TimeSliceBootstrap.lean — joint regularity from a time-slice PDE (bootstrap direction)

## What this file provides (all VERIFIED, sorry-free, axiom-clean)

Companions to `TimeJetCommute.lean` in the OPPOSITE direction: BUILD joint `(t, y)`
regularity on an open `U ⊆ ℝ × E` from separated data (pointwise time PDE + spatial slice
differentiability).  This is the analytic kernel of the Ricci-flow limit joint-regularity
bootstrap (`∂ₜ g = −2 Ric(g)` upgrades time regularity from spatial regularity); the
consumer plan lives in
`Geometry/Flow/RicciFlow/HCGCompactness/FlowLimitRegularity.md`.

- `hasFDerivAt_of_slice` — kernel: `∂ₜ G = R` pointwise on `U` (`HasDerivAt`), `R`
  continuous (within `U`) at `p₀`, slice `G p₀.1` differentiable at `p₀.2` ⟹ the joint map
  is differentiable at `p₀` with derivative `(fst).smulRight (R p₀) + W.comp snd`.
  Mathlib has NO "continuous partials ⟹ differentiable" on products; this fills the
  one-time-variable case.  Proof: mean-value inequality
  (`Convex.norm_image_sub_le_of_norm_hasDerivWithin_le`) on the time segment
  `[[p₀.1, p.1]] × {p.2}` (stays in a ball where `‖R − R p₀‖ ≤ ε`; prod norm is sup norm so
  the segment bound is direct), plus `hslice.comp hasFDerivAt_snd` for the spatial part.
- `contDiffOn_succ_of_pde` — induction step: `R`, `W` jointly `C^q` ⟹ `G` jointly
  `C^{q+1}`.  Assembly of the fderiv is CLM algebra: `smulRightL`-composition for the
  `R`-part, `ContDiffOn.clm_comp` with a constant for the `W`-part, then
  `contDiffOn_succ_iff_fderiv_of_isOpen` (the `n = ω` conjunct is discharged by `simp`).
- `contDiffOn_one_of_pde` — first bootstrap step (`q = 0`): continuous `R`, `W` give joint
  `C¹`.
- `contDiffOn_inf_of_pde` — `C^∞` endpoint: jointly-`C^∞` `R`, `W` give jointly-`C^∞` `G`
  (instantiate the step at each finite order via `contDiffOn_infty`; no induction).

No completeness assumptions; codomain `F` is any real normed space, so the lemmas apply
verbatim to jet-valued families (`W_k`-bootstrap at every jet level).

## Verification

Focused check + targeted build passed; all four endpoints
`[propext, Classical.choice, Quot.sound]`, no `sorryAx` (temporary `#print axioms`
removed after reading).  Not added to the umbrella `DifferentialGeometry.lean` — matches
the `TimeJetCommute`/`TimeJetEvolution` precedent (these Analysis/Calculus helpers enter
the import graph through their consumers).

## Gotchas found

- `norm_image_sub_le_of_norm_hasDerivWithin_le` is in `namespace Convex` despite ALSO
  taking `Convex ℝ s` as an explicit argument.
- `ContDiffOn.add` needs `Mathlib.Analysis.Calculus.ContDiff.Operations` (NOT pulled in by
  `ContDiff.Comp`); without it, dot-notation `.add` falls through to `Function.add` with a
  confusing "environment does not contain" error.
- `(q : ℕ)` smoothness-index casts: `mod_cast le_top` for `(q : WithTop ℕ∞) ≤ ∞`
  (plain `le_top` gives `≤ ω`, which is NOT `∞`), `exact_mod_cast` for `↑(q+1) = ↑q + 1`.

## What is NOT here (next bricks)

- The SWAP lemma (`∂ₜ` of spatial jets = spatial jets of `R`, via FTC + parametric
  interval-integral differentiation) — needed to run the step lemma at jet levels `k ≥ 1`.
- The jets-of-algebra closure ("jets of the Ricci expression are `C^q` given tracked jets
  of the metric") — the one genuine wall of the full `C^∞` bootstrap; see the route note.
