import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.Analytic.Constructions

/-! # `C^∞` of rational / Neumann-series composites in a Banach algebra

A small, self-contained toolkit of `ContDiffOn ℝ ∞` closure primitives for maps built from
**bounded (multi)linear operations and the Banach-algebra inverse** — the exact analytic
shape a chart-Sobolev rational-polynomial / inverse-Gram-Neumann Nemytskii map factors through.

Mathlib already supplies the atoms (`contDiffAt_ringInverse`: `Ring.inverse` is `C^∞` at a unit;
`IsBoundedBilinearMap.contDiff`: a bounded bilinear map is `C^∞`; the `ContDiffOn` closure
calculus `.comp`/`.add`/`.sub`/`.prodMk`).  This file packages the two recurring *composite*
shapes a quasilinear chart-Sobolev functional needs, so consumers cite a single lemma rather than
re-thread the `.comp`/unit bookkeeping:

* `contDiffOn_ringInverse_comp` — post-composition with `Ring.inverse` of a `C^∞` map that lands
  in the units (the inverse-Gram denominator);
* `contDiffOn_oneSub_inverse_comp` — the Neumann special case `x ↦ (1 − g x)⁻¹` when `g` lands in
  the open unit ball (the uniformly-convergent geometric series of a small perturbation);
* `contDiffOn_oneSub_inverse_clm` / `contDiffOn_oneSub_inverse_clm_mul_const` /
  `contDiffOn_continuousLinearMap_comp_oneSub_inverse_clm` — the Neumann inverse-Gram composite when
  the perturbation is genuinely **linear** in the input, presented as a continuous linear map
  `L : E →L[ℝ] A`: on any ball where `‖L x‖ < 1` (the only nonlinear input — the smallness witness),
  `x ↦ Ring.inverse (1 − L x)` is `C^∞`, as is its product with a constant base-inverse factor `c`
  (the full inverse Gram `(1 − L)⁻¹ · c` of a metric `g₀ + (linear-in-input perturbation)`), and the
  read-off of any single entry/multiplier through a fixed `A →L[ℝ] F`.  These are the brick the
  realized-metric inverse-Gram fires through: the realized Gram is `g₀`-Gram `· (1 + g₀⁻¹·h)`, `h`
  linear in the input section, so the inverse Gram is `(1 + g₀⁻¹·h)⁻¹ · g₀⁻¹`, a `Ring.inverse (1 − ·)`
  composite of a CLM perturbation;
* `contDiffOn_bilinDiag` — the diagonal `x ↦ B (f x, h x)` of a bounded bilinear `B` (the
  polynomial numerator's product bricks).

These hold over any real Banach space domain and any complete unital Banach algebra codomain; the
order `n : WithTop ℕ∞` is arbitrary, so each gives `C^∞` (`n = ∞`) directly.  No geometry, no
chart-Sobolev structure — this is the dry Banach-algebra layer the geometric inverse-Gram
smoothness is assembled on top of. -/

noncomputable section

open scoped ContDiff Topology

namespace DifferentialGeometry.Analysis.BanachAlgebraSmoothness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

/-- **`C^∞` of the Banach-algebra inverse post-composed with a unit-valued `C^∞` map.**

If `g : E → A` is `ContDiffOn ℝ n` on `s` and `g x` is a unit of the complete unital Banach
algebra `A` for every `x ∈ s`, then `x ↦ Ring.inverse (g x)` is `ContDiffOn ℝ n` on `s`.  This is
the inverse-Gram denominator brick: `Ring.inverse` is `C^∞` at every unit
(`contDiffAt_ringInverse`, the geometric-series analyticity of the algebra inverse on the open
unit set), composed with `g` by `ContDiffOn.comp`. -/
theorem contDiffOn_ringInverse_comp {s : Set E} {g : E → A} {n : WithTop ℕ∞}
    (hg : ContDiffOn ℝ n g s) (hunit : ∀ x ∈ s, IsUnit (g x)) :
    ContDiffOn ℝ n (fun x => Ring.inverse (g x)) s := by
  have hinv : ContDiffOn ℝ n Ring.inverse {y : A | IsUnit y} := by
    intro y hy
    exact (contDiffAt_ringInverse ℝ (IsUnit.unit hy)).contDiffWithinAt
  exact hinv.comp hg (fun x hx => hunit x hx)

/-- **`C^∞` of the Neumann inverse `x ↦ (1 − g x)⁻¹` of a small-perturbation `C^∞` map.**

If `g : E → A` is `ContDiffOn ℝ n` on `s` and lands strictly inside the open unit ball
(`‖g x‖ < 1` for `x ∈ s`), then `x ↦ Ring.inverse (1 − g x)` is `ContDiffOn ℝ n` on `s`.  This is
the uniformly-convergent Neumann series of a uniformly-small perturbation: `1 − g x` is a unit by
`Units.oneSub`, so this is `contDiffOn_ringInverse_comp` applied to the `C^∞` map
`x ↦ 1 − g x`. -/
theorem contDiffOn_oneSub_inverse_comp {s : Set E} {g : E → A} {n : WithTop ℕ∞}
    (hg : ContDiffOn ℝ n g s) (hlt : ∀ x ∈ s, ‖g x‖ < 1) :
    ContDiffOn ℝ n (fun x => Ring.inverse (1 - g x)) s := by
  refine contDiffOn_ringInverse_comp (contDiffOn_const.sub hg) (fun x hx => ?_)
  exact (Units.oneSub (g x) (hlt x hx)).isUnit

/-- **`C^∞` of the Neumann inverse `x ↦ (1 − L x)⁻¹` of a *linear* small-perturbation map.**

When the perturbation is genuinely **linear** in the input — a continuous linear map `L : E →L[ℝ] A`
— and lands strictly inside the open unit ball on `s` (`‖L x‖ < 1` for `x ∈ s`), the Neumann inverse
`x ↦ Ring.inverse (1 − L x)` is `ContDiffOn ℝ n` on `s`.  A continuous linear map is `C^∞`
(`ContinuousLinearMap.contDiff`), so this is `contDiffOn_oneSub_inverse_comp` applied to `⇑L`.  This
is the inverse-Gram denominator of a metric whose Gram is `g₀`-Gram times `(1 + (linear-in-input
perturbation))`: the realized perturbation `h` is linear in the input section, so the small factor
`L = −g₀⁻¹·h` (in the chosen fibre-operator Banach algebra) is a CLM, and the `‖L x‖ < 1` ball is the
uniform fibre-non-degeneracy ball supplied by the supercritical embedding. -/
theorem contDiffOn_oneSub_inverse_clm {s : Set E} {L : E →L[ℝ] A} {n : WithTop ℕ∞}
    (hlt : ∀ x ∈ s, ‖L x‖ < 1) :
    ContDiffOn ℝ n (fun x => Ring.inverse (1 - L x)) s :=
  contDiffOn_oneSub_inverse_comp L.contDiff.contDiffOn hlt

/-- **`C^∞` of the full inverse-Gram composite `x ↦ (1 − L x)⁻¹ · c` of a linear perturbation.**

The Neumann inverse of a CLM perturbation `L`, right-multiplied by a constant algebra element `c`.
On any ball where `‖L x‖ < 1`, `x ↦ Ring.inverse (1 − L x) * c` is `ContDiffOn ℝ n` on `s` — the
Neumann factor is `C^∞` by `contDiffOn_oneSub_inverse_clm` and the right factor is constant, so their
product is `C^∞` (`ContDiffOn.mul`).  With `c` the base inverse Gram `g₀⁻¹` this is the realized
metric's full inverse Gram `(1 + g₀⁻¹·h)⁻¹ · g₀⁻¹`, the rational object the retag's Christoffel /
Ricci / Lie numerators contract against. -/
theorem contDiffOn_oneSub_inverse_clm_mul_const {s : Set E} {L : E →L[ℝ] A} {c : A}
    {n : WithTop ℕ∞} (hlt : ∀ x ∈ s, ‖L x‖ < 1) :
    ContDiffOn ℝ n (fun x => Ring.inverse (1 - L x) * c) s :=
  (contDiffOn_oneSub_inverse_clm hlt).mul contDiffOn_const

/-- **`C^∞` of a single inverse-Gram entry / multiplier `x ↦ Φ ((1 − L x)⁻¹ · c)`.**

Reading off one scalar entry (or any fixed linear functional / contraction `Φ : A →L[ℝ] F`) of the
inverse-Gram composite keeps it `ContDiffOn ℝ n`: `C^∞` is preserved by post-composition with a
continuous linear map (`ContDiffOn.continuousLinearMap_comp`).  This is the form a downstream rational
assembly consumes — the inverse-Gram **entries as multipliers** of the polynomial numerator — without
ever re-threading the unit / Neumann bookkeeping. -/
theorem contDiffOn_continuousLinearMap_comp_oneSub_inverse_clm
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {s : Set E} {L : E →L[ℝ] A} {c : A} (Φ : A →L[ℝ] F) {n : WithTop ℕ∞}
    (hlt : ∀ x ∈ s, ‖L x‖ < 1) :
    ContDiffOn ℝ n (fun x => Φ (Ring.inverse (1 - L x) * c)) s :=
  (contDiffOn_oneSub_inverse_clm_mul_const hlt).continuousLinearMap_comp Φ

omit [CompleteSpace A] in
/-- **`C^∞` of the diagonal of a bounded bilinear map applied to two `C^∞` maps.**

For a bounded bilinear map `B : A × A → G` and `C^∞` maps `f, h : E → A` on `s`, the diagonal
`x ↦ B (f x, h x)` is `ContDiffOn ℝ n` on `s`.  A bounded bilinear map is `C^∞`
(`IsBoundedBilinearMap.contDiff`); composing with the `C^∞` pairing `x ↦ (f x, h x)` keeps it
`C^∞`.  This is the polynomial-numerator product brick (the metric-jet bilinear contractions of a
rational chart functional). -/
theorem contDiffOn_bilinDiag {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {s : Set E} {B : A × A → G} {f h : E → A} {n : WithTop ℕ∞}
    (hB : IsBoundedBilinearMap ℝ B) (hf : ContDiffOn ℝ n f s) (hh : ContDiffOn ℝ n h s) :
    ContDiffOn ℝ n (fun x => B (f x, h x)) s :=
  hB.contDiff.comp_contDiffOn (hf.prodMk hh)

end DifferentialGeometry.Analysis.BanachAlgebraSmoothness

end
