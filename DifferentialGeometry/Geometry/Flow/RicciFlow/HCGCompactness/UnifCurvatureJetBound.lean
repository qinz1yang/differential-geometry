import DifferentialGeometry.Geometry.Curvature.PerturbedRiemannOpDifferenceBound
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciArmResidualCoefficientFields
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.RealizedGramDiff
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.IteratedCovGradLinear
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricCovDerivBridge
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.ConvFieldInputs
import DifferentialGeometry.Geometry.Curvature.RicciOperatorNormBound
import DifferentialGeometry.Geometry.Metric.ConvexCombination

/-!
# Uniform curvature-jet bound (item-6 brick 2a)

Downstream discharge of the class-uniform curvature-jet bound that the S1
Gårding constant (`UnifBochnerGap.lean`) consumes abstractly.  This file is the
`HCGCompactness` home of brick (2a); it imports the `Geometry/Curvature/`
difference/fixed assets (upstream of HCG, so importable) — see
`UnifCurvatureJetBound.md` for the ratified route (2a-0 → 2a-tel → 2a-hi → 2a-pkg)
and the asset inventory.

## This file (session 4, order-0 composition core)

`unifCurvatureSup_singleLink_of_diff` — the order-0 curvature sup bound assembled
from the order-0 Riemann *difference* bound (its conclusion, taken as a
hypothesis `hdiff`; discharged from the class jets by the frontier layer) and the
committed *fixed*-`gBase` curvature bound
(`exists_uniform_riemannOp_LeviCivita_gNorm_bound`), converted from the `gBase`
to the `g₀` inner product by `Λ`-comparability.  Explicit constant
`F = Λ²·(Cd + √Kbase)`.

The genuinely-missing infrastructure (constructing `P = g₀ − gBase` as a
`SmoothCcTensor gBase 0 2`, its `htie`, the comparability→`gFibreOpBound` bridge,
and the metric-jet envelope), together with the `convexComb` telescoping to the
full class `Λ ≥ 1`, is the named frontier recorded in `UnifCurvatureJetBound.md`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.HCGCompactness

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

set_option linter.unusedSectionVars false in
/-- The `g`-norm triangle inequality on a fibre:
`√(g(a+b,a+b)) ≤ √(g(a,a)) + √(g(b,b))`.  (Local copy of the private
`gNorm_self_triangle` used in `PerturbedRiemannOpDifferenceBound`.) -/
private lemma gAddNorm_le
    (g : SmoothRiemannianMetric I M) (x : M) (a b : TangentSpace I x) :
    Real.sqrt (g.inner x (a + b) (a + b)) ≤
      Real.sqrt (g.inner x a a) + Real.sqrt (g.inner x b b) := by
  have haa : 0 ≤ g.inner x a a := metric_inner_self_nonneg (I := I) (M := M) g x a
  have hbb : 0 ≤ g.inner x b b := metric_inner_self_nonneg (I := I) (M := M) g x b
  have hcs : g.inner x a b ≤ Real.sqrt (g.inner x a a) * Real.sqrt (g.inner x b b) := by
    refine le_trans (le_abs_self _) ?_
    exact abs_metric_inner_le_sqrt_metric_quadratic (I := I) (M := M) g x a b
  have hexpand : g.inner x (a + b) (a + b) =
      g.inner x a a + 2 * g.inner x a b + g.inner x b b := by
    have h1 : g.inner x (a + b) (a + b) =
        g.inner x a (a + b) + g.inner x b (a + b) := by
      rw [map_add (g.inner x), ContinuousLinearMap.add_apply]
    have h2 : g.inner x a (a + b) = g.inner x a a + g.inner x a b :=
      map_add (g.inner x a) a b
    have h3 : g.inner x b (a + b) = g.inner x b a + g.inner x b b :=
      map_add (g.inner x b) a b
    have h4 : g.inner x b a = g.inner x a b := g.symm x b a
    rw [h1, h2, h3, h4]; ring
  have hsum_nn : 0 ≤ Real.sqrt (g.inner x a a) + Real.sqrt (g.inner x b b) :=
    add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  rw [show Real.sqrt (g.inner x a a) + Real.sqrt (g.inner x b b) =
      Real.sqrt ((Real.sqrt (g.inner x a a) + Real.sqrt (g.inner x b b)) ^ 2) from
    (Real.sqrt_sq hsum_nn).symm]
  refine Real.sqrt_le_sqrt ?_
  rw [hexpand]
  have hsq : (Real.sqrt (g.inner x a a) + Real.sqrt (g.inner x b b)) ^ 2 =
      g.inner x a a + 2 * (Real.sqrt (g.inner x a a) * Real.sqrt (g.inner x b b)) +
        g.inner x b b := by
    rw [add_sq, Real.sq_sqrt haa, Real.sq_sqrt hbb]; ring
  rw [hsq]
  linarith [hcs]

/-- **Order-0 curvature sup bound, single-link (`Λ < 2`) regime.**

Given the order-0 Riemann *difference* bound `hdiff` (the conclusion of
`exists_riemannOp_LeviCivita_difference_gQuadratic_le_of_jetEnvelope` at role
base = `gBase`, `g₁ = g₀`; discharged from the class metric jets by the frontier
layer) and `Λ`-comparability of `g₀` with `gBase`, the absolute Riemann operator
of `g₀` is bounded in the `g₀` inner product by `F²` with

  `F = Λ² · (Cd + √Kbase)`,

where `Kbase` is the fixed `gBase` curvature constant
(`exists_uniform_riemannOp_LeviCivita_gNorm_bound`).  This is the composition
spine of brick 2a-0; the full class `Λ ≥ 1` follows by `convexComb` telescoping
(2a-tel). -/
theorem unifCurvatureSup_singleLink_of_diff
    (gBase g₀ : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 1 ≤ Λ)
    (hcomp : ∀ (x : M) (v : TangentSpace I x),
      Λ⁻¹ * gBase.inner x v v ≤ g₀.inner x v v ∧
        g₀.inner x v v ≤ Λ * gBase.inner x v v)
    {Cd : ℝ} (hCd : 0 ≤ Cd)
    (hdiff : ∀ (x : M) (v w u : TangentSpace I x),
      gBase.inner x
          (riemannOp (cov := LeviCivita (I := I) g₀) x v w u -
            riemannOp (cov := LeviCivita (I := I) gBase) x v w u)
          (riemannOp (cov := LeviCivita (I := I) g₀) x v w u -
            riemannOp (cov := LeviCivita (I := I) gBase) x v w u) ≤
        Cd ^ 2 * gBase.inner x v v * gBase.inner x w w * gBase.inner x u u) :
    ∃ F : ℝ, 0 ≤ F ∧
      ∀ (x : M) (v w u : TangentSpace I x),
        g₀.inner x
            (riemannOp (cov := LeviCivita (I := I) g₀) x v w u)
            (riemannOp (cov := LeviCivita (I := I) g₀) x v w u) ≤
          F ^ 2 * g₀.inner x v v * g₀.inner x w w * g₀.inner x u u := by
  classical
  have hΛ0 : (0 : ℝ) < Λ := lt_of_lt_of_le one_pos hΛ
  obtain ⟨Kb, hKb0, hKb⟩ :=
    exists_uniform_riemannOp_LeviCivita_gNorm_bound (I := I) (M := M) gBase
  refine ⟨Λ ^ 2 * (Cd + Real.sqrt Kb),
    mul_nonneg (sq_nonneg _) (add_nonneg hCd (Real.sqrt_nonneg _)), ?_⟩
  intro x v w u
  set R0 : TangentSpace I x := riemannOp (cov := LeviCivita (I := I) g₀) x v w u with hR0
  set Rb : TangentSpace I x := riemannOp (cov := LeviCivita (I := I) gBase) x v w u with hRb
  -- fibre quadratics in the base metric, all nonnegative
  have hbvv0 : 0 ≤ gBase.inner x v v := metric_inner_self_nonneg (I := I) (M := M) gBase x v
  have hbww0 : 0 ≤ gBase.inner x w w := metric_inner_self_nonneg (I := I) (M := M) gBase x w
  have hbuu0 : 0 ≤ gBase.inner x u u := metric_inner_self_nonneg (I := I) (M := M) gBase x u
  set P3 : ℝ := gBase.inner x v v * gBase.inner x w w * gBase.inner x u u with hP3
  have hP30 : 0 ≤ P3 := by
    rw [hP3]; exact mul_nonneg (mul_nonneg hbvv0 hbww0) hbuu0
  -- the two committed inputs, folded to `R0`/`Rb` and the single product `P3`
  have h := hdiff x v w u
  rw [← hR0, ← hRb] at h
  have hk := hKb x v w u
  rw [← hRb] at hk
  have hd3 : gBase.inner x (R0 - Rb) (R0 - Rb) ≤ Cd ^ 2 * P3 := by
    rw [hP3]
    calc gBase.inner x (R0 - Rb) (R0 - Rb)
        ≤ Cd ^ 2 * gBase.inner x v v * gBase.inner x w w * gBase.inner x u u := h
      _ = Cd ^ 2 * (gBase.inner x v v * gBase.inner x w w * gBase.inner x u u) := by ring
  have hb3 : gBase.inner x Rb Rb ≤ Kb * P3 := by
    rw [hP3]
    calc gBase.inner x Rb Rb
        ≤ Kb * gBase.inner x v v * gBase.inner x w w * gBase.inner x u u := hk
      _ = Kb * (gBase.inner x v v * gBase.inner x w w * gBase.inner x u u) := by ring
  -- √ of each input
  have hnDiff : Real.sqrt (gBase.inner x (R0 - Rb) (R0 - Rb)) ≤ Cd * Real.sqrt P3 := by
    calc Real.sqrt (gBase.inner x (R0 - Rb) (R0 - Rb))
        ≤ Real.sqrt (Cd ^ 2 * P3) := Real.sqrt_le_sqrt hd3
      _ = Cd * Real.sqrt P3 := by rw [Real.sqrt_mul (sq_nonneg Cd), Real.sqrt_sq hCd]
  have hnRb : Real.sqrt (gBase.inner x Rb Rb) ≤ Real.sqrt Kb * Real.sqrt P3 := by
    calc Real.sqrt (gBase.inner x Rb Rb)
        ≤ Real.sqrt (Kb * P3) := Real.sqrt_le_sqrt hb3
      _ = Real.sqrt Kb * Real.sqrt P3 := by rw [Real.sqrt_mul hKb0]
  -- triangle: `R0 = (R0 - Rb) + Rb`
  have hcancel : (R0 - Rb) + Rb = R0 := by abel
  have htri : Real.sqrt (gBase.inner x R0 R0) ≤
      (Cd + Real.sqrt Kb) * Real.sqrt P3 := by
    have htr := gAddNorm_le (I := I) (M := M) gBase x (R0 - Rb) Rb
    rw [hcancel] at htr
    calc Real.sqrt (gBase.inner x R0 R0)
        ≤ Real.sqrt (gBase.inner x (R0 - Rb) (R0 - Rb)) +
            Real.sqrt (gBase.inner x Rb Rb) := htr
      _ ≤ Cd * Real.sqrt P3 + Real.sqrt Kb * Real.sqrt P3 := add_le_add hnDiff hnRb
      _ = (Cd + Real.sqrt Kb) * Real.sqrt P3 := by ring
  -- square the triangle to get the base-metric curvature bound
  have hR0nn : 0 ≤ gBase.inner x R0 R0 :=
    metric_inner_self_nonneg (I := I) (M := M) gBase x R0
  have hbaseSq : gBase.inner x R0 R0 ≤ (Cd + Real.sqrt Kb) ^ 2 * P3 := by
    have hmm := mul_self_le_mul_self (Real.sqrt_nonneg _) htri
    rw [Real.mul_self_sqrt hR0nn] at hmm
    calc gBase.inner x R0 R0
        ≤ ((Cd + Real.sqrt Kb) * Real.sqrt P3) *
            ((Cd + Real.sqrt Kb) * Real.sqrt P3) := hmm
      _ = (Cd + Real.sqrt Kb) ^ 2 * (Real.sqrt P3 * Real.sqrt P3) := by ring
      _ = (Cd + Real.sqrt Kb) ^ 2 * P3 := by rw [Real.mul_self_sqrt hP30]
  -- convert the base-metric bound to the `g₀` inner product via comparability
  have hout : g₀.inner x R0 R0 ≤ Λ * gBase.inner x R0 R0 := (hcomp x R0).2
  have hcoeff_nn : 0 ≤ (Cd + Real.sqrt Kb) ^ 2 := sq_nonneg _
  -- input conversion: `gBase(z,z) ≤ Λ · g₀(z,z)` on the diagonal
  have hinConv : ∀ z : TangentSpace I x, gBase.inner x z z ≤ Λ * g₀.inner x z z := by
    intro z
    have hz := (hcomp x z).1
    have hz2 := mul_le_mul_of_nonneg_left hz hΛ0.le
    rwa [← mul_assoc, mul_inv_cancel₀ hΛ0.ne', one_mul] at hz2
  have hg0vv0 : 0 ≤ g₀.inner x v v := metric_inner_self_nonneg (I := I) (M := M) g₀ x v
  have hg0ww0 : 0 ≤ g₀.inner x w w := metric_inner_self_nonneg (I := I) (M := M) g₀ x w
  have hΛg0vv : 0 ≤ Λ * g₀.inner x v v := mul_nonneg hΛ0.le hg0vv0
  have hΛg0ww : 0 ≤ Λ * g₀.inner x w w := mul_nonneg hΛ0.le hg0ww0
  have hstep1 : gBase.inner x v v * gBase.inner x w w ≤
      (Λ * g₀.inner x v v) * (Λ * g₀.inner x w w) :=
    mul_le_mul (hinConv v) (hinConv w) hbww0 hΛg0vv
  have hstep2 : P3 ≤ (Λ * g₀.inner x v v) * (Λ * g₀.inner x w w) * (Λ * g₀.inner x u u) := by
    rw [hP3]
    exact mul_le_mul hstep1 (hinConv u) hbuu0 (mul_nonneg hΛg0vv hΛg0ww)
  have hP3_conv : P3 ≤ Λ ^ 3 * (g₀.inner x v v * g₀.inner x w w * g₀.inner x u u) := by
    refine le_trans hstep2 (le_of_eq ?_); ring
  -- assemble
  calc g₀.inner x R0 R0
      ≤ Λ * gBase.inner x R0 R0 := hout
    _ ≤ Λ * ((Cd + Real.sqrt Kb) ^ 2 * P3) :=
          mul_le_mul_of_nonneg_left hbaseSq hΛ0.le
    _ ≤ Λ * ((Cd + Real.sqrt Kb) ^ 2 *
          (Λ ^ 3 * (g₀.inner x v v * g₀.inner x w w * g₀.inner x u u))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hP3_conv hcoeff_nn) hΛ0.le
    _ = (Λ ^ 2 * (Cd + Real.sqrt Kb)) ^ 2 *
          g₀.inner x v v * g₀.inner x w w * g₀.inner x u u := by ring

/-! ### P-construction tie API (session 5)

The metric-difference realization `metricDifferenceCcTensor gBase g₀`
(`RicciArmResidualCoefficientFields.lean:118`, reused) supplies the perturbation
`P` the order-0 difference asset consumes; these lemmas prove it satisfies the
asset's `htie` shape at role base = `gBase`, `g₁ = g₀`.  The two dischargers
(`gFibreOpBound` from comparability; the order-`≤2` jet envelope from
`MetricCovDerivOrderBoundOn`) are the remaining frontier — see
`UnifCurvatureJetBound.md`. -/

/-- The metric difference `metricDifferenceCcTensor gBase g₀` extracts, before
symmetrization, to the pointwise metric difference `g₀ − gBase`. -/
theorem metricDiff_ccBilin (gBase g₀ : SmoothRiemannianMetric I M)
    (x : M) (v w : TangentSpace I x) :
    ccTensorBilin (I := I) gBase
        (metricDifferenceCcTensor (I := I) (M := M) gBase g₀) x v w =
      g₀.inner x v w - gBase.inner x v w := by
  have h : metricDifferenceCcTensor (I := I) (M := M) gBase g₀ =
      metricCcTensor (I := I) (M := M) gBase g₀ -
        metricCcTensor (I := I) (M := M) gBase gBase := rfl
  rw [h, ccTensorBilin_sub, metricCcTensor_apply, metricCcTensor_apply]

/-- The metric difference realizes `g₀ − gBase` after symmetrization as well:
the difference of two symmetric metrics is already symmetric. -/
theorem metricDiff_ccBilinSymm (gBase g₀ : SmoothRiemannianMetric I M)
    (x : M) (v w : TangentSpace I x) :
    ccTensorBilinSymm (I := I) gBase
        (metricDifferenceCcTensor (I := I) (M := M) gBase g₀) x v w =
      g₀.inner x v w - gBase.inner x v w := by
  rw [ccTensorBilinSymm_apply, metricDiff_ccBilin gBase g₀ x v w,
    metricDiff_ccBilin gBase g₀ x w v, gBase.symm x w v, g₀.symm x w v]
  ring

/-- **Tie identity — the asset `htie` shape (role base = `gBase`, `g₁ = g₀`).**
`g₀` is realized as `gBase` plus the symmetric perturbation
`ccTensorBilinSymm gBase (metricDifferenceCcTensor gBase g₀)`.  This discharges
the `htie` hypothesis of
`exists_riemannOp_LeviCivita_difference_gQuadratic_le_of_jetEnvelope`. -/
theorem metricDiff_tie (gBase g₀ : SmoothRiemannianMetric I M)
    (x : M) (v w : TangentSpace I x) :
    g₀.inner x v w =
      gBase.inner x v w +
        ccTensorBilinSymm (I := I) gBase
          (metricDifferenceCcTensor (I := I) (M := M) gBase g₀) x v w := by
  rw [metricDiff_ccBilinSymm]; ring

/-! ### Discharger 1 — comparability ⟹ `gFibreOpBound` (session 6)

The perturbation `ccTensorBilinSymm gBase P` (`P = metricDifferenceCcTensor
gBase g₀`), which realizes `g₀ − gBase`, has `gBase`-fibre operator norm at most
`Λ − 1`.  This supplies the `hδ` hypothesis of the order-0 difference asset (with
`δ₀ = Λ − 1 < 1`, i.e. the `Λ < 2` regime). -/

set_option linter.unusedSectionVars false in
/-- **Off-diagonal control from a diagonal bound** (the reusable "operator norm =
diagonal norm" fact for a symmetric fibre form): a symmetric bilinear form `D`
on a metric fibre with `|D u u| ≤ c · gBase(u,u)` on the diagonal satisfies
`|D v w| ≤ c · √(gBase(v,v)) · √(gBase(w,w))`.  Proof: polarization gives the
arithmetic-mean bound `|D v w| ≤ ½c(gBase(v,v)+gBase(w,w))`; applying it to the
`gBase`-unit rescalings `v/√(gBase(v,v))`, `w/√(gBase(w,w))` sharpens it to the
geometric mean.  Degenerate slots (`gBase(·,·)=0 ⟹ ·=0` by positivity) are
handled separately. -/
private lemma clm_offdiag_le_of_diag {x : M} (gBase : SmoothRiemannianMetric I M)
    (D : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (hDsymm : ∀ v w : TangentSpace I x, D v w = D w v)
    {c : ℝ} (hc : 0 ≤ c)
    (hdiag : ∀ u : TangentSpace I x, |D u u| ≤ c * gBase.inner x u u) :
    ∀ v w : TangentSpace I x,
      |D v w| ≤ c * Real.sqrt (gBase.inner x v v) * Real.sqrt (gBase.inner x w w) := by
  have hAM : ∀ v w : TangentSpace I x,
      |D v w| ≤ c / 2 * (gBase.inner x v v + gBase.inner x w w) := by
    intro v w
    have hpol : (4 : ℝ) * D v w = D (v + w) (v + w) - D (v - w) (v - w) := by
      simp only [map_add, map_sub, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.sub_apply]
      rw [hDsymm w v]; ring
    have hpar : gBase.inner x (v + w) (v + w) + gBase.inner x (v - w) (v - w) =
        2 * gBase.inner x v v + 2 * gBase.inner x w w := by
      simp only [map_add, map_sub, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.sub_apply]
      ring
    obtain ⟨hd1lo, hd1hi⟩ := abs_le.mp (hdiag (v + w))
    obtain ⟨hd2lo, hd2hi⟩ := abs_le.mp (hdiag (v - w))
    have h4 : (4 : ℝ) * |D v w| ≤ c * (2 * gBase.inner x v v + 2 * gBase.inner x w w) := by
      have hstep : |(4 : ℝ) * D v w| ≤
          c * gBase.inner x (v + w) (v + w) + c * gBase.inner x (v - w) (v - w) := by
        rw [hpol, abs_le]
        constructor <;> linarith
      rw [abs_mul, show |(4 : ℝ)| = 4 from by norm_num, ← mul_add, hpar] at hstep
      exact hstep
    linarith
  intro v w
  rcases eq_or_ne v 0 with rfl | hv
  · simp only [map_zero, ContinuousLinearMap.zero_apply, abs_zero]
    exact mul_nonneg (mul_nonneg hc (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  rcases eq_or_ne w 0 with rfl | hw
  · simp only [map_zero, abs_zero]
    exact mul_nonneg (mul_nonneg hc (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  · have hvv : 0 < gBase.inner x v v := gBase.pos x v hv
    have hww : 0 < gBase.inner x w w := gBase.pos x w hw
    have ha0 : 0 < Real.sqrt (gBase.inner x v v) := Real.sqrt_pos.mpr hvv
    have hb0 : 0 < Real.sqrt (gBase.inner x w w) := Real.sqrt_pos.mpr hww
    set a := Real.sqrt (gBase.inner x v v) with ha_def
    set b := Real.sqrt (gBase.inner x w w) with hb_def
    have hna : gBase.inner x (a⁻¹ • v) (a⁻¹ • v) = 1 := by
      simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
      rw [← Real.sq_sqrt hvv.le, ← ha_def]; field_simp
    have hnb : gBase.inner x (b⁻¹ • w) (b⁻¹ • w) = 1 := by
      simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
      rw [← Real.sq_sqrt hww.le, ← hb_def]; field_simp
    have hDscale : D (a⁻¹ • v) (b⁻¹ • w) = a⁻¹ * b⁻¹ * D v w := by
      simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]; ring
    have hAMs := hAM (a⁻¹ • v) (b⁻¹ • w)
    rw [hna, hnb, hDscale, abs_mul, abs_mul,
      abs_of_pos (by positivity : (0 : ℝ) < a⁻¹),
      abs_of_pos (by positivity : (0 : ℝ) < b⁻¹)] at hAMs
    have hAMs' : a⁻¹ * b⁻¹ * |D v w| ≤ c := by
      have hcc : c / 2 * (1 + 1) = c := by ring
      rw [hcc] at hAMs; exact hAMs
    have hid : a * b * (a⁻¹ * b⁻¹) = 1 := by
      rw [mul_mul_mul_comm, mul_inv_cancel₀ ha0.ne', mul_inv_cancel₀ hb0.ne', one_mul]
    calc |D v w| = a * b * (a⁻¹ * b⁻¹) * |D v w| := by rw [hid, one_mul]
      _ = a * b * (a⁻¹ * b⁻¹ * |D v w|) := by ring
      _ ≤ a * b * c := mul_le_mul_of_nonneg_left hAMs' (by positivity)
      _ = c * a * b := by ring

set_option linter.unusedSectionVars false in
/-- The diagonal bound `|g₀(u,u) − gBase(u,u)| ≤ (Λ−1)·gBase(u,u)` from
`Λ`-comparability (`|Λ⁻¹ − 1| = 1 − Λ⁻¹ ≤ Λ − 1` for `Λ ≥ 1`). -/
private lemma metricDiff_diag_le (gBase g₀ : SmoothRiemannianMetric I M) {Λ : ℝ}
    (hΛ : 1 ≤ Λ)
    (hcomp : ∀ (x : M) (v : TangentSpace I x),
      Λ⁻¹ * gBase.inner x v v ≤ g₀.inner x v v ∧
        g₀.inner x v v ≤ Λ * gBase.inner x v v)
    (x : M) (u : TangentSpace I x) :
    |g₀.inner x u u - gBase.inner x u u| ≤ (Λ - 1) * gBase.inner x u u := by
  have hΛ0 : (0 : ℝ) < Λ := lt_of_lt_of_le one_pos hΛ
  have hb0 : 0 ≤ gBase.inner x u u := metric_inner_self_nonneg (I := I) (M := M) gBase x u
  obtain ⟨hlo, hhi⟩ := hcomp x u
  have hLam : (0 : ℝ) ≤ Λ⁻¹ + Λ - 2 := by
    have hrw : Λ⁻¹ + Λ - 2 = (Λ - 1) ^ 2 / Λ := by field_simp; ring
    rw [hrw]; positivity
  rw [abs_le]
  refine ⟨?_, by linarith⟩
  have hprod : 0 ≤ (Λ⁻¹ + Λ - 2) * gBase.inner x u u := mul_nonneg hLam hb0
  nlinarith [hlo, hprod]

/-- **Discharger 1.**  Under `Λ`-comparability, the symmetric perturbation
`ccTensorBilinSymm gBase (metricDifferenceCcTensor gBase g₀)` realizing
`g₀ − gBase` has `gBase`-fibre operator norm at most `Λ − 1`. -/
theorem metricDiff_gFibreOpBound (gBase g₀ : SmoothRiemannianMetric I M) {Λ : ℝ}
    (hΛ : 1 ≤ Λ)
    (hcomp : ∀ (x : M) (v : TangentSpace I x),
      Λ⁻¹ * gBase.inner x v v ≤ g₀.inner x v v ∧
        g₀.inner x v v ≤ Λ * gBase.inner x v v) :
    gFibreOpBound (I := I) gBase
      (ccTensorBilinSymm (I := I) gBase
        (metricDifferenceCcTensor (I := I) (M := M) gBase g₀)) (Λ - 1) := by
  intro x v w
  have hsymm : ∀ p q : TangentSpace I x,
      ccTensorBilinSymm (I := I) gBase
          (metricDifferenceCcTensor (I := I) (M := M) gBase g₀) x p q =
        ccTensorBilinSymm (I := I) gBase
          (metricDifferenceCcTensor (I := I) (M := M) gBase g₀) x q p :=
    fun p q => ccTensorBilinSymm_symm (I := I) gBase _ x p q
  have hdiag : ∀ u : TangentSpace I x,
      |ccTensorBilinSymm (I := I) gBase
          (metricDifferenceCcTensor (I := I) (M := M) gBase g₀) x u u| ≤
        (Λ - 1) * gBase.inner x u u := by
    intro u
    rw [metricDiff_ccBilinSymm]
    exact metricDiff_diag_le (I := I) (M := M) gBase g₀ hΛ hcomp x u
  exact clm_offdiag_le_of_diag (I := I) (M := M) gBase
    (ccTensorBilinSymm (I := I) gBase
      (metricDifferenceCcTensor (I := I) (M := M) gBase g₀) x)
    hsymm (by linarith : (0 : ℝ) ≤ Λ - 1) hdiag v w

/-! ### Discharger 2 — jet envelope: RS linearity reduction (session 7)

Recon verdict (see `UnifCurvatureJetBound.md`, session 7): the covariant-derivative
convention/slot-order/connection mismatch feared in session 6 is **resolved** —
`covGrad` and `metricCovDeriv` differentiate against the *same* connection
(`LeviCivita g = leviCivitaConnectionOfMetric g` by `rfl`) with the *same*
derivative-slot-first order, and the `r = 0` RS↔0S unit-evaluation bridges exist
(`covDeriv_unit_eval_eq_genVal`, `curry_covGrad_unit_eval_genVal`).  The whole
order-`≤2` envelope then reduces to a **single reusable frontier lemma**, the norm
bridge `‖(iteratedCovGrad gBase 0 2 j (metricCcTensor gBase h)).toSection x‖ =
√(normSq0S gBase x (j+2) (metricCovDeriv h gBase j x))`, which belongs upstream
(`CovGrad`/`Geometry`) and is proposed there rather than placed in this leaf.

Everything around the frontier composes from existing API: RS linearity (below),
`j ≥ 1` self-zero of the `metricCcTensor gBase gBase` tower (from `nabla_metric_zero`,
applied after the bridge), and the order-0 HS bound `≤ finrank·(Λ−1)` (Discharger 1's
operator bound plus the `normSq0S` Parseval expansion), pinning
`B(Λ) = finrank·(Λ−1) + 2Λ`. -/

/-- **Envelope-summand linearity split (Discharger 2 reduction).**  At every order
`j`, the iterated covariant gradient of the metric difference splits into the
difference of the two metric-realizing towers, because
`metricDifferenceCcTensor gBase g₀ = metricCcTensor gBase g₀ − metricCcTensor gBase gBase`.
This is the design-independent first assembly step of the brick-2a jet envelope: it
is needed whether the class-uniform curvature-jet hypothesis is discharged through the
upstream `metricCovDeriv` norm bridge or restated directly in the RS
`iteratedCovGrad` currency. -/
theorem metricDiff_iterCovGrad_sub (gBase g₀ : SmoothRiemannianMetric I M) (j : ℕ) :
    iteratedCovGrad gBase 0 2 j
        (metricDifferenceCcTensor (I := I) (M := M) gBase g₀) =
      iteratedCovGrad gBase 0 2 j (metricCcTensor (I := I) (M := M) gBase g₀) -
        iteratedCovGrad gBase 0 2 j (metricCcTensor (I := I) (M := M) gBase gBase) := by
  have h : metricDifferenceCcTensor (I := I) (M := M) gBase g₀ =
      metricCcTensor (I := I) (M := M) gBase g₀ -
        metricCcTensor (I := I) (M := M) gBase gBase := rfl
  rw [h, iteratedCovGrad_sub]

/-! ### Discharger 2 — the order-`≤2` jet envelope (session 9)

`normBridge` (`MetricCovDerivBridge.lean`) is now proved sorry-free, so the jet
envelope lands.  The `j = 0` term is the order-0 Hilbert–Schmidt norm of
`g₀ − gBase`, bounded by `n·(Λ−1)` (`n = finrank`) through a `normSq0S` Parseval
expansion of Discharger 1's operator bound on an orthonormal frame; the `j ≥ 1`
terms reduce, through `normBridge` and the self-vanishing of the `gBase`-tower
(`covNorm_self_succ`), to `metricCovDerivNorm j g₀ gBase x ≤ Λ` from
`MetricCovDerivOrderBoundOn`.  The two private helpers below re-derive the
fibre-norm ↔ `normSq0S`-of-unit-value bridge (private in `MetricCovDerivBridge`;
re-derived here since this leaf may not edit that file). -/

set_option linter.unusedSectionVars false in
/-- The `r = 0` index-lowering is unit-evaluation (local re-derivation of the
private `MetricCovDerivBridge.lowerAllUpper_zero_eq_unit`). -/
private lemma lowerAllUpper_zero_eq_unit'
    (gBase : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
    (W : SmoothCcTensor gBase 0 s) (w : Fin (0 + s) → TangentSpace I x) :
    lowerAllUpperIndices (I := I) (M := M) gBase 0 s x
        (TensorRSSpace.toModel
          (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from W.toSection x)) w =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from W.toSection x)
        (unitZeroSec (I := I) (M := M) x) (fun j : Fin s => w (Fin.natAdd 0 j)) := by
  rw [lowerAllUpperIndices_apply, separableFormAt_zero]
  rw [show (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ)) =
      Tensor0SSpace.toModel (unitZeroSec (I := I) (M := M) x) from rfl]
  rw [← toModel_tensorRS_apply (I := I) (M := M) 0 s x (W.toSection x)
    (unitZeroSec (I := I) (M := M) x)]
  rfl

/-- The `gBase`-Riemannian squared fibre norm of a smooth `(0, s)`-tensor section
equals the intrinsic `normSq0S` of its unit-value (local re-derivation of the
private `MetricCovDerivBridge.rfns_eq_normSq0S_unit`). -/
private lemma rfns_eq_normSq0S_unit'
    (gBase : SmoothRiemannianMetric I M) (s : ℕ) (x : M) (W : SmoothCcTensor gBase 0 s) :
    riemannianFiberNormSq (I := I) (M := M) gBase 0 s x (W.toSection x) =
      Tensor0SBundle.normSq0S (I := I) gBase x s
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from W.toSection x)
          (unitZeroSec (I := I) (M := M) x)) := by
  classical
  obtain ⟨basis, hON⟩ := exists_gOrthonormalBasis (I := I) gBase x
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) gBase 0 s x
    (W.toSection x)]
  rw [show tensorInnerPointwise (I := I) (M := M) gBase 0 s x
        (TensorRSSpace.toModel (W.toSection x)) (TensorRSSpace.toModel (W.toSection x)) =
      tensorInnerPointwise_0s (I := I) (M := M) (0 + s) gBase x
        (lowerAllUpperIndices (I := I) (M := M) gBase 0 s x
          (TensorRSSpace.toModel (W.toSection x)))
        (lowerAllUpperIndices (I := I) (M := M) gBase 0 s x
          (TensorRSSpace.toModel (W.toSection x))) from rfl]
  rw [tensorInnerPointwise_0s_eq_diag_sum_orthoFrame (I := I) (M := M) gBase x (0 + s)
    basis hON _ _]
  rw [Tensor0SBundle.normSq0S_identity_eq_sum_sq (I := I) gBase x s basis
    (metricInverseInBasis_of_orthonormal (I := I) gBase basis hON) _]
  symm
  refine Fintype.sum_equiv
    (Equiv.arrowCongr (finCongr (Nat.zero_add s).symm) (Equiv.refl _)) _ _ ?_
  intro slots
  rw [Tensor0SBundle.component0S_apply]
  rw [lowerAllUpper_zero_eq_unit' (I := I) gBase s x W]
  rw [sq]
  congr 1 <;>
    (congr 1; funext a;
     simp only [Equiv.arrowCongr_apply, Equiv.coe_refl, Function.comp_apply, id_eq];
     congr 1;
     apply Fin.ext;
     simp)

set_option linter.unusedSectionVars false in
/-- The intrinsic component of the unit-value of a `(0,2)`-tensor section against
a basis pair is exactly the extracted bilinear form on the two basis vectors. -/
private lemma component0S_unit_eq_ccBilin
    (gBase : SmoothRiemannianMetric I M) (S : SmoothCcTensor gBase 0 2) (x : M)
    (basis : Module.Basis (Fin (Module.finrank ℝ (TangentSpace I x))) ℝ (TangentSpace I x))
    (slots : Fin 2 → Fin (Module.finrank ℝ (TangentSpace I x))) :
    Tensor0SBundle.component0S (I := I) basis
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from S.toSection x)
          (unitZeroSec (I := I) (M := M) x)) slots =
      ccTensorBilin (I := I) gBase S x (basis (slots 0)) (basis (slots 1)) := by
  have hbil : ∀ u v : TangentSpace I x,
      ccTensorBilin (I := I) gBase S x u v =
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from S.toSection x)
          (unitZeroSec (I := I) (M := M) x) ![u, v] := by
    intro u v
    rw [ccTensorBilin_apply]
    rfl
  rw [Tensor0SBundle.component0S_apply, hbil (basis (slots 0)) (basis (slots 1))]
  congr 1
  funext k
  fin_cases k <;> rfl

set_option linter.unusedSectionVars false in
set_option synthInstance.maxHeartbeats 1600000 in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
/-- **Envelope term, order 0.**  The `gBase`-Riemannian fibre norm of the metric
difference `g₀ − gBase` (as a `(0,2)` cc-tensor) is at most `n·(Λ−1)`,
`n = finrank ℝ E`, by a `normSq0S` Parseval expansion of Discharger 1's operator
bound on a `gBase`-orthonormal frame. -/
theorem metricDiff_order0_bound (gBase g₀ : SmoothRiemannianMetric I M) {Λ : ℝ}
    (hΛ : 1 ≤ Λ)
    (hcomp : ∀ (x : M) (v : TangentSpace I x),
      Λ⁻¹ * gBase.inner x v v ≤ g₀.inner x v v ∧
        g₀.inner x v v ≤ Λ * gBase.inner x v v)
    (x : M) :
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 2 I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) gBase 0 2
    ‖((metricDifferenceCcTensor (I := I) (M := M) gBase g₀).toSection x :
        TensorRSSpace 0 2 I x)‖ ≤ (Module.finrank ℝ E : ℝ) * (Λ - 1) := by
  classical
  letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 2 I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) gBase 0 2
  obtain ⟨basis, hON⟩ := exists_gOrthonormalBasis (I := I) gBase x
  have hΛ1 : (0 : ℝ) ≤ Λ - 1 := by linarith
  -- norm = √ riemannianFiberNormSq = √ normSq0S(unit-value)
  rw [norm_toSection_eq_sqrt_riemannianFiberNormSq (I := I) (M := M) gBase 0 2 x
    (metricDifferenceCcTensor (I := I) (M := M) gBase g₀)]
  rw [rfns_eq_normSq0S_unit' (I := I) gBase 2 x
    (metricDifferenceCcTensor (I := I) (M := M) gBase g₀)]
  -- component bound: |component| = |g₀ - gBase on ON basis| ≤ Λ - 1
  have hcompbound : ∀ slots : Fin 2 → Fin (Module.finrank ℝ (TangentSpace I x)),
      |Tensor0SBundle.component0S (I := I) basis
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
              (metricDifferenceCcTensor (I := I) (M := M) gBase g₀).toSection x)
            (unitZeroSec (I := I) (M := M) x)) slots| ≤ Λ - 1 := by
    intro slots
    rw [component0S_unit_eq_ccBilin (I := I) gBase
      (metricDifferenceCcTensor (I := I) (M := M) gBase g₀) x basis slots]
    have heq : ccTensorBilin (I := I) gBase
          (metricDifferenceCcTensor (I := I) (M := M) gBase g₀) x
          (basis (slots 0)) (basis (slots 1)) =
        ccTensorBilinSymm (I := I) gBase
          (metricDifferenceCcTensor (I := I) (M := M) gBase g₀) x
          (basis (slots 0)) (basis (slots 1)) := by
      rw [metricDiff_ccBilin, metricDiff_ccBilinSymm]
    rw [heq]
    have hbound := metricDiff_gFibreOpBound (I := I) (M := M) gBase g₀ hΛ hcomp
      x (basis (slots 0)) (basis (slots 1))
    have h00 : gBase.inner x (basis (slots 0)) (basis (slots 0)) = 1 := by
      rw [hON (slots 0) (slots 0)]; simp
    have h11 : gBase.inner x (basis (slots 1)) (basis (slots 1)) = 1 := by
      rw [hON (slots 1) (slots 1)]; simp
    rw [h00, h11, Real.sqrt_one, mul_one, mul_one] at hbound
    exact hbound
  have hnormsq := Tensor0SBundle.normSq0S_le_card_of_component_bound (I := I) gBase x 2 basis
    (metricInverseInBasis_of_orthonormal (I := I) gBase basis hON)
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
        (metricDifferenceCcTensor (I := I) (M := M) gBase g₀).toSection x)
      (unitZeroSec (I := I) (M := M) x)) (Λ - 1) hΛ1 hcompbound
  -- card (Fin 2 → Fin n) = n²
  have hcard : (Fintype.card (Fin 2 → Fin (Module.finrank ℝ (TangentSpace I x))) : ℝ) =
      (Module.finrank ℝ E : ℝ) ^ 2 := by
    have hc : Fintype.card (Fin 2 → Fin (Module.finrank ℝ (TangentSpace I x))) =
        Module.finrank ℝ E ^ 2 := by
      change Fintype.card (Fin 2 → Fin (Module.finrank ℝ E)) = Module.finrank ℝ E ^ 2
      rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
    rw [hc]; push_cast; ring
  rw [hcard] at hnormsq
  -- √ normSq0S ≤ √ (n² (Λ-1)²) = n (Λ-1)
  calc Real.sqrt (Tensor0SBundle.normSq0S (I := I) gBase x 2
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
              (metricDifferenceCcTensor (I := I) (M := M) gBase g₀).toSection x)
            (unitZeroSec (I := I) (M := M) x)))
      ≤ Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 2 * (Λ - 1) ^ 2) := Real.sqrt_le_sqrt hnormsq
    _ = (Module.finrank ℝ E : ℝ) * (Λ - 1) := by
        rw [← mul_pow, Real.sqrt_sq (mul_nonneg (Nat.cast_nonneg _) hΛ1)]

set_option linter.unusedSectionVars false in
set_option synthInstance.maxHeartbeats 1600000 in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
/-- **Envelope term, order `a + 1 ≥ 1`.**  Through the linearity split
`metricDiff_iterCovGrad_sub`, the `metricCcTensor gBase gBase` half vanishes
(`normBridge` + `covNorm_self_succ`), leaving the `metricCcTensor gBase g₀` half,
whose fibre norm is `metricCovDerivNorm (a+1) g₀ gBase x ≤ Λ` by
`MetricCovDerivOrderBoundOn`. -/
theorem metricDiff_orderPos_bound (gBase g₀ : SmoothRiemannianMetric I M) {Λ : ℝ}
    (a : ℕ) (hjet : MetricCovDerivOrderBoundOn Set.univ (a + 1) g₀ gBase Λ) (x : M) :
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + (a + 1)) I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) gBase 0 (2 + (a + 1))
    ‖((iteratedCovGrad gBase 0 2 (a + 1)
        (metricDifferenceCcTensor (I := I) (M := M) gBase g₀)).toSection x :
        TensorRSSpace 0 (2 + (a + 1)) I x)‖ ≤ Λ := by
  letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + (a + 1)) I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) gBase 0 (2 + (a + 1))
  -- the gBase-tower half has zero norm
  have hBzero : ‖((iteratedCovGrad gBase 0 2 (a + 1)
        (metricCcTensor (I := I) (M := M) gBase gBase)).toSection x :
        TensorRSSpace 0 (2 + (a + 1)) I x)‖ = 0 := by
    rw [normBridge gBase gBase (a + 1) x]
    exact covNorm_self_succ gBase a x
  have hBsec : (iteratedCovGrad gBase 0 2 (a + 1)
      (metricCcTensor (I := I) (M := M) gBase gBase)).toSection x = 0 :=
    norm_eq_zero.mp hBzero
  -- split via linearity and drop the zero half
  have hsplit : (iteratedCovGrad gBase 0 2 (a + 1)
        (metricDifferenceCcTensor (I := I) (M := M) gBase g₀)).toSection x =
      (iteratedCovGrad gBase 0 2 (a + 1)
        (metricCcTensor (I := I) (M := M) gBase g₀)).toSection x := by
    rw [metricDiff_iterCovGrad_sub]
    simp only [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply, hBsec,
      sub_zero]
  rw [hsplit, normBridge g₀ gBase (a + 1) x]
  exact hjet x (Set.mem_univ x)

set_option linter.unusedSectionVars false in
set_option synthInstance.maxHeartbeats 1600000 in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
/-- **The order-`≤2` jet envelope `B(Λ) = n·(Λ−1) + 2Λ`.**  This is the metric-jet
envelope the order-0 Riemann *difference* asset consumes at role base = `gBase`,
`P = metricDifferenceCcTensor gBase g₀`. -/
theorem metricDiff_jetEnvelope (gBase g₀ : SmoothRiemannianMetric I M) {Λ : ℝ}
    (hΛ : 1 ≤ Λ)
    (hcomp : ∀ (x : M) (v : TangentSpace I x),
      Λ⁻¹ * gBase.inner x v v ≤ g₀.inner x v v ∧
        g₀.inner x v v ≤ Λ * gBase.inner x v v)
    (hjet1 : MetricCovDerivOrderBoundOn Set.univ 1 g₀ gBase Λ)
    (hjet2 : MetricCovDerivOrderBoundOn Set.univ 2 g₀ gBase Λ)
    (x : M) :
    (∑ j ∈ Finset.range 3,
        (letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + j) I b) :=
          Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) gBase 0 (2 + j)
        ‖((iteratedCovGrad gBase 0 2 j
            (metricDifferenceCcTensor (I := I) (M := M) gBase g₀)).toSection x :
            TensorRSSpace 0 (2 + j) I x)‖)) ≤ (Module.finrank ℝ E : ℝ) * (Λ - 1) + 2 * Λ := by
  refine le_trans (Finset.sum_le_sum
    (g := fun j => if j = 0 then (Module.finrank ℝ E : ℝ) * (Λ - 1) else Λ) ?_)
    (le_of_eq ?_)
  · intro j hj
    fin_cases hj
    · simpa only [iteratedCovGrad_zero] using
        metricDiff_order0_bound (I := I) (M := M) gBase g₀ hΛ hcomp x
    · simpa only [iteratedCovGrad_zero] using
        metricDiff_orderPos_bound (I := I) (M := M) gBase g₀ 0 hjet1 x
    · simpa only [iteratedCovGrad_zero] using
        metricDiff_orderPos_bound (I := I) (M := M) gBase g₀ 1 hjet2 x
  · rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_zero, zero_add, if_pos (rfl : (0 : ℕ) = 0),
      if_neg (by norm_num : ¬(1 : ℕ) = 0), if_neg (by norm_num : ¬(2 : ℕ) = 0)]
    ring

/-- **Order-0 curvature sup, single link (`Λ < 2` regime), from comparability and
jets alone.**

Under `Λ`-comparability of `g₀` with `gBase` (`1 ≤ Λ < 2`) and the class metric-jet
bounds `MetricCovDerivOrderBoundOn` at orders `1` and `2`, the absolute Riemann
operator of `g₀` is bounded in the `g₀` inner product by `F²` with an explicit
`F = Λ² · (Cd + √Kbase)`, where `Cd` is the order-0 Riemann *difference* constant
of `exists_riemannOp_LeviCivita_difference_gQuadratic_le_of_jetEnvelope` at envelope
`B = n·(Λ−1) + 2Λ` and operator radius `δ₀ = Λ − 1 < 1`, and `Kbase` is the fixed
`gBase` curvature constant.  This discharges brick 2a-0; the full class `Λ ≥ 1`
follows by `convexComb` telescoping (2a-tel). -/
theorem unifCurvatureSup_singleLink
    (gBase g₀ : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 1 ≤ Λ) (hΛ2 : Λ < 2)
    (hcomp : ∀ (x : M) (v : TangentSpace I x),
      Λ⁻¹ * gBase.inner x v v ≤ g₀.inner x v v ∧
        g₀.inner x v v ≤ Λ * gBase.inner x v v)
    (hjet1 : MetricCovDerivOrderBoundOn Set.univ 1 g₀ gBase Λ)
    (hjet2 : MetricCovDerivOrderBoundOn Set.univ 2 g₀ gBase Λ) :
    ∃ F : ℝ, 0 ≤ F ∧
      ∀ (x : M) (v w u : TangentSpace I x),
        g₀.inner x
            (riemannOp (cov := LeviCivita (I := I) g₀) x v w u)
            (riemannOp (cov := LeviCivita (I := I) g₀) x v w u) ≤
          F ^ 2 * g₀.inner x v v * g₀.inner x w w * g₀.inner x u u := by
  classical
  have hΛ1 : (0 : ℝ) ≤ Λ - 1 := by linarith
  have hB0 : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) * (Λ - 1) + 2 * Λ :=
    add_nonneg (mul_nonneg (Nat.cast_nonneg _) hΛ1) (by linarith)
  obtain ⟨Cd, hCd0, hCd⟩ :=
    exists_riemannOp_LeviCivita_difference_gQuadratic_le_of_jetEnvelope (I := I) (M := M)
      gBase (δ₀ := Λ - 1) (by linarith : Λ - 1 < 1)
      ((Module.finrank ℝ E : ℝ) * (Λ - 1) + 2 * Λ) hB0
  have hdiff : ∀ (x : M) (v w u : TangentSpace I x),
      gBase.inner x
          (riemannOp (cov := LeviCivita (I := I) g₀) x v w u -
            riemannOp (cov := LeviCivita (I := I) gBase) x v w u)
          (riemannOp (cov := LeviCivita (I := I) g₀) x v w u -
            riemannOp (cov := LeviCivita (I := I) gBase) x v w u) ≤
        Cd ^ 2 * gBase.inner x v v * gBase.inner x w w * gBase.inner x u u := by
    intro x v w u
    exact hCd g₀ (metricDifferenceCcTensor (I := I) (M := M) gBase g₀) (δ := Λ - 1)
      (le_of_eq (max_eq_left hΛ1).symm)
      (metricDiff_gFibreOpBound (I := I) (M := M) gBase g₀ hΛ hcomp)
      (fun x v w => metricDiff_tie (I := I) (M := M) gBase g₀ x v w) x
      (metricDiff_jetEnvelope (I := I) (M := M) gBase g₀ hΛ hcomp hjet1 hjet2 x) v w u
  exact unifCurvatureSup_singleLink_of_diff (I := I) (M := M) gBase g₀ hΛ hcomp hCd0 hdiff

/-! ### 2a-tel telescoping link lemmas (session 10)

The linear interpolation path `g_t = t·g₀ + (1−t)·gBase` (`convexCombPath`, `t = 0` at
`gBase`, `t = 1` at `g₀`) supplies the `(a)` link data of the full-class `Λ ≥ 1`
telescoping (see `UnifCurvatureJetBound.md`, session 10):

* `convexCombPath_comparable` — **(a)(i)** consecutive path metrics are mutually
  comparable, with the explicit modulus `μ = |t − s|·Λ(Λ−1)`:
  `|g_t(v,v) − g_s(v,v)| ≤ μ·g_s(v,v)`.  (Two-sided `(1 ± μ)` comparability, hence
  link constant `Λ_link = (1−μ)⁻¹ < 2` when `μ < ½`.)
* `convexCombPath_jetBound` — **(a)(ii)** metric-jet inheritance in the **fixed-`gBase`**
  currency: `∇^{gBase,a+1} g_t = t·∇^{gBase,a+1} g₀` (the `gBase`-tower self-vanishes),
  so the class bound `MetricCovDerivOrderBoundOn (a+1) g₀ gBase Λ` transfers to `g_t`.

These discharge the FIRST link (base `= gBase`) and are the convex-combination inputs the
telescoping bridge consumes.  The composition to the full class is NOT closed here: it
needs the metric jets against the **moving** base `g_{t_k}` (`k ≥ 1`), i.e. the order-`≤2`
change-of-reference-connection currency, whose order-`2` assembly is a declared frontier
(`UnifCovSumCross.lean`, active lane) plus the ungated `∇connDiff` bound — see
`UnifCurvatureJetBound.md`. -/

/-- The constant-weight convex-combination path `g_t = t·g₀ + (1−t)·gBase`. -/
noncomputable def convexCombPath (g₀ gBase : SmoothRiemannianMetric I M) (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) : SmoothRiemannianMetric I M :=
  g₀.convexComb gBase (fun _ => t) contMDiff_const (fun _ => ht)

set_option linter.unusedSectionVars false in
/-- The fibre inner product of the convex-combination path is the convex combination of
the two inner products. -/
theorem convexCombPath_inner (g₀ gBase : SmoothRiemannianMetric I M) (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (x : M) (v w : TangentSpace I x) :
    (convexCombPath g₀ gBase t ht).inner x v w =
      t • g₀.inner x v w + (1 - t) • gBase.inner x v w :=
  convexComb_inner g₀ gBase (fun _ => t) contMDiff_const (fun _ => ht) x v w

set_option linter.unusedSectionVars false in
/-- **(a)(i) Link comparability.**  For the interpolation path `g_t = t·g₀ + (1−t)·gBase`,
consecutive metrics are mutually comparable with modulus `μ = |t − s|·Λ(Λ−1)`:
`|g_t(v,v) − g_s(v,v)| ≤ μ·g_s(v,v)`.  With `μ < 1` this gives the two-sided bound
`(1−μ)·g_s ≤ g_t ≤ (1+μ)·g_s`, i.e. `Λ_link`-comparability with `Λ_link = (1−μ)⁻¹`. -/
theorem convexCombPath_comparable
    (g₀ gBase : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 1 ≤ Λ)
    (hcomp : ∀ (x : M) (v : TangentSpace I x),
      Λ⁻¹ * gBase.inner x v v ≤ g₀.inner x v v ∧
        g₀.inner x v v ≤ Λ * gBase.inner x v v)
    {s t : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (x : M) (v : TangentSpace I x) :
    |(convexCombPath g₀ gBase t ht).inner x v v -
        (convexCombPath g₀ gBase s hs).inner x v v| ≤
      |t - s| * (Λ * (Λ - 1)) * (convexCombPath g₀ gBase s hs).inner x v v := by
  have hΛ0 : (0 : ℝ) < Λ := lt_of_lt_of_le one_pos hΛ
  rw [convexCombPath_inner, convexCombPath_inner]
  simp only [smul_eq_mul]
  set a := g₀.inner x v v with ha_def
  set b := gBase.inner x v v with hb_def
  have hb0 : 0 ≤ b := metric_inner_self_nonneg (I := I) (M := M) gBase x v
  have ha0 : 0 ≤ a := metric_inner_self_nonneg (I := I) (M := M) g₀ x v
  obtain ⟨hlo, hhi⟩ := hcomp x v
  -- clear the inverse from the lower comparability: `b ≤ Λ · a`
  have hlo' : b ≤ Λ * a := by
    have h := mul_le_mul_of_nonneg_left hlo hΛ0.le
    rwa [← mul_assoc, mul_inv_cancel₀ hΛ0.ne', one_mul] at h
  -- `|a − b| ≤ (Λ − 1)·b`
  have hab : |a - b| ≤ (Λ - 1) * b := by
    rw [abs_le]
    refine ⟨?_, ?_⟩
    · rcases le_total Λ 2 with hle | hge
      · have hp2 : (0 : ℝ) ≤ (2 - Λ) * (Λ * a - b) :=
          mul_nonneg (by linarith) (by linarith [hlo'])
        nlinarith [mul_nonneg (sq_nonneg (Λ - 1)) ha0, hp2]
      · nlinarith [ha0, mul_nonneg (by linarith : (0 : ℝ) ≤ Λ - 2) hb0]
    · nlinarith [hhi, hb0]
  -- `b ≤ Λ · g_s`
  obtain ⟨hs0, hs1⟩ := hs
  have hgs : b ≤ Λ * (s * a + (1 - s) * b) := by
    have hsb : s * b ≤ s * (Λ * a) := mul_le_mul_of_nonneg_left hlo' hs0
    have hbb : b ≤ Λ * b := by nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ Λ - 1) hb0]
    have h1sb : (1 - s) * b ≤ (1 - s) * (Λ * b) :=
      mul_le_mul_of_nonneg_left hbb (by linarith)
    nlinarith [hsb, h1sb]
  -- assemble
  have hts : 0 ≤ |t - s| := abs_nonneg _
  have hΛ1 : (0 : ℝ) ≤ Λ - 1 := by linarith
  have hGdiff : t * a + (1 - t) * b - (s * a + (1 - s) * b) = (t - s) * (a - b) := by ring
  rw [hGdiff, abs_mul]
  calc |t - s| * |a - b|
      ≤ |t - s| * ((Λ - 1) * b) := mul_le_mul_of_nonneg_left hab hts
    _ ≤ |t - s| * ((Λ - 1) * (Λ * (s * a + (1 - s) * b))) := by
        refine mul_le_mul_of_nonneg_left ?_ hts
        exact mul_le_mul_of_nonneg_left hgs hΛ1
    _ = |t - s| * (Λ * (Λ - 1)) * (s * a + (1 - s) * b) := by ring

/-- The metric tensor field of the convex-combination path is the convex combination of the
two metric tensor fields (linearity of `metricTensorField` in the metric argument). -/
theorem metricTensorField_convexCombPath (g₀ gBase : SmoothRiemannianMetric I M) (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    metricTensorField (convexCombPath g₀ gBase t ht) =
      t • metricTensorField g₀ + (1 - t) • metricTensorField gBase := by
  refine DFunLike.ext _ _ (fun x => ?_)
  refine DFunLike.ext _ _ (fun v => ?_)
  simp only [ContMDiffSection.coe_add, ContMDiffSection.coe_smul, Pi.add_apply, Pi.smul_apply,
    Tensor0SSpace.add_apply, Tensor0SSpace.smul_apply, metricTensorField_apply,
    convexCombPath_inner, smul_eq_mul]

/-- Linearity of the fixed-`gBase` covariant metric derivative in the metric argument, along
the convex-combination path: `∇^{gBase,a} g_t = t·∇^{gBase,a} g₀ + (1−t)·∇^{gBase,a} gBase`. -/
theorem metricCovDeriv_convexCombPath (g₀ gBase : SmoothRiemannianMetric I M) (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (a : ℕ) :
    metricCovDeriv (convexCombPath g₀ gBase t ht) gBase a =
      t • metricCovDeriv g₀ gBase a + (1 - t) • metricCovDeriv gBase gBase a := by
  rw [metricCovDeriv_eq_covDerivOfField, metricTensorField_convexCombPath,
    covDerivOfField_add, covDerivOfField_smul, covDerivOfField_smul,
    ← metricCovDeriv_eq_covDerivOfField, ← metricCovDeriv_eq_covDerivOfField]

/-- At every order `a + 1 ≥ 1` the `gBase`-self derivative vanishes (metric compatibility),
so the path derivative is simply `t·∇^{gBase,a+1} g₀`. -/
theorem metricCovDeriv_convexCombPath_succ (g₀ gBase : SmoothRiemannianMetric I M) (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (a : ℕ) :
    metricCovDeriv (convexCombPath g₀ gBase t ht) gBase (a + 1) =
      t • metricCovDeriv g₀ gBase (a + 1) := by
  rw [metricCovDeriv_convexCombPath, covDeriv_self_succ gBase a, smul_zero, add_zero]

set_option linter.unusedSectionVars false in
/-- **(a)(ii) Link jet inheritance (fixed-`gBase` currency).**  A class metric-jet bound
`MetricCovDerivOrderBoundOn (a+1) g₀ gBase Λ` transfers verbatim to every path metric `g_t`:
`MetricCovDerivOrderBoundOn (a+1) g_t gBase Λ`, since `‖∇^{gBase,a+1} g_t‖ = t·‖∇^{gBase,a+1}
g₀‖ ≤ Λ` for `t ∈ [0,1]`.  This exactly discharges the FIRST telescoping link's jets. -/
theorem convexCombPath_jetBound (g₀ gBase : SmoothRiemannianMetric I M) {Λ : ℝ}
    (hΛ0 : 0 ≤ Λ) (a : ℕ) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hjet : MetricCovDerivOrderBoundOn Set.univ (a + 1) g₀ gBase Λ) :
    MetricCovDerivOrderBoundOn Set.univ (a + 1) (convexCombPath g₀ gBase t ht) gBase Λ := by
  obtain ⟨ht0, ht1⟩ := ht
  intro x _
  have hfield : metricCovDeriv (convexCombPath g₀ gBase t ⟨ht0, ht1⟩) gBase (a + 1) x =
      t • metricCovDeriv g₀ gBase (a + 1) x := by
    rw [metricCovDeriv_convexCombPath_succ]
    simp only [ContMDiffSection.coe_smul, Pi.smul_apply]
  have hnorm : metricCovDerivNorm (a + 1) (convexCombPath g₀ gBase t ⟨ht0, ht1⟩) gBase x =
      |t| * metricCovDerivNorm (a + 1) g₀ gBase x := by
    unfold metricCovDerivNorm
    rw [hfield, sqrt_normSq0S_smul]
  rw [hnorm, abs_of_nonneg ht0]
  have hjx := hjet x (Set.mem_univ x)
  calc t * metricCovDerivNorm (a + 1) g₀ gBase x
      ≤ t * Λ := mul_le_mul_of_nonneg_left hjx ht0
    _ ≤ 1 * Λ := mul_le_mul_of_nonneg_right ht1 hΛ0
    _ = Λ := one_mul _

end RicciFlow
end PDE
end DifferentialGeometry
