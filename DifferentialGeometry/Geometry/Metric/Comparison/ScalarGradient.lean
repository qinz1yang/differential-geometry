import DifferentialGeometry.Geometry.Metric.Comparison.ScalarBarrier
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Inv

set_option autoImplicit false
noncomputable section
open Bundle Set Manifold
open scoped Manifold ContDiff
namespace DifferentialGeometry.Geometry.Metric
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private theorem abs_mvfderiv_inv_sqrt_le
    (g : SmoothRiemannianMetric I M) {f : M → ℝ} {x : M} {C : ℝ}
    (hf : MDifferentiableAt I 𝓘(ℝ) f x) (hpos : 0 < f x)
    (v : TangentSpace I x)
    (hbound : |mvfderiv I f x v| ≤ C * f x * Real.sqrt (f x) *
      Real.sqrt (g.inner x v v)) :
    |mvfderiv I (fun y => (Real.sqrt (f y))⁻¹) x v| ≤
      (C / 2) * Real.sqrt (g.inner x v v) := by
  have hspos : 0 < Real.sqrt (f x) := Real.sqrt_pos.mpr hpos
  have hsquare : Real.sqrt (f x) ^ 2 = f x := Real.sq_sqrt hpos.le
  have hconst : -(1 / (2 * Real.sqrt (f x))) / Real.sqrt (f x) ^ 2 =
      -(1 / (2 * (f x * Real.sqrt (f x)))) := by
    rw [hsquare]
    field_simp
  have hd : HasDerivAt (fun r : ℝ => (Real.sqrt r)⁻¹)
      (-(1 / (2 * (f x * Real.sqrt (f x))))) (f x) :=
    ((Real.hasDerivAt_sqrt hpos.ne').inv hspos.ne').congr_deriv hconst
  have hmf : HasMFDerivAt I 𝓘(ℝ) (fun y => (Real.sqrt (f y))⁻¹) x
      (-(1 / (2 * (f x * Real.sqrt (f x)))) •
        (mfderiv I 𝓘(ℝ) f x : TangentSpace I x →L[ℝ] ℝ)) := by
    refine (hd.hasFDerivAt.hasMFDerivAt.comp x hf.hasMFDerivAt).congr_mfderiv ?_
    ext w
    change (show ℝ from mfderiv I 𝓘(ℝ) f x w) *
      (-(1 / (2 * (f x * Real.sqrt (f x))))) =
        (-(1 / (2 * (f x * Real.sqrt (f x))))) *
          (show ℝ from mfderiv I 𝓘(ℝ) f x w)
    exact mul_comm _ _
  have hval : mvfderiv I (fun y => (Real.sqrt (f y))⁻¹) x v =
      -(1 / (2 * (f x * Real.sqrt (f x)))) * mvfderiv I f x v :=
    DFunLike.congr_fun hmf.mfderiv v
  have hden : 0 < 2 * (f x * Real.sqrt (f x)) := by positivity
  rw [hval, abs_mul, abs_neg, abs_of_pos (one_div_pos.mpr hden),
    div_mul_eq_mul_div, one_mul, div_le_iff₀ hden]
  calc
    |mvfderiv I f x v| ≤ C * f x * Real.sqrt (f x) * Real.sqrt (g.inner x v v) := hbound
    _ = C / 2 * Real.sqrt (g.inner x v v) * (2 * (f x * Real.sqrt (f x))) := by ring

theorem riemannianEDistOf_ball_subset_superlevel_of_gradient_bound
    (g : SmoothRiemannianMetric I M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ) 1 f) {C L r : ℝ} {x : M}
    (hC : 0 ≤ C) (hL : 0 < L) (hx : L < f x)
    (hgrad : ∀ z, L < f z → ∀ v : TangentSpace I z,
      |mvfderiv I f z v| ≤ C * f z * Real.sqrt (f z) * Real.sqrt (g.inner z v v))
    (hr : C / 2 * r ≤ (Real.sqrt L)⁻¹ - (Real.sqrt (f x))⁻¹) :
    {y : M | riemannianEDistOf g x y < ENNReal.ofReal r} ⊆ {y | L < f y} := by
  let A : Set M := {z | L < f z}
  let V : Set M := {z | 0 < f z}
  let F : M → ℝ := fun z => (Real.sqrt (f z))⁻¹
  have hA : IsOpen A := isOpen_lt continuous_const hf.continuous
  have hV : IsOpen V := isOpen_lt continuous_const hf.continuous
  have hAV : closure A ⊆ V := by
    have hsub : closure A ⊆ {z | L ≤ f z} :=
      closure_minimal (fun z (hz : L < f z) => hz.le)
        (isClosed_le continuous_const hf.continuous)
    intro z hz
    exact hL.trans_le (hsub hz)
  have hF : ContMDiffOn I 𝓘(ℝ) 1 F V := by
    intro z hz
    have hz' : 0 < f z := hz
    have houter : ContDiffAt ℝ 1 (fun u : ℝ => (Real.sqrt u)⁻¹) (f z) :=
      (Real.contDiffAt_sqrt hz'.ne').inv (Real.sqrt_pos.mpr hz').ne'
    exact (houter.comp_contMDiffAt (x := z) (hf z)).contMDiffWithinAt
  have hd : 0 < (Real.sqrt L)⁻¹ - (Real.sqrt (f x))⁻¹ := by
    apply sub_pos.mpr
    exact (inv_lt_inv₀ (Real.sqrt_pos.mpr (hL.trans hx)) (Real.sqrt_pos.mpr hL)).mpr
      (Real.sqrt_lt_sqrt hL.le hx)
  have hfront (z : M) (hz : z ∈ frontier A) :
      (Real.sqrt L)⁻¹ - (Real.sqrt (f x))⁻¹ ≤ |F z - F x| := by
    have hboundary := hf.continuous.frontier_preimage_subset (Ioi L) hz
    have heq : f z = L := by
      simpa only [frontier_Ioi, mem_preimage, mem_singleton_iff] using hboundary
    change _ ≤ |(Real.sqrt (f z))⁻¹ - (Real.sqrt (f x))⁻¹|
    rw [heq, abs_of_pos hd]
  have h := riemannianEDistOf_ball_subset_of_frontier_gap g hV hAV F hF
    (⟨C / 2, by positivity⟩ : NNReal) (fun z hz v => by
      have hzA : L < f z := (show z ∈ A from interior_subset hz)
      exact abs_mvfderiv_inv_sqrt_le g ((hf z).mdifferentiableAt one_ne_zero)
        (hL.trans hzA) v (hgrad z hzA v))
    (by rwa [hA.interior_eq]) hd hfront hr
  simpa only [hA.interior_eq] using h

private theorem scalar_lower_barrier_bounds {Q C R : ℝ}
    (hQ : 0 < Q) (hC : 0 ≤ C) (hR : 0 ≤ R) :
    0 < Q / (2 + C * R) ^ 2 ∧
      Q / (2 + C * R) ^ 2 < Q ∧
      R / Real.sqrt Q < (R + 1 / (C + 1)) / Real.sqrt Q ∧
      Real.sqrt (Q / (2 + C * R) ^ 2) = Real.sqrt Q / (2 + C * R) ∧
      (C / 2) * ((R + 1 / (C + 1)) / Real.sqrt Q) ≤
        (Real.sqrt (Q / (2 + C * R) ^ 2))⁻¹ - (Real.sqrt Q)⁻¹ := by
  have hs : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQ
  have hCR : 0 ≤ C * R := mul_nonneg hC hR
  have hden : 0 < 2 + C * R := by positivity
  have hC1 : 0 < C + 1 := by positivity
  have hsq : Real.sqrt (Q / (2 + C * R) ^ 2) =
      Real.sqrt Q / (2 + C * R) := by
    rw [Real.sqrt_div hQ.le, Real.sqrt_sq hden.le]
  refine ⟨by positivity, div_lt_self hQ ?_, ?_, hsq, ?_⟩
  · nlinarith [sq_nonneg (C * R)]
  · exact (div_lt_div_iff_of_pos_right hs).mpr
      (lt_add_of_pos_right R (one_div_pos.mpr hC1))
  · rw [hsq, inv_div, ← one_div (Real.sqrt Q), ← sub_div]
    rw [← mul_div_assoc]
    apply (div_le_div_iff_of_pos_right hs).mpr
    have hfrac : C * (1 / (C + 1)) ≤ 1 := by
      rw [mul_one_div, div_le_iff₀ hC1]
      linarith
    nlinarith

theorem lower_bound_on_closed_ball_of_threshold_gradient_bound
    (g : SmoothRiemannianMetric I M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ) 1 f) {C Q q R : ℝ} {x y : M}
    (hC : 0 ≤ C) (hQ : 0 < Q) (hR : 0 ≤ R) (hq : q ≤ Q / (2 + C * R) ^ 2)
    (hgrad : ∀ z, q < f z → ∀ v : TangentSpace I z,
      |mvfderiv I f z v| ≤ C * f z * Real.sqrt (f z) * Real.sqrt (g.inner z v v))
    (hx : f x = Q)
    (hy : riemannianEDistOf g x y ≤ ENNReal.ofReal (R / Real.sqrt Q)) :
    Q / (2 + C * R) ^ 2 < f y := by
  obtain ⟨hL, hLQ, hrad, _, hmargin⟩ := scalar_lower_barrier_bounds hQ hC hR
  have hbound := riemannianEDistOf_ball_subset_superlevel_of_gradient_bound g hf
    (x := x) (r := (R + 1 / (C + 1)) / Real.sqrt Q) hC hL
    (by simpa [hx] using hLQ) (fun z hz v => hgrad z (hq.trans_lt hz) v)
    (by simpa [hx] using hmargin)
  apply hbound
  apply hy.trans_lt
  exact ENNReal.ofReal_lt_ofReal_iff (by positivity) |>.mpr hrad

end DifferentialGeometry.Geometry.Metric
