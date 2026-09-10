import DifferentialGeometry.Analysis.ODE.Flow.Planar.SmoothGlobalFlow
import DifferentialGeometry.Analysis.Calculus.Inverse.TransverseImmersion
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Dynamics.Flow

noncomputable section
open Set Metric
open scoped ContDiff Topology

namespace Poincare.Analysis

theorem exists_smooth_planar_flowBox
    (φ : _root_.Flow ℝ ℂ) {v : ℂ → ℂ} (hv : ContDiff ℝ ∞ v)
    (hderiv : ∀ x t, HasDerivAt (fun s ↦ φ s x) (v (φ t x)) t)
    {x : ℂ} (hx : v x ≠ 0) :
    ∃ ε > 0, ∃ e : OpenPartialHomeomorph (ℝ × ℝ) ℂ,
      e.source = Ioo (-ε) ε ×ˢ Ioo (-ε) ε ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      ∀ p, e p = φ p.2 (x + p.1 • (Complex.I * v x)) := by
  let w := Complex.I * v x
  have hw : w ≠ 0 := mul_ne_zero Complex.I_ne_zero hx
  let ι : ℝ → ℂ := fun u ↦ x + u • w
  have hι : ContDiff ℝ ∞ ι := by fun_prop
  have hιd : HasDerivAt ι w 0 := by
    change HasDerivAt (fun u : ℝ ↦ x + u • w) w 0
    convert ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add x using 1 <;>
      first | rfl | simp only [one_smul]
  have hL : fderiv ℝ ι 0 = ContinuousLinearMap.toSpanSingleton ℝ w := hιd.hasFDerivAt.fderiv
  have hinj : Function.Injective (fderiv ℝ ι 0) := by
    rw [hL]
    exact smul_left_injective ℝ hw
  have htrans : v x ∉ range (fderiv ℝ ι 0) := by
    rw [hL]
    rintro ⟨a, ha⟩
    have he : (a : ℂ) * Complex.I = 1 := mul_right_cancel₀ hx (by
      simpa only [ContinuousLinearMap.toSpanSingleton_apply, w, Complex.real_smul,
        mul_assoc, one_mul] using ha)
    have hre := congrArg Complex.re he
    norm_num at hre
  have hflow : ContDiff ℝ ∞ (fun q : ℂ × ℝ ↦ φ q.2 q.1) :=
    contDiff_globalIntegralCurveFamily hv (fun y ↦ φ.map_zero_apply y) hderiv
  let f : ℝ × ℝ → ℂ := fun p ↦ φ p.2 (ι p.1)
  have hf : ContDiff ℝ ∞ f := hflow.comp ((hι.comp contDiff_fst).prodMk contDiff_snd)
  have htime : deriv (fun t ↦ f (0, t)) 0 = v x := by
    simpa only [f, ι, zero_smul, add_zero, φ.map_zero_apply] using (hderiv x 0).deriv
  obtain ⟨e, hzero, _, he, heinv, heq⟩ := exists_localInverse_of_transverse_family
    (ι := ι) hf.contDiffOn isOpen_univ (mem_univ _)
    (fun y _ ↦ φ.map_zero_apply (ι y)) hinj (by simp [Complex.finrank_real_complex])
    (by rwa [htime])
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (e.open_source.mem_nhds hzero)
  let R : Set (ℝ × ℝ) := Ioo (-ε) ε ×ˢ Ioo (-ε) ε
  have hR : IsOpen R := isOpen_Ioo.prod isOpen_Ioo
  have hsub : R ⊆ e.source := by
    intro p hp
    apply hball
    simpa only [R, mem_prod, mem_Ioo, mem_ball, Prod.dist_eq, Real.dist_eq,
      sub_zero, max_lt_iff, abs_lt] using hp
  let d := e.restrOpen R hR
  refine ⟨ε, hε, d, ?_, he.mono inter_subset_left, heinv.mono inter_subset_left, heq⟩
  change e.source ∩ R = R
  exact inter_eq_right.mpr hsub

end Poincare.Analysis
