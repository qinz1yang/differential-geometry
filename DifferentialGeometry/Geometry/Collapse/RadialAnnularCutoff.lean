import DifferentialGeometry.Analysis.Calculus.AnnularCutoff
import DifferentialGeometry.Geometry.Operator.Gradient.Basic
import DifferentialGeometry.Geometry.Operator.Scalar.Calculus
import DifferentialGeometry.Geometry.Metric.PointwiseInner.Bounds

/-!
# LC31: the compact annular cutoff of a radial function (unconditional tier)

Blueprint 207A, LC31 (`thm:collapse-eventual-radial-cutoff`, A:21294–21348). Given a radial
function `η` with the LC30 output properties used by the blueprint's second paragraph (continuous,
smooth on an open set containing `η⁻¹[1/5, 9/10]`, `|η - d_p| < e`, `‖∇η‖ ≤ 1 + ε` on that
band), the composition `ζ = Φ ∘ η` with the scalar cutoff `Φ` of `AnnularCutoff.lean` is globally
smooth, valued in `[0, 1]`, equal to one where `3/10 ≤ η ≤ 4/5`, supported in
`{1/5 - e < d_p < 9/10 + e}` (compactly, on a proper space), and `‖∇ζ‖ ≤ L_Φ (1 + ε)`.

The eventual choice of the scale `r_p^0` and the curvature transfer of LC31's first paragraph need
the standing sequence (LC24); the radial function itself needs LC28 through LC30. This file is the
part that is independent of both.
-/

set_option autoImplicit false

noncomputable section
open Set Filter
open scoped Topology ContDiff Manifold
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Analysis.Calculus

namespace DifferentialGeometry.Geometry.Collapse

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- LC31, unconditional tier: `ζ = Φ ∘ η` is smooth, `[0,1]`-valued, one on
`η⁻¹[3/10, 4/5]`, topologically supported in `{1/5 - e < d_p < 9/10 + e}`, and
`‖∇ζ‖_g ≤ L (1 + ε)` everywhere, where `L` bounds `|Φ'|`. -/
theorem annularCutoff_comp_radial {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hrange : ∀ t, φ t ∈ Icc (0 : ℝ) 1) (hone : ∀ t, t ≤ 0 → φ t = 1)
    (hzero : ∀ t, 1 ≤ t → φ t = 0) (g : SmoothRiemannianMetric I M) (p : M) {η : M → ℝ}
    {O : Set M} {ε e L : ℝ} (hε : 0 ≤ ε) (hηc : Continuous η) (hO : IsOpen O)
    (hηO : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ η O) (hband : η ⁻¹' Icc (1 / 5 : ℝ) (9 / 10) ⊆ O)
    (hclose : ∀ x, |η x - dist x p| < e)
    (hgrad : ∀ q ∈ η ⁻¹' Icc (1 / 5 : ℝ) (9 / 10),
      Real.sqrt (g.inner q (gradFun g η q) (gradFun g η q)) ≤ 1 + ε)
    (hL : ∀ t, |deriv (annularCutoff φ) t| ≤ L) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x => annularCutoff φ (η x)) ∧
    (∀ x, annularCutoff φ (η x) ∈ Icc (0 : ℝ) 1) ∧
    (∀ x, η x ∈ Icc (3 / 10 : ℝ) (4 / 5) → annularCutoff φ (η x) = 1) ∧
    tsupport (fun x => annularCutoff φ (η x)) ⊆
      {x : M | 1 / 5 - e < dist x p ∧ dist x p < 9 / 10 + e} ∧
    ∀ q, Real.sqrt (g.inner q (gradFun g (fun x => annularCutoff φ (η x)) q)
      (gradFun g (fun x => annularCutoff φ (η x)) q)) ≤ L * (1 + ε) := by
  have hΦ := annularCutoff_contDiff hφ
  have hclosed : IsClosed (η ⁻¹' Icc (1 / 5 : ℝ) (9 / 10)) := isClosed_Icc.preimage hηc
  -- off the band, `ζ` vanishes on a neighbourhood
  have hlocal (x : M) (hx : η x ∉ Icc (1 / 5 : ℝ) (9 / 10)) :
      (fun y => annularCutoff φ (η y)) =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
    filter_upwards [hclosed.isOpen_compl.mem_nhds hx] with y hy
    exact annularCutoff_eq_zero_of_not_mem hzero fun h => hy (Ioo_subset_Icc_self h)
  have hL0 : 0 ≤ L := (abs_nonneg _).trans (hL 0)
  refine ⟨fun x => ?_, fun x => annularCutoff_mem_Icc hrange (η x),
    fun x hx => annularCutoff_eq_one hone hx, ?_, fun q => ?_⟩
  · by_cases hx : η x ∈ Icc (1 / 5 : ℝ) (9 / 10)
    · exact hΦ.contMDiff.contMDiffAt.comp x (hηO.contMDiffAt (hO.mem_nhds (hband hx)))
    · exact contMDiffAt_const.congr_of_eventuallyEq (hlocal x hx)
  · have hsupp : Function.support (fun x => annularCutoff φ (η x)) ⊆
        η ⁻¹' Icc (1 / 5 : ℝ) (9 / 10) := by
      intro x hx
      by_contra h
      exact hx (annularCutoff_eq_zero_of_not_mem hzero fun h' => h (Ioo_subset_Icc_self h'))
    intro x hx
    have hxI := hclosed.closure_subset_iff.mpr hsupp hx
    have h := abs_lt.mp (hclose x)
    exact ⟨by linarith [hxI.1], by linarith [hxI.2]⟩
  · by_cases hq : η q ∈ Icc (1 / 5 : ℝ) (9 / 10)
    · have hηq : MDifferentiableAt I 𝓘(ℝ, ℝ) η q :=
        (hηO.contMDiffAt (hO.mem_nhds (hband hq))).mdifferentiableAt (by simp)
      have hcomp : gradFun g (fun x => annularCutoff φ (η x)) q =
          deriv (annularCutoff φ) (η q) • gradFun g η q :=
        gradientFun_comp g (hΦ.differentiable (by simp) (η q)) hηq
      rw [hcomp, SmoothRiemannianMetric.metric_inner_smul_self, Real.sqrt_mul (sq_nonneg _),
        Real.sqrt_sq_eq_abs]
      exact mul_le_mul (hL _) (hgrad q hq) (Real.sqrt_nonneg _) hL0
    · have hzero' : gradFun g (fun x => annularCutoff φ (η x)) q = 0 := by
        apply gradFun_eq_zero_of_mfderiv_eq_zero
        rw [(hlocal q hq).mfderiv_eq]
        exact (hasMFDerivAt_const (I := I) (I' := 𝓘(ℝ, ℝ)) (0 : ℝ) q).mfderiv
      rw [hzero']
      simp only [map_zero, Real.sqrt_zero]
      positivity

/-- LC31: on a proper space the cutoff `ζ = Φ ∘ η` has compact support. -/
theorem hasCompactSupport_annularCutoff_comp_radial [ProperSpace M] {φ : ℝ → ℝ}
    (hzero : ∀ t, 1 ≤ t → φ t = 0) (p : M) {η : M → ℝ} {e : ℝ}
    (hclose : ∀ x, |η x - dist x p| < e) :
    HasCompactSupport (fun x => annularCutoff φ (η x)) := by
  refine HasCompactSupport.intro (isCompact_closedBall p (9 / 10 + e)) fun x hx => ?_
  apply annularCutoff_eq_zero_of_not_mem hzero
  intro h
  apply hx
  have h' := abs_lt.mp (hclose x)
  rw [Metric.mem_closedBall]
  linarith [h.2]

end DifferentialGeometry.Geometry.Collapse
