import DifferentialGeometry.Geometry.Collapse.SublevelCore.JointWitnessConeRadial
import DifferentialGeometry.Geometry.Metric.Scaling.RescaleGeometry

/-!
# Adapters at a fixed scale: LC30's clauses as the core theorems' radial-function inputs

The LC30 output at scale `R` (`exists_scale_eventually_cone_radial_witnesses`) is stated with
`Metric.infDist x {p}`, a pointwise Lipschitz-difference bound and the gradient bound
`1 - ε ≤ ‖∇F‖`; the LC51/LC60 core theorems take `|F x - d(p, x)| < e`,
`LipschitzWith ε (F - d_p)` and `(1 - ε)² ≤ g(∇F, ∇F)` on the shell.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Bundle Metric
open scoped Manifold ContDiff Topology NNReal

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Operator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

/-- **LC30's clauses at scale `R` give the core theorems' radial-function inputs.** -/
theorem core_clauses_of_radial_clauses_at_scale {X : Type*} [m : MetricSpace X]
    [ChartedSpace H X] [IsManifold I ∞ X] (g : SmoothRiemannianMetric I X) {R : ℝ} (hR : 0 < R)
    (p : X) {ε : ℝ≥0} (hε1 : (ε : ℝ) < 1) {e : ℝ} (he1 : e < 1 / 40) {F : X → ℝ}
    (h : letI := m.rescale R⁻¹ (inv_pos.mpr hR)
      let gR := scaleMetric (R⁻¹ ^ 2) (pow_pos (inv_pos.mpr hR) 2) g
      (∃ O : Set X, IsOpen O ∧ {x : X | 1 / 10 ≤ dist x p ∧ dist x p ≤ 10} ⊆ O ∧
        ContMDiffOn I 𝓘(ℝ, ℝ) ∞ F O) ∧
      (∀ x, |F x - Metric.infDist x {p}| < e) ∧
      (∀ x y, |(F x - Metric.infDist x {p}) - (F y - Metric.infDist y {p})| ≤
        (ε : ℝ) * dist x y) ∧
      ∀ q ∈ {x : X | 1 / 10 ≤ dist x p ∧ dist x p ≤ 10},
        1 - (ε : ℝ) ≤ Real.sqrt (gR.inner q (gradFun gR F q) (gradFun gR F q))) :
    letI := m.rescale R⁻¹ (inv_pos.mpr hR)
    let gR : SmoothRiemannianMetric I X := scaleMetric (R⁻¹ ^ 2) (pow_pos (inv_pos.mpr hR) 2) g
    e < 1 / 40 ∧ (∀ x, |F x - dist p x| < e) ∧ LipschitzWith ε (fun x => F x - dist p x) ∧
      ∃ W : Set X, IsOpen W ∧ (∀ x, 1 / 10 ≤ dist p x → dist p x ≤ 10 → x ∈ W) ∧
        ContMDiffOn I 𝓘(ℝ, ℝ) ∞ F W ∧
        ∀ x, 1 / 10 ≤ dist p x → dist p x ≤ 10 →
          (1 - (ε : ℝ)) ^ 2 ≤ gR.inner x (gradientFun (I := I) gR F x)
            (gradientFun (I := I) gR F x) := by
  let := m.rescale R⁻¹ (inv_pos.mpr hR)
  obtain ⟨⟨O, hO, hshell, hFO⟩, hclose, hdiff, hgrad⟩ := h
  refine ⟨he1, fun x => ?_, ?_, O, hO, fun x h1 h2 => hshell ⟨?_, ?_⟩, hFO, fun x h1 h2 => ?_⟩
  · have hx := hclose x
    rwa [Metric.infDist_singleton, dist_comm] at hx
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    have hxy := hdiff x y
    rw [Metric.infDist_singleton, Metric.infDist_singleton, dist_comm x p, dist_comm y p] at hxy
    rw [Real.dist_eq]
    exact hxy
  · rw [dist_comm]; exact h1
  · rw [dist_comm]; exact h2
  · have hq := hgrad x ⟨by rw [dist_comm]; exact h1, by rw [dist_comm]; exact h2⟩
    have h0 : 0 ≤ 1 - (ε : ℝ) := by linarith
    have hnn : 0 ≤ (scaleMetric (R⁻¹ ^ 2) (pow_pos (inv_pos.mpr hR) 2) g).inner x
        (gradFun (scaleMetric (R⁻¹ ^ 2) (pow_pos (inv_pos.mpr hR) 2) g) F x)
        (gradFun (scaleMetric (R⁻¹ ^ 2) (pow_pos (inv_pos.mpr hR) 2) g) F x) :=
      metric_inner_self_nonneg _ _ _
    have hsq := pow_le_pow_left₀ h0 hq 2
    rw [Real.sq_sqrt hnn] at hsq
    exact hsq

end DifferentialGeometry.Geometry.Collapse
