import DifferentialGeometry.Analysis.Calculus.GraphCoverageAdapters
import DifferentialGeometry.Geometry.Metric.RetainedMarkerRadii

set_option autoImplicit false

noncomputable section

open Set Metric
open scoped ContDiff Topology InnerProductSpace BigOperators

namespace DifferentialGeometry.Geometry.Fibration

variable {M E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]

/-- Actual source coordinates and their coverage yield identical-radius relative coverage. -/
theorem finite_packet_original_image_coverage (F : M → H) (η : M → E) (D : Set M)
    (Φ : E → H) (P : H →L[ℝ] E) (hP : ∀ z, ‖P z‖ ≤ ‖z‖) (hgraph : ∀ u, P (Φ u) = u)
    (p : M) (hp : p ∈ D) {σ Γ r B e : ℝ} (hσ : 0 < σ) (hΓ : 0 < Γ)
    (hB : 0 ≤ B) (he : 0 ≤ e) (hrlow : σ / 2 ≤ r) (hrhigh : r ≤ 2 * σ)
    (hebudget : e ≤ Γ * σ / 24) (hcurv : B * σ ≤ Γ ^ 3 / 6)
    (hreg : ∀ u ∈ closedBall (P (F p)) (r / Γ), ContDiffAt ℝ 2 Φ u)
    (hsecond : ∀ u ∈ closedBall (P (F p)) (r / Γ), ‖iteratedFDeriv ℝ 2 Φ u‖ ≤ B)
    (hcoord : ∀ q ∈ D, P (F q) = η q)
    (happrox : ∀ q ∈ D, dist (F q) (Φ (η q)) ≤ e)
    (hcover : ∀ u ∈ closedBall (P (F p)) (r / Γ), ∃ q ∈ D, η q = u) :
    hausdorffDist (F '' D ∩ closedBall (F p) (r / Γ))
      ((fun v => F p + fderiv ℝ Φ (P (F p)) v) '' (univ : Set E) ∩
        closedBall (F p) (r / Γ)) ≤ Γ * r := by
  have hr : 0 < r := by linarith
  have h := GC.MetricGeometry.hausdorffDist_coordinate_graph_coverage_le F η D Φ P hP
    hgraph (F '' D) (F p) ⟨p, hp, rfl⟩ (div_pos hr hΓ) hB he hreg hsecond
    (by
      rintro y ⟨⟨q, hq, rfl⟩, _⟩
      exact ⟨q, hq, rfl, hcoord q hq⟩) happrox
    (by
      intro u hu
      obtain ⟨q, hq, hη⟩ := hcover u hu
      exact ⟨q, hq, hη, ⟨q, hq, rfl⟩⟩)
  have hb := GC.MetricGeometry.graph_coverage_relative_error_le hσ hΓ hB hrlow hrhigh
    hebudget hcurv
  exact h.trans ((div_le_iff₀ hr).mp hb)

end DifferentialGeometry.Geometry.Fibration

namespace DifferentialGeometry.Geometry.Fibration

/-- Radius choices on the actual image obey the cloudy radius law, without scale descent. -/
theorem finite_packet_image_radius {P X ι : Type*} [PseudoMetricSpace P] [PseudoMetricSpace X]
    (f : P → X) (ρ : P → ℝ) {Λ : NNReal} (hρ : LipschitzWith Λ ρ)
    (hpos : ∀ p, 0 < ρ p) (marker : ι → X → ℝ) (R : ι → ℝ) (c : ι → P) (C : ι → ℝ)
    (hR : ∀ j, R j = ρ (c j)) (hsmall : ∀ j, Λ * C j ≤ 1 / 4)
    (hmarker : ∀ j, LipschitzWith 1 (marker j))
    (hfull : ∀ p, ∃ j, marker j (f p) = R j)
    (hsupport : ∀ j p, 0 < marker j (f p) → p ∈ closedBall (c j) (C j * ρ (c j)))
    {σ : ℝ} (hσ : 0 < σ) (hσhalf : σ ≤ 1 / 2) :
    ∃ r : range f → ℝ, (∀ x, 0 < r x) ∧
      (∀ x, ∃ p, f p = x.val ∧ r x = σ * ρ p) ∧
      ∀ x y, |r y - r x| ≤ 2 * (dist x.val y.val + r x) := by
  classical
  have hpositive (j : ι) : 0 < R j := by rw [hR j]; exact hpos (c j)
  have hs (j : ι) (p : P) (hp : 0 < marker j (f p)) :
      3 * R j / 4 ≤ ρ p ∧ ρ p ≤ 5 * R j / 4 := by
    rw [hR j]
    exact GC.MetricGeometry.scale_bounds_on_closedBall hρ (hpos (c j)) (hsmall j)
      (hsupport j p hp)
  let chosen (x : range f) : P := x.property.choose
  have hchosen (x : range f) : f (chosen x) = x.val := x.property.choose_spec
  refine ⟨fun x => σ * ρ (chosen x), fun x => mul_pos hσ (hpos (chosen x)),
    fun x => ⟨chosen x, hchosen x, rfl⟩, ?_⟩
  intro x y
  simpa only [hchosen] using GC.MetricGeometry.radius_control_of_retained_markers f ρ marker R
    hpositive hmarker hfull hs hσ.le hσhalf (chosen x) (chosen y)

end DifferentialGeometry.Geometry.Fibration
