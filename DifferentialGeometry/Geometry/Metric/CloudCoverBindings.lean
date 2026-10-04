import DifferentialGeometry.Geometry.Metric.AffineScaleCover
import DifferentialGeometry.Geometry.Metric.CloudPlaneCoherence

set_option autoImplicit false
noncomputable section
open Set Metric
namespace GC.MetricGeometry

theorem exists_coherent_cloud_cover
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (S T : Set H) (hST : S ⊆ T) (hS : TotallyBounded S)
    (r : H → ℝ) (P : S → Submodule ℝ H)
    [∀ x : S, FiniteDimensional ℝ (P x)]
    (k : ℕ) (hdim : ∀ x : S, Module.finrank ℝ (P x) = k)
    (rmin R C δ : ℝ) (hrmin : 0 < rmin)
    (hlower : ∀ x ∈ S, rmin ≤ r x) (hupper : ∀ x ∈ S, r x ≤ R)
    (hC : 0 ≤ C) (hδ : 0 < δ)
    (hδsmall : δ ≤ (1 / (100 * (C + 1))) / (2 * (2 * (C + 1))))
    (hscale : ∀ x ∈ S, ∀ y ∈ S, |r y - r x| ≤ C * (dist x y + r x))
    (hcloud : ∀ x : S, hausdorffEDist (T ∩ ball (x : H) (r x / δ))
      ((AffineSubspace.mk' (x : H) (P x) : Set H) ∩ ball (x : H) (r x / δ)) ≤
        ENNReal.ofReal (δ * r x)) :
    let ℓ : ℝ := 1 / (100 * (C + 1))
    let A : ℝ := 2 * (C + 1)
    let D : ℝ := 20 * A + 6
    ∃ (I : Set H) (hIS : I ⊆ S), I.Finite ∧
      I.PairwiseDisjoint (fun i => ball i (ℓ * r i)) ∧
      ((⋃ x ∈ S, ball x (ℓ * r x)) ⊆ ⋃ i ∈ I, ball i (5 * ℓ * r i)) ∧
      ∀ x : S, ∀ v ∈ ball (x : H) (5 * ℓ * r x),
        let J := I ∩ {i | (closedBall i (20 * ℓ * r i) ∩ ball v (ℓ * r x)).Nonempty}
        (J.ncard : ℝ) ≤ (1 + 2 * A * D) ^ k ∧
        ∀ (i : H) (hi : i ∈ J), r x / A ≤ r i ∧ r i ≤ A * r x ∧
          dist i x ≤ D * ℓ * r x ∧
          ‖(P x)ᗮ.starProjection (i - x)‖ ≤ δ * r x ∧
          ‖(P ⟨i, hIS hi.1⟩)ᗮ.starProjection - (P x)ᗮ.starProjection‖ ≤ 6 * (A + 1) * δ := by
  let ℓ : ℝ := 1 / (100 * (C + 1))
  have hr (x : H) (hx : x ∈ S) : 0 < r x := hrmin.trans_le (hlower x hx)
  have hℓ : 0 < ℓ := by dsimp [ℓ]; positivity
  have hbudget : C * ℓ ≤ 1 / 100 := by
    dsimp [ℓ]
    rw [← mul_div_assoc, mul_one]
    apply (div_le_iff₀ (by positivity : 0 < 100 * (C + 1))).mpr
    nlinarith
  obtain ⟨I, hIS, hI, hdisj, hcover, hpack⟩ :=
    exists_finite_disjoint_scale_cover_of_hausdorffEDist_le
      S T hST hS r P hrmin hlower hupper hC hδ hδsmall hscale hcloud
  refine ⟨I, hIS, hI, hdisj, hcover, ?_⟩
  intro x v hv
  refine ⟨by simpa only [hdim x] using hpack x v hv, ?_⟩
  intro i hi
  have hlo := Metric.coarse_scale_comparison_of_support_meeting
    (hr x x.property) (hr i (hIS hi.1)) hC hℓ.le hbudget
    (show r i - r x ≤ C * (dist i x + r x) from by
      simpa only [dist_comm (x : H) i] using (abs_le.mp (hscale x x.property i (hIS hi.1))).2)
    ((abs_le.mp (hscale i (hIS hi.1) x x.property)).2) hv hi.2
  have hc := normal_projection_coherence_of_cloud_support_meeting
    S T hST r P C hC δ hδ hr hscale hcloud hδsmall
    x ⟨i, hIS hi.1⟩ (by rw [hdim x, hdim ⟨i, hIS hi.1⟩]) v hv hi.2
  exact ⟨hlo.1, hlo.2.1, hlo.2.2, hc.1, hc.2⟩

end GC.MetricGeometry
