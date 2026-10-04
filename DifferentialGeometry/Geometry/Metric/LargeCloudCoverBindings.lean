import DifferentialGeometry.Geometry.Metric.LargeCloudCover

set_option autoImplicit false
noncomputable section
open Set Metric
namespace GC.MetricGeometry
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
theorem exists_large_cloud_cover_of_blueprint_smallness
    (S T : Set H) (hST : S ⊆ T) (hS : TotallyBounded S)
    (r : H → ℝ) (P : S → Submodule ℝ H)
    [∀ x : S, FiniteDimensional ℝ (P x)]
    (k : ℕ) (hdim : ∀ x : S, Module.finrank ℝ (P x) = k)
    (rmin R b B δ : ℝ) (hrmin : 0 < rmin)
    (hlower : ∀ x ∈ S, rmin ≤ r x) (hupper : ∀ x ∈ S, r x ≤ R)
    (hb : 1 ≤ b) (hB : 1 ≤ B) (hδ : 0 < δ)
    (hδsmall : δ ≤ min (1 / (8 * B))
      (min (1 / (4 * (128 * b * B + 3))) (1 / (8 * (B + 1)))))
    (hscale : ∀ x ∈ S, ∀ y ∈ S, dist y x ≤ 128 * b * max (r y) (r x) →
      r x / B ≤ r y ∧ r y ≤ B * r x)
    (hcloud : ∀ x : S,
      hausdorffEDist (T ∩ ball x (r x / δ))
        ((AffineSubspace.mk' (x : H) (P x) : Set H) ∩ ball x (r x / δ)) ≤
          ENNReal.ofReal (δ * r x)) :
    let D : ℝ := 80 * B + 31
    ∃ (I : Set H) (hIS : I ⊆ S), I.Finite ∧
      I.PairwiseDisjoint (fun i => ball i (r i)) ∧
      (∀ x ∈ S, ∃ i ∈ I, r x ≤ 2 * r i ∧ dist x i < 3 * r i) ∧
      ((⋃ x ∈ S, ball x (8 * b * r x)) ⊆ ⋃ i ∈ I, ball i (20 * b * r i)) ∧
      ∀ x : S,
        let J : Set H := I ∩ {i | (closedBall i (80 * b * r i) ∩ ball x (30 * b * r x)).Nonempty}
        (J.ncard : ℝ) ≤ (1 + 2 * B * D * b) ^ k ∧
        ∀ (i : H) (hi : i ∈ J), r x / B ≤ r i ∧ r i ≤ B * r x ∧ dist i x < D * b * r x ∧
          ‖(P x)ᗮ.starProjection (i - x)‖ ≤ δ * r x ∧
          ‖(P ⟨i, hIS hi.1⟩)ᗮ.starProjection - (P x)ᗮ.starProjection‖ ≤ 6 * (B + 1) * δ := by
  have hs := le_trans hδsmall (min_le_right _ _)
  have ht := le_trans hs (min_le_left _ _)
  have hd : δ * (4 * (128 * b * B + 3)) ≤ 1 :=
    (le_div_iff₀ (by positivity)).mp ht
  have hm : (80 * B + 31) * b + 2 < 4 * (128 * b * B + 3) := by
    have hbb : b ≤ b * B := by nlinarith
    nlinarith
  have hi : δ * ((80 * B + 31) * b + 2) < 1 :=
    (mul_lt_mul_of_pos_left hm hδ).trans_le hd
  exact exists_large_cloud_cover_of_hausdorffEDist_le
    S T hST hS r P k hdim rmin R b B δ hrmin hlower hupper hb hB hδ hi hscale hcloud

end GC.MetricGeometry
