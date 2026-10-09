import DifferentialGeometry.Geometry.Comparison.PairedPacket
import DifferentialGeometry.Geometry.Comparison.PairedCorrection
import DifferentialGeometry.Topology.MetricSpace.DistanceCoordinates
import DifferentialGeometry.Topology.MetricSpace.CoordinateResidual

set_option autoImplicit false

open Set Metric Real

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

variable {X ι : Type*} [MetricSpace X]

theorem PairedComparisonPacket.exists_distance_coordinate_move
    (hcurves : ∀ p u : X, ∀ η : ℝ, 0 < η →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = p ∧ c 1 = u ∧
        eVariationOn c univ < ENNReal.ofReal (dist p u + η))
    {Ω V : Set X} {a b : ι → X} {x : X} {a₀ A δ t : ℝ}
    (hpacket : PairedComparisonPacket δ V a b)
    (hcomp : fourPointComparison 1 Ω) (hV : V ⊆ Ω)
    (hanchors : range a ∪ range b ⊆ Ω)
    (ha₀ : 0 < a₀) (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 100)
    (ht : 0 < t) (ht1 : t ≤ 1) (hta : t ≤ a₀ / 2)
    (hscale : t ≤ δ ^ 2 / (4 * cosh (A + 1) / sinh a₀))
    (hball : closedBall x t ⊆ V)
    (hbounds : ∀ z ∈ V, ∀ c ∈ range a ∪ range b, dist z c ∈ Icc a₀ A)
    (i : ι) (w : ℝ) :
    ∃ y ∈ V, dist x y = t ∧
      (if w ≤ dist x (a i) then
        (1 - 3 * δ ^ 2) * t ≤ dist x (a i) - dist y (a i) ∧ dist x (a i) - dist y (a i) ≤ t
       else (1 - 3 * δ ^ 2) * t ≤ dist y (a i) - dist x (a i) ∧ dist y (a i) - dist x (a i) ≤ t) ∧
      ∀ j ≠ i, dist (dist y (a j)) (dist x (a j)) ≤ (6 * δ) * t := by
  let W : Set X := {c | ∃ j, j ≠ i ∧ c = a j}
  have hordered (u v : X) (huv : (u = a i ∧ v = b i) ∨ (u = b i ∧ v = a i)) :
      ∃ y ∈ V, dist x y = t ∧
        (1 - δ ^ 2) * t ≤ dist x u - dist y u ∧ dist x u - dist y u ≤ t ∧
        (1 - 3 * δ ^ 2) * t ≤ dist y v - dist x v ∧ dist y v - dist x v ≤ t ∧
        ∀ j ≠ i, dist (dist y (a j)) (dist x (a j)) ≤ (6 * δ) * t := by
    have hsub : insert u (insert v W) ⊆ range a ∪ range b := by
      intro c hc
      rcases mem_insert_iff.mp hc with rfl | hc
      · rcases huv with ⟨rfl, _⟩ | ⟨rfl, _⟩
        · exact Or.inl ⟨i, rfl⟩
        · exact Or.inr ⟨i, rfl⟩
      · rcases mem_insert_iff.mp hc with rfl | hc
        · rcases huv with ⟨_, rfl⟩ | ⟨_, rfl⟩
          · exact Or.inr ⟨i, rfl⟩
          · exact Or.inl ⟨i, rfl⟩
        · obtain ⟨j, _, rfl⟩ := hc
          exact Or.inl ⟨j, rfl⟩
    obtain ⟨y, hy, hxy, hd, hdu, hv, hvu, hrest⟩ := exists_paired_geometric_correction
      hcurves hcomp hV (hsub.trans hanchors) ha₀ hδ hδ1 ht ht1 hta hscale hball
      (fun z hz c hc => hbounds z hz c (hsub hc))
      (fun z hz => by
        rcases huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hpacket.opposite z hz i
        · exact hpacket.swap.opposite z hz i)
      (fun z hz c hc => by
        obtain ⟨j, hji, rfl⟩ := hc
        have hu : u ∈ ({a i, b i} : Set X) := by rcases huv with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> simp
        have hv : v ∈ ({a i, b i} : Set X) := by rcases huv with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp
        exact ⟨hpacket.cross z hz i j hji.symm u hu (a j) (by simp),
          hpacket.cross z hz i j hji.symm v hv (a j) (by simp)⟩)
    refine ⟨y, hy, hxy, hd, hdu, hv, hvu, ?_⟩
    intro j hji
    simpa only [Real.dist_eq] using hrest (a j) ⟨j, hji, rfl⟩
  by_cases hw : w ≤ dist x (a i)
  · obtain ⟨y, hy, hxy, hd, hdu, _, _, hrest⟩ := hordered (a i) (b i) (Or.inl ⟨rfl, rfl⟩)
    refine ⟨y, hy, hxy, ?_, hrest⟩
    rw [ite_eq_left hw]
    exact ⟨by nlinarith [mul_nonneg (sq_nonneg δ) ht.le], hdu⟩
  · obtain ⟨y, hy, hxy, _, _, hd, hdu, hrest⟩ := hordered (b i) (a i) (Or.inr ⟨rfl, rfl⟩)
    exact ⟨y, hy, hxy, by rw [ite_eq_right hw]; exact ⟨hd, hdu⟩, hrest⟩

end DifferentialGeometry.Geometry.Comparison.Toponogov
