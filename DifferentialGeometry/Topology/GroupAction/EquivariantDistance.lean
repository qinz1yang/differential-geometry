import DifferentialGeometry.Topology.GroupAction.CompactLifting
import Mathlib.Topology.MetricSpace.IsometricSMul
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Order.Compact

namespace MulAction

section LocallyCompact

variable {Γ Δ X Y : Type*} [Group Γ] [TopologicalSpace X]
  [WeaklyLocallyCompactSpace X] [MulAction Γ X] [ContinuousConstSMul Γ X]
  [PseudoMetricSpace Y] [SMul Δ Y] [IsIsometricSMul Δ Y]

theorem exists_dist_le_on_quotient_preimage_of_equivariant
    {K : Set (orbitRel.Quotient Γ X)} (hK : IsCompact K)
    (f g : C(X, Y)) (φ : Γ → Δ)
    (hf : ∀ γ x, f (γ • x) = φ γ • f x)
    (hg : ∀ γ x, g (γ • x) = φ γ • g x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : X,
      Quotient.mk (orbitRel Γ X) x ∈ K → dist (f x) (g x) ≤ C := by
  obtain ⟨S, hS, hrep⟩ := exists_compact_representatives hK
  obtain ⟨C, hC⟩ := hS.bddAbove_image (f.continuous.dist g.continuous).continuousOn
  refine ⟨max 0 C, le_max_left _ _, ?_⟩
  intro x hx
  obtain ⟨γ, hγ⟩ := hrep x hx
  have hbound := hC (Set.mem_image_of_mem (fun z => dist (f z) (g z)) hγ)
  rw [hf, hg, dist_smul] at hbound
  exact hbound.trans (le_max_right _ _)

end LocallyCompact

section Proper

variable {Γ Δ X Y : Type*} [Group Γ] [PseudoMetricSpace X] [ProperSpace X]
  [MulAction Γ X] [IsIsometricSMul Γ X]
  [PseudoMetricSpace Y] [SMul Δ Y] [IsIsometricSMul Δ Y]

theorem exists_dist_image_le_on_quotient_preimage_of_equivariant
    {K : Set (orbitRel.Quotient Γ X)} (hK : IsCompact K)
    (f : C(X, Y)) (φ : Γ → Δ)
    (hf : ∀ γ x, f (γ • x) = φ γ • f x) (r : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x y : X,
      Quotient.mk (orbitRel Γ X) x ∈ K → dist x y ≤ r → dist (f x) (f y) ≤ C := by
  obtain ⟨S, hS, hrep⟩ := exists_compact_representatives hK
  have hT : IsCompact (Metric.cthickening r S) := hS.cthickening
  obtain ⟨C, hC⟩ := Metric.isBounded_iff.mp (hT.image f.continuous).isBounded
  refine ⟨max 0 C, le_max_left _ _, ?_⟩
  intro x y hx hxy
  obtain ⟨γ, hγ⟩ := hrep x hx
  have hxT : γ • x ∈ Metric.cthickening r S :=
    Metric.self_subset_cthickening S hγ
  have hyT : γ • y ∈ Metric.cthickening r S :=
    Metric.mem_cthickening_of_dist_le (γ • y) (γ • x) r S hγ
      (by simpa only [dist_smul, dist_comm] using hxy)
  have hbound := hC (Set.mem_image_of_mem f hxT) (Set.mem_image_of_mem f hyT)
  rw [hf, hf, dist_smul] at hbound
  exact hbound.trans (le_max_right _ _)

end Proper

end MulAction
