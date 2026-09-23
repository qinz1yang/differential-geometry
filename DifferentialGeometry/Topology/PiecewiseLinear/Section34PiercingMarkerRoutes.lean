import DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercedBallFrontiers
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Instances.Real.Lemmas

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem exists_disjoint_piercing_marker_routes {E : Type*} [TopologicalSpace E]
    {P : Set E} {g : E → ℝ} (hg : Continuous g) {a : ℝ} (ha1 : a ≤ 1)
    {p₀ p₁ : E × ℝ} (hp₀P : p₀.1 ∈ interior P) (hp₁P : p₁.1 ∈ interior P)
    (hp₀t : -a / 2 ≤ p₀.2 ∧ p₀.2 ≤ 0) (hp₁t : 0 ≤ p₁.2 ∧ p₁.2 ≤ a / 2)
    (hg₀ : 0 < g p₀.1 ∧ g p₀.1 ≤ a / 2) (hg₁ : 0 < g p₁.1 ∧ g p₁.1 ≤ a / 2)
    (hne : p₀ ≠ p₁) :
    ∃ (K₀ K₁ : Set (E × ℝ)) (q₀ q₁ : E × ℝ),
      IsCompact K₀ ∧ IsCompact K₁ ∧ IsConnected K₀ ∧ IsConnected K₁ ∧ Disjoint K₀ K₁ ∧
      p₀ ∈ K₀ ∧ q₀ ∈ K₀ ∧ p₁ ∈ K₁ ∧ q₁ ∈ K₁ ∧
      K₀ ⊆ interior {y : E × ℝ | y.1 ∈ P ∧ -1 ≤ y.2 ∧ y.2 ≤ g y.1} ∩
        (univ ×ˢ Ioo (-a) a) ∧
      K₁ ⊆ interior {y : E × ℝ | y.1 ∈ P ∧ -g y.1 ≤ y.2 ∧ y.2 ≤ 1} ∩
        (univ ×ˢ Ioo (-a) a) ∧
      q₀ ∉ {y : E × ℝ | y.1 ∈ P ∧ -g y.1 ≤ y.2 ∧ y.2 ≤ 1} ∧
      q₁ ∉ {y : E × ℝ | y.1 ∈ P ∧ -1 ≤ y.2 ∧ y.2 ≤ g y.1} := by
  let K₀ := {p₀.1} ×ˢ Icc (-3 * a / 4) p₀.2
  let K₁ := {p₁.1} ×ˢ Icc p₁.2 (3 * a / 4)
  have hlo : -3 * a / 4 ≤ p₀.2 := by linarith [hp₀t.1]
  have hhi : p₁.2 ≤ 3 * a / 4 := by linarith [hp₁t.2]
  have hAi : {y : E × ℝ | y.1 ∈ interior P ∧ -1 < y.2 ∧ y.2 < g y.1} ⊆
      interior {y : E × ℝ | y.1 ∈ P ∧ -1 ≤ y.2 ∧ y.2 ≤ g y.1} := by
    refine interior_maximal ?_ ?_
    · exact fun _ hy => ⟨interior_subset hy.1, hy.2.1.le, hy.2.2.le⟩
    exact (isOpen_interior.preimage continuous_fst).inter
      ((isOpen_lt continuous_const continuous_snd).inter
        (isOpen_lt continuous_snd (hg.comp continuous_fst)))
  have hBi : {y : E × ℝ | y.1 ∈ interior P ∧ -g y.1 < y.2 ∧ y.2 < 1} ⊆
      interior {y : E × ℝ | y.1 ∈ P ∧ -g y.1 ≤ y.2 ∧ y.2 ≤ 1} := by
    refine interior_maximal ?_ ?_
    · exact fun _ hy => ⟨interior_subset hy.1, hy.2.1.le, hy.2.2.le⟩
    exact (isOpen_interior.preimage continuous_fst).inter
      ((isOpen_lt (hg.neg.comp continuous_fst) continuous_snd).inter
        (isOpen_lt continuous_snd continuous_const))
  refine ⟨K₀, K₁, (p₀.1, -3 * a / 4), (p₁.1, 3 * a / 4),
    isCompact_singleton.prod isCompact_Icc, isCompact_singleton.prod isCompact_Icc,
    isConnected_singleton.prod (isConnected_Icc hlo),
    isConnected_singleton.prod (isConnected_Icc hhi), ?_,
    ⟨rfl, hlo, le_rfl⟩, ⟨rfl, le_rfl, hlo⟩, ⟨rfl, le_rfl, hhi⟩,
    ⟨rfl, hhi, le_rfl⟩, ?_, ?_, ?_, ?_⟩
  · apply Set.disjoint_left.mpr
    intro x hx₀ hx₁
    have he₀ : x.1 = p₀.1 := hx₀.1
    have he₁ : x.1 = p₁.1 := hx₁.1
    apply hne (Prod.ext (he₀.symm.trans he₁) _)
    linarith [hx₀.2.2, hx₁.2.1, hp₀t.2, hp₁t.1]
  · intro x hx
    have he : x.1 = p₀.1 := hx.1
    refine ⟨hAi ⟨he.symm ▸ hp₀P, ?_, ?_⟩, mem_univ _, ?_, ?_⟩
    · linarith [hx.2.1]
    · rw [he]
      linarith [hx.2.2, hp₀t.2, hg₀.1]
    · linarith [hx.2.1]
    · linarith [hx.2.2, hp₀t.2]
  · intro x hx
    have he : x.1 = p₁.1 := hx.1
    refine ⟨hBi ⟨he.symm ▸ hp₁P, ?_, ?_⟩, mem_univ _, ?_, ?_⟩
    · rw [he]
      linarith [hx.2.1, hp₁t.1, hg₁.1]
    · linarith [hx.2.2]
    · linarith [hx.2.1, hp₁t.1]
    · linarith [hx.2.2]
  · intro hq
    have hq' : -g p₀.1 ≤ -3 * a / 4 := hq.2.1
    linarith [hg₀.2]
  · intro hq
    have hq' : 3 * a / 4 ≤ g p₁.1 := hq.2.2
    linarith [hg₁.2]

end DifferentialGeometry.Topology.PiecewiseLinear
