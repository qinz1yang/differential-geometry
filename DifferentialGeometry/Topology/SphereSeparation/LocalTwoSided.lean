import DifferentialGeometry.Topology.SphereSeparation.Incidence
import DifferentialGeometry.Topology.SphereSeparation.LocalNormalForm

set_option autoImplicit false

open Function Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.SphereSeparation

namespace EmbeddedSphereNormalChart

variable {N : Type*} [TopologicalSpace N] [ChartedSpace EuclideanThree N]
  {e : SphereTwo → N} {x : SphereTwo}

private theorem central_subset_closure_half
    (c : EmbeddedSphereNormalChart e x) (sign : ℝ)
    (hsign : sign = 1 ∨ sign = -1) :
    c.neighborhood ∩ Set.range e ⊆
      closure (c.neighborhood ∩
        {y | 0 < sign * c.normalCoordinate y}) := by
  intro y hy
  rw [mem_closure_iff]
  intro U hU hyU
  let h := c.normalForm
  let W : Set N := U ∩ c.neighborhood
  have hWopen : IsOpen W := hU.inter c.isOpen_neighborhood
  have hWsource : W ⊆ h.codChart.source := by
    intro q hq
    exact c.neighborhood_subset_codChart_source hq.2
  let D : Set EuclideanThree := h.codChart '' W
  have hDopen : IsOpen D :=
    h.codChart.isOpen_image_of_subset_source hWopen hWsource
  have hyW : y ∈ W := ⟨hyU, hy.1⟩
  have hyD : h.codChart y ∈ D := ⟨y, hyW, rfl⟩
  obtain ⟨ε, hε, hballD⟩ := (Metric.isOpen_iff.1 hDopen) _ hyD
  let v : EuclideanThree := h.equiv (0, (sign : ℝ))
  have hvne : v ≠ 0 := by
    intro hv
    have hv' : ((0 : EuclideanSpace ℝ (Fin 2)), sign) = 0 :=
      h.equiv.map_eq_zero_iff.mp hv
    have hs0 : sign = 0 := congrArg Prod.snd hv'
    rcases hsign with rfl | rfl <;> norm_num at hs0
  have hvnorm : 0 < ‖v‖ := norm_pos_iff.mpr hvne
  let δ : ℝ := ε / (2 * ‖v‖)
  have hδ : 0 < δ := div_pos hε (mul_pos (by norm_num) hvnorm)
  let z : EuclideanThree := h.codChart y + δ • v
  have hzball : z ∈ Metric.ball (h.codChart y) ε := by
    rw [Metric.mem_ball, dist_eq_norm]
    have hsub : z - h.codChart y = δ • v := by simp [z]
    rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_pos hδ]
    change δ * ‖v‖ < ε
    rw [show δ * ‖v‖ = ε / 2 by
      dsimp [δ]
      field_simp]
    linarith
  obtain ⟨q, hqW, hqz⟩ := hballD hzball
  have hyzero : (h.equiv.symm (h.codChart y)).2 = 0 := by
    exact (c.normalCoordinate_eq_zero_iff hy.1).2 hy.2
  have hqsign : 0 < sign * c.normalCoordinate q := by
    change 0 < sign * (h.equiv.symm (h.codChart q)).2
    rw [hqz]
    simp only [z, map_add, map_smul, v, h.equiv.symm_apply_apply,
      Prod.smul_mk, smul_eq_mul, Prod.snd_add]
    rw [hyzero]
    rcases hsign with rfl | rfl
    · simpa using hδ
    · simpa using hδ
  exact ⟨q, hqW.1, hqW.2, hqsign⟩

theorem central_subset_closure_positiveHalf
    (c : EmbeddedSphereNormalChart e x) :
    c.neighborhood ∩ Set.range e ⊆ closure c.positiveHalf := by
  simpa only [positiveHalf, one_mul] using
    c.central_subset_closure_half 1 (Or.inl rfl)

theorem central_subset_closure_negativeHalf
    (c : EmbeddedSphereNormalChart e x) :
    c.neighborhood ∩ Set.range e ⊆ closure c.negativeHalf := by
  have h := c.central_subset_closure_half (-1) (Or.inr rfl)
  simpa only [negativeHalf, neg_mul, one_mul, neg_pos] using h

end EmbeddedSphereNormalChart

theorem locallyTwoSided_range_of_isSmoothEmbedding
    {N : Type*} [TopologicalSpace N] [ChartedSpace EuclideanThree N]
    {e : SphereTwo → N}
    (he : Manifold.IsSmoothEmbedding (𝓡 2)
      (modelWithCornersSelf ℝ EuclideanThree) ∞ e) :
    LocallyTwoSided (Set.range e) := by
  intro y hy
  rcases hy with ⟨x, rfl⟩
  obtain ⟨c, hpos, hneg⟩ :=
    exists_embeddedSphereNormalChart_connected_halves he x
  exact ⟨{
    neighborhood := c.neighborhood
    negative := c.negativeHalf
    positive := c.positiveHalf
    isOpen_neighborhood := c.isOpen_neighborhood
    mem_neighborhood := c.image_mem_neighborhood
    isConnected_negative := hneg
    isConnected_positive := hpos
    disjoint := c.disjoint_positiveHalf_negativeHalf.symm
    punctured_eq := c.neighborhood_diff_range_eq_halves.trans
      (union_comm _ _)
    central_subset_closure_negative :=
      c.central_subset_closure_negativeHalf
    central_subset_closure_positive :=
      c.central_subset_closure_positiveHalf
  }⟩

end DifferentialGeometry.Topology.SphereSeparation
