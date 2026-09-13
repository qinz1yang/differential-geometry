import DifferentialGeometry.Topology.SphereSeparation.LocalNormalForm
import DifferentialGeometry.Topology.FundamentalGroup.Sphere

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.SphereSeparation

variable {N : Type*} [TopologicalSpace N] [ChartedSpace EuclideanThree N]
  {e : SphereTwo → N} {x : SphereTwo}

theorem not_both_normalHalves_subset_of_twoSidedCover
    [IsManifold (modelWithCornersSelf ℝ EuclideanThree) ∞ N]
    {B D : Set N} (hBd : Disjoint B D)
    (hunion : B ∪ D = (Set.range e)ᶜ)
    (hBcl : closure B = B ∪ Set.range e)
    (hDcl : closure D = D ∪ Set.range e)
    (c : EmbeddedSphereNormalChart e x) :
    ¬ (c.positiveHalf ⊆ B ∧ c.negativeHalf ⊆ B) ∧
      ¬ (c.positiveHalf ⊆ D ∧ c.negativeHalf ⊆ D) := by
  have hBsub : B ⊆ (Set.range e)ᶜ := by
    rw [← hunion]; exact Set.subset_union_left
  have hDsub : D ⊆ (Set.range e)ᶜ := by
    rw [← hunion]; exact Set.subset_union_right
  have key : ∀ {S T : Set N}, (c.positiveHalf ⊆ S) → (c.negativeHalf ⊆ S) →
      T ⊆ (Set.range e)ᶜ → Disjoint S T → T ∩ c.neighborhood = ∅ := by
    intro S T hp hn hTsub hST
    rw [Set.eq_empty_iff_forall_notMem]
    rintro z ⟨hzT, hzN⟩
    have hzhalves : z ∈ c.positiveHalf ∪ c.negativeHalf := by
      rw [← c.neighborhood_diff_range_eq_halves]
      exact ⟨hzN, fun h => hTsub hzT h⟩
    rcases hzhalves with h | h
    · exact hST.le_bot ⟨hp h, hzT⟩
    · exact hST.le_bot ⟨hn h, hzT⟩
  constructor
  · rintro ⟨hp, hn⟩
    have hemp : D ∩ c.neighborhood = ∅ := key hp hn hDsub hBd
    have hsub : D ⊆ (c.neighborhood)ᶜ := fun z hz hzN =>
      Set.eq_empty_iff_forall_notMem.mp hemp z ⟨hz, hzN⟩
    have hcl : closure D ⊆ (c.neighborhood)ᶜ :=
      closure_minimal hsub c.isOpen_neighborhood.isClosed_compl
    have : e x ∈ closure D := by rw [hDcl]; exact Or.inr ⟨x, rfl⟩
    exact (hcl this) c.image_mem_neighborhood
  · rintro ⟨hp, hn⟩
    have hemp : B ∩ c.neighborhood = ∅ := key hp hn hBsub hBd.symm
    have hsub : B ⊆ (c.neighborhood)ᶜ := fun z hz hzN =>
      Set.eq_empty_iff_forall_notMem.mp hemp z ⟨hz, hzN⟩
    have hcl : closure B ⊆ (c.neighborhood)ᶜ :=
      closure_minimal hsub c.isOpen_neighborhood.isClosed_compl
    have : e x ∈ closure B := by rw [hBcl]; exact Or.inr ⟨x, rfl⟩
    exact (hcl this) c.image_mem_neighborhood

namespace EmbeddedSphereNormalChart

private theorem isConnected_positiveHalf_of_neighborhood_eq_chart_symm_ball
    (c : EmbeddedSphereNormalChart e x) (ε : ℝ) (hε : 0 < ε)
    (hballTarget : Metric.ball (c.normalForm.codChart (e x)) ε ⊆
      c.normalForm.codChart.target)
    (hneigh : c.neighborhood = c.normalForm.codChart.symm ''
      Metric.ball (c.normalForm.codChart (e x)) ε) :
    IsConnected c.positiveHalf := by
  let h := c.normalForm
  let z₀ : EuclideanThree := h.codChart (e x)
  let ball : Set EuclideanThree := Metric.ball z₀ ε
  let P : Set EuclideanThree := {z | 0 < (h.equiv.symm z).2}
  have hconvP : Convex ℝ P := by
    let normalMap : EuclideanThree →ₗ[ℝ] ℝ :=
      (LinearMap.snd ℝ (EuclideanSpace ℝ (Fin 2)) ℝ).comp
        h.equiv.symm.toLinearEquiv.toLinearMap
    simpa [P, normalMap] using
      convex_halfSpace_gt normalMap.isLinear 0
  have hnonempty : (ball ∩ P).Nonempty := by
    let v : EuclideanThree := h.equiv (0, (1 : ℝ))
    have hvne : v ≠ 0 := by
      intro hv
      have hv' : ((0 : EuclideanSpace ℝ (Fin 2)), (1 : ℝ)) = 0 :=
        h.equiv.map_eq_zero_iff.mp hv
      have hone := congrArg Prod.snd hv'
      norm_num at hone
    have hvnorm : 0 < ‖v‖ := norm_pos_iff.mpr hvne
    let δ : ℝ := ε / (2 * ‖v‖)
    have hδ : 0 < δ :=
      div_pos hε (mul_pos (by norm_num) hvnorm)
    let zplus : EuclideanThree := z₀ + δ • v
    have hzball : zplus ∈ ball := by
      rw [Metric.mem_ball, dist_eq_norm]
      have hsub : zplus - z₀ = δ • v := by simp [zplus]
      rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_pos hδ]
      change δ * ‖v‖ < ε
      rw [show δ * ‖v‖ = ε / 2 by
        dsimp [δ]
        field_simp]
      linarith
    have hz₀normal : (h.equiv.symm z₀).2 = 0 := by
      exact (c.normalCoordinate_eq_zero_iff
        c.image_mem_neighborhood).2 ⟨x, rfl⟩
    have hzpos : 0 < (h.equiv.symm zplus).2 := by
      simp only [zplus, map_add, map_smul, v,
        h.equiv.symm_apply_apply, Prod.smul_mk, smul_eq_mul,
        mul_one, Prod.snd_add]
      rw [hz₀normal, zero_add]
      exact hδ
    exact ⟨zplus, hzball, hzpos⟩
  have hcoordConnected : IsConnected (ball ∩ P) :=
    ((convex_ball z₀ ε).inter hconvP).isConnected hnonempty
  have himage : c.positiveHalf =
      h.codChart.symm '' (ball ∩ P) := by
    ext y
    constructor
    · rintro ⟨hyO, hyPos⟩
      rw [hneigh] at hyO
      rcases hyO with ⟨z, hz, rfl⟩
      refine ⟨z, ⟨hz, ?_⟩, rfl⟩
      change 0 <
        (h.equiv.symm (h.codChart (h.codChart.symm z))).2 at hyPos
      rw [h.codChart.right_inv (hballTarget hz)] at hyPos
      exact hyPos
    · rintro ⟨z, ⟨hz, hzPos⟩, rfl⟩
      refine ⟨?_, ?_⟩
      · rw [hneigh]
        exact ⟨z, hz, rfl⟩
      · change 0 <
          (h.equiv.symm (h.codChart (h.codChart.symm z))).2
        rw [h.codChart.right_inv (hballTarget hz)]
        exact hzPos
  rw [himage]
  exact hcoordConnected.image _
    (h.codChart.continuousOn_symm.mono
      (inter_subset_left.trans hballTarget))

private theorem isConnected_negativeHalf_of_neighborhood_eq_chart_symm_ball
    (c : EmbeddedSphereNormalChart e x) (ε : ℝ) (hε : 0 < ε)
    (hballTarget : Metric.ball (c.normalForm.codChart (e x)) ε ⊆
      c.normalForm.codChart.target)
    (hneigh : c.neighborhood = c.normalForm.codChart.symm ''
      Metric.ball (c.normalForm.codChart (e x)) ε) :
    IsConnected c.negativeHalf := by
  let h := c.normalForm
  let z₀ : EuclideanThree := h.codChart (e x)
  let ball : Set EuclideanThree := Metric.ball z₀ ε
  let P : Set EuclideanThree := {z | (h.equiv.symm z).2 < 0}
  have hconvP : Convex ℝ P := by
    let normalMap : EuclideanThree →ₗ[ℝ] ℝ :=
      (LinearMap.snd ℝ (EuclideanSpace ℝ (Fin 2)) ℝ).comp
        h.equiv.symm.toLinearEquiv.toLinearMap
    simpa [P, normalMap] using
      convex_halfSpace_lt normalMap.isLinear 0
  have hnonempty : (ball ∩ P).Nonempty := by
    let v : EuclideanThree := h.equiv (0, (1 : ℝ))
    have hvne : v ≠ 0 := by
      intro hv
      have hv' : ((0 : EuclideanSpace ℝ (Fin 2)), (1 : ℝ)) = 0 :=
        h.equiv.map_eq_zero_iff.mp hv
      have hone := congrArg Prod.snd hv'
      norm_num at hone
    have hvnorm : 0 < ‖v‖ := norm_pos_iff.mpr hvne
    let δ : ℝ := ε / (2 * ‖v‖)
    have hδ : 0 < δ :=
      div_pos hε (mul_pos (by norm_num) hvnorm)
    let zminus : EuclideanThree := z₀ - δ • v
    have hzball : zminus ∈ ball := by
      rw [Metric.mem_ball, dist_eq_norm]
      have hsub : zminus - z₀ = -(δ • v) := by simp [zminus]
      rw [hsub, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hδ]
      change δ * ‖v‖ < ε
      rw [show δ * ‖v‖ = ε / 2 by
        dsimp [δ]
        field_simp]
      linarith
    have hz₀normal : (h.equiv.symm z₀).2 = 0 := by
      exact (c.normalCoordinate_eq_zero_iff
        c.image_mem_neighborhood).2 ⟨x, rfl⟩
    have hzneg : (h.equiv.symm zminus).2 < 0 := by
      simp only [zminus, map_sub, map_smul, v,
        h.equiv.symm_apply_apply, Prod.smul_mk, smul_eq_mul,
        mul_one, Prod.snd_sub]
      rw [hz₀normal, zero_sub]
      exact neg_neg_of_pos hδ
    exact ⟨zminus, hzball, hzneg⟩
  have hcoordConnected : IsConnected (ball ∩ P) :=
    ((convex_ball z₀ ε).inter hconvP).isConnected hnonempty
  have himage : c.negativeHalf =
      h.codChart.symm '' (ball ∩ P) := by
    ext y
    constructor
    · rintro ⟨hyO, hyNeg⟩
      rw [hneigh] at hyO
      rcases hyO with ⟨z, hz, rfl⟩
      refine ⟨z, ⟨hz, ?_⟩, rfl⟩
      change
        (h.equiv.symm (h.codChart (h.codChart.symm z))).2 < 0 at hyNeg
      rw [h.codChart.right_inv (hballTarget hz)] at hyNeg
      exact hyNeg
    · rintro ⟨z, ⟨hz, hzNeg⟩, rfl⟩
      refine ⟨?_, ?_⟩
      · rw [hneigh]
        exact ⟨z, hz, rfl⟩
      · change
          (h.equiv.symm (h.codChart (h.codChart.symm z))).2 < 0
        rw [h.codChart.right_inv (hballTarget hz)]
        exact hzNeg
  rw [himage]
  exact hcoordConnected.image _
    (h.codChart.continuousOn_symm.mono
      (inter_subset_left.trans hballTarget))

end EmbeddedSphereNormalChart

theorem exists_normalChart_connectedHalves_subset
    [IsManifold (modelWithCornersSelf ℝ EuclideanThree) ∞ N]
    {e : SphereTwo → N} (he : IsSmoothEmbedding (𝓡 2)
      (modelWithCornersSelf ℝ EuclideanThree) ∞ e)
    (x : SphereTwo) {O : Set N} (hO : IsOpen O) (hxO : e x ∈ O) :
    ∃ c : EmbeddedSphereNormalChart e x, IsConnected c.positiveHalf ∧
      IsConnected c.negativeHalf ∧ c.neighborhood ⊆ O := by
  let c₀ := Classical.choice (embeddedSphereNormalChart_nonempty he x)
  let h := c₀.normalForm
  let z₀ : EuclideanThree := h.codChart (e x)
  have hO' : IsOpen (O ∩ c₀.neighborhood) := hO.inter c₀.isOpen_neighborhood
  have hsub' : O ∩ c₀.neighborhood ⊆ h.codChart.source := fun y hy =>
    c₀.neighborhood_subset_codChart_source hy.2
  have himg : IsOpen (h.codChart '' (O ∩ c₀.neighborhood)) :=
    h.codChart.isOpen_image_of_subset_source hO' hsub'
  have hz₀ : z₀ ∈ h.codChart '' (O ∩ c₀.neighborhood) :=
    ⟨e x, ⟨hxO, c₀.image_mem_neighborhood⟩, rfl⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 himg z₀ hz₀
  have hballTarget : Metric.ball z₀ ε ⊆ h.codChart.target := by
    intro z hz
    obtain ⟨y, hy, hyz⟩ := hball hz
    rw [← hyz]
    exact h.codChart.map_source (c₀.neighborhood_subset_codChart_source hy.2)
  let O' : Set N := h.codChart.symm '' Metric.ball z₀ ε
  have hO'open : IsOpen O' :=
    h.codChart.isOpen_image_symm_of_subset_target Metric.isOpen_ball hballTarget
  have hO'sub : O' ⊆ c₀.neighborhood := by
    rintro y ⟨z, hz, rfl⟩
    obtain ⟨y', hy', hy'z⟩ := hball hz
    rw [← hy'z, h.codChart.left_inv (c₀.neighborhood_subset_codChart_source hy'.2)]
    exact hy'.2
  have hO'O : O' ⊆ O := by
    rintro y ⟨z, hz, rfl⟩
    obtain ⟨y', hy', hy'z⟩ := hball hz
    rw [← hy'z, h.codChart.left_inv (c₀.neighborhood_subset_codChart_source hy'.2)]
    exact hy'.1
  let c : EmbeddedSphereNormalChart e x := {
    normalForm := h
    neighborhood := O'
    isOpen_neighborhood := hO'open
    image_mem_neighborhood :=
      ⟨z₀, Metric.mem_ball_self hε, h.codChart.left_inv h.mem_codChart_source⟩
    neighborhood_subset_codChart_source := fun y hy => by
      obtain ⟨z, hz, rfl⟩ := hy
      exact h.codChart.map_target (hballTarget hz)
    tangent_mem_domChart_target := fun y hy => c₀.tangent_mem_domChart_target y (hO'sub hy)
    neighborhood_inter_range_subset_image := fun _ hy =>
      c₀.neighborhood_inter_range_subset_image ⟨hO'sub hy.1, hy.2⟩ }
  refine ⟨c, ?_, ?_, fun y hy => hO'O hy⟩
  · apply EmbeddedSphereNormalChart.isConnected_positiveHalf_of_neighborhood_eq_chart_symm_ball
      c ε hε
    · simpa [c, h, z₀] using hballTarget
    · rfl
  · apply EmbeddedSphereNormalChart.isConnected_negativeHalf_of_neighborhood_eq_chart_symm_ball
      c ε hε
    · simpa [c, h, z₀] using hballTarget
    · rfl

end DifferentialGeometry.Topology.SphereSeparation
