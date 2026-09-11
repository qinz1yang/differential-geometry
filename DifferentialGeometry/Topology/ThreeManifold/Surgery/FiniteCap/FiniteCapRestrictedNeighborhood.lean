import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCapChartOverlap

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace
open DifferentialGeometry.Geometry.Neck
namespace DifferentialGeometry.Topology.ThreeManifold.Surgery
private abbrev RestrictedE3 := EuclideanSpace ℝ (Fin 3)
private abbrev RestrictedS2 := Metric.sphere (0 : RestrictedE3) 1
private abbrev RestrictedCollar (δ : ℝ) := RestrictedS2 × Ico (0 : ℝ) (cuttingCollarWidth δ)
variable {ι M : Type*} [Finite ι] [TopologicalSpace M] [T2Space M]
variable {precision : ι → ℝ} {L : ℝ}
variable (hL : 0 < L) (hδ : ∀ i, 0 < precision i)
variable (f : ∀ i : ι, bufferedCylinder (precision i) → M)
variable (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
variable (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
local notation "RestrictedQ" => FiniteCapQuotient hL hδ f (fun i => _root_.Topology.IsEmbedding.injective (_root_.Topology.IsOpenEmbedding.toIsEmbedding (hf i))) hdisj

def finiteCapRestrictedNeighborhood (b : ι × Bool) (r : ℝ) : Opens RestrictedQ :=
  let c := finiteCapOpenChart hL hδ f hf hdisj b
  ⟨c.source ∩ c ⁻¹' {x | ‖x‖ < L + r},
    c.continuousOn.isOpen_inter_preimage c.open_source (isOpen_lt continuous_norm continuous_const)⟩

theorem mem_finiteCapRestrictedNeighborhood_iff (b : ι × Bool) (r : ℝ) (q : RestrictedQ) :
    q ∈ finiteCapRestrictedNeighborhood hL hδ f hf hdisj b r ↔
      q ∈ finiteCapNeighborhood hL hδ f (fun i => (hf i).injective) hdisj b ∧
        ‖finiteCapOpenChart hL hδ f hf hdisj b q‖ < L + r := by
  change q ∈ (finiteCapOpenChart hL hδ f hf hdisj b).source ∧ _ ↔ _
  rw [finiteCapOpenChart_source]
  rfl

theorem finiteCapInclusion_mem_restrictedNeighborhood (b : ι × Bool) {r : ℝ} (hr : 0 < r)
    (x : {v : RestrictedE3 // ‖v‖ ≤ L}) :
    finiteCapInclusion hL hδ f (fun i => (hf i).injective) hdisj ⟨b, x⟩ ∈
      finiteCapRestrictedNeighborhood hL hδ f hf hdisj b r := by
  rw [mem_finiteCapRestrictedNeighborhood_iff, finiteCapOpenChart_cap]
  exact ⟨Or.inl ⟨x, rfl⟩, x.property.trans_lt (lt_add_of_pos_right L hr)⟩

theorem finiteCapRestrictedNeighborhood_collar_iff (b : ι × Bool) (r : ℝ)
    (q : RestrictedCollar (precision b.1)) :
    finiteCoreInclusion hL hδ f (fun i => (hf i).injective) hdisj
      (cuttingCollarMap hδ f (fun i => (hf i).injective) hdisj b q) ∈
      finiteCapRestrictedNeighborhood hL hδ f hf hdisj b r ↔ q.2.val < r := by
  rw [mem_finiteCapRestrictedNeighborhood_iff, finiteCapOpenChart_collar]
  have hnorm : ‖(L + q.2.val) • q.1.val‖ = L + q.2.val := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (add_pos_of_pos_of_nonneg hL q.2.property.1),
      mem_sphere_zero_iff_norm.mp q.1.property, mul_one]
  rw [hnorm]
  exact ⟨fun h => (add_lt_add_iff_left L).mp h.2,
    fun h => ⟨Or.inr ⟨q, rfl⟩, (add_lt_add_iff_left L).mpr h⟩⟩

theorem finiteCapRestrictedNeighborhood_core_preimage (b : ι × Bool) (r : ℝ) :
    finiteCoreInclusion hL hδ f (fun i => (hf i).injective) hdisj ⁻¹'
      (finiteCapRestrictedNeighborhood hL hδ f hf hdisj b r : Set RestrictedQ) =
        cuttingCollarMap hδ f (fun i => (hf i).injective) hdisj b '' {q | q.2.val < r} := by
  ext p
  constructor
  · intro hp
    have hn := ((mem_finiteCapRestrictedNeighborhood_iff hL hδ f hf hdisj b r _).mp hp).1
    change p ∈ finiteCoreInclusion hL hδ f (fun i => (hf i).injective) hdisj ⁻¹'
      finiteCapNeighborhood hL hδ f (fun i => (hf i).injective) hdisj b at hn
    rw [finiteCapNeighborhood_core_preimage] at hn
    obtain ⟨q, rfl⟩ := hn
    exact ⟨q, (finiteCapRestrictedNeighborhood_collar_iff hL hδ f hf hdisj b r q).mp hp, rfl⟩
  · rintro ⟨q, hq, rfl⟩
    exact (finiteCapRestrictedNeighborhood_collar_iff hL hδ f hf hdisj b r q).mpr hq

theorem pairwise_disjoint_finiteCapRestrictedNeighborhoods (r : ι × Bool → ℝ) :
    Pairwise (fun b c : ι × Bool => Disjoint
      (finiteCapRestrictedNeighborhood hL hδ f hf hdisj b (r b) : Set RestrictedQ)
      (finiteCapRestrictedNeighborhood hL hδ f hf hdisj c (r c) : Set RestrictedQ)) := by
  intro b c hbc
  apply (pairwise_disjoint_finiteCapOpenChart_sources hL hδ f hf hdisj hbc).mono
  · exact inter_subset_left
  · exact inter_subset_left

theorem finiteCapRestrictedNeighborhood_cover (r : ι × Bool → ℝ) (hr : ∀ b, 0 < r b) :
    finiteCoreInterior hL hδ f (fun i => (hf i).injective) hdisj ∪
      (⋃ b, (finiteCapRestrictedNeighborhood hL hδ f hf hdisj b (r b) : Set RestrictedQ)) = univ := by
  apply eq_univ_iff_forall.mpr
  intro p
  have hp := eq_univ_iff_forall.mp (finiteCapOpenChart_source_cover hL hδ f hf hdisj) p
  rcases hp with hp | hp
  · exact Or.inl hp
  · obtain ⟨b, hb⟩ := mem_iUnion.mp hp
    rw [finiteCapOpenChart_source] at hb
    rcases hb with ⟨x, rfl⟩ | ⟨q, rfl⟩
    · exact Or.inr (mem_iUnion.mpr ⟨b, finiteCapInclusion_mem_restrictedNeighborhood hL hδ f hf hdisj b (hr b) x⟩)
    · by_cases hq : q.2.val < r b
      · exact Or.inr (mem_iUnion.mpr ⟨b,
          (finiteCapRestrictedNeighborhood_collar_iff hL hδ f hf hdisj b (r b) q).mpr hq⟩)
      · exact Or.inl ((finiteCoreInterior_collar_iff hL hδ f hf hdisj b q).mpr
          ((hr b).trans_le (le_of_not_gt hq)))
end DifferentialGeometry.Topology.ThreeManifold.Surgery
