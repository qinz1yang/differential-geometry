import DifferentialGeometry.Topology.BicollaredComplement
import DifferentialGeometry.Topology.VanKampen.TwoSidedCollarRescale
import Mathlib.Topology.Order.Compact

open Set Filter Topology

namespace DifferentialGeometry.Topology

variable {S X : Type*} [TopologicalSpace S] [TopologicalSpace X] {e : S → X}

theorem ThreeManifold.TwoSidedCollar.isEmbedding_e (c : ThreeManifold.TwoSidedCollar e) :
    IsEmbedding e := by
  have h := c.isOpenEmbedding_toFun.isEmbedding.comp (isEmbedding_prodMkLeft (0 : ℝ))
  simpa only [Function.comp_def, c.zero_eq] using h

theorem ThreeManifold.TwoSidedCollar.isBicollared_range (c : ThreeManifold.TwoSidedCollar e) :
    IsBicollared (Set.range e) := by
  let d := c.isEmbedding_e.toHomeomorph
  let p := d.symm.prodCongr (Homeomorph.refl ℝ)
  refine ⟨⟨c.toFun ∘ p, c.isOpenEmbedding_toFun.comp p.isOpenEmbedding, ?_⟩⟩
  intro x
  change c.toFun (d.symm x, 0) = (x : X)
  rw [c.zero_eq]
  exact congrArg Subtype.val (d.apply_symm_apply x)

theorem exists_twoSidedCollar_of_closedInterval [CompactSpace S]
    {a : ℝ} (ha : 0 < a) (ρ : S × Icc (-a) a → X) (hρ : IsEmbedding ρ)
    (hzero : ∀ s, ρ (s, ⟨0, by constructor <;> linarith⟩) = e s)
    (hneighborhood : Set.range ρ ∈ 𝓝ˢ (Set.range e)) :
    ∃ c : ThreeManifold.TwoSidedCollar e, Set.range c.toFun ⊆ Set.range ρ := by
  let t₀ : Icc (-a) a := ⟨0, by constructor <;> linarith⟩
  let G := ρ ⁻¹' interior (Set.range ρ)
  have hG : G ∈ (𝓝ˢ (univ : Set S)) ×ˢ 𝓝 t₀ := by
    apply isCompact_univ.mem_nhdsSet_prod_of_forall
    intro s _
    rw [← nhds_prod_eq]
    apply (isOpen_interior.preimage hρ.continuous).mem_nhds
    change ρ (s, t₀) ∈ interior (Set.range ρ)
    rw [show ρ (s, t₀) = e s from hzero s]
    exact subset_interior_iff_mem_nhdsSet.mpr hneighborhood ⟨s, rfl⟩
  obtain ⟨A, hA, V, hV, hAV⟩ := mem_prod_iff.mp hG
  have hV' : V ∈ comap (Subtype.val : Icc (-a) a → ℝ) (𝓝 0) := by
    rw [show 𝓝 t₀ = comap (Subtype.val : Icc (-a) a → ℝ) (𝓝 0) from
      nhds_subtype_eq_comap] at hV
    exact hV
  obtain ⟨B, hB, hBV⟩ := mem_comap.mp hV'
  obtain ⟨δ, hδ, hδB⟩ := Metric.mem_nhds_iff.mp hB
  let ε := min a δ
  have hε : 0 < ε := lt_min ha hδ
  have hεa : ε ≤ a := min_le_left _ _
  have hεδ : ε ≤ δ := min_le_right _ _
  have hinterval : Ioo (-ε) ε ⊆ Icc (-a) a := fun t ht =>
    ⟨(neg_le_neg hεa).trans ht.1.le, ht.2.le.trans hεa⟩
  let j : Ioo (-ε) ε → Icc (-a) a := Set.inclusion hinterval
  have hj : IsOpenEmbedding j :=
    IsOpenEmbedding.inclusion hinterval (isOpen_Ioo.preimage continuous_subtype_val)
  let k : S × Ioo (-ε) ε → S × Icc (-a) a := Prod.map id j
  have hk : IsOpenEmbedding k := IsOpenEmbedding.id.prodMap hj
  have hkin (p : S × Ioo (-ε) ε) : ρ (k p) ∈ interior (Set.range ρ) := by
    apply hAV
    refine ⟨subset_of_mem_nhdsSet hA (mem_univ _), hBV (hδB ?_)⟩
    change dist (p.2 : ℝ) 0 < δ
    rw [Real.dist_eq, sub_zero, abs_lt]
    exact ⟨(neg_le_neg hεδ).trans_lt p.2.2.1, p.2.2.2.trans_le hεδ⟩
  have hopen : IsOpen (Set.range (ρ ∘ k)) := by
    obtain ⟨O, hO, hOr⟩ := hρ.isInducing.image_eq_isOpen_inter_range hk.isOpen_range
    have hsub : O ∩ Set.range ρ ⊆ interior (Set.range ρ) := by
      rw [← hOr]
      rintro _ ⟨_, ⟨p, rfl⟩, rfl⟩
      exact hkin p
    have heq : O ∩ Set.range ρ = O ∩ interior (Set.range ρ) :=
      Subset.antisymm (fun _ hx => ⟨hx.1, hsub hx⟩)
        (inter_subset_inter_right _ interior_subset)
    rw [Set.range_comp, hOr, heq]
    exact hO.inter isOpen_interior
  let c : ThreeManifold.TwoSidedCollar e :=
    ThreeManifold.TwoSidedCollar.ofOpenInterval hε (ρ ∘ k)
      ⟨hρ.comp hk.isEmbedding, hopen⟩ (fun s => hzero s)
  refine ⟨c, ?_⟩
  rintro _ ⟨p, rfl⟩
  exact ⟨_, rfl⟩

theorem ThreeManifold.TwoSidedCollar.isBicollared_image
    {Y : Type*} [TopologicalSpace Y] (c : ThreeManifold.TwoSidedCollar e)
    {U : Set X} (hU : Set.range c.toFun ⊆ U) {f : X → Y}
    (hf : IsOpenEmbedding (fun x : U => f x)) : IsBicollared (f '' Set.range e) := by
  let g : S × ℝ → U := fun p => ⟨c.toFun p, hU ⟨p, rfl⟩⟩
  have hg : IsOpenEmbedding g :=
    IsOpenEmbedding.of_isEmbedding_isOpenMap
      (c.isOpenEmbedding_toFun.isEmbedding.codRestrict U _)
      (c.isOpenEmbedding_toFun.isOpenMap.codRestrict _)
  let d : ThreeManifold.TwoSidedCollar (f ∘ e) :=
    ⟨(fun x : U => f x) ∘ g, hf.comp hg, fun s => congrArg f (c.zero_eq s)⟩
  have h := d.isBicollared_range
  rwa [Set.range_comp] at h

end DifferentialGeometry.Topology
