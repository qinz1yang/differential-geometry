import DifferentialGeometry.Topology.SphereSeparation.BicollarOrientation
import DifferentialGeometry.Topology.SphereSeparation.Incidence

set_option autoImplicit false

open Function Set Topology
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.SphereSeparation

variable {N : Type*} {a : ℝ} (Φ : SphereTwo × AxialInterval a → N)

private theorem lowerHalfImage_disjoint_upperHalfImage
    (hΦ : Function.Injective Φ) (c : AxialInterval a) :
    Disjoint (lowerHalfImage Φ c) (upperHalfImage Φ c) := by
  rw [Set.disjoint_left]
  intro y hyLower hyUpper
  rcases hyLower with ⟨p, hp, rfl⟩
  rcases hyUpper with ⟨q, hq, hqp⟩
  have hpq : q = p := hΦ hqp
  have hlt : p.2 < c := hp.2
  have hgt : c < q.2 := hq.2
  rw [hpq] at hgt
  exact (not_lt_of_ge hgt.le) hlt

private theorem range_diff_sliceImage
    (hΦ : Function.Injective Φ) (c : AxialInterval a) :
    Set.range Φ \ sliceImage Φ c =
      lowerHalfImage Φ c ∪ upperHalfImage Φ c := by
  ext y
  constructor
  · rintro ⟨⟨p, rfl⟩, hpNotSlice⟩
    rcases lt_trichotomy p.2 c with hp | hp | hp
    · exact Or.inl ⟨p, ⟨Set.mem_univ _, hp⟩, rfl⟩
    · exfalso
      apply hpNotSlice
      exact ⟨p, ⟨Set.mem_univ _, hp⟩, rfl⟩
    · exact Or.inr ⟨p, ⟨Set.mem_univ _, hp⟩, rfl⟩
  · rintro (⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩)
    · refine ⟨⟨p, rfl⟩, ?_⟩
      rintro ⟨q, hq, hqp⟩
      have hpq : q = p := hΦ hqp
      have hqc : q.2 = c := hq.2
      have hplt : p.2 < c := hp.2
      rw [← hpq, hqc] at hplt
      exact lt_irrefl _ hplt
    · refine ⟨⟨p, rfl⟩, ?_⟩
      rintro ⟨q, hq, hqp⟩
      have hpq : q = p := hΦ hqp
      have hqc : q.2 = c := hq.2
      have hcplt : c < p.2 := hp.2
      rw [← hpq, hqc] at hcplt
      exact lt_irrefl _ hcplt

private theorem self_mem_closure_Iio_axial (c : AxialInterval a) :
    c ∈ closure (Iio c : Set (AxialInterval a)) := by
  rw [IsEmbedding.subtypeVal.closure_eq_preimage_closure_image]
  change (c : ℝ) ∈ closure
    ((Subtype.val : AxialInterval a → ℝ) '' Iio c)
  have himage :
      (Subtype.val : AxialInterval a → ℝ) '' Iio c =
        Ioo (-a) (c : ℝ) := by
    ext r
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨q.2.1, hq⟩
    · intro hr
      exact ⟨⟨r, hr.1, lt_trans hr.2 c.2.2⟩, hr.2, rfl⟩
  rw [himage, closure_Ioo (ne_of_lt c.2.1)]
  exact ⟨c.2.1.le, le_rfl⟩

private theorem self_mem_closure_Ioi_axial (c : AxialInterval a) :
    c ∈ closure (Ioi c : Set (AxialInterval a)) := by
  rw [IsEmbedding.subtypeVal.closure_eq_preimage_closure_image]
  change (c : ℝ) ∈ closure
    ((Subtype.val : AxialInterval a → ℝ) '' Ioi c)
  have himage :
      (Subtype.val : AxialInterval a → ℝ) '' Ioi c =
        Ioo (c : ℝ) a := by
    ext r
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨hq, q.2.2⟩
    · intro hr
      exact ⟨⟨r, lt_trans c.2.1 hr.1, hr.2⟩, hr.1, rfl⟩
  rw [himage, closure_Ioo (ne_of_lt c.2.2)]
  exact ⟨le_rfl, c.2.2.le⟩

private theorem sliceImage_subset_closure_lowerHalfImage
    [TopologicalSpace N]
    (hΦ : Continuous Φ) (c : AxialInterval a) :
    sliceImage Φ c ⊆ closure (lowerHalfImage Φ c) := by
  rintro y ⟨p, hp, rfl⟩
  have hpEq : p = (p.1, c) := by
    apply Prod.ext
    · rfl
    · exact hp.2
  rw [hpEq]
  have hsource : (p.1, c) ∈ closure (lowerHalfDomain c) := by
    rw [lowerHalfDomain, closure_prod_eq, closure_univ]
    exact ⟨Set.mem_univ _, self_mem_closure_Iio_axial c⟩
  exact map_mem_closure hΦ hsource fun q hq => ⟨q, hq, rfl⟩

private theorem sliceImage_subset_closure_upperHalfImage
    [TopologicalSpace N]
    (hΦ : Continuous Φ) (c : AxialInterval a) :
    sliceImage Φ c ⊆ closure (upperHalfImage Φ c) := by
  rintro y ⟨p, hp, rfl⟩
  have hpEq : p = (p.1, c) := by
    apply Prod.ext
    · rfl
    · exact hp.2
  rw [hpEq]
  have hsource : (p.1, c) ∈ closure (upperHalfDomain c) := by
    rw [upperHalfDomain, closure_prod_eq, closure_univ]
    exact ⟨Set.mem_univ _, self_mem_closure_Ioi_axial c⟩
  exact map_mem_closure hΦ hsource fun q hq => ⟨q, hq, rfl⟩

theorem locallyTwoSided_sliceImage
    [TopologicalSpace N] [ChartedSpace EuclideanThree N]
    (hΦ : Manifold.IsSmoothEmbedding
      ((𝓘(ℝ, EuclideanSpace ℝ (Fin 2))).prod 𝓘(ℝ))
      (𝓘(ℝ, EuclideanThree)) ∞ Φ)
    (c : AxialInterval a) :
    LocallyTwoSided (sliceImage Φ c) := by
  have hcont : Continuous Φ := hΦ.contMDiff.continuous
  have hopen : IsOpen (Set.range Φ) := by
    have hrank :
        Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × ℝ) =
          Module.finrank ℝ EuclideanThree := by
      norm_num [Module.finrank_prod, Module.finrank_fin_fun, EuclideanThree]
    exact Manifold.isOpen_range_of_isSmoothEmbedding
      (I := ((𝓘(ℝ, EuclideanSpace ℝ (Fin 2))).prod 𝓘(ℝ)))
      (J := 𝓘(ℝ, EuclideanThree)) hrank hΦ
  intro y hy
  exact ⟨{
    neighborhood := Set.range Φ
    negative := lowerHalfImage Φ c
    positive := upperHalfImage Φ c
    isOpen_neighborhood := hopen
    mem_neighborhood := by
      rcases hy with ⟨p, -, rfl⟩
      exact ⟨p, rfl⟩
    isConnected_negative := isConnected_lowerHalfImage Φ hcont c
    isConnected_positive := isConnected_upperHalfImage Φ hcont c
    disjoint := lowerHalfImage_disjoint_upperHalfImage Φ
      hΦ.isEmbedding.injective c
    punctured_eq := range_diff_sliceImage Φ hΦ.isEmbedding.injective c
    central_subset_closure_negative := fun _ hz =>
      sliceImage_subset_closure_lowerHalfImage Φ hcont c hz.2
    central_subset_closure_positive := fun _ hz =>
      sliceImage_subset_closure_upperHalfImage Φ hcont c hz.2
  }⟩

end DifferentialGeometry.Topology.SphereSeparation
