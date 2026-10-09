import DifferentialGeometry.Topology.PiecewiseLinear.Section34EssentialCircleAdjacency
import DifferentialGeometry.Topology.PiecewiseLinear.Section34AnnularBandComponents
import DifferentialGeometry.Topology.PiecewiseLinear.Section34InnermostDisk

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem IsPLSphere.exists_disk_neighborhood_avoiding_closed {S F : Set E}
    (hS : IsPLSphere 2 S) (hF : IsClosed F) {p : E} (hp : p ∈ S) (hpF : p ∉ F) :
    ∃ (D : Set E) (q : (Fin 3 → ℝ) → E),
      IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D ∧ D ⊆ S ∧ Disjoint D F ∧
      p ∈ D ∧ p ∉ q '' stdSimplexBoundary 2 := by
  obtain ⟨K, hKfin, hKS⟩ := hS.isPolyhedron.exists_simplicialComplex
  let _ : Finite K.faces := hKfin.to_subtype
  have hK := (hKS.symm ▸ hS).isCombinatorialManifold (K := K)
  obtain ⟨D, hD, hsub, hnhds⟩ := hK.exists_isPLBall_subset_of_mem_nhds
    (hKS.symm ▸ hp) (hF.isOpen_compl.mem_nhds hpF)
  rw [hKS] at hsub hnhds
  obtain ⟨q, hq⟩ := hD
  refine ⟨D, q, hq, hsub.trans inter_subset_left,
    disjoint_left.mpr (fun x hx => (hsub hx).2), mem_of_mem_nhdsWithin hp hnhds, ?_⟩
  intro hpBd
  have hpcl : p ∈ closure (S \ D) := by
    have hmeet := hS.inter_closure_sdiff_eq_image_stdSimplexBoundary hq
      (hsub.trans inter_subset_left)
    exact (hmeet.symm ▸ hpBd).2
  obtain ⟨V, hV, hVD⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hnhds
  obtain ⟨x, hxV, hxS, hxD⟩ := mem_closure_iff_nhds.mp hpcl V hV
  exact hxD (hVD ⟨hxV, hxS⟩)

theorem IsPLSphere.exists_annulus_avoiding_pair {S C : Set E}
    (hS : IsPLSphere 2 S) (hC : IsClosed C) (hCS : C ⊆ S)
    {x y : E} (hxS : x ∈ S) (hyS : y ∈ S) (hxy : x ≠ y)
    (hxC : x ∉ C) (hyC : y ∉ C) :
    ∃ A A₀ A₁ : Set E, IsAnnulusOn A A₀ A₁ ∧ A ⊆ S ∧ C ⊆ A ∧
      Disjoint C (A₀ ∪ A₁) ∧ x ∉ A ∧ y ∉ A := by
  obtain ⟨D₀, q₀, hq₀, hD₀S, hD₀C, hxD₀, hxBd₀⟩ :=
    hS.exists_disk_neighborhood_avoiding_closed (hC.union isClosed_singleton) hxS
      (fun h => h.elim hxC hxy)
  have hyD₀ : y ∉ D₀ := fun hy => disjoint_left.mp hD₀C hy (Or.inr rfl)
  obtain ⟨D₁, q₁, hq₁, hD₁S, hD₁C, hyD₁, hyBd₁⟩ :=
    hS.exists_disk_neighborhood_avoiding_closed
      (hC.union (IsPLBall.isPolyhedron ⟨q₀, hq₀⟩).isClosed) hyS
      (fun h => h.elim hyC hyD₀)
  obtain ⟨φ, hφ, hφS, hφ₀, hφ₁, hB₀, hB₁, hcover⟩ :=
    exists_isPLHomeomorphOn_lateral_annulus_cover_of_disjoint_disks hS hq₀ hq₁ rfl rfl
      hD₀S hD₁S (hD₁C.mono_right subset_union_right).symm
  have hann := isAnnulusOn_stdSimplex_lateral.image_of_continuousOn_injOn
    hφ.isPiecewiseAffineOn.continuousOn hφ.bijOn.injOn
  rw [hφ₀, hφ₁] at hann
  refine ⟨_, _, _, hann, hφS, ?_, ?_, ?_, ?_⟩
  · intro z hz
    rcases hcover (hCS hz) with (hz₀ | hz₁) | hzA
    · exact (disjoint_left.mp hD₀C hz₀ (Or.inl hz)).elim
    · exact (disjoint_left.mp hD₁C hz₁ (Or.inl hz)).elim
    · exact hzA
  · refine disjoint_left.mpr ?_
    rintro z hz (hz₀ | hz₁)
    · have hzD : z ∈ D₀ := hq₀.image_eq ▸ image_mono (fun _ h => h.1) hz₀
      exact disjoint_left.mp hD₀C hzD (Or.inl hz)
    · have hzD : z ∈ D₁ := hq₁.image_eq ▸ image_mono (fun _ h => h.1) hz₁
      exact disjoint_left.mp hD₁C hzD (Or.inl hz)
  · exact fun hxA => hxBd₀ (hB₀ ▸ ⟨hxA, hxD₀⟩)
  · exact fun hyA => hyBd₁ (hB₁ ▸ ⟨hyA, hyD₁⟩)


theorem IsPLSphere.exists_innermost_disk_or_band_avoiding_pair {S : Set E}
    (hS : IsPLSphere 2 S) (C : Set (Set E)) (hC : C.Finite) (hcard : 1 < C.ncard)
    (hCsph : ∀ J ∈ C, IsPLSphere 1 J) (hCS : ∀ J ∈ C, J ⊆ S)
    (hCdisj : C.PairwiseDisjoint id) {x y : E} (hxS : x ∈ S) (hyS : y ∈ S)
    (hxy : x ≠ y) (hxC : x ∉ ⋃₀ C) (hyC : y ∉ ⋃₀ C) :
    (∃ J ∈ C, ∃ (D : Set E) (q : (Fin 3 → ℝ) → E),
      IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D ∧ D ⊆ S ∧
        q '' stdSimplexBoundary 2 = J ∧ x ∉ D ∧ y ∉ D ∧
          ∀ L ∈ C, L ≠ J → Disjoint D L) ∨
    ∃ J ∈ C, ∃ L ∈ C, J ≠ L ∧ ∃ φ : (Fin 3 → ℝ) × ℝ → E,
      IsPLHomeomorphOn φ (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)
        (φ '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)) ∧
      φ '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ⊆ S ∧
      φ '' (stdSimplexBoundary 2 ×ˢ {0}) = J ∧
      φ '' (stdSimplexBoundary 2 ×ˢ {1}) = L ∧
      x ∉ φ '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ∧
      y ∉ φ '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ∧
      Disjoint (φ '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1)) (⋃₀ C) := by
  classical
  have hclosed : IsClosed (⋃₀ C) := by
    rw [sUnion_eq_biUnion]
    exact hC.isClosed_biUnion fun J hJ => (hCsph J hJ).isPolyhedron.isClosed
  obtain ⟨A, A₀, A₁, hA, hAS, hCA, hends, hxA, hyA⟩ :=
    hS.exists_annulus_avoiding_pair hclosed (sUnion_subset hCS) hxS hyS hxy hxC hyC
  have hJA : ∀ J ∈ C, J ⊆ A := fun J hJ => (subset_sUnion_of_mem hJ).trans hCA
  have hJend : ∀ J ∈ C, Disjoint J (A₀ ∪ A₁) := fun J hJ =>
    hends.mono_left (subset_sUnion_of_mem hJ)
  by_cases hex : ∃ J ∈ C, ∃ (D : Set E) (q : (Fin 3 → ℝ) → E),
      IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D ∧ D ⊆ A ∧
        q '' stdSimplexBoundary 2 = J
  · let _ : Finite C := hC.to_subtype
    obtain ⟨i, D, q, hq, hDA, hqJ, hdis⟩ :=
      hS.exists_innermost_disk_subset hAS (J := fun J : C => J.val)
        (fun J => hCsph J J.property) (fun J => hCS J J.property)
        (fun J L hne => hCdisj J.property L.property (fun h => hne (Subtype.ext h)))
        (by
          obtain ⟨J, hJ, D, q, hq, hDA, hqJ⟩ := hex
          exact ⟨⟨J, hJ⟩, D, q, hq, hDA, hqJ⟩)
    exact Or.inl ⟨i.val, i.property, D, q, hq, hDA.trans hAS, hqJ,
      fun hx => hxA (hDA hx), fun hy => hyA (hDA hy),
      fun L hL hne => hdis ⟨L, hL⟩ (fun h => hne (congrArg Subtype.val h))⟩
  · obtain ⟨J, hJ, L, hL, hJL, φ, hφ, hφA, hzero, hone, hdis⟩ :=
      hS.exists_empty_annular_band_of_essential_family hA hAS C hC hcard hCsph hJA hJend
        hCdisj (fun J hJ h => hex ⟨J, hJ, h⟩)
    exact Or.inr ⟨J, hJ, L, hL, hJL, φ, hφ, hφA.trans hAS, hzero, hone,
      fun hx => hxA (hφA hx), fun hy => hyA (hφA hy), hdis⟩

end DifferentialGeometry.Topology.PiecewiseLinear
