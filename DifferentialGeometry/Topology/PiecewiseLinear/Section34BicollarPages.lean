import DifferentialGeometry.Topology.PiecewiseLinear.Section34CrossingCircleCore
import DifferentialGeometry.Topology.PiecewiseLinear.PLHomeomorphTopology
import DifferentialGeometry.Topology.Connected.ClosedCover

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem connectedComponentIn_iUnion_sdiff_eq_of_inter_eq
    {X ι : Type*} [TopologicalSpace X] [Finite ι] [Nontrivial ι]
    {P : ι → Set X} {J : Set X} (hclosed : ∀ i, IsClosed (P i))
    (hinter : ∀ i j, i ≠ j → P i ∩ P j = J)
    (hconn : ∀ i, IsPreconnected (P i \ J)) (i : ι) {x : X} (hx : x ∈ P i \ J) :
    connectedComponentIn ((⋃ j, P j) \ J) x = P i \ J := by
  let Q := ⋃ j, ⋃ (_ : j ≠ i), P j
  have hQ : IsClosed Q := isClosed_iUnion_of_finite fun j =>
    isClosed_iUnion_of_finite fun _ => hclosed j
  have hcover : P i ∪ Q = ⋃ j, P j := by
    ext y
    constructor
    · rintro (hy | hy)
      · exact mem_iUnion.mpr ⟨i, hy⟩
      · obtain ⟨j, -, hj⟩ := mem_iUnion₂.mp hy
        exact mem_iUnion.mpr ⟨j, hj⟩
    · intro hy
      obtain ⟨j, hj⟩ := mem_iUnion.mp hy
      by_cases hji : j = i
      · exact Or.inl (hji ▸ hj)
      · exact Or.inr (mem_iUnion₂.mpr ⟨j, hji, hj⟩)
  have hmeet : P i ∩ Q = J := by
    apply Subset.antisymm
    · rintro y ⟨hi, hy⟩
      obtain ⟨j, hji, hj⟩ := mem_iUnion₂.mp hy
      exact (hinter i j hji.symm).subset ⟨hi, hj⟩
    · intro y hy
      obtain ⟨j, hji⟩ := exists_ne i
      have h := (hinter i j hji.symm).symm.subset hy
      exact ⟨h.1, mem_iUnion₂.mpr ⟨j, hji, h.2⟩⟩
  have hdiff : P i \ Q = P i \ J := by
    ext y
    have h := Set.ext_iff.mp hmeet y
    simp only [mem_inter_iff, mem_sdiff] at h ⊢
    tauto
  have h := DifferentialGeometry.Topology.connectedComponentIn_sdiff_inter_eq_sdiff
    (hclosed i) hQ (hdiff.symm ▸ hconn i) (hdiff.symm ▸ hx)
  rwa [hcover, hmeet, hdiff] at h

theorem IsPLHomeomorphOn.centered_bicollar_half_images
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {J W : Set E} {ρ : E × ℝ → E} (hρ : IsPLHomeomorphOn ρ (J ×ˢ Icc (-1 : ℝ) 1) W)
    (hJ : IsPolyhedron J) (hconn : IsConnected J) (hzero : ∀ x ∈ J, ρ (x, 0) = x) :
    let A := ρ '' (J ×ˢ Icc (-1 : ℝ) 0)
    let B := ρ '' (J ×ˢ Icc (0 : ℝ) 1)
    IsPolyhedron A ∧ IsPolyhedron B ∧ A ∪ B = W ∧ A ∩ B = J ∧
      A \ J = ρ '' (J ×ˢ Ico (-1 : ℝ) 0) ∧ B \ J = ρ '' (J ×ˢ Ioc (0 : ℝ) 1) ∧
      IsConnected (A \ J) ∧ IsConnected (B \ J) ∧
      closure (A \ J) = A ∧ closure (B \ J) = B := by
  let A := ρ '' (J ×ˢ Icc (-1 : ℝ) 0)
  let B := ρ '' (J ×ˢ Icc (0 : ℝ) 1)
  have hneg : J ×ˢ Icc (-1 : ℝ) 0 ⊆ J ×ˢ Icc (-1 : ℝ) 1 :=
    fun _ hx => ⟨hx.1, hx.2.1, hx.2.2.trans zero_le_one⟩
  have hpos : J ×ˢ Icc (0 : ℝ) 1 ⊆ J ×ˢ Icc (-1 : ℝ) 1 :=
    fun _ hx => ⟨hx.1, (by norm_num : (-1 : ℝ) ≤ 0).trans hx.2.1, hx.2.2⟩
  have hneg' : J ×ˢ Ico (-1 : ℝ) 0 ⊆ J ×ˢ Icc (-1 : ℝ) 1 :=
    (prod_mono_right Ico_subset_Icc_self).trans hneg
  have hpos' : J ×ˢ Ioc (0 : ℝ) 1 ⊆ J ×ˢ Icc (-1 : ℝ) 1 :=
    (prod_mono_right Ioc_subset_Icc_self).trans hpos
  have hcore : ρ '' (J ×ˢ ({0} : Set ℝ)) = J := by
    ext x
    constructor
    · rintro ⟨⟨y, t⟩, ⟨hy, ht⟩, rfl⟩
      have ht0 : t = 0 := ht
      rw [ht0, hzero y hy]
      exact hy
    · exact fun hx => ⟨(x, 0), ⟨hx, rfl⟩, hzero x hx⟩
  have hcover : A ∪ B = W := by
    dsimp only [A, B]
    rw [← image_union, ← prod_union, Icc_union_Icc_eq_Icc (by norm_num) (by norm_num),
      hρ.image_eq]
  have hmeet : A ∩ B = J := by
    dsimp only [A, B]
    rw [← hρ.bijOn.injOn.image_inter hneg hpos, ← prod_inter]
    have hI : Icc (-1 : ℝ) 0 ∩ Icc 0 1 = {0} := by
      ext t
      simp only [mem_inter_iff, mem_Icc, mem_singleton_iff]
      constructor
      · exact fun h => le_antisymm h.1.2 h.2.1
      · rintro rfl
        norm_num
    rw [hI, hcore]
  have hn : A \ J = ρ '' (J ×ˢ Ico (-1 : ℝ) 0) := by
    nth_rw 1 [← hcore]
    change ρ '' (J ×ˢ Icc (-1 : ℝ) 0) \ ρ '' (J ×ˢ {0}) = _
    rw [← (hρ.bijOn.injOn.mono hneg).image_sdiff_subset (by
      rintro ⟨x, t⟩ ⟨hx, rfl⟩
      exact ⟨hx, by norm_num⟩)]
    congr 1
    ext p
    simp only [mem_sdiff, mem_prod, mem_Icc, mem_singleton_iff, mem_Ico]
    constructor
    · rintro ⟨⟨hp, hlo, hhi⟩, hn⟩
      exact ⟨hp, hlo, lt_of_le_of_ne hhi (fun heq => hn ⟨hp, heq⟩)⟩
    · rintro ⟨hp, hlo, hhi⟩
      exact ⟨⟨hp, hlo, hhi.le⟩, fun h => hhi.ne h.2⟩
  have hp : B \ J = ρ '' (J ×ˢ Ioc (0 : ℝ) 1) := by
    nth_rw 1 [← hcore]
    change ρ '' (J ×ˢ Icc (0 : ℝ) 1) \ ρ '' (J ×ˢ {0}) = _
    rw [← (hρ.bijOn.injOn.mono hpos).image_sdiff_subset (by
      rintro ⟨x, t⟩ ⟨hx, rfl⟩
      exact ⟨hx, by norm_num⟩)]
    congr 1
    ext p
    simp only [mem_sdiff, mem_prod, mem_Icc, mem_singleton_iff, mem_Ioc]
    constructor
    · rintro ⟨⟨hp, hlo, hhi⟩, hn⟩
      exact ⟨hp, lt_of_le_of_ne hlo (fun heq => hn ⟨hp, heq.symm⟩), hhi⟩
    · rintro ⟨hp, hlo, hhi⟩
      exact ⟨⟨hp, hlo.le, hhi⟩, fun h => hlo.ne' h.2⟩
  refine ⟨(hJ.prod isHPolytope_Icc.isPolyhedron).image_of_isPiecewiseAffineOn
    (hρ.isPiecewiseAffineOn.mono_of_isPolyhedron
      (hJ.prod isHPolytope_Icc.isPolyhedron) hneg) (hρ.bijOn.injOn.mono hneg),
    (hJ.prod isHPolytope_Icc.isPolyhedron).image_of_isPiecewiseAffineOn
      (hρ.isPiecewiseAffineOn.mono_of_isPolyhedron
        (hJ.prod isHPolytope_Icc.isPolyhedron) hpos) (hρ.bijOn.injOn.mono hpos),
    hcover, hmeet, hn, hp, ?_, ?_, ?_, ?_⟩
  · rw [hn]
    exact (hconn.prod (isConnected_Ico (by norm_num : (-1 : ℝ) < 0))).image ρ
      (hρ.isPiecewiseAffineOn.continuousOn.mono hneg')
  · rw [hp]
    exact (hconn.prod (isConnected_Ioc (by norm_num : (0 : ℝ) < 1))).image ρ
      (hρ.isPiecewiseAffineOn.continuousOn.mono hpos')
  · rw [hn, ← hρ.image_closure (hJ.isCompact.prod isCompact_Icc) hneg', closure_prod_eq,
      hJ.isClosed.closure_eq, closure_Ico (by norm_num : (-1 : ℝ) ≠ 0)]
  · rw [hp, ← hρ.image_closure (hJ.isCompact.prod isCompact_Icc) hpos', closure_prod_eq,
      hJ.isClosed.closure_eq, closure_Ioc (by norm_num : (0 : ℝ) ≠ 1)]

end DifferentialGeometry.Topology.PiecewiseLinear
