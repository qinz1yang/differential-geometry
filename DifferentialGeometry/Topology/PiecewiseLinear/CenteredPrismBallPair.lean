import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceSplitCenteredPrism
import DifferentialGeometry.Topology.PiecewiseLinear.ExhaustionGeneral
import DifferentialGeometry.Topology.PiecewiseLinear.PieceParametrization
import DifferentialGeometry.Topology.PiecewiseLinear.PolyhedralBallTopology

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

private theorem centered_prism_piece_in
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {X : Type*} [TopologicalSpace X] [T2Space X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {Y : Set X} (R : PLPieceIn F 3 X Y)
    {P : Set E} (hP : IsPLBall 2 P) {C₀ C₁ : Set X}
    (h₀ : IsPolyhedralBall (n := 3) 3 C₀) (h₁ : IsPolyhedralBall (n := 3) 3 C₁)
    (hD : IsPolyhedralBall (n := 3) 2 (C₀ ∩ C₁))
    (hD₀ : C₀ ∩ C₁ ⊆ frontier C₀) (hD₁ : C₀ ∩ C₁ ⊆ frontier C₁)
    (hCY : C₀ ∪ C₁ ⊆ Y) :
    ∃ T : PLPieceIn (E × ℝ) 3 X (C₀ ∪ C₁),
      T.complex.space = P ×ˢ Icc (-1 : ℝ) 1 ∧
      T.map '' (P ×ˢ Icc (-1 : ℝ) 0) = C₀ ∧
      T.map '' (P ×ˢ Icc (0 : ℝ) 1) = C₁ ∧
      T.map '' (P ×ˢ {(0 : ℝ)}) = C₀ ∩ C₁ := by
  classical
  have h₀Y : C₀ ⊆ Y := subset_union_left.trans hCY
  have h₁Y : C₁ ⊆ Y := subset_union_right.trans hCY
  obtain ⟨S₀, hspace₀, hmap₀⟩ := R.exists_restrict_of_isPolyhedralBall h₀ h₀Y
  obtain ⟨S₁, hspace₁, hmap₁⟩ := R.exists_restrict_of_isPolyhedralBall h₁ h₁Y
  let : Finite S₀.complex.faces := S₀.finite_faces.to_subtype
  let : Finite S₁.complex.faces := S₁.finite_faces.to_subtype
  have hK₀ : IsPLBall 3 S₀.complex.space :=
    hspace₀.symm ▸ h₀.isPLBall_inter_preimage R h₀Y
  have hK₁ : IsPLBall 3 S₁.complex.space :=
    hspace₁.symm ▸ h₁.isPLBall_inter_preimage R h₁Y
  have hinter : S₀.complex.space ∩ S₁.complex.space =
      R.complex.space ∩ R.map ⁻¹' (C₀ ∩ C₁) := by
    rw [hspace₀, hspace₁]
    ext x
    simp only [mem_inter_iff, mem_preimage]
    tauto
  have hKD : IsPLBall 2 (S₀.complex.space ∩ S₁.complex.space) := by
    rw [hinter]
    exact hD.isPLBall_inter_preimage R (inter_subset_left.trans h₀Y)
  have hDK₀ : S₀.complex.space ∩ S₁.complex.space ⊆
      (boundaryComplex 3 S₀.complex).space := by
    intro x hx
    have hxfront : S₀.map x ∈ frontier C₀ := by
      rw [hmap₀]
      exact hD₀ ⟨(hspace₀.subset hx.1).2, (hspace₁.subset hx.2).2⟩
    rw [S₀.frontier_eq_image_boundaryComplex hK₀.isCombinatorialManifoldWithBoundary] at hxfront
    obtain ⟨y, hy, hyx⟩ := hxfront
    exact S₀.bijOn.injOn (boundaryComplex_space_subset 3 S₀.complex hy) hx.1 hyx ▸ hy
  have hDK₁ : S₀.complex.space ∩ S₁.complex.space ⊆
      (boundaryComplex 3 S₁.complex).space := by
    intro x hx
    have hxfront : S₁.map x ∈ frontier C₁ := by
      rw [hmap₁]
      exact hD₁ ⟨(hspace₀.subset hx.1).2, (hspace₁.subset hx.2).2⟩
    rw [S₁.frontier_eq_image_boundaryComplex hK₁.isCombinatorialManifoldWithBoundary] at hxfront
    obtain ⟨y, hy, hyx⟩ := hxfront
    exact S₁.bijOn.injOn (boundaryComplex_space_subset 3 S₁.complex hy) hx.2 hyx ▸ hy
  obtain ⟨p, hp⟩ := hP
  obtain ⟨d, hd⟩ := hKD
  obtain ⟨ρ, hρ, -, hlower, hupper⟩ :=
    exists_isPLHomeomorphOn_centered_prism_of_boundary_disk_pair ⟨p, hp⟩
      S₀.complex S₁.complex hK₀ hK₁ hDK₀ hDK₁ rfl (hp.symm.trans hd)
  have hQ : IsPolyhedron (S₀.complex.space ∪ S₁.complex.space) :=
    hK₀.isPolyhedron.union hK₁.isPolyhedron
  have hQR : S₀.complex.space ∪ S₁.complex.space ⊆ R.complex.space := by
    rw [hspace₀, hspace₁]
    exact union_subset inter_subset_left inter_subset_left
  obtain ⟨S, hSQ, hSR⟩ := R.exists_restrict_of_isPolyhedron hQ hQR
  have himage₀ : R.map '' S₀.complex.space = C₀ := by
    rw [← hmap₀]
    exact S₀.bijOn.image_eq
  have himage₁ : R.map '' S₁.complex.space = C₁ := by
    rw [← hmap₁]
    exact S₁.bijOn.image_eq
  have himage : R.map '' (S₀.complex.space ∪ S₁.complex.space) = C₀ ∪ C₁ := by
    rw [image_union, himage₀, himage₁]
  obtain ⟨J, hJfin, hJP⟩ :=
    ((show IsPLBall 2 P from ⟨p, hp⟩).isPolyhedron.prod
      (isHPolytope_Icc (a := (-1 : ℝ)) (b := 1)).isPolyhedron).exists_simplicialComplex
  have hρS : IsPLHomeomorphOn ρ J.space S.complex.space := by
    rw [hJP, hSQ]
    exact hρ
  let T := S.precomp J hJfin hρS
  have hTl : T.map '' (P ×ˢ Icc (-1 : ℝ) 0) = C₀ := by
    change (S.map ∘ ρ) '' _ = C₀
    rw [image_comp, hlower, hSR, himage₀]
  have hTu : T.map '' (P ×ˢ Icc (0 : ℝ) 1) = C₁ := by
    change (S.map ∘ ρ) '' _ = C₁
    rw [image_comp, hupper, hSR, himage₁]
  have hmid : P ×ˢ {(0 : ℝ)} =
      (P ×ˢ Icc (-1 : ℝ) 0) ∩ (P ×ˢ Icc (0 : ℝ) 1) := by
    ext ⟨x, t⟩
    simp only [mem_prod, mem_singleton_iff, mem_inter_iff, mem_Icc]
    constructor
    · rintro ⟨hx, rfl⟩
      exact ⟨⟨hx, by norm_num, le_rfl⟩, hx, le_rfl, by norm_num⟩
    · rintro ⟨⟨hx, -, ht⟩, -, ht', -⟩
      exact ⟨hx, le_antisymm ht ht'⟩
  have hlow : P ×ˢ Icc (-1 : ℝ) 0 ⊆ T.complex.space := by
    change P ×ˢ Icc (-1 : ℝ) 0 ⊆ J.space
    rw [hJP]
    exact prod_mono Subset.rfl (Icc_subset_Icc le_rfl zero_le_one)
  have hupp : P ×ˢ Icc (0 : ℝ) 1 ⊆ T.complex.space := by
    change P ×ˢ Icc (0 : ℝ) 1 ⊆ J.space
    rw [hJP]
    exact prod_mono Subset.rfl (Icc_subset_Icc (by norm_num) le_rfl)
  have hTm : T.map '' (P ×ˢ {(0 : ℝ)}) = C₀ ∩ C₁ :=
    (congrArg (fun A => T.map '' A) hmid).trans
      ((T.bijOn.injOn.image_inter hlow hupp).trans (congrArg₂ (· ∩ ·) hTl hTu))
  have hex : ∃ T : PLPieceIn (E × ℝ) 3 X (R.map ''
      (S₀.complex.space ∪ S₁.complex.space)),
      T.complex.space = P ×ˢ Icc (-1 : ℝ) 1 ∧
      T.map '' (P ×ˢ Icc (-1 : ℝ) 0) = C₀ ∧
      T.map '' (P ×ˢ Icc (0 : ℝ) 1) = C₁ ∧
      T.map '' (P ×ˢ {(0 : ℝ)}) = C₀ ∩ C₁ := ⟨T, hJP, hTl, hTu, hTm⟩
  rwa [himage] at hex

theorem exists_centered_prism_piece_of_boundary_disk_pair
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {X : Type*} [TopologicalSpace X] [T2Space X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X] [HasGroupoid X (plGroupoid 3)]
    {P : Set E} (hP : IsPLBall 2 P) {C₀ C₁ : Set X}
    (h₀ : IsPolyhedralBall (n := 3) 3 C₀) (h₁ : IsPolyhedralBall (n := 3) 3 C₁)
    (hD : IsPolyhedralBall (n := 3) 2 (C₀ ∩ C₁))
    (hD₀ : C₀ ∩ C₁ ⊆ frontier C₀) (hD₁ : C₀ ∩ C₁ ⊆ frontier C₁) :
    ∃ T : PLPieceIn (E × ℝ) 3 X (C₀ ∪ C₁),
      T.complex.space = P ×ˢ Icc (-1 : ℝ) 1 ∧
      T.map '' (P ×ˢ Icc (-1 : ℝ) 0) = C₀ ∧
      T.map '' (P ×ˢ Icc (0 : ℝ) 1) = C₁ ∧
      T.map '' (P ×ˢ {(0 : ℝ)}) = C₀ ∩ C₁ := by
  let : Nonempty X := ⟨h₀.nonempty.some⟩
  obtain ⟨Y, -, ⟨R⟩, hCY, -⟩ := exists_pLPiece_of_isCompact (n := 3)
    (h₀.isPolyhedralManifoldWithBoundary.isCompact.union
      h₁.isPolyhedralManifoldWithBoundary.isCompact) isOpen_univ (subset_univ _)
  exact centered_prism_piece_in R.piece hP h₀ h₁ hD hD₀ hD₁ (hCY.trans interior_subset)

end DifferentialGeometry.Topology.PiecewiseLinear
