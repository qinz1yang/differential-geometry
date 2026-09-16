import DifferentialGeometry.Topology.PiecewiseLinear.PrismDisk
import DifferentialGeometry.Topology.PiecewiseLinear.SphericalDiskExtension
import DifferentialGeometry.Topology.PiecewiseLinear.PLHomeomorphGluing

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_isPLHomeomorphOn_bottom_union_collar_sides
    {B P D W : Set E} (hP : IsPolyhedron P) (hD : IsPolyhedron D) (hDB : D ⊆ B)
    {a b : ℝ} (hab : a < b) {ρ : E × ℝ → E}
    (hρ : IsPLHomeomorphOn ρ (P ×ˢ Icc a b) W)
    (hbottom : ∀ x ∈ P, ρ (x, a) = x) (hWB : W ∩ B = P) :
    ∃ g : E × ℝ → E,
      IsPLHomeomorphOn g (D ×ˢ {a} ∪ (D ∩ P) ×ˢ Icc a b)
        (D ∪ ρ '' ((D ∩ P) ×ˢ Icc a b)) ∧
      EqOn g Prod.fst (D ×ˢ {a}) ∧ EqOn g ρ ((D ∩ P) ×ˢ Icc a b) := by
  have hI := (isPLBall_Icc hab).isPolyhedron
  have hDP := hD.inter hP
  have hside := hρ.restrict (hDP.prod hI) (prod_mono inter_subset_right Subset.rfl)
  have hbase := hD.isPLHomeomorphOn_fst_prod_const a
  apply exists_isPLHomeomorphOn_union
    (hD.prod (isHPolytope_singleton a).isPolyhedron) (hDP.prod hI) hbase hside
  · intro x hx
    have hxa : x = (x.1, a) := Prod.ext rfl hx.1.2
    rw [hxa]
    exact (hbottom x.1 hx.2.1.2).symm
  · rintro y ⟨hyD, hyimage⟩
    have hyW : y ∈ W := (image_mono (prod_mono inter_subset_right Subset.rfl)).trans
      hρ.image_eq.subset hyimage
    have hyP : y ∈ P := hWB ▸ ⟨hyW, hDB hyD⟩
    exact ⟨(y, a), ⟨⟨hyD, rfl⟩, ⟨hyD, hyP⟩, le_rfl, hab.le⟩, rfl⟩

open Classical in
private theorem exists_isPLHomeomorphOn_prism_of_isPLBall_bottom_union_sides
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hK : IsPLBall 2 K.space)
    {B P W : Set E} (hP : IsPolyhedron P) (hKB : K.space ⊆ B)
    {a b : ℝ} (hab : a < b) {ρ : E × ℝ → E}
    (hρ : IsPLHomeomorphOn ρ (P ×ˢ Icc a b) W)
    (hbottom : ∀ x ∈ P, ρ (x, a) = x) (hWB : W ∩ B = P)
    (hmeet : K.space ∩ P ⊆ (boundaryComplex 2 K).space)
    (hpatch : IsPLBall 2 (K.space ×ˢ {a} ∪ (K.space ∩ P) ×ˢ Icc a b))
    (L : Geometry.SimplicialComplex ℝ E) [Finite L.faces] (hL : IsPLBall 3 L.space)
    (hattach : K.space ∪ ρ '' ((K.space ∩ P) ×ˢ Icc a b) ⊆ (boundaryComplex 3 L).space) :
    ∃ G : E × ℝ → E, IsPLHomeomorphOn G (K.space ×ˢ Icc a b) L.space ∧
      EqOn G Prod.fst (K.space ×ˢ {a}) ∧ EqOn G ρ ((K.space ∩ P) ×ˢ Icc a b) := by
  let _ : DecidableEq (E × ℝ) := Classical.decEq _
  obtain ⟨g, hg, hgb, hgs⟩ := exists_isPLHomeomorphOn_bottom_union_collar_sides
    hP hK.isPolyhedron hKB hab hρ hbottom hWB
  have hprod := isPLBall_three_prod hK (isPLBall_Icc hab)
  obtain ⟨A, hAfin, hAspace⟩ := hprod.isPolyhedron.exists_simplicialComplex
  let _ : Finite A.faces := hAfin.to_subtype
  have hA : IsPLBall 3 A.space := hAspace.symm ▸ hprod
  have hpatchA : K.space ×ˢ {a} ∪ (K.space ∩ P) ×ˢ Icc a b ⊆
      (boundaryComplex 3 A).space := by
    rw [boundaryComplex_space_prism K hK hab A hAspace]
    rintro x (hx | hx)
    · exact Or.inl ⟨hx.1, Or.inl hx.2⟩
    · exact Or.inr ⟨hmeet hx.1, hx.2⟩
  obtain ⟨G, hG, hGg⟩ := exists_isPLHomeomorphOn_eqOn_disk_of_boundaryComplex
    A L hA hL hpatch hpatchA hg hattach
  rw [hAspace] at hG
  exact ⟨G, hG, (hGg.mono subset_union_left).trans hgb,
    (hGg.mono subset_union_right).trans hgs⟩

open Classical in
theorem exists_isPLHomeomorphOn_prism_eqOn_collar_sides_of_boundary_arcs {ι : Type*}
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hK : IsPLBall 2 K.space)
    {B P W : Set E} (hP : IsPolyhedron P) (hKB : K.space ⊆ B)
    {a b : ℝ} (hab : a < b) {ρ : E × ℝ → E}
    (hρ : IsPLHomeomorphOn ρ (P ×ˢ Icc a b) W)
    (hbottom : ∀ x ∈ P, ρ (x, a) = x) (hWB : W ∩ B = P)
    (d : Finset ι) (C : ι → Set E) (hC : ∀ i ∈ d, IsPLBall 1 (C i))
    (hCB : ∀ i ∈ d, C i ⊆ (boundaryComplex 2 K).space)
    (hdis : ∀ i ∈ d, ∀ j ∈ d, i ≠ j → Disjoint (C i) (C j))
    (hcover : (⋃ i ∈ d, C i) = K.space ∩ P)
    (L : Geometry.SimplicialComplex ℝ E) [Finite L.faces] (hL : IsPLBall 3 L.space)
    (hattach : K.space ∪ ρ '' ((K.space ∩ P) ×ˢ Icc a b) ⊆ (boundaryComplex 3 L).space) :
    ∃ G : E × ℝ → E, IsPLHomeomorphOn G (K.space ×ˢ Icc a b) L.space ∧
      EqOn G Prod.fst (K.space ×ˢ {a}) ∧ EqOn G ρ ((K.space ∩ P) ×ˢ Icc a b) := by
  have hmeet : K.space ∩ P ⊆ (boundaryComplex 2 K).space := by
    rw [← hcover]
    exact iUnion₂_subset hCB
  have hpatch := isPLBall_prism_bottom_union_strips K hK hab d C hC hCB hdis
  rw [hcover] at hpatch
  exact exists_isPLHomeomorphOn_prism_of_isPLBall_bottom_union_sides K hK hP hKB hab
    hρ hbottom hWB hmeet hpatch L hL hattach

open Classical in
theorem exists_isPLHomeomorphOn_prism_eqOn_collar_sides_of_boundary
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hK : IsPLBall 2 K.space)
    {B P W : Set E} (hP : IsPolyhedron P) (hKB : K.space ⊆ B)
    {a b : ℝ} (hab : a < b) {ρ : E × ℝ → E}
    (hρ : IsPLHomeomorphOn ρ (P ×ˢ Icc a b) W)
    (hbottom : ∀ x ∈ P, ρ (x, a) = x) (hWB : W ∩ B = P)
    (hmeet : K.space ∩ P = (boundaryComplex 2 K).space)
    (L : Geometry.SimplicialComplex ℝ E) [Finite L.faces] (hL : IsPLBall 3 L.space)
    (hattach : K.space ∪ ρ '' ((K.space ∩ P) ×ˢ Icc a b) ⊆ (boundaryComplex 3 L).space) :
    ∃ G : E × ℝ → E, IsPLHomeomorphOn G (K.space ×ˢ Icc a b) L.space ∧
      EqOn G Prod.fst (K.space ×ˢ {a}) ∧ EqOn G ρ ((K.space ∩ P) ×ˢ Icc a b) := by
  have hpatch : IsPLBall 2 (K.space ×ˢ {a} ∪ (K.space ∩ P) ×ˢ Icc a b) := by
    rw [hmeet]
    exact isPLBall_prism_bottom_union_side K hK hab
  exact exists_isPLHomeomorphOn_prism_of_isPLBall_bottom_union_sides K hK hP hKB hab
    hρ hbottom hWB hmeet.subset hpatch L hL hattach

end DifferentialGeometry.Topology.PiecewiseLinear
