import DifferentialGeometry.Topology.PiecewiseLinear.Section34LateralFaceMatching
import DifferentialGeometry.Topology.PiecewiseLinear.DiskUnion
import DifferentialGeometry.Topology.PiecewiseLinear.PlanarDiskComplement

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem exists_complementary_lateral_disks
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {P A₀ A₁ : Set E} {r : (Fin 3 → ℝ) → E}
    (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) P) {a b : ℝ} (hab : a < b)
    {Z : (r '' stdSimplexBoundary 2) → Set (E × ℝ)}
    (hZ : ∀ z, IsPreconnected (Z z))
    (hZside : ∀ z, Z z ⊆ (r '' stdSimplexBoundary 2) ×ˢ Icc a b)
    (hZa : ∀ z, Z z ∩ ((r '' stdSimplexBoundary 2) ×ˢ ({a} : Set ℝ)) = {((z : E), a)})
    (hZb : ∀ z, Z z ∩ ((r '' stdSimplexBoundary 2) ×ˢ ({b} : Set ℝ)) = {((z : E), b)})
    (hdis : Pairwise fun z w => Disjoint (Z z) (Z w))
    (hcover : ⋃ z, Z z = (r '' stdSimplexBoundary 2) ×ˢ Icc a b)
    {x y : r '' stdSimplexBoundary 2} {α β : ℝ → E × ℝ} {δ₀ δ₁ : ℝ → E}
    (hα : IsPLHomeomorphOn α (Icc 0 1) (Z x))
    (hβ : IsPLHomeomorphOn β (Icc 0 1) (Z y))
    (hδ₀ : IsPLHomeomorphOn δ₀ (Icc 0 1) A₀)
    (hδ₁ : IsPLHomeomorphOn δ₁ (Icc 0 1) A₁)
    (hα₀ : α 0 = ((x : E), a)) (hα₁ : α 1 = ((x : E), b))
    (hβ₀ : β 0 = ((y : E), a)) (hβ₁ : β 1 = ((y : E), b))
    (hδ₀₀ : δ₀ 0 = x) (hδ₀₁ : δ₀ 1 = y)
    (hδ₁₀ : δ₁ 0 = x) (hδ₁₁ : δ₁ 1 = y)
    (hAcover : A₀ ∪ A₁ = r '' stdSimplexBoundary 2)
    (hAinter : A₀ ∩ A₁ = {(x : E), (y : E)}) :
    ∃ (F₀ F₁ : Set (E × ℝ)) (q₀ q₁ : (Fin 3 → ℝ) → E × ℝ),
      IsPLHomeomorphOn q₀ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) F₀ ∧
      IsPLHomeomorphOn q₁ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) F₁ ∧
      F₀ ∪ F₁ = (r '' stdSimplexBoundary 2) ×ˢ Icc a b ∧ F₀ ∩ F₁ = Z x ∪ Z y ∧
      q₀ '' stdSimplexBoundary 2 =
        ((Z x ∪ (A₀ ×ˢ ({a} : Set ℝ))) ∪ Z y) ∪ (A₀ ×ˢ ({b} : Set ℝ)) ∧
      q₁ '' stdSimplexBoundary 2 =
        ((Z x ∪ (A₁ ×ˢ ({a} : Set ℝ))) ∪ Z y) ∪ (A₁ ×ˢ ({b} : Set ℝ)) ∧
      F₀ ∩ ((r '' stdSimplexBoundary 2) ×ˢ ({b} : Set ℝ)) = A₀ ×ˢ ({b} : Set ℝ) ∧
      F₁ ∩ ((r '' stdSimplexBoundary 2) ×ˢ ({b} : Set ℝ)) = A₁ ×ˢ ({b} : Set ℝ) ∧
      F₀ ∩ (P ×ˢ ({a} : Set ℝ)) = A₀ ×ˢ ({a} : Set ℝ) ∧
      F₁ ∩ (P ×ˢ ({a} : Set ℝ)) = A₁ ×ˢ ({a} : Set ℝ) ∧
      (∀ z : r '' stdSimplexBoundary 2, (z : E) ∉ A₀ → Disjoint F₀ (Z z)) ∧
      (∀ z : r '' stdSimplexBoundary 2, (z : E) ∉ A₁ → Disjoint F₁ (Z z)) := by
  classical
  let _ : DecidableEq (E × ℝ) := Classical.decEq _
  have hA₀P : A₀ ⊆ r '' stdSimplexBoundary 2 := subset_union_left.trans hAcover.subset
  have hA₁P : A₁ ⊆ r '' stdSimplexBoundary 2 := subset_union_right.trans hAcover.subset
  obtain ⟨F₀, q₀, hq₀, hF₀side, hq₀bd, hF₀top, hF₀bottom, hF₀out⟩ :=
    exists_lateral_disk_with_matching_rim_arcs hr hab hZ hZside hZa hZb hdis hα hβ hδ₀
      hα₀ hα₁ hβ₀ hβ₁ hδ₀₀ hδ₀₁ hA₀P
  obtain ⟨F₁, q₁, hq₁, hF₁side, hq₁bd, hF₁top, hF₁bottom, hF₁out⟩ :=
    exists_lateral_disk_with_matching_rim_arcs hr hab hZ hZside hZa hZb hdis hα hβ hδ₁
      hα₀ hα₁ hβ₀ hβ₁ hδ₁₀ hδ₁₁ hA₁P
  have hF₀ : IsPLBall 2 F₀ := ⟨q₀, hq₀⟩
  have hF₁ : IsPLBall 2 F₁ := ⟨q₁, hq₁⟩
  have hZsub (A : Set E) (F : Set (E × ℝ)) (q : (Fin 3 → ℝ) → E × ℝ)
      (hq : IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) F)
      (hbd : q '' stdSimplexBoundary 2 =
        ((Z x ∪ (A ×ˢ ({a} : Set ℝ))) ∪ Z y) ∪ (A ×ˢ ({b} : Set ℝ))) : Z x ∪ Z y ⊆ F := by
    have hbF : q '' stdSimplexBoundary 2 ⊆ F :=
      (image_mono (fun _ hx => hx.1)).trans hq.image_eq.subset
    rw [hbd] at hbF
    intro z hz
    exact hbF (Or.inl (hz.elim (fun hx => Or.inl (Or.inl hx)) Or.inr))
  have hZ₀ := hZsub A₀ F₀ q₀ hq₀ hq₀bd
  have hZ₁ := hZsub A₁ F₁ q₁ hq₁ hq₁bd
  have hinter : F₀ ∩ F₁ = Z x ∪ Z y := by
    apply Subset.antisymm
    · intro p hp
      obtain ⟨z, hpZ⟩ := mem_iUnion.mp (hcover.symm.subset (hF₀side hp.1))
      have hz₀ : (z : E) ∈ A₀ := by
        by_contra hz
        exact disjoint_left.mp (hF₀out z hz) hp.1 hpZ
      have hz₁ : (z : E) ∈ A₁ := by
        by_contra hz
        exact disjoint_left.mp (hF₁out z hz) hp.2 hpZ
      rcases hAinter.subset ⟨hz₀, hz₁⟩ with hzx | hzy
      · have heq : z = x := Subtype.ext hzx
        exact Or.inl (heq ▸ hpZ)
      · have heq : z = y := Subtype.ext hzy
        exact Or.inr (heq ▸ hpZ)
    · exact fun p hp => ⟨hZ₀ hp, hZ₁ hp⟩
  have hP : IsPLBall 2 P := ⟨r, hr⟩
  obtain ⟨K, hKfin, hKP⟩ := hP.isPolyhedron.exists_simplicialComplex
  let _ : Finite K.faces := hKfin.to_subtype
  have hK : IsPLBall 2 K.space := hKP.symm ▸ hP
  have hrK : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) K.space := hKP.symm ▸ hr
  have hJ : (boundaryComplex 2 K).space = r '' stdSimplexBoundary 2 :=
    (hr.image_stdSimplexBoundary_eq_boundaryComplex K hKP).symm
  let C := P ×ˢ ({a} : Set ℝ)
  let D := C ∪ (r '' stdSimplexBoundary 2) ×ˢ Icc a b
  have hD : IsPLBall 2 D := by
    have h := isPLBall_prism_bottom_union_side K hK hab
    rwa [hKP, hJ] at h
  obtain ⟨d, hd⟩ := hD
  have hD : IsPLBall 2 D := ⟨d, hd⟩
  have hDboundary : d '' stdSimplexBoundary 2 =
      (r '' stdSimplexBoundary 2) ×ˢ ({b} : Set ℝ) := by
    apply IsPLHomeomorphOn.capped_prism_boundary K hK hrK hab
    rwa [hKP]
  have hC : IsPLBall 2 C :=
    hP.of_isPLHomeomorphOn (hP.isPolyhedron.isPLHomeomorphOn_prod_const a)
  have hF₀D : F₀ ⊆ D := hF₀side.trans subset_union_right
  have hF₁D : F₁ ⊆ D := hF₁side.trans subset_union_right
  have hA₀ : IsPLBall 1 A₀ := (isPLBall_Icc zero_lt_one).of_isPLHomeomorphOn hδ₀
  have hCF₀ : IsPLBall 1 (C ∩ F₀) := by
    rw [inter_comm, hF₀bottom]
    exact hA₀.of_isPLHomeomorphOn (hA₀.isPolyhedron.isPLHomeomorphOn_prod_const a)
  have hCF₀ball := isPLBall_union_of_inter_isPLBall_one_in_ball hD hC hF₀
    subset_union_left hF₀D hCF₀
  have hxy : x ≠ y := by
    intro heq
    exact zero_ne_one (hδ₀.bijOn.injOn ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩
      (hδ₀₀.trans ((congrArg Subtype.val heq).trans hδ₀₁.symm)))
  obtain ⟨γ, hγ, -, -, -, -, -⟩ :=
    exists_spanning_pair_returning_arc hab hα hβ hδ₁ hα₀ hα₁ hβ₀ hβ₁ hδ₁₀ hδ₁₁
      (hZside x) (hZside y) hA₁P (hZa x) (hZb x) (hZa y) (hZb y) (hdis hxy)
  have hglue : (C ∪ F₀) ∩ F₁ = (Z x ∪ (A₁ ×ˢ ({a} : Set ℝ))) ∪ Z y := by
    rw [union_inter_distrib_right, inter_comm C F₁, hF₁bottom, hinter]
    exact (union_left_comm _ _ _).trans (union_assoc _ _ _).symm
  have hgluePL : IsPLBall 1 ((C ∪ F₀) ∩ F₁) := by
    rw [hglue]
    exact (isPLBall_Icc zero_lt_one).of_isPLHomeomorphOn hγ
  have hwhole : IsPLBall 2 ((C ∪ F₀) ∪ F₁) :=
    isPLBall_union_of_inter_isPLBall_one_in_ball hD hCF₀ball hF₁
      (union_subset subset_union_left hF₀D) hF₁D hgluePL
  obtain ⟨L, hLfin, hLD⟩ := hD.isPolyhedron.exists_simplicialComplex
  let _ : Finite L.faces := hLfin.to_subtype
  have hL : IsPLBall 2 L.space := hLD.symm ▸ hD
  have hwholeD : (C ∪ F₀) ∪ F₁ ⊆ L.space :=
    (union_subset (union_subset subset_union_left hF₀D) hF₁D).trans hLD.symm.subset
  have hwholebd : (boundaryComplex 2 L).space ⊆ (C ∪ F₀) ∪ F₁ := by
    rw [← hd.image_stdSimplexBoundary_eq_boundaryComplex L hLD, hDboundary, ← hAcover,
      union_prod]
    exact union_subset
      (fun p hp => Or.inl (Or.inr ((hF₀top.symm.subset hp).1)))
      (fun p hp => Or.inr ((hF₁top.symm.subset hp).1))
  have hwholeEq : (C ∪ F₀) ∪ F₁ = D :=
    (eq_of_isPLBall_of_boundaryComplex_subset L hL hwhole hwholeD hwholebd).trans hLD
  have hfaces : F₀ ∪ F₁ = (r '' stdSimplexBoundary 2) ×ˢ Icc a b := by
    apply Subset.antisymm (union_subset hF₀side hF₁side)
    intro p hp
    by_cases hpa : p.2 = a
    · rcases hAcover.symm.subset hp.1 with hp₀ | hp₁
      · exact Or.inl ((hF₀bottom.symm.subset ⟨hp₀, hpa⟩).1)
      · exact Or.inr ((hF₁bottom.symm.subset ⟨hp₁, hpa⟩).1)
    · rcases hwholeEq.symm.subset (Or.inr hp) with (hpC | hp₀) | hp₁
      · exact (hpa hpC.2).elim
      · exact Or.inl hp₀
      · exact Or.inr hp₁
  exact ⟨F₀, F₁, q₀, q₁, hq₀, hq₁, hfaces, hinter, hq₀bd, hq₁bd,
    hF₀top, hF₁top, hF₀bottom, hF₁bottom, hF₀out, hF₁out⟩

end DifferentialGeometry.Topology.PiecewiseLinear
