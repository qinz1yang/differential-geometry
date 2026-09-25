import DifferentialGeometry.Topology.PiecewiseLinear.Section34OutermostReturningDisk
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CappedLateralAnnulus

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem exists_innermost_disk_of_lateral_returning_arcs
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {P : Set E} {r : (Fin 3 → ℝ) → E}
    (hr : IsPLHomeomorphOn r (stdSimplex ℝ (Fin 3)) P) {a b : ℝ} (hab : a < b)
    {ι : Type*} [Finite ι] [Nonempty ι] {T : ι → Set (E × ℝ)} {γ : ι → ℝ → E × ℝ}
    (hγ : ∀ i, IsPLHomeomorphOn (γ i) (Icc 0 1) (T i))
    (hside : ∀ i, T i ⊆ (r '' stdSimplexBoundary 2) ×ˢ Icc a b)
    (hends : ∀ i, T i ∩ ((r '' stdSimplexBoundary 2) ×ˢ ({b} : Set ℝ)) =
      {γ i 0, γ i 1})
    (hbase : ∀ i, Disjoint (T i) (P ×ˢ ({a} : Set ℝ)))
    (hdisj : Pairwise fun i j => Disjoint (T i) (T j)) :
    ∃ (i : ι) (F B : Set (E × ℝ)) (q : (Fin 3 → ℝ) → E × ℝ),
      IsPLHomeomorphOn q (stdSimplex ℝ (Fin 3)) F ∧ IsPLBall 1 B ∧
      F ⊆ (r '' stdSimplexBoundary 2) ×ˢ Ioc a b ∧
      q '' stdSimplexBoundary 2 = T i ∪ B ∧
      F ∩ ((r '' stdSimplexBoundary 2) ×ˢ ({b} : Set ℝ)) = B ∧
      F ∩ (⋃ j, T j) = T i ∧ (∀ j, j ≠ i → Disjoint F (T j)) ∧
      ∀ Z : Set (E × ℝ), IsPreconnected Z →
        Z ⊆ (r '' stdSimplexBoundary 2) ×ˢ Icc a b → Disjoint Z (T i) →
        (Z ∩ (P ×ˢ ({a} : Set ℝ))).Nonempty → Disjoint F Z := by
  classical
  have hP : IsPLBall 2 P := ⟨r, hr⟩
  obtain ⟨K, hKfin, hKP⟩ := hP.isPolyhedron.exists_simplicialComplex
  let _ : Finite K.faces := hKfin.to_subtype
  have hK : IsPLBall 2 K.space := hKP.symm ▸ hP
  have hrK : IsPLHomeomorphOn r (stdSimplex ℝ (Fin 3)) K.space := hKP.symm ▸ hr
  have hJ : (boundaryComplex 2 K).space = r '' stdSimplexBoundary 2 :=
    (hr.image_stdSimplexBoundary_eq_boundaryComplex K hKP).symm
  have hD := isPLBall_prism_bottom_union_side K hK hab
  rw [hKP, hJ] at hD
  obtain ⟨d, hd⟩ := hD
  have hrim : d '' stdSimplexBoundary 2 = (r '' stdSimplexBoundary 2) ×ˢ ({b} : Set ℝ) := by
    apply IsPLHomeomorphOn.capped_prism_boundary K hK hrK hab
    rwa [hKP]
  have hTD (i : ι) : T i ⊆ P ×ˢ ({a} : Set ℝ) ∪
      (r '' stdSimplexBoundary 2) ×ˢ Icc a b :=
    (hside i).trans subset_union_right
  have hC : IsPLBall 2 (P ×ˢ ({a} : Set ℝ)) :=
    hP.of_isPLHomeomorphOn (hP.isPolyhedron.isPLHomeomorphOn_prod_const a)
  have hCrim : Disjoint (P ×ˢ ({a} : Set ℝ)) (d '' stdSimplexBoundary 2) := by
    rw [hrim]
    exact disjoint_left.mpr fun _ hx hy => hab.ne (hx.2.symm.trans hy.2)
  obtain ⟨i, F, B, q, hq, hB, hFD, hFC, hqbd, hFB, hFT, hother, havoid⟩ :=
    hd.exists_outermost_crosscut_disk_avoiding_hole hC.isConnected subset_union_left
      hCrim hγ hTD (fun i => hrim.symm ▸ hends i) hdisj (fun i => (hbase i).symm)
  refine ⟨i, F, B, q, hq, hB, ?_, hqbd, hrim ▸ hFB, hFT, hother, ?_⟩
  · intro z hz
    have hzC := disjoint_left.mp hFC hz
    have hzside := (hFD hz).resolve_left hzC
    refine ⟨hzside.1, lt_of_le_of_ne hzside.2.1 ?_, hzside.2.2⟩
    intro heq
    exact hzC ⟨(image_mono (fun _ hx => hx.1)).trans hr.image_eq.subset hzside.1, heq.symm⟩
  · exact fun Z hZ hZS hZT hZC => havoid Z hZ
      (hZS.trans subset_union_right) hZT hZC

theorem exists_innermost_disk_of_lateral_arc_family
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {P : Set E} {r : (Fin 3 → ℝ) → E}
    (hr : IsPLHomeomorphOn r (stdSimplex ℝ (Fin 3)) P) {a b : ℝ} (hab : a < b)
    {ι : Type*} [Finite ι] {T : ι → Set (E × ℝ)} {γ : ι → ℝ → E × ℝ}
    (hγ : ∀ i, IsPLHomeomorphOn (γ i) (Icc 0 1) (T i))
    (hside : ∀ i, T i ⊆ (r '' stdSimplexBoundary 2) ×ˢ Icc a b)
    (hends : ∀ i, T i ∩ ((P ×ˢ ({a} : Set ℝ)) ∪
      (r '' stdSimplexBoundary 2) ×ˢ ({b} : Set ℝ)) = {γ i 0, γ i 1})
    (hdisj : Pairwise fun i j => Disjoint (T i) (T j))
    (hreturn : ∃ i, Disjoint (T i) (P ×ˢ ({a} : Set ℝ))) :
    ∃ (i : ι) (F B : Set (E × ℝ)) (q : (Fin 3 → ℝ) → E × ℝ),
      IsPLHomeomorphOn q (stdSimplex ℝ (Fin 3)) F ∧ IsPLBall 1 B ∧
      F ⊆ (r '' stdSimplexBoundary 2) ×ˢ Ioc a b ∧
      q '' stdSimplexBoundary 2 = T i ∪ B ∧
      F ∩ ((r '' stdSimplexBoundary 2) ×ˢ ({b} : Set ℝ)) = B ∧
      F ∩ (⋃ j, T j) = T i ∧ ∀ j, j ≠ i → Disjoint F (T j) := by
  classical
  let R := {i : ι | Disjoint (T i) (P ×ˢ ({a} : Set ℝ))}
  have hRne : Nonempty R := by
    obtain ⟨i, hi⟩ := hreturn
    exact ⟨⟨i, hi⟩⟩
  let _ := hRne
  have hRends (i : R) : T i.val ∩ ((r '' stdSimplexBoundary 2) ×ˢ ({b} : Set ℝ)) =
      {γ i.val 0, γ i.val 1} := by
    rw [← hends i.val, inter_union_distrib_left,
      disjoint_iff_inter_eq_empty.mp i.property, empty_union]
  obtain ⟨i, F, B, q, hq, hB, hFS, hqbd, hFB, hFT, hother, havoid⟩ :=
    exists_innermost_disk_of_lateral_returning_arcs hr hab
      (fun i : R => hγ i.val) (fun i : R => hside i.val) hRends
      (fun i : R => i.property)
      (fun j k hjk => hdisj (fun heq => hjk (Subtype.ext heq)))
  have hother' (j : ι) (hji : j ≠ i.val) : Disjoint F (T j) := by
    by_cases hj : j ∈ R
    · exact hother ⟨j, hj⟩ (fun heq => hji (congrArg Subtype.val heq))
    · have hball : IsPLBall 1 (T j) :=
        (isPLBall_Icc zero_lt_one).of_isPLHomeomorphOn (hγ j)
      exact havoid (T j) hball.isConnected.isPreconnected (hside j) (hdisj hji)
        (not_disjoint_iff_nonempty_inter.mp hj)
  refine ⟨i.val, F, B, q, hq, hB, hFS, hqbd, hFB, ?_, hother'⟩
  apply Subset.antisymm
  · rintro x ⟨hxF, hxT⟩
    obtain ⟨j, hxj⟩ := mem_iUnion.mp hxT
    by_cases hji : j = i.val
    · exact hji ▸ hxj
    · exact (disjoint_left.mp (hother' j hji) hxF hxj).elim
  · intro x hxi
    have hxF := (hFT.symm.subset hxi).1
    exact ⟨hxF, mem_iUnion.mpr ⟨i.val, hxi⟩⟩

end DifferentialGeometry.Topology.PiecewiseLinear
