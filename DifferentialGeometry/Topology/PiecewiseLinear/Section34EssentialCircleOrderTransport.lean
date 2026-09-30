import DifferentialGeometry.Topology.PiecewiseLinear.Section34EssentialCircleOrder
import DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercingEssentialTrace

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLCellOn.exists_ordered_disk_caps_of_essential_family {M : Type*}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {S B A A₀ A₁ : Set M} (hS : IsPLCellOn 3 S B) (hA : IsAnnulusOn A A₀ A₁)
    (hAB : A ⊆ B) (C : Set (Set M)) (hC : C.Finite)
    (hCsph : ∀ J ∈ C, IsPolyhedralSphere (n := 3) 1 J) (hCA : ∀ J ∈ C, J ⊆ A)
    (hCend : ∀ J ∈ C, Disjoint J (A₀ ∪ A₁)) (hCdisj : C.PairwiseDisjoint id)
    (hCess : ∀ J ∈ C, ¬ ∃ D : Set M, IsPLCellOn 2 D J ∧ D ⊆ A) :
    ∃ (e : Fin C.ncard ≃ C) (D₀ D₁ : Fin C.ncard → Set M),
      (∀ i, IsPLCellOn 2 (D₀ i) (e i).val ∧ IsPLCellOn 2 (D₁ i) (e i).val ∧
        D₀ i ∪ D₁ i = B ∧ D₀ i ∩ D₁ i = (e i).val ∧
        A₀ ⊆ D₀ i ∧ A₁ ⊆ D₁ i) ∧
      StrictMono D₀ ∧ StrictAnti D₁ ∧
      (∀ i j, i < j → Disjoint (D₀ i) (D₁ j)) ∧
      (∀ i j, (e i).val ⊆ D₀ j ↔ i ≤ j) ∧
      (∀ i j, (e i).val ⊆ D₁ j ↔ j ≤ i) := by
  classical
  obtain ⟨P, r, u, hr, hu, -, hB⟩ := hS
  have hP : IsPLBall 3 P := ⟨r, hr⟩
  have hfront : frontier P ⊆ P := hP.isPolyhedron.isClosed.frontier_subset
  rw [hr.image_stdSimplexBoundary_eq_frontier] at hB
  have hAP : A ⊆ u '' P := hAB.trans (hB ▸ image_mono hfront)
  let τ := Function.invFunOn u P
  have hleft : LeftInvOn τ u P := hu.injOn.leftInvOn_invFunOn
  have hright : RightInvOn τ u (u '' P) := hu.injOn.bijOn_image.invOn_invFunOn.2
  have hτc : ContinuousOn τ (u '' P) := (hu.isPLOn_inverse hleft).continuousOn
  have hτi : InjOn τ (u '' P) := by
    intro x hx y hy hxy
    rw [← hright hx, ← hright hy, hxy]
  have hA' := hA.image_of_continuousOn_injOn (hτc.mono hAP) (hτi.mono hAP)
  have hA'S : τ '' A ⊆ frontier P := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨z, hz, rfl⟩ : x ∈ u '' frontier P := hB ▸ hAB hx
    rw [hleft (hfront hz)]
    exact hz
  have hback (X : Set M) (hXA : X ⊆ A) : u '' (τ '' X) = X := by
    rw [image_image]
    exact (image_congr fun x hx => hright (hAP (hXA hx))).trans (image_id' X)
  have hdisj {X Y : Set M} (hXA : X ⊆ A) (hYA : Y ⊆ A) (hXY : Disjoint X Y) :
      Disjoint (τ '' X) (τ '' Y) := by
    refine disjoint_left.mpr ?_
    rintro z ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
    have heq := hτi (hAP (hXA hx)) (hAP (hYA hy)) hxy.symm
    exact disjoint_left.mp hXY hx (heq ▸ hy)
  have hess {X : Set M} (hXA : X ⊆ A)
      (hXess : ¬ ∃ D : Set M, IsPLCellOn 2 D X ∧ D ⊆ A) :
      ¬ ∃ (D : Set (EuclideanSpace ℝ (Fin 3)))
        (q : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)),
        IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D ∧ D ⊆ τ '' A ∧
          q '' stdSimplexBoundary 2 = τ '' X := by
    rintro ⟨D, q, hq, hDA, hqb⟩
    have hDP := (hDA.trans hA'S).trans hfront
    have hpoly : IsPolyhedron D := IsPLBall.isPolyhedron ⟨q, hq⟩
    have huD : IsPLHomeomorphInto 3 u D :=
      (hu.isPLOn.mono_of_isPolyhedron hpoly hDP).isPLHomeomorphInto_model
        hpoly.isCompact (hu.injOn.mono hDP)
    have hc := (isPLCellOn_id_of_isPLBall hq).image huD
    rw [hqb, hback X hXA] at hc
    exact hXess ⟨u '' D, hc, hback A Subset.rfl ▸ image_mono hDA⟩
  let C' := (fun J : Set M => τ '' J) '' C
  have himg : InjOn (fun J : Set M => τ '' J) C := by
    intro J hJ L hL hJL
    change τ '' J = τ '' L at hJL
    rw [← hback J (hCA J hJ), ← hback L (hCA L hL), hJL]
  have hC'sph : ∀ J ∈ C', IsPLSphere 1 J := by
    rintro _ ⟨J, hJ, rfl⟩
    exact hu.isPLSphere_invFunOn_image (hCsph J hJ) ((hCA J hJ).trans hAP)
  have hC'A : ∀ J ∈ C', J ⊆ τ '' A := by
    rintro _ ⟨J, hJ, rfl⟩
    exact image_mono (hCA J hJ)
  have hendA := union_subset hA.first_subset hA.second_subset
  have hC'end : ∀ J ∈ C', Disjoint J (τ '' A₀ ∪ τ '' A₁) := by
    rintro _ ⟨J, hJ, rfl⟩
    rw [← image_union]
    exact hdisj (hCA J hJ) hendA (hCend J hJ)
  have hC'disj : C'.PairwiseDisjoint id := by
    rintro _ ⟨J, hJ, rfl⟩ _ ⟨L, hL, rfl⟩ hJL
    exact hdisj (hCA J hJ) (hCA L hL)
      (hCdisj hJ hL (fun h => hJL (congrArg (fun K => τ '' K) h)))
  have hC'ess : ∀ J ∈ C', ¬ ∃ (D : Set (EuclideanSpace ℝ (Fin 3)))
      (q : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)),
      IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D ∧ D ⊆ τ '' A ∧
        q '' stdSimplexBoundary 2 = J := by
    rintro _ ⟨J, hJ, rfl⟩
    exact hess (hCA J hJ) (hCess J hJ)
  have hex := hP.isPLSphere_frontier.exists_ordered_disk_caps_of_essential_family
    hA' hA'S C' (hC.image _) hC'sph hC'A hC'end hC'disj hC'ess
  have hcard : C'.ncard = C.ncard := himg.ncard_image
  rw [hcard] at hex
  obtain ⟨e', D₀, D₁, r₀, r₁, hcaps, hmono, hanti, hdis, hpos₀, hpos₁⟩ := hex
  let β : C ≃ C' := Equiv.Set.imageOfInjOn (fun J : Set M => τ '' J) C himg
  let e := e'.trans β.symm
  have he (i : Fin C.ncard) : τ '' (e i).val = (e' i).val :=
    congrArg Subtype.val (β.apply_symm_apply (e' i))
  have hDP₀ (i : Fin C.ncard) : D₀ i ⊆ P := by
    obtain ⟨-, -, -, -, hcover, -⟩ := hcaps i
    exact (hcover ▸ subset_union_left).trans hfront
  have hDP₁ (i : Fin C.ncard) : D₁ i ⊆ P := by
    obtain ⟨-, -, -, -, hcover, -⟩ := hcaps i
    exact (hcover ▸ subset_union_right).trans hfront
  have hcircle (i : Fin C.ncard) : u '' (e' i).val = (e i).val := by
    rw [← he i, hback _ (hCA (e i).val (e i).property)]
  have hcell {D : Set (EuclideanSpace ℝ (Fin 3))}
      {q : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)} (i : Fin C.ncard)
      (hq : IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D) (hDP : D ⊆ P)
      (hqb : q '' stdSimplexBoundary 2 = (e' i).val) :
      IsPLCellOn 2 (u '' D) (e i).val := by
    have hpoly : IsPolyhedron D := IsPLBall.isPolyhedron ⟨q, hq⟩
    have huD : IsPLHomeomorphInto 3 u D :=
      (hu.isPLOn.mono_of_isPolyhedron hpoly hDP).isPLHomeomorphInto_model
        hpoly.isCompact (hu.injOn.mono hDP)
    have hc := (isPLCellOn_id_of_isPLBall hq).image huD
    rwa [hqb, hcircle i] at hc
  have hJP (i : Fin C.ncard) : (e' i).val ⊆ P :=
    ((hC'A (e' i).val (e' i).property).trans hA'S).trans hfront
  refine ⟨e, (fun i => u '' D₀ i), (fun i => u '' D₁ i), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    obtain ⟨hr₀, hr₁, hb₀, hb₁, hcover, hmeet, hend₀, hend₁⟩ := hcaps i
    refine ⟨hcell i hr₀ (hDP₀ i) hb₀, hcell i hr₁ (hDP₁ i) hb₁, ?_, ?_, ?_, ?_⟩
    · rw [← image_union, hcover, ← hB]
    · rw [← hu.injOn.image_inter (hDP₀ i) (hDP₁ i), hmeet, hcircle i]
    · exact hback A₀ hA.first_subset ▸ image_mono hend₀
    · exact hback A₁ hA.second_subset ▸ image_mono hend₁
  · intro i j hij
    exact (hu.injOn.image_ssubset_image_iff (hDP₀ i) (hDP₀ j)).mpr (hmono hij)
  · intro i j hij
    exact (hu.injOn.image_ssubset_image_iff (hDP₁ j) (hDP₁ i)).mpr (hanti hij)
  · intro i j hij
    rw [disjoint_iff_inter_eq_empty, ← hu.injOn.image_inter (hDP₀ i) (hDP₁ j),
      (hdis i j hij).inter_eq, image_empty]
  · intro i j
    rw [← hcircle i, hu.injOn.image_subset_image_iff (hJP i) (hDP₀ j), hpos₀]
  · intro i j
    rw [← hcircle i, hu.injOn.image_subset_image_iff (hJP i) (hDP₁ j), hpos₁]

end DifferentialGeometry.Topology.PiecewiseLinear
