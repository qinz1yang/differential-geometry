import DifferentialGeometry.Topology.PiecewiseLinear.PlanarOutermostCrosscut
import DifferentialGeometry.Topology.PiecewiseLinear.DiskCrosscut
import DifferentialGeometry.Topology.PiecewiseLinear.Section34ReturningArcDisk

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E2" => EuclideanSpace ℝ (Fin 2)

theorem exists_outermost_PL_crosscut_disk_avoiding_hole
    {D C : Set E2} (hD : IsPLBall 2 D) (hC : IsConnected C)
    (hCD : C ⊆ interior D) {ι : Type*} [Finite ι] [Nonempty ι]
    {T : ι → Set E2} {p q : ι → E2} (hT : ∀ i, IsPLBall 1 (T i))
    (hcut : ∀ i, Schoenflies.IsCrosscut (frontier D) (T i) (p i) (q i))
    (hdisj : Pairwise fun i j => Disjoint (T i) (T j))
    (hCT : ∀ i, Disjoint C (T i)) :
    ∃ (i : ι) (F B : Set E2), IsPLBall 2 F ∧ IsPLBall 1 B ∧ F ⊆ D ∧
      Disjoint F C ∧ frontier F = T i ∪ B ∧ F ∩ frontier D = B ∧
      F ∩ (⋃ j, T j) = T i ∧ (∀ j, j ≠ i → Disjoint F (T j)) ∧
      ∀ Z : Set E2, IsPreconnected Z → Z ⊆ D → Disjoint Z (T i) →
        (Z ∩ C).Nonempty → Disjoint F Z := by
  obtain ⟨a, ha⟩ := hC.nonempty
  have hγ := isJordanCurve_of_isPLSphere_one hD.isPLSphere_frontier
  obtain ⟨i, B, ⟨B', hBB'⟩, _, hJ, hJD, haJ, hBD, hothers⟩ :=
    exists_outermost_crosscut hγ
      (hD.interior_eq_inside_frontier ▸ hCD ha) (fun i => (hcut i).arc)
      (fun i => (hcut i).left_mem) (fun i => (hcut i).right_mem)
      (fun i => (hcut i).sdiff_subset) hdisj
      (fun i => disjoint_left.mp (hCT i) ha)
  have hPL := isPLSphere_one_union_of_isCrosscut hD.isPLSphere_frontier (hT i)
    (hcut i) hBB'
  let F := closure (Schoenflies.inside (B ∪ T i))
  have hF : IsPLBall 2 F := isPLBall_closure_inside_of_isPLSphere_one hPL
  have hfront : frontier F = B ∪ T i :=
    frontier_closure_inside_of_isPLSphere_one hPL
  have hCF : Disjoint C (B ∪ T i) := by
    refine disjoint_union_right.mpr ⟨?_, hCT i⟩
    exact disjoint_interior_frontier.mono hCD hBB'.fst_subset
  have hCout : C ⊆ Schoenflies.outside (B ∪ T i) :=
    (subset_inside_or_subset_outside hJ hC.isPreconnected hCF).resolve_left
      (fun h => haJ (h ha))
  have hTiF : T i ⊆ F := fun x hx =>
    hF.isPolyhedron.isClosed.frontier_subset (hfront.symm.subset (Or.inr hx))
  have hFC : Disjoint F C := disjoint_left.mpr fun x hxF hxC =>
    (compl_closure_inside hJ).symm.subset (hCout hxC) hxF
  refine ⟨i, F, B, hF,
    isPLBall_of_isArc_subset_isPLSphere hD.isPLSphere_frontier hBB'.fst.isArc
      hBB'.fst_subset, ?_, hFC, hfront.trans (union_comm _ _), hBD, ?_,
      (fun j hji => (hothers j hji).symm), ?_⟩
  · exact closure_minimal
      (hJD.trans (hD.interior_eq_inside_frontier.symm.subset.trans interior_subset))
      hD.isPolyhedron.isClosed
  · apply Subset.antisymm
    · rintro x ⟨hxF, hxT⟩
      obtain ⟨j, hxj⟩ := mem_iUnion.mp hxT
      by_cases hji : j = i
      · exact hji ▸ hxj
      · exact (disjoint_left.mp (hothers j hji) hxj hxF).elim
    · exact fun x hx => ⟨hTiF hx, mem_iUnion.mpr ⟨i, hx⟩⟩
  · intro Z hZ hZD hZT hZC
    let V := closure (Schoenflies.inside (B' ∪ T i))
    have hcover : F ∪ V = D := by
      rw [show F ∪ V = closure (Schoenflies.inside (frontier D)) from
        PlanarJordan.closure_inside_union_of_isCrosscut (hcut i) hBB',
        ← hD.interior_eq_inside_frontier]
      exact hD.closure_interior
    have hmeet : F ∩ V = T i :=
      PlanarJordan.closure_inside_inter_of_isCrosscut (hcut i) hBB'
    obtain ⟨a, haZ, haC⟩ := hZC
    have haV : a ∈ V :=
      (hcover.symm.subset (hZD haZ)).resolve_left (disjoint_right.mp hFC haC)
    refine disjoint_left.mpr fun x hxF hxZ => ?_
    obtain ⟨y, hyZ, hyFV⟩ := isPreconnected_closed_iff.mp hZ F V isClosed_closure
      isClosed_closure (hZD.trans hcover.symm.subset) ⟨x, hxZ, hxF⟩ ⟨a, haZ, haV⟩
    exact disjoint_left.mp hZT hyZ (hmeet.subset hyFV)

theorem IsPLHomeomorphOn.exists_outermost_crosscut_disk_avoiding_hole
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {D C : Set E} {r : (Fin 3 → ℝ) → E}
    (hr : IsPLHomeomorphOn r (stdSimplex ℝ (Fin 3)) D)
    (hC : IsConnected C) (hCD : C ⊆ D)
    (hCrim : Disjoint C (r '' stdSimplexBoundary 2))
    {ι : Type*} [Finite ι] [Nonempty ι] {T : ι → Set E} {γ : ι → ℝ → E}
    (hγ : ∀ i, IsPLHomeomorphOn (γ i) (Icc 0 1) (T i))
    (hTD : ∀ i, T i ⊆ D)
    (hends : ∀ i, T i ∩ r '' stdSimplexBoundary 2 = {γ i 0, γ i 1})
    (hdisj : Pairwise fun i j => Disjoint (T i) (T j))
    (hCT : ∀ i, Disjoint C (T i)) :
    ∃ (i : ι) (F B : Set E) (q : (Fin 3 → ℝ) → E),
      IsPLHomeomorphOn q (stdSimplex ℝ (Fin 3)) F ∧ IsPLBall 1 B ∧
      F ⊆ D ∧ Disjoint F C ∧ q '' stdSimplexBoundary 2 = T i ∪ B ∧
      F ∩ r '' stdSimplexBoundary 2 = B ∧ F ∩ (⋃ j, T j) = T i ∧
      (∀ j, j ≠ i → Disjoint F (T j)) ∧
      ∀ Z : Set E, IsPreconnected Z → Z ⊆ D → Disjoint Z (T i) →
        (Z ∩ C).Nonempty → Disjoint F Z := by
  have hD : IsPLBall 2 D := ⟨r, hr⟩
  have hT (i : ι) : IsPLBall 1 (T i) :=
    (isPLBall_Icc zero_lt_one).of_isPLHomeomorphOn (hγ i)
  obtain ⟨J, σ, hJ, hσ⟩ := exists_planar_coordinates_of_isPLBall_two hD
  let R := closure (Schoenflies.inside J)
  have hR : IsPLBall 2 R := isPLBall_closure_inside_of_isPLSphere_one hJ
  have hrimD : r '' stdSimplexBoundary 2 ⊆ D :=
    (image_mono (fun _ hx => hx.1)).trans hr.image_eq.subset
  have hσrim : σ '' (r '' stdSimplexBoundary 2) = frontier R := by
    rw [← image_comp]
    exact (hr.trans hσ).image_stdSimplexBoundary
  have hσT (i : ι) := hσ.restrict (hT i).isPolyhedron (hTD i)
  have hC' : IsConnected (σ '' C) :=
    hC.image σ (hσ.isPiecewiseAffineOn.continuousOn.mono hCD)
  have hCD' : σ '' C ⊆ interior R := by
    rintro _ ⟨x, hx, rfl⟩
    apply (mem_interior_iff_notMem_frontier (hσ.bijOn.mapsTo (hCD hx))).mpr
    rw [← hσrim]
    rintro ⟨y, hy, hyx⟩
    exact disjoint_left.mp hCrim hx
      (hσ.bijOn.injOn (hrimD hy) (hCD hx) hyx ▸ hy)
  have hdisj' : Pairwise fun i j => Disjoint (σ '' T i) (σ '' T j) := by
    intro i j hij
    apply disjoint_left.mpr
    rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hyx⟩
    exact disjoint_left.mp (hdisj hij) hx
      (hσ.bijOn.injOn (hTD j hy) (hTD i hx) hyx ▸ hy)
  have hCT' (i : ι) : Disjoint (σ '' C) (σ '' T i) := by
    apply disjoint_left.mpr
    rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hyx⟩
    exact disjoint_left.mp (hCT i) hx
      (hσ.bijOn.injOn (hTD i hy) (hCD hx) hyx ▸ hy)
  have hcut (i : ι) := isCrosscut_image_of_disk_arc hJ hσ
    (hσrim.trans (frontier_closure_inside_of_isPLSphere_one hJ)) hrimD
    (hγ i) (hTD i) (hends i)
  have hcut' (i : ι) : Schoenflies.IsCrosscut (frontier R) (σ '' T i)
      (σ (γ i 0)) (σ (γ i 1)) := by
    rw [frontier_closure_inside_of_isPLSphere_one hJ]
    exact hcut i
  obtain ⟨i, F, B, hF, hB, hFR, hFC, hfrontF, hFB, hFT, hother, havoid⟩ :=
    exists_outermost_PL_crosscut_disk_avoiding_hole hR hC' hCD'
      (fun i => (hT i).of_isPLHomeomorphOn (hσT i)) hcut' hdisj' hCT'
  let τ := Function.invFunOn σ D
  have hτ : IsPLHomeomorphOn τ R D := hσ.symm
  have hBR : B ⊆ R := hFB ▸ (inter_subset_left.trans hFR)
  have hτF := hτ.restrict hF.isPolyhedron hFR
  have hτB := hτ.restrict hB.isPolyhedron hBR
  have hτimage (S : Set E) (hSD : S ⊆ D) : τ '' (σ '' S) = S := by
    rw [← image_comp]
    exact (show EqOn (τ ∘ σ) id S from fun _ hx =>
      hσ.bijOn.invOn_invFunOn.1 (hSD hx)).image_eq.trans (image_id S)
  have hτrim : τ '' frontier R = r '' stdSimplexBoundary 2 := by
    rw [← hσrim]
    exact hτimage _ hrimD
  obtain ⟨q, hq⟩ := hF
  refine ⟨i, τ '' F, τ '' B, τ ∘ q, hq.trans hτF, hB.of_isPLHomeomorphOn hτB,
    image_subset_iff.mpr (hτ.bijOn.mapsTo.mono_left hFR), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply disjoint_left.mpr
    rintro _ ⟨x, hx, rfl⟩ hxC
    exact disjoint_left.mp hFC hx
      ⟨τ x, hxC, hσ.bijOn.invOn_invFunOn.2 (hFR hx)⟩
  · rw [image_comp, hq.image_stdSimplexBoundary, hfrontF, image_union,
      hτimage (T i) (hTD i)]
  · rw [← hτrim, ← hτ.bijOn.injOn.image_inter hFR hR.isPolyhedron.isClosed.frontier_subset,
      hFB]
  · have hTR : (⋃ j, σ '' T j) ⊆ R :=
      iUnion_subset fun j => image_subset_iff.mpr (hσ.bijOn.mapsTo.mono_left (hTD j))
    have hτT : τ '' (⋃ j, σ '' T j) = ⋃ j, T j := by
      rw [image_iUnion]
      exact iUnion_congr fun j => hτimage (T j) (hTD j)
    rw [← hτT, ← hτ.bijOn.injOn.image_inter hFR hTR, hFT, hτimage (T i) (hTD i)]
  · intro j hji
    apply disjoint_left.mpr
    rintro _ ⟨x, hx, rfl⟩ hxT
    exact disjoint_left.mp (hother j hji) hx
      ⟨τ x, hxT, hσ.bijOn.invOn_invFunOn.2 (hFR hx)⟩
  · intro Z hZ hZD hZT hZC
    have hZ' := hZ.image σ (hσ.isPiecewiseAffineOn.continuousOn.mono hZD)
    have hZR : σ '' Z ⊆ R :=
      image_subset_iff.mpr (hσ.bijOn.mapsTo.mono_left hZD)
    have hZT' : Disjoint (σ '' Z) (σ '' T i) := by
      apply disjoint_left.mpr
      rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hyx⟩
      exact disjoint_left.mp hZT hx
        (hσ.bijOn.injOn (hTD i hy) (hZD hx) hyx ▸ hy)
    obtain ⟨a, haZ, haC⟩ := hZC
    have hd := havoid (σ '' Z) hZ' hZR hZT'
      ⟨σ a, ⟨a, haZ, rfl⟩, ⟨a, haC, rfl⟩⟩
    apply disjoint_left.mpr
    rintro _ ⟨x, hx, rfl⟩ hxZ
    exact disjoint_left.mp hd hx
      ⟨τ x, hxZ, hσ.bijOn.invOn_invFunOn.2 (hFR hx)⟩

end DifferentialGeometry.Topology.PiecewiseLinear
