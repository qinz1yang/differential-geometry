import DifferentialGeometry.Topology.PiecewiseLinear.DiskCrosscut
import DifferentialGeometry.Topology.PiecewiseLinear.FourSpokeSphere
import DifferentialGeometry.Topology.PiecewiseLinear.DiskCrosscutExtension

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E2" => EuclideanSpace ℝ (Fin 2)

theorem exists_returning_crosscut_disk_avoiding_hole
    {D C A : Set E2} (hD : IsPLBall 2 D) (hC : IsPLBall 2 C) (hCD : C ⊆ D)
    (hA : IsPLBall 1 A) {p q : E2} (hcut : Schoenflies.IsCrosscut (frontier D) A p q)
    (hCA : Disjoint C A) :
    ∃ F B : Set E2, IsPLBall 2 F ∧ IsPLBall 1 B ∧ F ⊆ D ∧ Disjoint F C ∧
      frontier F = A ∪ B ∧ F ∩ frontier D = B := by
  obtain ⟨U, V, hU, hV, hcover, hmeet, hUF, hVF, hAU, hAV, hUB, hVB, hside⟩ :=
    exists_isPLBall_pair_with_boundary_arcs_of_isCrosscut hD hA hcut
  have hUD : U ⊆ D := subset_union_left.trans hcover.subset
  have hVD : V ⊆ D := subset_union_right.trans hcover.subset
  have hfront (F : Set E2) (hF : IsPLBall 2 F) (hFD : F ⊆ D)
      (hFA : frontier F ⊆ frontier D ∪ A) (hAF : A ⊆ frontier F) :
      frontier F = A ∪ (F ∩ frontier D) := by
    apply Subset.antisymm
    · intro x hx
      rcases hFA hx with hxD | hxA
      · exact Or.inr ⟨hF.isPolyhedron.isClosed.frontier_subset hx, hxD⟩
      · exact Or.inl hxA
    · rintro x (hxA | hxD)
      · exact hAF hxA
      · exact ⟨subset_closure hxD.1, fun hx => hxD.2.2 (interior_mono hFD hx)⟩
  rcases hside C hC hCD (hCA.mono_left interior_subset) with hCU | hCV
  · refine ⟨V, V ∩ frontier D, hV, hVB, hVD, ?_, hfront V hV hVD hVF hAV, rfl⟩
    exact disjoint_left.mpr fun x hxV hxC =>
      disjoint_left.mp hCA hxC (hmeet.subset ⟨hCU hxC, hxV⟩)
  · refine ⟨U, U ∩ frontier D, hU, hUB, hUD, ?_, hfront U hU hUD hUF hAU, rfl⟩
    exact disjoint_left.mpr fun x hxU hxC =>
      disjoint_left.mp hCA hxC (hmeet.subset ⟨hxU, hCV hxC⟩)

theorem IsPLHomeomorphOn.exists_returning_crosscut_disk_avoiding_hole
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {D C A : Set E} {r : (Fin 3 → ℝ) → E}
    (hr : IsPLHomeomorphOn r (stdSimplex ℝ (Fin 3)) D)
    (hC : IsPLBall 2 C) (hCD : C ⊆ D) {γ : ℝ → E}
    (hγ : IsPLHomeomorphOn γ (Icc 0 1) A) (hAD : A ⊆ D)
    (hends : A ∩ r '' stdSimplexBoundary 2 = {γ 0, γ 1}) (hCA : Disjoint C A) :
    ∃ (F B : Set E) (q : (Fin 3 → ℝ) → E),
      IsPLHomeomorphOn q (stdSimplex ℝ (Fin 3)) F ∧ IsPLBall 1 B ∧
      F ⊆ D ∧ Disjoint F C ∧ q '' stdSimplexBoundary 2 = A ∪ B ∧
      F ∩ r '' stdSimplexBoundary 2 = B := by
  have hD : IsPLBall 2 D := ⟨r, hr⟩
  have hA : IsPLBall 1 A := (isPLBall_Icc zero_lt_one).of_isPLHomeomorphOn hγ
  obtain ⟨J, σ, hJ, hσ⟩ := exists_planar_coordinates_of_isPLBall_two hD
  let R := closure (Schoenflies.inside J)
  have hR : IsPLBall 2 R := isPLBall_closure_inside_of_isPLSphere_one hJ
  have hrimD : r '' stdSimplexBoundary 2 ⊆ D :=
    (image_mono (fun _ hx => hx.1)).trans hr.image_eq.subset
  have hσrim : σ '' (r '' stdSimplexBoundary 2) = J := by
    rw [← image_comp]
    exact (hr.trans hσ).image_stdSimplexBoundary.trans
      (frontier_closure_inside_of_isPLSphere_one hJ)
  have hσC := hσ.restrict hC.isPolyhedron hCD
  have hσA := hσ.restrict hA.isPolyhedron hAD
  have hC' : IsPLBall 2 (σ '' C) := hC.of_isPLHomeomorphOn hσC
  have hA' : IsPLBall 1 (σ '' A) := hA.of_isPLHomeomorphOn hσA
  have hC'R : σ '' C ⊆ R := image_subset_iff.mpr (hσ.bijOn.mapsTo.mono_left hCD)
  have hdis : Disjoint (σ '' C) (σ '' A) := by
    apply disjoint_left.mpr
    rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hyx⟩
    have hxy := hσ.bijOn.injOn (hAD hy) (hCD hx) hyx
    exact disjoint_left.mp hCA hx (hxy ▸ hy)
  have hcut := isCrosscut_image_of_disk_arc hJ hσ hσrim hrimD hγ hAD hends
  rw [← frontier_closure_inside_of_isPLSphere_one hJ] at hcut
  obtain ⟨F, B, hF, hB, hFR, hFC, hfrontF, hFB⟩ :=
    DifferentialGeometry.Topology.PiecewiseLinear.exists_returning_crosscut_disk_avoiding_hole
      hR hC' hC'R hA' hcut hdis
  have hBR : B ⊆ R := hFB ▸ (inter_subset_left.trans hFR)
  let τ := Function.invFunOn σ D
  have hτ : IsPLHomeomorphOn τ R D := hσ.symm
  have hτF := hτ.restrict hF.isPolyhedron hFR
  have hτB := hτ.restrict hB.isPolyhedron hBR
  have hτimage (S : Set E) (hSD : S ⊆ D) : τ '' (σ '' S) = S := by
    rw [← image_comp]
    exact (show EqOn (τ ∘ σ) id S from fun _ hx =>
      hσ.bijOn.invOn_invFunOn.1 (hSD hx)).image_eq.trans (image_id S)
  have hτrim : τ '' frontier R = r '' stdSimplexBoundary 2 := by
    rw [frontier_closure_inside_of_isPLSphere_one hJ, ← hσrim]
    exact hτimage _ hrimD
  obtain ⟨q, hq⟩ := hF
  refine ⟨τ '' F, τ '' B, τ ∘ q, hq.trans hτF, hB.of_isPLHomeomorphOn hτB,
    image_subset_iff.mpr (hτ.bijOn.mapsTo.mono_left hFR), ?_, ?_, ?_⟩
  · apply disjoint_left.mpr
    rintro _ ⟨x, hx, rfl⟩ hxC
    have hσx := hσ.bijOn.invOn_invFunOn.2 (hFR hx)
    exact disjoint_left.mp hFC hx ⟨τ x, hxC, hσx⟩
  · rw [image_comp, hq.image_stdSimplexBoundary, hfrontF, image_union, hτimage A hAD]
  · rw [← hτrim, ← hτ.bijOn.injOn.image_inter hFR hR.isPolyhedron.isClosed.frontier_subset,
      hFB]

end DifferentialGeometry.Topology.PiecewiseLinear
