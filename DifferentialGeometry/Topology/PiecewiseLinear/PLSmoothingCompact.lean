/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Smoothing
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryComplexPLCellAttachmentZero
import DifferentialGeometry.Topology.PiecewiseLinear.RelativeBoundaryGluing
import DifferentialGeometry.Topology.PiecewiseLinear.IsSmoothHandleStageAdjunctionZero
import DifferentialGeometry.Topology.PiecewiseLinear.IsSmoothHandleStageAdjunctionThree
import DifferentialGeometry.Topology.PiecewiseLinear.IsSmoothHandleStageAdjunctionOne
import DifferentialGeometry.Topology.PiecewiseLinear.IsSmoothHandleStageAdjunctionTwo
import DifferentialGeometry.Topology.PiecewiseLinear.SmoothBoundaryDisksTaming
import DifferentialGeometry.Topology.PiecewiseLinear.BoundarySphereComponent
import DifferentialGeometry.Topology.PiecewiseLinear.BoundarySurfaceEmbedding
import DifferentialGeometry.Topology.PiecewiseLinear.SmoothAnnulusTaming
import DifferentialGeometry.Topology.PiecewiseLinear.Exhaustion
import DifferentialGeometry.Topology.PiecewiseLinear.PieceParametrization
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedNeighborhoodHandleFiltration
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryInvariance
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryFaces
import DifferentialGeometry.Topology.Attachment.Homeomorph
import DifferentialGeometry.Topology.Manifold.InteriorAtlas
import Mathlib.Geometry.Manifold.SmoothEmbedding
import Mathlib.Geometry.Manifold.Instances.Sphere
import DifferentialGeometry.Topology.Manifold.SphereDiffeomorph

open Set Topology Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.PiecewiseLinear

open DifferentialGeometry.Topology.SimplicialComplex (geometricFacePrefix)

universe u

def PLSmoothingCompact (n : ℕ) : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [T2Space X] [SecondCountableTopology X] [CompactSpace X]
    (C : ChartedSpace (EuclideanSpace ℝ (Fin n)) X),
    (letI := C; HasGroupoid X (plGroupoid n)) →
    ∃ C' : ChartedSpace (EuclideanSpace ℝ (Fin n)) X,
      letI := C'
      IsManifold (𝓡 n) ∞ X

def PLSmoothingModelCompact (n : ℕ) : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [T2Space X] [SecondCountableTopology X] [CompactSpace X]
    (C : ChartedSpace (EuclideanSpace ℝ (Fin n)) X),
    (letI := C; HasGroupoid X (plGroupoid n)) →
    ∃ (N : Type u) (_ : TopologicalSpace N) (_ : ChartedSpace (EuclideanSpace ℝ (Fin n)) N),
      IsManifold (𝓡 n) ∞ N ∧ Nonempty (X ≃ₜ N)

theorem plSmoothingCompact_of_plSmoothingModelCompact {n : ℕ}
    (h : PLSmoothingModelCompact.{u} n) : PLSmoothingCompact.{u} n := by
  intro X _ _ _ _ C hC
  obtain ⟨N, _, _, hN, ⟨e⟩⟩ := h C hC
  exact ⟨DifferentialGeometry.Manifold.Homeomorph.pullbackChartedSpace e,
    DifferentialGeometry.Manifold.Homeomorph.instIsManifoldPullback (I := 𝓡 n) (n := ∞) e⟩

theorem exists_isManifold_of_plApproximation_of_plSmoothingCompact {n : ℕ} {X : Type u}
    [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]
    (hA : PLApproximation.{u} n) (hB : PLSmoothingCompact.{u} n) :
    ∃ C : ChartedSpace (EuclideanSpace ℝ (Fin n)) X,
      letI := C
      IsManifold (𝓡 n) ∞ X := by
  have hsc : SecondCountableTopology X :=
    ChartedSpace.secondCountable_of_sigmaCompact (H := EuclideanSpace ℝ (Fin n)) (M := X)
  obtain ⟨C, hC⟩ := exists_chartedSpace_hasGroupoid_plGroupoid_of_plApproximation (X := X) hA
  exact hB C hC

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

section SphereRecognition

open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary

theorem nonempty_diffeomorph_sphere_of_homeomorph_sphere
    {S : Type} [TopologicalSpace S] [T2Space S] [CompactSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]
    (h : S ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    Nonempty (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ≃ₘ⟮𝓡 2, 𝓡 2⟯ S) := by
  let _ := (inferInstance : CompactSpace S)
  exact h.nonempty_diffeomorph_sphere

theorem exists_isSmoothEmbedding_sphere_of_isClosedEmbedding
    {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
    [IsManifold (𝓡∂ 3) ∞ M] [T2Space M]
    (ψ : {z : Convexity.StdSimplex.coordinateSet ℝ (Fin 4) | z.val ∈ stdSimplexBoundary 3} → M)
    (hψ : IsClosedEmbedding ψ) (hψbd : range ψ ⊆ (𝓡∂ 3).boundary M) :
    ∃ d : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → M,
      IsSmoothEmbedding (𝓡 2) (𝓡∂ 3) ∞ d ∧ range d = range ψ := by
  obtain ⟨W, -, hWc, hWimg, ⟨h⟩⟩ := exists_opens_boundaryManifold_homeomorph_sphere ψ hψ hψbd
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 2)) (BoundaryManifold (𝓡∂ 3) M) :=
    BoundaryManifold.chartedSpace (I := 𝓡∂ 3)
  let _ : IsManifold (𝓡 2) ∞ (BoundaryManifold (𝓡∂ 3) M) :=
    BoundaryManifold.isManifold (I := 𝓡∂ 3)
  obtain ⟨D⟩ := nonempty_diffeomorph_sphere_of_homeomorph_sphere (S := W) h
  have _ : Nonempty (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
    (NormedSpace.sphere_nonempty.mpr zero_le_one).to_subtype
  refine ⟨fun x => ((D x : BoundaryManifold (𝓡∂ 3) M) : M),
    isSmoothEmbedding_coe_of_diffeomorph_boundary_opens W D, ?_⟩
  rw [← hWimg]
  ext p
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨D x, (D x).2, rfl⟩
  · rintro ⟨q, hq, rfl⟩
    refine ⟨D.symm ⟨q, hq⟩, ?_⟩
    change (((D (D.symm ⟨q, hq⟩)) : BoundaryManifold (𝓡∂ 3) M) : M) = q
    rw [D.apply_symm_apply]

end SphereRecognition

theorem isSmoothHandleStage_of_attachment
    {P B R Fr : Set F} (hRB : R ⊆ B) (hBR : B \ R ⊆ Fr) (hFrP : Fr ⊆ P) (hBP : B ⊆ P)
    {L : Geometry.SimplicialComplex ℝ E} {C N' : Set E} {g : F → E}
    (hg : IsPLHomeomorphOn g P C) (hgB : IsPLHomeomorphOn g B (C ∩ L.space))
    {S T : Set E} (hSL : S ⊆ L.space) (hT : T = (S \ g '' R) ∪ g '' Fr)
    (φ : {z : P | z.val ∈ B} → L.space) (hφg : ∀ z, (φ z : E) = g z.val.val)
    (e : AdjunctionSpace (Subtype.val : {z : P | z.val ∈ B} → P) φ ≃ₜ N')
    (helow : ∀ x, (e (adjunctionLower φ x) : E) = x)
    (hecell : ∀ z, (e (adjunctionCell Subtype.val φ z) : E) = g z.val)
    {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
    (h : L.space ≃ₜ M) (hbd : h '' (Subtype.val ⁻¹' S) = (𝓡∂ 3).boundary M)
    (θ : M ≃ₜ M) (hθ : θ '' (𝓡∂ 3).boundary M = (𝓡∂ 3).boundary M)
    (ψ : {z : P | z.val ∈ B} → M) (hψ : ∀ z, ψ z = θ (h (φ z)))
    (hstage : IsSmoothHandleStage
      (AdjunctionSpace (Subtype.val : {z : P | z.val ∈ B} → P) ψ)
      (adjunctionLower ψ '' ((𝓡∂ 3).boundary M \ ψ '' {z | z.val.val ∈ R}) ∪
        adjunctionCell Subtype.val ψ '' {z : P | z.val ∈ Fr})) :
    IsSmoothHandleStage N' (Subtype.val ⁻¹' T) := by
  have hgim : g '' B = C ∩ L.space := hgB.bijOn.image_eq
  have hmemB : ∀ w ∈ P, g w ∈ L.space → w ∈ B := by
    intro w hw hwL
    have hw' : g w ∈ g '' B := by
      rw [hgim]
      exact ⟨hg.bijOn.mapsTo hw, hwL⟩
    obtain ⟨b, hb, hbw⟩ := hw'
    rwa [← hg.bijOn.injOn (hBP hb) hw hbw]
  have hθmem : ∀ {x}, x ∈ (𝓡∂ 3).boundary M → θ x ∈ (𝓡∂ 3).boundary M := by
    intro x hx
    rw [← hθ]
    exact ⟨x, hx, rfl⟩
  have hθmem' : ∀ {x}, θ x ∈ (𝓡∂ 3).boundary M → x ∈ (𝓡∂ 3).boundary M := by
    intro x hx
    rw [← hθ] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    rwa [← θ.injective hyx]
  have hS : ∀ x : L.space, x.val ∈ S ↔ h x ∈ (𝓡∂ 3).boundary M := by
    intro x
    rw [← hbd]
    constructor
    · intro hx
      exact ⟨x, hx, rfl⟩
    · rintro ⟨x', hx', hxx⟩
      rwa [← h.injective hxx]
  let adjH := adjunctionHomeomorph (Subtype.val : {z : P | z.val ∈ B} → P) φ
    (Subtype.val : {z : P | z.val ∈ B} → P) ψ (Equiv.refl _) (Homeomorph.refl P) (h.trans θ)
    (fun _ => rfl) (fun u => (hψ u).symm)
  let E' : N' ≃ₜ AdjunctionSpace (Subtype.val : {z : P | z.val ∈ B} → P) ψ := e.symm.trans adjH
  have hE'lower : ∀ x, E' (e (adjunctionLower φ x)) = adjunctionLower ψ (θ (h x)) := by
    intro x
    change adjH (e.symm (e (adjunctionLower φ x))) = _
    rw [Homeomorph.symm_apply_apply]
    rfl
  have hE'cell : ∀ z,
      E' (e (adjunctionCell Subtype.val φ z)) = adjunctionCell Subtype.val ψ z := by
    intro z
    change adjH (e.symm (e (adjunctionCell Subtype.val φ z))) = _
    rw [Homeomorph.symm_apply_apply]
    rfl
  have key : adjunctionLower ψ '' ((𝓡∂ 3).boundary M \ ψ '' {z | z.val.val ∈ R}) ∪
      adjunctionCell Subtype.val ψ '' {z | z.val ∈ Fr} = E' '' (Subtype.val ⁻¹' T) := by
    apply Subset.antisymm
    · rintro p (⟨m, ⟨hm, hmR⟩, rfl⟩ | ⟨z, hz, rfl⟩)
      · have hθhx : θ (h (h.symm (θ.symm m))) = m := by simp
        refine ⟨e (adjunctionLower φ (h.symm (θ.symm m))), ?_, ?_⟩
        · change (e (adjunctionLower φ (h.symm (θ.symm m)))).val ∈ T
          rw [helow, hT]
          refine Or.inl ⟨?_, ?_⟩
          · exact (hS _).mpr (hθmem' (by rw [hθhx]; exact hm))
          · rintro ⟨r, hr, hrx⟩
            apply hmR
            refine ⟨⟨⟨r, hBP (hRB hr)⟩, hRB hr⟩, hr, ?_⟩
            have hφu : φ ⟨⟨r, hBP (hRB hr)⟩, hRB hr⟩ = h.symm (θ.symm m) := by
              apply Subtype.ext
              rw [hφg]
              exact hrx
            rw [hψ, hφu, hθhx]
        · rw [hE'lower, hθhx]
      · refine ⟨e (adjunctionCell Subtype.val φ z), ?_, hE'cell z⟩
        change (e (adjunctionCell Subtype.val φ z)).val ∈ T
        rw [hecell, hT]
        exact Or.inr ⟨z.val, hz, rfl⟩
    · rintro _ ⟨y, hy, rfl⟩
      have hq : ∀ q : AdjunctionSpace (Subtype.val : {z : P | z.val ∈ B} → P) φ,
          (e q).val ∈ T →
          E' (e q) ∈ adjunctionLower ψ '' ((𝓡∂ 3).boundary M \ ψ '' {z | z.val.val ∈ R}) ∪
            adjunctionCell Subtype.val ψ '' {z | z.val ∈ Fr} := by
        intro q hqT
        induction q using Quot.ind with
        | mk s =>
          cases s with
          | inl z =>
            change (e (adjunctionCell Subtype.val φ z)).val ∈ T at hqT
            change E' (e (adjunctionCell Subtype.val φ z)) ∈ _
            rw [hE'cell]
            rw [hecell, hT] at hqT
            refine Or.inr ⟨z, ?_, rfl⟩
            change z.val ∈ Fr
            rcases hqT with ⟨hzS, hzR⟩ | ⟨w, hw, hwz⟩
            · have hzB : z.val ∈ B := hmemB z.val z.property (hSL hzS)
              exact hBR ⟨hzB, fun hr => hzR ⟨z.val, hr, rfl⟩⟩
            · have hwz' : w = z.val := hg.bijOn.injOn (hFrP hw) z.property hwz
              rw [← hwz']
              exact hw
          | inr x =>
            change (e (adjunctionLower φ x)).val ∈ T at hqT
            change E' (e (adjunctionLower φ x)) ∈ _
            rw [hE'lower]
            rw [helow, hT] at hqT
            rcases hqT with ⟨hxS, hxR⟩ | ⟨w, hw, hwx⟩
            · refine Or.inl ⟨θ (h x), ⟨hθmem ((hS x).mp hxS), ?_⟩, rfl⟩
              rintro ⟨u, hu, hux⟩
              rw [hψ] at hux
              exact hxR ⟨u.val.val, hu,
                (hφg u).symm.trans (congrArg Subtype.val (h.injective (θ.injective hux)))⟩
            · have hwB : w ∈ B := hmemB w (hFrP hw) (by rw [hwx]; exact x.property)
              have hφu : φ ⟨⟨w, hBP hwB⟩, hwB⟩ = x := by
                apply Subtype.ext
                rw [hφg]
                exact hwx
              refine Or.inr ⟨(⟨⟨w, hBP hwB⟩, hwB⟩ : {z : P | z.val ∈ B}).val, hw, ?_⟩
              rw [adjunction_coherence, hψ, hφu]
      have hq' := hq (e.symm y) (by rw [Homeomorph.apply_symm_apply]; exact hy)
      rwa [Homeomorph.apply_symm_apply] at hq'
  have hfinal := hstage.transport E'.symm
  have hUU : E'.symm '' (E' '' (Subtype.val ⁻¹' T)) = Subtype.val ⁻¹' T :=
    E'.toEquiv.symm_image_image _
  rw [key, hUU] at hfinal
  exact hfinal

open Classical in
theorem isSmoothHandleStage_step [FiniteDimensional ℝ E]
    {L N' : Geometry.SimplicialComplex ℝ E} [Finite L.faces] [Finite N'.faces]
    (hL : IsCombinatorialManifoldWithBoundary 3 L)
    (hN' : IsCombinatorialManifoldWithBoundary 3 N') {C : Set E} (k : Fin 4)
    (hatt : IsPLThreeHandleAttachment k L C N'.space)
    (hstage : IsSmoothHandleStage L.space (Subtype.val ⁻¹' (boundaryComplex 3 L).space)) :
    IsSmoothHandleStage N'.space (Subtype.val ⁻¹' (boundaryComplex 3 N').space) := by
  obtain ⟨M, iT, iC, hM, hT2, hc, h, hbd⟩ := hstage
  have hrefl : (Homeomorph.refl M) '' (𝓡∂ 3).boundary M = (𝓡∂ 3).boundary M := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hSL : (boundaryComplex 3 L).space ⊆ L.space := boundaryComplex_space_subset 3 L
  fin_cases k
  · change IsPLCellAttachment 3 (Convexity.StdSimplex.coordinateSet ℝ (Fin 4)) ∅ L C N'.space at hatt
    obtain ⟨g, hg⟩ := hatt.exists_isPLCellAttachmentWith
    have hT := boundaryComplex_space_of_isPLCellAttachmentWith_zero hL hN' hg
    obtain ⟨-, hBP, hgP, hgB, φ, -, hφg, -, e, helow, hecell⟩ := hg
    refine isSmoothHandleStage_of_attachment (R := ∅) (Fr := stdSimplexBoundary 3) Subset.rfl
      (fun _ hx => absurd hx.1 (Set.notMem_empty _)) (fun _ hx => hx.1) hBP hgP hgB hSL ?_ φ
      hφg e helow hecell h hbd (Homeomorph.refl M) hrefl (fun z => h (φ z)) (fun _ => rfl) ?_
    · rw [hT, Set.image_empty, Set.sdiff_empty]
    · have hR : (fun z => h (φ z)) '' {z | z.val.val ∈ (∅ : Set (Fin 4 → ℝ))} = ∅ := by
        ext p
        simp
      rw [hR, Set.sdiff_empty]
      exact isSmoothHandleStage_adjunction_zero _
  · change IsPLCellAttachment 3 (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (0 : ℝ) 1)
      (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ ({0, 1} : Set ℝ)) L C N'.space at hatt
    obtain ⟨g, hg⟩ := hatt.exists_isPLCellAttachmentWith
    have hT := boundaryComplex_space_of_isPLCellAttachmentWith_one hL hN' hg
    obtain ⟨-, hBP, hgP, hgB, φ, hφemb, hφg, hφbd, e, helow, hecell⟩ := hg
    have hψ₀ : IsClosedEmbedding (fun z => h (φ z)) := h.isClosedEmbedding.comp hφemb
    have hψ₀bd : range (fun z => h (φ z)) ⊆ (𝓡∂ 3).boundary M := by
      rintro _ ⟨z, rfl⟩
      rw [← hbd]
      exact ⟨φ z, hφbd z, rfl⟩
    obtain ⟨θ, hθ, f, hf, hfbd, hdisj, hrange⟩ :=
      exists_homeomorph_smooth_disks_of_isClosedEmbedding _ hψ₀ hψ₀bd
    have hψ : IsClosedEmbedding (fun z => θ (h (φ z))) := θ.isClosedEmbedding.comp hψ₀
    have hrange' : range (fun z => θ (h (φ z))) = ⋃ j, f j '' Metric.closedBall 0 1 := by
      rw [← hrange, ← Set.range_comp']
    refine isSmoothHandleStage_of_attachment
      (R := (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) \ stdSimplexBoundary 2) ×ˢ ({0, 1} : Set ℝ))
      (Fr := stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)
      (Set.prod_mono Set.sdiff_subset Subset.rfl) ?_ (Set.prod_mono (fun _ hx => hx.1) Subset.rfl)
      hBP hgP hgB hSL hT φ hφg e helow hecell h hbd θ hθ (fun z => θ (h (φ z))) (fun _ => rfl)
      (isSmoothHandleStage_adjunction_one _ hψ f hf hfbd hdisj hrange')
    rintro ⟨x, t⟩ ⟨⟨hx, ht⟩, hnot⟩
    refine ⟨?_, ?_⟩
    · by_contra hxb
      exact hnot ⟨⟨hx, hxb⟩, ht⟩
    · rcases ht with rfl | rfl
      · exact ⟨le_rfl, zero_le_one⟩
      · exact ⟨zero_le_one, le_rfl⟩
  · change IsPLCellAttachment 3 (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (0 : ℝ) 1)
      (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) L C N'.space at hatt
    obtain ⟨g, hg⟩ := hatt.exists_isPLCellAttachmentWith
    have hT := boundaryComplex_space_of_isPLCellAttachmentWith_two hL hN' hg
    obtain ⟨-, hBP, hgP, hgB, φ, hφemb, hφg, hφbd, e, helow, hecell⟩ := hg
    have hψ₀ : IsClosedEmbedding (fun z => h (φ z)) := h.isClosedEmbedding.comp hφemb
    have hψ₀bd : range (fun z => h (φ z)) ⊆ (𝓡∂ 3).boundary M := by
      rintro _ ⟨z, rfl⟩
      rw [← hbd]
      exact ⟨φ z, hφbd z, rfl⟩
    obtain ⟨θ, hθ, f, hf, hfbd, hrange⟩ :=
      exists_homeomorph_smooth_annulus_of_isClosedEmbedding _ hψ₀ hψ₀bd
    have hψ : IsClosedEmbedding (fun z => θ (h (φ z))) := θ.isClosedEmbedding.comp hψ₀
    have hrange' : range (fun z => θ (h (φ z))) = f '' (univ ×ˢ Icc (0 : ℝ) 1) := by
      rw [← hrange, ← Set.range_comp']
    refine isSmoothHandleStage_of_attachment
      (R := stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1)
      (Fr := Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ ({0, 1} : Set ℝ))
      (Set.prod_mono Subset.rfl Set.Ioo_subset_Icc_self) ?_ ?_
      hBP hgP hgB hSL hT φ hφg e helow hecell h hbd θ hθ (fun z => θ (h (φ z))) (fun _ => rfl)
      (isSmoothHandleStage_adjunction_two _ hψ f hf hfbd hrange')
    · rintro ⟨x, t⟩ ⟨⟨hx, ht⟩, hnot⟩
      refine ⟨hx.1, ?_⟩
      by_contra htn
      apply hnot
      refine ⟨hx, ?_⟩
      have h0 : t ≠ 0 := fun h0 => htn (Or.inl h0)
      have h1 : t ≠ 1 := fun h1 => htn (Or.inr h1)
      exact ⟨lt_of_le_of_ne ht.1 (Ne.symm h0), lt_of_le_of_ne ht.2 h1⟩
    · rintro ⟨x, t⟩ ⟨hx, ht⟩
      refine ⟨hx, ?_⟩
      rcases ht with rfl | rfl
      · exact ⟨le_rfl, zero_le_one⟩
      · exact ⟨zero_le_one, le_rfl⟩
  · change IsPLCellAttachment 3 (Convexity.StdSimplex.coordinateSet ℝ (Fin 4)) (stdSimplexBoundary 3) L C N'.space
      at hatt
    obtain ⟨g, hg⟩ := hatt.exists_isPLCellAttachmentWith
    have hT := boundaryComplex_space_of_isPLCellAttachmentWith_three hL hN' hg
    obtain ⟨-, hBP, hgP, hgB, φ, hφemb, hφg, hφbd, e, helow, hecell⟩ := hg
    have hψ₀ : IsClosedEmbedding (fun z => h (φ z)) := h.isClosedEmbedding.comp hφemb
    have hψ₀bd : range (fun z => h (φ z)) ⊆ (𝓡∂ 3).boundary M := by
      rintro _ ⟨z, rfl⟩
      rw [← hbd]
      exact ⟨φ z, hφbd z, rfl⟩
    obtain ⟨d, hd, hrange⟩ := exists_isSmoothEmbedding_sphere_of_isClosedEmbedding _ hψ₀ hψ₀bd
    have hdbd : range d ⊆ (𝓡∂ 3).boundary M := by
      rw [hrange]
      exact hψ₀bd
    refine isSmoothHandleStage_of_attachment (R := stdSimplexBoundary 3) (Fr := ∅) Subset.rfl
      (fun _ hx => (hx.2 hx.1).elim) (Set.empty_subset _) hBP hgP hgB hSL ?_ φ hφg e helow
      hecell h hbd (Homeomorph.refl M) hrefl (fun z => h (φ z)) (fun _ => rfl) ?_
    · rw [hT, Set.image_empty, Set.union_empty]
    · have hR : (fun z => h (φ z)) '' {z | z.val.val ∈ stdSimplexBoundary 3} =
          range (fun z => h (φ z)) := by
        rw [← Set.image_univ]
        congr 1
        exact Set.eq_univ_of_forall fun z => z.property
      have hFr : adjunctionCell Subtype.val (fun z => h (φ z)) ''
          {z : Convexity.StdSimplex.coordinateSet ℝ (Fin 4) | z.val ∈ (∅ : Set (Fin 4 → ℝ))} = ∅ := by
        ext p
        simp
      rw [hR, hFr, Set.union_empty]
      exact isSmoothHandleStage_adjunction_three _ hψ₀ d hd hdbd hrange

open Classical in
theorem exists_boundarylessManifold_of_isCombinatorialManifold_three [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hK : IsCombinatorialManifold 3 K) :
    ∃ (M : Type) (_ : TopologicalSpace M) (_ : ChartedSpace (EuclideanHalfSpace 3) M),
      IsManifold (𝓡∂ 3) ∞ M ∧ BoundarylessManifold (𝓡∂ 3) M ∧ Nonempty (K.space ≃ₜ M) := by
  obtain ⟨m, e, he, k, -, -, hzero, hlast, -, hman, hstep⟩ :=
    exists_pl_three_handle_filtration K hK
  let N : ℕ → Geometry.SimplicialComplex ℝ E :=
    fun i => derivedNeighborhood K (geometricFacePrefix K e he i)
  have hzero' : (N 0).space = ∅ := hzero
  have hlast' : (N m).space = K.space := hlast
  have hman' : ∀ i, IsCombinatorialManifoldWithBoundary 3 (N i) := hman
  have hstep' : ∀ i : Fin m, IsPLThreeHandleAttachment (k i) (N i.val)
      (derivedNeighborhoodCell K (e i).val).space (N (i.val + 1)).space := hstep
  have hfin : ∀ i, Finite (N i).faces := fun i => (derivedNeighborhood_faces_finite _ _).to_subtype
  have hind : ∀ i, i ≤ m →
      IsSmoothHandleStage (N i).space (Subtype.val ⁻¹' (boundaryComplex 3 (N i)).space) := by
    intro i
    induction i with
    | zero =>
      intro _
      have : IsEmpty (N 0).space := ⟨fun x => Set.notMem_empty x.val (hzero' ▸ x.property)⟩
      exact isSmoothHandleStage_of_isEmpty _ _
    | succ i ih =>
      intro hi
      have := hfin i
      have := hfin (i + 1)
      exact isSmoothHandleStage_step (hman' i) (hman' (i + 1)) (k ⟨i, hi⟩) (hstep' ⟨i, hi⟩)
        (ih (Nat.le_of_succ_le hi))
  obtain ⟨M, iT, iC, hM, -, -, h, hbd⟩ := hind m le_rfl
  have := hfin m
  have hbdempty : (boundaryComplex 3 (N m)).space = ∅ := by
    have h1 : (boundaryComplex 3 (N m)).space = id '' (boundaryComplex 3 K).space :=
      boundaryComplex_space_of_isPLHomeomorphOn (n := 2) K (N m)
        hK.isCombinatorialManifoldWithBoundary (f := id)
        (by rw [hlast']; exact (isPolyhedron_space K).isPLHomeomorphOn_id)
    have h2 : (boundaryComplex 3 K).faces = ∅ := hK.boundaryComplex_faces_eq_empty K
    rw [h1, Set.image_id, Geometry.SimplicialComplex.space, h2]
    simp
  have hbdM : (𝓡∂ 3).boundary M = ∅ := by
    rw [← hbd, hbdempty, Set.preimage_empty, Set.image_empty]
  exact ⟨M, iT, iC, hM, ModelWithCorners.Boundaryless.of_boundary_eq_empty hbdM,
    ⟨(Homeomorph.setCongr hlast'.symm).trans h⟩⟩

theorem plSmoothingModelCompact_three : PLSmoothingModelCompact.{u} 3 := by
  intro X _ _ _ _ C hC
  let _ := C
  by_cases hX : Nonempty X
  · obtain ⟨T, hT⟩ := plManifoldTriangulation 3 C hC
    have : Finite T.complex.faces := T.finite_faces
    obtain ⟨M, iT, iC, hM, hbl, ⟨h⟩⟩ :=
      exists_boundarylessManifold_of_isCombinatorialManifold_three T.complex hT
    let iC' : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M :=
      DifferentialGeometry.Manifold.interiorChartedSpace (𝓡∂ 3) ∞ (M := M)
    have hM' : IsManifold (𝓡 3) ∞ M :=
      DifferentialGeometry.Manifold.interiorIsManifold (𝓡∂ 3) ∞ (M := M)
    refine ⟨ULift.{u} M, inferInstance,
      DifferentialGeometry.Manifold.Homeomorph.pullbackChartedSpace
        (Homeomorph.ulift : ULift.{u} M ≃ₜ M),
      DifferentialGeometry.Manifold.Homeomorph.instIsManifoldPullback (I := 𝓡 3) (n := ∞) _,
      ⟨?_⟩⟩
    have e₀ : T.complex.space ≃ₜ X := T.toPieceIn.homeomorph.trans (Homeomorph.Set.univ X)
    exact e₀.symm.trans (h.trans Homeomorph.ulift.symm)
  · have : IsEmpty X := not_nonempty_iff.mp hX
    exact ⟨X, inferInstance, C, IsManifold.empty _, ⟨Homeomorph.refl X⟩⟩

end DifferentialGeometry.Topology.PiecewiseLinear
