/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceSplitPrismChart
import DifferentialGeometry.Topology.PiecewiseLinear.ExhaustionGeneral
import DifferentialGeometry.Topology.PiecewiseLinear.PieceTransition
import DifferentialGeometry.Topology.PiecewiseLinear.PieceMap
import DifferentialGeometry.Topology.PiecewiseLinear.BallFrontier
import DifferentialGeometry.Topology.PiecewiseLinear.StdChart

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

open Classical in
theorem exists_centeredPrism_of_isPLOn {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [T2Space M] [HasGroupoid M (plGroupoid 3)]
    {β : EuclideanSpace ℝ (Fin 2) → M} {E₁ E₂ : Set (EuclideanSpace ℝ (Fin 2))} {V : Set M}
    (hE₁ : IsPLBall 2 E₁) (hE₂ : IsPLBall 2 E₂) (hE₁₂ : E₁ ⊆ interior E₂)
    (hβ : IsPLOn 2 3 β E₂) (hinj : InjOn β E₂) (hV : IsOpen V) (hβV : β '' E₂ ⊆ V) :
    ∃ (prism : (Fin 3 → ℝ) × ℝ → M) (b : EuclideanSpace ℝ (Fin 2) → (Fin 3 → ℝ)),
      ContinuousOn prism (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (-1 : ℝ) 1) ∧
        InjOn prism (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (-1 : ℝ) 1) ∧
          prism '' (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (-1 : ℝ) 1) ⊆ V ∧
            (∀ x ∈ E₁, prism '' (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (-1 : ℝ) 1) ∈ 𝓝 (β x)) ∧
              prism '' (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ {(0 : ℝ)}) =
                β '' E₂ ∩ prism '' (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (-1 : ℝ) 1) ∧
                MapsTo b E₁ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) ∧ IsPiecewiseAffineOn b E₁ ∧
                  (∀ x ∈ E₁, prism (b x, 0) = β x) ∧
                    ∀ (G : EuclideanSpace ℝ (Fin 2) → (Fin 3 → ℝ) × ℝ)
                      (S : Set (EuclideanSpace ℝ (Fin 2))), IsPiecewiseAffineOn G S →
                        MapsTo G S (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (-1 : ℝ) 1) →
                          IsPLOn 2 3 (prism ∘ G) S := by
  classical
  obtain ⟨x₀, hx₀⟩ := hE₂.nonempty
  have _ : Nonempty M := ⟨β x₀⟩
  have hβcont : ContinuousOn β E₂ := fun x hx => (hβ x hx).continuousWithinAt
  have hcomp : IsCompact (β '' E₂) := hE₂.isPolyhedron.isCompact.image_of_continuousOn hβcont
  obtain ⟨P, -, ⟨Tp, hTp⟩, hCP, hPV⟩ :=
    exists_isPolyhedralManifoldWithBoundary_neighborhood (m := 2) hcomp hV hβV
  set T := Tp.piece with hTdef
  have _ : Finite T.complex.faces := T.finite_faces.to_subtype
  have hβP : ∀ x ∈ E₂, β x ∈ P := fun x hx => interior_subset (hCP ⟨x, hx, rfl⟩)
  set β' : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin Tp.ambientDim) :=
    Function.invFunOn T.map T.complex.space ∘ β with hβ'def
  have hβ'pa : IsPiecewiseAffineOn β' E₂ := by
    have h := T.isPiecewiseAffineOn_invFunOn_comp hβ
    rwa [inter_eq_left.mpr (show E₂ ⊆ β ⁻¹' P from fun x hx => hβP x hx)] at h
  have hβ'K : ∀ x ∈ E₂, β' x ∈ T.complex.space := fun x hx =>
    T.bijOn.surjOn.mapsTo_invFunOn (hβP x hx)
  have hβ'map : ∀ x ∈ E₂, T.map (β' x) = β x := fun x hx =>
    T.bijOn.invOn_invFunOn.2 (hβP x hx)
  have hβ'inj : InjOn β' E₂ := by
    intro x hx y hy hxy
    apply hinj hx hy
    rw [← hβ'map x hx, ← hβ'map y hy, hxy]
  have hβ'pl : IsPLHomeomorphOn β' E₂ (β' '' E₂) :=
    isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn hE₂.isPolyhedron hβ'pa hβ'inj.bijOn_image
  have hE₁E₂ : E₁ ⊆ E₂ := hE₁₂.trans interior_subset
  obtain ⟨ψ₁, hψ₁⟩ := id hE₁
  obtain ⟨ψ₂, hψ₂⟩ := id hE₂
  have hΔ : IsPLBall 2 (β' '' E₁) :=
    ⟨β' ∘ ψ₁, hψ₁.trans (hβ'pl.restrict hE₁.isPolyhedron hE₁E₂)⟩
  have hr₂ : IsPLHomeomorphOn (β' ∘ ψ₂) (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (β' '' E₂) := hψ₂.trans hβ'pl
  have hΔint : β' '' E₁ ⊆ (β' ∘ ψ₂) '' openSimplex (stdVertices 1) := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, rfl⟩ := hψ₂.bijOn.surjOn (hE₁E₂ hx)
    refine ⟨y, ?_, rfl⟩
    by_contra hyopen
    have hyb : y ∈ stdSimplexBoundary 2 := by
      refine ⟨hy, ?_⟩
      by_contra hne
      push Not at hne
      exact hyopen ((mem_openSimplex_stdVertices_iff 1).mpr
        ⟨fun i => lt_of_le_of_ne (hy.1 i) (hne i).symm, hy.2⟩)
    have hfr : ψ₂ y ∈ frontier E₂ := by
      rw [← hψ₂.image_stdSimplexBoundary]
      exact ⟨y, hyb, rfl⟩
    exact hfr.2 (hE₁₂ hx)
  have hΔD₂ : β' '' E₁ ⊆ β' '' E₂ := image_mono hE₁E₂
  have hΔK : β' '' E₁ ⊆ T.complex.space := by
    rintro _ ⟨x, hx, rfl⟩
    exact hβ'K x (hE₁E₂ hx)
  have hD₂K : β' '' E₂ ⊆ T.complex.space := by
    rintro _ ⟨x, hx, rfl⟩
    exact hβ'K x hx
  let _ : DecidableEq (EuclideanSpace ℝ (Fin Tp.ambientDim)) := Classical.decEq _
  let _ : Finite (boundaryComplex 3 T.complex).faces :=
    (boundaryComplex_faces_finite 3 T.complex).to_subtype
  have hbdclosed : IsClosed (boundaryComplex 3 T.complex).space :=
    (isPolyhedron_space (boundaryComplex 3 T.complex)).isClosed
  have hΔbd : β' '' E₂ ⊆ ((boundaryComplex 3 T.complex).space)ᶜ := by
    rintro _ ⟨x, hx, rfl⟩ hxbd
    have hint : T.map (β' x) ∈ interior P := by
      rw [hβ'map x hx]
      exact hCP ⟨x, hx, rfl⟩
    exact (T.mem_interior_iff_not_mem_boundaryComplex_space (n := 2) hTp (hβ'K x hx)).mp hint
      hxbd
  have hU : T.complex.space \ (boundaryComplex 3 T.complex).space ∈
      𝓝ˢ[T.complex.space] (β' '' E₁) :=
    mem_nhdsSetWithin.mpr ⟨_, hbdclosed.isOpen_compl, hΔD₂.trans hΔbd,
      fun z hz => ⟨hz.2, hz.1⟩⟩
  have hUdis : Disjoint (T.complex.space \ (boundaryComplex 3 T.complex).space)
      (boundaryComplex 3 T.complex).space := disjoint_sdiff_left
  obtain ⟨R, A, -, -, -, -, -, -, -, g, ρ, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
      -, hΔN, hNK, -, hnhds, -, -, hg, -, -, -, -, -, -, -, -, -, hρ, hρmid, -, -⟩ :=
    hTp.exists_isSubdivision_disk_pair_with_centered_prism hΔ hΔ hr₂ hΔint subset_rfl hΔD₂
      (inter_eq_left.mpr hΔD₂) hΔK hD₂K hU hUdis
  set N := (PiecewiseLinear.derivedNeighborhood R A).space with hNdef
  have hρN : ∀ p ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (-1 : ℝ) 1, ρ p ∈ T.complex.space :=
    fun p hp => hNK (hρ.bijOn.mapsTo hp)
  have hgN : ∀ x ∈ E₁, β' x ∈ β' '' E₂ ∩ N := fun x hx =>
    ⟨⟨x, hE₁E₂ hx, rfl⟩, hΔN ⟨x, hx, rfl⟩⟩
  have himage : (T.map ∘ ρ) '' (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (-1 : ℝ) 1) = T.map '' N := by
    rw [image_comp, hρ.image_eq]
  refine ⟨T.map ∘ ρ, Function.invFunOn g (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) ∘ β', ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · exact T.continuousOn.comp hρ.isPiecewiseAffineOn.continuousOn hρN
  · intro p hp q hq hpq
    exact hρ.bijOn.injOn hp hq (T.bijOn.injOn (hρN p hp) (hρN q hq) hpq)
  · rw [himage]
    rintro _ ⟨y, hy, rfl⟩
    exact hPV (T.bijOn.mapsTo (hNK hy))
  · intro x hx
    rw [himage]
    have hP : P ∈ 𝓝 (T.map (β' x)) := by
      rw [hβ'map x (hE₁E₂ hx)]
      exact mem_interior_iff_mem_nhds.mp (hCP ⟨x, hE₁E₂ hx, rfl⟩)
    have h := T.image_mem_nhds_of_mem_nhds (hβ'K x (hE₁E₂ hx)) hP (hnhds _ ⟨x, hx, rfl⟩)
    rwa [hβ'map x (hE₁E₂ hx)] at h
  · have hcenter : ρ '' (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ {(0 : ℝ)}) = g '' Convexity.StdSimplex.coordinateSet ℝ (Fin 3) := by
      ext y
      constructor
      · rintro ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩
        have ht0 : t = 0 := ht
        rw [ht0]
        exact ⟨x, hx, (hρmid x hx).symm⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨(x, 0), ⟨hx, rfl⟩, hρmid x hx⟩
    have hD₂img : T.map '' (β' '' E₂) = β '' E₂ := by
      rw [image_image]
      exact image_congr fun x hx => hβ'map x hx
    rw [himage, image_comp, hcenter, hg.image_eq,
      T.bijOn.injOn.image_inter hD₂K hNK, hD₂img]
  · intro x hx
    exact hg.bijOn.surjOn.mapsTo_invFunOn (hgN x hx)
  · have h := hg.symm.isPiecewiseAffineOn.comp hβ'pa
    have hsub : E₁ ⊆ E₂ ∩ β' ⁻¹' (β' '' E₂ ∩ N) := fun x hx => ⟨hE₁E₂ hx, hgN x hx⟩
    exact h.mono_of_isPolyhedron hE₁.isPolyhedron hsub
  · intro x hx
    change T.map (ρ (Function.invFunOn g (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (β' x), 0)) = β x
    rw [hρmid _ (hg.bijOn.surjOn.mapsTo_invFunOn (hgN x hx)),
      hg.bijOn.invOn_invFunOn.2 (hgN x hx), hβ'map x (hE₁E₂ hx)]
  · intro G S hG hGS
    have hpa : IsPiecewiseAffineOn (ρ ∘ G) S := by
      have h := hρ.isPiecewiseAffineOn.comp hG
      rwa [inter_eq_left.mpr
        (show S ⊆ G ⁻¹' (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (-1 : ℝ) 1) from hGS)] at h
    exact T.isPLOn_comp hpa fun x hx => hρN (G x) (hGS hx)

end DifferentialGeometry.Topology.PiecewiseLinear
