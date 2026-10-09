/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.DoubleBoundaryPush

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem exists_nonsingular_two_cell_of_disk_in_double_boundary_eqOn
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) :
    letI := combinatorialChartedSpace (double 3 K) (isCombinatorialManifold_double_succ_succ K hK)
    let ι := simplicialMap K (glueEmbed₂ (PiecewiseLinear.boundaryComplex 3 K) id)
    ∀ {R : Set (EuclideanSpace ℝ (Fin 2))} {D : Set (E × E × ℝ)}
        {r : EuclideanSpace ℝ (Fin 2) → E × E × ℝ},
      IsPLBall 2 R → IsPLHomeomorphOn r R D →
        D ⊆ ι '' (boundaryComplex 3 K).space →
          ∃ A : SingularTwoCell (double 3 K).space,
            A.domain = R ∧ A.IsNonsingular ∧
              Subtype.val '' (A '' A.domain) ⊆ ι '' K.space ∧
              EqOn (fun x => (A x : E × E × ℝ)) r (frontier R) ∧
              Set.range (fun x => (A.boundary x : E × E × ℝ)) = r '' frontier R ∧
              Subtype.val '' (A '' A.domain) ∩ ι '' (boundaryComplex 3 K).space =
                r '' frontier R := by
  classical
  let L := double 3 K
  have hL : IsCombinatorialManifold 3 L := isCombinatorialManifold_double_succ_succ K hK
  let _ := combinatorialChartedSpace L hL
  let B := boundaryComplex 3 K
  let ι : E → E × E × ℝ := simplicialMap K (glueEmbed₂ B id)
  dsimp only
  intro R D r hR hr hD
  have hι : IsPLHomeomorphOn ι K.space (glued₂ K B id).space :=
    isPLHomeomorphOn_embedComplex K (glueEmbed₂ B id) (glueSnd E E) (fun _ _ _ _ => rfl)
  have hcopy : ι '' K.space ⊆ L.space := by
    rw [hι.image_eq]
    change (glued₂ K B id).space ⊆ (double 3 K).space
    rw [double, gluedComplex_space]
    exact subset_union_right
  have hDcopy : D ⊆ (glued₂ K B id).space :=
    hD.trans ((image_mono (boundaryComplex_space_subset 3 K)).trans hι.image_eq.subset)
  let g := Function.invFunOn ι K.space
  have hDball : IsPLBall 2 D := hR.of_isPLHomeomorphOn hr
  have hgD : IsPLHomeomorphOn g D (g '' D) :=
    hι.symm.restrict hDball.isPolyhedron hDcopy
  have hD₀ : g '' D ⊆ B.space := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨x, hx, hxy⟩ := hD hy
    rw [← hxy]
    change Function.invFunOn ι K.space (ι x) ∈ B.space
    rw [hι.bijOn.invOn_invFunOn.1 (boundaryComplex_space_subset 3 K hx)]
    exact hx
  have hRball : IsPLBall 2 R := hR
  obtain ⟨p, hp⟩ := hR
  let r₀ := (g ∘ r) ∘ p
  have hr₀ : IsPLHomeomorphOn r₀ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (g '' D) :=
    hp.trans (hr.trans hgD)
  obtain ⟨Q, q, hq, hQK, hqboundary, hQboundary⟩ :=
    hK.exists_isPLHomeomorphOn_push_boundary_disk hr₀ hD₀
  let Q' := ι '' Q
  let q' := ι ∘ q
  have hQ : IsPLBall 2 Q := ⟨q, hq⟩
  have hιQ : IsPLHomeomorphOn ι Q Q' := hι.restrict hQ.isPolyhedron hQK
  have hq' : IsPLHomeomorphOn q' (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Q' := hq.trans hιQ
  have hQcopy : Q' ⊆ L.space := (image_mono hQK).trans hcopy
  have hfrontR : frontier R ⊆ R := hRball.isPolyhedron.isClosed.frontier_subset
  have hrfrontD : r '' frontier R ⊆ D := by
    rintro _ ⟨x, hx, rfl⟩
    exact hr.bijOn.mapsTo (hfrontR hx)
  have hιg : EqOn (ι ∘ g) id D := by
    intro y hy
    exact hι.bijOn.invOn_invFunOn.2 (hDcopy hy)
  have hpboundary : p '' stdSimplexBoundary 2 = frontier R :=
    hp.image_stdSimplexBoundary_eq_frontier
  have hq'r : q' '' stdSimplexBoundary 2 = r '' frontier R := by
    calc
      q' '' stdSimplexBoundary 2 = ι '' (q '' stdSimplexBoundary 2) := image_comp _ _ _
      _ = ι '' (r₀ '' stdSimplexBoundary 2) := congrArg (ι '' ·) hqboundary
      _ = (ι ∘ g) '' (r '' (p '' stdSimplexBoundary 2)) := by
        simp only [r₀, image_comp]
      _ = (ι ∘ g) '' (r '' frontier R) := by rw [hpboundary]
      _ = id '' (r '' frontier R) := (hιg.mono hrfrontD).image_eq
      _ = r '' frontier R := image_id _
  have hrfront : IsPLHomeomorphOn r (frontier R) (q' '' stdSimplexBoundary 2) := by
    rw [hq'r]
    exact hr.restrict hRball.isPLSphere_frontier.isPolyhedron hfrontR
  have hrboundary :
      IsPLHomeomorphOn r (p '' stdSimplexBoundary 2) (q' '' stdSimplexBoundary 2) := by
    rw [hpboundary]
    exact hrfront
  obtain ⟨H, hH, hHr⟩ :=
    exists_isPLHomeomorphOn_of_stdSimplexBoundary (n := 1) hp hq' hrboundary
  have hHboundary : EqOn H r (frontier R) := hpboundary ▸ hHr
  obtain ⟨x, hx⟩ := hRball.nonempty
  let T := combinatorialPLPieceIn L hL ⟨H x, hQcopy (hH.bijOn.mapsTo hx)⟩
  have hval (y : E × E × ℝ) (hy : y ∈ L.space) : (T.map y : E × E × ℝ) = y := by
    simp only [T, combinatorialPLPieceIn, dite_eq_left hy]
  have hHcopy : MapsTo H R L.space := fun _ hy => hQcopy (hH.bijOn.mapsTo hy)
  let A : SingularTwoCell L.space :=
    { domain := R
      isPLBall_domain := hRball
      toFun := T.map ∘ H
      isPLOn := T.isPLOn_comp hH.isPiecewiseAffineOn hHcopy }
  have hAeq : EqOn (fun z => (A z : E × E × ℝ)) H R := by
    intro z hz
    exact hval (H z) (hHcopy hz)
  have hAimage : Subtype.val '' (A '' A.domain) = Q' := by
    rw [← image_comp]
    change (fun z => (A z : E × E × ℝ)) '' R = Q'
    exact hAeq.image_eq.trans hH.image_eq
  have hAboundary :
      Set.range (fun z => (A.boundary z : E × E × ℝ)) = r '' frontier R := by
    change Set.range ((fun z => (A z : E × E × ℝ)) ∘
      (Subtype.val : frontier R → EuclideanSpace ℝ (Fin 2))) = _
    rw [range_comp, Subtype.range_coe]
    exact ((hAeq.mono hfrontR).trans hHboundary).image_eq
  have hQ'inter : Q' ∩ ι '' B.space = r '' frontier R := by
    calc
      Q' ∩ ι '' B.space = ι '' (Q ∩ B.space) :=
        (hι.bijOn.injOn.image_inter hQK (boundaryComplex_space_subset 3 K)).symm
      _ = ι '' (r₀ '' stdSimplexBoundary 2) := congrArg (ι '' ·) hQboundary
      _ = ι '' (q '' stdSimplexBoundary 2) := congrArg (ι '' ·) hqboundary.symm
      _ = q' '' stdSimplexBoundary 2 := (image_comp _ _ _).symm
      _ = r '' frontier R := hq'r
  refine ⟨A, rfl, T.bijOn.injOn.comp hH.bijOn.injOn hHcopy, ?_, ?_, hAboundary, ?_⟩
  · rw [hAimage]
    exact image_mono hQK
  · exact (hAeq.mono hfrontR).trans hHboundary
  · rw [hAimage]
    exact hQ'inter

namespace NormalSystem

open Classical in
theorem exists_singular_two_cell_in_double (S : NormalSystem E) :
    let K := S.manifoldComplex
    letI : Finite K.faces := S.manifoldComplex_faces_finite.to_subtype
    letI := combinatorialChartedSpace (double 3 K)
      (isCombinatorialManifold_double_succ_succ K S.isManifold)
    let ι := simplicialMap K (glueEmbed₂ (PiecewiseLinear.boundaryComplex 3 K) id)
    ∃ D : SingularTwoCell (double 3 K).space,
      D.domain = S.sourceComplex.space ∧
      EqOn (fun x => (D x : E × E × ℝ)) (ι ∘ S.singularMap)
        S.sourceComplex.space ∧
      Subtype.val '' (D '' D.domain) = ι '' S.imageComplex.space ∧
      Set.range (fun x => (D.boundary x : E × E × ℝ)) =
        ι '' S.loopComplex.space ∧
      Subtype.val '' (D '' D.domain) ∩ ι '' (PiecewiseLinear.boundaryComplex 3 K).space =
        ι '' S.loopComplex.space ∧
      (∀ θ, (D (S.boundaryParam θ) : E × E × ℝ) = ι (S.boundaryLoop θ)) ∧
      (D.IsNonsingular ↔ S.IsNonsingular) := by
  classical
  let K := S.manifoldComplex
  let _ : Finite K.faces := S.manifoldComplex_faces_finite.to_subtype
  let L := double 3 K
  have hL : IsCombinatorialManifold 3 L :=
    isCombinatorialManifold_double_succ_succ K S.isManifold
  let _ := combinatorialChartedSpace L hL
  let B := PiecewiseLinear.boundaryComplex 3 K
  let ι : E → E × E × ℝ := simplicialMap K (glueEmbed₂ B id)
  dsimp only
  have hι : IsPLHomeomorphOn ι K.space (glued₂ K B id).space :=
    isPLHomeomorphOn_embedComplex K (glueEmbed₂ B id) (glueSnd E E) (fun _ _ _ _ => rfl)
  have hcopy : ι '' K.space ⊆ L.space := by
    rw [hι.image_eq]
    change (glued₂ K B id).space ⊆ (double 3 K).space
    rw [double, gluedComplex_space]
    exact subset_union_right
  let F := ι ∘ S.singularMap
  let _ : Finite S.sourceComplex.faces := S.finite_source.to_subtype
  have hFcopy : MapsTo F S.sourceComplex.space L.space := by
    intro x hx
    exact hcopy ⟨S.singularMap x, S.singularMap_mapsTo_manifoldComplex hx, rfl⟩
  have hSmap : IsPiecewiseAffineOn S.singularMap S.sourceComplex.space := by
    exact isPiecewiseAffineOn_simplicialMap S.sourceComplex S.vertexMap
  have hF : IsPiecewiseAffineOn F S.sourceComplex.space := by
    have hcomp := (isPiecewiseAffineOn_simplicialMap K (glueEmbed₂ B id)).comp hSmap
    have hpre : S.sourceComplex.space ∩ S.singularMap ⁻¹' K.space =
        S.sourceComplex.space := inter_eq_left.mpr S.singularMap_mapsTo_manifoldComplex
    rw [hpre] at hcomp
    exact hcomp
  obtain ⟨x, hx⟩ := S.source_isPLBall.nonempty
  let T := combinatorialPLPieceIn L hL ⟨F x, hFcopy hx⟩
  have hval (y : E × E × ℝ) (hy : y ∈ L.space) : (T.map y : E × E × ℝ) = y := by
    simp only [T, combinatorialPLPieceIn, dite_eq_left hy]
  let D : SingularTwoCell L.space :=
    { domain := S.sourceComplex.space
      isPLBall_domain := S.source_isPLBall
      toFun := T.map ∘ F
      isPLOn := T.isPLOn_comp hF hFcopy }
  have hDeq : EqOn (fun z => (D z : E × E × ℝ)) F S.sourceComplex.space := by
    intro z hz
    exact hval (F z) (hFcopy hz)
  have hDimage : Subtype.val '' (D '' D.domain) = ι '' S.imageComplex.space := by
    rw [← image_comp]
    change (fun z => (D z : E × E × ℝ)) '' S.sourceComplex.space = _
    calc
      (fun z => (D z : E × E × ℝ)) '' S.sourceComplex.space =
          F '' S.sourceComplex.space := hDeq.image_eq
      _ = ι '' (S.singularMap '' S.sourceComplex.space) := image_comp ι S.singularMap _
      _ = ι '' S.imageComplex.space := by
        have himage := S.image_space
        change S.imageComplex.space = S.singularMap '' S.sourceComplex.space at himage
        rw [← himage]
  have hfrontier : frontier S.sourceComplex.space ⊆ S.sourceComplex.space :=
    S.source_isPLBall.isPolyhedron.isClosed.frontier_subset
  have hDboundary : Set.range (fun z => (D.boundary z : E × E × ℝ)) =
      ι '' S.loopComplex.space := by
    change Set.range ((fun z => (D z : E × E × ℝ)) ∘
      (Subtype.val : frontier S.sourceComplex.space → EuclideanSpace ℝ (Fin 2))) = _
    rw [range_comp, Subtype.range_coe]
    calc
      (fun z => (D z : E × E × ℝ)) '' frontier S.sourceComplex.space =
          F '' frontier S.sourceComplex.space := (hDeq.mono hfrontier).image_eq
      _ = ι '' (S.singularMap '' frontier S.sourceComplex.space) :=
        image_comp ι S.singularMap _
      _ = ι '' S.loopComplex.space := by
        have hloop := S.loop_space
        change S.loopComplex.space =
          S.singularMap '' frontier S.sourceComplex.space at hloop
        rw [← hloop]
  have hboundary : S.imageComplex.space ∩ B.space = S.loopComplex.space := by
    exact S.image_inter_boundary
  have hDinter : Subtype.val '' (D '' D.domain) ∩ ι '' B.space =
      ι '' S.loopComplex.space := by
    rw [hDimage]
    calc
      ι '' S.imageComplex.space ∩ ι '' B.space =
          ι '' (S.imageComplex.space ∩ B.space) :=
        (hι.bijOn.injOn.image_inter S.image_space_subset_manifoldComplex
          (boundaryComplex_space_subset 3 K)).symm
      _ = ι '' S.loopComplex.space := by rw [hboundary]
  have hparam : ∀ θ, (D (S.boundaryParam θ) : E × E × ℝ) =
      ι (S.boundaryLoop θ) := by
    intro θ
    calc
      (D (S.boundaryParam θ) : E × E × ℝ) = F (S.boundaryParam θ) :=
        hDeq (hfrontier (S.boundaryParam θ).property)
      _ = ι (S.singularMap (S.boundaryParam θ)) := rfl
      _ = ι (S.boundaryLoop θ) := congrArg ι (S.boundaryLoop_eq θ).symm
  have hnonsingular : D.IsNonsingular ↔ S.IsNonsingular := by
    constructor
    · intro hD x hx y hy hxy
      apply hD hx hy
      apply Subtype.ext
      exact (hDeq hx).trans ((congrArg ι hxy).trans (hDeq hy).symm)
    · intro hS x hx y hy hxy
      apply hS hx hy
      apply hι.bijOn.injOn (S.singularMap_mapsTo_manifoldComplex hx)
        (S.singularMap_mapsTo_manifoldComplex hy)
      exact (hDeq hx).symm.trans ((congrArg Subtype.val hxy).trans (hDeq hy))
  exact ⟨D, rfl, hDeq, hDimage, hDboundary, hDinter, hparam, hnonsingular⟩

end NormalSystem

end DifferentialGeometry.Topology.PiecewiseLinear
