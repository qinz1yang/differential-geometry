import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.DoubleBoundaryPush

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem exists_nonsingular_two_cell_of_disk_in_double_boundary_eqOn
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) :
    letI := combinatorialChartedSpace (double 3 K) (isCombinatorialManifold_double_succ_succ K hK)
    let ι := simplicialMap K (glueEmbed₂ (boundaryComplex 3 K) id)
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
  have hr₀ : IsPLHomeomorphOn r₀ (stdSimplex ℝ (Fin 3)) (g '' D) :=
    hp.trans (hr.trans hgD)
  obtain ⟨Q, q, hq, hQK, hqboundary, hQboundary⟩ :=
    hK.exists_isPLHomeomorphOn_push_boundary_disk hr₀ hD₀
  let Q' := ι '' Q
  let q' := ι ∘ q
  have hQ : IsPLBall 2 Q := ⟨q, hq⟩
  have hιQ : IsPLHomeomorphOn ι Q Q' := hι.restrict hQ.isPolyhedron hQK
  have hq' : IsPLHomeomorphOn q' (stdSimplex ℝ (Fin 3)) Q' := hq.trans hιQ
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
    simp only [T, combinatorialPLPieceIn, dif_pos hy]
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

end DifferentialGeometry.Topology.PiecewiseLinear
