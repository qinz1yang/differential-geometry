/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.CoverReduction
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.ProjectedBoundaryLoop
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.SurfaceNeighborhood

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

open Classical in
theorem DoubleCoverDiagram.exists_boundaryNeighborhood_radius
    {S : NormalSystem E} {T : NormalSystem F} (R : DoubleCoverDiagram S T)
    (hbuffer : ∀ x ∈ T.boundaryNeighborhood.space,
      S.boundaryNeighborhood.space ∈ 𝓝[S.boundaryComplex.space] (R.projection x)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ T.boundaryNeighborhood.space,
      ∀ y ∈ S.boundaryComplex.space, dist y (R.projection x) < ε →
        y ∈ S.boundaryNeighborhood.space := by
  have hcompactT : IsCompact T.boundaryNeighborhood.space :=
    T.boundaryNeighborhood_faces_finite.isCompact_biUnion fun s _ =>
      s.finite_toSet.isCompact_convexHull ℝ
  have hcont : Continuous (T.boundaryNeighborhood.space.domRestrict R.projection) :=
    (continuous_subtype_val.comp R.boundaryMap.continuous).congr R.boundaryMap_eq
  have hcompact : IsCompact (R.projection '' T.boundaryNeighborhood.space) :=
    hcompactT.image_of_continuousOn (continuousOn_iff_continuous_domRestrict.mpr hcont)
  let O := (closure (S.boundaryComplex.space \ S.boundaryNeighborhood.space))ᶜ
  have hO : IsOpen O := isClosed_closure.isOpen_compl
  have hmapO : R.projection '' T.boundaryNeighborhood.space ⊆ O := by
    rintro _ ⟨x, hx, rfl⟩ hxcl
    obtain ⟨U, hU, hUB⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp (hbuffer x hx)
    obtain ⟨y, hyU, hybd, hyB⟩ := mem_closure_iff_nhds.mp hxcl U hU
    exact hyB (hUB ⟨hyU, hybd⟩)
  obtain ⟨ε, hε, hεO⟩ := hcompact.exists_thickening_subset_open hO hmapO
  refine ⟨ε, hε, fun x hx y hy hdist => ?_⟩
  have hyO : y ∈ O := hεO (Metric.mem_thickening_iff.mpr ⟨R.projection x, ⟨x, hx, rfl⟩, hdist⟩)
  by_contra hyB
  exact hyO (subset_closure ⟨hy, hyB⟩)

open Classical in
theorem exists_doubleCoverReduction_boundary_radius_of_not_isPLSphere
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (S : NormalSystem E)
    (hproper : S.sourceComplex.space ∩ S.singularMap ⁻¹' S.boundaryComplex.space =
      frontier S.sourceComplex.space)
    (hbase : S.basepoint = S.boundaryLoop 0)
    (hnot : ¬IsPLSphere 2 S.boundaryComponent) :
    ∃ (N : ℕ) (T : NormalSystem (EuclideanSpace ℝ (Fin N)))
      (R : DoubleCoverReduction S T) (ε : ℝ),
      T.basepoint = T.boundaryLoop 0 ∧
      T.sourceComplex.space ∩ T.singularMap ⁻¹' T.boundaryComplex.space =
        frontier T.sourceComplex.space ∧ 0 < ε ∧
      ∀ x ∈ T.boundaryNeighborhood.space, ∀ y ∈ S.boundaryComplex.space,
        dist y (R.projection x) < ε → y ∈ S.boundaryNeighborhood.space := by
  obtain ⟨N, T, R, hbaseT, hproperT, hbuffer⟩ :=
    S.exists_doubleCoverReduction_boundary_mem_nhdsWithin_of_not_isPLSphere hproper hbase hnot
  obtain ⟨ε, hε, hεB⟩ := R.toDoubleCoverDiagram.exists_boundaryNeighborhood_radius hbuffer
  exact ⟨N, T, R, ε, hbaseT, hproperT, hε, hεB⟩

variable [FiniteDimensional ℝ F]

open Classical in
theorem DoubleCoverDiagram.exists_projected_boundary_loop_homotopy
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {S : NormalSystem E} {T : NormalSystem F} (R : DoubleCoverDiagram S T)
    (hbuffer : ∀ x ∈ T.boundaryNeighborhood.space,
      S.boundaryNeighborhood.space ∈ 𝓝[S.boundaryComplex.space] (R.projection x))
    (D : EmbeddedDisk T) :
    let K := S.manifoldComplex
    letI : Finite K.faces := S.manifoldComplex_faces_finite.to_subtype
    letI := combinatorialChartedSpace (double 3 K)
      (isCombinatorialManifold_double_succ_succ K S.isManifold)
    let ι := simplicialMap K (glueEmbed₂ (PiecewiseLinear.boundaryComplex 3 K) id)
    let C := ((↑) : (double 3 K).space → E × E × ℝ) ⁻¹' (ι '' K.space)
    ∃ (G : SingularTwoCell (double 3 K).space) (γ : freeLoop S.boundaryNeighborhoodSpace)
      (q : Path S.basepoint (γ 0)) (β : ContinuousMap loopCircle (frontier G.domain)) (ε : ℝ),
      G.domain = D.domain ∧ γ = R.boundaryMap.comp D.boundaryLoop ∧
      EqOn (fun x => (G x : E × E × ℝ)) (ι ∘ R.projection ∘ D.map) D.domain ∧
      MapsTo G G.domain C ∧ G.domain ∩ G ⁻¹' frontier C = frontier G.domain ∧
      IsLocallyInjective (G.domain.domRestrict G) ∧
      (∀ y, (G.domain ∩ G ⁻¹' {y}).encard ≤ 2) ∧
      ¬conjugacyClassMeets (normalSystemLoopConjugacyClass S.basepoint γ q) S.normalSubgroup ∧
      Function.Surjective β ∧ (∀ θ, (G (β θ) : E × E × ℝ) = ι (γ θ : E)) ∧ 0 < ε ∧
      ∀ H : ContinuousMap (unitInterval × frontier G.domain) (double 3 K).space,
        (∀ x, H (0, x) = G x) → (∀ t x, H (t, x) ∈ frontier C) →
        (∀ t x, dist (H (t, x)) (G x) < ε) →
        ∃ (δ : freeLoop S.boundaryNeighborhoodSpace) (r : Path S.basepoint (δ 0)),
          γ.Homotopic δ ∧
          (∀ θ, (δ θ : E) = glueSnd E E (H (1, β θ))) ∧
          range (fun θ => (δ θ : E)) =
            range (fun x : frontier G.domain => glueSnd E E (H (1, x))) ∧
          ¬conjugacyClassMeets (normalSystemLoopConjugacyClass S.basepoint δ r)
            S.normalSubgroup := by
  classical
  intro K
  let _ : Finite K.faces := S.manifoldComplex_faces_finite.to_subtype
  let _ := combinatorialChartedSpace (double 3 K)
    (isCombinatorialManifold_double_succ_succ K S.isManifold)
  let ι := simplicialMap K (glueEmbed₂ (PiecewiseLinear.boundaryComplex 3 K) id)
  let C := ((↑) : (double 3 K).space → E × E × ℝ) ⁻¹' (ι '' K.space)
  obtain ⟨G, γ, q, β, hdom, hγ, hGeq, hmap, hproper, hloc, hcard, havoid, hβsurj, hβ⟩ :=
    R.exists_projected_singular_two_cell_with_boundaryLoop_lift D
  obtain ⟨ε, hε, hεB⟩ := R.exists_boundaryNeighborhood_radius hbuffer
  refine ⟨G, γ, q, β, ε, hdom, hγ, hGeq, hmap, hproper, hloc, hcard, havoid,
    hβsurj, hβ, hε, fun H hHzero hHfront hHclose => ?_⟩
  have hfront : frontier C = ((↑) : (double 3 K).space → E × E × ℝ) ⁻¹'
      (ι '' S.boundaryComplex.space) := by
    change frontier (((↑) : (double 3 K).space → E × E × ℝ) ⁻¹' (ι '' K.space)) = _
    rw [← glued₂_space]
    exact frontier_preimage_glued₂_space_in_double K S.isManifold
  let π : (double 3 K).space → E := fun x => glueSnd E E x
  have hπcont : Continuous π := continuous_glueSnd.comp continuous_subtype_val
  have hπi (x : E) (hx : x ∈ K.space) : glueSnd E E (ι x) = x :=
    glueSnd_simplicialMap K (PiecewiseLinear.boundaryComplex 3 K) id hx
  have hγK (θ : loopCircle) : (γ θ : E) ∈ K.space :=
    boundaryComplex_space_subset 3 K
      (derivedNeighborhood_space_subset S.boundaryComplex S.loopComplex (γ θ).property)
  have hπG (θ : loopCircle) : π (G (β θ)) = (γ θ : E) :=
    (congrArg (glueSnd E E) (hβ θ)).trans (hπi _ (hγK θ))
  have hγproj (θ : loopCircle) : (γ θ : E) = R.projection (D.boundaryLoop θ) := by
    rw [hγ]
    exact R.boundaryMap_eq (D.boundaryLoop θ)
  have hπbd (z : (double 3 K).space) (hz : z ∈ frontier C) :
      π z ∈ S.boundaryComplex.space := by
    rw [hfront] at hz
    obtain ⟨x, hx, hxz⟩ := hz
    have heq : π z = x :=
      (congrArg (glueSnd E E) hxz.symm).trans
        (hπi x (boundaryComplex_space_subset 3 K hx))
    exact heq.symm ▸ hx
  have hπdist (x y : (double 3 K).space) : dist (π x) (π y) ≤ dist x y := by
    change dist x.val.2.1 y.val.2.1 ≤
      max (dist x.val.1 y.val.1) (max (dist x.val.2.1 y.val.2.1) (dist x.val.2.2 y.val.2.2))
    exact (le_max_left _ _).trans (le_max_right _ _)
  have hmem (t : unitInterval) (θ : loopCircle) :
      π (H (t, β θ)) ∈ S.boundaryNeighborhood.space := by
    apply hεB _ (D.boundaryLoop θ).property _ (hπbd _ (hHfront t (β θ)))
    rw [← hγproj θ, ← hπG θ]
    exact (hπdist _ _).trans_lt (hHclose t (β θ))
  let δ : freeLoop S.boundaryNeighborhoodSpace :=
    ⟨fun θ => ⟨π (H (1, β θ)), hmem 1 θ⟩,
      (hπcont.comp (H.continuous.comp (continuous_const.prodMk β.continuous))).subtype_mk _⟩
  let B : ContinuousMap.Homotopy γ δ :=
    { toFun := fun z => ⟨π (H (z.1, β z.2)), hmem z.1 z.2⟩
      continuous_toFun :=
        (hπcont.comp (H.continuous.comp
          (continuous_fst.prodMk (β.continuous.comp continuous_snd)))).subtype_mk _
      map_zero_left := fun θ => Subtype.ext
        ((congrArg π (hHzero (β θ))).trans (hπG θ))
      map_one_left := fun _ => rfl }
  let _ : PathConnectedSpace S.boundaryNeighborhoodSpace := S.boundaryNeighborhoodPathConnectedSpace
  let r := PathConnectedSpace.somePath S.basepoint (δ 0)
  have hclass : normalSystemLoopConjugacyClass S.basepoint δ r =
      normalSystemLoopConjugacyClass S.basepoint γ q := by
    calc
      normalSystemLoopConjugacyClass S.basepoint δ r = FreeLoop.conjugacyClass δ S.basepoint :=
        (FreeLoop.conjugacyClass_eq_mk_loopRepresentativeAlong r ⟨δ, rfl⟩).symm
      _ = FreeLoop.conjugacyClass γ S.basepoint :=
        (FreeLoop.conjugacyClass_eq_of_homotopic ⟨B⟩ S.basepoint).symm
      _ = normalSystemLoopConjugacyClass S.basepoint γ q :=
        FreeLoop.conjugacyClass_eq_mk_loopRepresentativeAlong q ⟨γ, rfl⟩
  refine ⟨δ, r, ⟨B⟩, fun _ => rfl, ?_, ?_⟩
  · apply Subset.antisymm
    · rintro _ ⟨θ, rfl⟩
      exact ⟨β θ, rfl⟩
    · rintro _ ⟨x, rfl⟩
      obtain ⟨θ, rfl⟩ := hβsurj x
      exact ⟨θ, rfl⟩
  · rwa [hclass]

end DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem
