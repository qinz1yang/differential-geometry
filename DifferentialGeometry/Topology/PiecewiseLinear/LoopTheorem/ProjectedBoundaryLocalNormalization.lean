/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.ProjectedBoundaryNormalization
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.ProjectedBoundaryHalfSpace

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem exists_doubleCoverReduction_boundary_crossing_of_not_isPLSphere
    (S : NormalSystem E)
    (hproper : S.sourceComplex.space ∩ S.singularMap ⁻¹' S.boundaryComplex.space =
      frontier S.sourceComplex.space)
    (hbase : S.basepoint = S.boundaryLoop 0)
    (hnot : ¬IsPLSphere 2 S.boundaryComponent) :
    ∃ (N : ℕ) (T : NormalSystem (EuclideanSpace ℝ (Fin N))) (R : DoubleCoverReduction S T),
      T.basepoint = T.boundaryLoop 0 ∧
      T.sourceComplex.space ∩ T.singularMap ⁻¹' T.boundaryComplex.space =
        frontier T.sourceComplex.space ∧
      ∀ D : EmbeddedDisk T,
        let K := S.manifoldComplex
        letI : Finite K.faces := S.manifoldComplex_faces_finite.to_subtype
        letI := combinatorialChartedSpace (double 3 K)
          (isCombinatorialManifold_double_succ_succ K S.isManifold)
        let ι := simplicialMap K (glueEmbed₂ (PiecewiseLinear.boundaryComplex 3 K) id)
        let C := ((↑) : (double 3 K).space → E × E × ℝ) ⁻¹' (ι '' K.space)
        ∃ (G : SingularTwoCell (double 3 K).space) (γ : freeLoop S.boundaryNeighborhoodSpace)
          (q : Path S.basepoint (γ 0)),
          G.domain = D.domain ∧ γ = R.boundaryMap.comp D.boundaryLoop ∧
          EqOn (fun x => (G x : E × E × ℝ)) (ι ∘ R.projection ∘ D.map) D.domain ∧
          MapsTo G G.domain C ∧ G.domain ∩ G ⁻¹' frontier C = frontier G.domain ∧
          IsLocallyInjective (G.domain.domRestrict G) ∧
          (∀ y, (G.domain ∩ G ⁻¹' {y}).encard ≤ 2) ∧
          ¬conjugacyClassMeets (normalSystemLoopConjugacyClass S.basepoint γ q) S.normalSubgroup ∧
          ∀ y ∈ doublePointSet G G.domain ∩ frontier C,
            ∃ (e : OpenPartialHomeomorph (double 3 K).space (EuclideanSpace ℝ (Fin 3)))
              (ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ),
              e ∈ (plGroupoid 3).maximalAtlas (double 3 K).space ∧ ℓ ≠ 0 ∧ y ∈ e.source ∧
              (∀ x ∈ e.source, x ∈ C ↔ 0 ≤ ℓ (e x)) ∧
              (∀ x ∈ e.source, x ∈ frontier C ↔ ℓ (e x) = 0) ∧
              ∀ V : Set (double 3 K).space, V ∈ 𝓝 y →
              ∃ W : Set (double 3 K).space,
                IsOpen W ∧ y ∈ W ∧ closure W ⊆ V ∧ W ⊆ e.source ∧
              ∀ ε : ℝ, 0 < ε → ∃ (A : SingularTwoCell (double 3 K).space)
                (J : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
                (δ : freeLoop S.boundaryNeighborhoodSpace) (r : Path S.basepoint (δ 0)),
                A.domain = D.domain ∧ (∀ x, dist (A x) (G x) < ε) ∧
                MapsTo A A.domain C ∧ A.domain ∩ A ⁻¹' frontier C = frontier A.domain ∧
                A '' A.domain ∩ frontier C = range A.boundary ∧
                (∀ z ∉ V, A ⁻¹' {z} = G ⁻¹' {z}) ∧
                IsLocallyInjective (A.domain.domRestrict A) ∧
                (∀ z, (A.domain ∩ A ⁻¹' {z}).encard ≤ 2) ∧
                J.faces.Finite ∧ IsCombinatorialManifoldWithBoundary 1 J ∧
                (∀ z ∈ W, z ∈ doublePointSet A A.domain ↔ e z ∈ J.space) ∧
                (∀ z ∈ W ∩ doublePointSet A A.domain,
                  (z ∈ frontier C ∧ HasPLBoundaryDoubleCrossingAt (e ∘ A)
                    (A.domain ∩ A ⁻¹' e.source) (e '' (e.source ∩ C)) (e z)) ∨
                  (z ∉ frontier C ∧ HasPLDoubleCrossingAt (e ∘ A)
                    (A.domain ∩ A ⁻¹' e.source) (e z))) ∧
                γ.Homotopic δ ∧
                range (fun θ => (δ θ : E)) =
                  range (fun x : frontier A.domain => glueSnd E E (A x)) ∧
                range (fun x => (A.boundary x : E × E × ℝ)) = ι '' range (fun θ => (δ θ : E)) ∧
                ¬conjugacyClassMeets (normalSystemLoopConjugacyClass S.basepoint δ r)
                  S.normalSubgroup := by
  classical
  obtain ⟨N, T, R, hbaseT, hproperT, hnormalize⟩ :=
    S.exists_doubleCoverReduction_boundary_crossing_in_chart_of_not_isPLSphere hproper hbase hnot
  refine ⟨N, T, R, hbaseT, hproperT, fun D => ?_⟩
  intro K
  let _ : Finite K.faces := S.manifoldComplex_faces_finite.to_subtype
  let _ := combinatorialChartedSpace (double 3 K)
    (isCombinatorialManifold_double_succ_succ K S.isManifold)
  let ι := simplicialMap K (glueEmbed₂ (PiecewiseLinear.boundaryComplex 3 K) id)
  let C := ((↑) : (double 3 K).space → E × E × ℝ) ⁻¹' (ι '' K.space)
  obtain ⟨G, γ, q, hdom, hγ, hGeq, hmap, hGproper, hloc, hcard, havoid, hcharts⟩ := hnormalize D
  refine ⟨G, γ, q, hdom, hγ, hGeq, hmap, hGproper, hloc, hcard, havoid, ?_⟩
  intro y hy
  let p : K.space := ⟨S.basepoint, boundaryComplex_space_subset 3 K
    (derivedNeighborhood_space_subset S.boundaryComplex S.loopComplex S.basepoint.property)⟩
  obtain ⟨e, ℓ, he, hℓ, hye, hC, hBd⟩ :=
    exists_halfSpace_chart_glued₂_space_in_double K S.isManifold p y hy.2
  exact ⟨e, ℓ, he, hℓ, hye, hC, hBd, hcharts e he ℓ hℓ hC hBd y hy.1 hye⟩

end DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem
