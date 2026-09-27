/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.ProjectedBoundaryCrossing
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.ProjectedBoundaryHomotopy

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem exists_doubleCoverReduction_boundary_crossing_in_chart_of_not_isPLSphere
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
          ∀ e : OpenPartialHomeomorph (double 3 K).space (EuclideanSpace ℝ (Fin 3)),
            e ∈ (plGroupoid 3).maximalAtlas (double 3 K).space →
            ∀ ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ, ℓ ≠ 0 →
            (∀ x ∈ e.source, x ∈ C ↔ 0 ≤ ℓ (e x)) →
            (∀ x ∈ e.source, x ∈ frontier C ↔ ℓ (e x) = 0) →
            ∀ y ∈ doublePointSet G G.domain, y ∈ e.source →
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
  obtain ⟨N, T, R, hbaseT, hproperT, hbuffer⟩ :=
    S.exists_doubleCoverReduction_boundary_mem_nhdsWithin_of_not_isPLSphere hproper hbase hnot
  refine ⟨N, T, R, hbaseT, hproperT, fun D => ?_⟩
  intro K
  let _ : Finite K.faces := S.manifoldComplex_faces_finite.to_subtype
  let _ := combinatorialChartedSpace (double 3 K)
    (isCombinatorialManifold_double_succ_succ K S.isManifold)
  let ι := simplicialMap K (glueEmbed₂ (PiecewiseLinear.boundaryComplex 3 K) id)
  let C := ((↑) : (double 3 K).space → E × E × ℝ) ⁻¹' (ι '' K.space)
  obtain ⟨G, γ, q, β, ρ, hdom, hγ, hGeq, hmap, hGproper, hloc, hcard,
    havoid, -, -, hρ, hhomotopy⟩ :=
    R.toDoubleCoverDiagram.exists_projected_boundary_loop_homotopy hbuffer D
  refine ⟨G, γ, q, hdom, hγ, hGeq, hmap, hGproper, hloc, hcard, havoid,
    fun e he ℓ hℓ hC hBd y hy hye V hV => ?_⟩
  obtain ⟨W, hW, hyW, hWV, hWe, hsmall⟩ :=
    G.exists_small_boundary_doubleCrossing_in_chart hmap hGproper hloc hcard
      e he ℓ hℓ hC hBd hy hye hV
  refine ⟨W, hW, hyW, hWV, hWe, fun ε hε => ?_⟩
  obtain ⟨A, J, hAdom, hclose, hAmap, hAproper, hAinter, hfiber, hAloc, hAcard,
    hJfin, hJman, hJspace, hcross, H, hHzero, hHone, hH⟩ := hsmall (min ε ρ) (lt_min hε hρ)
  obtain ⟨δ, r, hhom, -, hδrange, hδavoid⟩ := hhomotopy H hHzero
    (fun t x => (hH t x).2.1) (fun t x => (hH t x).1.trans_le (min_le_right _ _))
  have hδrangeA : range (fun θ => (δ θ : E)) =
      range (fun x : frontier A.domain => glueSnd E E (A x)) := by
    rw [hδrange]
    apply Subset.antisymm
    · rintro _ ⟨x, rfl⟩
      refine ⟨⟨x, by rw [hAdom]; exact x.property⟩, ?_⟩
      exact (congrArg (fun z : (double 3 K).space => glueSnd E E z) (hHone x)).symm
    · rintro _ ⟨x, rfl⟩
      let xG : frontier G.domain := ⟨x, (congrArg frontier hAdom).subset x.property⟩
      exact ⟨xG, congrArg (fun z : (double 3 K).space => glueSnd E E z) (hHone xG)⟩
  have hιπA (x : EuclideanSpace ℝ (Fin 2)) (hx : x ∈ A.domain) :
      ι (glueSnd E E (A x)) = (A x : E × E × ℝ) := by
    obtain ⟨z, hz, hzx⟩ := hAmap hx
    rw [← hzx, glueSnd_simplicialMap K (PiecewiseLinear.boundaryComplex 3 K) id hz]
  have hboundary : range (fun x => (A.boundary x : E × E × ℝ)) =
      ι '' range (fun θ => (δ θ : E)) := by
    rw [hδrangeA]
    apply Subset.antisymm
    · rintro _ ⟨x, rfl⟩
      exact ⟨glueSnd E E (A x), ⟨x, rfl⟩, hιπA x (A.frontier_subset_domain x.property)⟩
    · rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨x, (hιπA x (A.frontier_subset_domain x.property)).symm⟩
  exact ⟨A, J, δ, r, hAdom.trans hdom, fun x => (hclose x).trans_le (min_le_left _ _),
    hAmap, hAproper, hAinter, hfiber, hAloc, hAcard, hJfin, hJman, hJspace, hcross,
    hhom, hδrangeA, hboundary, hδavoid⟩

end DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem
