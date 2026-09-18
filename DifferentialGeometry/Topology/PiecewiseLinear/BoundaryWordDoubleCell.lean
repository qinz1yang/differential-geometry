import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryWordLoopClass
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.LemmaTwo

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

open Classical in
theorem NormalSystem.exists_boundary_word_loop_dichotomy_in_double
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (S : NormalSystem E) [PathConnectedSpace S.boundaryNeighborhoodSpace] :
    let K := S.manifoldComplex
    letI : Finite K.faces := S.manifoldComplex_faces_finite.to_subtype
    letI := combinatorialChartedSpace (double 3 K)
      (isCombinatorialManifold_double_succ_succ K S.isManifold)
    ∃ D : SingularTwoCell (double 3 K).space,
      D.domain = S.sourceComplex.space ∧
      ∀ (BdM Bn : Set (double 3 K).space) (hD : NormalSingularCellData D BdM Bn)
        (c : hD.singularSet.Branch), hD.singularSet.IsBoundaryBranch c →
        ∃ A₁ A₂ A₃ A₄ : Set (EuclideanSpace ℝ (Fin 2)),
          frontier D.domain = A₁ ∪ (A₂ ∪ (A₃ ∪ A₄)) ∧
          ((∃ (a b : S.boundaryNeighborhoodSpace) (σ υ : Path a b) (τ φ : Path b a),
              Set.range (fun t => (σ t : E)) = S.singularMap '' A₁ ∧
              Set.range (fun t => (τ t : E)) = S.singularMap '' A₂ ∧
              Set.range (fun t => (υ t : E)) = S.singularMap '' A₃ ∧
              Set.range (fun t => (φ t : E)) = S.singularMap '' A₄ ∧
              (¬loopClassMeets (pathToCircle (σ.trans υ.symm)) S.basepoint S.normalSubgroup ∨
                ¬loopClassMeets (pathToCircle (σ.trans (φ.trans (υ.trans τ)))) S.basepoint
                  S.normalSubgroup)) ∨
            (∃ (a b : S.boundaryNeighborhoodSpace) (σ : Path a b) (τ : Path b b) (υ : Path b a)
                (φ : Path a a),
              Set.range (fun t => (σ t : E)) = S.singularMap '' A₁ ∧
              Set.range (fun t => (τ t : E)) = S.singularMap '' A₂ ∧
              Set.range (fun t => (υ t : E)) = S.singularMap '' A₃ ∧
              Set.range (fun t => (φ t : E)) = S.singularMap '' A₄ ∧
              (¬loopClassMeets (pathToCircle (σ.trans υ)) S.basepoint S.normalSubgroup ∨
                ¬loopClassMeets (pathToCircle (σ.trans (τ.symm.trans (υ.trans φ.symm))))
                  S.basepoint S.normalSubgroup))) := by
  classical
  intro K
  let _ : Finite K.faces := S.manifoldComplex_faces_finite.to_subtype
  let _ := combinatorialChartedSpace (double 3 K)
    (isCombinatorialManifold_double_succ_succ K S.isManifold)
  obtain ⟨D, hdom, hDeq, -, -, -, -, -⟩ := S.exists_singular_two_cell_in_double
  refine ⟨D, hdom, fun BdM Bn hD c hc => ?_⟩
  have hι : IsPLHomeomorphOn
      (simplicialMap K (glueEmbed₂ (PiecewiseLinear.boundaryComplex 3 K) id)) K.space
      (glued₂ K (PiecewiseLinear.boundaryComplex 3 K) id).space :=
    isPLHomeomorphOn_embedComplex K (glueEmbed₂ (PiecewiseLinear.boundaryComplex 3 K) id)
      (glueSnd E E) (fun _ _ _ _ => rfl)
  refine S.exists_boundary_word_loop_dichotomy_of_boundaryBranch hD hc hdom ?_
  intro z hz w hw hzw
  have hzs : z ∈ S.sourceComplex.space := hdom ▸ D.frontier_subset_domain hz
  have hws : w ∈ S.sourceComplex.space := hdom ▸ D.frontier_subset_domain hw
  exact hι.bijOn.injOn (S.singularMap_mapsTo_manifoldComplex hzs)
    (S.singularMap_mapsTo_manifoldComplex hws)
    ((hDeq hzs).symm.trans ((congrArg Subtype.val hzw).trans (hDeq hws)))

end DifferentialGeometry.Topology.PiecewiseLinear
