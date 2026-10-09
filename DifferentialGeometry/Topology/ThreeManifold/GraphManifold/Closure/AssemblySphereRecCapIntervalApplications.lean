import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereRecCapInterval

/-!
# Consumers of packet S3a, `S² × I` case (lane ASM-SPH)

* `DecompositionCertificate.exists_ballVertex_of_sphereInterval_side`: the vertex that replaces a
  capped `S² × I` side in the successor certificate — a ball vertex of the capped carrier whose
  image is the lifted side together with the cap of its copy and whose model boundary is the
  transport of the uncut end.
* `exists_ballChart_of_shell_cap_closedBall`: the shell lemma read on closed balls (the union of an
  injective full-rank `S² × [0, 1]` and a ball chart glued along an end is the image of the closed
  unit ball under a ball chart).
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

/-- **The new ball vertex of a capped `S² × I` side.** -/
theorem DecompositionCertificate.exists_ballVertex_of_sphereInterval_side {W : CompactCarrier.{u}}
    {n : ℕ} {E : BoundaryTori W n} (D : DecompositionCertificate W E) (c : Fin D.sphereSeamCount)
    (X : SphereCutCapped W (D.sphereSeam c) E) (b : Bool) {P : PieceEmbedding W}
    {e : (ClosureSphere.{u} × Icc (0 : ℝ) 1) ≃ₘ⟮(𝓡 2).prod (𝓡∂ 1), 𝓡∂ 3⟯ P.Piece}
    (hv : D.vertex (D.sphereSide c b) = .slim P (.sphereInterval e)) :
    ∃ v' : Vertex X.Q, v'.IsBall ∧
      v'.image = range (D.liftVertex c X (D.sphereSide c b)).map ∪
        range (X.capping.cap (Fin.cast X.h2.symm (sideCopy b))) ∧
      v'.boundaryImage =
        X.transport '' ((D.vertex (D.sphereSide c b)).boundaryImage \ (D.sphereSeam c).zeroSphere) := by
  obtain ⟨P', e', hr, hbd⟩ := D.exists_capUnion_ball_of_sphereInterval c X b hv
  exact ⟨.zero P' (.ball e'), ⟨P', e', rfl⟩, hr, hbd⟩

/-- **The shell lemma, closed-ball form.** -/
theorem exists_ballChart_of_shell_cap_closedBall {N : Type*} [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N] [IsManifold (𝓡 3) ∞ N] [T2Space N]
    (F₀ : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × Icc (0 : ℝ) 1 → N)
    (hF : ContMDiff ((𝓡 2).prod (𝓡∂ 1)) (𝓡 3) ∞ F₀) (hinj : Injective F₀)
    (hbij : ∀ p, Bijective (mfderiv ((𝓡 2).prod (𝓡∂ 1)) (𝓡 3) F₀ p))
    (G : PartialDiffeomorph (𝓡 3) (𝓡 3) (EuclideanSpace ℝ (Fin 3)) N ∞)
    (hG : Metric.closedBall 0 1 ⊆ G.source)
    (hGs : G '' Metric.sphere 0 1 = range fun z => F₀ (z, iccZero))
    (hinter : range F₀ ∩ G '' Metric.closedBall 0 1 ⊆ G '' Metric.sphere 0 1) :
    ∃ A : PartialDiffeomorph (𝓡 3) (𝓡 3) (EuclideanSpace ℝ (Fin 3)) N ∞,
      range F₀ ⊆ A '' Metric.closedBall 0 1 ∧ G '' Metric.closedBall 0 1 ⊆ A '' Metric.closedBall 0 1 ∧
      A '' Metric.sphere 0 1 = range fun z => F₀ (z, iccOne) := by
  obtain ⟨A, -, hAcl, hAs⟩ := exists_ballChart_of_shell_cap F₀ hF hinj hbij G hG hGs hinter
  exact ⟨A, hAcl ▸ subset_union_left, hAcl ▸ subset_union_right, hAs⟩

end GC.GraphManifold.Assembly
