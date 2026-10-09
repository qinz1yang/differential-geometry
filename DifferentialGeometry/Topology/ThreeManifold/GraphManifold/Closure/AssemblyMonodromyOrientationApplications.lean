import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyMonodromyOrientation

/-!
# Consumer of D2S1 input (c): the inverse monodromy in the seam shape

The D2S1 assembly needs a diffeomorphism `ν` of the disk with `Φ (2π) ∘ fibre ∘ ν = fibre` (the seam
identity of the mapping-torus lemma `nonempty_solidTorus_diffeomorph_of_liftFlow`) that preserves the
orientation of the disk. It is the inverse of the monodromy of `exists_monodromy_preservesOrientation`.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

local instance diskChartsMonodromyApp_D2S1C : ChartedSpace (EuclideanHalfSpace 2) (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 1

local instance diskSmoothMonodromyApp_D2S1C : IsManifold (𝓡∂ 2) ∞ (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellIsManifold 1

/-- The inverse monodromy: an orientation-preserving diffeomorphism `ν` of the disk with
`Φ (2π) (fibre (ν x)) = fibre x`. -/
theorem exists_inverseMonodromy_preservesOrientation {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 3) M] [IsManifold (𝓡∂ 3) ∞ M] [ConnectedSpace M]
    (oM : ManifoldOrientation (𝓡∂ 3) M 3)
    (p : M → Circle) (hp : ContMDiff (𝓡∂ 3) (𝓡 1) ∞ p)
    (Φ : ℝ → (M ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ M))
    (hΦ : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡∂ 3)) (𝓡∂ 3) ∞ (fun x : ℝ × M => Φ x.1 x.2))
    (hΦ0 : ∀ q, Φ 0 q = q) (hΦadd : ∀ s t q, Φ (s + t) q = Φ s (Φ t q))
    (hΦp : ∀ t q, p (Φ t q) = Circle.exp t * p q)
    (fibre : ClosedCell 2 → M) (hfibre : IsSmoothEmbedding (𝓡∂ 2) (𝓡∂ 3) ∞ fibre)
    (hrange : range fibre = p ⁻¹' {1}) (o : ManifoldOrientation (𝓡∂ 2) (ClosedCell 2) 2) :
    ∃ ν : ClosedCell 2 ≃ₘ⟮𝓡∂ 2, 𝓡∂ 2⟯ ClosedCell 2,
      (∀ x, Φ (2 * Real.pi) (fibre (ν x)) = fibre x) ∧ ν.preservesOrientation o o := by
  obtain ⟨μ, hμ, hμo⟩ := exists_monodromy_preservesOrientation oM p hp Φ hΦ hΦ0 hΦadd hΦp fibre
    hfibre hrange o
  refine ⟨μ.symm, fun x => ?_, Diffeomorph.preservesOrientation_symm hμo⟩
  rw [← hμ, Diffeomorph.apply_symm_apply]

end GC.GraphManifold.Assembly
