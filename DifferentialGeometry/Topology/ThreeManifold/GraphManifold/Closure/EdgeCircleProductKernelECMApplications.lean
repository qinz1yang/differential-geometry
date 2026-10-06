import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.EdgeCircleProductKernelECM

/-!
# Consumer of the E4 kernel: the old D2S1 conclusion (a circle-fibred piece is a solid torus)

The product `T : D² × S¹ ≃ₘ M` of `edge_circle_product_kernel_ECM` composed with the standard
parametrization of the solid torus by `D² × S¹` recovers the tree's D2S1 output
(`nonempty_solidTorus_diffeomorph_of_liftFlow`: `Nonempty` of a diffeomorphism from the standard
solid torus onto `M`), now for an AMBIENT disk chart (`ι ∘ fibre` a smooth embedding for a smooth
`ι : M → N`) and with the fibre-preserving map available.
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

local instance diskChartsKernelApp_ECM : ChartedSpace (EuclideanHalfSpace 2) (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 1

local instance diskSmoothKernelApp_ECM : IsManifold (𝓡∂ 2) ∞ (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellIsManifold 1

/-- **Consumer.** The oriented compact connected disk bundle `p : M → S¹` over the circle with an
ambient smooth disk chart is diffeomorphic to the standard solid torus. -/
theorem nonempty_solidTorus_of_product_kernel_ECM {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 3) M] [IsManifold (𝓡∂ 3) ∞ M] [CompactSpace M] [T2Space M]
    [ConnectedSpace M] (oM : ManifoldOrientation (𝓡∂ 3) M 3) {E' : Type*}
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] {H' : Type*} [TopologicalSpace H']
    {J' : ModelWithCorners ℝ E' H'} {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
    (ι : M → N) (hι : ContMDiff (𝓡∂ 3) J' ∞ ι)
    (p : M → Circle) (hp : ContMDiff (𝓡∂ 3) (𝓡 1) ∞ p)
    (hsub : ∀ q, Surjective (mfderiv (𝓡∂ 3) (𝓡 1) p q))
    (hbd : ∀ q, (𝓡∂ 3).IsBoundaryPoint q → ∃ γ : ℝ → M,
      ContMDiff 𝓘(ℝ, ℝ) (𝓡∂ 3) ∞ γ ∧ γ 0 = q ∧ (∀ t, (𝓡∂ 3).IsBoundaryPoint (γ t)) ∧
        mfderiv 𝓘(ℝ, ℝ) (𝓡 1) (p ∘ γ) 0 ≠ 0)
    (fibre : ClosedCell 2 → M) (hfibre_sm : ContMDiff (𝓡∂ 2) (𝓡∂ 3) ∞ fibre)
    (hφ : IsSmoothEmbedding (𝓡∂ 2) J' ∞ (ι ∘ fibre)) (hrange : range fibre = p ⁻¹' {1}) :
    Nonempty (solidTorusCarrier.{u}.Carrier ≃ₘ⟮solidTorusCarrier.{u}.model, 𝓡∂ 3⟯ M) := by
  obtain ⟨T, -⟩ := edge_circle_product_kernel_ECM oM ι hι p hp hsub hbd fibre hfibre_sm hφ hrange
  exact ⟨(solidTorusDiscCircle.{u}.trans
    ((closedCellUnitDiscDiffeomorph.{u}.symm).prodCongr (Diffeomorph.refl (𝓡 1) Circle ∞))).trans
      T⟩

end GC.GraphManifold.Assembly
