import DifferentialGeometry.Topology.Manifold.SeparatingCollarBoundary
import DifferentialGeometry.Topology.Manifold.Boundary.MorseProjectiveObstruction
import DifferentialGeometry.Topology.Manifold.EmbeddedHypersurface.NormalTriviality
import DifferentialGeometry.Topology.ProjectiveSpace.Connected

set_option autoImplicit false
noncomputable section
open Set Bundle DifferentialGeometry.Topology.Morse Poincare.Topology
open scoped Manifold ContDiff Topology
namespace Poincare.Manifold

theorem isConnected_complement_of_projectivePlane_bicollar
    {E H G S M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [TopologicalSpace G]
    [TopologicalSpace S] [ChartedSpace H S]
    [TopologicalSpace M] [ChartedSpace G M]
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ (MorseModel 3) G}
    [J.Boundaryless] [IsManifold J ∞ M]
    [T2Space M] [CompactSpace M] [ConnectedSpace M]
    {e : S → M} (h : SmoothTwoSidedCollar I J e)
    (hRP : S ≃ₜ Projectivization ℝ (EuclideanSpace ℝ (Fin 3))) :
    IsConnected (range e)ᶜ := by
  let _ : LocallyPathConnectedSpace G := J.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  let _ : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace G M
  let _ : CompactSpace S := hRP.symm.surjective.compactSpace hRP.symm.continuous
  let _ : ConnectedSpace S := hRP.symm.surjective.connectedSpace hRP.symm.continuous
  by_contra hsep
  let N := closure h.toTwoSidedCollar.negativeSide
  let aN : ChartedSpace (MorseHalfSpace 2) N := h.negativeClosureChartedSpace (m := 2) hsep
  let sN : IsManifold (morseModelWithCornersHalfSpace 2) ∞ N := h.negativeClosureIsManifold (m := 2) hsep
  let _ : CompactSpace N := isCompact_iff_compactSpace.mp isClosed_closure.isCompact
  exact @not_morseBoundary_homeomorphic_projectivePlane N inferInstance aN sN inferInstance inferInstance
    ⟨(h.negativeBoundaryHomeomorph (m := 2) hsep).symm.trans hRP⟩

theorem isConnected_complement_of_projectivePlane_normalTrivialization
    {H G S M : Type} [TopologicalSpace H] [TopologicalSpace G]
    [TopologicalSpace S] [ChartedSpace H S]
    [TopologicalSpace M] [ChartedSpace G M]
    (I : ModelWithCorners ℝ (MorseModel 2) H) (J : ModelWithCorners ℝ (MorseModel 3) G)
    [I.Boundaryless] [J.Boundaryless] [IsManifold I ∞ S] [IsManifold J ∞ M]
    [T2Space M] [CompactSpace M] [ConnectedSpace M]
    {e : S → M} (he : Manifold.IsSmoothEmbedding I J ∞ e)
    (hRP : S ≃ₜ Projectivization ℝ (EuclideanSpace ℝ (Fin 3)))
    (t : Trivialization ℝ (TotalSpace.proj : TotalSpace ℝ
      (EmbeddedHypersurface.normalSpace I J e) → S))
    [t.IsLinear ℝ] (ht : t.baseSet = univ) :
    IsConnected (range e)ᶜ := by
  let _ : CompactSpace S := hRP.symm.surjective.compactSpace hRP.symm.continuous
  obtain ⟨h⟩ := EmbeddedHypersurface.nonempty_smoothTwoSidedCollar_of_normalTrivialization I J
    he (isCompact_range he.contMDiff.continuous) t ht
  exact isConnected_complement_of_projectivePlane_bicollar h hRP

end Poincare.Manifold
