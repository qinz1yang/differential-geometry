import DifferentialGeometry.Topology.Homeomorph.SmallPerturbation
import DifferentialGeometry.Topology.InvarianceOfDomainManifold
import DifferentialGeometry.Topology.Manifold.ModelTransport

open Set Topology

namespace DifferentialGeometry.Topology.Manifold

universe u v w

theorem exists_continuousOn_pos_image_eq_of_isOpen
    {E : Type w} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M₁ : Type u} {M₂ : Type v} [TopologicalSpace M₁] [SecondCountableTopology M₁]
    [MetricSpace M₂] [ChartedSpace E M₁] [ChartedSpace E M₂]
    {U : Set M₁} (hU : IsOpen U) {h : M₁ → M₂}
    (hh : Topology.IsEmbedding (U.domRestrict h))
    (φ : M₁ → ℝ) (hφ : ContinuousOn φ U) (hpos : ∀ x ∈ U, 0 < φ x) :
    ∃ ε : M₁ → ℝ, ContinuousOn ε U ∧ (∀ x ∈ U, 0 < ε x) ∧
      (∀ x ∈ U, ε x ≤ φ x) ∧
      ∀ f : M₁ → M₂, ContinuousOn f U → InjOn f U → IsOpenMap (U.domRestrict f) →
        (∀ x ∈ U, dist (f x) (h x) < ε x) → f '' U = h '' U := by
  let : LocallyCompactSpace M₁ := ChartedSpace.locallyCompactSpace E M₁
  let : LocallyCompactSpace U := hU.locallyCompactSpace
  let : LocallyPathConnectedSpace M₂ := ChartedSpace.locallyPathConnectedSpace E M₂
  have hhcont : ContinuousOn h U := continuousOn_iff_continuous_domRestrict.mpr hh.continuous
  have hhinj : InjOn h U := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (hh.injective (show (U.domRestrict h) ⟨x, hx⟩ =
      (U.domRestrict h) ⟨y, hy⟩ from hxy))
  have himage : IsOpen (h '' U) := by
    let H := EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
    let e : E ≃L[ℝ] H := ContinuousLinearEquiv.ofFinrankEq (by simp [H])
    let : ChartedSpace H M₁ :=
      DifferentialGeometry.Manifold.chartedSpaceTransHomeomorph (M := M₁) e.toHomeomorph
    let : ChartedSpace H M₂ :=
      DifferentialGeometry.Manifold.chartedSpaceTransHomeomorph (M := M₂) e.toHomeomorph
    exact isOpen_image_of_continuousOn_injOn (E := H) hU hhcont hhinj
  exact DifferentialGeometry.Topology.PiecewiseLinear.exists_continuousOn_pos_image_eq_of_dist_lt
    hh himage (CompactExhaustion.choice U) φ hφ hpos

end DifferentialGeometry.Topology.Manifold
