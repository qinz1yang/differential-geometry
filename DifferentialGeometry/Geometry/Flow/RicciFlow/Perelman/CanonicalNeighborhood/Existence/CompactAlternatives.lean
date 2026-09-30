import DifferentialGeometry.Geometry.Neck.CompactClassification
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialNeckLocalTransport
import DifferentialGeometry.Topology.ThreeManifold.SphereTwoTimesCircleSimplyConnected
import DifferentialGeometry.Topology.Manifold.Orientation

noncomputable section

open Set Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Geometry.Curvature

universe u

theorem exists_cap_or_positive_or_round_canonicalWitness_tolerance_of_simply_connected :
    ∃ eta : ℝ, 0 < eta ∧ ∀ eps : ℝ, eps ≤ eta →
      ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
        [IsManifold I3 ∞ M] [T2Space M] [CompactSpace M] [SimplyConnectedSpace M]
        {D : RealTimeInterval} (S : SolutionOn (I := I3) (M := M) D) (C1 C2 t : ℝ)
        (W : ∀ x : M, CanonicalWitness S eps C1 C2 x t),
        ∃ x : M,
          (∃ cap : LocalCap S eps x t (W x).domain.carrier,
            ∃ depth : ∀ z ∈ cap.tube,
              10000 / Real.sqrt (S.scalar t x) ≤ metricDistance (S.base.metric t) x z,
              (W x).alternative = CanonicalAlternative.cap cap depth) ∨
          (∃ whole : (W x).domain.carrier = connectedComponent x,
            ∃ data : PositiveComponent (W x).domain.carrier,
              ∃ sec : SecLower (S.base.metric t) (C2⁻¹ * S.scalar t x) (W x).domain.carrier,
                (W x).alternative = CanonicalAlternative.positive whole data sec) ∨
          ∃ whole : (W x).domain.carrier = connectedComponent x,
            ∃ data : RoundComponent S eps x t (W x).domain.carrier,
              (W x).alternative = CanonicalAlternative.round whole data := by
  obtain ⟨eta, heta, hall⟩ := exists_spatial_neck_sphereTwoTimesCircle_tolerance.{u}
  refine ⟨eta, heta, ?_⟩
  intro eps heps M _ _ _ _ _ _ D S C1 C2 t W
  have hnot : ¬ ∀ x : M, Nonempty (SpatialNeck (S.base.metric t) eps x) := by
    intro hnecks
    obtain ⟨o⟩ :=
      DifferentialGeometry.Topology.Manifold.exists_manifoldOrientation_of_simply_connected
      (E := ThreeSpace) (M := M) (n := 3) (by simp [ThreeSpace])
    let orientation := DifferentialGeometry.Topology.Manifold.smoothOrientationOfManifoldOrientation
      I3 (by simpa using o)
    obtain ⟨F⟩ := hall eps heps M (S.base.metric t) orientation hnecks
    exact DifferentialGeometry.Topology.not_simplyConnectedSpace_sphereTwoTimesCircle
      (F.toHomeomorph.toHomotopyEquiv.simplyConnectedSpace_iff.mp inferInstance)
  push Not at hnot
  obtain ⟨x, hx⟩ := hnot
  refine ⟨x, ?_⟩
  cases htag : (W x).alternative with
  | neck data => exact (hx.false data.strong.toSpatialNeck).elim
  | cap data deep => exact Or.inl ⟨data, deep, rfl⟩
  | positive whole data sec => exact Or.inr (Or.inl ⟨whole, data, sec, rfl⟩)
  | round whole data => exact Or.inr (Or.inr ⟨whole, data, rfl⟩)

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
