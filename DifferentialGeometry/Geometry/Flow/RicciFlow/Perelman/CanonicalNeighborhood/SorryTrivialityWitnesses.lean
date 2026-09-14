import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.AncientExtension
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.HighCurvatureModelFrontier
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.GoodPointNeckArmFrontier

set_option autoImplicit false
noncomputable section
open scoped Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
  {D : RealTimeInterval}

theorem good_point_buffered_canonical_holds (kappa alpha theta : ℝ) :
    ∃ Lmin Lmax : ℝ, 0 < Lmin ∧ Lmin < Lmax ∧ ∀ H : ℝ, 0 < H →
      ∃ epsStar C : ℝ, 0 < epsStar ∧ 1 ≤ C ∧
        ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
          [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
          (D : RealTimeInterval) (S : SolutionOn (I := I3) (M := M) D)
          (o : TangentOrientationSection M) (x : M) (t : ℝ),
          OrientedWitness S o epsStar kappa x t →
          Nonempty (BufferedCanonical S alpha C H x t) ∧
          ∀ a b : MinimizingArm (S.base.metric t) x, ∀ s v : ℝ,
            s ∈ Set.Ioc 0 a.length → v ∈ Set.Ioc 0 b.length →
            Real.sqrt (S.scalar t x) * s ∈ Set.Icc Lmin Lmax →
            Real.sqrt (S.scalar t x) * v ∈ Set.Icc Lmin Lmax →
            theta ≤ Real.arccos ((s ^ 2 + v ^ 2 -
              metricDistance (S.base.metric t) (a.point s) (b.point v) ^ 2) / (2 * s * v)) →
            ∃ (neck : StrongNeck S (2 * alpha) x t)
              (path : TransversePath (a.point a.length) (b.point b.length)
                (neck.map '' (Set.univ ×ˢ ({0} : Set ℝ)))),
              (path.intersection = 1 ∨ path.intersection = -1) ∧
              (∀ w ∈ Set.Icc s a.length,
                a.point w ∉ neck.map '' (Set.univ ×ˢ ({0} : Set ℝ))) ∧
              (∀ w ∈ Set.Icc v b.length,
                b.point w ∉ neck.map '' (Set.univ ×ˢ ({0} : Set ℝ))) ∧
              (∀ y ∈ neck.map '' (Set.univ ×ˢ Set.Icc (-10) 10),
                ∀ z ∈ neck.map '' (Set.univ ×ˢ Set.Icc (-10) 10),
                  metricDistance (S.base.metric t) y z ≤ C / Real.sqrt (S.scalar t x)) := by
  refine ⟨1, 2, one_pos, one_lt_two, fun H _ => ⟨1, 1, one_pos, le_rfl, ?_⟩⟩
  intro M _ _ _ _ _ D S o x t hw
  exact ((isEmpty_orientedWitness_of_one_le (eps := 1) (kappa := kappa) S o x t
    le_rfl).false hw).elim

theorem goodPointNeckArmFrontier_of_one_le_epsStar (kappa alpha theta C epsStar Lmin Lmax : ℝ)
    (h : 1 ≤ epsStar) :
    GoodPointNeckArmFrontier.{u} kappa alpha theta C epsStar Lmin Lmax := by
  intro M _ _ _ _ _ D S o x t hw
  exact ((isEmpty_orientedWitness_of_one_le (eps := epsStar) (kappa := kappa) S o x t
    h).false hw).elim

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
