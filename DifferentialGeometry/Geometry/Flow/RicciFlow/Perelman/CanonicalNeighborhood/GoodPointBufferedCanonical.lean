import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedBufferedCanonical
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.GoodPointArmBounds

noncomputable section
open Set
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem good_point_buffered_canonical {kappa alpha theta : ℝ}
    (ha : 0 < alpha) (haSmall : alpha < 1 / 44) (htheta : 0 < theta) :
    ∃ Lmin Lmax : ℝ, 0 < Lmin ∧ Lmin < Lmax ∧ ∀ H : ℝ, 0 < H →
      ∃ epsStar C : ℝ, 0 < epsStar ∧ epsStar < alpha ∧ 1 ≤ C ∧
        ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
          [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
          (D : RealTimeInterval) (S : SolutionOn (I := I3) (M := M) D)
          (o : TangentOrientationSection M) (x : M) (t : ℝ),
          IsSolutionOn S →
          Set.Ioo (t - (epsStar * S.scalar t x)⁻¹) t ⊆ D.regular →
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
  obtain ⟨Lmin, Lmax, epsArm, CArm, hLmin, hLmax, hepsArm, hepsAlpha, hCArm, harm⟩ :=
    exists_good_point_neck_arm_bounds kappa ha haSmall htheta
  refine ⟨Lmin, Lmax, hLmin, hLmax, ?_⟩
  intro H _hH
  obtain ⟨CBuffer, delta, hCBuffer, hdelta, _hdelta1, hbuffer⟩ :=
    exists_uniform_windowed_bufferedCanonical.{u} ha (by linarith) H
  let epsStar := min epsArm delta
  let C := max CArm CBuffer + 1
  have hC : 1 ≤ C := by dsimp only [C]; linarith [le_max_left CArm CBuffer]
  refine ⟨epsStar, C, lt_min hepsArm hdelta,
    (min_le_left _ _).trans_lt hepsAlpha, hC, ?_⟩
  intro M _ _ _ _ _ D S o x t hS hreg hw
  obtain ⟨B⟩ := hbuffer kappa M D S hS epsStar o x t (min_le_right _ _) hreg hw
  let P : PointedFlowData.{u, 0, 0} I3 D := { M := M, basepoint := x, S := S, isSolution := hS }
  have harm' := harm D P o epsStar x t hw.choose (min_le_left _ _) hreg
  refine ⟨⟨B.enlargeConstants (by dsimp only [C]; linarith [le_max_right CArm CBuffer])⟩, ?_⟩
  intro a b s v hs hv hsa hvb hang
  obtain ⟨neck, path, hinter, hano, hbno, hdiam⟩ := harm' a b s v hs hv hsa hvb hang
  refine ⟨neck, path, hinter, hano, hbno, ?_⟩
  intro y hy z hz
  exact (hdiam y hy z hz).trans (div_le_div_of_nonneg_right
    (by dsimp only [C]; linarith [le_max_left CArm CBuffer]) (Real.sqrt_nonneg _))

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
