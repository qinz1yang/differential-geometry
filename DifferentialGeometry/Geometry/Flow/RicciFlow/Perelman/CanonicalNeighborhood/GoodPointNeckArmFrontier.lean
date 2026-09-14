import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TransverseCrossingArm

set_option autoImplicit false
noncomputable section
open Bundle Manifold Set
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

def ArmNeckHeights {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold I3 ∞ M] [T2Space M] {D : RealTimeInterval}
    {S : SolutionOn (I := I3) (M := M) D} {alpha : ℝ} {x : M} {t : ℝ}
    (neck : StrongNeck S (2 * alpha) x t) (a b : MinimizingArm (S.base.metric t) x)
    (s v : ℝ) : Prop :=
  ∃ (p q : Sphere 2) (k l : ℝ),
    a.point s = neck.map (p, k) ∧ b.point v = neck.map (q, l) ∧
      k * l < 0 ∧
      twoArmNoReturnDepth (M := M) ≤ |k| ∧ |k| < (2 * alpha)⁻¹ ∧
      twoArmNoReturnDepth (M := M) ≤ |l| ∧ |l| < (2 * alpha)⁻¹

theorem exists_transversePath_of_armNeckHeights {M : Type u} [TopologicalSpace M]
    [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M] [T2Space M]
    {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D} {alpha : ℝ}
    {x : M} {t : ℝ} (neck : StrongNeck S (2 * alpha) x t)
    (a b : MinimizingArm (S.base.metric t) x) {s v : ℝ}
    (hs : s ∈ Set.Ioc 0 a.length) (hv : v ∈ Set.Ioc 0 b.length)
    (h : ArmNeckHeights neck a b s v) :
    ∃ path : TransversePath (a.point a.length) (b.point b.length)
        (neck.map '' (Set.univ ×ˢ ({0} : Set ℝ))),
      (path.intersection = 1 ∨ path.intersection = -1) ∧
      (∀ w ∈ Set.Icc s a.length,
        a.point w ∉ neck.map '' (Set.univ ×ˢ ({0} : Set ℝ))) ∧
      (∀ w ∈ Set.Icc v b.length,
        b.point w ∉ neck.map '' (Set.univ ×ˢ ({0} : Set ℝ))) := by
  obtain ⟨p, q, k, l, ha, hb, hkl, hk, hk', hl, hl'⟩ := h
  exact exists_transversePath_of_neck_heights neck a b hs hv ha hb hkl hk hk' hl hl'

def GoodPointNeckArmFrontier (kappa alpha theta C epsStar : ℝ) (Lmin Lmax : ℝ) : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
    (D : RealTimeInterval) (S : SolutionOn (I := I3) (M := M) D)
    (o : TangentOrientationSection M) (x : M) (t : ℝ),
    OrientedWitness S o epsStar kappa x t →
    ∀ a b : MinimizingArm (S.base.metric t) x, ∀ s v : ℝ,
      s ∈ Set.Ioc 0 a.length → v ∈ Set.Ioc 0 b.length →
      Real.sqrt (S.scalar t x) * s ∈ Set.Icc Lmin Lmax →
      Real.sqrt (S.scalar t x) * v ∈ Set.Icc Lmin Lmax →
      theta ≤ Real.arccos ((s ^ 2 + v ^ 2 -
        metricDistance (S.base.metric t) (a.point s) (b.point v) ^ 2) / (2 * s * v)) →
      ∃ neck : StrongNeck S (2 * alpha) x t,
        ArmNeckHeights neck a b s v ∧
        (∀ y ∈ neck.map '' (Set.univ ×ˢ Set.Icc (-10) 10),
          ∀ z ∈ neck.map '' (Set.univ ×ˢ Set.Icc (-10) 10),
            metricDistance (S.base.metric t) y z ≤ C / Real.sqrt (S.scalar t x))

theorem good_point_neck_separation_of_frontier {kappa alpha theta C epsStar : ℝ}
    {Lmin Lmax : ℝ}
    (h : GoodPointNeckArmFrontier.{u} kappa alpha theta C epsStar Lmin Lmax) :
    ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
      [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
      (D : RealTimeInterval) (S : SolutionOn (I := I3) (M := M) D)
      (o : TangentOrientationSection M) (x : M) (t : ℝ),
      OrientedWitness S o epsStar kappa x t →
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
  intro M _ _ _ _ _ D S o x t hw a b s v hs hv hsL hvL hang
  obtain ⟨neck, hheights, hdiam⟩ := h M D S o x t hw a b s v hs hv hsL hvL hang
  obtain ⟨path, hsign, hnoA, hnoB⟩ :=
    exists_transversePath_of_armNeckHeights neck a b hs hv hheights
  exact ⟨neck, path, hsign, hnoA, hnoB, hdiam⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
