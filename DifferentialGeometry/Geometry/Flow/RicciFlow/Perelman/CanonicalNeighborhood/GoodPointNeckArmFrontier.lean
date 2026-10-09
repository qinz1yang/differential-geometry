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

def NeckCoreDiameterBound : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
      [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
      (J : RealTimeInterval) (S : SolutionOn (I := I3) (M := M) J)
      (eps : ℝ) (x : M) (t : ℝ) (neck : StrongNeck S eps x t),
      ∀ y ∈ neck.map '' (Set.univ ×ˢ Set.Icc (-10 : ℝ) 10),
        ∀ z ∈ neck.map '' (Set.univ ×ˢ Set.Icc (-10 : ℝ) 10),
          riemannianEDistOf (rescaledMetric S t (S.scalar t x) neck.Q_pos 0) y z ≤
            ENNReal.ofReal C

def NeckAxialBound : Prop :=
  ∃ Ax : ℝ, 0 < Ax ∧
    ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
      [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
      (J : RealTimeInterval) (S : SolutionOn (I := I3) (M := M) J)
      (eps : ℝ) (x : M) (t : ℝ) (neck : StrongNeck S eps x t)
      (p : Sphere 2) (k : ℝ), |k| ≤ 10 →
        riemannianEDistOf (rescaledMetric S t (S.scalar t x) neck.Q_pos 0)
          (neck.map (p, k)) (neck.map (p, 0)) ≤ ENNReal.ofReal Ax

theorem metricDistance_core_le_of_neckCoreDiameterBound
    (h : NeckCoreDiameterBound.{u}) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
        [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
        (J : RealTimeInterval) (S : SolutionOn (I := I3) (M := M) J)
        (eps : ℝ) (x : M) (t : ℝ) (neck : StrongNeck S eps x t),
        ∀ y ∈ neck.map '' (Set.univ ×ˢ Set.Icc (-10 : ℝ) 10),
          ∀ z ∈ neck.map '' (Set.univ ×ˢ Set.Icc (-10 : ℝ) 10),
            metricDistance (S.base.metric t) y z ≤ C / Real.sqrt (S.scalar t x) := by
  obtain ⟨C, hC, hbound⟩ := h
  refine ⟨C, hC, ?_⟩
  intro M _ _ _ _ _ J S eps x t neck y hy z hz
  have hb := hbound M J S eps x t neck y hy z hz
  have hscale : riemannianEDistOf (rescaledMetric S t (S.scalar t x) neck.Q_pos 0) y z =
      ENNReal.ofReal (Real.sqrt (S.scalar t x)) *
        riemannianEDistOf (S.base.metric t) y z :=
    edistOf_rescaledMetric_zero S t (S.scalar t x) neck.Q_pos y z
  rw [hscale] at hb
  have hQpos : 0 < Real.sqrt (S.scalar t x) := Real.sqrt_pos.mpr neck.Q_pos
  have hreal : Real.sqrt (S.scalar t x) *
      (riemannianEDistOf (S.base.metric t) y z).toReal ≤ C := by
    have h1 := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hQpos.le, ENNReal.toReal_ofReal hC.le] at h1
  have hdiv : (riemannianEDistOf (S.base.metric t) y z).toReal ≤
      C / Real.sqrt (S.scalar t x) := by
    rw [le_div_iff₀ hQpos]
    simpa only [mul_comm] using hreal
  simpa only [metricDistance] using hdiv

theorem two_mul_lt_one_div_eleven_of_lt_one_div_fortyfour {a : ℝ} (h : a < 1 / 44) :
    2 * a < 1 / 11 := by
  linarith

theorem ten_lt_inv_two_mul_of_pos_of_lt_one_div_fortyfour {a : ℝ} (ha : 0 < a) (h : a < 1 / 44) :
    10 < (2 * a)⁻¹ := by
  have hpos : 0 < 2 * a := by linarith
  rw [inv_eq_one_div, lt_div_iff₀ hpos]
  linarith

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
