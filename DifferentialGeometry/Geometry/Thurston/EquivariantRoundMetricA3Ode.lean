import DifferentialGeometry.Geometry.Thurston.EquivariantRoundMetricA3Flow
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.FiniteTime.CurvatureBlowupRate
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Restriction

/-!
# ODE comparison for the scalar curvature of a surface flow

Chapter 7, packet P8, surface lemma U1, route (a), lane a3. In dimension two the scalar curvature
satisfies `∂ₜ R = Δ R + R²` (`surfaceScalar_hasDerivAt`), so it is a heat-potential subsolution
(`surfaceFlow_scalar_heatSubsolution`). `surfaceFlow_scalar_le_of_ode`: if `R(a, ·) ≤ q` with
`q > 0` and `q (t - a) < 1` then `R(t, ·) ≤ q / (1 - q (t - a))`, by the weak maximum principle
with ODE comparison (`scalar_weak_maximum_principle_ode_compare_subsolution_of_heat_pot`) applied
to the flow restricted to `[a, t]` and shifted to `[0, t - a]`.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open Filter Topology Set
open scoped Manifold ContDiff

namespace GC.Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [CompactSpace M]
  {T : ℝ} {hT : 0 < T}

omit [CompactSpace M] in
theorem surfaceFlow_scalar_heatSubsolution (hdim : Module.finrank ℝ E = 2)
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S) :
    IsHeatPotSubsolutionOn D (flowG S) (fun s x => S.scalar s x) (fun s x => S.scalar s x) where
  jointSmooth := scalar_joint S hS
  jointCont := hS.scalarCont
  sliceSmooth := fun t _ => scalarSmoothOfSolution S t
  timeDiff := fun t ht x => (surfaceScalar_hasDerivAt S hS hdim ht x).differentiableAt
  equation_le := by
    intro t ht x
    rw [(surfaceScalar_hasDerivAt S hS hdim ht x).deriv]
    have hlap : laplacianAt (flowG S) t (S.scalar t) x =
        ΔG (S.family.metric t) ⟨S.scalar t, scalarSmoothOfSolution S t⟩ x :=
      laplacian_levi_eq (S.family.metric t) (scalarSmoothOfSolution S t) x
    rw [hlap]
    nlinarith

theorem odeBarrier_hasDerivAt {q s : ℝ} (hs : q * s < 1) :
    HasDerivAt (fun r : ℝ => q / (1 - q * r)) ((q / (1 - q * s)) ^ 2) s := by
  have hden : (1 - q * s) ≠ 0 := by linarith
  have hd : HasDerivAt (fun r : ℝ => 1 - q * r) (-q) s := by
    simpa using ((hasDerivAt_id s).const_mul q).const_sub 1
  have h := (hasDerivAt_const s q).div hd hden
  convert h using 1
  field_simp
  ring

theorem surfaceFlow_scalar_le_of_ode (hdim : Module.finrank ℝ E = 2)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 T hT)) (hS : IsSolutionOn S)
    {a t q : ℝ} (ha : 0 < a) (hat : a < t) (htT : t < T) (hq : ∀ x, S.scalar a x ≤ q)
    (hq0 : 0 < q) (hqt : q * (t - a) < 1) (x : M) :
    S.scalar t x ≤ q / (1 - q * (t - a)) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let Dsub := RealTimeInterval.closed a t hat.le
  let U := S.timeRestrict Dsub
  have hU : IsSolutionOn U := isSolutionOn_timeRestrict hS
    (fun s hs => (⟨ha.le.trans hs.1, lt_of_le_of_lt hs.2 htT⟩ : s ∈ Ico 0 T))
    (fun s hs => (⟨ha.trans hs.1, hs.2.trans htT⟩ : s ∈ Ioo 0 T))
  have hT' : (0 : ℝ) ≤ t - a := sub_nonneg.mpr hat.le
  let Dsh := RealTimeInterval.closed 0 (t - a) hT'
  have hsub := isHeatPotSubsolutionOn_timeShift_flowG (Dsub' := Dsh) U _ _ a
    (surfaceFlow_scalar_heatSubsolution hdim U hU)
    (fun s hs => (⟨by linarith [hs.1], by linarith [hs.2]⟩ : s + a ∈ Icc a t))
    (fun s hs => (⟨by linarith [hs.1], by linarith [hs.2]⟩ : s + a ∈ Ioo a t))
  let c : ℝ → ℝ := fun r => q / (1 - q * r)
  have hden : ∀ r ∈ Icc 0 (t - a), q * r < 1 := fun r hr =>
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left hr.2 hq0.le) hqt
  have hc_cont : ContinuousOn c (Icc 0 (t - a)) := fun r hr =>
    (odeBarrier_hasDerivAt (hden r hr)).continuousAt.continuousWithinAt
  let u : ℝ → M → ℝ := fun s y => U.scalar (s + a) y
  have hu_cont : ContinuousOn (fun p : ℝ × M => u p.1 p.2) (spacetimeSlab (M := M) (t - a)) :=
    hsub.jointCont
  obtain ⟨R0, hR0⟩ := (scalarWeakMaximumPrincipleValueSet_isCompact (M := M) (t - a) u c
    hu_cont hc_cont).isBounded.exists_norm_le
  have hcmp := scalar_weak_maximum_principle_ode_compare_subsolution_of_heat_pot
    (flowG (U.timeShift a)) (t - a) hT' u c (fun b _ => b ^ 2) (Real.toNNReal (2 * R0)) _ hsub
    hc_cont
    (fun r hr _ => (odeBarrier_hasDerivAt (hden r hr)).differentiableAt.differentiableWithinAt)
    (fun r _ y => le_of_eq (by ring))
    (fun r hr hr0 => by
      have hTpos : (0 : ℝ) < t - a := lt_of_lt_of_le hr0 hr.2
      exact (odeBarrier_hasDerivAt (hden r hr)).hasDerivWithinAt.derivWithin
        ((uniqueDiffOn_Icc hTpos) r hr))
    (fun y => by
      change U.scalar (0 + a) y ≤ q / (1 - q * 0)
      rw [zero_add, mul_zero, sub_zero, div_one]
      exact hq y)
    (fun r _ => by
      rw [lipschitzOnWith_iff_dist_le_mul]
      intro b hb b' hb'
      have hb0 := hR0 b hb
      have hb1 := hR0 b' hb'
      rw [Real.norm_eq_abs] at hb0 hb1
      have hR0nn : 0 ≤ R0 := (abs_nonneg b).trans hb0
      rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ (by positivity)]
      rw [show b ^ 2 - b' ^ 2 = (b + b') * (b - b') by ring, abs_mul]
      exact mul_le_mul_of_nonneg_right (by
        calc |b + b'| ≤ |b| + |b'| := abs_add_le b b'
          _ ≤ 2 * R0 := by linarith) (abs_nonneg _))
  have h := hcmp (t - a) ⟨hT', le_rfl⟩ x
  change U.scalar (t - a + a) x ≤ q / (1 - q * (t - a)) at h
  rwa [sub_add_cancel] at h

end GC.Geometry
