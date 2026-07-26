import DifferentialGeometry.Geometry.Comparison.Volume.FamilySmallBall
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.NoncollapseOpen

set_option autoImplicit false

/-!
# Initial-time small-ball producer for Perelman noncollapsing

This file supplies the initial-boundary geometric input for no-local-collapsing
on a half-open short-time Ricci flow.  The positive-time entropy argument is
already in `NoncollapseOpen`; the compact-uniform volume producer is imported
from `FamilySmallBall`.
-/

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

noncomputable section

open Bundle MeasureTheory Set Tensor0SBundle
open scoped Manifold ContDiff ENNReal
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open DifferentialGeometry.Integral.Connection

universe u uE uH

variable {M : Type u}
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
variable [T3Space M] [SigmaCompactSpace M] [ConnectedSpace M] [CompactSpace M]
variable [I.Boundaryless] [BoundarylessManifold I M]

private local instance : CompleteSpace E := FiniteDimensional.complete Real E
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

omit [ConnectedSpace M] [BoundarylessManifold I M] in
/-- The raw initial-boundary producer: for a short-time Ricci flow on
`[0, omega)`, small enough early Riemannian-distance balls have a uniform
normalized volume lower bound, for every centre and every radius satisfying
`r^2 <= t`. -/
theorem early_vol_low
    [T2Space (TangentBundle I M)]
    {omega : Real} (h0omega : 0 < omega)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 omega h0omega))
    (hS : IsSolutionOn (I := I) S)
    (_hDim : Module.finrank Real E = 3)
    {rho : Real} (hrho : 0 < rho) :
    ∃ tau kappa : Real, 0 < tau ∧ tau < omega ∧ 0 < kappa ∧
      ∀ (t : RealTimeInterval.FlowTime (RealTimeInterval.closedOpen 0 omega h0omega)),
        (t : Real) ≤ tau →
        ∀ (p : M) {r : Real}, 0 < r → r ≤ rho → r ^ 2 ≤ (t : Real) →
          ENNReal.ofReal kappa * ENNReal.ofReal r ^ Module.finrank Real E ≤
            DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure
              (I := I) (M := M) (S.base.metric t)
              {x : M | DifferentialGeometry.riemannianEDistOf
                (I := I) (S.base.metric t) p x < ENNReal.ofReal r} := by
  simpa only [SolutionOn.family_metric] using
    family_vol_low (I := I) (M := M) h0omega S.family hS.smoothMetric hrho

omit [ConnectedSpace M] [BoundarylessManifold I M] in
/-- Flow-ball form of `early_vol_low`.  This is only the definitional adapter
from raw Riemannian-distance balls to `FlowMetricBall.IsKappaNoncollapsed`; the
geometric content remains entirely in `early_vol_low`. -/
theorem early_ball_low
    [T2Space (TangentBundle I M)]
    {omega : Real} (h0omega : 0 < omega)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 omega h0omega))
    (hS : IsSolutionOn (I := I) S)
    (hDim : Module.finrank Real E = 3)
    {rho : Real} (hrho : 0 < rho) :
    ∃ tau kappa : Real, 0 < tau ∧ tau < omega ∧ 0 < kappa ∧
      ∀ (t : RealTimeInterval.FlowTime (RealTimeInterval.closedOpen 0 omega h0omega)),
        (t : Real) ≤ tau →
        ∀ B : FlowMetricBall S t, B.radius ≤ rho → B.radius ^ 2 ≤ (t : Real) →
          B.IsKappaNoncollapsed kappa := by
  classical
  obtain ⟨tau, kappa, htau0, htauomega, hkappa, hvol⟩ :=
    early_vol_low (I := I) (M := M) h0omega S hS hDim hrho
  refine ⟨tau, kappa, htau0, htauomega, hkappa, ?_⟩
  intro t ht B hBrho hsq
  refine ⟨hkappa, ?_⟩
  simpa only [FlowMetricBall.volume, FlowMetricBall.set, FlowMetricBall.setAt,
    DifferentialGeometry.Integral.Measure.volumeMeasureOn_eq_metric,
    SolutionOn.family_metric] using
      hvol t ht B.center B.radius_pos hBrho hsq

omit [NeZero (Module.finrank Real E)] [ConnectedSpace M] [CompactSpace M]
  [I.Boundaryless] [BoundarylessManifold I M] in
private theorem kappa_mono
    {D : RealTimeInterval} {S : SolutionOn (I := I) (M := M) D}
    {t : RealTimeInterval.FlowTime D} {B : FlowMetricBall S t}
    {kappa kappa' : Real} (hkappa : 0 < kappa) (hle : kappa ≤ kappa')
    (hB : B.IsKappaNoncollapsed kappa') :
    B.IsKappaNoncollapsed kappa := by
  rcases hB with ⟨_, hvol⟩
  refine ⟨hkappa, ?_⟩
  exact (mul_le_mul' (ENNReal.ofReal_le_ofReal hle) le_rfl).trans hvol

/-- Assuming the isolated initial small-ball producer, a compact short-time
Ricci flow on `[0, omega)` satisfies Perelman's no-local-collapsing predicate
below any fixed positive scale. -/
theorem no_local_open
    [T2Space (TangentBundle I M)]
    {omega : Real} (h0omega : 0 < omega)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 omega h0omega))
    (hS : IsSolutionOn (I := I) S)
    (hDim : Module.finrank Real E = 3)
    {rho : Real} (hrho : 0 < rho) :
    NoLocalCollapsing S rho := by
  classical
  obtain ⟨tau, kappa0, htau0, htauomega, hkappa0, hearly⟩ :=
    early_ball_low (I := I) (M := M) h0omega S hS hDim hrho
  have htau2 : 0 < tau / 2 := half_pos htau0
  have htau2tau : tau / 2 < tau := half_lt_self htau0
  obtain ⟨kappa1, hkappa1, hafter⟩ :=
    noncollapse_after (I := I) (M := M) h0omega S hS hDim
      htau2 htau2tau hrho
  let kappa : Real := min kappa0 kappa1
  have hkappa : 0 < kappa := lt_min hkappa0 hkappa1
  refine ⟨kappa, hkappa, hrho, ?_⟩
  intro t B hBrho hB
  by_cases ht : (t : Real) ≤ tau
  · have hsq : B.radius ^ 2 ≤ (t : Real) := by
      have hleft_mem :
          (t : Real) - B.radius ^ 2 ∈
            (RealTimeInterval.closedOpen 0 omega h0omega).carrier := by
        exact hB.1 ⟨le_rfl, by nlinarith [sq_nonneg B.radius]⟩
      have hleft_nonneg : 0 ≤ (t : Real) - B.radius ^ 2 := by
        simpa [RealTimeInterval.closedOpen] using hleft_mem.1
      nlinarith
    exact kappa_mono (I := I) (M := M) hkappa (min_le_left _ _)
      (hearly t ht B hBrho hsq)
  · have htau_le : tau ≤ (t : Real) := le_of_not_ge ht
    exact kappa_mono (I := I) (M := M) hkappa (min_le_right _ _)
      (hafter t htau_le B hBrho hB)

end

end DifferentialGeometry.PDE.RicciFlow.Perelman
