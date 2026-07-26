import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.NoncollapseSpan

set_option autoImplicit false

/-!
# No local collapsing after a positive time on a half-open flow interval

This file removes the artificial finite upper endpoint from the positive-time
noncollapsing theorem when the flow interval is `[0, ω)`.  It still starts at a
strictly positive time.  The remaining initial-time producer is separate.
-/

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

noncomputable section

open Bundle MeasureTheory Set Tensor0SBundle
open scoped Manifold ContDiff ENNReal
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Entropy

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

/-- A Ricci flow on `[0, ω)` is uniformly noncollapsed on every
curvature-controlled ball below a fixed radius after any fixed positive start
time `a`.  The constant is independent of the later time, even though the
regular slab used in the proof ends before `ω` and is chosen around that time. -/
theorem noncollapse_after
    [T2Space (TangentBundle I M)]
    {omega : Real} (h0omega : 0 < omega)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 omega h0omega))
    (hS : IsSolutionOn (I := I) S)
    (hDim : Module.finrank Real E = 3)
    {a0 a rho : Real} (h0a0 : 0 < a0) (ha0a : a0 < a)
    (hrho : 0 < rho) :
    ∃ kappa : Real, 0 < kappa ∧
      ∀ (t : RealTimeInterval.FlowTime (RealTimeInterval.closedOpen 0 omega h0omega)),
        a ≤ (t : Real) →
        ∀ B : FlowMetricBall S t, B.radius ≤ rho → B.IsRmControlled →
          B.IsKappaNoncollapsed kappa := by
  classical
  let tauMax : Real := rho ^ 2 + (omega - a) + 1
  obtain ⟨L, hL⟩ := w_span_uniform (I := I) (M := M) S hS hDim
    (tauMax := tauMax) ha0a
  let kappa : Real :=
    Real.exp (L - collapseWConst (Module.finrank Real E) - 1)
  have hkappa : 0 < kappa := Real.exp_pos _
  refine ⟨kappa, hkappa, ?_⟩
  intro t hta B hBrho hB
  refine ⟨hkappa, ?_⟩
  have htomega : (t : Real) < omega := t.2.2
  let b : Real := ((t : Real) + omega) / 2
  have htb : (t : Real) ≤ b := by
    dsimp only [b]
    linarith
  have hbomega : b < omega := by
    dsimp only [b]
    linarith
  have hab : a ≤ b := hta.trans htb
  have hreg : Set.Icc a0 b ⊆ (RealTimeInterval.closedOpen 0 omega h0omega).regular := by
    intro s hs
    exact ⟨h0a0.trans_le hs.1, hs.2.trans_lt hbomega⟩
  have htIcc : (t : Real) ∈ Set.Icc a b := ⟨hta, htb⟩
  obtain ⟨B', w, _hnest, hB'radius, _hB'curv, _hnorm,
      hw, hwpos, hwmass, hwupper⟩ :=
    exists_sel_w_bound (I := I) (M := M) B hB
      (δ := 1) (hδ := by norm_num)
  have hB'rho : B'.radius ≤ rho := hB'radius.trans hBrho
  have hB'sq : B'.radius ^ 2 ≤ rho ^ 2 :=
    (sq_le_sq₀ B'.radius_pos.le hrho.le).2 hB'rho
  have htheta : 0 < B'.radius ^ 2 := sq_pos_of_pos B'.radius_pos
  have hbudget : B'.radius ^ 2 + ((t : Real) - a) < tauMax := by
    dsimp only [tauMax]
    linarith [hB'sq, htomega]
  have hwsq : ContMDiff I 𝓘(Real) ∞ (fun x : M => w x * w x) := by
    simpa only [Pi.mul_apply] using hw.mul hw
  have hwsq_pos : ∀ x : M, 0 < w x * w x := by
    intro x
    exact mul_pos (hwpos x) (hwpos x)
  have hwsq_mass :
      (∫ x, w x * w x
        ∂(riemannianVolumeMeasure (I := I) (M := M)
          (S.family.metric (t : Real)))) = 1 := by
    simpa only [pow_two, SolutionOn.family_metric] using hwmass
  have hwlower :
      L ≤ flowW (I := I) (M := M) S (t : Real) (B'.radius ^ 2)
        (fun x => w x * w x) :=
    hL hab hreg (t : Real) htIcc htheta hbudget hwsq hwsq_pos hwsq_mass
  have hwupper' :
      flowW (I := I) (M := M) S (t : Real) (B'.radius ^ 2)
          (fun x => w x * w x) ≤
        collapseWConst (Module.finrank Real E) +
          Real.log (B.volume.toReal /
            B.radius ^ Module.finrank Real E) + 1 := by
    simpa only [flowW, SolutionOn.family_metric, SolutionOn.scalar,
      SolutionFamily.scalar, SolutionOn.scalar_eq_metricTrace] using hwupper
  have hlog :
      L - collapseWConst (Module.finrank Real E) - 1 ≤
        Real.log (B.volume.toReal / B.radius ^ Module.finrank Real E) := by
    linarith [hwlower.trans hwupper']
  have hBvol : 0 < B.volume.toReal := by
    simpa only [FlowMetricBall.volume, FlowMetricBall.set, FlowMetricBall.setAt,
      volumeMeasureOn_eq_metric, SolutionOn.family_metric] using
        edist_vol_pos (I := I) (M := M)
          (S.base.metric t) B.center B.radius_pos
  have hratio :
      0 < B.volume.toReal / B.radius ^ Module.finrank Real E :=
    div_pos hBvol (pow_pos B.radius_pos _)
  have hkappa_ratio :
      kappa ≤ B.volume.toReal / B.radius ^ Module.finrank Real E := by
    dsimp only [kappa]
    rw [← Real.exp_log hratio]
    exact Real.exp_le_exp.mpr hlog
  have hkappa_real :
      kappa * B.radius ^ Module.finrank Real E ≤ B.volume.toReal :=
    (le_div_iff₀ (pow_pos B.radius_pos _)).1 hkappa_ratio
  calc
    ENNReal.ofReal kappa *
          ENNReal.ofReal B.radius ^ Module.finrank Real E =
        ENNReal.ofReal
          (kappa * B.radius ^ Module.finrank Real E) := by
      rw [ENNReal.ofReal_mul hkappa.le,
        ENNReal.ofReal_pow B.radius_pos.le]
    _ ≤ ENNReal.ofReal B.volume.toReal :=
      ENNReal.ofReal_le_ofReal hkappa_real
    _ ≤ B.volume := ENNReal.ofReal_toReal_le

end

end DifferentialGeometry.PDE.RicciFlow.Perelman
