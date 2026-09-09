import DifferentialGeometry.Geometry.Comparison.Volume.Family.SmallBall
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedVolume.LowerBound.InteriorTime
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ShortTime.ReducedVolumeLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedVolume.BallEstimate.UniformUpperBound

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Set
open scoped ContDiff Manifold

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure
open MeasureTheory

universe u uE uH

section SmoothCapstone

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]
  [T2Space M] [ConnectedSpace M] [CompactSpace M]
  [I.Boundaryless]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem no_local_collapsing
    {omega : Real} (h0omega : 0 < omega)
    (S : SolutionOn (I := I) (M := M)
      (RealTimeInterval.closedOpen 0 omega h0omega))
    (hS : IsSolutionOn (I := I) S)
    {rho : Real} (hrho : 0 < rho) :
    NoLocalCollapsing S rho := by
  classical
  by_cases hdim : Module.finrank ℝ E = 0
  · let : Subsingleton E := Module.finrank_zero_iff.mp hdim
    let : Subsingleton H := I.injective.subsingleton
    let : DiscreteTopology M := ChartedSpace.discreteTopology H M
    let : Subsingleton M := subsingleton_of_preconnected_totallyDisconnected
    let mu := riemannianVolumeMeasure (I := I) (M := M) (S.base.metric 0)
    let : mu.IsOpenPosMeasure := riemannianVolumeMeasure_isOpenPosMeasure _
    let : IsFiniteMeasure mu := riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace _
    have hmu : 0 < mu Set.univ := isOpen_univ.measure_pos mu Set.univ_nonempty
    have hmutop : mu Set.univ ≠ ⊤ := (measure_lt_top mu Set.univ).ne
    have hkappa : 0 < (mu Set.univ).toReal := ENNReal.toReal_pos hmu.ne' hmutop
    refine ⟨(mu Set.univ).toReal, hkappa, hrho, ?_⟩
    intro time B hBrho hB
    refine ⟨hkappa, ?_⟩
    have hv (z : M) (v : TangentSpace I z) : v = 0 := by
      apply (tangentSpaceModelContinuousLinearEquiv (I := I) z).injective
      exact Subsingleton.elim _ _
    have hset : B.set = Set.univ := by
      apply Set.eq_univ_of_forall
      intro x
      change riemannianEDistOf (S.base.metric (time : ℝ)) B.center x <
        ENNReal.ofReal B.radius
      rw [Subsingleton.elim x B.center, riemannianEDistOf_self]
      exact ENNReal.ofReal_pos.mpr B.radius_pos
    have hmeasure := volumeMeasure_le (I := I) (M := M)
      (S.base.metric (time : ℝ)) (S.base.metric 0)
      (Q := 1) zero_lt_one (fun x v => by rw [hv x v]; simp)
    rw [hdim, pow_zero, mul_one, ENNReal.ofReal_toReal hmutop]
    calc
      mu Set.univ ≤ riemannianVolumeMeasure (I := I) (M := M)
          (S.base.metric (time : ℝ)) Set.univ := by
        simpa only [one_pow, Real.sqrt_one, ENNReal.ofReal_one, one_smul] using
          hmeasure Set.univ
      _ = B.volume := by
        simp only [FlowMetricBall.volume, volumeMeasureOn_eq_metric,
          SolutionOn.family_metric, hset]
  let : NeZero (Module.finrank ℝ E) := ⟨hdim⟩
  let : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let : MetricSpace M := TopologicalSpace.metrizableSpaceMetric M
  let : T2Space (TangentBundle I M) := inferInstance
  obtain ⟨tauE, kappaE, htauE, htauEomega, hkappaE, hearly⟩ :=
    DifferentialGeometry.Geometry.Riemannian.VolumeComparison.family_vol_low
      (I := I) (M := M) (rho := rho) h0omega S.family.metric hS.smoothMetric
  let a₀ : Real := tauE / 4
  let a : Real := tauE / 2
  have ha₀a : a₀ < a := by
    dsimp only [a₀, a]
    linarith
  have haomega : a < omega := by
    dsimp only [a]
    linarith
  have hregLate : Set.Ico a₀ omega ⊆
      (RealTimeInterval.closedOpen 0 omega h0omega).regular := by
    intro q hq
    exact ⟨(div_pos htauE (by norm_num)).trans_le hq.1, hq.2⟩
  let x₀ : M := Classical.choice inferInstance
  obtain ⟨v₀, hv₀, hlate⟩ :=
    redVolume_late_low (I := I) S hS ha₀a haomega hregLate x₀
  have hv₀one : v₀ ≤ 1 := by
    have hfloor : v₀ ≤ redVolume S a x₀ (a - a₀) :=
      hlate le_rfl haomega x₀ (sub_pos.mpr ha₀a) le_rfl
    have hslab : Set.Icc (a - (a - a₀)) a ⊆
        (RealTimeInterval.closedOpen 0 omega h0omega).regular := by
      intro q hq
      have hq' : q ∈ Set.Icc a₀ a := by
        simpa only [sub_sub_cancel] using hq
      exact hregLate ⟨hq'.1, hq'.2.trans_lt haomega⟩
    exact hfloor.trans
      (redVolume_le_one (I := I) S hS a x₀ (a - a₀)
        (sub_pos.mpr ha₀a) hslab)
  have hv₀top : v₀ ≠ (⊤ : ENNReal) := by
    exact (hv₀one.trans_lt ENNReal.one_lt_top).ne
  let eta : ENNReal := v₀ / 2
  have heta : 0 < eta := by
    dsimp only [eta]
    exact ENNReal.half_pos hv₀.ne'
  obtain ⟨eps₀, heps₀, hball⟩ :=
    exists_pos_redVolume_le_on_flowMetricBall (E := E) (I := I) (M := M)
      (Q := 4 / 3) (by norm_num) rho hrho eta heta
  let eps : Real := min eps₀ (1 / 2)
  have heps : 0 < eps := lt_min heps₀ (by norm_num)
  have heps_le : eps ≤ eps₀ := min_le_left _ _
  have heps_half : eps ≤ (1 / 2 : Real) := min_le_right _ _
  let n : Nat := Module.finrank Real E
  let core : Real := Real.exp
    ((n : Real) ^ 2 * eps / 3 -
      ((n : Real) / 2) * Real.log eps -
      ((n : Real) / 2) * Real.log (4 * Real.pi))
  let sqrtC : Real := Real.sqrt ((4 / 3 : Real) ^ n)
  let Ceps : Real := core * sqrtC
  have hcore : 0 < core := Real.exp_pos _
  have hsqrtC : 0 < sqrtC := by
    dsimp only [sqrtC]
    exact Real.sqrt_pos.2 (pow_pos (by norm_num) _)
  have hCeps : 0 < Ceps := mul_pos hcore hsqrtC
  let delta : ENNReal := v₀ / 2
  let coeff : ENNReal := ENNReal.ofReal Ceps
  have hdelta : 0 < delta := by
    simpa only [delta] using ENNReal.half_pos hv₀.ne'
  have hdeltatop : delta ≠ (⊤ : ENNReal) := by
    exact ENNReal.div_ne_top hv₀top (by norm_num)
  have hcoeff : 0 < coeff := by
    simpa only [coeff] using ENNReal.ofReal_pos.2 hCeps
  have hcoefftop : coeff ≠ (⊤ : ENNReal) := by
    exact ENNReal.ofReal_ne_top
  let kappaL : Real := (delta / coeff).toReal
  have hkappaL : 0 < kappaL := by
    apply ENNReal.toReal_pos
    · exact (ENNReal.div_pos hdelta.ne' hcoefftop).ne'
    · exact ENNReal.div_ne_top hdeltatop hcoeff.ne'
  let kappa : Real := min kappaE kappaL
  have hkappa : 0 < kappa := lt_min hkappaE hkappaL
  refine ⟨kappa, hkappa, hrho, ?_⟩
  intro t B hBrho hB
  have hleft_mem :
      (t : Real) - B.radius ^ 2 ∈
        (RealTimeInterval.closedOpen 0 omega h0omega).carrier :=
    hB.1 ⟨le_rfl, sub_le_self _ (sq_nonneg B.radius)⟩
  have hleft_nonneg : 0 ≤ (t : Real) - B.radius ^ 2 := by
    simpa only [RealTimeInterval.closedOpen] using hleft_mem.1
  have hsq : B.radius ^ 2 ≤ (t : Real) := by
    linarith
  by_cases ht : (t : Real) ≤ a
  · have htE : (t : Real) ≤ tauE := by
      dsimp only [a] at ht
      linarith
    refine ⟨hkappa, ?_⟩
    have hvol := hearly t htE B.center B.radius_pos hBrho hsq
    have hvol' : ENNReal.ofReal kappaE *
        ENNReal.ofReal B.radius ^ Module.finrank Real E ≤ B.volume := by
      simpa only [FlowMetricBall.volume, FlowMetricBall.set,
        FlowMetricBall.setAt, volumeMeasureOn_eq_metric,
        SolutionOn.family_metric] using hvol
    exact (mul_le_mul'
      (ENNReal.ofReal_le_ofReal (min_le_left kappaE kappaL)) le_rfl).trans hvol'
  · have hat : a ≤ (t : Real) := le_of_not_ge ht
    have hregB : Set.Ioc ((t : Real) - B.radius ^ 2) (t : Real) ⊆
        (RealTimeInterval.closedOpen 0 omega h0omega).regular := by
      intro q hq
      have hqCarrier := hB.1 ⟨hq.1.le, hq.2⟩
      exact ⟨hleft_nonneg.trans_lt hq.1, hqCarrier.2⟩
    let tau : Real := eps * B.radius ^ 2
    have htau : 0 < tau := mul_pos heps (sq_pos_of_pos B.radius_pos)
    have htau_le : tau ≤ (t : Real) - a₀ := by
      have hhalf_t : eps * B.radius ^ 2 ≤ (t : Real) / 2 := by
        calc
          eps * B.radius ^ 2 ≤ (1 / 2 : Real) * B.radius ^ 2 :=
            mul_le_mul_of_nonneg_right heps_half (sq_nonneg B.radius)
          _ ≤ (t : Real) / 2 := by linarith
      dsimp only [tau]
      dsimp only [a₀, a] at hat ⊢
      linarith
    have hlower : v₀ ≤ redVolume S (t : Real) B.center tau :=
      hlate hat t.2.2 B.center htau htau_le
    let c : Real := Real.exp
      ((n : Real) ^ 2 * eps / 3 -
        ((n : Real) / 2) * Real.log tau -
        ((n : Real) / 2) * Real.log (4 * Real.pi))
    have hupper : redVolume S (t : Real) B.center tau ≤
        ENNReal.ofReal c * (ENNReal.ofReal sqrtC * B.volume) + eta := by
      simpa only [tau, c, n, sqrtC] using
        hball hS B hBrho hB hregB eps heps heps_le
    have hhalf : delta ≤
        ENNReal.ofReal c * (ENNReal.ofReal sqrtC * B.volume) := by
      have hsub : v₀ - eta ≤
          ENNReal.ofReal c * (ENNReal.ofReal sqrtC * B.volume) := by
        apply (tsub_le_iff_right).2
        simpa only [add_comm] using hlower.trans hupper
      rw [show eta = v₀ / 2 by rfl, ENNReal.sub_half hv₀top] at hsub
      simpa only [delta] using hsub
    have hlogtau : Real.log tau =
        Real.log eps + 2 * Real.log B.radius := by
      dsimp only [tau]
      rw [Real.log_mul heps.ne' (sq_pos_of_pos B.radius_pos).ne']
      rw [Real.log_pow]
      norm_num
    have hcscale : c * B.radius ^ n = core := by
      have hexpPow : Real.exp ((n : Real) * Real.log B.radius) =
          B.radius ^ n := by
        rw [Real.exp_nat_mul, Real.exp_log B.radius_pos]
      dsimp only [c, core]
      rw [hlogtau]
      rw [show
        (n : Real) ^ 2 * eps / 3 -
            (n : Real) / 2 * (Real.log eps + 2 * Real.log B.radius) -
              (n : Real) / 2 * Real.log (4 * Real.pi) =
          ((n : Real) ^ 2 * eps / 3 -
              (n : Real) / 2 * Real.log eps -
                (n : Real) / 2 * Real.log (4 * Real.pi)) -
            (n : Real) * Real.log B.radius by ring]
      rw [Real.exp_sub, hexpPow]
      field_simp [ne_of_gt (pow_pos B.radius_pos n)]
    have hscaled : delta * ENNReal.ofReal B.radius ^ n ≤
        coeff * B.volume := by
      have hc : 0 < c := Real.exp_pos _
      calc
        delta * ENNReal.ofReal B.radius ^ n ≤
            (ENNReal.ofReal c * (ENNReal.ofReal sqrtC * B.volume)) *
              ENNReal.ofReal B.radius ^ n :=
          by
            exact mul_le_mul_left hhalf (ENNReal.ofReal B.radius ^ n)
        _ = (ENNReal.ofReal c * ENNReal.ofReal sqrtC *
              ENNReal.ofReal B.radius ^ n) * B.volume := by
          ac_rfl
        _ = ENNReal.ofReal
              ((c * sqrtC) * B.radius ^ n) * B.volume := by
          congr 1
          rw [← ENNReal.ofReal_pow B.radius_pos.le,
            ← ENNReal.ofReal_mul hc.le,
            ← ENNReal.ofReal_mul (mul_nonneg hc.le hsqrtC.le)]
        _ = coeff * B.volume := by
          congr 1
          rw [show (c * sqrtC) * B.radius ^ n = Ceps by
            dsimp only [Ceps]
            rw [show (c * sqrtC) * B.radius ^ n =
              (c * B.radius ^ n) * sqrtC by ring, hcscale]]
    have hratio : (delta / coeff) * ENNReal.ofReal B.radius ^ n ≤
        B.volume := by
      have hdiv :
          (delta * ENNReal.ofReal B.radius ^ n) / coeff ≤ B.volume :=
        (ENNReal.div_le_iff hcoeff.ne' hcoefftop).2 (by
          simpa only [mul_comm] using hscaled)
      simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hdiv
    refine ⟨hkappa, ?_⟩
    have hkappaLvol : ENNReal.ofReal kappaL *
        ENNReal.ofReal B.radius ^ Module.finrank Real E ≤ B.volume := by
      have hratioTop : delta / coeff ≠ (⊤ : ENNReal) :=
        ENNReal.div_ne_top hdeltatop hcoeff.ne'
      have hkappaLEq : ENNReal.ofReal kappaL = delta / coeff := by
        dsimp only [kappaL]
        exact ENNReal.ofReal_toReal hratioTop
      rw [hkappaLEq]
      simpa only [n] using hratio
    exact (mul_le_mul'
      (ENNReal.ofReal_le_ofReal (min_le_right kappaE kappaL)) le_rfl).trans
        hkappaLvol

end SmoothCapstone

end DifferentialGeometry.PDE.RicciFlow.Perelman
