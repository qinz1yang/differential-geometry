import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.MetricComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.Noncollapsing.FlowBall.MetricComparison
import DifferentialGeometry.Geometry.Metric.Completeness

noncomputable section
namespace DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall

open Bundle MeasureTheory Set
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Integral.Measure
open scoped ContDiff ENNReal Manifold Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem exists_pos_volume_le_on_terminal_ball {Q : Real} (hQ : 1 < Q) :
    ∃ eps₀ : Real, 0 < eps₀ ∧
      ∀ {D : RealTimeInterval} {S : SolutionOn (I := I) (M := M) D},
        IsSolutionOn (I := I) S →
        ∀ {time : RealTimeInterval.FlowTime D} (B : FlowMetricBall S time),
          B.IsRmControlled →
          Set.Ioo ((time : Real) - B.radius ^ 2) (time : Real) ⊆ D.regular →
          RiemannianMetricComplete (I := I) (S.base.metric (time : Real)) →
          ∀ eps : Real, 0 < eps → eps ≤ eps₀ →
            let K : Set M := {y | riemannianEDistOf (I := I)
              (S.base.metric (time : Real)) B.center y ≤
                ENNReal.ofReal (B.radius / 32)}
            riemannianVolumeMeasure (I := I) (M := M)
                (S.base.metric ((time : Real) - eps * B.radius ^ 2)) K ≤
              ENNReal.ofReal
                  (Real.sqrt (Q ^ Module.finrank Real E)) *
                B.volume := by
  by_cases hdim : Module.finrank Real E = 0
  · let : Subsingleton E := Module.finrank_zero_iff.mp hdim
    refine ⟨1, zero_lt_one, ?_⟩
    intro D S hS time B hB hreg hcomplete eps heps heps₀
    dsimp only
    let K : Set M := {y | riemannianEDistOf (I := I)
      (S.base.metric (time : Real)) B.center y ≤ ENNReal.ofReal (B.radius / 32)}
    have hmeasure := volumeMeasure_le (I := I) (M := M)
      (S.base.metric (time : Real))
      (S.base.metric ((time : Real) - eps * B.radius ^ 2))
      (Q := Q) (zero_lt_one.trans hQ) (fun x v => by
        have hv : v = (0 : TangentSpace I x) := by
          apply (tangentSpaceModelContinuousLinearEquiv (I := I) x).injective
          exact Subsingleton.elim _ _
        rw [hv]
        simp)
    have hKB : K ⊆ B.set := by
      intro x hx
      change riemannianEDistOf (S.base.metric (time : Real)) B.center x <
        ENNReal.ofReal B.radius
      have hx' : riemannianEDistOf (S.base.metric (time : Real)) B.center x ≤
          ENNReal.ofReal (B.radius / 32) := by
        simpa only [K, Set.mem_ofPred_eq] using hx
      exact hx'.trans_lt ((ENNReal.ofReal_lt_ofReal_iff B.radius_pos).2 (by
        nlinarith only [B.radius_pos]))
    calc
      _ ≤ (ENNReal.ofReal (Real.sqrt (Q ^ Module.finrank Real E)) •
          riemannianVolumeMeasure (I := I) (M := M) (S.base.metric (time : Real))) K :=
        hmeasure K
      _ = ENNReal.ofReal (Real.sqrt (Q ^ Module.finrank Real E)) *
          riemannianVolumeMeasure (I := I) (M := M) (S.base.metric (time : Real)) K := by
        rw [Measure.smul_apply, smul_eq_mul]
      _ ≤ ENNReal.ofReal (Real.sqrt (Q ^ Module.finrank Real E)) * B.volume :=
        mul_le_mul_right (measure_mono hKB) _
  let : NeZero (Module.finrank Real E) := ⟨hdim⟩
  obtain ⟨epsM, hepsM, hmetric⟩ :=
    exists_pos_inner_exp_bounds_on_terminal_ball (E := E) (I := I) (M := M)
  let n : Real := Module.finrank Real E
  let epsF : Real := Real.log Q / (2 * (n ^ 2 + 1))
  have hdenF : 0 < 2 * (n ^ 2 + 1) := by positivity
  have hepsF : 0 < epsF :=
    div_pos (Real.log_pos hQ) hdenF
  let eps₀ : Real := min epsM epsF
  have heps₀ : 0 < eps₀ := lt_min hepsM hepsF
  refine ⟨eps₀, heps₀, ?_⟩
  intro D S hS time B hB hreg hcomplete eps heps heps₀
  dsimp only
  let K : Set M := {y | riemannianEDistOf (I := I)
    (S.base.metric (time : Real)) B.center y ≤ ENNReal.ofReal (B.radius / 32)}
  have hKcompact : IsCompact K := by
    simpa only [K] using
      RiemannianMetricComplete.closedEBall_isCompact
        (I := I) hcomplete B.center (B.radius / 32)
  have hKmeas : MeasurableSet K := hKcompact.isClosed.measurableSet
  have hepsM' : eps ≤ epsM := heps₀.trans (min_le_left epsM epsF)
  have hepsF' : eps ≤ epsF := heps₀.trans (min_le_right epsM epsF)
  have ht : (time : Real) - eps * B.radius ^ 2 ∈
      Set.Icc ((time : Real) - eps * B.radius ^ 2) (time : Real) :=
    ⟨le_rfl, sub_le_self _ (mul_nonneg heps.le (sq_nonneg B.radius))⟩
  have hmetric' := hmetric hS B hB hreg hcomplete eps heps hepsM'
    ((time : Real) - eps * B.radius ^ 2) ht
  have harg : 2 * n ^ 2 * eps ≤ Real.log Q := by
    have hcore : eps * (2 * (n ^ 2 + 1)) ≤ Real.log Q := by
      apply (le_div_iff₀ hdenF).mp
      simpa only [epsF] using hepsF'
    nlinarith [sq_nonneg n, heps.le]
  have hexp : Real.exp (2 * n ^ 2 * eps) ≤ Q := by
    calc
      Real.exp (2 * n ^ 2 * eps) ≤ Real.exp (Real.log Q) :=
        Real.exp_le_exp.mpr harg
      _ = Q := Real.exp_log (zero_lt_one.trans hQ)
  have hcomp : ∀ x ∈ K, ∀ v : TangentSpace I x,
      (S.base.metric ((time : Real) - eps * B.radius ^ 2)).inner x v v ≤
        Q * (S.base.metric (time : Real)).inner x v v := by
    intro x hx v
    have hx' : riemannianEDistOf (I := I) (S.base.metric (time : Real))
        B.center x ≤ ENNReal.ofReal (B.radius / 32) := by
      simpa only [K, Set.mem_ofPred_eq] using hx
    exact (hmetric' x hx' v).2.trans
      (mul_le_mul_of_nonneg_right hexp
        (by
          by_cases hv : v = 0
          · subst v
            simp
          · exact ((S.base.metric (time : Real)).pos x v hv).le))
  have hmeasure := volumeMeasure_restrict_le (I := I) (M := M)
    (S.base.metric (time : Real))
    (S.base.metric ((time : Real) - eps * B.radius ^ 2))
    (Q := Q) (zero_lt_one.trans hQ) hKmeas hcomp
  have hKmeasure := Measure.le_iff.mp hmeasure K hKmeas
  rw [Measure.restrict_apply hKmeas, Measure.smul_apply,
    Measure.restrict_apply hKmeas, smul_eq_mul, inter_self] at hKmeasure
  have hKB : K ⊆ B.set := by
    intro x hx
    change riemannianEDistOf (I := I) (S.base.metric (time : Real))
      B.center x < ENNReal.ofReal B.radius
    have hx' : riemannianEDistOf (I := I) (S.base.metric (time : Real))
        B.center x ≤ ENNReal.ofReal (B.radius / 32) := by
      simpa only [K, Set.mem_ofPred_eq] using hx
    exact hx'.trans_lt ((ENNReal.ofReal_lt_ofReal_iff B.radius_pos).2 (by
      nlinarith only [B.radius_pos]))
  calc
    riemannianVolumeMeasure (I := I) (M := M)
        (S.base.metric ((time : Real) - eps * B.radius ^ 2)) K ≤
      ENNReal.ofReal (Real.sqrt (Q ^ Module.finrank Real E)) *
        riemannianVolumeMeasure (I := I) (M := M)
          (S.base.metric (time : Real)) K := hKmeasure
    _ ≤ ENNReal.ofReal (Real.sqrt (Q ^ Module.finrank Real E)) *
        riemannianVolumeMeasure (I := I) (M := M)
          (S.base.metric (time : Real)) B.set := by
      simpa only [mul_comm] using
        mul_le_mul_right (measure_mono hKB)
          (ENNReal.ofReal
            (Real.sqrt (Q ^ Module.finrank Real E)))
    _ = ENNReal.ofReal
          (Real.sqrt (Q ^ Module.finrank Real E)) * B.volume := rfl

end DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall
