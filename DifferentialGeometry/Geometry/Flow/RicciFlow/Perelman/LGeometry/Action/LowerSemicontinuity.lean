import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.ChartTimeH1
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.Partition
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Chart.KineticEnergy
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.ScalarCompactness
import DifferentialGeometry.Geometry.Operator.MetricFamilyGramWeak

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Filter Function MeasureTheory Set
open scoped ContDiff Manifold Topology

open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Geometry.Curvature

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]
variable {D : RealTimeInterval}

private theorem liminf_add_tendsto
    {q r : ℕ → ℝ} {q₀ r₀ : ℝ}
    (hq : q₀ ≤ liminf q atTop)
    (hq_lo : IsBoundedUnder (· ≥ ·) atTop q)
    (hq_hi : IsBoundedUnder (· ≤ ·) atTop q)
    (hr : Tendsto r atTop (nhds r₀)) :
    q₀ + r₀ ≤ liminf (fun n ↦ q n + r n) atTop := by
  calc
    q₀ + r₀ ≤ liminf q atTop + r₀ := add_le_add_left hq r₀
    _ = liminf q atTop + liminf r atTop := by rw [hr.liminf_eq]
    _ ≤ liminf (fun n ↦ q n + r n) atTop := by
      with_unfolding_all
        exact le_liminf_add hq_lo hq_hi
          hr.isBoundedUnder_ge hr.isCoboundedUnder_ge

private theorem sum_liminf_le
    {ι : Type*} (s : Finset ι) (q : ι → ℕ → ℝ)
    (hlo : ∀ i ∈ s, IsBoundedUnder (· ≥ ·) atTop (q i))
    (hhi : ∀ i ∈ s, IsBoundedUnder (· ≤ ·) atTop (q i)) :
    (∑ i ∈ s, liminf (q i) atTop) ≤
      liminf (∑ i ∈ s, q i) atTop := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      change 0 ≤ liminf (fun _ : ℕ ↦ (0 : ℝ)) atTop
      rw [liminf_const]
  | @insert i s hi ih =>
      have hi_lo := hlo i (Finset.mem_insert_self i s)
      have hi_hi := hhi i (Finset.mem_insert_self i s)
      have hs_lo : ∀ j ∈ s, IsBoundedUnder (· ≥ ·) atTop (q j) :=
        fun j hj ↦ hlo j (Finset.mem_insert_of_mem hj)
      have hs_hi : ∀ j ∈ s, IsBoundedUnder (· ≤ ·) atTop (q j) :=
        fun j hj ↦ hhi j (Finset.mem_insert_of_mem hj)
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      exact (add_le_add_right (ih hs_lo hs_hi) _).trans
        (le_liminf_add hi_lo hi_hi
          (isBoundedUnder_ge_sum s hs_lo)
          (isBoundedUnder_le_sum s hs_hi).isCoboundedUnder_ge)

theorem lKinetic_liminf
    (S : SolutionOn (I := I) (M := M) D)
    (hS : MetricFamilySmoothOn (I := I) (M := M) D S.family.metric)
    (T a b : Real) (hab : a ≤ b)
    (p : M) (alpha : ℕ → Real → M)
    (u : ℕ → timeH1 E (b - a))
    (hsrc : ∀ n, MapsTo (alpha n) (Icc a b) (chartAt H p).source)
    (hrep : ∀ n, EqOn (u n).toFun
      (fun r ↦ extChartAt I p (alpha n (a + r))) (Icc (0 : Real) (b - a)))
    (hdiff : ∀ n, ∀ᵐ r ∂timeMeasure (b - a),
      MDifferentiableAt (modelWithCornersSelf Real Real) I (alpha n) (a + r))
    (uLim : timeH1 E (b - a)) {K : Set E} (hKc : IsCompact K)
    (hKchart : K ⊆ interior (extChartAt I p).target)
    (huK : ∀ n (r : Icc (0 : Real) (b - a)),
      (u n).toFun r.1 ∈ K)
    (huLimK : ∀ r : Icc (0 : Real) (b - a),
      uLim.toFun r.1 ∈ K)
    (hu : TendstoUniformly
      (fun n (r : Icc (0 : Real) (b - a)) ↦ (u n).toFun r.1)
      (fun r ↦ uLim.toFun r.1) atTop)
    (hdu : ∀ z : timeL2 E (b - a), Tendsto
      (fun n ↦ inner Real (u n).deriv z) atTop
      (nhds (inner Real uLim.deriv z)))
    (hreg : ∀ s ∈ Icc a b, T - s ^ 2 ∈ D.regular) :
    (∫ r in (0 : Real)..b - a, (1 / 2 : Real) * inner Real
      (chartGramOp (I := I) S.family p
        (T - (a + r) ^ 2, uLim.toFun r) (uLim.deriv r))
      (uLim.deriv r)) ≤
      liminf (fun n ↦ ∫ s in a..b, (1 / 2 : Real) *
        (S.base.metric (T - s ^ 2)).inner (alpha n s)
          (lVelocity (I := I) (alpha n) s) (lVelocity (I := I) (alpha n) s)) atTop := by
  have hba : 0 ≤ b - a := sub_nonneg.mpr hab
  have hτc : ContinuousOn (fun r : Real ↦ T - (a + r) ^ 2)
      (Icc (0 : Real) (b - a)) :=
    (continuous_const.sub ((continuous_const.add continuous_id).pow 2)).continuousOn
  have hτreg : MapsTo (fun r : Real ↦ T - (a + r) ^ 2)
      (Icc (0 : Real) (b - a)) D.regular := by
    intro r hr
    exact hreg (a + r) ⟨le_add_of_nonneg_right hr.1, by linarith [hr.2]⟩
  have hlim := chartKin_liminf (I := I) hS p hba
    (fun r : Real ↦ T - (a + r) ^ 2) hτc hτreg hKc hKchart
    u uLim huK huLimK hu hdu
  have hseq :
      (fun n ↦ ∫ r in (0 : Real)..b - a, (1 / 2 : Real) * inner Real
        (chartGramOp (I := I) S.family p
          (T - (a + r) ^ 2, (u n).toFun r) ((u n).deriv r))
        ((u n).deriv r)) =
      (fun n ↦ ∫ s in a..b, (1 / 2 : Real) *
        (S.base.metric (T - s ^ 2)).inner (alpha n s)
          (lVelocity (I := I) (alpha n) s) (lVelocity (I := I) (alpha n) s)) := by
    funext n
    simpa only [smul_apply, real_inner_smul_left] using
      (lKinetic_eq_chart_integral S T (alpha n) p a b hab (u n)
        (hsrc n) (hrep n) (hdiff n)).symm
  rw [hseq] at hlim
  exact hlim

variable {N : Type u} [UniformSpace N] [ChartedSpace H N]
  [IsManifold I ∞ N] [CompactSpace N]

omit [CompactSpace N] in
theorem lRegAction_lim_cpt
    [I.Boundaryless]
    (S : SolutionOn (I := I) (M := N) D)
    (hMet : MetricFamilySmoothOn (I := I) (M := N) D S.family.metric)
    (hSc : ScalarSTContOn (I := I) (M := N) S)
    (T a b : Real) (hab : a ≤ b)
    (p : N) (alpha : ℕ → Real → N)
    (u : ℕ → timeH1 E (b - a))
    (hsrc : ∀ n, MapsTo (alpha n) (Icc a b) (chartAt H p).source)
    (hrep : ∀ n, EqOn (u n).toFun
      (fun r ↦ extChartAt I p (alpha n (a + r))) (Icc (0 : Real) (b - a)))
    (hdiff : ∀ n, ∀ᵐ r ∂timeMeasure (b - a),
      MDifferentiableAt (modelWithCornersSelf Real Real) I (alpha n) (a + r))
    (alphaLim : Real → N) (uLim : timeH1 E (b - a))
    (Q : Set N) (hQ : IsCompact Q)
    (hval : ∀ n s, s ∈ Icc a b → alpha n s ∈ Q)
    {K : Set E} (hKc : IsCompact K)
    (hKchart : K ⊆ interior (extChartAt I p).target)
    (huK : ∀ n (r : Icc (0 : Real) (b - a)), (u n).toFun r.1 ∈ K)
    (huLimK : ∀ r : Icc (0 : Real) (b - a), uLim.toFun r.1 ∈ K)
    (hu : TendstoUniformly
      (fun n (r : Icc (0 : Real) (b - a)) ↦ (u n).toFun r.1)
      (fun r ↦ uLim.toFun r.1) atTop)
    (hdu : ∀ z : timeL2 E (b - a), Tendsto
      (fun n ↦ inner Real (u n).deriv z) atTop
      (nhds (inner Real uLim.deriv z)))
    (halpha : TendstoUniformly
      (fun n (s : Icc a b) ↦ alpha n s.1)
      (fun s ↦ alphaLim s.1) atTop)
    (hact : IsBoundedUnder (· ≤ ·) atTop
      (fun n ↦ lRegAction S T (alpha n) a b))
    (hreg : ∀ s ∈ Icc a b, T - s ^ 2 ∈ D.regular) :
    (∫ r in (0 : Real)..b - a, (1 / 2 : Real) * inner Real
        (chartGramOp (I := I) S.family p
          (T - (a + r) ^ 2, uLim.toFun r) (uLim.deriv r))
        (uLim.deriv r)) +
      (∫ s in a..b, 2 * s ^ 2 * S.scalar (T - s ^ 2) (alphaLim s)) ≤
        liminf (fun n ↦ lRegAction S T (alpha n) a b) atTop := by
  let kin : ℕ → Real := fun n ↦ ∫ s in a..b, (1 / 2 : Real) *
    (S.base.metric (T - s ^ 2)).inner (alpha n s)
      (lVelocity (I := I) (alpha n) s) (lVelocity (I := I) (alpha n) s)
  let kinLim : Real := ∫ r in (0 : Real)..b - a, (1 / 2 : Real) * inner Real
    (chartGramOp (I := I) S.family p
      (T - (a + r) ^ 2, uLim.toFun r) (uLim.deriv r)) (uLim.deriv r)
  let pot : ℕ → Real := fun n ↦
    ∫ s in a..b, 2 * s ^ 2 * S.scalar (T - s ^ 2) (alpha n s)
  let potLim : Real :=
    ∫ s in a..b, 2 * s ^ 2 * S.scalar (T - s ^ 2) (alphaLim s)
  change kinLim + potLim ≤
    liminf (fun n ↦ lRegAction S T (alpha n) a b) atTop
  have hkin : kinLim ≤ liminf kin atTop := by
    exact lKinetic_liminf S hMet T a b hab p alpha u hsrc hrep hdiff
      uLim hKc hKchart huK huLimK hu hdu hreg
  have hcont (n : ℕ) : ContinuousOn (alpha n) (Icc a b) :=
    curve_cont_local I p (alpha n) (u n) hab (hsrc n) (hrep n)
  have hcarrier : ∀ s ∈ Icc a b, T - s ^ 2 ∈ D.carrier :=
    fun s hs ↦ D.regular_subset (hreg s hs)
  have hpot : Tendsto pot atTop (nhds potLim) := by
    exact lScalar_tendsto_cpt (I := I) S hSc T a b hab hcarrier Q hQ
      alpha alphaLim hcont hval halpha
  have hkinInt (n : ℕ) : IntervalIntegrable
      (fun s ↦ (1 / 2 : Real) *
        (S.base.metric (T - s ^ 2)).inner (alpha n s)
          (lVelocity (I := I) (alpha n) s)
          (lVelocity (I := I) (alpha n) s)) volume a b :=
    intervalIntegrable_lKinetic_of_chartH1 S hMet T (alpha n) p a b hab (u n)
      (hsrc n) (hrep n) (hdiff n) hreg
  have hpotInt (n : ℕ) : IntervalIntegrable
      (fun s ↦ 2 * s ^ 2 * S.scalar (T - s ^ 2) (alpha n s)) volume a b :=
    lScalar_int (I := I) S hSc T a b (alpha n) (by
      simpa only [uIcc_of_le hab] using hcarrier) (by
      simpa only [uIcc_of_le hab] using hcont n)
  have hsplit (n : ℕ) :
      lRegAction S T (alpha n) a b = kin n + pot n := by
    simpa only [lRegAction, lRegLag, kin, pot] using
      intervalIntegral.integral_add (hkinInt n) (hpotInt n)
  have hkin_nonneg (n : ℕ) : 0 ≤ kin n := by
    change 0 ≤ ∫ s in a..b, (1 / 2 : Real) *
      (S.base.metric (T - s ^ 2)).inner (alpha n s)
        (lVelocity (I := I) (alpha n) s) (lVelocity (I := I) (alpha n) s)
    rw [lKinetic_eq_chart_integral S T (alpha n) p a b hab (u n)
      (hsrc n) (hrep n) (hdiff n)]
    apply intervalIntegral.integral_nonneg (sub_nonneg.mpr hab)
    intro r _hr
    rw [smul_apply, real_inner_smul_left]
    exact mul_nonneg (by norm_num)
      (chartGramOp_nonneg (I := I) S.family p
        (T - (a + r) ^ 2, (u n).toFun r) ((u n).deriv r))
  have hkin_lo : IsBoundedUnder (· ≥ ·) atTop kin :=
    isBoundedUnder_of_eventually_ge (Eventually.of_forall hkin_nonneg)
  have hkin_hi : IsBoundedUnder (· ≤ ·) atTop kin := by
    rcases hact with ⟨A, hA⟩
    change ∀ᶠ n in atTop, lRegAction S T (alpha n) a b ≤ A at hA
    rcases hpot.isBoundedUnder_ge with ⟨B, hB⟩
    change ∀ᶠ n in atTop, pot n ≥ B at hB
    refine ⟨A - B, ?_⟩
    change ∀ᶠ n in atTop, kin n ≤ A - B
    filter_upwards [hA, hB] with n hn hpn
    rw [hsplit n] at hn
    linarith
  have hsum := liminf_add_tendsto hkin hkin_lo hkin_hi hpot
  have hseq : (fun n ↦ kin n + pot n) =
      (fun n ↦ lRegAction S T (alpha n) a b) := by
    funext n
    exact (hsplit n).symm
  rw [hseq] at hsum
  exact hsum

theorem lRegAction_liminf
    [I.Boundaryless]
    (S : SolutionOn (I := I) (M := N) D)
    (hMet : MetricFamilySmoothOn (I := I) (M := N) D S.family.metric)
    (hSc : ScalarSTContOn (I := I) (M := N) S)
    (T a b : Real) (hab : a ≤ b)
    (p : N) (alpha : ℕ → Real → N)
    (u : ℕ → timeH1 E (b - a))
    (hsrc : ∀ n, MapsTo (alpha n) (Icc a b) (chartAt H p).source)
    (hrep : ∀ n, EqOn (u n).toFun
      (fun r ↦ extChartAt I p (alpha n (a + r))) (Icc (0 : Real) (b - a)))
    (hdiff : ∀ n, ∀ᵐ r ∂timeMeasure (b - a),
      MDifferentiableAt (modelWithCornersSelf Real Real) I (alpha n) (a + r))
    (alphaLim : Real → N) (uLim : timeH1 E (b - a))
    {K : Set E} (hKc : IsCompact K)
    (hKchart : K ⊆ interior (extChartAt I p).target)
    (huK : ∀ n (r : Icc (0 : Real) (b - a)), (u n).toFun r.1 ∈ K)
    (huLimK : ∀ r : Icc (0 : Real) (b - a), uLim.toFun r.1 ∈ K)
    (hu : TendstoUniformly
      (fun n (r : Icc (0 : Real) (b - a)) ↦ (u n).toFun r.1)
      (fun r ↦ uLim.toFun r.1) atTop)
    (hdu : ∀ z : timeL2 E (b - a), Tendsto
      (fun n ↦ inner Real (u n).deriv z) atTop
      (nhds (inner Real uLim.deriv z)))
    (halpha : TendstoUniformly
      (fun n (s : Icc a b) ↦ alpha n s.1)
      (fun s ↦ alphaLim s.1) atTop)
    (hact : IsBoundedUnder (· ≤ ·) atTop
      (fun n ↦ lRegAction S T (alpha n) a b))
    (hreg : ∀ s ∈ Icc a b, T - s ^ 2 ∈ D.regular) :
    (∫ r in (0 : Real)..b - a, (1 / 2 : Real) * inner Real
        (chartGramOp (I := I) S.family p
          (T - (a + r) ^ 2, uLim.toFun r) (uLim.deriv r))
        (uLim.deriv r)) +
      (∫ s in a..b, 2 * s ^ 2 * S.scalar (T - s ^ 2) (alphaLim s)) ≤
        liminf (fun n ↦ lRegAction S T (alpha n) a b) atTop := by
  exact lRegAction_lim_cpt S hMet hSc T a b hab p alpha u hsrc hrep hdiff
    alphaLim uLim Set.univ isCompact_univ (fun _ _ _ ↦ Set.mem_univ _)
    hKc hKchart huK huLimK hu hdu halpha hact hreg

omit [CompactSpace N] in
theorem lRegAction_chart
    [I.Boundaryless]
    (S : SolutionOn (I := I) (M := N) D)
    (hMet : MetricFamilySmoothOn (I := I) (M := N) D S.family.metric)
    (hSc : ScalarSTContOn (I := I) (M := N) S)
    (T a b : Real) {m : Nat} (t : Fin (m + 1) → Real)
    (htmono : Monotone t) (ht0 : t 0 = a)
    (htlast : t (Fin.last m) = b)
    (p : Fin m → N) (gamma : Real → N)
    (u : (i : Fin m) → timeH1 E (partitionIntervalLength t i))
    (hsrc : ∀ i, MapsTo gamma
      (Icc (t i.castSucc) (t i.succ)) (chartAt H (p i)).source)
    (hrep : ∀ i, EqOn (u i).toFun
      (fun r ↦ extChartAt I (p i) (gamma (t i.castSucc + r)))
      (Icc (0 : Real) (partitionIntervalLength t i)))
    (hreg : ∀ s ∈ Icc a b, T - s ^ 2 ∈ D.regular) :
    lRegAction S T gamma a b =
      ∑ i : Fin m, (
        (∫ r in (0 : Real)..partitionIntervalLength t i, (1 / 2 : Real) * inner Real
          (chartGramOp (I := I) S.family (p i)
            (T - (t i.castSucc + r) ^ 2, (u i).toFun r) ((u i).deriv r))
          ((u i).deriv r)) +
        (∫ s in (t i.castSucc)..(t i.succ),
          2 * s ^ 2 * S.scalar (T - s ^ 2) (gamma s))) := by
  classical
  have hab : a ≤ b := by
    rw [← ht0, ← htlast]
    exact htmono (Fin.zero_le _)
  have hleft (i : Fin m) : a ≤ t i.castSucc := by
    rw [← ht0]
    exact htmono (Fin.zero_le _)
  have hseg (i : Fin m) : t i.castSucc ≤ t i.succ :=
    htmono Fin.castSucc_lt_succ.le
  have hright (i : Fin m) : t i.succ ≤ b := by
    rw [← htlast]
    exact htmono (Fin.le_last _)
  have hreg_i (i : Fin m) (s : Real) (hs : s ∈ Icc (t i.castSucc) (t i.succ)) :
      T - s ^ 2 ∈ D.regular :=
    hreg s ⟨(hleft i).trans hs.1, hs.2.trans (hright i)⟩
  have hcarrier_i (i : Fin m) :
      ∀ s ∈ uIcc (t i.castSucc) (t i.succ), T - s ^ 2 ∈ D.carrier := by
    intro s hs
    apply D.regular_subset
    apply hreg_i i s
    simpa only [uIcc_of_le (hseg i)] using hs
  have hdiff (i : Fin m) : ∀ᵐ r ∂timeMeasure (partitionIntervalLength t i),
      MDifferentiableAt (modelWithCornersSelf Real Real) I gamma
        (t i.castSucc + r) := by
    exact curve_mdiff_local I (p i) gamma (u i) (hseg i) (hsrc i) (hrep i)
  have hcont (i : Fin m) :
      ContinuousOn gamma (Icc (t i.castSucc) (t i.succ)) :=
    curve_cont_local I (p i) gamma (u i) (hseg i) (hsrc i) (hrep i)
  have hkinInt (i : Fin m) : IntervalIntegrable
      (fun s ↦ (1 / 2 : Real) *
        (S.base.metric (T - s ^ 2)).inner (gamma s)
          (lVelocity (I := I) gamma s) (lVelocity (I := I) gamma s))
      volume (t i.castSucc) (t i.succ) :=
    intervalIntegrable_lKinetic_of_chartH1 S hMet T gamma (p i) (t i.castSucc) (t i.succ)
      (hseg i) (u i) (hsrc i) (hrep i) (hdiff i) (hreg_i i)
  have hpotInt (i : Fin m) : IntervalIntegrable
      (fun s ↦ 2 * s ^ 2 * S.scalar (T - s ^ 2) (gamma s))
      volume (t i.castSucc) (t i.succ) :=
    lScalar_int (I := I) S hSc T (t i.castSucc) (t i.succ) gamma
      (hcarrier_i i) (by
        simpa only [uIcc_of_le (hseg i)] using hcont i)
  let kin : Fin m → Real := fun i ↦
    ∫ s in t i.castSucc..t i.succ, (1 / 2 : Real) *
      (S.base.metric (T - s ^ 2)).inner (gamma s)
        (lVelocity (I := I) gamma s) (lVelocity (I := I) gamma s)
  let pot : Fin m → Real := fun i ↦
    ∫ s in t i.castSucc..t i.succ,
      2 * s ^ 2 * S.scalar (T - s ^ 2) (gamma s)
  have hsplit (i : Fin m) :
      lRegAction S T gamma (t i.castSucc) (t i.succ) = kin i + pot i := by
    simpa only [lRegAction, lRegLag, kin, pot] using
      intervalIntegral.integral_add (hkinInt i) (hpotInt i)
  have hkinChart (i : Fin m) : kin i =
      ∫ r in (0 : Real)..partitionIntervalLength t i, (1 / 2 : Real) * inner Real
        (chartGramOp (I := I) S.family (p i)
          (T - (t i.castSucc + r) ^ 2, (u i).toFun r) ((u i).deriv r))
        ((u i).deriv r) := by
    simpa only [kin, partitionIntervalLength, smul_apply, real_inner_smul_left] using
      lKinetic_eq_chart_integral S T gamma (p i) (t i.castSucc) (t i.succ)
        (hseg i) (u i) (hsrc i) (hrep i) (hdiff i)
  have hLag (i : Fin m) : IntervalIntegrable (lRegLag S T gamma) volume
      (t i.castSucc) (t i.succ) := by
    with_unfolding_all exact (hkinInt i).add (hpotInt i)
  let tNat : Nat → Real := fun k ↦
    if hk : k < m + 1 then t ⟨k, hk⟩ else b
  have hsum : (∑ i : Fin m,
      lRegAction S T gamma (t i.castSucc) (t i.succ)) =
      lRegAction S T gamma a b := by
    calc
      (∑ i : Fin m, lRegAction S T gamma (t i.castSucc) (t i.succ)) =
          ∑ k ∈ Finset.range m,
            lRegAction S T gamma (tNat k) (tNat (k + 1)) := by
        rw [Finset.sum_fin_eq_sum_range]
        apply Finset.sum_congr rfl
        intro k hk
        have hk' : k < m := Finset.mem_range.mp hk
        have hk0 : k ≤ m := Nat.le_of_lt hk'
        have hk1 : k + 1 ≤ m := Nat.succ_le_of_lt hk'
        rw [dif_pos hk']
        simp only [tNat, Nat.lt_succ_iff, dif_pos hk0, dif_pos hk1]
        congr 2
      _ = lRegAction S T gamma (tNat 0) (tNat m) :=
        lRegAction_sum S T gamma (fun k hk ↦ by
          have hk' : k < m := hk
          simp only [tNat, dif_pos (Nat.lt_trans hk' (Nat.lt_succ_self m)),
            dif_pos (Nat.succ_lt_succ hk')]
          with_unfolding_all exact hLag ⟨k, hk'⟩)
      _ = lRegAction S T gamma a b := by
        simp only [tNat, dif_pos (Nat.succ_pos m),
          dif_pos (Nat.lt_succ_self m)]
        change lRegAction S T gamma (t 0) (t (Fin.last m)) =
          lRegAction S T gamma a b
        rw [ht0, htlast]
  rw [← hsum]
  apply Finset.sum_congr rfl
  intro i _
  rw [hsplit i, hkinChart i]

omit [CompactSpace N] in
theorem lRegAction_fin_cpt
    [I.Boundaryless]
    (S : SolutionOn (I := I) (M := N) D)
    (hMet : MetricFamilySmoothOn (I := I) (M := N) D S.family.metric)
    (hSc : ScalarSTContOn (I := I) (M := N) S)
    (T a b : Real) {m : Nat} (t : Fin (m + 1) → Real)
    (htmono : Monotone t) (ht0 : t 0 = a)
    (htlast : t (Fin.last m) = b)
    (p : Fin m → N) (alpha : Nat → Real → N) (gamma : Real → N)
    (Q : Set N) (hQ : IsCompact Q)
    (hval : ∀ n s, s ∈ Icc a b → alpha n s ∈ Q)
    (u : (i : Fin m) → Nat → timeH1 E (partitionIntervalLength t i))
    (hsrc : ∀ i n, MapsTo (alpha n)
      (Icc (t i.castSucc) (t i.succ)) (chartAt H (p i)).source)
    (hrep : ∀ i n, EqOn (u i n).toFun
      (fun r ↦ extChartAt I (p i) (alpha n (t i.castSucc + r)))
      (Icc (0 : Real) (partitionIntervalLength t i)))
    (hdiff : ∀ i n, ∀ᵐ r ∂timeMeasure (partitionIntervalLength t i),
      MDifferentiableAt (modelWithCornersSelf Real Real) I
        (alpha n) (t i.castSucc + r))
    (K : Fin m → Set E) (hKc : ∀ i, IsCompact (K i))
    (hKchart : ∀ i, K i ⊆ interior (extChartAt I (p i)).target)
    (huK : ∀ i n (r : Icc (0 : Real) (partitionIntervalLength t i)),
      (u i n).toFun r.1 ∈ K i)
    (uLim : (i : Fin m) → timeH1 E (partitionIntervalLength t i))
    (hu : ∀ i, TendstoUniformly
      (fun n (r : Icc (0 : Real) (partitionIntervalLength t i)) ↦ (u i n).toFun r.1)
      (fun r ↦ (uLim i).toFun r.1) atTop)
    (hdu : ∀ i (z : timeL2 E (partitionIntervalLength t i)), Tendsto
      (fun n ↦ inner Real (u i n).deriv z) atTop
      (nhds (inner Real (uLim i).deriv z)))
    (halpha : TendstoUniformly
      (fun n (s : Icc a b) ↦ alpha n s.1)
      (fun s ↦ gamma s.1) atTop)
    (hact : IsBoundedUnder (· ≤ ·) atTop
      (fun n ↦ lRegAction S T (alpha n) a b))
    (hreg : ∀ s ∈ Icc a b, T - s ^ 2 ∈ D.regular) :
    (∑ i : Fin m, (
      (∫ r in (0 : Real)..partitionIntervalLength t i, (1 / 2 : Real) * inner Real
        (chartGramOp (I := I) S.family (p i)
          (T - (t i.castSucc + r) ^ 2, (uLim i).toFun r)
          ((uLim i).deriv r))
        ((uLim i).deriv r)) +
      (∫ s in (t i.castSucc)..(t i.succ),
        2 * s ^ 2 * S.scalar (T - s ^ 2) (gamma s)))) ≤
      liminf (fun n ↦ lRegAction S T (alpha n) a b) atTop := by
  classical
  have hab : a ≤ b := by
    rw [← ht0, ← htlast]
    exact htmono (Fin.zero_le _)
  have hleft (i : Fin m) : a ≤ t i.castSucc := by
    rw [← ht0]
    exact htmono (Fin.zero_le _)
  have hseg (i : Fin m) : t i.castSucc ≤ t i.succ :=
    htmono Fin.castSucc_lt_succ.le
  have hright (i : Fin m) : t i.succ ≤ b := by
    rw [← htlast]
    exact htmono (Fin.le_last _)
  have hreg_i (i : Fin m) (s : Real) (hs : s ∈ Icc (t i.castSucc) (t i.succ)) :
      T - s ^ 2 ∈ D.regular :=
    hreg s ⟨(hleft i).trans hs.1, hs.2.trans (hright i)⟩
  have hcarrier : ∀ s ∈ uIcc a b, T - s ^ 2 ∈ D.carrier := by
    intro s hs
    apply D.regular_subset
    apply hreg s
    simpa only [uIcc_of_le hab] using hs
  have hcarrier_i (i : Fin m) :
      ∀ s ∈ uIcc (t i.castSucc) (t i.succ), T - s ^ 2 ∈ D.carrier := by
    intro s hs
    apply D.regular_subset
    apply hreg_i i s
    simpa only [uIcc_of_le (hseg i)] using hs
  have hcont (i : Fin m) (n : Nat) :
      ContinuousOn (alpha n) (Icc (t i.castSucc) (t i.succ)) :=
    curve_cont_local I (p i) (alpha n) (u i n) (hseg i) (hsrc i n) (hrep i n)
  have hkinInt (i : Fin m) (n : Nat) : IntervalIntegrable
      (fun s ↦ (1 / 2 : Real) *
        (S.base.metric (T - s ^ 2)).inner (alpha n s)
          (lVelocity (I := I) (alpha n) s) (lVelocity (I := I) (alpha n) s))
      volume (t i.castSucc) (t i.succ) :=
    intervalIntegrable_lKinetic_of_chartH1 S hMet T (alpha n) (p i) (t i.castSucc) (t i.succ)
      (hseg i) (u i n) (hsrc i n) (hrep i n) (hdiff i n) (hreg_i i)
  have hpotInt (i : Fin m) (n : Nat) : IntervalIntegrable
      (fun s ↦ 2 * s ^ 2 * S.scalar (T - s ^ 2) (alpha n s))
      volume (t i.castSucc) (t i.succ) :=
    lScalar_int (I := I) S hSc T (t i.castSucc) (t i.succ) (alpha n)
      (hcarrier_i i) (by
        simpa only [uIcc_of_le (hseg i)] using hcont i n)
  have hLag (i : Fin m) (n : Nat) : IntervalIntegrable
      (lRegLag S T (alpha n)) volume (t i.castSucc) (t i.succ) := by
    with_unfolding_all exact (hkinInt i n).add (hpotInt i n)
  let q : Fin m → Nat → Real := fun i n ↦
    lRegAction S T (alpha n) (t i.castSucc) (t i.succ)
  let kin : Fin m → Nat → Real := fun i n ↦
    ∫ s in t i.castSucc..t i.succ, (1 / 2 : Real) *
      (S.base.metric (T - s ^ 2)).inner (alpha n s)
        (lVelocity (I := I) (alpha n) s) (lVelocity (I := I) (alpha n) s)
  let pot : Fin m → Nat → Real := fun i n ↦
    ∫ s in t i.castSucc..t i.succ,
      2 * s ^ 2 * S.scalar (T - s ^ 2) (alpha n s)
  have hsplit (i : Fin m) (n : Nat) : q i n = kin i n + pot i n := by
    simpa only [q, kin, pot, lRegAction, lRegLag] using
      intervalIntegral.integral_add (hkinInt i n) (hpotInt i n)
  have hkinNonneg (i : Fin m) (n : Nat) : 0 ≤ kin i n := by
    change 0 ≤ ∫ s in t i.castSucc..t i.succ, (1 / 2 : Real) *
      (S.base.metric (T - s ^ 2)).inner (alpha n s)
        (lVelocity (I := I) (alpha n) s) (lVelocity (I := I) (alpha n) s)
    rw [lKinetic_eq_chart_integral S T (alpha n) (p i) (t i.castSucc) (t i.succ)
      (hseg i) (u i n) (hsrc i n) (hrep i n) (hdiff i n)]
    apply intervalIntegral.integral_nonneg (sub_nonneg.mpr (hseg i))
    intro r _hr
    rw [smul_apply, real_inner_smul_left]
    exact mul_nonneg (by norm_num)
      (chartGramOp_nonneg (I := I) S.family (p i)
        (T - (t i.castSucc + r) ^ 2, (u i n).toFun r) ((u i n).deriv r))
  obtain ⟨C, hC⟩ := lScalar_lower_cpt (I := I) S hSc T a b hcarrier Q hQ
  have hpotLower (i : Fin m) (n : Nat) : C * partitionIntervalLength t i ≤ pot i n := by
    have hmono := intervalIntegral.integral_mono_on (hseg i)
      intervalIntegrable_const (hpotInt i n) (fun s hs ↦
        hC s (by
          simpa only [uIcc_of_le hab] using
            ⟨(hleft i).trans hs.1, hs.2.trans (hright i)⟩) (alpha n s)
          (hval n s ⟨(hleft i).trans hs.1, hs.2.trans (hright i)⟩))
    rw [intervalIntegral.integral_const] at hmono
    simpa only [pot, partitionIntervalLength, smul_eq_mul, mul_comm] using hmono
  have hqLower (i : Fin m) (n : Nat) : C * partitionIntervalLength t i ≤ q i n := by
    rw [hsplit]
    linarith [hkinNonneg i n, hpotLower i n]
  let tNat : Nat → Real := fun k ↦
    if hk : k < m + 1 then t ⟨k, hk⟩ else b
  have hsum (n : Nat) : (∑ i : Fin m, q i n) =
      lRegAction S T (alpha n) a b := by
    calc
      (∑ i : Fin m, q i n) =
          ∑ k ∈ Finset.range m,
            lRegAction S T (alpha n) (tNat k) (tNat (k + 1)) := by
        rw [Finset.sum_fin_eq_sum_range]
        simp only [q]
        apply Finset.sum_congr rfl
        intro k hk
        have hk' : k < m := Finset.mem_range.mp hk
        have hk0 : k ≤ m := Nat.le_of_lt hk'
        have hk1 : k + 1 ≤ m := Nat.succ_le_of_lt hk'
        rw [dif_pos hk']
        simp only [tNat, Nat.lt_succ_iff, dif_pos hk0, dif_pos hk1]
        congr 2
      _ = lRegAction S T (alpha n) (tNat 0) (tNat m) :=
        lRegAction_sum S T (alpha n) (fun k hk ↦ by
          have hk' : k < m := hk
          simp only [tNat, dif_pos (Nat.lt_trans hk' (Nat.lt_succ_self m)),
            dif_pos (Nat.succ_lt_succ hk')]
          with_unfolding_all exact hLag ⟨k, hk'⟩ n)
      _ = lRegAction S T (alpha n) a b := by
        simp only [tNat, dif_pos (Nat.succ_pos m),
          dif_pos (Nat.lt_succ_self m)]
        change lRegAction S T (alpha n) (t 0) (t (Fin.last m)) =
          lRegAction S T (alpha n) a b
        rw [ht0, htlast]
  obtain ⟨A, hA⟩ := hact
  change ∀ᶠ n in atTop, lRegAction S T (alpha n) a b ≤ A at hA
  have hqUpper (i : Fin m) : IsBoundedUnder (· ≤ ·) atTop (q i) := by
    refine ⟨A - (∑ j ∈ (Finset.univ.erase i), C * partitionIntervalLength t j), ?_⟩
    change ∀ᶠ n in atTop,
      q i n ≤ A - (∑ j ∈ (Finset.univ.erase i), C * partitionIntervalLength t j)
    filter_upwards [hA] with n hn
    rw [← hsum n] at hn
    have hrest : (∑ j ∈ (Finset.univ.erase i), C * partitionIntervalLength t j) ≤
        ∑ j ∈ (Finset.univ.erase i), q j n :=
      Finset.sum_le_sum fun j hj ↦ hqLower j n
    have hdecomp : q i n + (∑ j ∈ (Finset.univ.erase i), q j n) =
        ∑ j : Fin m, q j n :=
      Finset.add_sum_erase Finset.univ (fun j ↦ q j n) (Finset.mem_univ i)
    linarith
  have huLimK (i : Fin m) (r : Icc (0 : Real) (partitionIntervalLength t i)) :
      (uLim i).toFun r.1 ∈ K i := by
    apply (hKc i).isClosed.mem_of_tendsto ((hu i).tendsto_at r)
    exact Eventually.of_forall fun n ↦ huK i n r
  have hlocal (i : Fin m) :
      (∫ r in (0 : Real)..partitionIntervalLength t i, (1 / 2 : Real) * inner Real
          (chartGramOp (I := I) S.family (p i)
            (T - (t i.castSucc + r) ^ 2, (uLim i).toFun r)
            ((uLim i).deriv r))
          ((uLim i).deriv r)) +
        (∫ s in t i.castSucc..t i.succ,
          2 * s ^ 2 * S.scalar (T - s ^ 2) (gamma s)) ≤
        liminf (q i) atTop := by
    let inc : Icc (t i.castSucc) (t i.succ) → Icc a b := fun s ↦
      ⟨s.1, (hleft i).trans s.2.1, s.2.2.trans (hright i)⟩
    have halpha_i := halpha.comp inc
    apply lRegAction_lim_cpt S hMet hSc T (t i.castSucc) (t i.succ) (hseg i)
      (p i) alpha (u i) (hsrc i) (hrep i) (hdiff i) gamma (uLim i) Q hQ
      (fun n s hs ↦ hval n s
        ⟨(hleft i).trans hs.1, hs.2.trans (hright i)⟩)
      (hKc i) (hKchart i) (huK i) (huLimK i) (hu i) (hdu i)
    · with_unfolding_all exact halpha_i
    · exact hqUpper i
    · exact hreg_i i
  have hlo : ∀ i ∈ (Finset.univ : Finset (Fin m)),
      IsBoundedUnder (· ≥ ·) atTop (q i) := fun i _ ↦
    isBoundedUnder_of_eventually_ge (Eventually.of_forall (hqLower i))
  have hhi : ∀ i ∈ (Finset.univ : Finset (Fin m)),
      IsBoundedUnder (· ≤ ·) atTop (q i) := fun i _ ↦ hqUpper i
  have hsumlim : (∑ i : Fin m, liminf (q i) atTop) ≤
      liminf (fun n ↦ ∑ i : Fin m, q i n) atTop := by
    have hsumfun : (∑ i : Fin m, q i) = fun n ↦ ∑ i : Fin m, q i n := by
      funext n
      simp only [Finset.sum_apply]
    rw [← hsumfun]
    simpa using sum_liminf_le (Finset.univ : Finset (Fin m)) q hlo hhi
  calc
    (∑ i : Fin m, (
      (∫ r in (0 : Real)..partitionIntervalLength t i, (1 / 2 : Real) * inner Real
        (chartGramOp (I := I) S.family (p i)
          (T - (t i.castSucc + r) ^ 2, (uLim i).toFun r)
          ((uLim i).deriv r))
        ((uLim i).deriv r)) +
      (∫ s in (t i.castSucc)..(t i.succ),
        2 * s ^ 2 * S.scalar (T - s ^ 2) (gamma s)))) ≤
        ∑ i : Fin m, liminf (q i) atTop :=
      Finset.sum_le_sum fun i _ ↦ hlocal i
    _ ≤ liminf (fun n ↦ ∑ i : Fin m, q i n) atTop := hsumlim
    _ = liminf (fun n ↦ lRegAction S T (alpha n) a b) atTop := by
      congr 1
      funext n
      exact hsum n

theorem lRegAction_fin_lsc
    [I.Boundaryless]
    (S : SolutionOn (I := I) (M := N) D)
    (hMet : MetricFamilySmoothOn (I := I) (M := N) D S.family.metric)
    (hSc : ScalarSTContOn (I := I) (M := N) S)
    (T a b : Real) {m : Nat} (t : Fin (m + 1) → Real)
    (htmono : Monotone t) (ht0 : t 0 = a)
    (htlast : t (Fin.last m) = b)
    (p : Fin m → N) (alpha : Nat → Real → N) (gamma : Real → N)
    (u : (i : Fin m) → Nat → timeH1 E (partitionIntervalLength t i))
    (hsrc : ∀ i n, MapsTo (alpha n)
      (Icc (t i.castSucc) (t i.succ)) (chartAt H (p i)).source)
    (hrep : ∀ i n, EqOn (u i n).toFun
      (fun r ↦ extChartAt I (p i) (alpha n (t i.castSucc + r)))
      (Icc (0 : Real) (partitionIntervalLength t i)))
    (hdiff : ∀ i n, ∀ᵐ r ∂timeMeasure (partitionIntervalLength t i),
      MDifferentiableAt (modelWithCornersSelf Real Real) I
        (alpha n) (t i.castSucc + r))
    (K : Fin m → Set E) (hKc : ∀ i, IsCompact (K i))
    (hKchart : ∀ i, K i ⊆ interior (extChartAt I (p i)).target)
    (huK : ∀ i n (r : Icc (0 : Real) (partitionIntervalLength t i)),
      (u i n).toFun r.1 ∈ K i)
    (uLim : (i : Fin m) → timeH1 E (partitionIntervalLength t i))
    (hu : ∀ i, TendstoUniformly
      (fun n (r : Icc (0 : Real) (partitionIntervalLength t i)) ↦ (u i n).toFun r.1)
      (fun r ↦ (uLim i).toFun r.1) atTop)
    (hdu : ∀ i (z : timeL2 E (partitionIntervalLength t i)), Tendsto
      (fun n ↦ inner Real (u i n).deriv z) atTop
      (nhds (inner Real (uLim i).deriv z)))
    (halpha : TendstoUniformly
      (fun n (s : Icc a b) ↦ alpha n s.1)
      (fun s ↦ gamma s.1) atTop)
    (hact : IsBoundedUnder (· ≤ ·) atTop
      (fun n ↦ lRegAction S T (alpha n) a b))
    (hreg : ∀ s ∈ Icc a b, T - s ^ 2 ∈ D.regular) :
    (∑ i : Fin m, (
      (∫ r in (0 : Real)..partitionIntervalLength t i, (1 / 2 : Real) * inner Real
        (chartGramOp (I := I) S.family (p i)
          (T - (t i.castSucc + r) ^ 2, (uLim i).toFun r)
          ((uLim i).deriv r))
        ((uLim i).deriv r)) +
      (∫ s in (t i.castSucc)..(t i.succ),
        2 * s ^ 2 * S.scalar (T - s ^ 2) (gamma s)))) ≤
      liminf (fun n ↦ lRegAction S T (alpha n) a b) atTop := by
  exact lRegAction_fin_cpt S hMet hSc T a b t htmono ht0 htlast p alpha gamma
    Set.univ isCompact_univ (fun _ _ _ ↦ Set.mem_univ _) u hsrc hrep hdiff
    K hKc hKchart huK uLim hu hdu halpha hact hreg

end DifferentialGeometry.PDE.RicciFlow.Perelman
