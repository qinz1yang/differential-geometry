import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.CarrierKineticAction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.ChartPartition.Construction.TwoPieceSplicing
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.Defs
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Chart.KineticEnergy
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Compactness.Scalar

set_option autoImplicit false

noncomputable section

open Bundle Filter Function MeasureTheory Set DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open scoped BigOperators ContDiff Manifold Topology Interval

namespace DifferentialGeometry.PDE.RicciFlow

variable {E H M : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [UniformSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {D : RealTimeInterval}

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private theorem integral_fin_partition
    {m : ℕ} (t : Fin (m + 1) → ℝ) (f : ℝ → ℝ)
    (hint : ∀ i : Fin m, IntervalIntegrable f volume (t i.castSucc) (t i.succ)) :
    IntervalIntegrable f volume (t 0) (t (Fin.last m)) ∧
      (∑ i : Fin m, ∫ s in t i.castSucc..t i.succ, f s) =
        ∫ s in t 0..t (Fin.last m), f s := by
  classical
  let tNat : ℕ → ℝ := fun k ↦ if hk : k < m + 1 then t ⟨k, hk⟩ else t (Fin.last m)
  have hNat (k : ℕ) (hk : k < m) :
      IntervalIntegrable f volume (tNat k) (tNat (k + 1)) := by
    dsimp only [tNat]
    rw [dite_eq_left (Nat.lt_trans hk (Nat.lt_succ_self m)), dite_eq_left (Nat.succ_lt_succ hk)]
    convert hint ⟨k, hk⟩ using 1 <;> rfl
  have hwhole := IntervalIntegrable.trans_iterate hNat
  have hsum := intervalIntegral.sum_integral_adjacent_intervals hNat
  have hends : tNat 0 = t 0 ∧ tNat m = t (Fin.last m) := by
    constructor <;> simp only [tNat, dite_eq_left (Nat.succ_pos m),
      dite_eq_left (Nat.lt_succ_self m)] <;> rfl
  refine ⟨by simpa only [hends.1, hends.2] using hwhole, ?_⟩
  calc
    (∑ i : Fin m, ∫ s in t i.castSucc..t i.succ, f s) =
        ∑ k ∈ Finset.range m, ∫ s in tNat k..tNat (k + 1), f s := by
      rw [Finset.sum_fin_eq_sum_range]
      apply Finset.sum_congr rfl
      intro k hk
      have hk' : k < m := Finset.mem_range.mp hk
      have hk0 : k ≤ m := Nat.le_of_lt hk'
      have hk1 : k + 1 ≤ m := Nat.succ_le_of_lt hk'
      rw [dite_eq_left hk']
      simp only [tNat, Nat.lt_succ_iff, dite_eq_left hk0, dite_eq_left hk1]
      congr 2
    _ = ∫ s in t 0..t (Fin.last m), f s := by
      simpa only [hends.1, hends.2] using hsum

private theorem action_partition_on_carrier
    (S : SolutionOn (I := I) (M := M) D)
    (hMet : MetricFamilySmoothOn (I := I) (M := M) D S.family.metric)
    (hSc : ScalarSTContOn (I := I) (M := M) S)
    (T a b : ℝ) {m : ℕ} (t : Fin (m + 1) → ℝ)
    (htmono : Monotone t) (ht0 : t 0 = a) (htlast : t (Fin.last m) = b)
    (p : Fin m → M) (gamma : ℝ → M)
    (u : (i : Fin m) → timeH1 E (partitionIntervalLength t i))
    (hsrc : ∀ i, MapsTo gamma (Icc (t i.castSucc) (t i.succ))
      (chartAt H (p i)).source)
    (hrep : ∀ i, EqOn (u i).toFun
      (fun r ↦ extChartAt I (p i) (gamma (t i.castSucc + r)))
      (Icc (0 : ℝ) (partitionIntervalLength t i)))
    (hback : ∀ s ∈ Icc a b, T - s ^ 2 ∈ D.carrier) :
    IntervalIntegrable (lRegularizedLagrangian S T gamma) volume a b ∧
      lRegularizedAction S T gamma a b =
        ∑ i : Fin m, lRegularizedAction S T gamma (t i.castSucc) (t i.succ) := by
  have hleft (i : Fin m) : a ≤ t i.castSucc := by
    rw [← ht0]
    exact htmono (Fin.zero_le _)
  have hright (i : Fin m) : t i.succ ≤ b := by
    rw [← htlast]
    exact htmono (Fin.le_last _)
  have hint (i : Fin m) : IntervalIntegrable (lRegularizedLagrangian S T gamma) volume
      (t i.castSucc) (t i.succ) := by
    apply lRegLag_integrable_chart_on_carrier S hMet hSc T
      (t i.castSucc) (t i.succ) (htmono Fin.castSucc_lt_succ.le)
      (p i) gamma (u i) (hsrc i) (hrep i)
    intro s hs
    apply hback s
    exact ⟨(hleft i).trans hs.1, hs.2.trans (hright i)⟩
  obtain ⟨hwhole, hsum⟩ := integral_fin_partition t (lRegularizedLagrangian S T gamma) hint
  refine ⟨by simpa only [ht0, htlast] using hwhole, ?_⟩
  simpa only [lRegularizedAction, ht0, htlast] using hsum.symm

private theorem action_split_chart_on_carrier
    (S : SolutionOn (I := I) (M := M) D)
    (hMet : MetricFamilySmoothOn (I := I) (M := M) D S.family.metric)
    (hSc : ScalarSTContOn (I := I) (M := M) S)
    (T a b : ℝ) (hab : a ≤ b) (p : M) (alpha : ℝ → M)
    (u : timeH1 E (b - a))
    (hsrc : MapsTo alpha (Icc a b) (chartAt H p).source)
    (hrep : EqOn u.toFun (fun r ↦ extChartAt I p (alpha (a + r)))
      (Icc (0 : ℝ) (b - a)))
    (hback : ∀ s ∈ Icc a b, T - s ^ 2 ∈ D.carrier) :
    lRegularizedAction S T alpha a b =
      (∫ r in (0 : ℝ)..b - a, (1 / 2 : ℝ) * inner ℝ
        (chartGramOp S.family p (T - (a + r) ^ 2, u.toFun r) (u.deriv r))
        (u.deriv r)) +
      (∫ s in a..b, 2 * s ^ 2 * S.scalar (T - s ^ 2) (alpha s)) := by
  have hLag := lRegLag_integrable_chart_on_carrier S hMet hSc T a b hab
    p alpha u hsrc hrep hback
  have hPot := lScalar_int (I := I) S hSc T a b alpha
    (by simpa only [uIcc_of_le hab] using hback)
    (by simpa only [uIcc_of_le hab] using curve_cont_local I p alpha u hab hsrc hrep)
  have hKin : IntervalIntegrable (fun s ↦ (1 / 2 : ℝ) *
      (S.base.metric (T - s ^ 2)).inner (alpha s)
        (lVelocity (I := I) alpha s) (lVelocity (I := I) alpha s)) volume a b := by
    simpa only [lRegularizedLagrangian, Pi.sub_apply, add_sub_cancel_right] using hLag.sub hPot
  have hsplit := intervalIntegral.integral_add hKin hPot
  have hcoord := lKinetic_eq_chart_integral S T alpha p a b hab u hsrc hrep
  change lRegularizedAction S T alpha a b = _ at hsplit
  rw [hcoord] at hsplit
  simpa only [smul_apply, real_inner_smul_left] using hsplit

private theorem action_chart_tendsto_on_carrier
    (S : SolutionOn (I := I) (M := M) D)
    (hMet : MetricFamilySmoothOn (I := I) (M := M) D S.family.metric)
    (hSc : ScalarSTContOn (I := I) (M := M) S)
    (T a b : ℝ) (hab : a ≤ b) (p : M)
    (alpha : ℕ → ℝ → M) (gamma : ℝ → M)
    (u : ℕ → timeH1 E (b - a)) (uLim : timeH1 E (b - a))
    (hsrc : ∀ n, MapsTo (alpha n) (Icc a b) (chartAt H p).source)
    (hrep : ∀ n, EqOn (u n).toFun
      (fun r ↦ extChartAt I p (alpha n (a + r))) (Icc (0 : ℝ) (b - a)))
    (hsrcLim : MapsTo gamma (Icc a b) (chartAt H p).source)
    (hrepLim : EqOn uLim.toFun
      (fun r ↦ extChartAt I p (gamma (a + r))) (Icc (0 : ℝ) (b - a)))
    (K : Set E) (hKc : IsCompact K) (hKchart : K ⊆ interior (extChartAt I p).target)
    (huK : ∀ n (r : Icc (0 : ℝ) (b - a)), (u n).toFun r.1 ∈ K)
    (huLimK : ∀ r : Icc (0 : ℝ) (b - a), uLim.toFun r.1 ∈ K)
    (hu : Tendsto u atTop (𝓝 uLim))
    (hunif : TendstoUniformly (fun n (s : Icc a b) ↦ alpha n s.1)
      (fun s ↦ gamma s.1) atTop)
    (hback : ∀ s ∈ Icc a b, T - s ^ 2 ∈ D.carrier) :
    Tendsto (fun n ↦ lRegularizedAction S T (alpha n) a b) atTop
      (𝓝 (lRegularizedAction S T gamma a b)) := by
  have hclock : MapsTo (fun r : ℝ ↦ T - (a + r) ^ 2)
      (Icc (0 : ℝ) (b - a)) D.carrier := by
    intro r hr
    exact hback (a + r) ⟨by linarith [hr.1], by linarith [hr.2]⟩
  have hkin := chartKin_tendsto_on_carrier hMet p (sub_nonneg.mpr hab)
    (fun r : ℝ ↦ T - (a + r) ^ 2)
    (continuous_const.sub ((continuous_const.add continuous_id).pow 2)).continuousOn
    hclock hKc hKchart u uLim huK huLimK hu
  let Q : Set M := (extChartAt I p).symm '' K
  have hQc : IsCompact Q := hKc.image_of_continuousOn
    ((continuousOn_extChartAt_symm (I := I) p).mono
      (fun z hz ↦ interior_subset (hKchart hz)))
  have hval : ∀ n s, s ∈ Icc a b → alpha n s ∈ Q := by
    intro n s hs
    have hr : s - a ∈ Icc (0 : ℝ) (b - a) :=
      ⟨sub_nonneg.mpr hs.1, sub_le_sub_right hs.2 a⟩
    refine ⟨extChartAt I p (alpha n s), ?_, ?_⟩
    · have h := huK n ⟨s - a, hr⟩
      rw [hrep n hr] at h
      have hshift : a + (s - a) = s := by ring
      simpa only [hshift] using h
    · exact (extChartAt I p).left_inv (by
        rw [extChartAt_source]
        exact hsrc n hs)
  have hpot := lScalar_tendsto_compact (I := I) S hSc T a b hab hback Q hQc
    alpha gamma (fun n ↦ curve_cont_local I p (alpha n) (u n) hab (hsrc n) (hrep n))
    hval hunif
  have hsum := hkin.add hpot
  have hseq : (fun n ↦ lRegularizedAction S T (alpha n) a b) =
      (fun n ↦
        (∫ r in (0 : ℝ)..b - a, (1 / 2 : ℝ) * inner ℝ
          (chartGramOp S.family p (T - (a + r) ^ 2, (u n).toFun r) ((u n).deriv r))
          ((u n).deriv r)) +
        (∫ s in a..b, 2 * s ^ 2 * S.scalar (T - s ^ 2) (alpha n s))) := by
    funext n
    exact action_split_chart_on_carrier S hMet hSc T a b hab p (alpha n)
      (u n) (hsrc n) (hrep n) hback
  rw [hseq, action_split_chart_on_carrier S hMet hSc T a b hab p gamma
    uLim hsrcLim hrepLim hback]
  exact hsum

private theorem action_finite_tendsto_on_carrier
    (S : SolutionOn (I := I) (M := M) D)
    (hMet : MetricFamilySmoothOn (I := I) (M := M) D S.family.metric)
    (hSc : ScalarSTContOn (I := I) (M := M) S)
    (T a b : ℝ) {m : ℕ} (t : Fin (m + 1) → ℝ)
    (htmono : Monotone t) (ht0 : t 0 = a) (htlast : t (Fin.last m) = b)
    (p : Fin m → M) (alpha : ℕ → ℝ → M) (gamma : ℝ → M)
    (u : (i : Fin m) → ℕ → timeH1 E (partitionIntervalLength t i))
    (uLim : (i : Fin m) → timeH1 E (partitionIntervalLength t i))
    (hsrc : ∀ i n, MapsTo (alpha n) (Icc (t i.castSucc) (t i.succ))
      (chartAt H (p i)).source)
    (hrep : ∀ i n, EqOn (u i n).toFun
      (fun r ↦ extChartAt I (p i) (alpha n (t i.castSucc + r)))
      (Icc (0 : ℝ) (partitionIntervalLength t i)))
    (hsrcLim : ∀ i, MapsTo gamma (Icc (t i.castSucc) (t i.succ))
      (chartAt H (p i)).source)
    (hrepLim : ∀ i, EqOn (uLim i).toFun
      (fun r ↦ extChartAt I (p i) (gamma (t i.castSucc + r)))
      (Icc (0 : ℝ) (partitionIntervalLength t i)))
    (K : Fin m → Set E) (hKc : ∀ i, IsCompact (K i))
    (hKchart : ∀ i, K i ⊆ interior (extChartAt I (p i)).target)
    (huK : ∀ i n (r : Icc (0 : ℝ) (partitionIntervalLength t i)), (u i n).toFun r.1 ∈ K i)
    (huLimK : ∀ i (r : Icc (0 : ℝ) (partitionIntervalLength t i)), (uLim i).toFun r.1 ∈ K i)
    (hu : ∀ i, Tendsto (u i) atTop (𝓝 (uLim i)))
    (hunif : TendstoUniformly (fun n (s : Icc a b) ↦ alpha n s.1)
      (fun s ↦ gamma s.1) atTop)
    (hback : ∀ s ∈ Icc a b, T - s ^ 2 ∈ D.carrier) :
    Tendsto (fun n ↦ lRegularizedAction S T (alpha n) a b) atTop
      (𝓝 (lRegularizedAction S T gamma a b)) := by
  have hsub (i : Fin m) : Icc (t i.castSucc) (t i.succ) ⊆ Icc a b := by
    apply Icc_subset_Icc
    · rw [← ht0]
      exact htmono (Fin.zero_le _)
    · rw [← htlast]
      exact htmono (Fin.le_last _)
  have hpiece (i : Fin m) : Tendsto
      (fun n ↦ lRegularizedAction S T (alpha n) (t i.castSucc) (t i.succ)) atTop
      (𝓝 (lRegularizedAction S T gamma (t i.castSucc) (t i.succ))) := by
    apply action_chart_tendsto_on_carrier S hMet hSc T (t i.castSucc) (t i.succ)
      (htmono Fin.castSucc_lt_succ.le) (p i) alpha gamma (u i) (uLim i)
      (hsrc i) (hrep i) (hsrcLim i) (hrepLim i)
      (K i) (hKc i) (hKchart i) (huK i) (huLimK i) (hu i)
    · exact hunif.comp (fun s : Icc (t i.castSucc) (t i.succ) ↦
        (⟨s.1, hsub i s.2⟩ : Icc a b))
    · exact fun s hs ↦ hback s (hsub i hs)
  have hsum := tendsto_finsetSum Finset.univ (fun i _ ↦ hpiece i)
  have hseq : (fun n ↦ lRegularizedAction S T (alpha n) a b) =
      (fun n ↦ ∑ i : Fin m, lRegularizedAction S T (alpha n) (t i.castSucc) (t i.succ)) := by
    funext n
    exact (action_partition_on_carrier S hMet hSc T a b t htmono ht0 htlast
      p (alpha n) (fun i ↦ u i n) (fun i ↦ hsrc i n) (fun i ↦ hrep i n) hback).2
  rw [hseq, (action_partition_on_carrier S hMet hSc T a b t htmono ht0 htlast
    p gamma uLim hsrcLim hrepLim hback).2]
  exact hsum

omit [IsManifold I ∞ M] in
private theorem exists_flat_chart_approx
    (p : M) {L : ℝ} (hL : 0 ≤ L) (uLim : timeH1 E L)
    (htar : ∀ r : Icc (0 : ℝ) L, uLim.toFun r.1 ∈ (extChartAt I p).target) :
    ∃ K : Set E, ∃ w : ℕ → timeH1 E L, ∃ v : ℕ → ℝ → E,
      IsCompact K ∧ K ⊆ (extChartAt I p).target ∧
      (∀ r : Icc (0 : ℝ) L, uLim.toFun r.1 ∈ K) ∧
      (∀ n, ContDiff ℝ 1 (v n)) ∧
      (∀ n, EqOn (w n).toFun (v n) (Icc (0 : ℝ) L)) ∧
      (∀ n, v n 0 = uLim.toFun 0) ∧ (∀ n, v n L = uLim.toFun L) ∧
      (∀ n, v n =ᶠ[𝓝 (0 : ℝ)] fun _ ↦ v n 0) ∧
      (∀ n, v n =ᶠ[𝓝 L] fun _ ↦ v n L) ∧
      (∀ n (r : Icc (0 : ℝ) L), v n r.1 ∈ K) ∧
      Tendsto w atTop (𝓝 uLim) ∧
      TendstoUniformly (fun n (r : Icc (0 : ℝ) L) ↦ v n r.1)
        (fun r ↦ uLim.toFun r.1) atTop := by
  classical
  obtain ⟨K, hKc, _hKclosed, hKint, hKtar⟩ :=
    exists_compact_closed_between
      (isCompact_Icc.image_of_continuousOn uLim.continuousOn_toFun)
      (isOpen_extChartAt_target (I := I) p)
      (by rintro _ ⟨r, hr, rfl⟩; exact htar ⟨r, hr⟩)
  have hLimInt (r : Icc (0 : ℝ) L) : uLim.toFun r.1 ∈ interior K :=
    hKint ⟨r.1, r.2, rfl⟩
  have hflat : ∃ w : ℕ → timeH1 E L, ∃ v : ℕ → ℝ → E,
      (∀ n, ContDiff ℝ 1 (v n)) ∧
      (∀ n, EqOn (w n).toFun (v n) (Icc (0 : ℝ) L)) ∧
      (∀ n, v n 0 = uLim.toFun 0) ∧ (∀ n, v n L = uLim.toFun L) ∧
      (∀ n, v n =ᶠ[𝓝 (0 : ℝ)] fun _ ↦ uLim.toFun 0) ∧
      (∀ n, v n =ᶠ[𝓝 L] fun _ ↦ uLim.toFun L) ∧
      Tendsto w atTop (𝓝 uLim) := by
    rcases hL.eq_or_lt with hL0 | hLpos
    · subst L
      refine ⟨fun _ ↦ uLim, fun _ _ ↦ uLim.toFun 0,
        fun _ ↦ contDiff_const, ?_, fun _ ↦ rfl, fun _ ↦ rfl,
        fun _ ↦ Eventually.of_forall fun _ ↦ rfl,
        fun _ ↦ Eventually.of_forall fun _ ↦ rfl, tendsto_const_nhds⟩
      intro n r hr
      have hr0 : r = 0 := le_antisymm hr.2 hr.1
      subst r
      rfl
    · obtain ⟨w, v, hv, hwv, hv0, hvL, hvg0, hvgL, hw, _hderiv⟩ :=
        exists_flat_dense hLpos uLim
      exact ⟨w, v, hv, hwv, hv0, hvL, hvg0, hvgL, hw⟩
  obtain ⟨w, v, hv, hwv, hv0, hvL, hvg0, hvgL, hw⟩ := hflat
  have hvlim : TendstoUniformly (fun n (r : Icc (0 : ℝ) L) ↦ v n r.1)
      (fun r ↦ uLim.toFun r.1) atTop := by
    exact (tendstoUniformly_congr
      (F := fun n (r : Icc (0 : ℝ) L) ↦ (w n).toFun r.1)
      (F' := fun n r ↦ v n r.1)
      (Eventually.of_forall fun n ↦ funext fun r ↦ hwv n r.2)).mp
      (DifferentialGeometry.Analysis.timeH1_tendstoUniformly w uLim hw)
  have hcompact : IsCompact (range fun r : Icc (0 : ℝ) L ↦ uLim.toFun r.1) :=
    isCompact_range uLim.continuousOn_toFun.domRestrict
  obtain ⟨delta, hdelta, hthick⟩ := hcompact.exists_thickening_subset_open
    isOpen_interior (by rintro _ ⟨r, rfl⟩; exact hLimInt r)
  have hev : ∀ᶠ n in atTop, ∀ r : Icc (0 : ℝ) L, v n r.1 ∈ K := by
    filter_upwards [(Metric.tendstoUniformly_iff.mp hvlim) delta hdelta] with n hn
    intro r
    apply interior_subset
    apply hthick
    exact Metric.mem_thickening_iff.mpr
      ⟨uLim.toFun r.1, mem_range_self r, by simpa only [dist_comm] using hn r⟩
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  refine ⟨K, (fun n ↦ w (n + N)), (fun n ↦ v (n + N)), hKc, hKtar,
    (fun r ↦ interior_subset (hLimInt r)), (fun n ↦ hv (n + N)),
    (fun n ↦ hwv (n + N)), (fun n ↦ hv0 (n + N)), (fun n ↦ hvL (n + N)),
    ?_, ?_, ?_, hw.comp (tendsto_add_atTop_nat N), ?_⟩
  · exact fun n ↦ (hvg0 (n + N)).trans
      (Eventually.of_forall fun _ ↦ (hv0 (n + N)).symm)
  · exact fun n ↦ (hvgL (n + N)).trans
      (Eventually.of_forall fun _ ↦ (hvL (n + N)).symm)
  · exact fun n r ↦ hN (n + N) (Nat.le_add_left N n) r
  · intro U hU
    exact (tendsto_add_atTop_nat N).eventually (hvlim U hU)

theorem exists_lRegAction_c1_approx_on_carrier
    (S : SolutionOn (I := I) (M := M) D)
    (hMet : MetricFamilySmoothOn (I := I) (M := M) D S.family.metric)
    (hSc : ScalarSTContOn (I := I) (M := M) S)
    (T a b : ℝ) {m : ℕ} (t : Fin (m + 1) → ℝ)
    (htmono : Monotone t) (ht0 : t 0 = a) (htlast : t (Fin.last m) = b)
    (p : Fin m → M) (gamma : ℝ → M)
    (uLim : (i : Fin m) → timeH1 E (partitionIntervalLength t i))
    (hsrcLim : ∀ i, MapsTo gamma (Icc (t i.castSucc) (t i.succ))
      (chartAt H (p i)).source)
    (hrepLim : ∀ i, EqOn (uLim i).toFun
      (fun r ↦ extChartAt I (p i) (gamma (t i.castSucc + r)))
      (Icc (0 : ℝ) (partitionIntervalLength t i)))
    (hback : ∀ s ∈ Icc a b, T - s ^ 2 ∈ D.carrier) :
    ∃ alpha : ℕ → ℝ → M,
      (∀ n, ContMDiff (modelWithCornersSelf ℝ ℝ) I 1 (alpha n)) ∧
      (∀ n, alpha n a = gamma a) ∧ (∀ n, alpha n b = gamma b) ∧
      Tendsto (fun n ↦ lRegularizedAction S T (alpha n) a b) atTop
        (𝓝 (lRegularizedAction S T gamma a b)) := by
  classical
  have htar (i : Fin m) (r : Icc (0 : ℝ) (partitionIntervalLength t i)) :
      (uLim i).toFun r.1 ∈ (extChartAt I (p i)).target := by
    rw [hrepLim i r.2]
    apply (extChartAt I (p i)).map_source
    rw [extChartAt_source]
    apply hsrcLim i
    have hr2 : r.1 ≤ t i.succ - t i.castSucc := r.2.2
    exact ⟨by linarith [r.2.1], by linarith [hr2]⟩
  choose K u v hKc hKtar huLimK hvC1 huv hv0 hvL hvg0 hvgL hvK hu hvlim using
    fun i : Fin m ↦ exists_flat_chart_approx (p i)
      (sub_nonneg.mpr (htmono Fin.castSucc_lt_succ.le)) (uLim i) (htar i)
  obtain ⟨alpha, halpha, ha, hb, hrepV, hsrc, hunif⟩ :=
    exists_c1_of_flat a b t htmono ht0 htlast p gamma uLim hsrcLim hrepLim
      K hKc hKtar v hvC1 hvg0 hvgL hv0 hvL hvK huLimK hvlim
  have hrep (i : Fin m) (n : ℕ) : EqOn (u i n).toFun
      (fun r ↦ extChartAt I (p i) (alpha n (t i.castSucc + r)))
      (Icc (0 : ℝ) (partitionIntervalLength t i)) :=
    (huv i n).trans (hrepV i n)
  have huK (i : Fin m) (n : ℕ) (r : Icc (0 : ℝ) (partitionIntervalLength t i)) :
      (u i n).toFun r.1 ∈ K i := by
    rw [huv i n r.2]
    exact hvK i n r
  have hKchart (i : Fin m) : K i ⊆ interior (extChartAt I (p i)).target := by
    rw [(isOpen_extChartAt_target (I := I) (p i)).interior_eq]
    exact hKtar i
  exact ⟨alpha, halpha, ha, hb,
    action_finite_tendsto_on_carrier S hMet hSc T a b t htmono ht0 htlast
      p alpha gamma u uLim hsrc hrep hsrcLim hrepLim K hKc hKchart
      huK huLimK hu hunif hback⟩

theorem exists_lRegAction_join_lt_on_carrier
    (S : SolutionOn (I := I) (M := M) D)
    (hMet : MetricFamilySmoothOn (I := I) (M := M) D S.family.metric)
    (hSc : ScalarSTContOn (I := I) (M := M) S)
    (T b : ℝ) {c : ℝ} (hc : 0 < c) (hcb : c < b)
    (alpha beta : ℝ → M)
    (halpha : ContMDiffOn (modelWithCornersSelf ℝ ℝ) I 1 alpha (Icc (0 : ℝ) c))
    (hbeta : ContMDiffOn (modelWithCornersSelf ℝ ℝ) I 1 beta (Icc c b))
    (hnode : alpha c = beta c)
    (hback : ∀ s ∈ Icc (0 : ℝ) b, T - s ^ 2 ∈ D.carrier)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ gamma : ℝ → M,
      ContMDiff (modelWithCornersSelf ℝ ℝ) I 1 gamma ∧
      gamma 0 = alpha 0 ∧ gamma b = beta b ∧
      lRegularizedAction S T gamma 0 b <
        lRegularizedAction S T alpha 0 c + lRegularizedAction S T beta c b + epsilon := by
  obtain ⟨eta, m, t, p, u, heqHead, heqTail, htmono, ht0, htlast,
      _hnodeTime, hsrc, hrep⟩ :=
    exists_chartH1_join (I := I) 0 c b hc hcb alpha beta halpha hbeta hnode
  obtain ⟨delta, hdelta, hdelta0, hdeltab, hlimit⟩ :=
    exists_lRegAction_c1_approx_on_carrier S hMet hSc T 0 b t htmono ht0 htlast
      p eta u hsrc hrep hback
  have hInt := (action_partition_on_carrier S hMet hSc T 0 b t htmono ht0 htlast
    p eta u hsrc hrep hback).1
  have hb : 0 ≤ b := (hc.trans hcb).le
  have hIntHead : IntervalIntegrable (lRegularizedLagrangian S T eta) volume 0 c :=
    hInt.mono_set (by
      rw [uIcc_of_le hc.le, uIcc_of_le hb]
      exact Icc_subset_Icc le_rfl hcb.le)
  have hIntTail : IntervalIntegrable (lRegularizedLagrangian S T eta) volume c b :=
    hInt.mono_set (by
      rw [uIcc_of_le hcb.le, uIcc_of_le hb]
      exact Icc_subset_Icc hc.le le_rfl)
  have hHead : lRegularizedAction S T eta 0 c = lRegularizedAction S T alpha 0 c := by
    apply lRegularizedAction_congr
    intro s hs
    have hs' : s ∈ Ioo (0 : ℝ) c := by simpa only [uIoo_of_le hc.le] using hs
    exact heqHead ⟨hs'.1.le, hs'.2.le⟩
  have hTail : lRegularizedAction S T eta c b = lRegularizedAction S T beta c b := by
    apply lRegularizedAction_congr
    intro s hs
    have hs' : s ∈ Ioo c b := by simpa only [uIoo_of_le hcb.le] using hs
    exact heqTail ⟨hs'.1.le, hs'.2.le⟩
  have hAction : lRegularizedAction S T eta 0 b =
      lRegularizedAction S T alpha 0 c + lRegularizedAction S T beta c b := by
    rw [← lRegularizedAction_add S T eta 0 c b hIntHead hIntTail, hHead, hTail]
  have hevent : ∀ᶠ n in atTop,
      lRegularizedAction S T (delta n) 0 b < lRegularizedAction S T eta 0 b + epsilon :=
    hlimit.eventually (Iio_mem_nhds (lt_add_of_pos_right _ hepsilon))
  obtain ⟨n, hn⟩ := hevent.exists
  refine ⟨delta n, hdelta n, ?_, ?_, ?_⟩
  · exact (hdelta0 n).trans (heqHead ⟨le_rfl, hc.le⟩)
  · exact (hdeltab n).trans (heqTail ⟨hcb.le, le_rfl⟩)
  · simpa only [hAction] using hn

end DifferentialGeometry.PDE.RicciFlow

end
