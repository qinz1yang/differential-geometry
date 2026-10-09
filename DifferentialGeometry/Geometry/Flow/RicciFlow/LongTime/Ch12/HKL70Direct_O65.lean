import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HtraceU_O56
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.MicroGlueTracedLocal
import DifferentialGeometry.Geometry.Metric.RestrictionDistance

/-!
# CH12-O65, group 1: hKL70 by the direct route (F1) — chain traces + local volume test ⇒ KL70

`[FROZEN] CH12-O65 G1` (lead ruling: F1 direct route; F2 → (a), `hloc` an explicit binder).
* `sliceBound_U_O65`: along non-`capPtU_O56` centres with `1 ≤ R(y i)`, the chain traces of
  `htrace_U_O56` (its `D n → ∞` construction, ending in the chain-trace binder instead of
  `traced_buffer_of_chain_traces`) feed the tree theorem
  `exists_normalized_scalar_bound_of_chain_traces_local_O3` at `x i := y i`: the normalized
  scalar is bounded on every normalized ball.
* `hKL70_direct_O65`: the hKL70 U-form (`hKL70_U_O56`'s conclusion verbatim) from `hloc`
  (`[FROZEN] CH12-O65 hloc`): tail shift to `1 ≤ R(y n)`, `sliceBound_U_O65` at radius `ρ + 1`,
  contradiction with `R(z n)/R(y n) → ∞` and `z n ∈ B(y n, (ρ + 1)/√R(y n))`.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian Set Filter Topology
open DifferentialGeometry.Integral.Measure DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff ENNReal NNReal

namespace GC.LongTime.Ch12

universe u

private local instance {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s) :
    SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel G.terminalRegularOpen.isOpen)

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
  {δ : ℝ → ℝ}

/-- **Normalized scalar bound along non-`capPtU` centres** (F1 (a)–(b)): chain traces from
`¬ capPtU_O56` (proof of `htrace_U_O56` / `htrace_core_O56`) and the local volume test give the
conclusion of `exists_normalized_scalar_bound_of_chain_traces_local_O3` at `x i := y i`. -/
theorem sliceBound_U_O65 (Hp : GC.LongTime.AnalyticSurgeryProfile F δ)
    (hKcap :
      ∀ A : ℝ, 0 < A → ∃ Q _T θ : ℝ, 1 ≤ Q ∧ 0 < θ ∧ ∀ Dcap : ℝ, StandardCap.transitionEnd < Dcap →
        ∃ T' : ℝ, ∀ s : RegularSlice F.observation, T' ≤ s.time → ∀ T₀ : ℝ, T' ≤ T₀ → T₀ ≤ s.time →
        ∀ (p : CutoffParameters)
          (records : ∀ i : Fin (sliceHistoryR_O3 F s).eventCount,
            T₀ - θ ≤ (sliceHistoryR_O3 F s).time i.succ →
            GeometricCutoffRecord (sliceHistoryR_O3 F s).toHistory i p),
          (p.delta = Hp.parameters.delta ∧ p.neckRadius = Hp.parameters.neckRadius ∧
            p.fixed = Hp.parameters.fixed ∧ p.recenterConstant = Hp.parameters.recenterConstant ∧
            32 * (Dcap + 1 + 4 * A) + 2 ≤ p.modelRadius ∧
            (∀ i hi b, linkedCanonicalWindow_O2 ((records i hi).static b))) →
          ∀ y : s.stage.Carrier,
          (∃ (j : Fin (sliceHistoryR_O3 F s).eventCount)
              (hj : T₀ - θ ≤ (sliceHistoryR_O3 F s).time j.succ)
              (hl : j.succ ≤ Fin.last (sliceHistoryR_O3 F s).eventCount)
              (B : BackwardPointTrace (sliceHistoryR_O3 F s).toHistory j.succ
                (Fin.last (sliceHistoryR_O3 F s).eventCount) hl y)
              (b : ((sliceHistoryR_O3 F s).toHistory.event j).RetainedBoundaryIndex)
              (x : standardCapWindow p.modelRadius),
              B.point j.succ le_rfl hl = ((records j hj).static b).window x ∧ ‖x.val‖ < Dcap + 1 ∧
                s.time - (sliceHistoryR_O3 F s).time j.succ ≤
                  θ * (((records j hj).static b).neck.scale)⁻¹) →
          ∀ z ∈ riemannianBallOf s.metric y (A / Real.sqrt (metricScalarAt s.metric y)),
            metricScalarAt s.metric z ≤ Q * metricScalarAt s.metric y)
    (Ctime : ℝ≥0) (hP2 : P2_O2 Hp Ctime) (hP5 : P5Linked_O13 Hp)
    (heps : 13000 * (13000 * Hp.epsilon) ≤
      min (neckModelTolerance ((1 / 4000000 : ℝ) / 26000)) (((1 / 4000000 : ℝ) / 26000) / 64))
    (A : ℝ) (hA : 0 < A) (s : ℕ → RegularSlice F.observation) (y : ∀ n, (s n).stage.Carrier)
    (h1 : Tendsto (fun n => (s n).time) atTop atTop)
    (h2 : ∀ n, (Hp.parameters.neckRadius (s n).time ^ 2)⁻¹ ≤ metricScalarAt (s n).metric (y n))
    (h3 : Tendsto (fun n => metricScalarAt (s n).metric (y n)) atTop atTop)
    (h4 : ∀ n, ¬ capPtU_O56 Hp hKcap A (s n) (y n))
    (hQ : ∀ i, 1 ≤ (sliceSlabR_O3 F (s i)).flow.scalar (s i).time (y i))
    {κ : ℝ} (σ : ℕ → ℝ) (hκ : 0 < κ)
    (hσlim : Tendsto (fun i => σ i *
        Real.sqrt ((sliceSlabR_O3 F (s i)).flow.scalar (s i).time (y i))) atTop atTop)
    (hloc : ∀ i (w : ((sliceSlabR_O3 F (s i)).restrictIncoming le_rfl
          (sliceSlabR_O3 F (s i)).lt le_rfl).terminalRegularOpen),
        riemannianEDistOf ((sliceSlabR_O3 F (s i)).endpointTerminalLimitMetric
          ((sliceHistoryR_O3 F (s i)).stage
            (Fin.last (sliceHistoryR_O3 F (s i)).eventCount))).metric
          ⟨y i, mem_slice_terminalRegularOpen_O51 F (s i) (y i)⟩ w <
          ENNReal.ofReal (σ i) →
        ∀ b : ℝ, 0 < b → b ≤ σ i →
          ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
            riemannianVolumeMeasure ThreeModel
              ((sliceSlabR_O3 F (s i)).restrictIncoming le_rfl
                (sliceSlabR_O3 F (s i)).lt le_rfl).terminalRegularOpen
              ((sliceSlabR_O3 F (s i)).endpointTerminalLimitMetric
                ((sliceHistoryR_O3 F (s i)).stage
                  (Fin.last (sliceHistoryR_O3 F (s i)).eventCount))).metric
              (riemannianBallOf ((sliceSlabR_O3 F (s i)).endpointTerminalLimitMetric
                ((sliceHistoryR_O3 F (s i)).stage
                  (Fin.last (sliceHistoryR_O3 F (s i)).eventCount))).metric w b)) :
    ∀ R : ℝ, 0 < R → ∃ B : ℝ, ∀ᶠ i in atTop,
      ∀ w : ((sliceSlabR_O3 F (s i)).restrictIncoming le_rfl
          (sliceSlabR_O3 F (s i)).lt le_rfl).terminalRegularOpen,
        riemannianEDistOf (scaleMetric ((sliceSlabR_O3 F (s i)).flow.scalar (s i).time (y i))
          (zero_lt_one.trans_le (hQ i))
          ((sliceSlabR_O3 F (s i)).endpointTerminalLimitMetric
            ((sliceHistoryR_O3 F (s i)).stage
              (Fin.last (sliceHistoryR_O3 F (s i)).eventCount))).metric)
          ⟨y i, mem_slice_terminalRegularOpen_O51 F (s i) (y i)⟩ w < ENNReal.ofReal R →
        metricScalarAt ((sliceSlabR_O3 F (s i)).endpointTerminalLimitMetric
            ((sliceHistoryR_O3 F (s i)).stage
              (Fin.last (sliceHistoryR_O3 F (s i)).eventCount))).metric w /
          (sliceSlabR_O3 F (s i)).flow.scalar (s i).time (y i) ≤ B := by
  classical
  have hTE := StandardCap.transitionEnd_pos
  have hspec := (hKcap A hA).choose_spec.choose_spec.choose_spec
  have hθ : 0 < (hKcap A hA).choose_spec.choose_spec.choose := hspec.2.1
  obtain ⟨ε₀, hε₀, hsc⟩ := exists_presented_cap_scalar_lower_bound_of_canonical_window_core.{u}
    (StandardCap.transitionEnd + 1) (by linarith)
  have hζ : 0 < min (1 / 2 : ℝ) ε₀ := lt_min (by norm_num) hε₀
  choose T5 hT5 using fun m : ℕ =>
    hP5 (32 * (StandardCap.transitionEnd + 1 + m + 1 + 4 * A) + 2) (min (1 / 2) ε₀) 2 hζ
  let T' : ℕ → ℝ := fun m =>
    (hspec.2.2 (StandardCap.transitionEnd + 1 + m) (dcapU_pos_O56 m A)).choose
  let Thr : ℕ → ℝ := fun m => max (T' m) (T5 m + (hKcap A hA).choose_spec.choose_spec.choose)
  let Pn : ℕ → ℕ → Prop := fun n m => ∀ m' ≤ m, Thr m' ≤ (s n).time
  let mn : ℕ → ℕ := fun n => Nat.findGreatest (Pn n) n
  let D : ℕ → ℝ := fun n =>
    if Pn n 0 then StandardCap.transitionEnd + 1 + (mn n : ℝ) else 0
  have hD : Tendsto D atTop atTop := by
    rw [tendsto_atTop]
    intro b
    obtain ⟨M, hM⟩ := exists_nat_ge b
    have hev : ∀ᶠ n in atTop, ∀ m' ∈ Set.Iic M, Thr m' ≤ (s n).time :=
      (Filter.eventually_all_finite (Set.finite_Iic M)).2 fun m' _ => h1.eventually_ge_atTop _
    filter_upwards [hev, eventually_ge_atTop M] with n hn hnM
    have hPM : Pn n M := fun m' hm' => hn m' hm'
    have h0 : Pn n 0 := fun m' hm' => hn m' (hm'.trans (Nat.zero_le M))
    have hle : M ≤ mn n := Nat.le_findGreatest hnM hPM
    have hle' : (M : ℝ) ≤ (mn n : ℝ) := by exact_mod_cast hle
    simp only [D, h0, ↓reduceIte]
    linarith
  have hq : ∀ i, (Hp.parameters.neckRadius (s i).time ^ 2)⁻¹ ≤
      (sliceSlabR_O3 F (s i)).flow.scalar (s i).time (y i) := fun i => by
    rw [slice_flow_scalar_O51]; exact h2 i
  have htime : Tendsto (fun i => (sliceSlabR_O3 F (s i)).flow.scalar (s i).time (y i) * (s i).time)
      atTop atTop := by
    simp_rw [slice_flow_scalar_O51]
    exact h3.atTop_mul_atTop₀ h1
  have hQlim : Tendsto (fun i => (sliceSlabR_O3 F (s i)).flow.scalar (s i).time (y i))
      atTop atTop := by
    simp_rw [slice_flow_scalar_O51]
    exact h3
  obtain ⟨phi, hadm, hphi⟩ := slice_pinching_O3 Hp
  refine exists_normalized_scalar_bound_of_chain_traces_local_O3
    (fun i => sliceHistoryR_O3 F (s i)) (fun i => (s i).time) (fun i => sliceSlabR_O3 F (s i))
    (fun i => sliceSlabR_initial_O3 F (s i)) (fun i => slice_precedingR_O3 F (s i)) Ctime
    ⟨Hp.C2, by linarith [Hp.C2_ge_one]⟩ (fun i => (Hp.parameters.neckRadius (s i).time ^ 2)⁻¹)
    (fun i => inv_pos.mpr (pow_pos (Hp.parameters.neckRadius_pos _ (s i).positive.le) 2))
    (fun i j w t ht hw => sliceHistory_eventSlabsDerivative_O3 Hp (s i) Ctime _ hP2 le_rfl j
      (Fin.castSucc_lt_last j) w t ht hw)
    (fun i w t ht hw => sliceSlab_derivative_O3 Hp (s i) Ctime _ hP2 le_rfl w t ht hw)
    (fun i w t ht hw v => sliceSlab_gradient_O3 Hp (s i) _ le_rfl w t ht hw v)
    (fun i => ⟨y i, mem_slice_terminalRegularOpen_O51 F (s i) (y i)⟩) hQ hq hQlim hadm
    (fun i j => (hphi (s i)).1 j) (fun i => (hphi (s i)).2.2) σ hκ hσlim hloc heps
    (fun i w hw => sliceSlab_canonical_O3 Hp (s i) w hw) htime (Kc := 1) (lam := 0) le_rfl hθ
    D hD ?_
  -- the chain-trace binder: `htrace_core_O56`'s `?_` with `hlev` inlined (`htrace_U_O56`, n := i)
  intro i N pp δ' M τ hp0 hδ hch hb hKc hM1 hτ0 hτt hC h4' hDi k hk w hw
  rw [zero_div, zero_add] at hDi
  have hX : 0 ≤ Real.sqrt (8 * M) *
      Real.exp (9 * (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * M) * τ) *
        ∑ k ∈ Finset.range (N + 1), δ' k := by
    have hsum : 0 ≤ ∑ k ∈ Finset.range (N + 1), δ' k :=
      Finset.sum_nonneg fun k hk => (hδ k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))).le
    positivity
  have hDn : 0 < D i := by linarith
  have h0 : Pn i 0 := by
    by_contra h0
    simp only [D, h0, ↓reduceIte] at hDn
    exact lt_irrefl _ hDn
  have hDeq : D i = StandardCap.transitionEnd + 1 + (mn i : ℝ) := by simp only [D, h0, ↓reduceIte]
  have hPm : Pn i (mn i) := Nat.findGreatest_spec (Nat.zero_le i) h0
  have hThr := hPm (mn i) le_rfl
  have hT'le : T' (mn i) ≤ (s i).time := (le_max_left _ _).trans hThr
  have hT5le : T5 (mn i) + (hKcap A hA).choose_spec.choose_spec.choose ≤ (s i).time :=
    (le_max_right _ _).trans hThr
  obtain ⟨p, hpd, hpn, hpf, hpc, hRp, hζp, hmp, recs, hlink⟩ := hT5 (mn i) (sliceIndexR_O3 F (s i))
  let H₀ := F.tower.history (sliceIndexR_O3 F (s i))
  let k₀ := sliceStageR_O3 F (s i)
  let records : ∀ j : Fin (sliceHistoryR_O3 F (s i)).eventCount,
      (s i).time - (hKcap A hA).choose_spec.choose_spec.choose ≤
        (sliceHistoryR_O3 F (s i)).time j.succ →
      GeometricCutoffRecord (sliceHistoryR_O3 F (s i)).toHistory j p := fun j hj =>
    H₀.geometricCutoffRecordOfPrefix k₀
      (recs (Fin.castLE (Nat.le_of_lt_succ k₀.isLt) j) (by
        have h' : T5 (mn i) ≤ (sliceHistoryR_O3 F (s i)).time j.succ := by linarith
        exact h'))
  have hcan : ∀ j hj b, ((records j hj).static b).hasCanonicalWindow := fun j hj b =>
    linkedCanonicalWindow_hasCanonicalWindow_O2 _ (hlink _ _ b)
  have hm0 : (0 : ℝ) ≤ (mn i : ℝ) := Nat.cast_nonneg _
  have hmodel : StandardCap.transitionEnd + 1 ≤ p.modelRadius := by linarith
  have hDm : D i ≤ p.modelRadius := by rw [hDeq]; linarith
  obtain ⟨hpin1, hpin2, -⟩ := hphi (s i)
  have hqM : (Hp.parameters.neckRadius (s i).time ^ 2)⁻¹ ≤ M := by
    have := hq i
    linarith
  refine chain_traces_of_not_capWindowPoint_of_closedSlab_O3L (sliceHistoryR_O3 F (s i)) rfl
    (sliceSlabR_O3 F (s i)) (sliceSlabR_initial_O3 F (s i))
    ((s i).time - (hKcap A hA).choose_spec.choose_spec.choose) (by linarith)
    records hcan (fun j hj b z => hsc _ hmodel (hζp.trans (min_le_right _ _)) hmp _
      (hcan j hj b) z) (hζp.trans (min_le_left _ _)) hadm hpin1 hpin2
    (sliceHistory_eventSlabsDerivative_O3 Hp (s i) Ctime _ hP2 le_rfl)
    (sliceSlab_derivative_O3 Hp (s i) Ctime _ hP2 le_rfl) hDm le_rfl (y i) ?_
    (Nc := 0) (fun _ => y i) (fun _ => 1) rfl (fun k hk => absurd hk (Nat.not_lt_zero k))
    (fun k hk => absurd hk (Nat.not_lt_zero k)) (Mc := 0) (lamc := 0)
    (fun k hk => absurd hk (Nat.not_lt_zero k)) (by simp)
    N pp δ' M τ hp0 hδ hch hb (by linarith) hqM hM1 hτ0 hτt hC h4' ?_ k hk w hw
  · rw [hDeq]
    intro hw'
    refine h4 i ⟨mn i, ?_⟩
    simp only [kcapPt_O29, hA, ↓reduceDIte]
    exact ⟨(s i).time, hT'le, le_rfl, p, records,
      ⟨hpd, hpn, hpf, hpc, hRp, fun j hj b => hlink _ _ b⟩, hw'⟩
  · rw [zero_add]
    exact hDi

/-- **hKL70 by the direct route** (`[FROZEN] CH12-O65 G1`): the hKL70 U-form from the local volume
test `hloc` (`[FROZEN] CH12-O65 hloc`, an explicit binder by lead ruling F2 → (a)). -/
theorem hKL70_direct_O65 (Hp : GC.LongTime.AnalyticSurgeryProfile F δ)
    (hKcap :
      ∀ A : ℝ, 0 < A → ∃ Q _T θ : ℝ, 1 ≤ Q ∧ 0 < θ ∧ ∀ Dcap : ℝ, StandardCap.transitionEnd < Dcap →
        ∃ T' : ℝ, ∀ s : RegularSlice F.observation, T' ≤ s.time → ∀ T₀ : ℝ, T' ≤ T₀ → T₀ ≤ s.time →
        ∀ (p : CutoffParameters)
          (records : ∀ i : Fin (sliceHistoryR_O3 F s).eventCount,
            T₀ - θ ≤ (sliceHistoryR_O3 F s).time i.succ →
            GeometricCutoffRecord (sliceHistoryR_O3 F s).toHistory i p),
          (p.delta = Hp.parameters.delta ∧ p.neckRadius = Hp.parameters.neckRadius ∧
            p.fixed = Hp.parameters.fixed ∧ p.recenterConstant = Hp.parameters.recenterConstant ∧
            32 * (Dcap + 1 + 4 * A) + 2 ≤ p.modelRadius ∧
            (∀ i hi b, linkedCanonicalWindow_O2 ((records i hi).static b))) →
          ∀ y : s.stage.Carrier,
          (∃ (j : Fin (sliceHistoryR_O3 F s).eventCount)
              (hj : T₀ - θ ≤ (sliceHistoryR_O3 F s).time j.succ)
              (hl : j.succ ≤ Fin.last (sliceHistoryR_O3 F s).eventCount)
              (B : BackwardPointTrace (sliceHistoryR_O3 F s).toHistory j.succ
                (Fin.last (sliceHistoryR_O3 F s).eventCount) hl y)
              (b : ((sliceHistoryR_O3 F s).toHistory.event j).RetainedBoundaryIndex)
              (x : standardCapWindow p.modelRadius),
              B.point j.succ le_rfl hl = ((records j hj).static b).window x ∧ ‖x.val‖ < Dcap + 1 ∧
                s.time - (sliceHistoryR_O3 F s).time j.succ ≤
                  θ * (((records j hj).static b).neck.scale)⁻¹) →
          ∀ z ∈ riemannianBallOf s.metric y (A / Real.sqrt (metricScalarAt s.metric y)),
            metricScalarAt s.metric z ≤ Q * metricScalarAt s.metric y)
    (Ctime : ℝ≥0) (hP2 : P2_O2 Hp Ctime) (hP5 : P5Linked_O13 Hp)
    (heps : 13000 * (13000 * Hp.epsilon) ≤
      min (neckModelTolerance ((1 / 4000000 : ℝ) / 26000)) (((1 / 4000000 : ℝ) / 26000) / 64))
    (hloc :
      ∀ A : ℝ, 0 < A → ∀ (s : ℕ → RegularSlice F.observation)
      (y z : ∀ n, (s n).stage.Carrier) (ρ : ℝ),
      Tendsto (fun n => (s n).time) atTop atTop →
      (∀ n, (Hp.parameters.neckRadius (s n).time ^ 2)⁻¹ ≤
        metricScalarAt (s n).metric (y n)) →
      Tendsto (fun n => metricScalarAt (s n).metric (y n)) atTop atTop →
      (∀ n, ¬ capPtU_O56 Hp hKcap A (s n) (y n)) →
      0 ≤ ρ → ρ ≤ A →
      (∀ n, z n ∈ riemannianBallOf (s n).metric (y n)
        (A / Real.sqrt (metricScalarAt (s n).metric (y n)))) →
      Tendsto (fun n => metricScalarAt (s n).metric (z n) /
        metricScalarAt (s n).metric (y n)) atTop atTop →
      (∀ r : ℝ, r < ρ → ∃ C : ℝ, ∀ᶠ n in atTop,
        ∀ w ∈ riemannianBallOf (s n).metric (y n)
          (r / Real.sqrt (metricScalarAt (s n).metric (y n))),
          metricScalarAt (s n).metric w ≤ C * metricScalarAt (s n).metric (y n)) →
      (∀ r : ℝ, ρ < r → ∀ᶠ n in atTop, z n ∈ riemannianBallOf (s n).metric (y n)
        (r / Real.sqrt (metricScalarAt (s n).metric (y n)))) →
      1 / 4 ≤ ρ →
      (∃ κ : ℝ, 0 < κ ∧ ∀ lam : ℝ, 1 < lam → ∀ r : ℝ, ρ < r → ∀ᶠ n in atTop,
          ∃ w : (s n).stage.Carrier,
            w ∈ riemannianBallOf (s n).metric (y n)
              (r / Real.sqrt (metricScalarAt (s n).metric (y n))) ∧
            metricScalarAt (s n).metric w = lam * metricScalarAt (s n).metric (y n) ∧
            ∃ hR : (Hp.parameters.neckRadius (s n).time ^ 2)⁻¹ < metricScalarAt (s n).metric w,
            ∃ W : SpatialCanonicalWitness (s n).metric Hp.epsilon Hp.C1 Hp.C2 w,
              W.capTubeHasNeckChart Hp.epsilon ∧
              (W.alternative.requiresVolume → ∀ b : ℝ, 0 < b → b ≤ (Real.sqrt Hp.C2)⁻¹ →
                ENNReal.ofReal (κ * b ^ 3) ≤
                  riemannianVolumeMeasure ThreeModel (s n).stage.Carrier
                    (scaleMetric (metricScalarAt (s n).metric w) W.Q_pos (s n).metric)
                    (riemannianBallOf
                      (scaleMetric (metricScalarAt (s n).metric w) W.Q_pos (s n).metric) w b)) ∧
              ∀ nk, W.alternative = SpatialCanonicalAlternative.neck nk →
                ∃ (U : TopologicalSpace.Opens (s n).stage.Carrier) (hxU : w ∈ U)
                  (S : SolutionOn (I := ThreeModel) (M := U)
                    (RealTimeInterval.closed
                      ((s n).time - (metricScalarAt (s n).metric w)⁻¹) (s n).time
                      (sub_le_self _ (inv_nonneg.mpr
                        (lt_of_le_of_lt (inv_nonneg.mpr (sq_nonneg _)) hR).le)))),
                  IsSolutionOn S ∧ S.base.metric (s n).time = (s n).metric.restrictOpen U ∧
                  Nonempty (StrongNeck S Hp.epsilon ⟨w, hxU⟩ (s n).time)) →
      ∃ (κ : ℝ) (σ : ℕ → ℝ), (0 < κ) ∧
      (Tendsto (fun i => σ i *
        Real.sqrt ((sliceSlabR_O3 F (s i)).flow.scalar (s i).time (y i))) atTop atTop) ∧
      (∀ i (w : ((sliceSlabR_O3 F (s i)).restrictIncoming le_rfl
          (sliceSlabR_O3 F (s i)).lt le_rfl).terminalRegularOpen),
        riemannianEDistOf ((sliceSlabR_O3 F (s i)).endpointTerminalLimitMetric
          ((sliceHistoryR_O3 F (s i)).stage
            (Fin.last (sliceHistoryR_O3 F (s i)).eventCount))).metric
          ⟨y i, mem_slice_terminalRegularOpen_O51 F (s i) (y i)⟩ w <
          ENNReal.ofReal (σ i) →
        ∀ b : ℝ, 0 < b → b ≤ σ i →
          ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
            riemannianVolumeMeasure ThreeModel
              ((sliceSlabR_O3 F (s i)).restrictIncoming le_rfl
                (sliceSlabR_O3 F (s i)).lt le_rfl).terminalRegularOpen
              ((sliceSlabR_O3 F (s i)).endpointTerminalLimitMetric
                ((sliceHistoryR_O3 F (s i)).stage
                  (Fin.last (sliceHistoryR_O3 F (s i)).eventCount))).metric
              (riemannianBallOf ((sliceSlabR_O3 F (s i)).endpointTerminalLimitMetric
                ((sliceHistoryR_O3 F (s i)).stage
                  (Fin.last (sliceHistoryR_O3 F (s i)).eventCount))).metric w b))) :
      ∀ A : ℝ, 0 < A → ∀ (s : ℕ → RegularSlice F.observation)
      (y z : ∀ n, (s n).stage.Carrier) (ρ : ℝ),
      Tendsto (fun n => (s n).time) atTop atTop →
      (∀ n, (Hp.parameters.neckRadius (s n).time ^ 2)⁻¹ ≤
        metricScalarAt (s n).metric (y n)) →
      Tendsto (fun n => metricScalarAt (s n).metric (y n)) atTop atTop →
      (∀ n, ¬ capPtU_O56 Hp hKcap A (s n) (y n)) →
      0 ≤ ρ → ρ ≤ A →
      (∀ n, z n ∈ riemannianBallOf (s n).metric (y n)
        (A / Real.sqrt (metricScalarAt (s n).metric (y n)))) →
      Tendsto (fun n => metricScalarAt (s n).metric (z n) /
        metricScalarAt (s n).metric (y n)) atTop atTop →
      (∀ r : ℝ, r < ρ → ∃ C : ℝ, ∀ᶠ n in atTop,
        ∀ w ∈ riemannianBallOf (s n).metric (y n)
          (r / Real.sqrt (metricScalarAt (s n).metric (y n))),
          metricScalarAt (s n).metric w ≤ C * metricScalarAt (s n).metric (y n)) →
      (∀ r : ℝ, ρ < r → ∀ᶠ n in atTop, z n ∈ riemannianBallOf (s n).metric (y n)
        (r / Real.sqrt (metricScalarAt (s n).metric (y n)))) →
      1 / 4 ≤ ρ →
      (∃ κ : ℝ, 0 < κ ∧ ∀ lam : ℝ, 1 < lam → ∀ r : ℝ, ρ < r → ∀ᶠ n in atTop,
          ∃ w : (s n).stage.Carrier,
            w ∈ riemannianBallOf (s n).metric (y n)
              (r / Real.sqrt (metricScalarAt (s n).metric (y n))) ∧
            metricScalarAt (s n).metric w = lam * metricScalarAt (s n).metric (y n) ∧
            ∃ hR : (Hp.parameters.neckRadius (s n).time ^ 2)⁻¹ < metricScalarAt (s n).metric w,
            ∃ W : SpatialCanonicalWitness (s n).metric Hp.epsilon Hp.C1 Hp.C2 w,
              W.capTubeHasNeckChart Hp.epsilon ∧
              (W.alternative.requiresVolume → ∀ b : ℝ, 0 < b → b ≤ (Real.sqrt Hp.C2)⁻¹ →
                ENNReal.ofReal (κ * b ^ 3) ≤
                  riemannianVolumeMeasure ThreeModel (s n).stage.Carrier
                    (scaleMetric (metricScalarAt (s n).metric w) W.Q_pos (s n).metric)
                    (riemannianBallOf
                      (scaleMetric (metricScalarAt (s n).metric w) W.Q_pos (s n).metric) w b)) ∧
              ∀ nk, W.alternative = SpatialCanonicalAlternative.neck nk →
                ∃ (U : TopologicalSpace.Opens (s n).stage.Carrier) (hxU : w ∈ U)
                  (S : SolutionOn (I := ThreeModel) (M := U)
                    (RealTimeInterval.closed
                      ((s n).time - (metricScalarAt (s n).metric w)⁻¹) (s n).time
                      (sub_le_self _ (inv_nonneg.mpr
                        (lt_of_le_of_lt (inv_nonneg.mpr (sq_nonneg _)) hR).le)))),
                  IsSolutionOn S ∧ S.base.metric (s n).time = (s n).metric.restrictOpen U ∧
                  Nonempty (StrongNeck S Hp.epsilon ⟨w, hxU⟩ (s n).time)) →
      False := by
  intro A hA s y z ρ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  obtain ⟨κ, σ, hκ, hσlim, hloc'⟩ := hloc A hA s y z ρ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  -- tail shift: `1 ≤ R(y n)` for `n ≥ N`
  obtain ⟨N, hN⟩ := (h3.eventually_ge_atTop 1).exists_forall_of_atTop
  have hsh : Tendsto (fun n : ℕ => n + N) atTop atTop := tendsto_add_atTop_nat N
  have hQ : ∀ i, 1 ≤ (sliceSlabR_O3 F (s (i + N))).flow.scalar (s (i + N)).time (y (i + N)) :=
    fun i => by rw [slice_flow_scalar_O51]; exact hN _ (Nat.le_add_left N i)
  obtain ⟨B, hB⟩ := sliceBound_U_O65 Hp hKcap Ctime hP2 hP5 heps A hA (fun n => s (n + N))
    (fun n => y (n + N)) (h1.comp hsh) (fun n => h2 (n + N)) (h3.comp hsh) (fun n => h4 (n + N))
    hQ (fun i => σ (i + N)) hκ (hσlim.comp hsh) (fun i => hloc' (i + N)) (ρ + 1) (by linarith)
  obtain ⟨i, hBi, hzi, hgt⟩ := (hB.and ((hsh.eventually (h10 (ρ + 1) (by linarith))).and
    (hsh.eventually (h8.eventually_gt_atTop B)))).exists
  have hpos : 0 < metricScalarAt (s (i + N)).metric (y (i + N)) :=
    zero_lt_one.trans_le (hN _ (Nat.le_add_left N i))
  have hd := Geometry.Metric.riemannianEDistOf_restrictOpen_lt_of_riemannianBallOf_subset
    (s (i + N)).metric
    ((sliceSlabR_O3 F (s (i + N))).restrictIncoming le_rfl
      (sliceSlabR_O3 F (s (i + N))).lt le_rfl).terminalRegularOpen
    ⟨y (i + N), mem_slice_terminalRegularOpen_O51 F (s (i + N)) (y (i + N))⟩
    ⟨z (i + N), mem_slice_terminalRegularOpen_O51 F (s (i + N)) (z (i + N))⟩
    (fun w _ => mem_slice_terminalRegularOpen_O51 F (s (i + N)) w) hzi
  have hsq : Real.sqrt (metricScalarAt (s (i + N)).metric (y (i + N))) *
      ((ρ + 1) / Real.sqrt (metricScalarAt (s (i + N)).metric (y (i + N)))) = ρ + 1 :=
    mul_div_cancel₀ _ (Real.sqrt_pos.2 hpos).ne'
  have hm := hBi ⟨z (i + N), mem_slice_terminalRegularOpen_O51 F (s (i + N)) (z (i + N))⟩ (by
    rw [edistOf_scale, slice_endpoint_metric_O51, slice_flow_scalar_O51, ← hsq,
      ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
    exact (ENNReal.mul_lt_mul_iff_right (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.2 hpos)).ne'
      ENNReal.ofReal_ne_top).mpr hd)
  rw [slice_endpoint_metric_O51, slice_flow_scalar_O51] at hm
  let U : TopologicalSpace.Opens (s (i + N)).stage.Carrier :=
    ((sliceSlabR_O3 F (s (i + N))).restrictIncoming le_rfl
      (sliceSlabR_O3 F (s (i + N))).lt le_rfl).terminalRegularOpen
  have : IsManifold ThreeModel 1 U := IsManifold.of_le (I := ThreeModel) (n := ∞) (by decide)
  have hsc := metricScalarAt_restrictOpen (I := ThreeModel) (s (i + N)).metric U
    ⟨z (i + N), mem_slice_terminalRegularOpen_O51 F (s (i + N)) (z (i + N))⟩
  have hz : metricScalarAt (s (i + N)).metric (z (i + N)) /
      metricScalarAt (s (i + N)).metric (y (i + N)) ≤ B :=
    (congrArg (· / metricScalarAt (s (i + N)).metric (y (i + N))) hsc.symm).trans_le hm
  linarith

end GC.LongTime.Ch12
