import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.KL70B1SlicePt_O51
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.KcapPt_O29
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BoundedCurvatureAtDistanceTracedPositive

/-!
# CH12-O56, group 1: the union cap predicate `capPtU_O56`, its cap branch, and HTRACE

`[FROZEN] CH12-O56 G1/G2` (lead ruling O56-1 (a)).  With a fixed cap radius `Dcap A` the backward
traces needed by the escape limit at radius `ρ` are not available (the chain-trace argument needs a
cap window radius `≳ R √B`, with `B` the unbounded scalar bound near the escape radius), so the cap
predicate is the union over the cap radii `te + 1 + m`:
* `capPtU_O56`: `∃ m, kcapPt_O29 … (fun _ => te + 1 + m) … A s y`;
* `hcap_U_O56`: the K-cap branch for `capPtU_O56` (the K-cap constant `Q` does not depend on `Dcap`);
* `htrace_core_O56`: per-slice non-cap data with cap radii `D i → ∞` ⇒ the traced-buffer premise
  (`htrace`) of `exists_pointed_convergence_at_scalar_escape_of_traced_buffer_kcan_O23` on the slice
  slabs (`chain_traces_of_not_capWindowPoint_of_closedSlab_O3L` + `traced_buffer_of_chain_traces`);
* `htrace_U_O56`: `¬ capPtU_O56` along the sequence ⇒ the same `htrace` (records from
  `P5Linked_O13`, cap scalar bound from `exists_presented_cap_scalar_lower_bound_of_canonical_window_core`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace GC.LongTime.Ch12

universe u

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
  {δ : ℝ → ℝ}

theorem dcapU_pos_O56 (m : ℕ) :
    ∀ _A : ℝ, StandardCap.transitionEnd < StandardCap.transitionEnd + 1 + m := fun _ => by
  have : (0 : ℝ) ≤ m := m.cast_nonneg
  linarith

/-- The union cap predicate (lead ruling O56-1 (a)): `y` is a recent cap point for some cap radius
`te + 1 + m`. -/
def capPtU_O56 (Hp : GC.LongTime.AnalyticSurgeryProfile F δ)
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
            metricScalarAt s.metric z ≤ Q * metricScalarAt s.metric y) :
    ℝ → ∀ s : RegularSlice F.observation, s.stage.Carrier → Prop :=
  fun A s y => ∃ m : ℕ,
    kcapPt_O29 Hp hKcap (fun _ => StandardCap.transitionEnd + 1 + m) (dcapU_pos_O56 m) A s y

/-- The K-cap branch (`hcap` of `hKcan_v2_of_branchesA_O23`) for `capPtU_O56`. -/
theorem hcap_U_O56 (Hp : GC.LongTime.AnalyticSurgeryProfile F δ)
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
            metricScalarAt s.metric z ≤ Q * metricScalarAt s.metric y) :
    ∀ A : ℝ, 0 < A → ∃ Q Λ T : ℝ, 1 ≤ Q ∧ 1 ≤ Λ ∧
      ∀ s : RegularSlice F.observation, T ≤ s.time → ∀ y : s.stage.Carrier,
        (Hp.parameters.neckRadius s.time ^ 2)⁻¹ ≤ metricScalarAt s.metric y →
        Λ ≤ metricScalarAt s.metric y → capPtU_O56 Hp hKcap A s y →
        ∀ z ∈ riemannianBallOf s.metric y (A / Real.sqrt (metricScalarAt s.metric y)),
          metricScalarAt s.metric z ≤ Q * metricScalarAt s.metric y := by
  intro A hA
  have hspec := (hKcap A hA).choose_spec.choose_spec.choose_spec
  refine ⟨(hKcap A hA).choose, 1, 0, hspec.1, le_rfl, ?_⟩
  intro s _ y _ _ hc z hz
  obtain ⟨m, hc⟩ := hc
  have hT' := (hspec.2.2 (StandardCap.transitionEnd + 1 + m) (dcapU_pos_O56 m A)).choose_spec
  simp only [kcapPt_O29, hA, ↓reduceDIte] at hc
  obtain ⟨T₀, hT₀, hT₀s, p, records, hrec, hcp⟩ := hc
  exact hT' s (hT₀.trans hT₀s) T₀ hT₀ hT₀s p records hrec y hcp z hz

/-- **HTRACE core**: non-cap-window data at cap radii `D i → ∞` on the slice slabs give the
traced-buffer premise of the O23 escape theorem at `x i := y i`. -/
theorem htrace_core_O56 (Hp : GC.LongTime.AnalyticSurgeryProfile F δ) (Ctime : ℝ≥0)
    (hP2 : P2_O2 Hp Ctime)
    (s : ℕ → RegularSlice F.observation) (y : ∀ n, (s n).stage.Carrier)
    (hQ : ∀ i, 1 ≤ (sliceSlabR_O3 F (s i)).flow.scalar (s i).time (y i))
    (hq : ∀ i, (Hp.parameters.neckRadius (s i).time ^ 2)⁻¹ ≤
      (sliceSlabR_O3 F (s i)).flow.scalar (s i).time (y i))
    (htime : Tendsto (fun i => (sliceSlabR_O3 F (s i)).flow.scalar (s i).time (y i) * (s i).time)
      atTop atTop)
    {θ : ℝ} (hθ : 0 < θ) (D : ℕ → ℝ) (hD : Tendsto D atTop atTop)
    (hlev : ∀ i, 0 < D i → ∃ (p : CutoffParameters)
      (records : ∀ j : Fin (sliceHistoryR_O3 F (s i)).eventCount,
        (s i).time - θ ≤ (sliceHistoryR_O3 F (s i)).time j.succ →
        GeometricCutoffRecord (sliceHistoryR_O3 F (s i)).toHistory j p),
      (∀ j hj b, ((records j hj).static b).hasCanonicalWindow) ∧
      (∀ j hj b z, ((records j hj).static b).neck.scale / 2 ≤
        metricScalarAt ((records j hj).static b).witness.metric
          (((records j hj).static b).witness.cap z)) ∧
      p.modelAccuracy ≤ 1 / 2 ∧ D i ≤ p.modelRadius ∧
      ¬ ∃ (j : Fin (sliceHistoryR_O3 F (s i)).eventCount)
        (hj : (s i).time - θ ≤ (sliceHistoryR_O3 F (s i)).time j.succ)
        (hl : j.succ ≤ Fin.last (sliceHistoryR_O3 F (s i)).eventCount)
        (B : BackwardPointTrace (sliceHistoryR_O3 F (s i)).toHistory j.succ
          (Fin.last (sliceHistoryR_O3 F (s i)).eventCount) hl (y i))
        (b : ((sliceHistoryR_O3 F (s i)).toHistory.event j).RetainedBoundaryIndex)
        (x : standardCapWindow p.modelRadius),
        B.point j.succ le_rfl hl = ((records j hj).static b).window x ∧ ‖x.val‖ < D i + 1 ∧
          (s i).time - (sliceHistoryR_O3 F (s i)).time j.succ ≤
            θ * (((records j hj).static b).neck.scale)⁻¹) :
    ∀ R ε B : ℝ, 0 < R → 0 < ε → (∀ᶠ i in atTop, ∀ w ∈ riemannianClosedBallOf
        (scaleMetric ((sliceSlabR_O3 F (s i)).flow.scalar (s i).time (y i))
          (zero_lt_one.trans_le (hQ i))
          ((sliceSlabR_O3 F (s i)).endpointTerminalLimitMetric
            ((sliceHistoryR_O3 F (s i)).stage
              (Fin.last (sliceHistoryR_O3 F (s i)).eventCount))).metric)
        ⟨y i, mem_slice_terminalRegularOpen_O51 F (s i) (y i)⟩ (R + ε),
        metricScalarAt ((sliceSlabR_O3 F (s i)).endpointTerminalLimitMetric
          ((sliceHistoryR_O3 F (s i)).stage
            (Fin.last (sliceHistoryR_O3 F (s i)).eventCount))).metric w ≤
          B * (sliceSlabR_O3 F (s i)).flow.scalar (s i).time (y i)) →
      ∃ θ₁ : ℝ, 0 < θ₁ ∧ ∀ᶠ i in atTop,
        ∃ first : Fin ((sliceHistoryR_O3 F (s i)).eventCount + 1),
        (sliceHistoryR_O3 F (s i)).time first ≤
          (s i).time - θ₁ / (sliceSlabR_O3 F (s i)).flow.scalar (s i).time (y i) ∧
        ∀ w ∈ riemannianClosedBallOf
          (scaleMetric ((sliceSlabR_O3 F (s i)).flow.scalar (s i).time (y i))
            (zero_lt_one.trans_le (hQ i))
            ((sliceSlabR_O3 F (s i)).endpointTerminalLimitMetric
              ((sliceHistoryR_O3 F (s i)).stage
                (Fin.last (sliceHistoryR_O3 F (s i)).eventCount))).metric)
          ⟨y i, mem_slice_terminalRegularOpen_O51 F (s i) (y i)⟩ R,
          Nonempty (BackwardPointTrace (sliceHistoryR_O3 F (s i)).toHistory first
            (Fin.last (sliceHistoryR_O3 F (s i)).eventCount) (Fin.le_last first) w.val) := by
  obtain ⟨phi, hphi, hpin⟩ := slice_pinching_O3 Hp
  have hTE := StandardCap.transitionEnd_pos
  refine RetainedCoreHistory.traced_buffer_of_chain_traces (fun i => sliceHistoryR_O3 F (s i))
    (fun i => (s i).time) (fun i => sliceSlabR_O3 F (s i))
    (fun i => ⟨y i, mem_slice_terminalRegularOpen_O51 F (s i) (y i)⟩) hQ (Kc := 1) (lam := 0)
    (Ctime := Ctime) (Phi := phi) hθ D hD htime ?_
  intro i N pp δ' M τ hp0 hδ hch hb hKc hM1 hτ0 hτt hC h4 hDi k hk z hz
  rw [zero_div, zero_add] at hDi
  have hX : 0 ≤ Real.sqrt (8 * M) *
      Real.exp (9 * (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * M) * τ) *
        ∑ k ∈ Finset.range (N + 1), δ' k := by
    have hsum : 0 ≤ ∑ k ∈ Finset.range (N + 1), δ' k :=
      Finset.sum_nonneg fun k hk => (hδ k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))).le
    positivity
  have hDpos : 0 < D i := by linarith
  obtain ⟨p, records, hcan, hscale, hacc, hDm, hnot⟩ := hlev i hDpos
  obtain ⟨hpin1, hpin2, -⟩ := hpin (s i)
  have hqM : (Hp.parameters.neckRadius (s i).time ^ 2)⁻¹ ≤ M := by
    have := hq i
    linarith
  refine chain_traces_of_not_capWindowPoint_of_closedSlab_O3L (sliceHistoryR_O3 F (s i)) rfl
    (sliceSlabR_O3 F (s i)) (sliceSlabR_initial_O3 F (s i)) ((s i).time - θ) (by linarith)
    records hcan hscale hacc hphi hpin1 hpin2
    (sliceHistory_eventSlabsDerivative_O3 Hp (s i) Ctime _ hP2 le_rfl)
    (sliceSlab_derivative_O3 Hp (s i) Ctime _ hP2 le_rfl) hDm le_rfl (y i) hnot
    (Nc := 0) (fun _ => y i) (fun _ => 1) rfl (fun k hk => absurd hk (Nat.not_lt_zero k))
    (fun k hk => absurd hk (Nat.not_lt_zero k)) (Mc := 0) (lamc := 0)
    (fun k hk => absurd hk (Nat.not_lt_zero k)) (by simp)
    N pp δ' M τ hp0 hδ hch hb (by linarith) hqM hM1 hτ0 hτt hC h4 ?_ k hk z hz
  rw [zero_add]
  exact hDi

/-- **HTRACE for the union cap predicate**: along a KL70 sequence of non-`capPtU` centres, the
traced-buffer premise of the O23 escape theorem holds on the slice slabs at `x i := y i`. -/
theorem htrace_U_O56 (Hp : GC.LongTime.AnalyticSurgeryProfile F δ)
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
    (A : ℝ) (hA : 0 < A) (s : ℕ → RegularSlice F.observation) (y : ∀ n, (s n).stage.Carrier)
    (h1 : Tendsto (fun n => (s n).time) atTop atTop)
    (h2 : ∀ n, (Hp.parameters.neckRadius (s n).time ^ 2)⁻¹ ≤ metricScalarAt (s n).metric (y n))
    (h3 : Tendsto (fun n => metricScalarAt (s n).metric (y n)) atTop atTop)
    (h4 : ∀ n, ¬ capPtU_O56 Hp hKcap A (s n) (y n))
    (hQ : ∀ i, 1 ≤ (sliceSlabR_O3 F (s i)).flow.scalar (s i).time (y i)) :
    ∀ R ε B : ℝ, 0 < R → 0 < ε → (∀ᶠ i in atTop, ∀ w ∈ riemannianClosedBallOf
        (scaleMetric ((sliceSlabR_O3 F (s i)).flow.scalar (s i).time (y i))
          (zero_lt_one.trans_le (hQ i))
          ((sliceSlabR_O3 F (s i)).endpointTerminalLimitMetric
            ((sliceHistoryR_O3 F (s i)).stage
              (Fin.last (sliceHistoryR_O3 F (s i)).eventCount))).metric)
        ⟨y i, mem_slice_terminalRegularOpen_O51 F (s i) (y i)⟩ (R + ε),
        metricScalarAt ((sliceSlabR_O3 F (s i)).endpointTerminalLimitMetric
          ((sliceHistoryR_O3 F (s i)).stage
            (Fin.last (sliceHistoryR_O3 F (s i)).eventCount))).metric w ≤
          B * (sliceSlabR_O3 F (s i)).flow.scalar (s i).time (y i)) →
      ∃ θ₁ : ℝ, 0 < θ₁ ∧ ∀ᶠ i in atTop,
        ∃ first : Fin ((sliceHistoryR_O3 F (s i)).eventCount + 1),
        (sliceHistoryR_O3 F (s i)).time first ≤
          (s i).time - θ₁ / (sliceSlabR_O3 F (s i)).flow.scalar (s i).time (y i) ∧
        ∀ w ∈ riemannianClosedBallOf
          (scaleMetric ((sliceSlabR_O3 F (s i)).flow.scalar (s i).time (y i))
            (zero_lt_one.trans_le (hQ i))
            ((sliceSlabR_O3 F (s i)).endpointTerminalLimitMetric
              ((sliceHistoryR_O3 F (s i)).stage
                (Fin.last (sliceHistoryR_O3 F (s i)).eventCount))).metric)
          ⟨y i, mem_slice_terminalRegularOpen_O51 F (s i) (y i)⟩ R,
          Nonempty (BackwardPointTrace (sliceHistoryR_O3 F (s i)).toHistory first
            (Fin.last (sliceHistoryR_O3 F (s i)).eventCount) (Fin.le_last first) w.val) := by
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
  refine htrace_core_O56 Hp Ctime hP2 s y hQ hq htime hθ D hD ?_
  intro n hDn
  have h0 : Pn n 0 := by
    by_contra h0
    simp only [D, h0, ↓reduceIte] at hDn
    exact lt_irrefl _ hDn
  have hDeq : D n = StandardCap.transitionEnd + 1 + (mn n : ℝ) := by simp only [D, h0, ↓reduceIte]
  have hPm : Pn n (mn n) := Nat.findGreatest_spec (Nat.zero_le n) h0
  have hThr := hPm (mn n) le_rfl
  have hT'le : T' (mn n) ≤ (s n).time := (le_max_left _ _).trans hThr
  have hT5le : T5 (mn n) + (hKcap A hA).choose_spec.choose_spec.choose ≤ (s n).time :=
    (le_max_right _ _).trans hThr
  obtain ⟨p, hpd, hpn, hpf, hpc, hRp, hζp, hmp, recs, hlink⟩ := hT5 (mn n) (sliceIndexR_O3 F (s n))
  let H₀ := F.tower.history (sliceIndexR_O3 F (s n))
  let k := sliceStageR_O3 F (s n)
  let records : ∀ i : Fin (sliceHistoryR_O3 F (s n)).eventCount,
      (s n).time - (hKcap A hA).choose_spec.choose_spec.choose ≤
        (sliceHistoryR_O3 F (s n)).time i.succ →
      GeometricCutoffRecord (sliceHistoryR_O3 F (s n)).toHistory i p := fun i hi =>
    H₀.geometricCutoffRecordOfPrefix k
      (recs (Fin.castLE (Nat.le_of_lt_succ k.isLt) i) (by
        have h' : T5 (mn n) ≤ (sliceHistoryR_O3 F (s n)).time i.succ := by linarith
        exact h'))
  have hcan : ∀ i hi b, ((records i hi).static b).hasCanonicalWindow := fun i hi b =>
    linkedCanonicalWindow_hasCanonicalWindow_O2 _ (hlink _ _ b)
  have hm0 : (0 : ℝ) ≤ (mn n : ℝ) := Nat.cast_nonneg _
  have hmodel : StandardCap.transitionEnd + 1 ≤ p.modelRadius := by linarith
  refine ⟨p, records, hcan, fun i hi b z => hsc _ hmodel (hζp.trans (min_le_right _ _)) hmp _
    (hcan i hi b) z, hζp.trans (min_le_left _ _), by rw [hDeq]; linarith, ?_⟩
  rw [hDeq]
  intro hw
  refine h4 n ⟨mn n, ?_⟩
  simp only [kcapPt_O29, hA, ↓reduceDIte]
  exact ⟨(s n).time, hT'le, le_rfl, p, records,
    ⟨hpd, hpn, hpf, hpc, hRp, fun i hi b => hlink _ _ b⟩, hw⟩

end GC.LongTime.Ch12
