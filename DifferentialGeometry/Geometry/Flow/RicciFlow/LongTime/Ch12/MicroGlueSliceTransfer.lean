import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.EnhancedProfileHypotheses
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RetainedCoreHistoryPrefixTransport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HamiltonIveyPinching
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.ExteriorDiskFlow

/-!
# CH12-O3 (helper R1): transfer of profile data to the slice history and slab

For a regular slice `s` of `F.observation`, with `n = ⌈s.time⌉` and `k` the active stage of
`F.tower.history n` at `s.time`, the *slice history* is the retained-core prefix
`(F.tower.history n).prefixAt k` and the *slice slab* is the closed prefix of the stage-`k` flow
from `time k` to `s.time`.  We transfer the profile fields `canonical`, `pinching` and the
hypothesis shape `P2_O2` to these objects.

The reusable kernel is `postData_eq_history_O3`: for `0 ≤ τ ≤ n`, the post-data
`(postStage τ, postMetric τ)` agrees (as a Sigma) with the stage/stage metric of
`F.tower.history n` at its active stage for `τ`.
-/

set_option autoImplicit false

noncomputable section

open Set
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Manifold ContDiff NNReal

namespace GC.LongTime.Ch12

universe u

/-! ## Generic transport along stage/metric identifications -/

theorem stageMetric_transport_O3 {A B : OrientedThreeStage.{u}} (h : A = B) {mA : A.Metric}
    {mB : B.Metric} (hm : HEq mA mB) (Φ : (S : OrientedThreeStage.{u}) → S.Metric → Prop)
    (hA : Φ A mA) : Φ B mB := by
  subst h
  cases eq_of_heq hm
  exact hA

theorem stageMetric_heq_of_index_eq_O3 (K : ObservedHistory.{u}) {i j : Fin (K.eventCount + 1)}
    (h : i = j) (τ : ℝ) : HEq (K.stageMetric i τ) (K.stageMetric j τ) := by
  subst h
  rfl

/-! ## The key identification -/

section Key

variable {P : OrientedThreeStage.{u}} {g : P.Metric}

/-- Post-data at `τ` versus the last stage of `observe τ`. -/
theorem postData_observe_O3 (O : ObservationTower P g) (τ : ℝ) (hτ : 0 ≤ τ) :
    postStage O τ = (O.observe τ hτ).stage (Fin.last (O.observe τ hτ).eventCount) ∧
      HEq (postMetric O τ)
        ((O.observe τ hτ).stageMetric (Fin.last (O.observe τ hτ).eventCount) τ) := by
  have hmax : max τ 0 = τ := max_eq_left hτ
  have hobs : O.observe (max τ 0) (le_max_right τ 0) = O.observe τ hτ := by
    have hsub : (⟨max τ 0, le_max_right τ 0⟩ : {t : ℝ // 0 ≤ t}) = ⟨τ, hτ⟩ :=
      Subtype.ext hmax
    exact congrArg (fun t : {t : ℝ // 0 ≤ t} => O.observe t.val t.property) hsub
  have hm : ∀ {H H' : ObservedHistory.{u}}, H = H' → ∀ a b : ℝ, a = b →
      HEq (H.stageMetric (Fin.last H.eventCount) a)
        (H'.stageMetric (Fin.last H'.eventCount) b) := by
    intro H H' h a b hab
    cases h
    cases hab
    rfl
  refine ⟨?_, hm hobs _ _ hmax⟩
  unfold postStage
  rw [hobs]

/-- **Key lemma.**  For `0 ≤ τ ≤ n`, the post-data at `τ` is the stage data of history `n` at its
active stage for `τ`. -/
theorem postData_eq_history_O3 (O : ObservationTower P g) (n : ℕ) (τ : ℝ) (hτ : 0 ≤ τ)
    (hτn : τ ≤ (n : ℝ)) (j : Fin ((O.history n).eventCount + 1))
    (hj : (O.history n).activeStage ⟨τ, hτ, by rw [O.horizon_eq]; exact hτn⟩ = j) :
    postStage O τ = (O.history n).stage j ∧
      HEq (postMetric O τ) ((O.history n).stageMetric j τ) := by
  obtain ⟨hs0, hm0⟩ := postData_observe_O3 O τ hτ
  let a : Icc (0 : ℝ) (O.history n).horizon := ⟨τ, hτ, by rw [O.horizon_eq]; exact hτn⟩
  have R : (O.observe τ hτ).SamePresentation ((O.history n).restrict a) :=
    O.observe_eq_atIndex n τ hτ hτn
  let ta : Icc (0 : ℝ) ((O.history n).restrict a).horizon :=
    ⟨((O.history n).restrict a).horizon, ((O.history n).restrict a).horizon_nonneg, le_rfl⟩
  have hL : Fin.cast (congrArg (· + 1) R.count_eq) (Fin.last (O.observe τ hτ).eventCount) =
      ((O.history n).restrict a).activeStage ta := by
    rw [((O.history n).restrict a).activeStage_at_horizon]
    exact Fin.ext R.count_eq
  have hact : (O.history n).activeStage ⟨ta.1, ta.2.1, ta.2.2.trans a.2.2⟩ = j := hj
  have hst := R.stage_eq (Fin.last (O.observe τ hτ).eventCount)
  rw [hL] at hst
  have hst2 := (O.history n).restrict_stageAt a ta
  have hmemK : τ ∈ (O.observe τ hτ).stageDomain (Fin.last (O.observe τ hτ).eventCount) := by
    have h := (O.observe τ hτ).activeStage_mem
      ⟨(O.observe τ hτ).horizon, (O.observe τ hτ).horizon_nonneg, le_rfl⟩
    rw [(O.observe τ hτ).activeStage_at_horizon] at h
    exact h
  have hmet := R.metric_heq (Fin.last (O.observe τ hτ).eventCount) τ hmemK
  have hmet2 := (hmet.trans (stageMetric_heq_of_index_eq_O3 _ hL τ)).trans
    ((O.history n).restrict_sliceMetric a ta)
  refine ⟨?_, ?_⟩
  · exact hs0.trans (hst.trans (hst2.trans (congrArg (O.history n).stage hact)))
  · exact hm0.trans (hmet2.trans (stageMetric_heq_of_index_eq_O3 _ hact τ))

/-- Sigma form of the key lemma. -/
theorem postData_sigma_eq_history_O3 (O : ObservationTower P g) (n : ℕ) (τ : ℝ) (hτ : 0 ≤ τ)
    (hτn : τ ≤ (n : ℝ)) :
    (⟨postStage O τ, postMetric O τ⟩ : Σ Q : OrientedThreeStage.{u}, Q.Metric) =
      ⟨(O.history n).stage
          ((O.history n).activeStage ⟨τ, hτ, by rw [O.horizon_eq]; exact hτn⟩),
        (O.history n).stageMetric
          ((O.history n).activeStage ⟨τ, hτ, by rw [O.horizon_eq]; exact hτn⟩) τ⟩ := by
  obtain ⟨h1, h2⟩ := postData_eq_history_O3 O n τ hτ hτn _ rfl
  exact Sigma.ext h1 h2

end Key

/-! ## Slice history and slice slab -/

section Slice

variable {P : OrientedThreeStage.{u}} {g : P.Metric} (F : GC.Interface.RawSurgery P g)

/-- The history index `⌈s.time⌉`. -/
def sliceIndexR_O3 (s : RegularSlice F.observation) : ℕ := Nat.ceil s.time

/-- The slice time inside history `⌈s.time⌉`. -/
def sliceTimeR_O3 (s : RegularSlice F.observation) :
    Icc (0 : ℝ) (F.tower.history (sliceIndexR_O3 F s)).toHistory.horizon :=
  ⟨s.time, s.positive.le, by
    change s.time ≤ (F.tower.history (sliceIndexR_O3 F s)).horizon
    rw [F.tower.horizon_eq]; exact Nat.le_ceil _⟩

/-- The active stage at the slice time. -/
def sliceStageR_O3 (s : RegularSlice F.observation) :
    Fin ((F.tower.history (sliceIndexR_O3 F s)).eventCount + 1) :=
  (F.tower.history (sliceIndexR_O3 F s)).toHistory.activeStage (sliceTimeR_O3 F s)

theorem slice_precedingR_O3 (s : RegularSlice F.observation) :
    (F.tower.history (sliceIndexR_O3 F s)).time (sliceStageR_O3 F s) < s.time :=
  s.preceding

/-- The slice history: the retained-core prefix up to the active stage. -/
def sliceHistoryR_O3 (s : RegularSlice F.observation) : RetainedCoreHistory.{u} :=
  (F.tower.history (sliceIndexR_O3 F s)).prefixAt (sliceStageR_O3 F s)

/-- The slice slab: the stage flow from the last surgery time to `s.time`. -/
def sliceSlabR_O3 (s : RegularSlice F.observation) :
    ((sliceHistoryR_O3 F s).stage (Fin.last (sliceHistoryR_O3 F s).eventCount)).ClosedSlab
      ((sliceHistoryR_O3 F s).time (Fin.last (sliceHistoryR_O3 F s).eventCount)) s.time :=
  (F.tower.history (sliceIndexR_O3 F s)).toHistory.closedPrefixAt (sliceTimeR_O3 F s)
    (slice_precedingR_O3 F s)

theorem sliceSlabR_metric_O3 (s : RegularSlice F.observation) (τ : ℝ) :
    (sliceSlabR_O3 F s).flow.base.metric τ =
      (F.tower.history (sliceIndexR_O3 F s)).toHistory.stageMetric (sliceStageR_O3 F s) τ :=
  (F.tower.history (sliceIndexR_O3 F s)).toHistory.closedPrefixAt_metric _ _ τ

/-- On `[time k, s.time]` the active stage of history `⌈s.time⌉` is `k`. -/
theorem slice_activeStage_O3 (s : RegularSlice F.observation) (τ : ℝ)
    (h1 : (F.tower.history (sliceIndexR_O3 F s)).time (sliceStageR_O3 F s) ≤ τ)
    (h2 : τ ≤ s.time) :
    (F.observation.history (sliceIndexR_O3 F s)).activeStage
      ⟨τ, ((F.tower.history (sliceIndexR_O3 F s)).toHistory.time_nonneg _).trans h1, by
        rw [F.observation.horizon_eq]; exact h2.trans (Nat.le_ceil _)⟩ = sliceStageR_O3 F s := by
  apply ObservedHistory.activeStage_eq_of_maximal _ _ _ h1
  intro k hk
  exact (F.tower.history (sliceIndexR_O3 F s)).toHistory.le_activeStage (sliceTimeR_O3 F s) k
    (hk.trans h2)

/-- Post-data on `[time k, s.time]` is the slab data. -/
theorem postData_slice_O3 (s : RegularSlice F.observation) (τ : ℝ)
    (h1 : (F.tower.history (sliceIndexR_O3 F s)).time (sliceStageR_O3 F s) ≤ τ)
    (h2 : τ ≤ s.time) :
    postStage F.observation τ =
        (sliceHistoryR_O3 F s).stage (Fin.last (sliceHistoryR_O3 F s).eventCount) ∧
      HEq (postMetric F.observation τ) ((sliceSlabR_O3 F s).flow.base.metric τ) := by
  rw [sliceSlabR_metric_O3]
  exact postData_eq_history_O3 F.observation (sliceIndexR_O3 F s) τ
    (((F.tower.history (sliceIndexR_O3 F s)).toHistory.time_nonneg _).trans h1)
    (h2.trans (Nat.le_ceil _)) _ (slice_activeStage_O3 F s τ h1 h2)

/-! ### T0 -/

theorem sliceSlabR_initial_O3 (s : RegularSlice F.observation) :
    (sliceSlabR_O3 F s).flow.base.metric
        ((sliceHistoryR_O3 F s).time (Fin.last (sliceHistoryR_O3 F s).eventCount)) =
      (sliceHistoryR_O3 F s).initialMetric (Fin.last (sliceHistoryR_O3 F s).eventCount) :=
  (F.tower.history (sliceIndexR_O3 F s)).toHistory.closedPrefixAt_initial _ _

theorem sliceHistoryR_stage_O3 (s : RegularSlice F.observation) :
    (sliceHistoryR_O3 F s).stage (Fin.last (sliceHistoryR_O3 F s).eventCount) = s.stage := rfl

theorem sliceSlabR_metric_time_O3 (s : RegularSlice F.observation) :
    (sliceSlabR_O3 F s).flow.base.metric s.time = s.metric := by
  unfold RegularSlice.metric ObservedHistory.stageMetric
  simp only [Fin.lastCases_last]
  have h : s.history.time (Fin.last s.history.eventCount) < s.history.horizon := s.preceding
  rw [dite_eq_left_of_eq_true (eq_true h)]
  rfl

end Slice

/-! ## Profile transfer (T1–T5) -/

section Profile

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
  {δ : ℝ → ℝ}

theorem neckThreshold_mono_O3 (Hp : GC.LongTime.AnalyticSurgeryProfile F δ) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) :
    (Hp.parameters.neckRadius a ^ 2)⁻¹ ≤ (Hp.parameters.neckRadius b ^ 2)⁻¹ := by
  have hb : 0 ≤ b := ha.trans hab
  have hr := Hp.radius_antitone (show a ∈ Ici 0 from ha) (show b ∈ Ici 0 from hb) hab
  have hr0 := Hp.parameters.neckRadius_pos _ hb
  exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hr0.le hr 2)

/-- **T1**: canonical witnesses on the slice slab at the slice time. -/
theorem sliceSlab_canonical_O3 (Hp : GC.LongTime.AnalyticSurgeryProfile F δ)
    (s : RegularSlice F.observation) :
    ∀ x, (Hp.parameters.neckRadius s.time ^ 2)⁻¹ < (sliceSlabR_O3 F s).flow.scalar s.time x →
      ∃ W : SpatialCanonicalWitness ((sliceSlabR_O3 F s).flow.base.metric s.time)
          Hp.epsilon Hp.C1 Hp.C2 x, W.capTubeHasNeckChart Hp.epsilon := by
  obtain ⟨hst, hm⟩ := postData_slice_O3 F s s.time (slice_precedingR_O3 F s).le le_rfl
  exact stageMetric_transport_O3 hst hm
    (fun Q m => ∀ x : Q.Carrier, (Hp.parameters.neckRadius s.time ^ 2)⁻¹ < metricScalarAt m x →
      ∃ W : SpatialCanonicalWitness m Hp.epsilon Hp.C1 Hp.C2 x,
        W.capTubeHasNeckChart Hp.epsilon)
    (Hp.canonical s.time s.positive.le)

/-- **T2**: event-slab derivative bounds on the slice history. -/
theorem sliceHistory_eventSlabsDerivative_O3 (Hp : GC.LongTime.AnalyticSurgeryProfile F δ)
    (s : RegularSlice F.observation) (Ctime : ℝ≥0) (q : ℝ) (hP2 : P2_O2 Hp Ctime)
    (hq : (Hp.parameters.neckRadius s.time ^ 2)⁻¹ ≤ q) :
    (sliceHistoryR_O3 F s).EventSlabsDerivative Ctime q
      (Fin.last (sliceHistoryR_O3 F s).eventCount) := by
  apply RetainedCoreHistory.eventSlabsDerivative_prefixAt
  intro j hj y τ hτ hqy
  have hjs : (F.tower.history (sliceIndexR_O3 F s)).time j.succ ≤ s.time := by
    have h1 : (F.tower.history (sliceIndexR_O3 F s)).time j.succ ≤
        (F.tower.history (sliceIndexR_O3 F s)).time (sliceStageR_O3 F s) :=
      (F.tower.history (sliceIndexR_O3 F s)).time_strictMono.monotone
        (Fin.castSucc_lt_iff_succ_le.mp hj)
    exact h1.trans (slice_precedingR_O3 F s).le
  refine eventSlab_derivative_of_P2_O2 Hp hP2 _ j q ?_ y τ hτ hqy
  exact (neckThreshold_mono_O3 Hp
    ((F.tower.history (sliceIndexR_O3 F s)).toHistory.time_nonneg _) hjs).trans hq

/-- P2 on a single stage of history `n`, for times before `t` (`t` at most the next event). -/
theorem stage_scalar_deriv_O3 (Hp : GC.LongTime.AnalyticSurgeryProfile F δ) {Ctime : ℝ≥0}
    (hP2 : P2_O2 Hp Ctime) (n : ℕ) (k : Fin ((F.tower.history n).eventCount + 1)) (t : ℝ)
    (hkt : (F.tower.history n).time k < t) (ht : t ≤ (F.tower.history n).horizon)
    (hnext : ∀ i : Fin (F.tower.history n).eventCount, k = i.castSucc →
      t ≤ (F.tower.history n).time i.succ)
    (y : ((F.tower.history n).stage k).Carrier) (τ : ℝ)
    (hτ : τ ∈ Ioo ((F.tower.history n).time k) t)
    (hq : (Hp.parameters.neckRadius τ ^ 2)⁻¹ <
      metricScalarAt ((F.tower.history n).toHistory.stageMetric k τ) y) :
    |derivWithin (fun v => metricScalarAt ((F.tower.history n).toHistory.stageMetric k v) y)
        (Iic τ) τ| ≤
      Ctime * metricScalarAt ((F.tower.history n).toHistory.stageMetric k τ) y ^ 2 := by
  cases k using Fin.lastCases with
  | last =>
    have hf : (F.tower.history n).time (Fin.last (F.tower.history n).eventCount) <
        (F.tower.history n).horizon := hkt.trans_le ht
    simp only [ObservedHistory.stageMetric, Fin.lastCases_last, dite_eq_left hf] at hq ⊢
    exact hP2.2 n hf y τ ⟨hτ.1, hτ.2.trans_le ht⟩ hq
  | cast i =>
    simp only [ObservedHistory.stageMetric_castSucc_apply] at hq ⊢
    exact hP2.1 n i y τ ⟨hτ.1, hτ.2.trans_le (hnext i rfl)⟩ hq

theorem slice_next_O3 (s : RegularSlice F.observation)
    (i : Fin (F.tower.history (sliceIndexR_O3 F s)).eventCount)
    (hi : sliceStageR_O3 F s = i.castSucc) :
    s.time ≤ (F.tower.history (sliceIndexR_O3 F s)).time i.succ := by
  have hk : (sliceStageR_O3 F s).val < (F.tower.history (sliceIndexR_O3 F s)).eventCount := by
    rw [hi]; exact i.isLt
  have hn := (F.tower.history (sliceIndexR_O3 F s)).toHistory.activeStage_before_next
    (sliceTimeR_O3 F s) hk
  have he : (⟨(sliceStageR_O3 F s).val + 1, by omega⟩ :
      Fin ((F.tower.history (sliceIndexR_O3 F s)).eventCount + 1)) = i.succ := by
    apply Fin.ext
    have hv : (sliceStageR_O3 F s).val = i.val := congrArg Fin.val hi
    simp only [Fin.val_succ]
    omega
  have hn' : s.time < (F.tower.history (sliceIndexR_O3 F s)).time
      ⟨(sliceStageR_O3 F s).val + 1, by omega⟩ := hn
  rw [he] at hn'
  exact hn'.le

/-- **T3**: the scalar time-derivative bound on the (incoming) slice slab. -/
theorem sliceSlab_derivative_O3 (Hp : GC.LongTime.AnalyticSurgeryProfile F δ)
    (s : RegularSlice F.observation) (Ctime : ℝ≥0) (q : ℝ) (hP2 : P2_O2 Hp Ctime)
    (hq : (Hp.parameters.neckRadius s.time ^ 2)⁻¹ ≤ q) :
    ((sliceSlabR_O3 F s).restrictIncoming le_rfl (sliceSlabR_O3 F s).lt le_rfl).DerivativeBoundBefore
      Ctime q s.time := by
  intro y τ hτ hqy
  have hfun : ∀ v, ((sliceSlabR_O3 F s).restrictIncoming le_rfl (sliceSlabR_O3 F s).lt
      le_rfl).flow.scalar v y =
      metricScalarAt ((F.tower.history (sliceIndexR_O3 F s)).toHistory.stageMetric
        (sliceStageR_O3 F s) v) y := fun v => by
    change metricScalarAt ((sliceSlabR_O3 F s).flow.base.metric v) y = _
    exact congrArg (fun m => metricScalarAt m y) (sliceSlabR_metric_O3 F s v)
  simp only [hfun] at hqy ⊢
  have hτ0 : 0 ≤ τ :=
    ((F.tower.history (sliceIndexR_O3 F s)).toHistory.time_nonneg _).trans hτ.1.le
  exact stage_scalar_deriv_O3 Hp hP2 (sliceIndexR_O3 F s) (sliceStageR_O3 F s) s.time
    (slice_precedingR_O3 F s) (sliceTimeR_O3 F s).2.2 (slice_next_O3 s) y τ hτ
    (((neckThreshold_mono_O3 Hp hτ0 hτ.2.le).trans hq).trans_lt hqy)

/-- **T4**: the scalar gradient bound on the (incoming) slice slab, from the witnesses'
`gradient` field at the earlier times. -/
theorem sliceSlab_gradient_O3 (Hp : GC.LongTime.AnalyticSurgeryProfile F δ)
    (s : RegularSlice F.observation) (q : ℝ)
    (hq : (Hp.parameters.neckRadius s.time ^ 2)⁻¹ ≤ q) :
    ((sliceSlabR_O3 F s).restrictIncoming le_rfl (sliceSlabR_O3 F s).lt le_rfl).GradientBoundBefore
      ⟨Hp.C2, by linarith [Hp.C2_ge_one]⟩ q s.time := by
  intro y τ hτ hqy v
  have hτ0 : 0 ≤ τ :=
    ((F.tower.history (sliceIndexR_O3 F s)).toHistory.time_nonneg _).trans hτ.1.le
  obtain ⟨hst, hm⟩ := postData_slice_O3 F s τ hτ.1.le hτ.2.le
  have key := stageMetric_transport_O3 hst hm
    (fun Q m => ∀ x : Q.Carrier, (Hp.parameters.neckRadius τ ^ 2)⁻¹ < metricScalarAt m x →
      ∀ w : TangentSpace I3 x, |(show ℝ from mfderiv I3 𝓘(ℝ, ℝ) (metricScalarAt m) x w)| ≤
        Hp.C2 * metricScalarAt m x * Real.sqrt (metricScalarAt m x) *
          Real.sqrt (m.inner x w w))
    (fun x hx w => by
      obtain ⟨W, -⟩ := Hp.canonical τ hτ0 x hx
      exact W.gradient w)
  exact key y (((neckThreshold_mono_O3 Hp hτ0 hτ.2.le).trans hq).trans_lt hqy) v

/-- Fixed Hamilton–Ivey region for the stage metrics of every history of the tower. -/
theorem history_region_O3 (Hp : GC.LongTime.AnalyticSurgeryProfile F δ) (n : ℕ) (τ : ℝ)
    (hτ : 0 ≤ τ) (hτn : τ ≤ (n : ℝ)) (j : Fin ((F.tower.history n).eventCount + 1))
    (hj : (F.observation.history n).activeStage
      ⟨τ, hτ, by rw [F.observation.horizon_eq]; exact hτn⟩ = j) :
    ∀ x, InFixedHamiltonIveyRegion ((F.tower.history n).toHistory.stageMetric j τ)
      (Hp.pinchingShift + τ) x := by
  obtain ⟨hst, hm⟩ := postData_eq_history_O3 F.observation n τ hτ hτn j hj
  exact stageMetric_transport_O3 hst hm
    (fun Q m => ∀ x : Q.Carrier, InFixedHamiltonIveyRegion m (Hp.pinchingShift + τ) x)
    (Hp.pinching τ hτ)

/-- Fixed Hamilton–Ivey region on the slice slab, on the closed interval. -/
theorem slice_region_O3 (Hp : GC.LongTime.AnalyticSurgeryProfile F δ)
    (s : RegularSlice F.observation) (τ : ℝ)
    (h1 : (F.tower.history (sliceIndexR_O3 F s)).time (sliceStageR_O3 F s) ≤ τ)
    (h2 : τ ≤ s.time) :
    ∀ x, InFixedHamiltonIveyRegion ((sliceSlabR_O3 F s).flow.base.metric τ)
      (Hp.pinchingShift + τ) x := by
  obtain ⟨hst, hm⟩ := postData_slice_O3 F s τ h1 h2
  exact stageMetric_transport_O3 hst hm
    (fun Q m => ∀ x : Q.Carrier, InFixedHamiltonIveyRegion m (Hp.pinchingShift + τ) x)
    (Hp.pinching τ (((F.tower.history (sliceIndexR_O3 F s)).toHistory.time_nonneg _).trans h1))

/-- **T5**: one admissible pinching function `phi` (depending only on the profile) such that every
slice history has pinched event slabs and the slice slab is `phi`-almost nonnegative on the closed
interval `[time last, s.time]` (and its incoming restriction on `[time last, s.time)`). -/
theorem slice_pinching_O3 (Hp : GC.LongTime.AnalyticSurgeryProfile F δ) :
    ∃ phi : ℝ → ℝ, AdmissiblePinchingFunction phi ∧
      ∀ s : RegularSlice F.observation,
        (sliceHistoryR_O3 F s).EventSlabsPinched phi ∧
        PhiAlmostNonnegative (sliceSlabR_O3 F s).flow
          (Icc ((sliceHistoryR_O3 F s).time (Fin.last (sliceHistoryR_O3 F s).eventCount))
            s.time) phi ∧
        PhiAlmostNonnegative
          ((sliceSlabR_O3 F s).restrictIncoming le_rfl (sliceSlabR_O3 F s).lt le_rfl).flow
          (Ico ((sliceHistoryR_O3 F s).time (Fin.last (sliceHistoryR_O3 F s).eventCount))
            s.time) phi := by
  obtain ⟨phi, hadm, hphi⟩ :=
    exists_admissiblePinchingFunction_phiAlmostNonnegative_of_fixedHamiltonIveyRegion.{u}
      Hp.pinchingShift_pos
  have hall : ∀ n, (F.tower.history n).EventSlabsPinched phi := by
    intro n j
    refine hphi _ _ _ _ (fun τ => Hp.pinchingShift + τ) ?_ ?_
    · intro τ hτ
      have : 0 ≤ τ := ((F.tower.history n).toHistory.time_nonneg _).trans hτ.1
      change Hp.pinchingShift ≤ Hp.pinchingShift + τ
      linarith
    · intro τ hτ x
      have hτ0 : 0 ≤ τ := ((F.tower.history n).toHistory.time_nonneg _).trans hτ.1
      have hτn : τ ≤ (n : ℝ) := by
        have h1 : (F.tower.history n).time j.succ ≤ (F.tower.history n).horizon :=
          (F.tower.history n).toHistory.time_le_horizon_at j.succ
        have h2 : (F.tower.history n).horizon = n := F.tower.horizon_eq n
        linarith [hτ.2]
      have hact : (F.observation.history n).activeStage
          ⟨τ, hτ0, by rw [F.observation.horizon_eq]; exact hτn⟩ = j.castSucc := by
        apply ObservedHistory.activeStage_eq_of_maximal _ _ _ hτ.1
        intro k hk
        have hlt : k < j.succ := (F.tower.history n).time_strictMono.lt_iff_lt.mp
          (hk.trans_lt hτ.2)
        exact Fin.le_castSucc_iff.mpr hlt
      have h := history_region_O3 Hp n τ hτ0 hτn j.castSucc hact x
      rw [ObservedHistory.stageMetric_castSucc_apply] at h
      exact h
  refine ⟨phi, hadm, fun s => ⟨?_, ?_, ?_⟩⟩
  · exact RetainedCoreHistory.eventSlabsPinched_prefixAt _ _ (hall _)
  · refine hphi _ _ _ _ (fun τ => Hp.pinchingShift + τ) ?_ ?_
    · intro τ hτ
      have : 0 ≤ τ :=
        ((F.tower.history (sliceIndexR_O3 F s)).toHistory.time_nonneg _).trans hτ.1
      change Hp.pinchingShift ≤ Hp.pinchingShift + τ
      linarith
    · intro τ hτ x
      exact slice_region_O3 Hp s τ hτ.1 hτ.2 x
  · refine hphi _ _ _ _ (fun τ => Hp.pinchingShift + τ) ?_ ?_
    · intro τ hτ
      have : 0 ≤ τ :=
        ((F.tower.history (sliceIndexR_O3 F s)).toHistory.time_nonneg _).trans hτ.1
      change Hp.pinchingShift ≤ Hp.pinchingShift + τ
      linarith
    · intro τ hτ x
      exact slice_region_O3 Hp s τ hτ.1 hτ.2.le x

end Profile

end GC.LongTime.Ch12
