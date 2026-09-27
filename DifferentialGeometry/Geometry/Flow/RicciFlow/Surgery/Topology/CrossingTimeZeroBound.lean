import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CrossingBaseSliceBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CrossingTracedRegion
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RetainedCoreHistoryExtendAtBefore
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegionTimeZeroScalarBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegionDepthInduction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegionMaximalDepth

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Metric
open scoped Manifold ContDiff NNReal Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace RetainedCoreHistory

theorem scalar_ball_bound_extendAt_iff {P₀ : OrientedThreeStage.{u}} (H : RetainedCoreHistory P₀)
    (hend : H.time (Fin.last H.eventCount) = H.horizon) {s : ℝ}
    (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s)
    (hG : G.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount)) {t : ℝ}
    (hat : H.time (Fin.last H.eventCount) < t) (hts : t < s)
    (y : (H.stage (Fin.last H.eventCount)).Carrier)
    (ŷ : ((H.extendAt hend G hG hat hts).toHistory.stageAt
      (H.extendAtTime hend G hG hat hts)).Carrier) (hŷ : HEq ŷ y) (ρ M : ℝ) :
    (∀ x ∈ riemannianBallOf ((H.extendAt hend G hG hat hts).toHistory.stageMetric
        ((H.extendAt hend G hG hat hts).toHistory.activeStage
          (H.extendAtTime hend G hG hat hts)) (H.extendAtTime hend G hG hat hts)) ŷ ρ,
      metricScalarAt ((H.extendAt hend G hG hat hts).toHistory.stageMetric
        ((H.extendAt hend G hG hat hts).toHistory.activeStage
          (H.extendAtTime hend G hG hat hts)) (H.extendAtTime hend G hG hat hts)) x ≤ M) ↔
      ∀ x ∈ riemannianBallOf (G.flow.base.metric t) y ρ, G.flow.scalar t x ≤ M := by
  have hlast : (H.extendAt hend G hG hat hts).toHistory.activeStage
      (H.extendAtTime hend G hG hat hts) = Fin.last H.eventCount :=
    H.activeStage_extendHorizon_eq_last (hend ▸ hat.le) (G.closedPrefix t hat hts) hG
      (H.extendAtTime hend G hG hat hts) hat.le
  have hmet : (H.extendAt hend G hG hat hts).toHistory.stageMetric (Fin.last H.eventCount)
      (H.extendAtTime hend G hG hat hts) = G.flow.base.metric t :=
    H.stageMetric_extendHorizon_last_of_mem_Icc (hend ▸ hat.le) (G.closedPrefix t hat hts) hG
      ⟨hat.le, le_rfl⟩
  revert ŷ
  change ∀ ŷ : ((H.extendAt hend G hG hat hts).toHistory.stage
      ((H.extendAt hend G hG hat hts).toHistory.activeStage
        (H.extendAtTime hend G hG hat hts))).Carrier, HEq ŷ y → _
  generalize (H.extendAt hend G hG hat hts).toHistory.activeStage
    (H.extendAtTime hend G hG hat hts) = k at hlast ⊢
  subst hlast
  intro ŷ hŷ
  obtain rfl := eq_of_heq hŷ
  rw [hmet]
  rfl

variable {P₀ : OrientedThreeStage.{u}} {g₀ : P₀.Metric}
  {B ε C1 C2 τmin θ κ C1s C2s Cs : ℝ} {Ctime Cgrad : ℝ≥0} {phi : ℝ → ℝ}
  {D θcap qcan qs η t₀ t s : ℕ → ℝ} {p₀ p : ℕ → CutoffParameters} {δb ρb : ℕ → ℝ}
  {H : ℕ → RetainedCoreHistory P₀}
  {records : ∀ n i, GeometricCutoffRecord (H n).toHistory i (p n)}
  {G : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).IncomingSlab
    ((H n).time (Fin.last (H n).eventCount)) (s n)}
  {y : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).Carrier}
  (hε : 0 < ε) (hεcone : ε ≤ coneAccuracy)
  (hκ : 0 < κ) (hphi : Perelman.AdmissiblePinchingFunction phi) (hθ : 0 < θ)
  (hCs : 1 ≤ Cs) (hCt : 0 < Ctime)
  (hH : ∀ n, (H n).InCutoffClass g₀ B (p₀ n) (δb n) (ρb n))
  (hG : ∀ n, (H n).IsContinuationSlab B (Fin.last (H n).eventCount) (G n))
  (hrec : ∀ n, (H n).IsCanonicalCutoffRecordFamily (p₀ n) (δb n) (ρb n) (records n))
  (hq : ∀ n : ℕ, (n : ℝ) + 1 ≤ qcan n ∧ qcan n ≤ qs n ∧ qs n ≤ Cs * qcan n)
  (hpar : ∀ n : ℕ, (p₀ n).modelAccuracy ≤ 1 / ((n : ℝ) + 1) ∧ (n : ℝ) + 1 ≤ D n ∧
    D n ≤ (p₀ n).modelRadius ∧ n + 2 ≤ (p₀ n).modelOrder ∧ δb n ≤ 1 / ((n : ℝ) + 1))
  (hscale : ∀ (n : ℕ) i b, ((n : ℝ) + 1) * qcan n ≤ ((records n i).static b).neck.scale)
  (hθcap : ∀ n : ℕ, 1 - 1 / ((n : ℝ) + 2) ≤ θcap n)
  (hpinch : ∀ n, (H n).EventSlabsPinched phi ∧
    Perelman.PhiAlmostNonnegative (G n).flow
      (Ico ((H n).time (Fin.last (H n).eventCount)) (s n)) phi)
  (hslabs : ∀ n,
    (H n).EventSlabsCanonical ε C1 C2 (qcan n) τmin (Fin.last (H n).eventCount) ∧
    (H n).EventSlabsDerivative Ctime (qcan n) (Fin.last (H n).eventCount) ∧
    (H n).EventSlabsGradient Cgrad (qcan n) (Fin.last (H n).eventCount) ∧
    (H n).EventSlabsSpatiallyCanonical ε C1s C2s (qs n) (Fin.last (H n).eventCount) ∧
    (H n).NoncollapsedBefore κ ε ((H n).time (Fin.last (H n).eventCount)))
  (hbefore : ∀ n, t₀ n ∈ Ico ((H n).time (Fin.last (H n).eventCount)) (s n) ∧
    (G n).CanonicalBefore ε C1 C2 (qcan n) τmin (t₀ n) ∧
    (G n).DerivativeBoundBefore Ctime (qcan n) (t₀ n) ∧
    (G n).GradientBoundBefore Cgrad (qcan n) (t₀ n) ∧
    (G n).SpatiallyCanonicalBefore ε C1s C2s (qs n) (t₀ n) ∧
    (H n).TerminalNoncollapsedBefore (hH n).2.1 (G n) (hG n).2 κ ε (t₀ n))
  (hsliver : ∀ n, 0 < η n ∧ t₀ n + η n < s n ∧
    (G n).DerivativeBoundBefore (2 * Ctime) (2 * qcan n) (t₀ n + η n) ∧
    (∀ t' ∈ Icc (t₀ n) (t₀ n + η n), ∀ x, (G n).flow.scalar t' x * η n ≤ 1 / ((n : ℝ) + 1) ∧
      |(G n).flow.scalar t' x - (G n).flow.scalar (t₀ n) x| ≤ qcan n / 4 ∧
      ∀ v : TangentSpace ThreeModel x,
        ((G n).flow.base.metric t').inner x v v ≤
          Real.exp 1 * ((G n).flow.base.metric (t₀ n)).inner x v v ∧
        ((G n).flow.base.metric (t₀ n)).inner x v v ≤
          Real.exp 1 * ((G n).flow.base.metric t').inner x v v) ∧
    ∀ i b, ((records n i).static b).neck.scale * η n ≤ 1 / ((n : ℝ) + 2))
  (hbad : ∀ n, (H n).time (Fin.last (H n).eventCount) < t n ∧ t₀ n ≤ t n ∧
    t n < t₀ n + η n ∧ qcan n < (G n).flow.scalar (t n) (y n) ∧
    (G n).flow.scalar (t n) (y n) * (t n - (H n).time (Fin.last (H n).eventCount)) < θ ∧
    ¬ (H n).CapWindowPoint (records n) (Fin.last (H n).eventCount) (y n) (t n) (D n) (θcap n))

include hphi hH hG hrec hq hpar hscale hθcap hpinch hslabs hsliver hbad in
theorem exists_eventually_isTracedRegion_extendAt_of_scalar_le_on_ball {A T Q : ℝ}
    (hA : 0 < A) (hT : 0 < T) (hQ : 2 ≤ Q) (hstep : 4 * (Ctime : ℝ) * Q * T ≤ 1) :
    ∃ K₀ : ℝ, 0 ≤ K₀ ∧
      ∀ ŷ : ∀ n, (((H n).extendAt (hH n).2.1 (G n) (hG n).2 (hbad n).1
          ((hbad n).2.2.1.trans (hsliver n).2.1)).toHistory.stageAt
          ((H n).extendAtTime (hH n).2.1 (G n) (hG n).2 (hbad n).1
            ((hbad n).2.2.1.trans (hsliver n).2.1))).Carrier,
      (∀ n, HEq (ŷ n) (y n)) → ∀ᶠ n in atTop,
        (∀ z ∈ riemannianBallOf ((G n).flow.base.metric (t n)) (y n)
            (A / Real.sqrt ((G n).flow.scalar (t n) (y n))),
          (G n).flow.scalar (t n) z ≤ Q * (G n).flow.scalar (t n) (y n)) →
        ((H n).extendAt (hH n).2.1 (G n) (hG n).2 (hbad n).1
          ((hbad n).2.2.1.trans (hsliver n).2.1)).toHistory.isTracedRegion
          ((H n).extendAtTime (hH n).2.1 (G n) (hG n).2 (hbad n).1
            ((hbad n).2.2.1.trans (hsliver n).2.1)) (ŷ n)
          (A / Real.sqrt ((G n).flow.scalar (t n) (y n)))
          (T / (G n).flow.scalar (t n) (y n)) (K₀ * (G n).flow.scalar (t n) (y n)) := by
  obtain ⟨K₀, hK₀, hev⟩ :=
    exists_eventually_isTracedRegion_extendAt_of_scalar_le_along_traces hphi (fun n => (hH n).1)
      (fun n => (hH n).2.1) (fun n => (hG n).2) hrec (fun n => (hq n).1) hpar hscale hθcap hpinch
      (fun n => (hslabs n).2.1) (fun n => (hbad n).1)
      (fun n => (hbad n).2.2.1.trans (hsliver n).2.1)
      (fun n => (G n).derivativeBoundBefore_mono (hbad n).2.2.1.le (hsliver n).2.2.1)
      (fun n => (hbad n).2.2.2.1) (fun n => (hbad n).2.2.2.2.2)
      (A := A) (T := T) (Q := Q) hA hT (by linarith)
  have hRt := tendsto_scalar_mul_time_atTop_of_inCutoffClass (B := fun _ => B) hH G
    (fun n => (hG n).2) y (fun n => ⟨(hbad n).1.le, (hbad n).2.2.1.trans (hsliver n).2.1⟩)
    (tendsto_scalar_at_bad_point_atTop hq hbad)
  refine ⟨K₀, hK₀, fun ŷ hŷ => ?_⟩
  filter_upwards [hev, hRt.eventually_gt_atTop T] with n hn hRtn hQn
  have hR0 : 0 < (G n).flow.scalar (t n) (y n) :=
    (lt_of_lt_of_le (by positivity) (hq n).1).trans (hbad n).2.2.2.1
  have hut0 : 0 ≤ t n - T / (G n).flow.scalar (t n) (y n) := by
    rw [sub_nonneg, div_le_iff₀ hR0]
    linarith
  let uu : Icc (0 : ℝ) ((H n).extendAt (hH n).2.1 (G n) (hG n).2 (hbad n).1
      ((hbad n).2.2.1.trans (hsliver n).2.1)).toHistory.horizon :=
    ⟨t n - T / (G n).flow.scalar (t n) (y n), hut0,
      show t n - T / (G n).flow.scalar (t n) (y n) ≤ t n from sub_le_self _ (div_pos hT hR0).le⟩
  refine hn (ŷ n) (hŷ n) uu rfl ?_
  have hdin := (H n).derivativeBound_inputs_extendAt (hH n).2.1 (G n) (hG n).2 (hbad n).1
    ((hbad n).2.2.1.trans (hsliver n).2.1)
    (by linarith [(hq n).1, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]) (hslabs n).2.1
    ((G n).derivativeBoundBefore_mono (hbad n).2.2.1.le (hsliver n).2.2.1)
  have hball := (RetainedCoreHistory.scalar_ball_bound_extendAt_iff (H n) (hH n).2.1 (G n)
    (hG n).2 (hbad n).1 ((hbad n).2.2.1.trans (hsliver n).2.1) (y n) (ŷ n) (hŷ n)
    (A / Real.sqrt ((G n).flow.scalar (t n) (y n))) (Q * (G n).flow.scalar (t n) (y n))).mpr hQn
  have hstep' : 2 * ((2 * Ctime : ℝ≥0) : ℝ) * Q * T ≤ 1 := by
    push_cast
    linarith
  have hut : uu ≤ (H n).extendAtTime (hH n).2.1 (G n) (hG n).2 (hbad n).1
      ((hbad n).2.2.1.trans (hsliver n).2.1) :=
    show t n - T / (G n).flow.scalar (t n) (y n) ≤ t n from sub_le_self _ (div_pos hT hR0).le
  exact RetainedCoreHistory.scalar_le_two_mul_along_backward_traces_of_scalar_le_on_ball
    ((H n).extendAt (hH n).2.1 (G n) (hG n).2 (hbad n).1 ((hbad n).2.2.1.trans (hsliver n).2.1))
    (Ctime := 2 * Ctime) (qcan := 2 * qcan n) hR0 (by linarith) hstep' rfl hut hdin.1 hdin.2.1
    hdin.2.2 (by nlinarith [(hbad n).2.2.2.1]) (ŷ n) hball

include hε hεcone hκ hphi hCs hH hG hrec hq hpar hscale hθcap hpinch hslabs hbefore hsliver
  hbad in
theorem exists_depth_schedule_isTracedRegion_extendAt :
    ∃ τs : ℕ → ℝ, (∀ k, 0 < τs k) ∧ (∀ k, τs k ≤ 1 / 8) ∧
      ∀ ŷ : ∀ n, (((H n).extendAt (hH n).2.1 (G n) (hG n).2 (hbad n).1
          ((hbad n).2.2.1.trans (hsliver n).2.1)).toHistory.stageAt
          ((H n).extendAtTime (hH n).2.1 (G n) (hG n).2 (hbad n).1
            ((hbad n).2.2.1.trans (hsliver n).2.1))).Carrier,
      (∀ n, HEq (ŷ n) (y n)) → ∀ k : ℕ, ∃ K₀ : ℝ, 0 ≤ K₀ ∧ ∀ᶠ n in atTop,
        ((H n).extendAt (hH n).2.1 (G n) (hG n).2 (hbad n).1
          ((hbad n).2.2.1.trans (hsliver n).2.1)).toHistory.isTracedRegion
          ((H n).extendAtTime (hH n).2.1 (G n) (hG n).2 (hbad n).1
            ((hbad n).2.2.1.trans (hsliver n).2.1)) (ŷ n)
          (((k + 3 : ℕ) : ℝ) / Real.sqrt ((G n).flow.scalar (t n) (y n)))
          (τs k / (G n).flow.scalar (t n) (y n)) (K₀ * (G n).flow.scalar (t n) (y n)) := by
  choose Q hQ1 hQev using fun k : ℕ =>
    eventually_scalar_le_on_normalized_ball_at_base hε hεcone hκ hphi hCs hH hG hrec hq hpar
      hθcap hpinch hslabs hbefore hsliver hbad ((k + 3 : ℕ) : ℝ) (by positivity)
  have hC0 : (0 : ℝ) ≤ Ctime := Ctime.coe_nonneg
  refine ⟨fun k => 1 / (4 * ((Ctime : ℝ) + 1) * max (Q k) 2), fun k => by positivity,
    fun k => ?_, fun ŷ hŷ k => ?_⟩
  · have h2 := le_max_right (Q k) 2
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hQ2 := le_max_right (Q k) 2
  have hstep : 4 * (Ctime : ℝ) * max (Q k) 2 *
      (1 / (4 * ((Ctime : ℝ) + 1) * max (Q k) 2)) ≤ 1 := by
    rw [show 4 * (Ctime : ℝ) * max (Q k) 2 * (1 / (4 * ((Ctime : ℝ) + 1) * max (Q k) 2)) =
      (Ctime : ℝ) / ((Ctime : ℝ) + 1) by field_simp]
    rw [div_le_one (by positivity)]
    linarith
  obtain ⟨K₀, hK₀, hev⟩ := exists_eventually_isTracedRegion_extendAt_of_scalar_le_on_ball hphi hH
    hG hrec hq hpar hscale hθcap hpinch hslabs hsliver hbad (A := ((k + 3 : ℕ) : ℝ))
    (by positivity) (by positivity) hQ2 hstep
  refine ⟨K₀, hK₀, ?_⟩
  filter_upwards [hev ŷ hŷ, hQev k] with n hn hQn
  exact hn fun z hz => (hQn z hz).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
    ((lt_of_lt_of_le (by positivity) (hq n).1).trans (hbad n).2.2.2.1).le)

include hε hεcone hκ hphi hCs hH hG hrec hq hpar hscale hθcap hpinch hslabs hbefore hsliver
  hbad in
theorem exists_subseq_scalar_le_on_normalized_balls_at_base
    (hεX : ε ≤ crossingNeckAccuracy.{u}) (σ : ℕ → ℕ) (hσ : StrictMono σ) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ C₀ : ℝ, 1 ≤ C₀ ∧ ∀ A : ℝ, 0 < A → ∀ᶠ i in atTop,
      ∀ z ∈ riemannianBallOf ((G (σ (ψ i))).flow.base.metric (t (σ (ψ i)))) (y (σ (ψ i)))
          (A / Real.sqrt ((G (σ (ψ i))).flow.scalar (t (σ (ψ i))) (y (σ (ψ i))))),
        (G (σ (ψ i))).flow.scalar (t (σ (ψ i))) z ≤
          C₀ * (G (σ (ψ i))).flow.scalar (t (σ (ψ i))) (y (σ (ψ i))) := by
  have hRpos : ∀ n, 0 < (G n).flow.scalar (t n) (y n) := fun n =>
    (lt_of_lt_of_le (by positivity) (hq n).1).trans (hbad n).2.2.2.1
  have hlast : ∀ n, ((H n).extendAt (hH n).2.1 (G n) (hG n).2 (hbad n).1
      ((hbad n).2.2.1.trans (hsliver n).2.1)).toHistory.activeStage
      ((H n).extendAtTime (hH n).2.1 (G n) (hG n).2 (hbad n).1
        ((hbad n).2.2.1.trans (hsliver n).2.1)) = Fin.last (H n).eventCount := fun n =>
    (H n).activeStage_extendHorizon_eq_last ((hH n).2.1 ▸ (hbad n).1.le)
      ((G n).closedPrefix (t n) (hbad n).1 ((hbad n).2.2.1.trans (hsliver n).2.1)) (hG n).2 _
      (hbad n).1.le
  let ŷ : ∀ n, (((H n).extendAt (hH n).2.1 (G n) (hG n).2 (hbad n).1
      ((hbad n).2.2.1.trans (hsliver n).2.1)).toHistory.stageAt
      ((H n).extendAtTime (hH n).2.1 (G n) (hG n).2 (hbad n).1
        ((hbad n).2.2.1.trans (hsliver n).2.1))).Carrier := fun n =>
    cast (congrArg (fun k => ((H n).stage k).Carrier) (hlast n).symm) (y n)
  have hŷ : ∀ n, HEq (ŷ n) (y n) := fun n => cast_heq _ _
  obtain ⟨τs, hτs, hτs8, htr⟩ := exists_depth_schedule_isTracedRegion_extendAt hε hεcone hκ hphi
    hCs hH hG hrec hq hpar hscale hθcap hpinch hslabs hbefore hsliver hbad
  have hRσ : Tendsto (fun m => (G (σ m)).flow.scalar (t (σ m)) (y (σ m))) atTop atTop :=
    (tendsto_scalar_at_bad_point_atTop hq hbad).comp hσ.tendsto_atTop
  have hgap : Tendsto (fun n => (G n).flow.scalar (t n) (y n) * (t n - t₀ n)) atTop (𝓝 0) := by
    have hup : ∀ n, (G n).flow.scalar (t n) (y n) * (t n - t₀ n) ≤ 1 / ((n : ℝ) + 1) := by
      intro n
      have h1 := ((hsliver n).2.2.2.1 (t n) ⟨(hbad n).2.1, (hbad n).2.2.1.le⟩ (y n)).1
      have hgap : t n - t₀ n ≤ η n := by linarith [(hbad n).2.2.1]
      exact (mul_le_mul_of_nonneg_left hgap (hRpos n).le).trans h1
    have hlow : ∀ n, 0 ≤ (G n).flow.scalar (t n) (y n) * (t n - t₀ n) := fun n =>
      mul_nonneg (hRpos n).le (sub_nonneg.mpr (hbad n).2.1)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      tendsto_one_div_add_atTop_nhds_zero_nat hlow hup
  obtain ⟨ψ, hψ, C₀, hC₀, hball⟩ :=
    ObservedHistory.exists_subseq_scalar_le_on_normalized_balls_of_depth_schedule
      (fun m => ((H (σ m)).extendAt (hH (σ m)).2.1 (G (σ m)) (hG (σ m)).2 (hbad (σ m)).1
        ((hbad (σ m)).2.2.1.trans (hsliver (σ m)).2.1)).toHistory)
      (fun m => (H (σ m)).extendAtTime (hH (σ m)).2.1 (G (σ m)) (hG (σ m)).2 (hbad (σ m)).1
        ((hbad (σ m)).2.2.1.trans (hsliver (σ m)).2.1))
      (fun m => ŷ (σ m)) (fun m => (G (σ m)).flow.scalar (t (σ m)) (y (σ m)))
      (fun m => hRpos (σ m)) hRσ τs hτs (fun k => (hτs8 k).trans (by norm_num))
      (fun k => (htr ŷ hŷ k).imp fun _ hK => ⟨hK.1, hσ.tendsto_atTop.eventually hK.2⟩)
      hκ hε (t₀ := fun m => t₀ (σ m)) (hgap.comp hσ.tendsto_atTop)
      (fun m v p r hv hr hb => (H (σ m)).volume_ge_extendAt_of_terminalNoncollapsedBefore
        (hH (σ m)).2.1 (G (σ m)) (hG (σ m)).2 (hbad (σ m)).1
        ((hbad (σ m)).2.2.1.trans (hsliver (σ m)).2.1) (hslabs (σ m)).2.2.2.2
        (hbefore (σ m)).2.2.2.2.2 v p r hv hr hb) hphi
      (fun m v _ x => (H (σ m)).curvatureOperatorLowerBoundAt_extendAt_of_pinched
        (hH (σ m)).2.1 (G (σ m)) (hG (σ m)).2 (hbad (σ m)).1
        ((hbad (σ m)).2.2.1.trans (hsliver (σ m)).2.1) (hpinch (σ m)).1 (hpinch (σ m)).2 v x)
      hε hεX (Cq := Cs) (qs := fun m => qs (σ m))
      (fun m => ((hq (σ m)).2.2.trans (mul_le_mul_of_nonneg_left (hbad (σ m)).2.2.2.1.le
        (by linarith))).trans_eq (mul_comm _ _))
      (fun m v hv hvk p hpq => (H (σ m)).exists_spatialCanonicalWitness_extendAt_of_before
        (hH (σ m)).2.1 (G (σ m)) (hG (σ m)).2 (hbad (σ m)).1
        ((hbad (σ m)).2.2.1.trans (hsliver (σ m)).2.1) (hslabs (σ m)).2.2.2.1
        (hbefore (σ m)).2.2.2.2.1 v hv hvk p hpq)
  refine ⟨ψ, hψ, C₀, hC₀, fun A hA => ?_⟩
  filter_upwards [hball A hA] with i hi
  exact (RetainedCoreHistory.scalar_ball_bound_extendAt_iff (H (σ (ψ i))) (hH (σ (ψ i))).2.1
    (G (σ (ψ i))) (hG (σ (ψ i))).2 (hbad (σ (ψ i))).1
    ((hbad (σ (ψ i))).2.2.1.trans (hsliver (σ (ψ i))).2.1) (y (σ (ψ i))) (ŷ (σ (ψ i)))
    (hŷ (σ (ψ i))) _ _).mp hi

include hε hεcone hκ hphi hCs hH hG hrec hq hpar hscale hθcap hpinch hslabs hbefore hsliver
  hbad in
theorem exists_subseq_depthExtendable_pos (hεX : ε ≤ crossingNeckAccuracy.{u}) (σ : ℕ → ℕ)
    (hσ : StrictMono σ) :
    let K : ℕ → RetainedCoreHistory P₀ := fun n => (H n).extendAt (hH n).2.1 (G n) (hG n).2
      (hbad n).1 ((hbad n).2.2.1.trans (hsliver n).2.1)
    let τ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon := fun n =>
      (H n).extendAtTime (hH n).2.1 (G n) (hG n).2 (hbad n).1
        ((hbad n).2.2.1.trans (hsliver n).2.1)
    ∀ ŷ : ∀ n, ((K n).toHistory.stageAt (τ n)).Carrier, (∀ n, HEq (ŷ n) (y n)) →
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ T₀ : ℝ, 0 < T₀ ∧
      ObservedHistory.DepthExtendable (fun n => (K n).toHistory) τ ŷ
        (fun n => (G n).flow.scalar (t n) (y n)) (σ ∘ ψ) T₀ := by
  intro K τ ŷ hŷ
  obtain ⟨ψ, hψ, C₀, -, hball⟩ := exists_subseq_scalar_le_on_normalized_balls_at_base hε hεcone
    hκ hphi hCs hH hG hrec hq hpar hscale hθcap hpinch hslabs hbefore hsliver hbad hεX σ hσ
  have hC0 : (0 : ℝ) ≤ Ctime := Ctime.coe_nonneg
  refine ⟨ψ, hψ, 1 / (4 * ((Ctime : ℝ) + 1) * max C₀ 2), by positivity, fun A hA => ?_⟩
  have hQ2 := le_max_right C₀ 2
  have hstep : 4 * (Ctime : ℝ) * max C₀ 2 * (1 / (4 * ((Ctime : ℝ) + 1) * max C₀ 2)) ≤ 1 := by
    rw [show 4 * (Ctime : ℝ) * max C₀ 2 * (1 / (4 * ((Ctime : ℝ) + 1) * max C₀ 2)) =
      (Ctime : ℝ) / ((Ctime : ℝ) + 1) by field_simp]
    rw [div_le_one (by positivity)]
    linarith
  obtain ⟨K₀, hK₀, hev⟩ := exists_eventually_isTracedRegion_extendAt_of_scalar_le_on_ball hphi hH
    hG hrec hq hpar hscale hθcap hpinch hslabs hsliver hbad (A := A) hA (by positivity) hQ2 hstep
  refine ⟨K₀, hK₀, ?_⟩
  filter_upwards [hball A hA, (hσ.comp hψ).tendsto_atTop.eventually (hev ŷ hŷ)] with i hi hn
  exact hn fun z hz => (hi z hz).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
    ((lt_of_lt_of_le (by positivity) (hq (σ (ψ i))).1).trans (hbad (σ (ψ i))).2.2.2.1).le)

end RetainedCoreHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
