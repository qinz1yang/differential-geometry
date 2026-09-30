import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalHornBlowupContradiction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalHornExtendAtTransports
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RetainedCoreHistoryExtendAtTransport
import DifferentialGeometry.Geometry.Metric.Distance.SeparatedSideBallClause
import DifferentialGeometry.Topology.Sequences.RescalingFactor

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
  (SpatialCanonicalWitness SpatialCanonicalAlternative SpatialNeck SpatialLocalNeck)
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory

universe u

theorem exists_tolerance_false_of_deep_horn_slices :
    ∃ epsW : ℝ, 0 < epsW ∧
    ∀ {κ ε ε₁ C1 C2 qcan a : ℝ} {Ctime Cgrad : ℝ≥0} {phi : ℝ → ℝ},
      0 < κ → 0 < qcan → 0 < ε → ε ≤ epsW → ε ≤ crossingNeckAccuracy.{u} → ε₁ ≤ 1 / 30000 →
      0 < a → Perelman.AdmissiblePinchingFunction phi →
    ∀ (H : ℕ → RetainedCoreHistory.{u})
      (hend : ∀ n, (H n).time (Fin.last (H n).eventCount) = (H n).horizon),
      (∀ n, (H n).EventSlabsDerivative Ctime qcan (Fin.last (H n).eventCount)) →
      (∀ n, (H n).EventSlabsPinched phi) →
      (∀ n, (H n).EventSlabsStronglyCanonical ε ε₁ C1 C2 qcan (Fin.last (H n).eventCount)) →
      (∀ n, (H n).NoncollapsedBefore κ ε ((H n).time (Fin.last (H n).eventCount))) →
    ∀ {s : ℕ → ℝ} (G : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).IncomingSlab
        ((H n).time (Fin.last (H n).eventCount)) (s n))
      (L : ∀ n, (G n).TerminalLimitMetric)
      (hG : ∀ n, (G n).flow.base.metric ((H n).time (Fin.last (H n).eventCount)) =
        (H n).initialMetric (Fin.last (H n).eventCount)),
      (∀ n, a ≤ s n) →
      (∀ n, (G n).DerivativeBoundBefore Ctime qcan (s n)) →
      (∀ n, (G n).GradientBoundBefore Cgrad qcan (s n)) →
      (∀ n, (H n).StronglyCanonicalBefore (Fin.last (H n).eventCount) (G n) ε ε₁ C1 C2 qcan
        (s n)) →
      (∀ n, Perelman.PhiAlmostNonnegative (G n).flow
        (Ico ((H n).time (Fin.last (H n).eventCount)) (s n)) phi) →
      (∀ n, ∀ t₀ ∈ Ioo ((H n).time (Fin.last (H n).eventCount)) (s n),
        (H n).TerminalNoncollapsedBefore (hend n) (G n) (hG n) κ ε t₀) →
    ∀ (x : ∀ n, (G n).terminalRegularOpen) {eps : ℝ}, 0 < eps → eps < 1 / 11 →
      (∀ n : ℕ, (n : ℝ) + 1 ≤ metricScalarAt (L n).metric (x n)) →
    ∀ (τ Q : ℕ → ℝ) (S V W : ∀ n, Set ((H n).stage (Fin.last (H n).eventCount)).Carrier),
      (∀ n, τ n ∈ Ioo ((H n).time (Fin.last (H n).eventCount)) (s n)) →
      (∀ m, 1 ≤ Q m) →
      (∀ n, ¬ Nonempty (SpatialNeck ((G n).flow.base.metric (τ n)) eps (x n).val)) →
      (∀ n, |(G n).flow.scalar (τ n) (x n).val - metricScalarAt (L n).metric (x n)| ≤
        metricScalarAt (L n).metric (x n) / 2) →
      (∀ n, (s n - τ n) * metricScalarAt (L n).metric (x n) ≤ 1 / ((n : ℝ) + 1)) →
      (∀ n, IsOpen (V n)) → (∀ n, IsOpen (W n)) → (∀ n, Disjoint (V n) (W n)) →
      (∀ n, ∀ z ∈ S n, riemannianEDistOf ((G n).flow.base.metric (τ n)) (x n).val z ≤
        ENNReal.ofReal (7 / Real.sqrt ((G n).flow.scalar (τ n) (x n).val))) →
      (∀ m : ℕ, ∀ᶠ n in atTop,
        riemannianClosedBallOf ((G n).flow.base.metric (τ n)) (x n).val
            (3 * ((m : ℝ) + 1) / Real.sqrt ((G n).flow.scalar (τ n) (x n).val)) \ S n ⊆
          V n ∪ W n ∧
        ∃ p ∈ V n, ∃ q ∈ W n,
          ENNReal.ofReal (((m : ℝ) + 1) / Real.sqrt ((G n).flow.scalar (τ n) (x n).val)) ≤
            riemannianEDistOf ((G n).flow.base.metric (τ n)) (x n).val p ∧
          riemannianEDistOf ((G n).flow.base.metric (τ n)) (x n).val p <
            ENNReal.ofReal (3 * ((m : ℝ) + 1) / Real.sqrt ((G n).flow.scalar (τ n) (x n).val)) ∧
          ENNReal.ofReal (((m : ℝ) + 1) / Real.sqrt ((G n).flow.scalar (τ n) (x n).val)) ≤
            riemannianEDistOf ((G n).flow.base.metric (τ n)) (x n).val q ∧
          riemannianEDistOf ((G n).flow.base.metric (τ n)) (x n).val q <
            ENNReal.ofReal (3 * ((m : ℝ) + 1) /
              Real.sqrt ((G n).flow.scalar (τ n) (x n).val))) →
      (∀ m : ℕ, ∀ᶠ n in atTop,
        (∀ w : (G n).terminalRegularOpen, riemannianEDistOf (L n).metric (x n) w <
          ENNReal.ofReal (8 * ((m : ℝ) + 1) / Real.sqrt (metricScalarAt (L n).metric (x n))) →
          metricScalarAt (L n).metric w ≤ Q m * metricScalarAt (L n).metric (x n)) ∧
        riemannianBallOf ((G n).flow.base.metric (τ n)) (x n).val
            (16 * (3 * ((m : ℝ) + 1) / Real.sqrt (metricScalarAt (L n).metric (x n))) / 17) ⊆
          Subtype.val '' riemannianClosedBallOf (L n).metric (x n)
            (3 * ((m : ℝ) + 1) / Real.sqrt (metricScalarAt (L n).metric (x n))) ∧
        ∀ w ∈ riemannianClosedBallOf (L n).metric (x n)
            (3 * ((m : ℝ) + 1) / Real.sqrt (metricScalarAt (L n).metric (x n))),
          |metricScalarAt ((G n).flow.base.metric (τ n)) w.val - metricScalarAt (L n).metric w| <
            metricScalarAt (L n).metric (x n)) →
      (∀ m : ℕ, ∀ᶠ n in atTop, ∀ w ∈ riemannianClosedBallOf (L n).metric (x n)
          (3 * ((m : ℝ) + 1) / Real.sqrt (metricScalarAt (L n).metric (x n))),
        ∀ W : SpatialCanonicalWitness ((G n).flow.base.metric (τ n)) ε C1 C2 w.val,
          W.capTubeHasNeckChart ε →
            ∃ neck : SpatialLocalNeck ((G n).flow.base.metric (τ n)) ε w.val W.domain.carrier,
              W.alternative = SpatialCanonicalAlternative.neck neck) → False := by
  obtain ⟨epsW, hepsW, hLemA⟩ := exists_tolerance_false_of_deep_horn_sequence.{u}
  refine ⟨epsW, hepsW, ?_⟩
  intro κ ε ε₁ C1 C2 qcan a Ctime Cgrad phi hκ hq hε hεW hεcross hε₁ ha hphi H hend hderiv
    hpinch hclass hnc s G L hG hs hderG hgradG hcanG hpinchG hncG x eps heps heps11 hRl1 τ Q S V W
    hτmem hQ1 hno hcl hgap hV hW hVW hS hpts hup hwit
  have hat : ∀ n, (H n).time (Fin.last (H n).eventCount) < τ n := fun n => (hτmem n).1
  have hτs : ∀ n, τ n < s n := fun n => (hτmem n).2
  have hRlpos : ∀ n, 0 < metricScalarAt (L n).metric (x n) := fun n =>
    (by positivity : (0 : ℝ) < n + 1).trans_le (hRl1 n)
  have hnat : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_mono (fun n => by linarith) tendsto_natCast_atTop_atTop
  have hRllim : Tendsto (fun n => metricScalarAt (L n).metric (x n)) atTop atTop :=
    tendsto_atTop_mono hRl1 hnat
  obtain ⟨hRpos, hRlim, hRC, -⟩ := exists_rescaling_factor_normalization
    (R := fun n => (G n).flow.scalar (τ n) (x n).val)
    (Rl := fun n => metricScalarAt (L n).metric (x n)) hRlpos hRllim hcl hτs hgap
  have hRlow : ∀ n, metricScalarAt (L n).metric (x n) / 2 ≤ (G n).flow.scalar (τ n) (x n).val :=
    fun n => by linarith [(abs_le.mp (hcl n)).1]
  obtain ⟨Cq, hqC⟩ := hRC qcan
  have hτlow : ∀ᶠ n in atTop, a / 2 ≤ τ n := by
    filter_upwards [tendsto_one_div_add_atTop_nhds_zero_nat.eventually_lt_const (half_pos ha)]
      with n hn
    have h1 := hgap n
    have h2 : s n - τ n ≤ (s n - τ n) * metricScalarAt (L n).metric (x n) :=
      le_mul_of_one_le_right (sub_nonneg.mpr (hτs n).le)
        (by linarith [hRl1 n, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
    linarith [hs n]
  have hRt : Tendsto (fun n => (G n).flow.scalar (τ n) (x n).val * τ n) atTop atTop := by
    refine tendsto_atTop_mono' atTop ?_
      ((hnat.atTop_div_const (by norm_num : (0 : ℝ) < 2)).atTop_mul_const (half_pos ha))
    filter_upwards [hτlow] with n hn
    have h1 : ((n : ℝ) + 1) / 2 ≤ (G n).flow.scalar (τ n) (x n).val := by
      linarith [hRl1 n, hRlow n]
    exact mul_le_mul h1 hn (by linarith) (hRpos n).le
  choose y hy using fun n =>
    (H n).exists_heq_extendAt_stageAt (hend n) (G n) (hG n) (hat n) (hτs n) (x n).val
  have hscal : ∀ n, metricScalarAt
      (((H n).extendAt (hend n) (G n) (hG n) (hat n) (hτs n)).toHistory.stageMetric
        (((H n).extendAt (hend n) (G n) (hG n) (hat n) (hτs n)).toHistory.activeStage
          ((H n).extendAtTime (hend n) (G n) (hG n) (hat n) (hτs n)))
        ((H n).extendAtTime (hend n) (G n) (hG n) (hat n) (hτs n))) (y n) =
      (G n).flow.scalar (τ n) (x n).val := fun n =>
    ((H n).riemannianEDistOf_extendAt_stageAt_eq (hend n) (G n) (hG n) (hat n) (hτs n) (x n).val
      (x n).val (y n) (y n) (hy n) (hy n)).2
  have hradA : ∀ A : ℝ, 0 < A → ∀ n, A / Real.sqrt ((G n).flow.scalar (τ n) (x n).val) ≤
      16 * (3 * ((⌊A⌋₊ : ℝ) + 1) / Real.sqrt (metricScalarAt (L n).metric (x n))) / 17 := by
    intro A hA n
    have hArad : A < (⌊A⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one A
    have hsRl : 0 < Real.sqrt (metricScalarAt (L n).metric (x n)) := Real.sqrt_pos.mpr (hRlpos n)
    have hsR : 0 < Real.sqrt ((G n).flow.scalar (τ n) (x n).val) := Real.sqrt_pos.mpr (hRpos n)
    have hsq : Real.sqrt (metricScalarAt (L n).metric (x n)) / 2 ≤
        Real.sqrt ((G n).flow.scalar (τ n) (x n).val) := by
      have h4 : metricScalarAt (L n).metric (x n) / 4 ≤ (G n).flow.scalar (τ n) (x n).val := by
        linarith [hRlow n, hRlpos n]
      calc Real.sqrt (metricScalarAt (L n).metric (x n)) / 2
          = Real.sqrt (metricScalarAt (L n).metric (x n) / 4) := by
            rw [Real.sqrt_div (hRlpos n).le, show (4 : ℝ) = 2 ^ 2 by norm_num,
              Real.sqrt_sq (by norm_num)]
        _ ≤ _ := Real.sqrt_le_sqrt h4
    have hX : (0 : ℝ) ≤ 16 * (3 * ((⌊A⌋₊ : ℝ) + 1) /
        Real.sqrt (metricScalarAt (L n).metric (x n))) / 17 := by positivity
    rw [div_le_iff₀ hsR]
    calc A ≤ (⌊A⌋₊ : ℝ) + 1 := hArad.le
      _ = 16 * (3 * ((⌊A⌋₊ : ℝ) + 1) / Real.sqrt (metricScalarAt (L n).metric (x n))) / 17 *
          (Real.sqrt (metricScalarAt (L n).metric (x n)) / 2) * (17 / 24) := by
          field_simp
          ring
      _ ≤ 16 * (3 * ((⌊A⌋₊ : ℝ) + 1) / Real.sqrt (metricScalarAt (L n).metric (x n))) / 17 *
          (Real.sqrt (metricScalarAt (L n).metric (x n)) / 2) * 1 :=
          mul_le_mul_of_nonneg_left (by norm_num) (by positivity)
      _ = 16 * (3 * ((⌊A⌋₊ : ℝ) + 1) / Real.sqrt (metricScalarAt (L n).metric (x n))) / 17 *
          (Real.sqrt (metricScalarAt (L n).metric (x n)) / 2) := mul_one _
      _ ≤ 16 * (3 * ((⌊A⌋₊ : ℝ) + 1) / Real.sqrt (metricScalarAt (L n).metric (x n))) / 17 *
          Real.sqrt ((G n).flow.scalar (τ n) (x n).val) := mul_le_mul_of_nonneg_left hsq hX
  have hballLow : ∀ A : ℝ, 0 < A → ∃ Qlow : ℝ, 0 < Qlow ∧ ∀ᶠ n in atTop,
      ∀ z ∈ riemannianBallOf
          (((H n).extendAt (hend n) (G n) (hG n) (hat n) (hτs n)).toHistory.stageMetric
            (((H n).extendAt (hend n) (G n) (hG n) (hat n) (hτs n)).toHistory.activeStage
              ((H n).extendAtTime (hend n) (G n) (hG n) (hat n) (hτs n)))
            ((H n).extendAtTime (hend n) (G n) (hG n) (hat n) (hτs n))) (y n)
          (A / Real.sqrt ((G n).flow.scalar (τ n) (x n).val)),
        Qlow * (G n).flow.scalar (τ n) (x n).val ≤ metricScalarAt
          (((H n).extendAt (hend n) (G n) (hG n) (hat n) (hτs n)).toHistory.stageMetric
            (((H n).extendAt (hend n) (G n) (hG n) (hat n) (hτs n)).toHistory.activeStage
              ((H n).extendAtTime (hend n) (G n) (hG n) (hat n) (hτs n)))
            ((H n).extendAtTime (hend n) (G n) (hG n) (hat n) (hτs n))) z := by
    intro A hA
    refine ⟨(4 * (1 + Cgrad * A) ^ 2)⁻¹, by positivity, ?_⟩
    filter_upwards [hRlim.eventually_gt_atTop (qcan * (4 * (1 + Cgrad * A) ^ 2))] with n hn
    exact (H n).extendAt_scalar_lower_on_ball_of_gradientBoundBefore (hend n) (G n) (hG n) (hat n)
      (hτs n) (x n) (y n) (hy n) (hgradG n) hq hA.le (by rw [lt_div_iff₀ (by positivity)]; exact hn)
  have hballUp : ∀ A : ℝ, 0 < A → ∃ Qup : ℝ, ∀ᶠ n in atTop,
      ∀ z ∈ riemannianBallOf
          (((H n).extendAt (hend n) (G n) (hG n) (hat n) (hτs n)).toHistory.stageMetric
            (((H n).extendAt (hend n) (G n) (hG n) (hat n) (hτs n)).toHistory.activeStage
              ((H n).extendAtTime (hend n) (G n) (hG n) (hat n) (hτs n)))
            ((H n).extendAtTime (hend n) (G n) (hG n) (hat n) (hτs n))) (y n)
          (A / Real.sqrt ((G n).flow.scalar (τ n) (x n).val)),
        metricScalarAt
          (((H n).extendAt (hend n) (G n) (hG n) (hat n) (hτs n)).toHistory.stageMetric
            (((H n).extendAt (hend n) (G n) (hG n) (hat n) (hτs n)).toHistory.activeStage
              ((H n).extendAtTime (hend n) (G n) (hG n) (hat n) (hτs n)))
            ((H n).extendAtTime (hend n) (G n) (hG n) (hat n) (hτs n))) z ≤
          Qup * (G n).flow.scalar (τ n) (x n).val := by
    intro A hA
    refine ⟨2 * (Q ⌊A⌋₊ + 1), ?_⟩
    filter_upwards [hup ⌊A⌋₊] with n hn
    refine (H n).extendAt_scalar_upper_on_ball (hend n) (G n) (hG n) (hat n) (hτs n) (x n) (y n)
      (hy n) (L n) (div_pos (by positivity) (Real.sqrt_pos.mpr (hRlpos n))) (hQ1 ⌊A⌋₊)
      (fun w hw => hn.1 w (hw.trans_le (ENNReal.ofReal_le_ofReal ?_))) hn.2.1 hn.2.2
      (hradA A hA n) (hRlow n)
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right (by linarith) (by positivity)
  have htopneck : ∀ A c' : ℝ, 0 < A → 0 < c' → ∀ᶠ n in atTop,
      ∀ z ∈ riemannianBallOf
          (((H n).extendAt (hend n) (G n) (hG n) (hat n) (hτs n)).toHistory.stageMetric
            (((H n).extendAt (hend n) (G n) (hG n) (hat n) (hτs n)).toHistory.activeStage
              ((H n).extendAtTime (hend n) (G n) (hG n) (hat n) (hτs n)))
            ((H n).extendAtTime (hend n) (G n) (hG n) (hat n) (hτs n))) (y n)
          (A / Real.sqrt ((G n).flow.scalar (τ n) (x n).val)),
        c' * (G n).flow.scalar (τ n) (x n).val ≤ metricScalarAt
          (((H n).extendAt (hend n) (G n) (hG n) (hat n) (hτs n)).toHistory.stageMetric
            (((H n).extendAt (hend n) (G n) (hG n) (hat n) (hτs n)).toHistory.activeStage
              ((H n).extendAtTime (hend n) (G n) (hG n) (hat n) (hτs n)))
            ((H n).extendAtTime (hend n) (G n) (hG n) (hat n) (hτs n))) z →
        ∀ W : SpatialCanonicalWitness
            (((H n).extendAt (hend n) (G n) (hG n) (hat n) (hτs n)).toHistory.stageMetric
              (((H n).extendAt (hend n) (G n) (hG n) (hat n) (hτs n)).toHistory.activeStage
                ((H n).extendAtTime (hend n) (G n) (hG n) (hat n) (hτs n)))
              ((H n).extendAtTime (hend n) (G n) (hG n) (hat n) (hτs n))) ε C1 C2 z,
          W.capTubeHasNeckChart ε → ∃ nk, W.alternative = SpatialCanonicalAlternative.neck nk := by
    intro A c' hA _
    filter_upwards [hup ⌊A⌋₊, hwit ⌊A⌋₊] with n hn hw
    exact (H n).extendAt_neck_alternative_on_ball (hend n) (G n) (hG n) (hat n) (hτs n) (x n) (y n)
      (hy n) (L n) hn.2.1 hw (hradA A hA n)
  choose S' V' W' hV' hW' hVW' hS' hcl' using fun n =>
    (H n).extendAt_exists_separating_sets (hend n) (G n) (hG n) (hat n) (hτs n) (x n) (y n) (hy n)
      (S n) (V n) (W n) (hV n) (hW n) (hVW n) (hS n)
  have hpoints : ∀ A : ℝ, 7 < A → ∀ᶠ n in atTop,
      riemannianClosedBallOf
          (((H n).extendAt (hend n) (G n) (hG n) (hat n) (hτs n)).toHistory.stageMetric
            (((H n).extendAt (hend n) (G n) (hG n) (hat n) (hτs n)).toHistory.activeStage
              ((H n).extendAtTime (hend n) (G n) (hG n) (hat n) (hτs n)))
            ((H n).extendAtTime (hend n) (G n) (hG n) (hat n) (hτs n))) (y n)
          (3 * A / Real.sqrt ((G n).flow.scalar (τ n) (x n).val)) \ S' n ⊆ V' n ∪ W' n ∧
      ∃ p ∈ V' n, ∃ q ∈ W' n,
        ENNReal.ofReal (A / Real.sqrt ((G n).flow.scalar (τ n) (x n).val)) ≤ riemannianEDistOf
          (((H n).extendAt (hend n) (G n) (hG n) (hat n) (hτs n)).toHistory.stageMetric
            (((H n).extendAt (hend n) (G n) (hG n) (hat n) (hτs n)).toHistory.activeStage
              ((H n).extendAtTime (hend n) (G n) (hG n) (hat n) (hτs n)))
            ((H n).extendAtTime (hend n) (G n) (hG n) (hat n) (hτs n))) (y n) p ∧
        riemannianEDistOf
          (((H n).extendAt (hend n) (G n) (hG n) (hat n) (hτs n)).toHistory.stageMetric
            (((H n).extendAt (hend n) (G n) (hG n) (hat n) (hτs n)).toHistory.activeStage
              ((H n).extendAtTime (hend n) (G n) (hG n) (hat n) (hτs n)))
            ((H n).extendAtTime (hend n) (G n) (hG n) (hat n) (hτs n))) (y n) p <
          ENNReal.ofReal (3 * A / Real.sqrt ((G n).flow.scalar (τ n) (x n).val)) ∧
        ENNReal.ofReal (A / Real.sqrt ((G n).flow.scalar (τ n) (x n).val)) ≤ riemannianEDistOf
          (((H n).extendAt (hend n) (G n) (hG n) (hat n) (hτs n)).toHistory.stageMetric
            (((H n).extendAt (hend n) (G n) (hG n) (hat n) (hτs n)).toHistory.activeStage
              ((H n).extendAtTime (hend n) (G n) (hG n) (hat n) (hτs n)))
            ((H n).extendAtTime (hend n) (G n) (hG n) (hat n) (hτs n))) (y n) q ∧
        riemannianEDistOf
          (((H n).extendAt (hend n) (G n) (hG n) (hat n) (hτs n)).toHistory.stageMetric
            (((H n).extendAt (hend n) (G n) (hG n) (hat n) (hτs n)).toHistory.activeStage
              ((H n).extendAtTime (hend n) (G n) (hG n) (hat n) (hτs n)))
            ((H n).extendAtTime (hend n) (G n) (hG n) (hat n) (hτs n))) (y n) q <
          ENNReal.ofReal (3 * A / Real.sqrt ((G n).flow.scalar (τ n) (x n).val)) := by
    intro A hA7
    have hArad : A < (⌊A⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one A
    filter_upwards [hpts ⌊A⌋₊] with n hn
    obtain ⟨hcov, p, hp, q, hq', hpa, hpc, hqa, hqc⟩ := hcl' n ((⌊A⌋₊ : ℝ) + 1) hn
    have hsR : 0 < Real.sqrt ((G n).flow.scalar (τ n) (x n).val) := Real.sqrt_pos.mpr (hRpos n)
    have h := Geometry.Metric.separated_side_clause_of_le_radius _ (hV' n) (hW' n) (hVW' n)
      (b := 7 / Real.sqrt ((G n).flow.scalar (τ n) (x n).val))
      (A := A / Real.sqrt ((G n).flow.scalar (τ n) (x n).val))
      (r := ((⌊A⌋₊ : ℝ) + 1) / Real.sqrt ((G n).flow.scalar (τ n) (x n).val)) (by positivity)
      (div_lt_div_of_pos_right hA7 hsR) (div_le_div_of_nonneg_right hArad.le hsR.le) (hS' n)
      (by rw [← mul_div_assoc]; exact hcov) hp hq' hpa (by rw [← mul_div_assoc]; exact hpc) hqa
      (by rw [← mul_div_assoc]; exact hqc)
    rw [← mul_div_assoc] at h
    exact h
  have hnoneck : ∀ n, ¬ Nonempty (SpatialNeck
      (((H n).extendAt (hend n) (G n) (hG n) (hat n) (hτs n)).toHistory.stageMetric
        (((H n).extendAt (hend n) (G n) (hG n) (hat n) (hτs n)).toHistory.activeStage
          ((H n).extendAtTime (hend n) (G n) (hG n) (hat n) (hτs n)))
        ((H n).extendAtTime (hend n) (G n) (hG n) (hat n) (hτs n))) eps (y n)) := fun n =>
    (H n).extendAt_not_nonempty_spatialNeck (hend n) (G n) (hG n) (hat n) (hτs n) (x n) (y n)
      (hy n) (hno n)
  exact hLemA H hend G hG hat hτs y (fun n => (G n).flow.scalar (τ n) (x n).val) hRpos hscal
    hRlim hRt hκ hε hεW hεcross hε₁ hqC hphi hpinch hpinchG hderiv hderG hclass hcanG hnc
    (fun n => hncG n (τ n) (hτmem n)) hballLow hballUp htopneck S' V' W' hV' hW' hVW' hS' hpoints
    heps heps11 hnoneck

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory

end
