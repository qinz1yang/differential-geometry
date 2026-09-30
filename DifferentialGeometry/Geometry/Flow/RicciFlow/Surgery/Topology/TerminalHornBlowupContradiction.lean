import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryStrongNeckStaggeredDepthInduction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryStrongNeckExtendHorizon
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RetainedCoreHistoryExtendAtLimitInputs
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegionLineNeck
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryStrongNeckTopSliceTracedRegion
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegionTimeZeroUniformBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegionDeepNeckSupply

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
  (SpatialCanonicalWitness SpatialCanonicalAlternative SpatialNeck)
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory

universe u

theorem exists_tolerance_false_of_deep_horn_sequence :
    ∃ epsW : ℝ, 0 < epsW ∧
    ∀ (H : ℕ → RetainedCoreHistory.{u})
      (hend : ∀ n, (H n).time (Fin.last (H n).eventCount) = (H n).horizon) {s τ : ℕ → ℝ}
      (G : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).IncomingSlab
        ((H n).time (Fin.last (H n).eventCount)) (s n))
      (hG : ∀ n, (G n).flow.base.metric ((H n).time (Fin.last (H n).eventCount)) =
        (H n).initialMetric (Fin.last (H n).eventCount))
      (hat : ∀ n, (H n).time (Fin.last (H n).eventCount) < τ n) (hτs : ∀ n, τ n < s n)
      (y : ∀ n, (((H n).extendAt (hend n) (G n) (hG n) (hat n) (hτs n)).toHistory.stageAt
        ((H n).extendAtTime (hend n) (G n) (hG n) (hat n) (hτs n))).Carrier) (R : ℕ → ℝ),
      (∀ n, 0 < R n) →
      (∀ n, metricScalarAt
        (((H n).extendAt (hend n) (G n) (hG n) (hat n) (hτs n)).toHistory.stageMetric
        (((H n).extendAt (hend n) (G n) (hG n) (hat n) (hτs n)).toHistory.activeStage
          ((H n).extendAtTime (hend n) (G n) (hG n) (hat n) (hτs n)))
        ((H n).extendAtTime (hend n) (G n) (hG n) (hat n) (hτs n))) (y n) = R n) →
      Tendsto R atTop atTop → Tendsto (fun n => R n * τ n) atTop atTop →
    ∀ {κ ε ε₁ C1 C2 qcan Cq : ℝ} {Ctime : ℝ≥0} {phi : ℝ → ℝ}, 0 < κ → 0 < ε → ε ≤ epsW →
      ε ≤ crossingNeckAccuracy.{u} → ε₁ ≤ 1 / 30000 → (∀ n, qcan ≤ Cq * R n) →
      Perelman.AdmissiblePinchingFunction phi →
      (∀ n, (H n).EventSlabsPinched phi) →
      (∀ n, Perelman.PhiAlmostNonnegative (G n).flow
        (Ico ((H n).time (Fin.last (H n).eventCount)) (s n)) phi) →
      (∀ n, (H n).EventSlabsDerivative Ctime qcan (Fin.last (H n).eventCount)) →
      (∀ n, (G n).DerivativeBoundBefore Ctime qcan (s n)) →
      (∀ n, (H n).EventSlabsStronglyCanonical ε ε₁ C1 C2 qcan (Fin.last (H n).eventCount)) →
      (∀ n, (H n).StronglyCanonicalBefore (Fin.last (H n).eventCount) (G n) ε ε₁ C1 C2 qcan
        (s n)) →
      (∀ n, (H n).NoncollapsedBefore κ ε ((H n).time (Fin.last (H n).eventCount))) →
      (∀ n, (H n).TerminalNoncollapsedBefore (hend n) (G n) (hG n) κ ε (τ n)) →
    (∀ A : ℝ, 0 < A → ∃ Qlow : ℝ, 0 < Qlow ∧ ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf
          (((H n).extendAt (hend n) (G n) (hG n) (hat n) (hτs n)).toHistory.stageMetric
            (((H n).extendAt (hend n) (G n) (hG n) (hat n) (hτs n)).toHistory.activeStage
              ((H n).extendAtTime (hend n) (G n) (hG n) (hat n) (hτs n)))
            ((H n).extendAtTime (hend n) (G n) (hG n) (hat n) (hτs n))) (y n)
          (A / Real.sqrt (R n)),
        Qlow * R n ≤ metricScalarAt
          (((H n).extendAt (hend n) (G n) (hG n) (hat n) (hτs n)).toHistory.stageMetric
            (((H n).extendAt (hend n) (G n) (hG n) (hat n) (hτs n)).toHistory.activeStage
              ((H n).extendAtTime (hend n) (G n) (hG n) (hat n) (hτs n)))
            ((H n).extendAtTime (hend n) (G n) (hG n) (hat n) (hτs n))) x) →
    (∀ A : ℝ, 0 < A → ∃ Qup : ℝ, ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf
          (((H n).extendAt (hend n) (G n) (hG n) (hat n) (hτs n)).toHistory.stageMetric
            (((H n).extendAt (hend n) (G n) (hG n) (hat n) (hτs n)).toHistory.activeStage
              ((H n).extendAtTime (hend n) (G n) (hG n) (hat n) (hτs n)))
            ((H n).extendAtTime (hend n) (G n) (hG n) (hat n) (hτs n))) (y n)
          (A / Real.sqrt (R n)),
        metricScalarAt
          (((H n).extendAt (hend n) (G n) (hG n) (hat n) (hτs n)).toHistory.stageMetric
            (((H n).extendAt (hend n) (G n) (hG n) (hat n) (hτs n)).toHistory.activeStage
              ((H n).extendAtTime (hend n) (G n) (hG n) (hat n) (hτs n)))
            ((H n).extendAtTime (hend n) (G n) (hG n) (hat n) (hτs n))) x ≤ Qup * R n) →
    (∀ A c : ℝ, 0 < A → 0 < c → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf
          (((H n).extendAt (hend n) (G n) (hG n) (hat n) (hτs n)).toHistory.stageMetric
            (((H n).extendAt (hend n) (G n) (hG n) (hat n) (hτs n)).toHistory.activeStage
              ((H n).extendAtTime (hend n) (G n) (hG n) (hat n) (hτs n)))
            ((H n).extendAtTime (hend n) (G n) (hG n) (hat n) (hτs n))) (y n)
          (A / Real.sqrt (R n)),
        c * R n ≤ metricScalarAt
          (((H n).extendAt (hend n) (G n) (hG n) (hat n) (hτs n)).toHistory.stageMetric
            (((H n).extendAt (hend n) (G n) (hG n) (hat n) (hτs n)).toHistory.activeStage
              ((H n).extendAtTime (hend n) (G n) (hG n) (hat n) (hτs n)))
            ((H n).extendAtTime (hend n) (G n) (hG n) (hat n) (hτs n))) x →
        ∀ W : SpatialCanonicalWitness
            (((H n).extendAt (hend n) (G n) (hG n) (hat n) (hτs n)).toHistory.stageMetric
              (((H n).extendAt (hend n) (G n) (hG n) (hat n) (hτs n)).toHistory.activeStage
                ((H n).extendAtTime (hend n) (G n) (hG n) (hat n) (hτs n)))
              ((H n).extendAtTime (hend n) (G n) (hG n) (hat n) (hτs n))) ε C1 C2 x,
          W.capTubeHasNeckChart ε → ∃ nk, W.alternative = SpatialCanonicalAlternative.neck nk) →
    ∀ (S V W : ∀ n, Set (((H n).extendAt (hend n) (G n) (hG n) (hat n) (hτs n)).toHistory.stageAt
        ((H n).extendAtTime (hend n) (G n) (hG n) (hat n) (hτs n))).Carrier),
      (∀ n, IsOpen (V n)) → (∀ n, IsOpen (W n)) → (∀ n, Disjoint (V n) (W n)) →
      (∀ n, ∀ z ∈ S n,
        riemannianEDistOf
          (((H n).extendAt (hend n) (G n) (hG n) (hat n) (hτs n)).toHistory.stageMetric
            (((H n).extendAt (hend n) (G n) (hG n) (hat n) (hτs n)).toHistory.activeStage
              ((H n).extendAtTime (hend n) (G n) (hG n) (hat n) (hτs n)))
            ((H n).extendAtTime (hend n) (G n) (hG n) (hat n) (hτs n))) (y n) z ≤
          ENNReal.ofReal (7 / Real.sqrt (R n))) →
      (∀ A : ℝ, 7 < A → ∀ᶠ n in atTop,
        riemannianClosedBallOf
            (((H n).extendAt (hend n) (G n) (hG n) (hat n) (hτs n)).toHistory.stageMetric
              (((H n).extendAt (hend n) (G n) (hG n) (hat n) (hτs n)).toHistory.activeStage
                ((H n).extendAtTime (hend n) (G n) (hG n) (hat n) (hτs n)))
              ((H n).extendAtTime (hend n) (G n) (hG n) (hat n) (hτs n))) (y n)
            (3 * A / Real.sqrt (R n)) \ S n ⊆ V n ∪ W n ∧
        ∃ p ∈ V n, ∃ q ∈ W n,
          ENNReal.ofReal (A / Real.sqrt (R n)) ≤ riemannianEDistOf
            (((H n).extendAt (hend n) (G n) (hG n) (hat n) (hτs n)).toHistory.stageMetric
              (((H n).extendAt (hend n) (G n) (hG n) (hat n) (hτs n)).toHistory.activeStage
                ((H n).extendAtTime (hend n) (G n) (hG n) (hat n) (hτs n)))
              ((H n).extendAtTime (hend n) (G n) (hG n) (hat n) (hτs n))) (y n) p ∧
          riemannianEDistOf
            (((H n).extendAt (hend n) (G n) (hG n) (hat n) (hτs n)).toHistory.stageMetric
              (((H n).extendAt (hend n) (G n) (hG n) (hat n) (hτs n)).toHistory.activeStage
                ((H n).extendAtTime (hend n) (G n) (hG n) (hat n) (hτs n)))
              ((H n).extendAtTime (hend n) (G n) (hG n) (hat n) (hτs n))) (y n) p <
            ENNReal.ofReal (3 * A / Real.sqrt (R n)) ∧
          ENNReal.ofReal (A / Real.sqrt (R n)) ≤ riemannianEDistOf
            (((H n).extendAt (hend n) (G n) (hG n) (hat n) (hτs n)).toHistory.stageMetric
              (((H n).extendAt (hend n) (G n) (hG n) (hat n) (hτs n)).toHistory.activeStage
                ((H n).extendAtTime (hend n) (G n) (hG n) (hat n) (hτs n)))
              ((H n).extendAtTime (hend n) (G n) (hG n) (hat n) (hτs n))) (y n) q ∧
          riemannianEDistOf
            (((H n).extendAt (hend n) (G n) (hG n) (hat n) (hτs n)).toHistory.stageMetric
              (((H n).extendAt (hend n) (G n) (hG n) (hat n) (hτs n)).toHistory.activeStage
                ((H n).extendAtTime (hend n) (G n) (hG n) (hat n) (hτs n)))
              ((H n).extendAtTime (hend n) (G n) (hG n) (hat n) (hτs n))) (y n) q <
            ENNReal.ofReal (3 * A / Real.sqrt (R n))) →
    ∀ {eps : ℝ}, 0 < eps → eps < 1 / 11 →
      (∀ n, ¬ Nonempty (SpatialNeck
        (((H n).extendAt (hend n) (G n) (hG n) (hat n) (hτs n)).toHistory.stageMetric
          (((H n).extendAt (hend n) (G n) (hG n) (hat n) (hτs n)).toHistory.activeStage
            ((H n).extendAtTime (hend n) (G n) (hG n) (hat n) (hτs n)))
          ((H n).extendAtTime (hend n) (G n) (hG n) (hat n) (hτs n))) eps (y n))) → False := by
  obtain ⟨epsW₀, hepsW₀, hline⟩ :=
    ObservedHistory.exists_eventually_spatialNeck_of_isTracedRegion_of_separating_set.{u}
  obtain ⟨etaD, hetaD, hdeepL⟩ :=
    ObservedHistory.exists_tolerance_eventually_neckAlternative_of_isTracedRegion_uniform.{u}
  refine ⟨min epsW₀ etaD, lt_min hepsW₀ hetaD, ?_⟩
  intro H hend s τ G hG hat hτs y R hR hscal hRlim hRt κ ε ε₁ C1 C2 qcan Cq Ctime phi hκ hε
    hεW hεcross hε₁ hqC hphi hpinch hpinchG hderiv hderivG hclass hcanG hnc hncG hballLow hballUp
    htopneck S V W hV hW hVW hS hpoints eps heps heps11 hnoneck
  have hεW₀ : ε ≤ epsW₀ := hεW.trans (min_le_left _ _)
  have hεD : ε ≤ etaD := hεW.trans (min_le_right _ _)
  have hlastt : ∀ n,
      ((H n).extendAt (hend n) (G n) (hG n) (hat n) (hτs n)).toHistory.activeStage
        ((H n).extendAtTime (hend n) (G n) (hG n) (hat n) (hτs n)) = Fin.last (H n).eventCount :=
    fun n => (H n).activeStage_extendHorizon_eq_last _ _ _ _ (hat n).le
  have hin := fun n => (H n).extendAt_traced_limit_inputs (hend n) (G n) (hG n) (hat n) (hτs n)
    (hpinch n) (hpinchG n) (hderiv n) (hderivG n) (hclass n) (hcanG n) (hnc n) (hncG n)
  have hlast : ∀ n, ((H n).extendAt (hend n) (G n) (hG n) (hat n) (hτs n)).toHistory.activeStage
      ((H n).extendAtTime (hend n) (G n) (hG n) (hat n) (hτs n)) = Fin.last (H n).eventCount →
      ∃ h : ((H n).extendAt (hend n) (G n) (hG n) (hat n) (hτs n)).time
          (Fin.last (H n).eventCount) <
          ((H n).extendAt (hend n) (G n) (hG n) (hat n) (hτs n)).horizon,
        Perelman.PhiAlmostNonnegative
          (((H n).extendAt (hend n) (G n) (hG n) (hat n) (hτs n)).finalSlab h).flow
          (Icc (((H n).extendAt (hend n) (G n) (hG n) (hat n) (hτs n)).time
            (Fin.last (H n).eventCount))
            ((H n).extendAt (hend n) (G n) (hG n) (hat n) (hτs n)).horizon) phi := fun n _ =>
    extendHorizon_finalSlab_phiAlmostNonnegative (hT := hat n) (hTs := hτs n) (hpinchG n)
  have htop : ∀ n, ((H n).extendAt (hend n) (G n) (hG n) (hat n) (hτs n)).time
      (((H n).extendAt (hend n) (G n) (hG n) (hat n) (hτs n)).toHistory.activeStage
        ((H n).extendAtTime (hend n) (G n) (hG n) (hat n) (hτs n))) <
      (H n).extendAtTime (hend n) (G n) (hG n) (hat n) (hτs n) := by
    intro n
    rw [hlastt n]
    exact hat n
  have hq : ∀ c : ℝ, 0 < c → ∀ᶠ n in atTop, qcan < c * R n := fun c hc =>
    (hRlim.eventually_gt_atTop (qcan / c)).mono fun n hn => by rwa [div_lt_iff₀ hc, mul_comm] at hn
  have hclass' : ∀ n, ((H n).extendAt (hend n) (G n) (hG n) (hat n)
      (hτs n)).EventSlabsStronglyCanonical ε ε₁ C1 C2 qcan (Fin.last (H n).eventCount) := fun n =>
    ((H n).eventSlabsStronglyCanonical_extendHorizon_iff (τ n) (hend n ▸ (hat n).le)
      ((G n).closedPrefix (τ n) (hat n) (hτs n)) (hG n) ε ε₁ C1 C2 qcan
      (Fin.last (H n).eventCount)).2 (hclass n)
  have hterm : ∀ n (v : Icc (0 : ℝ) ((H n).extendAt (hend n) (G n) (hG n) (hat n)
      (hτs n)).toHistory.horizon),
      v ≤ (H n).extendAtTime (hend n) (G n) (hG n) (hat n) (hτs n) →
      ((H n).extendAt (hend n) (G n) (hG n) (hat n) (hτs n)).time
        (((H n).extendAt (hend n) (G n) (hG n) (hat n) (hτs n)).toHistory.activeStage v) < v →
      ((H n).extendAt (hend n) (G n) (hG n) (hat n) (hτs n)).toHistory.activeStage v =
        Fin.last (H n).eventCount →
      ∃ (s' : ℝ) (G' : (((H n).extendAt (hend n) (G n) (hG n) (hat n) (hτs n)).stage
          (((H n).extendAt (hend n) (G n) (hG n) (hat n) (hτs n)).toHistory.activeStage
            v)).IncomingSlab (((H n).extendAt (hend n) (G n) (hG n) (hat n) (hτs n)).time
          (((H n).extendAt (hend n) (G n) (hG n) (hat n) (hτs n)).toHistory.activeStage v)) s'),
        (v : ℝ) < s' ∧
        (∀ τ' ∈ Icc (((H n).extendAt (hend n) (G n) (hG n) (hat n) (hτs n)).time
            (((H n).extendAt (hend n) (G n) (hG n) (hat n) (hτs n)).toHistory.activeStage v))
            (v : ℝ),
          G'.flow.base.metric τ' =
            ((H n).extendAt (hend n) (G n) (hG n) (hat n) (hτs n)).toHistory.stageMetric
              (((H n).extendAt (hend n) (G n) (hG n) (hat n) (hτs n)).toHistory.activeStage v)
              τ') ∧
        ((H n).extendAt (hend n) (G n) (hG n) (hat n) (hτs n)).StronglyCanonicalBefore
          (((H n).extendAt (hend n) (G n) (hG n) (hat n) (hτs n)).toHistory.activeStage v) G'
          ε ε₁ C1 C2 qcan s' := fun n v _ _ hv =>
    (H n).exists_slab_stronglyCanonicalBefore_extendHorizon_closedPrefix (hend n) (G n) (hG n)
      (hat n) (hτs n) (hcanG n) v hv
  have hball0 : ∀ A : ℝ, 0 < A → ∃ Qlow Qup : ℝ, 0 < Qlow ∧ ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf
          (((H n).extendAt (hend n) (G n) (hG n) (hat n) (hτs n)).toHistory.stageMetric
            (((H n).extendAt (hend n) (G n) (hG n) (hat n) (hτs n)).toHistory.activeStage
              ((H n).extendAtTime (hend n) (G n) (hG n) (hat n) (hτs n)))
            ((H n).extendAtTime (hend n) (G n) (hG n) (hat n) (hτs n))) (y n)
          (A / Real.sqrt (R n)),
        Qlow * R n ≤ metricScalarAt
            (((H n).extendAt (hend n) (G n) (hG n) (hat n) (hτs n)).toHistory.stageMetric
              (((H n).extendAt (hend n) (G n) (hG n) (hat n) (hτs n)).toHistory.activeStage
                ((H n).extendAtTime (hend n) (G n) (hG n) (hat n) (hτs n)))
              ((H n).extendAtTime (hend n) (G n) (hG n) (hat n) (hτs n))) x ∧
          metricScalarAt
            (((H n).extendAt (hend n) (G n) (hG n) (hat n) (hτs n)).toHistory.stageMetric
              (((H n).extendAt (hend n) (G n) (hG n) (hat n) (hτs n)).toHistory.activeStage
                ((H n).extendAtTime (hend n) (G n) (hG n) (hat n) (hτs n)))
              ((H n).extendAtTime (hend n) (G n) (hG n) (hat n) (hτs n))) x ≤ Qup * R n := by
    intro A hA
    obtain ⟨Qlow, hQlow, h1⟩ := hballLow A hA
    obtain ⟨Qup, h2⟩ := hballUp A hA
    exact ⟨Qlow, Qup, hQlow, (h1.and h2).mono fun n hn x hx => ⟨hn.1 x hx, hn.2 x hx⟩⟩
  have htraced0 := exists_eventually_isTracedRegion_of_forall_neckAlternative_at_top
    (fun n => (H n).extendAt (hend n) (G n) (hG n) (hat n) (hτs n))
    (fun n => (H n).extendAtTime (hend n) (G n) (hG n) (hat n) (hτs n)) y R hRlim hphi
    (fun n => hpinch n) hlast htop hε₁ (qcan := fun _ => qcan) hq hclass'
    (fun n hl => hterm n _ le_rfl (htop n) hl) hball0 htopneck
  obtain ⟨ψ, hψ, Qup, -, hQup⟩ :=
    ObservedHistory.exists_subseq_scalar_le_on_normalized_balls_of_forall_radius_positive_depth
      (fun n => ((H n).extendAt (hend n) (G n) (hG n) (hat n) (hτs n)).toHistory)
      (fun n => (H n).extendAtTime (hend n) (G n) (hG n) (hat n) (hτs n)) y R hR hRlim htraced0 hκ
      hε (t₀ := fun n => (H n).extendAtTime (hend n) (G n) (hG n) (hat n) (hτs n)) (by simp)
      (fun n v p r hv hr hball' => (hin n).1 v p r hv hr hball') hphi
      (fun n v hv x => (hin n).2.1 v hv x) hε hεcross (C1 := C1) (C2 := C2) (Cq := Cq)
      (qs := fun _ => qcan) (fun n => by rw [mul_comm]; exact hqC n)
      (fun n v hv hev p hq' => (hin n).2.2.1 v hv.le hev p hq')
  have hRlimψ : Tendsto (fun i => R (ψ i)) atTop atTop := hRlim.comp hψ.tendsto_atTop
  have hRtψ : Tendsto (fun i => R (ψ i) * τ (ψ i)) atTop atTop := hRt.comp hψ.tendsto_atTop
  have hballψ : ∀ A : ℝ, 0 < A → ∃ Qlow : ℝ, 0 < Qlow ∧ ∀ᶠ i in atTop,
      ∀ x ∈ riemannianBallOf
          (((H (ψ i)).extendAt (hend (ψ i)) (G (ψ i)) (hG (ψ i)) (hat (ψ i))
            (hτs (ψ i))).toHistory.stageMetric
            (((H (ψ i)).extendAt (hend (ψ i)) (G (ψ i)) (hG (ψ i)) (hat (ψ i))
              (hτs (ψ i))).toHistory.activeStage
              ((H (ψ i)).extendAtTime (hend (ψ i)) (G (ψ i)) (hG (ψ i)) (hat (ψ i)) (hτs (ψ i))))
            ((H (ψ i)).extendAtTime (hend (ψ i)) (G (ψ i)) (hG (ψ i)) (hat (ψ i)) (hτs (ψ i))))
          (y (ψ i)) (A / Real.sqrt (R (ψ i))),
        Qlow * R (ψ i) ≤ metricScalarAt
            (((H (ψ i)).extendAt (hend (ψ i)) (G (ψ i)) (hG (ψ i)) (hat (ψ i))
              (hτs (ψ i))).toHistory.stageMetric
              (((H (ψ i)).extendAt (hend (ψ i)) (G (ψ i)) (hG (ψ i)) (hat (ψ i))
                (hτs (ψ i))).toHistory.activeStage
                ((H (ψ i)).extendAtTime (hend (ψ i)) (G (ψ i)) (hG (ψ i)) (hat (ψ i))
                  (hτs (ψ i))))
              ((H (ψ i)).extendAtTime (hend (ψ i)) (G (ψ i)) (hG (ψ i)) (hat (ψ i))
                (hτs (ψ i)))) x ∧
          metricScalarAt
            (((H (ψ i)).extendAt (hend (ψ i)) (G (ψ i)) (hG (ψ i)) (hat (ψ i))
              (hτs (ψ i))).toHistory.stageMetric
              (((H (ψ i)).extendAt (hend (ψ i)) (G (ψ i)) (hG (ψ i)) (hat (ψ i))
                (hτs (ψ i))).toHistory.activeStage
                ((H (ψ i)).extendAtTime (hend (ψ i)) (G (ψ i)) (hG (ψ i)) (hat (ψ i))
                  (hτs (ψ i))))
              ((H (ψ i)).extendAtTime (hend (ψ i)) (G (ψ i)) (hG (ψ i)) (hat (ψ i))
                (hτs (ψ i)))) x ≤ Qup * R (ψ i) := by
    intro A hA
    obtain ⟨Qlow, hQlow, h1⟩ := hballLow A hA
    exact ⟨Qlow, hQlow, ((hψ.tendsto_atTop.eventually h1).and (hQup A hA)).mono
      fun i hi x hx => ⟨hi.1 x hx, hi.2 x hx⟩⟩
  have hdeepψ := hdeepL hκ hε hεD hphi
    (fun i => ((H (ψ i)).extendAt (hend (ψ i)) (G (ψ i)) (hG (ψ i)) (hat (ψ i))
      (hτs (ψ i))).toHistory)
    (fun i => (H (ψ i)).extendAtTime (hend (ψ i)) (G (ψ i)) (hG (ψ i)) (hat (ψ i)) (hτs (ψ i)))
    (fun i => y (ψ i)) (fun i => R (ψ i)) (fun i => hR (ψ i)) (fun i => hscal (ψ i)) hRlimψ
    (fun i => htop (ψ i)) (fun i v p r hv hr hball' => (hin (ψ i)).1 v p r hv hr hball')
    (fun i v hv x => (hin (ψ i)).2.1 v hv x) (fun i => hqC (ψ i))
    (fun i v hv hev p hq' => (hin (ψ i)).2.2.1 v hv hev p hq')
    (fun i v hv hev p hq' => (hin (ψ i)).2.2.2 v hv hev p hq')
    (fun A c hA hc => hψ.tendsto_atTop.eventually (htopneck A c hA hc))
    (fun i => S (ψ i)) (fun i => V (ψ i)) (fun i => W (ψ i)) (fun i => hV (ψ i))
    (fun i => hW (ψ i)) (fun i => hVW (ψ i)) (fun i => hS (ψ i))
    (fun A hA => hψ.tendsto_atTop.eventually (hpoints A hA))
  have htraced := exists_isTracedRegion_of_forall_neckAlternative_of_staggered_supply
    (fun i => (H (ψ i)).extendAt (hend (ψ i)) (G (ψ i)) (hG (ψ i)) (hat (ψ i)) (hτs (ψ i)))
    (fun i => (H (ψ i)).extendAtTime (hend (ψ i)) (G (ψ i)) (hG (ψ i)) (hat (ψ i)) (hτs (ψ i)))
    (fun i => y (ψ i)) (fun i => R (ψ i)) hRlimψ hRtψ hphi (fun i => hpinch (ψ i))
    (fun i => hlast (ψ i)) (fun i => htop (ψ i)) hε₁ (qcan := fun _ => qcan)
    (fun c hc => hψ.tendsto_atTop.eventually (hq c hc)) (fun i => hclass' (ψ i))
    (fun i => hterm (ψ i)) hballψ
    (fun A c hA hc => hψ.tendsto_atTop.eventually (htopneck A c hA hc)) hdeepψ
  obtain ⟨ψ', -, hψneck⟩ := hline
    (fun i => ((H (ψ i)).extendAt (hend (ψ i)) (G (ψ i)) (hG (ψ i)) (hat (ψ i))
      (hτs (ψ i))).toHistory)
    (fun i => (H (ψ i)).extendAtTime (hend (ψ i)) (G (ψ i)) (hG (ψ i)) (hat (ψ i)) (hτs (ψ i)))
    (fun i => y (ψ i)) (fun i => R (ψ i)) (fun i => hR (ψ i)) (fun i => hscal (ψ i)) hRlimψ
    htraced hκ hε
    (t₀ := fun i => (H (ψ i)).extendAtTime (hend (ψ i)) (G (ψ i)) (hG (ψ i)) (hat (ψ i))
      (hτs (ψ i))) (by simp)
    (fun i v p r hv hr hball' => (hin (ψ i)).1 v p r hv hr hball') hphi
    (fun i v hv x => (hin (ψ i)).2.1 v hv x) hε hεW₀ (C1 := C1) (C2 := C2) (Cs := Cq)
    (Cq := Cq) (Ctime := Ctime) (qs := fun _ => qcan) (qcan := fun _ => qcan)
    (fun i => hqC (ψ i)) (fun i => hqC (ψ i))
    (fun i v hv hev p hq' => (hin (ψ i)).2.2.1 v hv.le hev p hq')
    (fun i v hv hev p hq' => (hin (ψ i)).2.2.2 v hv hev p hq')
    (fun i => S (ψ i)) (fun i => V (ψ i)) (fun i => W (ψ i)) (fun i => hV (ψ i))
    (fun i => hW (ψ i)) (fun i => hVW (ψ i)) (B := 7) (by norm_num) (fun i => hS (ψ i))
    (fun A hA => hψ.tendsto_atTop.eventually (hpoints A hA))
  obtain ⟨i, hi⟩ := (hψneck eps heps heps11).exists
  exact hnoneck (ψ (ψ' i)) hi

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory

end
