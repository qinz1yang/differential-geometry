import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SpatialCrossingContinuation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SpatialCanonicalContinuationCases
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CapWindowPointTimeSlack
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SlabTimeWindowContinuity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SliverForwardComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RetainedCoreHistoryPrefixInvariants
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RetainedCoreHistoryExtendAtBefore
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CrossingTracedRegion
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CrossingTimeZeroBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CrossingDepthExtension
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CrossingAncientLimitSpatial
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegionAncientLimitDerivativeCutoff
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CrossingWindowAnchorBound

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold NNReal Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace RetainedCoreHistory

variable {P₀ : OrientedThreeStage.{u}}

private theorem derivativeBoundBefore_double {P : OrientedThreeStage.{u}} {a s : ℝ}
    {G : P.IncomingSlab a s} {Ctime : ℝ≥0} {q t₀ : ℝ} (hq : 0 ≤ q)
    (h : G.DerivativeBoundBefore Ctime q t₀) :
    G.DerivativeBoundBefore (2 * Ctime) (2 * q) t₀ := by
  intro y t ht hqy
  refine (h y t ht (by linarith)).trans ?_
  push_cast
  nlinarith [Ctime.coe_nonneg, sq_nonneg (G.flow.scalar t y)]

private theorem exists_spatial_crossing_bad_point (H : RetainedCoreHistory P₀) {s : ℝ}
    (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s)
    {p : CutoffParameters} (records : ∀ i, GeometricCutoffRecord H.toHistory i p)
    (Φ : (H.stage (Fin.last H.eventCount)).Carrier → ℝ → Prop)
    {qcan qs ζ ζ' ς η₃ t₀ : ℝ} {Ctime : ℝ≥0}
    (hζ : 0 < ζ) (hζ' : 0 < ζ') (hς : 0 < ς) (hη₃ : 0 < η₃) (hq : 0 ≤ qcan)
    (ht₀ : t₀ ∈ Ico (H.time (Fin.last H.eventCount)) s)
    (hdb : G.DerivativeBoundBefore Ctime qcan t₀) (hdOn : G.DerivativeBoundOn Ctime qcan t₀ η₃)
    (hfail : ∀ η : ℝ, 0 < η → η ≤ η₃ → t₀ + η ≤ s →
      ∃ (y : (H.stage (Fin.last H.eventCount)).Carrier) (t : ℝ),
        H.time (Fin.last H.eventCount) < t ∧ t₀ ≤ t ∧ t < t₀ + η ∧ t < s ∧
        qs < G.flow.scalar t y ∧ Φ y t) :
    ∃ η : ℝ, 0 < η ∧ t₀ + η < s ∧
      G.DerivativeBoundBefore (2 * Ctime) (2 * qcan) (t₀ + η) ∧
      (∀ t ∈ Icc t₀ (t₀ + η), ∀ x : (H.stage (Fin.last H.eventCount)).Carrier,
        G.flow.scalar t x * η ≤ ζ ∧ |G.flow.scalar t x - G.flow.scalar t₀ x| ≤ ζ' ∧
        ∀ v : TangentSpace ThreeModel x,
          (G.flow.base.metric t).inner x v v ≤
            Real.exp 1 * (G.flow.base.metric t₀).inner x v v ∧
          (G.flow.base.metric t₀).inner x v v ≤
            Real.exp 1 * (G.flow.base.metric t).inner x v v) ∧
      (∃ S : ℝ, 0 < S ∧ (∀ i b, ((records i).static b).neck.scale ≤ S) ∧ S * η ≤ ς) ∧
      ∃ (y : (H.stage (Fin.last H.eventCount)).Carrier) (t : ℝ),
        H.time (Fin.last H.eventCount) < t ∧ t₀ ≤ t ∧ t < t₀ + η ∧ t < s ∧
        qs < G.flow.scalar t y ∧ Φ y t := by
  obtain ⟨K₀, hK₀⟩ := G.exists_forall_Icc_riemannNorm_le (b := t₀) ht₀.2
  have hK : ∀ x, G.riemannNorm t₀ x ≤ max K₀ 1 :=
    fun x => (hK₀ t₀ ⟨ht₀.1, le_rfl⟩ x).trans (le_max_left _ _)
  obtain ⟨η₁, hη₁, -, hη₁s, hsl⟩ :=
    G.exists_sliver_forward_comparison (lt_max_of_lt_right one_pos) hζ ht₀ hK
  obtain ⟨δ, hδ, -, hclose⟩ := G.exists_forall_Icc_scalar_riemannNorm_metric_close ht₀ hζ'
  obtain ⟨S, hS, hSle⟩ := H.exists_forall_neck_scale_le records
  have hst : 0 < (s - t₀) / 2 := by linarith [ht₀.2]
  set η : ℝ := min (min ((s - t₀) / 2) η₁) (min δ (min (ς / S) η₃)) with hηdef
  have hηs : η ≤ (s - t₀) / 2 := (min_le_left _ _).trans (min_le_left _ _)
  have hηη₁ : η ≤ η₁ := (min_le_left _ _).trans (min_le_right _ _)
  have hηδ : η ≤ δ := (min_le_right _ _).trans (min_le_left _ _)
  have hηS : η ≤ ς / S := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hηη₃ : η ≤ η₃ := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hηpos : 0 < η := lt_min (lt_min hst hη₁) (lt_min hδ (lt_min (div_pos hς hS) hη₃))
  have hηlt : t₀ + η < s := by linarith
  refine ⟨η, hηpos, hηlt, derivativeBoundBefore_double hq
    (G.derivativeBoundBefore_of_derivativeBoundOn hdb hdOn (by linarith) hηlt.le),
    fun t ht x => ?_, ⟨S, hS, hSle, ?_⟩, hfail η hηpos hηη₃ hηlt.le⟩
  · have ht₁ : t ∈ Icc t₀ (t₀ + η₁) := ⟨ht.1, ht.2.trans (by linarith)⟩
    obtain ⟨-, hR, hmet, -⟩ := hsl t ht₁
    refine ⟨?_, ?_, fun v => hmet x v⟩
    · obtain ⟨-, hRη⟩ := hR x
      rcases le_total 0 (G.flow.scalar t x) with h0 | h0
      · exact (mul_le_mul_of_nonneg_left hηη₁ h0).trans hRη
      · exact (mul_nonpos_of_nonpos_of_nonneg h0 hηpos.le).trans hζ.le
    · have hmax : max (H.time (Fin.last H.eventCount)) (t₀ - δ) ≤ t₀ :=
        max_le ht₀.1 (by linarith)
      exact (hclose t ⟨hmax.trans ht.1, by linarith [ht.2]⟩ t₀ ⟨hmax, by linarith⟩ x).1
  · have := (le_div_iff₀ hS).mp hηS
    linarith

private theorem le_static_scale_of_neckRadius_le {H : RetainedCoreHistory P₀}
    {p₀ p : CutoffParameters} {δ₀ ρ₀ : ℝ}
    {records : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i p}
    (hrec : H.IsCanonicalCutoffRecordFamily p₀ δ₀ ρ₀ records)
    (hΛδ : p₀.recenterConstant * δ₀ ≤ 1 / 2) {X : ℝ} (hX : 0 < X)
    (hρ : ρ₀ ≤ Real.sqrt (1 / (2 * X))) (i : Fin H.eventCount)
    (b : (H.toHistory.event i).RetainedBoundaryIndex) :
    X ≤ ((records i).static b).neck.scale := by
  have hlt := hrec.inv_two_mul_sq_lt_static_scale hΛδ i b
  have hρpos : 0 < ρ₀ :=
    (p.neckRadius_pos _ (H.toHistory.time_nonneg i.succ)).trans_le (hrec.2.2.2.2.2.2.2 i)
  have hsq : ρ₀ ^ 2 ≤ 1 / (2 * X) :=
    calc ρ₀ ^ 2 ≤ Real.sqrt (1 / (2 * X)) ^ 2 := pow_le_pow_left₀ hρpos.le hρ 2
      _ = 1 / (2 * X) := Real.sq_sqrt (by positivity)
  have h2 : 2 * ρ₀ ^ 2 ≤ X⁻¹ :=
    calc 2 * ρ₀ ^ 2 ≤ 2 * (1 / (2 * X)) := by linarith
      _ = X⁻¹ := by rw [one_div, mul_inv, ← mul_assoc, mul_inv_cancel₀ two_ne_zero, one_mul]
  have h3 := inv_anti₀ (by positivity) h2
  rw [inv_inv] at h3
  exact h3.trans hlt.le

private theorem metricScalarAt_extendAt_eq (H : RetainedCoreHistory P₀)
    (hend : H.time (Fin.last H.eventCount) = H.horizon) {s : ℝ}
    (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s)
    (hG : G.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount)) {t : ℝ}
    (hat : H.time (Fin.last H.eventCount) < t) (hts : t < s)
    (y : (H.stage (Fin.last H.eventCount)).Carrier)
    (ŷ : ((H.extendAt hend G hG hat hts).toHistory.stageAt
      (H.extendAtTime hend G hG hat hts)).Carrier) (hŷ : HEq ŷ y) :
    metricScalarAt ((H.extendAt hend G hG hat hts).toHistory.stageMetric
        ((H.extendAt hend G hG hat hts).toHistory.activeStage
          (H.extendAtTime hend G hG hat hts)) (H.extendAtTime hend G hG hat hts)) ŷ =
      G.flow.scalar t y := by
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

private theorem exists_spatialCanonicalWitness_of_extendAt (H : RetainedCoreHistory P₀)
    (hend : H.time (Fin.last H.eventCount) = H.horizon) {s : ℝ}
    (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s)
    (hG : G.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount)) {t : ℝ}
    (hat : H.time (Fin.last H.eventCount) < t) (hts : t < s)
    (y : (H.stage (Fin.last H.eventCount)).Carrier)
    (ŷ : ((H.extendAt hend G hG hat hts).toHistory.stageAt
      (H.extendAtTime hend G hG hat hts)).Carrier) (hŷ : HEq ŷ y) {ε C1 C2 : ℝ}
    (W : SpatialCanonicalWitness ((H.extendAt hend G hG hat hts).toHistory.stageMetric
        ((H.extendAt hend G hG hat hts).toHistory.activeStage
          (H.extendAtTime hend G hG hat hts)) (H.extendAtTime hend G hG hat hts)) ε C1 C2 ŷ)
    (hW : W.capTubeHasNeckChart ε) :
    ∃ W' : SpatialCanonicalWitness (G.flow.base.metric t) ε C1 C2 y,
      W'.capTubeHasNeckChart ε := by
  have hlast : (H.extendAt hend G hG hat hts).toHistory.activeStage
      (H.extendAtTime hend G hG hat hts) = Fin.last H.eventCount :=
    H.activeStage_extendHorizon_eq_last (hend ▸ hat.le) (G.closedPrefix t hat hts) hG
      (H.extendAtTime hend G hG hat hts) hat.le
  have hmet : (H.extendAt hend G hG hat hts).toHistory.stageMetric (Fin.last H.eventCount)
      (H.extendAtTime hend G hG hat hts) = G.flow.base.metric t :=
    H.stageMetric_extendHorizon_last_of_mem_Icc (hend ▸ hat.le) (G.closedPrefix t hat hts) hG
      ⟨hat.le, le_rfl⟩
  revert W hW ŷ
  change ∀ ŷ : ((H.extendAt hend G hG hat hts).toHistory.stage
      ((H.extendAt hend G hG hat hts).toHistory.activeStage
        (H.extendAtTime hend G hG hat hts))).Carrier, HEq ŷ y →
    ∀ W : SpatialCanonicalWitness ((H.extendAt hend G hG hat hts).toHistory.stageMetric
        ((H.extendAt hend G hG hat hts).toHistory.activeStage
          (H.extendAtTime hend G hG hat hts)) (H.extendAtTime hend G hG hat hts)) ε C1 C2 ŷ,
      W.capTubeHasNeckChart ε → _
  generalize (H.extendAt hend G hG hat hts).toHistory.activeStage
    (H.extendAtTime hend G hG hat hts) = k at hlast ⊢
  subst hlast
  intro ŷ hŷ
  obtain rfl := eq_of_heq hŷ
  rw [hmet]
  exact fun W hW => ⟨W, hW⟩

end RetainedCoreHistory

theorem spatialCrossingContinuation_holds (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) :
    SpatialCrossingContinuation P₀ g₀ := by
  obtain ⟨epsW, hepsW, hX5⟩ :=
    ObservedHistory.exists_eventually_spatialCanonicalWitness_of_isTracedRegion.{u}
  refine ⟨min coneAccuracy (min epsW (min crossingNeckAccuracy.{u} crossingWindowNeckAccuracy.{u})),
    lt_min coneAccuracy_pos (lt_min hepsW (lt_min crossingNeckAccuracy_pos
      crossingWindowNeckAccuracy_pos)), min_le_left _ _, ?_⟩
  intro ε hε hε11 hεbar
  have hεcone : ε ≤ coneAccuracy := hεbar.trans (min_le_left _ _)
  have hεW : ε ≤ epsW := hεbar.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hεN : ε ≤ crossingNeckAccuracy.{u} :=
    hεbar.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hεWN : ε ≤ crossingWindowNeckAccuracy.{u} :=
    hεbar.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨C, hC1, hX5⟩ := hX5 ε hε hε11 hεW
  refine ⟨C, hC1, ?_⟩
  intro B hB C1 C2 τmin Ctime Cgrad hC1le hC2le hτle C1s C2s Cs hC1s hC2s hCs κ phi θ hκ hphi
    hθ
  by_contra hneg
  push Not at hneg
  choose qcan hqcan hneg using fun n : ℕ =>
    hneg ((n : ℝ) + 1) (1 - 1 / ((n : ℝ) + 2)) ((n : ℝ) + 1) (n + 2) (by positivity) (by
        have : (0 : ℝ) < 1 / ((n : ℝ) + 2) := by positivity
        linarith) (by positivity)
  have hq0 : ∀ n : ℕ, 0 < qcan n := fun n =>
    (by positivity : (0 : ℝ) < (n : ℝ) + 1).trans_le (hqcan n)
  have hpack : ∀ n : ℕ, ∃ (H : RetainedCoreHistory P₀) (s : ℝ)
      (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s)
      (p p₀ : CutoffParameters) (records : ∀ i, GeometricCutoffRecord H.toHistory i p)
      (δb ρb qs t₀ η t : ℝ) (y : (H.stage (Fin.last H.eventCount)).Carrier)
      (hH : H.InCutoffClass g₀ B p₀ δb ρb) (hG : H.IsContinuationSlab B (Fin.last H.eventCount) G),
      H.IsCanonicalCutoffRecordFamily p₀ δb ρb records ∧
      ((n : ℝ) + 1 ≤ qcan n ∧ qcan n ≤ qs ∧ qs ≤ Cs * qcan n) ∧
      (p₀.modelAccuracy ≤ 1 / ((n : ℝ) + 1) ∧ (n : ℝ) + 1 ≤ (n : ℝ) + 1 ∧
        (n : ℝ) + 1 ≤ p₀.modelRadius ∧ n + 2 ≤ p₀.modelOrder ∧ δb ≤ 1 / ((n : ℝ) + 1)) ∧
      (∀ i b, ((n : ℝ) + 1) * qcan n ≤ ((records i).static b).neck.scale) ∧
      (H.EventSlabsPinched phi ∧
        Perelman.PhiAlmostNonnegative G.flow (Ico (H.time (Fin.last H.eventCount)) s) phi) ∧
      (H.EventSlabsCanonical ε C1 C2 (qcan n) τmin (Fin.last H.eventCount) ∧
        H.EventSlabsDerivative Ctime (qcan n) (Fin.last H.eventCount) ∧
        H.EventSlabsGradient Cgrad (qcan n) (Fin.last H.eventCount) ∧
        H.EventSlabsSpatiallyCanonical ε C1s C2s qs (Fin.last H.eventCount) ∧
        H.NoncollapsedBefore κ ε (H.time (Fin.last H.eventCount))) ∧
      (t₀ ∈ Ico (H.time (Fin.last H.eventCount)) s ∧
        G.CanonicalBefore ε C1 C2 (qcan n) τmin t₀ ∧
        G.DerivativeBoundBefore Ctime (qcan n) t₀ ∧
        G.GradientBoundBefore Cgrad (qcan n) t₀ ∧
        G.SpatiallyCanonicalBefore ε C1s C2s qs t₀ ∧
        H.TerminalNoncollapsedBefore hH.2.1 G hG.2 κ ε t₀) ∧
      (0 < η ∧ t₀ + η < s ∧ G.DerivativeBoundBefore (2 * Ctime) (2 * qcan n) (t₀ + η) ∧
        (∀ t' ∈ Icc t₀ (t₀ + η), ∀ x, G.flow.scalar t' x * η ≤ 1 / ((n : ℝ) + 1) ∧
          |G.flow.scalar t' x - G.flow.scalar t₀ x| ≤ qcan n / 4 ∧
          ∀ v : TangentSpace ThreeModel x,
            (G.flow.base.metric t').inner x v v ≤
              Real.exp 1 * (G.flow.base.metric t₀).inner x v v ∧
            (G.flow.base.metric t₀).inner x v v ≤
              Real.exp 1 * (G.flow.base.metric t').inner x v v) ∧
        ∀ i b, ((records i).static b).neck.scale * η ≤ 1 / ((n : ℝ) + 2)) ∧
      (H.time (Fin.last H.eventCount) < t ∧ t₀ ≤ t ∧ t < t₀ + η ∧ qcan n < G.flow.scalar t y ∧
        G.flow.scalar t y * (t - H.time (Fin.last H.eventCount)) < θ ∧
        ¬ H.CapWindowPoint records (Fin.last H.eventCount) y t ((n : ℝ) + 1)
          (1 - 1 / ((n : ℝ) + 2))) ∧
      ¬ ∃ W : SpatialCanonicalWitness (G.flow.base.metric t) ε C C y,
        W.capTubeHasNeckChart ε := by
    intro n
    have hsq : (0 : ℝ) < 1 / (2 * (((n : ℝ) + 1) * qcan n)) :=
      div_pos one_pos (mul_pos two_pos (mul_pos (by positivity) (hq0 n)))
    obtain ⟨qs, hqs1, hqs2, p₀, δb, ρb, hacc, hrad, hord, hδb, hρb, H, hH, p, records, hrec,
        hpinch, hfail⟩ :=
      hneg n (1 / ((n : ℝ) + 1)) (Real.sqrt (1 / (2 * (((n : ℝ) + 1) * qcan n))))
        (1 / ((n : ℝ) + 1)) (by positivity) (Real.sqrt_pos.mpr hsq) (by positivity)
    have hqn : (n : ℝ) + 1 ≤ qcan n ∧ qcan n ≤ qs ∧ qs ≤ Cs * qcan n := ⟨hqcan n, hqs1, hqs2⟩
    have hparn : p₀.modelAccuracy ≤ 1 / ((n : ℝ) + 1) ∧ (n : ℝ) + 1 ≤ (n : ℝ) + 1 ∧
        (n : ℝ) + 1 ≤ p₀.modelRadius ∧ n + 2 ≤ p₀.modelOrder ∧ δb ≤ 1 / ((n : ℝ) + 1) :=
      ⟨hacc, le_rfl, hrad, hord, hδb⟩
    rcases imp_iff_not_or.mp hfail with hev | hterm
    · push Not at hev
      obtain ⟨j, hcan, hder, hgrad, hspat, t₀, ht₀, hcb, hdb, hgb, hsb, hnc, η₃, hη₃, hdOn, hgOn,
        hcOn, hfail⟩ := hev
      obtain ⟨η, hη, hηs, hder2, hsl, ⟨S, -, hSle, hSη⟩, y, t, hat, ht₀t, htη, hts, hqR, hθ',
          hcwp, hcl⟩ :=
        RetainedCoreHistory.exists_spatial_crossing_bad_point (H.prefixAt j.castSucc)
          (H.toHistory.event j).incoming (H.prefixRecords j.castSucc records)
          (fun y t => (H.toHistory.event j).incoming.flow.scalar t y * (t - H.time j.castSucc) < θ ∧
            ¬ H.CapWindowPoint records j.castSucc y t ((n : ℝ) + 1) (1 - 1 / ((n : ℝ) + 2)) ∧
            ∀ W : SpatialCanonicalWitness ((H.toHistory.event j).incoming.flow.base.metric t)
              ε C C y, ¬ W.capTubeHasNeckChart ε)
          (ζ := 1 / ((n : ℝ) + 1)) (ζ' := qcan n / 4) (ς := 1 / ((n : ℝ) + 2)) (by positivity)
          (div_pos (hq0 n) (by norm_num)) (by positivity) hη₃ (hq0 n).le ht₀ hdb hdOn
          (fun η hη hηη₃ hηs => (hfail η hη hηη₃ hηs).imp fun y hy => hy.imp fun t ht =>
            ⟨ht.1, ht.2.1, ht.2.2.1, ht.2.2.2.1, ht.2.2.2.2.1, ht.2.2.2.2.2.1, ht.2.2.2.2.2.2.1,
              ht.2.2.2.2.2.2.2⟩)
      exact ⟨H.prefixAt j.castSucc, H.time j.succ, (H.toHistory.event j).incoming, p, p₀,
        H.prefixRecords j.castSucc records, δb, ρb, qs, t₀, η, t, y,
        H.inCutoffClass_prefixAt hH j.castSucc,
        ⟨(H.isContinuationSlab_event hH.2.2.1 j).1, H.event_initial j⟩,
        H.isCanonicalCutoffRecordFamily_prefixAt j.castSucc hrec, hqn, hparn,
        fun i b => RetainedCoreHistory.le_static_scale_of_neckRadius_le
          (H.isCanonicalCutoffRecordFamily_prefixAt j.castSucc hrec) hH.2.2.2.2
          (mul_pos (by positivity) (hq0 n)) hρb i b,
        ⟨H.eventSlabsPinched_prefixAt j.castSucc hpinch, hpinch j⟩,
        ⟨H.eventSlabsCanonical_prefixAt j.castSucc hcan,
          H.eventSlabsDerivative_prefixAt j.castSucc hder,
          H.eventSlabsGradient_prefixAt j.castSucc hgrad,
          H.eventSlabsSpatiallyCanonical_prefixAt j.castSucc hspat,
          H.noncollapsedBefore_prefixAt j.castSucc hnc ht₀.1⟩,
        ⟨ht₀, hcb, hdb, hgb, hsb, H.terminalNoncollapsedBefore_prefixAt j hnc⟩,
        ⟨hη, hηs, hder2, hsl, fun i b =>
          (mul_le_mul_of_nonneg_right (hSle i b) hη.le).trans hSη⟩,
        ⟨hat, ht₀t, htη, hqs1.trans_lt hqR, hθ',
          fun h' => hcwp (H.capWindowPoint_of_prefixAt j records h')⟩,
        fun ⟨W, hW⟩ => hcl W hW⟩
    · obtain ⟨s, G, hG, hpG, hcan, hder, hgrad, hspat, hncL, t₀, ht₀, hcb, hdb, hgb, hsb, hnc,
        η₃, hη₃, hdOn, hgOn, hcOn, hfail⟩ := hterm
      obtain ⟨η, hη, hηs, hder2, hsl, ⟨S, -, hSle, hSη⟩, y, t, hat, ht₀t, htη, hts, hqR, hθ',
          hcwp, hcl⟩ :=
        RetainedCoreHistory.exists_spatial_crossing_bad_point H G records
          (fun y t => G.flow.scalar t y * (t - H.time (Fin.last H.eventCount)) < θ ∧
            ¬ H.CapWindowPoint records (Fin.last H.eventCount) y t ((n : ℝ) + 1)
              (1 - 1 / ((n : ℝ) + 2)) ∧
            ∀ W : SpatialCanonicalWitness (G.flow.base.metric t) ε C C y,
              ¬ W.capTubeHasNeckChart ε)
          (ζ := 1 / ((n : ℝ) + 1)) (ζ' := qcan n / 4) (ς := 1 / ((n : ℝ) + 2)) (by positivity)
          (div_pos (hq0 n) (by norm_num)) (by positivity) hη₃ (hq0 n).le ht₀ hdb hdOn
          (fun η hη hηη₃ hηs => (hfail η hη hηη₃ hηs).imp fun y hy => hy.imp fun t ht =>
            ⟨ht.1, ht.2.1, ht.2.2.1, ht.2.2.2.1, ht.2.2.2.2.1, ht.2.2.2.2.2.1, ht.2.2.2.2.2.2.1,
              ht.2.2.2.2.2.2.2⟩)
      exact ⟨H, s, G, p, p₀, records, δb, ρb, qs, t₀, η, t, y, hH, hG, hrec, hqn, hparn,
        fun i b => RetainedCoreHistory.le_static_scale_of_neckRadius_le hrec hH.2.2.2.2
          (mul_pos (by positivity) (hq0 n)) hρb i b,
        ⟨hpinch, hpG⟩, ⟨hcan, hder, hgrad, hspat, hncL⟩, ⟨ht₀, hcb, hdb, hgb, hsb, hnc⟩,
        ⟨hη, hηs, hder2, hsl, fun i b =>
          (mul_le_mul_of_nonneg_right (hSle i b) hη.le).trans hSη⟩,
        ⟨hat, ht₀t, htη, hqs1.trans_lt hqR, hθ', hcwp⟩,
        fun ⟨W, hW⟩ => hcl W hW⟩
  choose H s G p p₀ records δb ρb qs t₀ η t y hH hG hrec hq hpar hscale hpinch hslabs hbefore
    hsliver hbad hclause using hpack
  have hts : ∀ n, t n < s n := fun n => (hbad n).2.2.1.trans (hsliver n).2.1
  have hRpos : ∀ n, 0 < (G n).flow.scalar (t n) (y n) := fun n =>
    (lt_of_lt_of_le (by positivity) (hq n).1).trans (hbad n).2.2.2.1
  have hR := RetainedCoreHistory.tendsto_scalar_at_bad_point_atTop hq hbad
  have hRt := RetainedCoreHistory.tendsto_scalar_mul_time_atTop_of_inCutoffClass (B := fun _ => B)
    hH G (fun n => (hG n).2) y (fun n => ⟨(hbad n).1.le, hts n⟩) hR
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
  let K : ℕ → RetainedCoreHistory P₀ := fun n =>
    (H n).extendAt (hH n).2.1 (G n) (hG n).2 (hbad n).1 (hts n)
  let τ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon := fun n =>
    (H n).extendAtTime (hH n).2.1 (G n) (hG n).2 (hbad n).1 (hts n)
  have hlast : ∀ n, (K n).toHistory.activeStage (τ n) = Fin.last (H n).eventCount := fun n =>
    (H n).activeStage_extendHorizon_eq_last ((hH n).2.1 ▸ (hbad n).1.le)
      ((G n).closedPrefix (t n) (hbad n).1 (hts n)) (hG n).2 _ (hbad n).1.le
  let ŷ : ∀ n, ((K n).toHistory.stageAt (τ n)).Carrier := fun n =>
    cast (congrArg (fun k => ((H n).stage k).Carrier) (hlast n).symm) (y n)
  have hŷ : ∀ n, HEq (ŷ n) (y n) := fun n => cast_heq _ _
  have htime : ∀ n, (K n).toHistory.time ((K n).toHistory.activeStage (τ n)) =
      (H n).time (Fin.last (H n).eventCount) := fun n => by rw [hlast n]; rfl
  have hlt : ∀ n, (K n).toHistory.time ((K n).toHistory.activeStage (τ n)) < (τ n : ℝ) :=
    fun n => by rw [htime n]; exact (hbad n).1
  have hscal : ∀ n, metricScalarAt ((K n).toHistory.stageMetric
      ((K n).toHistory.activeStage (τ n)) (τ n)) (ŷ n) = (G n).flow.scalar (t n) (y n) :=
    fun n => RetainedCoreHistory.metricScalarAt_extendAt_eq (H n) (hH n).2.1 (G n) (hG n).2
      (hbad n).1 (hts n) (y n) (ŷ n) (hŷ n)
  have hdin := fun n => (H n).derivativeBound_inputs_extendAt (hH n).2.1 (G n) (hG n).2 (hbad n).1
    (hts n) (hq0 n).le (hslabs n).2.1
    ((G n).derivativeBoundBefore_mono (hbad n).2.2.1.le (hsliver n).2.2.1)
  obtain ⟨ψ, hψ, hdich⟩ := exists_strictMono_maximal_depth
    (fun σ T => ObservedHistory.DepthExtendable (fun n => (K n).toHistory) τ ŷ
      (fun n => (G n).flow.scalar (t n) (y n)) σ T)
    (fun _ _ _ hT' hle h => ObservedHistory.DepthExtendable.mono_depth h hRpos hT' hle)
    (fun _ _ _ hψ h => ObservedHistory.DepthExtendable.comp h hψ)
    (fun _ _ _ hσ h => ObservedHistory.DepthExtendable.congr h hσ) id
    (RetainedCoreHistory.exists_subseq_depthExtendable_pos hε hεcone hκ hphi hCs hH hG hrec hq
      hpar hscale (fun _ => le_rfl) hpinch hslabs hbefore hsliver hbad hεN id strictMono_id ŷ hŷ)
  rcases hdich with hall | ⟨Tstar, hT, hall, hmax⟩
  · obtain ⟨σ, hσ, hall⟩ : ∃ σ : ℕ → ℕ, StrictMono σ ∧
        ∀ T : ℝ, 0 < T → ObservedHistory.DepthExtendable (fun n => (K n).toHistory) τ ŷ
          (fun n => (G n).flow.scalar (t n) (y n)) σ T :=
      ⟨ψ, hψ, hall⟩
    obtain ⟨ψ₃, hψ₃, hev⟩ := hX5 (fun m => (K (σ m)).toHistory) (fun m => τ (σ m))
      (fun m => ŷ (σ m)) (fun m => (G (σ m)).flow.scalar (t (σ m)) (y (σ m)))
      (fun m => hRpos (σ m)) (fun m => hscal (σ m)) (hR.comp hσ.tendsto_atTop)
      (fun m => hlt (σ m)) (fun A T hA hT => hall T hT A hA) hκ hε
      (t₀ := fun m => t₀ (σ m)) (hgap.comp hσ.tendsto_atTop)
      (fun m v p r hv hr hb => (H (σ m)).volume_ge_extendAt_of_terminalNoncollapsedBefore
        (hH (σ m)).2.1 (G (σ m)) (hG (σ m)).2 (hbad (σ m)).1 (hts (σ m)) (hslabs (σ m)).2.2.2.2
        (hbefore (σ m)).2.2.2.2.2 v p r hv hr hb)
      hphi
      (fun m v _ x => (H (σ m)).curvatureOperatorLowerBoundAt_extendAt_of_pinched (hH (σ m)).2.1
        (G (σ m)) (hG (σ m)).2 (hbad (σ m)).1 (hts (σ m)) (hpinch (σ m)).1 (hpinch (σ m)).2 v x)
      (C1s := C1s) (C2s := C2s) (Cs := Cs) (Cq := 2) (Ctime := 2 * Ctime)
      (qs := fun m => qs (σ m)) (qcan := fun m => 2 * qcan (σ m))
      (fun m => (hq (σ m)).2.2.trans
        (mul_le_mul_of_nonneg_left (hbad (σ m)).2.2.2.1.le (by linarith)))
      (fun m => mul_le_mul_of_nonneg_left (hbad (σ m)).2.2.2.1.le (by norm_num))
      (fun m v hv hvk p hpq => (H (σ m)).exists_spatialCanonicalWitness_extendAt_of_before
        (hH (σ m)).2.1 (G (σ m)) (hG (σ m)).2 (hbad (σ m)).1 (hts (σ m)) (hslabs (σ m)).2.2.2.1
        (hbefore (σ m)).2.2.2.2.1 v hv hvk p hpq)
      (fun m v hv hvk p hpq =>
        (K (σ m)).abs_derivWithin_stageMetric_scalar_le_of_derivative_bounds_of_lt (t := τ (σ m))
          le_rfl (hdin (σ m)).1 (hdin (σ m)).2.1 (hdin (σ m)).2.2 v
          (hv.trans_le (hbad (σ m)).2.1) hvk p hpq)
    obtain ⟨i, Wt, hWt⟩ := hev.exists
    exact hclause (σ (ψ₃ i)) (RetainedCoreHistory.exists_spatialCanonicalWitness_of_extendAt
      (H (σ (ψ₃ i))) (hH (σ (ψ₃ i))).2.1 (G (σ (ψ₃ i))) (hG (σ (ψ₃ i))).2 (hbad (σ (ψ₃ i))).1
      (hts (σ (ψ₃ i))) (y (σ (ψ₃ i))) (ŷ (σ (ψ₃ i))) (hŷ (σ (ψ₃ i))) Wt hWt)
  · obtain ⟨σ, hσ, hall, hmax⟩ : ∃ σ : ℕ → ℕ, StrictMono σ ∧
        (∀ T : ℝ, 0 < T → T < Tstar → ObservedHistory.DepthExtendable (fun n => (K n).toHistory)
          τ ŷ (fun n => (G n).flow.scalar (t n) (y n)) σ T) ∧
        ∀ χ : ℕ → ℕ, StrictMono χ → ∀ T : ℝ, Tstar < T →
          ¬ ObservedHistory.DepthExtendable (fun n => (K n).toHistory) τ ŷ
            (fun n => (G n).flow.scalar (t n) (y n)) (σ ∘ χ) T :=
      ⟨ψ, hψ, hall, hmax⟩
    obtain ⟨ψ₂, hψ₂, M, hM, hanc⟩ :=
      RetainedCoreHistory.exists_subseq_windowAnchorBound_of_depthExtendable hε hεcone hκ hphi hCs
        hH hG hrec hq hpar hscale hpinch hslabs hbefore hsliver hbad hεWN hσ hT ŷ hŷ hall
    refine hmax ψ₂ hψ₂ (Tstar + 1 / (32 * ((Ctime : ℝ) + 1) * (M + 1)))
      (lt_add_of_pos_right _ (by positivity)) ?_
    exact depthExtendable_add_of_windowAnchorBound hphi (fun n => (hH n).1) (fun n => (hH n).2.1)
      (fun n => (hG n).2) hrec (fun n => (hq n).1) hpar hscale (fun _ => le_rfl) hpinch
      (fun n => (hslabs n).2.1) (fun n => (hbad n).1) hts
      (fun n => (G n).derivativeBoundBefore_mono (hbad n).2.2.1.le (hsliver n).2.2.1)
      (fun n => (hbad n).2.2.2.1) (fun n => (hbad n).2.2.2.2.2) hRt (hσ.comp hψ₂) hT hM ŷ hŷ
      (fun T hT0 hTT => ObservedHistory.DepthExtendable.comp (hall T hT0 hTT) hψ₂) hanc

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end
