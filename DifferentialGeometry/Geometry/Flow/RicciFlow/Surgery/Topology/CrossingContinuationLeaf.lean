import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CrossingBadPoint
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RetainedCoreHistoryPrefixInvariants
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CrossingTimeZeroBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CrossingDepthExtension
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CrossingAncientLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CrossingClauseTransport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SlabStartDerivativeBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.DerivativeBoundExtension
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

private theorem le_static_scale_of_neckRadius_le {H : RetainedCoreHistory P₀}
    {p₀ p : CutoffParameters} {δ₀ ρ₀ : ℝ}
    {records : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i p}
    (hrec : H.IsCanonicalCutoffRecordFamily p₀ δ₀ ρ₀ records)
    (hΛδ : p₀.recenterConstant * δ₀ ≤ 1 / 2) {X ρmax : ℝ} (hX : 0 < X) (hρ : ρ₀ ≤ ρmax)
    (hρmax : ρmax ≤ Real.sqrt (1 / (2 * X))) (i : Fin H.eventCount)
    (b : (H.toHistory.event i).RetainedBoundaryIndex) :
    X ≤ ((records i).static b).neck.scale := by
  have hlt := hrec.inv_two_mul_sq_lt_static_scale hΛδ i b
  have hρpos : 0 < ρ₀ :=
    (p.neckRadius_pos _ (H.toHistory.time_nonneg i.succ)).trans_le (hrec.2.2.2.2.2.2.2 i)
  have hsq : ρ₀ ^ 2 ≤ 1 / (2 * X) :=
    calc ρ₀ ^ 2 ≤ Real.sqrt (1 / (2 * X)) ^ 2 := pow_le_pow_left₀ hρpos.le (hρ.trans hρmax) 2
      _ = 1 / (2 * X) := Real.sq_sqrt (by positivity)
  have h2 : 2 * ρ₀ ^ 2 ≤ X⁻¹ :=
    calc 2 * ρ₀ ^ 2 ≤ 2 * (1 / (2 * X)) := by linarith
      _ = X⁻¹ := by rw [one_div, mul_inv, ← mul_assoc, mul_inv_cancel₀ two_ne_zero, one_mul]
  have h3 := inv_anti₀ (by positivity) h2
  rw [inv_inv] at h3
  exact h3.trans hlt.le

private theorem exists_sliver_bad_point (H : RetainedCoreHistory P₀) {s : ℝ}
    (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s)
    {p : CutoffParameters} (records : ∀ i, GeometricCutoffRecord H.toHistory i p)
    {ε C1 C2 qcan τmin θ D θcap t₀ : ℝ} {Ctime Cgrad : ℝ≥0} {n : ℕ} (hCt : 0 < Ctime)
    (hq : 0 < qcan) (ht₀ : t₀ ∈ Ico (H.time (Fin.last H.eventCount)) s)
    (hreg : ∀ y : (H.stage (Fin.last H.eventCount)).Carrier,
      ContinuousWithinAt (fun z : ℝ × (H.stage (Fin.last H.eventCount)).Carrier =>
        derivWithin (fun v => G.flow.scalar v z.2) (Ici z.1) z.1)
        (Ici (H.time (Fin.last H.eventCount)) ×ˢ univ) (H.time (Fin.last H.eventCount), y))
    (hstart : ∀ y : (H.stage (Fin.last H.eventCount)).Carrier,
      qcan < G.flow.scalar (H.time (Fin.last H.eventCount)) y →
      |derivWithin (fun v => G.flow.scalar v y) (Ici (H.time (Fin.last H.eventCount)))
        (H.time (Fin.last H.eventCount))| ≤
        Ctime * G.flow.scalar (H.time (Fin.last H.eventCount)) y ^ 2)
    (hdb : G.DerivativeBoundBefore Ctime qcan t₀)
    (hfail : ¬ ∃ η : ℝ, 0 < η ∧ G.CanonicalBoundsOn ε C1 C2 qcan τmin Ctime Cgrad t₀ η
      fun y t => G.flow.scalar t y * (t - H.time (Fin.last H.eventCount)) < θ ∧
        ¬ H.CapWindowPoint records (Fin.last H.eventCount) y t D θcap) :
    ∃ (η t : ℝ) (y : (H.stage (Fin.last H.eventCount)).Carrier),
      (0 < η ∧ t₀ + η < s ∧ G.DerivativeBoundBefore (2 * Ctime) (2 * qcan) (t₀ + η) ∧
        (∀ t' ∈ Icc t₀ (t₀ + η), ∀ x, G.flow.scalar t' x * η ≤ 1 / ((n : ℝ) + 1) ∧
          |G.flow.scalar t' x - G.flow.scalar t₀ x| ≤ qcan / 4 ∧
          ∀ v : TangentSpace ThreeModel x,
            (G.flow.base.metric t').inner x v v ≤
              Real.exp 1 * (G.flow.base.metric t₀).inner x v v ∧
            (G.flow.base.metric t₀).inner x v v ≤
              Real.exp 1 * (G.flow.base.metric t').inner x v v) ∧
        ∀ i b, ((records i).static b).neck.scale * η ≤ 1 / ((n : ℝ) + 2)) ∧
      (H.time (Fin.last H.eventCount) < t ∧ t₀ ≤ t ∧ t < t₀ + η ∧ qcan < G.flow.scalar t y ∧
        G.flow.scalar t y * (t - H.time (Fin.last H.eventCount)) < θ ∧
        ¬ H.CapWindowPoint records (Fin.last H.eventCount) y t D θcap) ∧
      ¬ ((τmin ≤ G.flow.scalar t y * (t - H.time (Fin.last H.eventCount)) →
            ∃ W : CanonicalWitness G.flow ε C1 C2 y t, W.capTubeHasNeckChart ε) ∧
          |derivWithin (fun v => G.flow.scalar v y) (Iic t) t| ≤ Ctime * G.flow.scalar t y ^ 2 ∧
          ∀ v : TangentSpace I3 y,
            |Perelman.CanonicalNeighborhood.scalarDifferential G.flow t y v| ≤
              Cgrad * G.flow.scalar t y * Real.sqrt (G.flow.scalar t y) *
                Real.sqrt ((G.flow.base.metric t).inner y v v)) := by
  obtain ⟨η₀, hη₀, hη₀s, hext⟩ :=
    G.exists_derivativeBoundBefore_extend_of_slice hCt hq ht₀ (fun _ => hreg) (fun _ => hstart) hdb
  obtain ⟨η, hη, hηs, hder, hsl, ⟨S, -, hSle, hSη⟩, y, t, hat, ht₀t, htη, hqR, hθ, hcwp, hcl⟩ :=
    H.exists_crossing_bad_point_terminal G records (ζ := 1 / ((n : ℝ) + 1)) (ζ' := qcan / 4)
      (ς := 1 / ((n : ℝ) + 2)) (by positivity) (div_pos hq (by norm_num)) (by positivity) ht₀
      ⟨η₀, hη₀, hη₀s, hext⟩ hfail
  refine ⟨η, t, y, ⟨hη, hηs, hder, hsl, fun i b => ?_⟩, ⟨hat, ht₀t, htη, hqR, hθ, hcwp⟩, hcl⟩
  exact (mul_le_mul_of_nonneg_right (hSle i b) hη.le).trans hSη

end RetainedCoreHistory

theorem crossingContinuation_holds (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) :
    CrossingContinuation P₀ g₀ := by
  obtain ⟨epsW, hepsW, hX5⟩ :=
    ObservedHistory.exists_eventually_canonical_clauses_of_isTracedRegion.{u}
  obtain ⟨CsS, hsliceC⟩ := RetainedCoreHistory.exists_slice_bounds_at_slab_start P₀ g₀
  refine ⟨min coneAccuracy (min epsW (min crossingNeckAccuracy.{u} crossingWindowNeckAccuracy.{u})),
    lt_min coneAccuracy_pos (lt_min hepsW (lt_min crossingNeckAccuracy_pos
      crossingWindowNeckAccuracy_pos)), ?_⟩
  intro B ε hB hε hε11 hεbar
  have hεcone : ε ≤ coneAccuracy := hεbar.trans (min_le_left _ _)
  have hεW : ε ≤ epsW := hεbar.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hεN : ε ≤ crossingNeckAccuracy.{u} :=
    hεbar.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hεWN : ε ≤ crossingWindowNeckAccuracy.{u} :=
    hεbar.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨C, τ₀, hC1, hτ₀, hX5⟩ := hX5 ε hε hε11 hεW
  have hC0 : (0 : ℝ) ≤ C := by linarith
  refine ⟨C, C, τ₀, max ⟨C, hC0⟩ CsS, ⟨C, hC0⟩, hC1, hC1, hτ₀, ?_⟩
  intro C1 C2 τmin Ctime Cgrad hC1le hC2le hτle hCtle hCgle C1s C2s Cs hC1s hC2s hCs κ phi θ hκ
    hphi hθ
  have hCC : C ≤ (Ctime : ℝ) := NNReal.coe_le_coe.mpr ((le_max_left _ _).trans hCtle)
  have hCsS : CsS ≤ Ctime := (le_max_right _ _).trans hCtle
  have hCg : C ≤ (Cgrad : ℝ) := NNReal.coe_le_coe.mpr hCgle
  have hCtpos : 0 < Ctime := NNReal.coe_pos.mp (by linarith)
  obtain ⟨Rs, qsS, ms, -, hsliceQ⟩ := hsliceC Ctime hCsS
  by_contra hneg
  push Not at hneg
  choose qcan hqcan hneg using fun n : ℕ =>
    hneg (max ((n : ℝ) + 1) Rs) (1 - 1 / ((n : ℝ) + 2)) (max ((n : ℝ) + 1) qsS) (max (n + 2) ms)
      (lt_max_of_lt_left (by positivity)) (by
        have : (0 : ℝ) < 1 / ((n : ℝ) + 2) := by positivity
        linarith) (lt_max_of_lt_left (by positivity))
  have hq0 : ∀ n : ℕ, 0 < qcan n := fun n =>
    (lt_max_of_lt_left (by positivity)).trans_le (hqcan n)
  choose δs ρs εs hδs hρs hεs hslice using fun n : ℕ =>
    hsliceQ (qcan n) ((le_max_right _ _).trans (hqcan n))
  have hpack : ∀ n : ℕ, ∃ (H : RetainedCoreHistory P₀) (s : ℝ)
      (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s)
      (p p₀ : CutoffParameters) (records : ∀ i, GeometricCutoffRecord H.toHistory i p)
      (δb ρb qs t₀ η t : ℝ) (y : (H.stage (Fin.last H.eventCount)).Carrier)
      (hH : H.InCutoffClass g₀ B p₀ δb ρb) (hG : H.IsContinuationSlab B (Fin.last H.eventCount) G),
      H.IsCanonicalCutoffRecordFamily p₀ δb ρb records ∧
      ((n : ℝ) + 1 ≤ qcan n ∧ qcan n ≤ qs ∧ qs ≤ Cs * qcan n) ∧
      (p₀.modelAccuracy ≤ 1 / ((n : ℝ) + 1) ∧ (n : ℝ) + 1 ≤ max ((n : ℝ) + 1) Rs ∧
        max ((n : ℝ) + 1) Rs ≤ p₀.modelRadius ∧ n + 2 ≤ p₀.modelOrder ∧
        δb ≤ 1 / ((n : ℝ) + 1)) ∧
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
        ¬ H.CapWindowPoint records (Fin.last H.eventCount) y t (max ((n : ℝ) + 1) Rs)
          (1 - 1 / ((n : ℝ) + 2))) ∧
      ¬ ((τmin ≤ G.flow.scalar t y * (t - H.time (Fin.last H.eventCount)) →
            ∃ W : CanonicalWitness G.flow ε C1 C2 y t, W.capTubeHasNeckChart ε) ∧
          |derivWithin (fun v => G.flow.scalar v y) (Iic t) t| ≤ Ctime * G.flow.scalar t y ^ 2 ∧
          ∀ v : TangentSpace I3 y,
            |Perelman.CanonicalNeighborhood.scalarDifferential G.flow t y v| ≤
              Cgrad * G.flow.scalar t y * Real.sqrt (G.flow.scalar t y) *
                Real.sqrt ((G.flow.base.metric t).inner y v v)) := by
    intro n
    have hsq : (0 : ℝ) < 1 / (2 * (((n : ℝ) + 1) * qcan n)) :=
      div_pos one_pos (mul_pos two_pos (mul_pos (by positivity) (hq0 n)))
    obtain ⟨qs, hqs1, hqs2, p₀, δb, ρb, hacc, hrad, hord, hδb, hρb, H, hH, p, records, hrec,
        hpinch, hfail⟩ :=
      hneg n (min (1 / ((n : ℝ) + 1)) (δs n))
        (min (Real.sqrt (1 / (2 * (((n : ℝ) + 1) * qcan n)))) (ρs n))
        (min (1 / ((n : ℝ) + 1)) (εs n)) (lt_min (by positivity) (hδs n))
        (lt_min (Real.sqrt_pos.mpr hsq) (hρs n)) (lt_min (by positivity) (hεs n))
    have hT := hslice n p₀ δb ρb (hacc.trans (min_le_right _ _)) ((le_max_right _ _).trans hrad)
      ((le_max_right _ _).trans hord) (hδb.trans (min_le_right _ _))
      (hρb.trans (min_le_right _ _)) H hH.1 hH.2.2.2.2 p records hrec
    have hqn : (n : ℝ) + 1 ≤ qcan n ∧ qcan n ≤ qs ∧ qs ≤ Cs * qcan n :=
      ⟨(le_max_left _ _).trans (hqcan n), hqs1, hqs2⟩
    have hparn : p₀.modelAccuracy ≤ 1 / ((n : ℝ) + 1) ∧ (n : ℝ) + 1 ≤ max ((n : ℝ) + 1) Rs ∧
        max ((n : ℝ) + 1) Rs ≤ p₀.modelRadius ∧ n + 2 ≤ p₀.modelOrder ∧
        δb ≤ 1 / ((n : ℝ) + 1) :=
      ⟨hacc.trans (min_le_left _ _), le_max_left _ _, hrad, (le_max_left _ _).trans hord,
        hδb.trans (min_le_left _ _)⟩
    rcases imp_iff_not_or.mp hfail with hev | hterm
    · push Not at hev
      obtain ⟨j, hcan, hder, hgrad, hspat, t₀, ht₀, hcb, hdb, hgb, hsb, hnc, hfail⟩ := hev
      obtain ⟨hreg, hstart⟩ :=
        hT j.castSucc _ (H.toHistory.event j).incoming (H.event_initial j) hder
      obtain ⟨η, t, y, hsliver, hbad, hclause⟩ :=
        RetainedCoreHistory.exists_sliver_bad_point (H.prefixAt j.castSucc)
          (H.toHistory.event j).incoming (H.prefixRecords j.castSucc records) (n := n) hCtpos
          (hq0 n) ht₀ hreg hstart hdb (fun ⟨η, hη, hb⟩ => hfail η hη
            fun y t hat ht₀' htη hts hR hS => hb y t hat ht₀' htη hts hR
              ⟨hS.1, fun h' => hS.2 (H.capWindowPoint_of_prefixAt j records h')⟩)
      exact ⟨H.prefixAt j.castSucc, H.time j.succ, (H.toHistory.event j).incoming, p, p₀,
        H.prefixRecords j.castSucc records, δb, ρb, qs, t₀, η, t, y,
        H.inCutoffClass_prefixAt hH j.castSucc,
        ⟨(H.isContinuationSlab_event hH.2.2.1 j).1, H.event_initial j⟩,
        H.isCanonicalCutoffRecordFamily_prefixAt j.castSucc hrec, hqn, hparn,
        fun i b => RetainedCoreHistory.le_static_scale_of_neckRadius_le
          (H.isCanonicalCutoffRecordFamily_prefixAt j.castSucc hrec) hH.2.2.2.2
          (mul_pos (by positivity) (hq0 n)) hρb (min_le_left _ _) i b,
        ⟨H.eventSlabsPinched_prefixAt j.castSucc hpinch, hpinch j⟩,
        ⟨H.eventSlabsCanonical_prefixAt j.castSucc hcan,
          H.eventSlabsDerivative_prefixAt j.castSucc hder,
          H.eventSlabsGradient_prefixAt j.castSucc hgrad,
          H.eventSlabsSpatiallyCanonical_prefixAt j.castSucc hspat,
          H.noncollapsedBefore_prefixAt j.castSucc hnc ht₀.1⟩,
        ⟨ht₀, hcb, hdb, hgb, hsb, H.terminalNoncollapsedBefore_prefixAt j hnc⟩, hsliver, hbad,
        hclause⟩
    · obtain ⟨s, G, hG, hpG, hcan, hder, hgrad, hspat, hncL, t₀, ht₀, hcb, hdb, hgb, hsb, hnc,
        hfail⟩ := hterm
      obtain ⟨hreg, hstart⟩ := hT (Fin.last H.eventCount) s G hG.2 hder
      obtain ⟨η, t, y, hsliver, hbad, hclause⟩ :=
        RetainedCoreHistory.exists_sliver_bad_point H G records (n := n) hCtpos (hq0 n) ht₀ hreg
          hstart hdb (fun ⟨η, hη, hb⟩ => hfail η hη hb)
      exact ⟨H, s, G, p, p₀, records, δb, ρb, qs, t₀, η, t, y, hH, hG, hrec, hqn, hparn,
        fun i b => RetainedCoreHistory.le_static_scale_of_neckRadius_le hrec hH.2.2.2.2
          (mul_pos (by positivity) (hq0 n)) hρb (min_le_left _ _) i b,
        ⟨hpinch, hpG⟩, ⟨hcan, hder, hgrad, hspat, hncL⟩, ⟨ht₀, hcb, hdb, hgb, hsb, hnc⟩, hsliver,
        hbad, hclause⟩
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
  obtain ⟨σ₀, hσ₀, hmode₀⟩ : ∃ σ₀ : ℕ → ℕ, StrictMono σ₀ ∧
      ((∀ i, τ₀ ≤ (G (σ₀ i)).flow.scalar (t (σ₀ i)) (y (σ₀ i)) *
          (t (σ₀ i) - (H (σ₀ i)).time (Fin.last (H (σ₀ i)).eventCount))) ∨
        ∀ i, (G (σ₀ i)).flow.scalar (t (σ₀ i)) (y (σ₀ i)) *
          (t (σ₀ i) - (H (σ₀ i)).time (Fin.last (H (σ₀ i)).eventCount)) < τ₀) := by
    rcases frequently_or_distrib.mp (Frequently.of_forall (f := atTop) fun n =>
        em (τ₀ ≤ (G n).flow.scalar (t n) (y n) *
          (t n - (H n).time (Fin.last (H n).eventCount)))) with h | h
    · obtain ⟨σ₀, hσ₀, hP⟩ := extraction_of_frequently_atTop h
      exact ⟨σ₀, hσ₀, Or.inl hP⟩
    · obtain ⟨σ₀, hσ₀, hP⟩ := extraction_of_frequently_atTop h
      exact ⟨σ₀, hσ₀, Or.inr fun i => not_le.mp (hP i)⟩
  obtain ⟨ψ, hψ, hdich⟩ := exists_strictMono_maximal_depth
    (fun σ T => ObservedHistory.DepthExtendable (fun n => (K n).toHistory) τ ŷ
      (fun n => (G n).flow.scalar (t n) (y n)) σ T)
    (fun _ _ _ hT' hle h => ObservedHistory.DepthExtendable.mono_depth h hRpos hT' hle)
    (fun _ _ _ hψ h => ObservedHistory.DepthExtendable.comp h hψ)
    (fun _ _ _ hσ h => ObservedHistory.DepthExtendable.congr h hσ) σ₀
    (RetainedCoreHistory.exists_subseq_depthExtendable_pos hε hεcone hκ hphi hCs hH hG hrec hq
      hpar hscale (fun _ => le_rfl) hpinch hslabs hbefore hsliver hbad hεN σ₀ hσ₀ ŷ hŷ)
  rcases hdich with hall | ⟨Tstar, hT, hall, hmax⟩
  · obtain ⟨σ, hσ, hall, hmode⟩ : ∃ σ : ℕ → ℕ, StrictMono σ ∧
        (∀ T : ℝ, 0 < T → ObservedHistory.DepthExtendable (fun n => (K n).toHistory) τ ŷ
          (fun n => (G n).flow.scalar (t n) (y n)) σ T) ∧
        ((∀ m, τ₀ ≤ (G (σ m)).flow.scalar (t (σ m)) (y (σ m)) *
            (t (σ m) - (H (σ m)).time (Fin.last (H (σ m)).eventCount))) ∨
          ∀ m, (G (σ m)).flow.scalar (t (σ m)) (y (σ m)) *
            (t (σ m) - (H (σ m)).time (Fin.last (H (σ m)).eventCount)) < τ₀) :=
      ⟨σ₀ ∘ ψ, hσ₀.comp hψ, hall, hmode₀.imp (fun h m => h (ψ m)) (fun h m => h (ψ m))⟩
    have hmodeK : (∀ m, τ₀ ≤ (G (σ m)).flow.scalar (t (σ m)) (y (σ m)) *
          ((τ (σ m) : ℝ) - (K (σ m)).toHistory.time
            ((K (σ m)).toHistory.activeStage (τ (σ m))))) ∨
        ∀ m, (G (σ m)).flow.scalar (t (σ m)) (y (σ m)) *
          ((τ (σ m) : ℝ) - (K (σ m)).toHistory.time
            ((K (σ m)).toHistory.activeStage (τ (σ m)))) < τ₀ := by
      refine hmode.imp (fun h m => ?_) (fun h m => ?_) <;> rw [htime] <;> exact h m
    obtain ⟨ψ₃, hψ₃, hev⟩ := hX5 (fun m => (K (σ m)).toHistory) (fun m => τ (σ m))
      (fun m => ŷ (σ m)) (fun m => (G (σ m)).flow.scalar (t (σ m)) (y (σ m)))
      (fun m => hRpos (σ m)) (fun m => hscal (σ m)) (hR.comp hσ.tendsto_atTop)
      (fun m => hlt (σ m)) hmodeK (fun A T hA hT => hall T hT A hA) hκ hε
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
    obtain ⟨i, hwit, hder, hgrad⟩ := hev.exists
    exact hclause (σ (ψ₃ i)) ((H (σ (ψ₃ i))).canonical_clauses_of_extendAt (hH (σ (ψ₃ i))).2.1
      (G (σ (ψ₃ i))) (hG (σ (ψ₃ i))).2 (hbad (σ (ψ₃ i))).1 (hts (σ (ψ₃ i))) (y (σ (ψ₃ i)))
      (ŷ (σ (ψ₃ i))) (hŷ (σ (ψ₃ i))) (hlt (σ (ψ₃ i))) hC1le hC2le hCC hCg hτle hwit hder hgrad)
  · obtain ⟨σ, hσ, hall, hmax⟩ : ∃ σ : ℕ → ℕ, StrictMono σ ∧
        (∀ T : ℝ, 0 < T → T < Tstar → ObservedHistory.DepthExtendable (fun n => (K n).toHistory)
          τ ŷ (fun n => (G n).flow.scalar (t n) (y n)) σ T) ∧
        ∀ χ : ℕ → ℕ, StrictMono χ → ∀ T : ℝ, Tstar < T →
          ¬ ObservedHistory.DepthExtendable (fun n => (K n).toHistory) τ ŷ
            (fun n => (G n).flow.scalar (t n) (y n)) (σ ∘ χ) T :=
      ⟨σ₀ ∘ ψ, hσ₀.comp hψ, hall, hmax⟩
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
