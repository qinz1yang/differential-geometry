import Batteries.Tactic.OpenPrivate
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.StrongNeckFullLeafC12X

/-!
# Crossing continuation with the young-point constant before the initial data (C12X, S16F G3)

`StrongSpatialCrossingContinuationFull_C12X P₀ g₀` (S16B G2e) states `∃ Cx` after `P₀ g₀`, but the
proof of `strongSpatialCrossingContinuationFull_holds_C12X` takes `Cx` from the blow-up lemma
`exists_eventually_strong_spatialCanonicalWitnessFull_of_isTracedRegion_C12X`, which does not see
`P₀ g₀`.  Along a chain the native initial data change, so the order matters.

* `StrongSpatialCrossingFullAt_C12X P₀ g₀ ε Cx` : the body of the S16B statement after `∃ Cx`.
* `exists_uniform_crossingFull_C12X` : `∀ ε ≤ εStrong_C12X, ∃ Cx ≥ 1, ∀ P₀ g₀, …At P₀ g₀ ε Cx`
  (the S16B proof re-run with `intro P₀ g₀` after the choice of `Cx`).
* `strongSpatialCrossingContinuationFull_of_uniform_C12X` : projection back to the S16B form.
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold NNReal Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open private RetainedCoreHistory.exists_spatial_crossing_bad_point
  RetainedCoreHistory.le_static_scale_of_neckRadius_le
  RetainedCoreHistory.metricScalarAt_extendAt_eq RetainedCoreHistory.slab_metric_of_extendAt from
 DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.StrongSpatialCrossingContinuationLeaf

universe u

/-- Body of `StrongSpatialCrossingContinuationFull_C12X P₀ g₀` after `∃ Cx, 1 ≤ Cx ∧`
(verbatim). -/
def StrongSpatialCrossingFullAt_C12X (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric)
    (ε Cx : ℝ) : Prop :=
  ∀ B : ℝ, 0 < B →
  ∀ (C1 C2 τmin : ℝ) (Ctime Cgrad : ℝ≥0), 1 ≤ C1 → 1 ≤ C2 → 0 < τmin →
  ∀ (C1s C2s Cs : ℝ), 1 ≤ C1s → 1 ≤ C2s → 1 ≤ Cs →
  ∀ (κ : ℝ) (phi : ℝ → ℝ) (θ : ℝ), 0 < κ → Perelman.AdmissiblePinchingFunction phi → 0 < θ →
  ∃ (Dcap θcap q₀ : ℝ) (mcap : ℕ), 0 < Dcap ∧ θcap < 1 ∧ 0 < q₀ ∧
  ∀ qcan : ℝ, q₀ ≤ qcan →
  ∃ (δmax ρmax εcap : ℝ), 0 < δmax ∧ 0 < ρmax ∧ 0 < εcap ∧
  ∀ qs : ℝ, qcan ≤ qs → qs ≤ Cs * qcan →
    ∀ (p₀ : CutoffParameters) (δbound ρbound : ℝ),
      p₀.modelAccuracy ≤ εcap → Dcap ≤ p₀.modelRadius → mcap ≤ p₀.modelOrder →
      δbound ≤ δmax → ρbound ≤ ρmax →
    ∀ (H : RetainedCoreHistory.{u}) (hH : H.InCutoffClass (P₀ := P₀) g₀ B p₀ δbound ρbound)
      (p : CutoffParameters) (records : ∀ i, GeometricCutoffRecord H.toHistory i p),
      H.IsCanonicalCutoffRecordFamily p₀ δbound ρbound records →
      H.EventSlabsPinched phi →
      (∀ j : Fin H.eventCount,
        H.EventSlabsCanonical ε C1 C2 qcan τmin j.castSucc →
        H.EventSlabsDerivative Ctime qcan j.castSucc →
        H.EventSlabsGradient Cgrad qcan j.castSucc →
        H.EventSlabsSpatiallyCanonical ε C1s C2s qs j.castSucc →
        ∀ t₀ : ℝ, t₀ ∈ Ico (H.time j.castSucc) (H.time j.succ) →
          (H.toHistory.event j).incoming.CanonicalBefore ε C1 C2 qcan τmin t₀ →
          (H.toHistory.event j).incoming.DerivativeBoundBefore Ctime qcan t₀ →
          (H.toHistory.event j).incoming.GradientBoundBefore Cgrad qcan t₀ →
          (H.toHistory.event j).incoming.SpatiallyCanonicalBefore ε C1s C2s qs t₀ →
          H.NoncollapsedBefore κ ε t₀ →
          ∀ η₃ : ℝ, 0 < η₃ →
            (H.toHistory.event j).incoming.DerivativeBoundOn Ctime qcan t₀ η₃ →
            (H.toHistory.event j).incoming.GradientBoundOn Cgrad qcan t₀ η₃ →
            (H.toHistory.event j).incoming.CanonicalOn ε C1 C2 qcan τmin t₀ η₃ →
          ∃ η : ℝ, 0 < η ∧ η ≤ η₃ ∧ t₀ + η ≤ H.time j.succ ∧
            ∀ (y : (H.stage j.castSucc).Carrier) (t : ℝ),
            H.time j.castSucc < t → t₀ ≤ t → t < t₀ + η → t < H.time j.succ →
            qs < (H.toHistory.event j).incoming.flow.scalar t y →
            (H.toHistory.event j).incoming.flow.scalar t y * (t - H.time j.castSucc) < θ →
            ¬ H.CapWindowPoint records j.castSucc y t Dcap θcap →
            ∃ W : SpatialCanonicalWitness
                ((H.toHistory.event j).incoming.flow.base.metric t) ε Cx Cx y,
              W.capTubeHasNeckChart ε ∧
                ((∃ n, W.alternative = .neck n) →
                  H.toHistory.HistoryStrongNeckFull_C12X j.castSucc
                    (H.toHistory.event j).incoming ε y t)) ∧
      ∀ (s : ℝ)
        (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s)
        (hG : H.IsContinuationSlab B (Fin.last H.eventCount) G),
        Perelman.PhiAlmostNonnegative G.flow (Ico (H.time (Fin.last H.eventCount)) s) phi →
        H.EventSlabsCanonical ε C1 C2 qcan τmin (Fin.last H.eventCount) →
        H.EventSlabsDerivative Ctime qcan (Fin.last H.eventCount) →
        H.EventSlabsGradient Cgrad qcan (Fin.last H.eventCount) →
        H.EventSlabsSpatiallyCanonical ε C1s C2s qs (Fin.last H.eventCount) →
        H.NoncollapsedBefore κ ε (H.time (Fin.last H.eventCount)) →
        ∀ t₀ : ℝ, t₀ ∈ Ico (H.time (Fin.last H.eventCount)) s →
          G.CanonicalBefore ε C1 C2 qcan τmin t₀ → G.DerivativeBoundBefore Ctime qcan t₀ →
          G.GradientBoundBefore Cgrad qcan t₀ →
          G.SpatiallyCanonicalBefore ε C1s C2s qs t₀ →
          H.TerminalNoncollapsedBefore hH.2.1 G hG.2 κ ε t₀ →
          ∀ η₃ : ℝ, 0 < η₃ → G.DerivativeBoundOn Ctime qcan t₀ η₃ →
            G.GradientBoundOn Cgrad qcan t₀ η₃ → G.CanonicalOn ε C1 C2 qcan τmin t₀ η₃ →
          ∃ η : ℝ, 0 < η ∧ η ≤ η₃ ∧ t₀ + η ≤ s ∧
            ∀ (y : (H.stage (Fin.last H.eventCount)).Carrier) (t : ℝ),
            H.time (Fin.last H.eventCount) < t → t₀ ≤ t → t < t₀ + η → t < s →
            qs < G.flow.scalar t y →
            G.flow.scalar t y * (t - H.time (Fin.last H.eventCount)) < θ →
            ¬ H.CapWindowPoint records (Fin.last H.eventCount) y t Dcap θcap →
            ∃ W : SpatialCanonicalWitness (G.flow.base.metric t) ε Cx Cx y,
              W.capTubeHasNeckChart ε ∧
                ((∃ n, W.alternative = .neck n) →
                  H.toHistory.HistoryStrongNeckFull_C12X (Fin.last H.eventCount) G ε y t)

/-- **Uniform young-point constant**: `Cx` depends on `ε` only and precedes the initial data
`P₀ g₀` (S16B proof of `strongSpatialCrossingContinuationFull_holds_C12X` re-run). -/
theorem exists_uniform_crossingFull_C12X :
    ∀ ε : ℝ, 0 < ε → ε ≤ εStrong_C12X.{u} →
    ∃ Cx : ℝ, 1 ≤ Cx ∧ ∀ (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric),
      StrongSpatialCrossingFullAt_C12X P₀ g₀ ε Cx := by
  intro ε hε hεbar
  have hε11 : ε < 1 / 11 := (hεbar.trans_lt εStrong_C12X_lt).trans (by norm_num)
  have hX5 :=
    ObservedHistory.exists_eventually_strong_spatialCanonicalWitnessFull_of_isTracedRegion_C12X.{u}
  have hεcone : ε ≤ coneAccuracy := hεbar.trans (min_le_left _ _)
  have hεW : ε ≤ ObservedHistory.crossingStrongEpsW_C12X.{u} :=
    hεbar.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hεN : ε ≤ crossingNeckAccuracy.{u} :=
    hεbar.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hεWN : ε ≤ crossingWindowNeckAccuracy.{u} :=
    hεbar.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨C, hC1, hX5⟩ := hX5 ε hε hε11 hεW
  refine ⟨C, hC1, ?_⟩
  intro P₀ g₀ B hB C1 C2 τmin Ctime Cgrad hC1le hC2le hτle C1s C2s Cs hC1s hC2s hCs κ phi θ hκ hphi
    hθ
  by_contra hneg
  push Not at hneg
  choose qcan hqcan hneg using fun n : ℕ =>
    hneg ((n : ℝ) + 1) (1 - 1 / ((n : ℝ) + 2)) ((n : ℝ) + 1) (n + 2) (by positivity) (by
        have : (0 : ℝ) < 1 / ((n : ℝ) + 2) := by positivity
        linarith) (by positivity)
  have hq0 : ∀ n : ℕ, 0 < qcan n := fun n =>
    (by positivity : (0 : ℝ) < (n : ℝ) + 1).trans_le (hqcan n)
  have hpack : ∀ n : ℕ, ∃ (H : RetainedCoreHistory.{u}) (s : ℝ)
      (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s)
      (p p₀ : CutoffParameters) (records : ∀ i, GeometricCutoffRecord H.toHistory i p)
      (δb ρb qs t₀ η t : ℝ) (y : (H.stage (Fin.last H.eventCount)).Carrier)
      (hH : H.InCutoffClass (P₀ := P₀) g₀ B p₀ δb ρb)
      (hG : H.IsContinuationSlab B (Fin.last H.eventCount) G),
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
        W.capTubeHasNeckChart ε ∧ ((∃ n, W.alternative = .neck n) →
          H.toHistory.HistoryStrongNeckFull_C12X (Fin.last H.eventCount) G ε y t) := by
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
              ε C C y, W.capTubeHasNeckChart ε → (∃ n, W.alternative = .neck n) ∧
                ¬ H.toHistory.HistoryStrongNeckFull_C12X j.castSucc
                  (H.toHistory.event j).incoming ε y t)
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
        fun ⟨W, hW, himp⟩ => (hcl W hW).2
          (H.historyStrongNeckFull_of_prefixAt_C12X j.castSucc (H.toHistory.event j).incoming
            (himp (hcl W hW).1))⟩
    · obtain ⟨s, G, hG, hpG, hcan, hder, hgrad, hspat, hncL, t₀, ht₀, hcb, hdb, hgb, hsb, hnc,
        η₃, hη₃, hdOn, hgOn, hcOn, hfail⟩ := hterm
      obtain ⟨η, hη, hηs, hder2, hsl, ⟨S, -, hSle, hSη⟩, y, t, hat, ht₀t, htη, hts, hqR, hθ',
          hcwp, hcl⟩ :=
        RetainedCoreHistory.exists_spatial_crossing_bad_point H G records
          (fun y t => G.flow.scalar t y * (t - H.time (Fin.last H.eventCount)) < θ ∧
            ¬ H.CapWindowPoint records (Fin.last H.eventCount) y t ((n : ℝ) + 1)
              (1 - 1 / ((n : ℝ) + 2)) ∧
            ∀ W : SpatialCanonicalWitness (G.flow.base.metric t) ε C C y,
              W.capTubeHasNeckChart ε → (∃ n, W.alternative = .neck n) ∧
                ¬ H.toHistory.HistoryStrongNeckFull_C12X (Fin.last H.eventCount) G ε y t)
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
        fun ⟨W, hW, himp⟩ => (hcl W hW).2 (himp (hcl W hW).1)⟩
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
  let K : ℕ → RetainedCoreHistory.{u} := fun n =>
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
    let Gs : ∀ m, (((K (σ m)).toHistory.stage
        ((K (σ m)).toHistory.activeStage (τ (σ m)))).IncomingSlab
          ((K (σ m)).toHistory.time ((K (σ m)).toHistory.activeStage (τ (σ m)))) (s (σ m))) :=
      fun m => cast (congrArg (fun k => (((K (σ m)).toHistory.stage k).IncomingSlab
        ((K (σ m)).toHistory.time k) (s (σ m)))) (hlast (σ m)).symm) (G (σ m))
    have hGs : ∀ m, HEq (Gs m) (G (σ m)) := fun m => cast_heq _ _
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
      (fun m => s (σ m)) Gs (fun m => hts (σ m))
      (fun m => RetainedCoreHistory.slab_metric_of_extendAt (H (σ m)) (hH (σ m)).2.1 (G (σ m))
        (hG (σ m)).2 (hbad (σ m)).1 (hts (σ m)) (Gs m) (hGs m))
    obtain ⟨i, Wt, hWt, hneck⟩ := hev.exists
    exact hclause (σ (ψ₃ i)) (RetainedCoreHistory.strong_clause_full_of_extendAt_C12X
      (H (σ (ψ₃ i))) (hH (σ (ψ₃ i))).2.1 (G (σ (ψ₃ i))) (hG (σ (ψ₃ i))).2 (hbad (σ (ψ₃ i))).1
      (hts (σ (ψ₃ i))) (y (σ (ψ₃ i))) (ŷ (σ (ψ₃ i))) (hŷ (σ (ψ₃ i))) (Gs (ψ₃ i)) (hGs (ψ₃ i))
      Wt hWt hneck)
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

/-- Projection: the uniform statement gives the S16B statement for every `P₀ g₀`. -/
theorem strongSpatialCrossingContinuationFull_of_uniform_C12X (P₀ : OrientedThreeStage.{u})
    (g₀ : P₀.Metric) : StrongSpatialCrossingContinuationFull_C12X P₀ g₀ := by
  intro ε hε hεb
  obtain ⟨Cx, hCx, h⟩ := exists_uniform_crossingFull_C12X.{u} ε hε hεb
  exact ⟨Cx, hCx, h P₀ g₀⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end
