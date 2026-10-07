import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.DeepContinuation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CrossingContinuationLeaf
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.UniformCapWindowContinuation

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold NNReal Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open private RetainedCoreHistory.metricScalarAt_extendAt_eq
  RetainedCoreHistory.le_static_scale_of_neckRadius_le
  RetainedCoreHistory.exists_sliver_bad_point from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CrossingContinuationLeaf

private theorem universalDeepContinuation :
  ∀ ε : ℝ, 0 < ε → ε < 1 / 11 →
  ∃ (C1₀ C2₀ τ₀ : ℝ) (Ctime₀ Cgrad₀ : ℝ≥0), 1 ≤ C1₀ ∧ 1 ≤ C2₀ ∧ 0 < τ₀ ∧
  ∀ (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric),
  ∀ B : ℝ, 0 < B →
  ∀ (C1 C2 τmin : ℝ) (Ctime Cgrad : ℝ≥0),
    C1₀ ≤ C1 → C2₀ ≤ C2 → τ₀ ≤ τmin → Ctime₀ ≤ Ctime → Cgrad₀ ≤ Cgrad →
  ∀ (κ : ℝ) (phi : ℝ → ℝ), 0 < κ → Perelman.AdmissiblePinchingFunction phi →
  ∃ (θ q₀ δmax ρmax εcap Dcap : ℝ) (mcap : ℕ),
    0 < θ ∧ 0 < q₀ ∧ 0 < δmax ∧ 0 < ρmax ∧ 0 < εcap ∧ 0 < Dcap ∧
  ∀ qcan : ℝ, q₀ ≤ qcan →
    ∀ (p₀ : CutoffParameters) (δbound ρbound : ℝ),
      p₀.modelAccuracy ≤ εcap → Dcap ≤ p₀.modelRadius → mcap ≤ p₀.modelOrder →
      δbound ≤ δmax → ρbound ≤ ρmax →
    ∀ (H : RetainedCoreHistory.{u}) (hH : H.InCutoffClass (P₀ := P₀) g₀ B p₀ δbound ρbound),
      H.EventSlabsPinched phi →
      (∀ j : Fin H.eventCount,
        H.EventSlabsCanonical ε C1 C2 qcan τmin j.castSucc →
        H.EventSlabsDerivative Ctime qcan j.castSucc →
        H.EventSlabsGradient Cgrad qcan j.castSucc →
        ∀ t₀ : ℝ, t₀ ∈ Ico (H.time j.castSucc) (H.time j.succ) →
          (H.toHistory.event j).incoming.CanonicalBefore ε C1 C2 qcan τmin t₀ →
          (H.toHistory.event j).incoming.DerivativeBoundBefore Ctime qcan t₀ →
          (H.toHistory.event j).incoming.GradientBoundBefore Cgrad qcan t₀ →
          H.NoncollapsedBefore κ ε t₀ →
          ∃ η : ℝ, 0 < η ∧
            (H.toHistory.event j).incoming.CanonicalBoundsOn ε C1 C2 qcan τmin Ctime Cgrad t₀ η
              fun y t => θ ≤ (H.toHistory.event j).incoming.flow.scalar t y *
                (t - H.time j.castSucc)) ∧
      ∀ (s : ℝ)
        (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s)
        (hG : H.IsContinuationSlab B (Fin.last H.eventCount) G),
        Perelman.PhiAlmostNonnegative G.flow (Ico (H.time (Fin.last H.eventCount)) s) phi →
        H.EventSlabsCanonical ε C1 C2 qcan τmin (Fin.last H.eventCount) →
        H.EventSlabsDerivative Ctime qcan (Fin.last H.eventCount) →
        H.EventSlabsGradient Cgrad qcan (Fin.last H.eventCount) →
        H.NoncollapsedBefore κ ε (H.time (Fin.last H.eventCount)) →
        ∀ t₀ : ℝ, t₀ ∈ Ico (H.time (Fin.last H.eventCount)) s →
          G.CanonicalBefore ε C1 C2 qcan τmin t₀ → G.DerivativeBoundBefore Ctime qcan t₀ →
          G.GradientBoundBefore Cgrad qcan t₀ →
          H.TerminalNoncollapsedBefore hH.2.1 G hG.2 κ ε t₀ →
          ∃ η : ℝ, 0 < η ∧ G.CanonicalBoundsOn ε C1 C2 qcan τmin Ctime Cgrad t₀ η
            fun y t => θ ≤ G.flow.scalar t y * (t - H.time (Fin.last H.eventCount)) := by
  intro ε hε hε'
  obtain ⟨C, hC, -, hU⟩ :=
    OrientedThreeStage.IncomingSlab.exists_uniform_canonical_threshold_of_parabolically_noncollapsed.{u}
      hε hε'
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  refine ⟨C, C, 1, ⟨C, hC0⟩, ⟨C, hC0⟩, hC, hC, one_pos, ?_⟩
  intro P₀ g₀ B _ C1 C2 τmin Ctime Cgrad hC1 hC2 _ hCt hCg κ phi hκ hphi
  have hCt' : C ≤ (Ctime : ℝ) := NNReal.coe_le_coe.mpr hCt
  have hCg' : C ≤ (Cgrad : ℝ) := NNReal.coe_le_coe.mpr hCg
  obtain ⟨Q₀, theta, hQ₀, htheta, hW⟩ :=
    hU (κ * Real.exp (-6)) (mul_pos hκ (Real.exp_pos _)) ε hε phi hphi
  have key : ∀ (P : OrientedThreeStage.{u}) (a s : ℝ) (G : P.IncomingSlab a s) (qcan t₀ : ℝ),
      Q₀ ≤ qcan → Perelman.PhiAlmostNonnegative G.flow (Ico a s) phi → t₀ ∈ Ico a s →
      (∀ (τ : (RealTimeInterval.closedOpen a s G.lt).FlowTime)
        (B : Perelman.FlowMetricBall G.flow τ), (τ : ℝ) ≤ t₀ → B.radius ≤ ε →
          B.IsParabolicallyRmControlled → B.IsKappaNoncollapsed κ) →
      ∃ η : ℝ, 0 < η ∧ G.CanonicalBoundsOn ε C1 C2 qcan τmin Ctime Cgrad t₀ η
        fun y t => 2 * theta ≤ G.flow.scalar t y * (t - a) := by
    intro P a s G qcan t₀ hq hpinch ht₀ hnc
    have hbounds : ∀ η : ℝ, (∀ (τ : (RealTimeInterval.closedOpen a s G.lt).FlowTime)
        (B : Perelman.FlowMetricBall G.flow τ), (τ : ℝ) < t₀ + η → B.radius ≤ ε →
          B.IsParabolicallyRmControlled → B.IsKappaNoncollapsed (κ * Real.exp (-6))) →
        G.CanonicalBoundsOn ε C1 C2 qcan τmin Ctime Cgrad t₀ η
          fun y t => 2 * theta ≤ G.flow.scalar t y * (t - a) := by
      intro η hncη y t _ _ htη hts hR hage
      have hRpos : 0 < G.flow.scalar t y := hQ₀.trans_le (hq.trans hR.le)
      have hwin : a ≤ t - theta / G.flow.scalar t y := by
        have h : theta / G.flow.scalar t y ≤ t - a := by
          rw [div_le_iff₀ hRpos]
          nlinarith
        linarith
      obtain ⟨W, hWc⟩ := hW P a s G y t hts (hq.trans hR.le) hwin
        (fun v hv z => hpinch v ⟨hwin.trans hv.1, hv.2.trans_lt hts⟩ z)
        (fun τ B _ h2 h3 h4 => hncη τ B (h2.trans_lt htη) h3 h4)
      refine ⟨fun _ => ⟨W.enlargeConstants hC1 hC2, hWc.enlarge_constants hC1 hC2⟩, ?_, ?_⟩
      · exact W.time_derivative.trans (mul_le_mul_of_nonneg_right hCt' (sq_nonneg _))
      · intro v
        exact (W.gradient v).trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCg' hRpos.le)
            (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))
    rcases eq_or_lt_of_le ht₀.1 with h | h
    · obtain ⟨K, hK⟩ := G.exists_forall_Icc_scalar_le (b := (a + s) / 2) (by linarith [G.lt])
      have hM : 0 < max K 1 := one_pos.trans_le (le_max_right _ _)
      refine ⟨min ((s - a) / 2) (theta / max K 1),
        lt_min (by linarith [G.lt]) (div_pos htheta hM), ?_⟩
      intro y t _ ht₀' htη _ hR hage
      exfalso
      have hle1 := min_le_left ((s - a) / 2) (theta / max K 1)
      have hle2 := min_le_right ((s - a) / 2) (theta / max K 1)
      have htb : t ∈ Icc a ((a + s) / 2) := ⟨by linarith, by linarith⟩
      have hRK : G.flow.scalar t y ≤ max K 1 := (hK t htb y).trans (le_max_left _ _)
      have hta : t - a < theta / max K 1 := by linarith
      have h1 : G.flow.scalar t y * (t - a) ≤ max K 1 * (t - a) :=
        mul_le_mul_of_nonneg_right hRK (by linarith)
      have h2 : max K 1 * (t - a) < theta := by
        rw [lt_div_iff₀ hM] at hta
        linarith
      linarith
    · obtain ⟨η, hη, hfw⟩ := G.exists_isKappaNoncollapsed_forward_of_before h ht₀.2 hnc
      exact ⟨η, hη, hbounds η hfw⟩
  refine ⟨2 * theta, Q₀, 1, 1, 1, 1, 0, mul_pos two_pos htheta, hQ₀, one_pos, one_pos, one_pos,
    one_pos, ?_⟩
  intro qcan hq p₀ δbound ρbound _ _ _ _ _ H hH hpinch
  refine ⟨fun j _ _ _ t₀ ht₀ _ _ _ hnc => ?_, fun s G hG hpG _ _ _ _ t₀ ht₀ _ _ _ hnc => ?_⟩
  · exact key _ _ _ (H.toHistory.event j).incoming qcan t₀ hq (hpinch j) ht₀
      (H.isKappaNoncollapsed_of_noncollapsedBefore hκ hnc j)
  · exact key _ _ _ G qcan t₀ hq hpG ht₀
      (H.isKappaNoncollapsed_of_terminalNoncollapsedBefore hH.2.1 G hG.2 hκ hnc)

private theorem universalCrossingContinuation :
  ∃ εbar : ℝ, 0 < εbar ∧
  ∀ ε : ℝ, 0 < ε → ε < 1 / 11 → ε ≤ εbar →
  ∃ (C1₀ C2₀ τ₀ : ℝ) (Ctime₀ Cgrad₀ : ℝ≥0), 1 ≤ C1₀ ∧ 1 ≤ C2₀ ∧ 0 < τ₀ ∧
  ∀ (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric),
  ∀ B : ℝ, 0 < B →
  ∀ (C1 C2 τmin : ℝ) (Ctime Cgrad : ℝ≥0),
    C1₀ ≤ C1 → C2₀ ≤ C2 → τ₀ ≤ τmin → Ctime₀ ≤ Ctime → Cgrad₀ ≤ Cgrad →
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
          ∃ η : ℝ, 0 < η ∧
            (H.toHistory.event j).incoming.CanonicalBoundsOn ε C1 C2 qcan τmin Ctime Cgrad t₀ η
              fun y t => (H.toHistory.event j).incoming.flow.scalar t y *
                  (t - H.time j.castSucc) < θ ∧
                ¬ H.CapWindowPoint records j.castSucc y t Dcap θcap) ∧
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
          G.GradientBoundBefore Cgrad qcan t₀ → G.SpatiallyCanonicalBefore ε C1s C2s qs t₀ →
          H.TerminalNoncollapsedBefore hH.2.1 G hG.2 κ ε t₀ →
          ∃ η : ℝ, 0 < η ∧ G.CanonicalBoundsOn ε C1 C2 qcan τmin Ctime Cgrad t₀ η
            fun y t => G.flow.scalar t y * (t - H.time (Fin.last H.eventCount)) < θ ∧
              ¬ H.CapWindowPoint records (Fin.last H.eventCount) y t Dcap θcap := by
  obtain ⟨epsW, hepsW, hX5⟩ :=
    ObservedHistory.exists_eventually_canonical_clauses_of_isTracedRegion.{u}
  obtain ⟨CsS, hsliceC⟩ := RetainedCoreHistory.exists_uniform_slice_bounds_at_slab_start.{u}
  refine ⟨min coneAccuracy (min epsW (min crossingNeckAccuracy.{u} crossingWindowNeckAccuracy.{u})),
    lt_min coneAccuracy_pos (lt_min hepsW (lt_min crossingNeckAccuracy_pos
      crossingWindowNeckAccuracy_pos)), ?_⟩
  intro ε hε hε11 hεbar
  have hεcone : ε ≤ coneAccuracy := hεbar.trans (min_le_left _ _)
  have hεW : ε ≤ epsW := hεbar.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hεN : ε ≤ crossingNeckAccuracy.{u} :=
    hεbar.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hεWN : ε ≤ crossingWindowNeckAccuracy.{u} :=
    hεbar.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨C, τ₀, hC1, hτ₀, hX5⟩ := hX5 ε hε hε11 hεW
  have hC0 : (0 : ℝ) ≤ C := by linarith
  refine ⟨C, C, τ₀, max ⟨C, hC0⟩ CsS, ⟨C, hC0⟩, hC1, hC1, hτ₀, ?_⟩
  intro P₀ g₀
  have hsliceC := hsliceC P₀ g₀
  intro B hB C1 C2 τmin Ctime Cgrad hC1le hC2le hτle hCtle hCgle C1s C2s Cs hC1s hC2s hCs κ phi θ hκ
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
  have hpack : ∀ n : ℕ, ∃ (H : RetainedCoreHistory.{u}) (s : ℝ)
      (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s)
      (p p₀ : CutoffParameters) (records : ∀ i, GeometricCutoffRecord H.toHistory i p)
      (δb ρb qs t₀ η t : ℝ) (y : (H.stage (Fin.last H.eventCount)).Carrier)
      (hH : H.InCutoffClass (P₀ := P₀) g₀ B p₀ δb ρb) (hG : H.IsContinuationSlab B (Fin.last H.eventCount) G),
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

/-- One canonical, scalar-time and scalar-gradient coefficient tuple works for
every initial metric and horizon. Fine thresholds and model/cutoff budgets are
chosen later. The cap and crossing branches use one selected record family on
the supplied history, and every continuation bound is on its actual metric. -/
theorem exists_universal_canonicalNeighborhoodContinuation :
  ∃ εbar : ℝ, 0 < εbar ∧
  ∀ ε : ℝ, 0 < ε → ε < 1 / 11 → ε ≤ εbar →
  ∃ (C1 C2 τmin : ℝ) (Ctime Cgrad : ℝ≥0), 1 ≤ C1 ∧ 1 ≤ C2 ∧ 0 < τmin ∧
  ∀ (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric),
  ∀ B : ℝ, 0 < B →
  ∀ (C1s C2s Cs : ℝ), 1 ≤ C1s → 1 ≤ C2s → 1 ≤ Cs →
  ∀ (κ : ℝ) (phi : ℝ → ℝ), 0 < κ → Perelman.AdmissiblePinchingFunction phi →
  ∀ qfloor : ℝ,
  ∃ (qcan δmax ρmax εcap Dcap : ℝ) (mcap : ℕ),
    qfloor ≤ qcan ∧ 0 < qcan ∧ 0 < δmax ∧ 0 < ρmax ∧ 0 < εcap ∧ 0 < Dcap ∧
  ∀ qs : ℝ, qcan ≤ qs → qs ≤ Cs * qcan →
    ∀ (p₀ : CutoffParameters) (δbound ρbound : ℝ),
      p₀.modelAccuracy ≤ εcap → Dcap ≤ p₀.modelRadius → mcap ≤ p₀.modelOrder →
      δbound ≤ δmax → ρbound ≤ ρmax →
    ∀ (H : RetainedCoreHistory.{u}) (hH : H.InCutoffClass (P₀ := P₀) g₀ B p₀ δbound ρbound),
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
          ∃ η : ℝ, 0 < η ∧
            (H.toHistory.event j).incoming.DerivativeBoundOn Ctime qcan t₀ η ∧
            (H.toHistory.event j).incoming.GradientBoundOn Cgrad qcan t₀ η ∧
            (H.toHistory.event j).incoming.CanonicalOn ε C1 C2 qcan τmin t₀ η) ∧
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
          G.GradientBoundBefore Cgrad qcan t₀ → G.SpatiallyCanonicalBefore ε C1s C2s qs t₀ →
          H.TerminalNoncollapsedBefore hH.2.1 G hG.2 κ ε t₀ →
          ∃ η : ℝ, 0 < η ∧ G.DerivativeBoundOn Ctime qcan t₀ η ∧
            G.GradientBoundOn Cgrad qcan t₀ η ∧ G.CanonicalOn ε C1 C2 qcan τmin t₀ η := by
  obtain ⟨εbar, hεbar, hcross⟩ := universalCrossingContinuation.{u}
  refine ⟨εbar, hεbar, ?_⟩
  intro ε hε hε' hεbar'
  obtain ⟨C1d, C2d, τd, Ctd, Cgd, hC1d, hC2d, hτd, hD⟩ := universalDeepContinuation.{u} ε hε hε'
  obtain ⟨C1w, C2w, τw, Ctw, Cgw, -, -, -, hW⟩ := exists_uniform_capWindowContinuation.{u} ε hε hε'
  obtain ⟨C1x, C2x, τx, Ctx, Cgx, -, -, -, hX⟩ := hcross ε hε hε' hεbar'
  refine ⟨max C1d (max C1w C1x), max C2d (max C2w C2x), max τd (max τw τx),
    max Ctd (max Ctw Ctx), max Cgd (max Cgw Cgx), le_max_of_le_left hC1d,
    le_max_of_le_left hC2d, lt_max_of_lt_left hτd, ?_⟩
  intro P₀ g₀
  have hD := hD P₀ g₀
  have hW := hW P₀ g₀
  have hX := hX P₀ g₀
  intro B hB C1s C2s Cs hC1s hC2s hCs κ phi hκ hphi qfloor
  obtain ⟨θ, qd, δd, ρd, εd, Dd, md, hθ, hqd, hδd, hρd, hεd, hDd, hDstep⟩ :=
    hD B hB _ _ _ _ _ (le_max_left _ _) (le_max_left _ _) (le_max_left _ _) (le_max_left _ _)
      (le_max_left _ _) κ phi hκ hphi
  obtain ⟨Dx, θcap, qx, mx, hDx, hθcap, hqx, hXq⟩ :=
    hX B hB _ _ _ _ _ ((le_max_right _ _).trans (le_max_right _ _))
      ((le_max_right _ _).trans (le_max_right _ _)) ((le_max_right _ _).trans (le_max_right _ _))
      ((le_max_right _ _).trans (le_max_right _ _)) ((le_max_right _ _).trans (le_max_right _ _))
      C1s C2s Cs hC1s hC2s hCs κ phi θ hκ hphi hθ
  obtain ⟨Rw, qw, mw, hRw, hqw, hWq⟩ :=
    hW B hB _ _ _ _ _ ((le_max_left _ _).trans (le_max_right _ _))
      ((le_max_left _ _).trans (le_max_right _ _)) ((le_max_left _ _).trans (le_max_right _ _))
      ((le_max_left _ _).trans (le_max_right _ _)) ((le_max_left _ _).trans (le_max_right _ _))
      κ phi θ Dx θcap hκ hphi hθ hDx hθcap
  have hqdc : qd ≤ max qfloor (max qd (max qw qx)) :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hqwc : qw ≤ max qfloor (max qd (max qw qx)) :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hqxc : qx ≤ max qfloor (max qd (max qw qx)) :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  obtain ⟨δw, ρw, εw, hδw, hρw, hεw, hWstep⟩ := hWq _ hqwc
  obtain ⟨δx, ρx, εx, hδx, hρx, hεx, hXstep⟩ := hXq _ hqxc
  refine ⟨max qfloor (max qd (max qw qx)), min δd (min δw δx), min ρd (min ρw ρx),
    min εd (min εw εx), max Dd Rw, max md (max mw mx), le_max_left _ _, hqd.trans_le hqdc,
    lt_min hδd (lt_min hδw hδx), lt_min hρd (lt_min hρw hρx), lt_min hεd (lt_min hεw hεx),
    lt_max_of_lt_left hDd, ?_⟩
  intro qs hqs hqsC p₀ δbound ρbound hacc hDc hm hδ hρ H hH hpinch
  obtain ⟨p, records, hrec⟩ :=
    (H.hasCanonicalCutoffRecords_iff_exists_isCanonicalCutoffRecordFamily p₀ δbound ρbound).mp
      hH.2.2.2.1
  have hd := hDstep _ hqdc p₀ δbound ρbound (hacc.trans (min_le_left _ _))
    ((le_max_left _ _).trans hDc) ((le_max_left _ _).trans hm) (hδ.trans (min_le_left _ _))
    (hρ.trans (min_le_left _ _)) H hH hpinch
  have hw := hWstep p₀ δbound ρbound
    (hacc.trans ((min_le_right _ _).trans (min_le_left _ _))) ((le_max_right _ _).trans hDc)
    (((le_max_left _ _).trans (le_max_right _ _)).trans hm)
    (hδ.trans ((min_le_right _ _).trans (min_le_left _ _)))
    (hρ.trans ((min_le_right _ _).trans (min_le_left _ _))) H hH p records hrec hpinch
  have hx := hXstep qs hqs hqsC p₀ δbound ρbound
    (hacc.trans ((min_le_right _ _).trans (min_le_right _ _)))
    ((by linarith : Dx ≤ Rw).trans ((le_max_right _ _).trans hDc))
    (((le_max_right _ _).trans (le_max_right _ _)).trans hm)
    (hδ.trans ((min_le_right _ _).trans (min_le_right _ _)))
    (hρ.trans ((min_le_right _ _).trans (min_le_right _ _))) H hH p records hrec hpinch
  refine ⟨?_, ?_⟩
  · intro j hcan hder hgrad hspat t₀ ht₀ hcb hdb hgb hsb hnc
    obtain ⟨η₁, hη₁, h₁⟩ := hd.1 j hcan hder hgrad t₀ ht₀ hcb hdb hgb hnc
    obtain ⟨η₂, hη₂, h₂⟩ := hw.1 j hcan hder hgrad t₀ ht₀ hcb hdb hgb hnc
    obtain ⟨η₃, hη₃, h₃⟩ := hx.1 j hcan hder hgrad hspat t₀ ht₀ hcb hdb hgb hsb hnc
    refine ⟨min η₁ (min η₂ η₃), lt_min hη₁ (lt_min hη₂ hη₃),
      (H.toHistory.event j).incoming.canonicalBoundsOn_of_cover h₁ h₂ h₃ fun y t => ?_⟩
    rcases le_or_gt θ ((H.toHistory.event j).incoming.flow.scalar t y *
      (t - H.time j.castSucc)) with h | h
    · exact Or.inl h
    · by_cases hc : H.CapWindowPoint records j.castSucc y t Dx θcap
      · exact Or.inr (Or.inl hc)
      · exact Or.inr (Or.inr ⟨h, hc⟩)
  · intro s G hG hpG hcan hder hgrad hspat hncL t₀ ht₀ hcb hdb hgb hsb hnc
    obtain ⟨η₁, hη₁, h₁⟩ := hd.2 s G hG hpG hcan hder hgrad hncL t₀ ht₀ hcb hdb hgb hnc
    obtain ⟨η₂, hη₂, h₂⟩ := hw.2 s G hG hpG hcan hder hgrad hncL t₀ ht₀ hcb hdb hgb hnc
    obtain ⟨η₃, hη₃, h₃⟩ :=
      hx.2 s G hG hpG hcan hder hgrad hspat hncL t₀ ht₀ hcb hdb hgb hsb hnc
    refine ⟨min η₁ (min η₂ η₃), lt_min hη₁ (lt_min hη₂ hη₃),
      G.canonicalBoundsOn_of_cover h₁ h₂ h₃ fun y t => ?_⟩
    rcases le_or_gt θ (G.flow.scalar t y * (t - H.time (Fin.last H.eventCount))) with h | h
    · exact Or.inl h
    · by_cases hc : H.CapWindowPoint records (Fin.last H.eventCount) y t Dx θcap
      · exact Or.inr (Or.inl hc)
      · exact Or.inr (Or.inr ⟨h, hc⟩)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end
