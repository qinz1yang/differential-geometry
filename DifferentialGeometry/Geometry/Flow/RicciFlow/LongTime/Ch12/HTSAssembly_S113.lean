import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HTSBarrierEvent_S113
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.PrefixTrace_S106
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.MicroWholeBallShi_O13

/-!
# CH12-S113, group 2b: `hTS_S113` (the `hTS v2` binder of `hZT_of_kl82_S113`) from S95 / S105 / S106 pieces

* `hbarP_S113`: the located barrier on the slice PREFIX `(sliceHistoryR_O3 F s).toHistory` with the prefix trace `B`
  as centre, from `barrier_event_S113` (one event; `hFront`, `hscale`, relevant-window `hshift`, `¬ CAP`), young events
  (`T₀ ≤ s.time`, `τ r² ≤ θ`).  Feeds `hbar_tower_of_prefix_S106`.
* `hTS_S113`: constants `K₁ = K₀ + K₀/(c₀ θ)` (so `exp (9 K₁ τ) < 2` gives `9 K₀ τ ≤ c₀ θ`), `θ₂` (so `τ (θ'ρ)² ≤ θ`
  from `ρ ≤ neckRadius 0` of `micro_scale_le_neckRadius_O13` + `radius_antitone`), `traced_of_seeds_ball_S95` for the
  seeds, `isTracedRegion.mono_bound` `K₀ → K₁`.  Inline binders (frozen in `[FROZEN v2] CH12-S113 G2`):
  `hFront` (S95 text on records, `Dc := Dcap - 1`; discharged by `hFront_of_collar_S95`), `hshift` (relevant-window
  birth shift, F-S106-3).  `hscale` is internal (`hscale_of_record_S105`).
-/

set_option autoImplicit false

noncomputable section

open Set Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
  DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
  DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Geometry.Curvature
  DifferentialGeometry.Geometry.Riemannian
open scoped Manifold ContDiff ENNReal NNReal

namespace GC.LongTime.Ch12

universe u

theorem hbarP_S113 {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    (s : RegularSlice F.observation) {T₀ θ Dc r τ K c₀ : ℝ} {pp : CutoffParameters}
    (records : ∀ i : Fin (sliceHistoryR_O3 F s).eventCount,
      T₀ - θ ≤ (sliceHistoryR_O3 F s).time i.succ →
      GeometricCutoffRecord (sliceHistoryR_O3 F s).toHistory i pp)
    (z : ((sliceHistoryR_O3 F s).toHistory.stage (Fin.last (sliceHistoryR_O3 F s).eventCount)).Carrier)
    (hT₀ : T₀ ≤ s.time) (hτr : τ * r ^ 2 ≤ θ)
    (hr : 0 < r) (hτ : 0 < τ) (hc₀ : 0 < c₀) (hτK : 9 * K * τ ≤ c₀ * θ)
    (hD : Dc + 2 ≤ pp.modelRadius) (hacc : pp.modelAccuracy ≤ 3 / 4)
    (hFront : ∀ (j : Fin (sliceHistoryR_O3 F s).eventCount)
      (hj : T₀ - θ ≤ (sliceHistoryR_O3 F s).time j.succ),
      ∀ y ∈ frontier (range ((sliceHistoryR_O3 F s).toHistory.event j).oldOutput),
        ∃ (b : ((sliceHistoryR_O3 F s).toHistory.event j).RetainedBoundaryIndex)
          (x : standardCapWindow pp.modelRadius),
          ((records j hj).static b).window x = y ∧ ‖x.val‖ < Dc + 1)
    (hscale : ∀ (j : Fin (sliceHistoryR_O3 F s).eventCount)
      (hj : T₀ - θ ≤ (sliceHistoryR_O3 F s).time j.succ)
      (b : ((sliceHistoryR_O3 F s).toHistory.event j).RetainedBoundaryIndex)
      (x : standardCapWindow pp.modelRadius), ‖x.val‖ < Dc + 1 →
      c₀ * ((records j hj).static b).neck.scale ≤
        metricScalarAt ((sliceHistoryR_O3 F s).toHistory.event j).outputMetric
          (((records j hj).static b).window x))
    (hshift : ∀ (j : Fin (sliceHistoryR_O3 F s).eventCount)
      (hj : T₀ - θ ≤ (sliceHistoryR_O3 F s).time j.succ)
      (B : BackwardPointTrace (sliceHistoryR_O3 F s).toHistory j.succ
        (Fin.last (sliceHistoryR_O3 F s).eventCount) (Fin.le_last _) z)
      (b : ((sliceHistoryR_O3 F s).toHistory.event j).RetainedBoundaryIndex)
      (x : standardCapWindow pp.modelRadius), ‖x.val‖ < Dc + 1 →
      ((records j hj).static b).window x ∈
        riemannianBallOf ((sliceHistoryR_O3 F s).toHistory.event j).outputMetric
          (B.point j.succ le_rfl (Fin.le_last _)) (20 * r) →
      metricScalarAt ((sliceHistoryR_O3 F s).toHistory.event j).outputMetric
        (((records j hj).static b).window x) ≤ 9 * K / r ^ 2 →
      s.time - (sliceHistoryR_O3 F s).time j.succ < τ * r ^ 2 →
      40 * r * Real.sqrt ((records j hj).static b).neck.scale ≤ 1)
    (hno : ¬ ∃ (j : Fin (sliceHistoryR_O3 F s).eventCount)
      (hj : T₀ - θ ≤ (sliceHistoryR_O3 F s).time j.succ)
      (hl : j.succ ≤ Fin.last (sliceHistoryR_O3 F s).eventCount)
      (B : BackwardPointTrace (sliceHistoryR_O3 F s).toHistory j.succ
        (Fin.last (sliceHistoryR_O3 F s).eventCount) hl z)
      (b : ((sliceHistoryR_O3 F s).toHistory.event j).RetainedBoundaryIndex)
      (x : standardCapWindow pp.modelRadius),
      B.point j.succ le_rfl hl = ((records j hj).static b).window x ∧
        ‖x.val‖ < Dc + 2 ∧
        s.time - (sliceHistoryR_O3 F s).time j.succ ≤
          θ * (((records j hj).static b).neck.scale)⁻¹) :
    ∀ (j : Fin (sliceHistoryR_O3 F s).eventCount)
      (B : BackwardPointTrace (sliceHistoryR_O3 F s).toHistory j.succ
        (Fin.last (sliceHistoryR_O3 F s).eventCount) (Fin.le_last _) z),
      (sliceHistoryR_O3 F s).time j.succ ∈ Ioc (s.time - τ * r ^ 2) s.time →
      ∀ U : Set (((sliceHistoryR_O3 F s).toHistory.stage j.succ).Carrier),
      U ⊆ riemannianBallOf ((sliceHistoryR_O3 F s).toHistory.event j).outputMetric
        (B.point j.succ le_rfl (Fin.le_last _)) (20 * r) → IsPreconnected U →
      (∀ y ∈ U, metricScalarAt ((sliceHistoryR_O3 F s).toHistory.event j).outputMetric y ≤
        (9 * K) / r ^ 2) →
      ∀ (x : ((sliceHistoryR_O3 F s).toHistory.event j).incoming.terminalRegularOpen)
        (z' : ((sliceHistoryR_O3 F s).toHistory.stage j.succ).Carrier), z' ∈ U →
        ((sliceHistoryR_O3 F s).toHistory.event j).RegularCrossing x.val z' →
        U ⊆ interior (range ((sliceHistoryR_O3 F s).toHistory.event j).oldOutput) := by
  intro j B ht U hUb hU hs x z' hz' hc
  have hj : T₀ - θ ≤ (sliceHistoryR_O3 F s).time j.succ := by
    have h1 := ht.1
    linarith only [h1, hT₀, hτr]
  have hage : s.time - (sliceHistoryR_O3 F s).time j.succ < τ * r ^ 2 := by
    have h1 := ht.1
    linarith only [h1]
  exact barrier_event_S113 (records j hj) (hFront j hj) hr hτ hc₀ hτK hD hacc (hscale j hj)
    (fun b x hx hb hs' => hshift j hj B b x hx hb hs' hage) hage
    (fun ⟨b, w', hw', he, hag⟩ => hno ⟨j, hj, Fin.le_last _, B, b, w', he.symm, hw', hag⟩)
    hUb hU hs hz' hc

variable {δ : ℝ → ℝ}

theorem hTS_S113 {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    (Hp : GC.LongTime.AnalyticSurgeryProfile F δ)
    (hFront : ∀ (θ Dcap : ℝ), StandardCap.transitionEnd + 3 < Dcap → ∃ (Tf εFr : ℝ), 0 < εFr ∧
      ∀ s : RegularSlice F.observation, Tf ≤ s.time → ∀ T₀ : ℝ, Tf ≤ T₀ → T₀ ≤ s.time →
      ∀ (pp : CutoffParameters)
        (records : ∀ i : Fin (sliceHistoryR_O3 F s).eventCount,
          T₀ - θ ≤ (sliceHistoryR_O3 F s).time i.succ →
          GeometricCutoffRecord (sliceHistoryR_O3 F s).toHistory i pp),
        pp.delta = Hp.parameters.delta → pp.neckRadius = Hp.parameters.neckRadius →
        pp.fixed = Hp.parameters.fixed → pp.recenterConstant = Hp.parameters.recenterConstant →
        32 * (Dcap + 1) + 2 ≤ pp.modelRadius →
        pp.modelAccuracy ≤ εFr → 4 ≤ pp.modelOrder →
        (∀ i hi b, linkedCanonicalWindow_O2 ((records i hi).static b)) →
      ∀ (j : Fin (sliceHistoryR_O3 F s).eventCount)
        (hj : T₀ - θ ≤ (sliceHistoryR_O3 F s).time j.succ),
        ∀ y ∈ frontier (range ((sliceHistoryR_O3 F s).toHistory.event j).oldOutput),
          ∃ (b : ((sliceHistoryR_O3 F s).toHistory.event j).RetainedBoundaryIndex)
            (x : standardCapWindow pp.modelRadius),
            ((records j hj).static b).window x = y ∧ ‖x.val‖ < Dcap - 1 + 1)
    (hshift : ∀ w : ℝ, 0 < w → ∀ Λ : ℝ, 1 ≤ Λ → ∀ (θ Dcap C0 : ℝ), 0 < θ → 0 < C0 →
      StandardCap.transitionEnd + 3 < Dcap → ∀ K : ℝ, 0 < K →
      ∃ (bH TH θH εH : ℝ), 0 < bH ∧ 0 < θH ∧ 0 < εH ∧
      ∀ s : RegularSlice F.observation, TH ≤ s.time → ∀ T₀ : ℝ, TH ≤ T₀ → T₀ ≤ s.time →
      ∀ (pp : CutoffParameters)
        (records : ∀ i : Fin (sliceHistoryR_O3 F s).eventCount,
          T₀ - θ ≤ (sliceHistoryR_O3 F s).time i.succ →
          GeometricCutoffRecord (sliceHistoryR_O3 F s).toHistory i pp),
        pp.delta = Hp.parameters.delta → pp.neckRadius = Hp.parameters.neckRadius →
        pp.fixed = Hp.parameters.fixed → pp.recenterConstant = Hp.parameters.recenterConstant →
        32 * (Dcap + 1) + 2 ≤ pp.modelRadius →
        pp.modelAccuracy ≤ εH → 4 ≤ pp.modelOrder →
        (∀ i hi b, linkedCanonicalWindow_O2 ((records i hi).static b)) →
      ∀ (p : s.stage.Carrier) (ρ : ℝ), 0 < ρ → ρ ≤ bH * Real.sqrt s.time →
        (∃ n, ∃ i : Fin (F.tower.history n).eventCount, ∃ h,
          (F.tower.history n).time i.succ ∈ Icc (s.time / 2) s.time ∧
          ρ < Λ * (Hp.records n i).nominalRadius h) →
        (∃ z ∈ connectedComponent p, ¬ SectionalBoundedBelowAt s.metric z 0) →
        (∀ q ∈ riemannianBallOf s.metric p ρ,
          SectionalBoundedBelowAt s.metric q (-(ρ ^ 2)⁻¹)) →
        ENNReal.ofReal (w * ρ ^ 3) ≤ ballVolume s.metric p ρ →
        (∀ x ∈ riemannianBallOf s.metric p (2 * ρ), metricScalarAt s.metric x ≤ C0 / ρ ^ 2) →
        ∀ q ∈ riemannianBallOf s.metric p ρ,
          ¬ (∃ (j : Fin (sliceHistoryR_O3 F s).eventCount)
            (hj : T₀ - θ ≤ (sliceHistoryR_O3 F s).time j.succ)
            (hl : j.succ ≤ Fin.last (sliceHistoryR_O3 F s).eventCount)
            (B : BackwardPointTrace (sliceHistoryR_O3 F s).toHistory j.succ
              (Fin.last (sliceHistoryR_O3 F s).eventCount) hl q)
            (b : ((sliceHistoryR_O3 F s).toHistory.event j).RetainedBoundaryIndex)
            (x : standardCapWindow pp.modelRadius),
            B.point j.succ le_rfl hl = ((records j hj).static b).window x ∧
              ‖x.val‖ < Dcap + 1 ∧
              s.time - (sliceHistoryR_O3 F s).time j.succ ≤
                θ * (((records j hj).static b).neck.scale)⁻¹) →
          ∀ θ' : ℝ, 0 < θ' → θ' ≤ θH → ∀ τ : ℝ, 0 < τ → 9 * K * τ ≤ 1 →
          ∀ (j : Fin (sliceHistoryR_O3 F s).eventCount)
            (hj : T₀ - θ ≤ (sliceHistoryR_O3 F s).time j.succ)
            (B : BackwardPointTrace (sliceHistoryR_O3 F s).toHistory j.succ
              (Fin.last (sliceHistoryR_O3 F s).eventCount) (Fin.le_last _) q)
            (b : ((sliceHistoryR_O3 F s).toHistory.event j).RetainedBoundaryIndex)
            (x : standardCapWindow pp.modelRadius), ‖x.val‖ < Dcap - 1 + 1 →
            ((records j hj).static b).window x ∈
              riemannianBallOf ((sliceHistoryR_O3 F s).toHistory.event j).outputMetric
                (B.point j.succ le_rfl (Fin.le_last _)) (20 * (θ' * ρ)) →
            metricScalarAt ((sliceHistoryR_O3 F s).toHistory.event j).outputMetric
              (((records j hj).static b).window x) ≤ 9 * K / (θ' * ρ) ^ 2 →
            s.time - (sliceHistoryR_O3 F s).time j.succ < τ * (θ' * ρ) ^ 2 →
            40 * (θ' * ρ) * Real.sqrt ((records j hj).static b).neck.scale ≤ 1)
    :
    ∀ w : ℝ, 0 < w → ∀ Λ : ℝ, 1 ≤ Λ → ∀ (θ Dcap C0 : ℝ), 0 < θ → 0 < C0 → StandardCap.transitionEnd + 3 < Dcap →
      ∀ a₀ c₁ : ℝ, 0 < a₀ → 0 < c₁ →
      ∃ (bS TS T₀' ρ₀ K₀ θ₂ εT : ℝ), 0 < bS ∧ 0 < TS ∧ 0 < T₀' ∧ 0 < ρ₀ ∧ 0 < K₀ ∧ 0 < θ₂ ∧ 0 < εT ∧
      ∀ s : RegularSlice F.observation, TS ≤ s.time → ∀ T₀ : ℝ, TS ≤ T₀ → T₀ ≤ s.time →
      ∀ (pp : CutoffParameters)
        (records : ∀ i : Fin (sliceHistoryR_O3 F s).eventCount,
          T₀ - θ ≤ (sliceHistoryR_O3 F s).time i.succ →
          GeometricCutoffRecord (sliceHistoryR_O3 F s).toHistory i pp),
        pp.delta = Hp.parameters.delta → pp.neckRadius = Hp.parameters.neckRadius →
        pp.fixed = Hp.parameters.fixed → pp.recenterConstant = Hp.parameters.recenterConstant →
        32 * (Dcap + 1) + 2 ≤ pp.modelRadius →
        pp.modelAccuracy ≤ εT → 4 ≤ pp.modelOrder →
        (∀ i hi b, linkedCanonicalWindow_O2 ((records i hi).static b)) →
      ∀ (p : s.stage.Carrier) (ρ : ℝ), 0 < ρ → ρ ≤ bS * Real.sqrt s.time →
        (∃ n, ∃ i : Fin (F.tower.history n).eventCount, ∃ h,
          (F.tower.history n).time i.succ ∈ Icc (s.time / 2) s.time ∧
          ρ < Λ * (Hp.records n i).nominalRadius h) →
        (∃ z ∈ connectedComponent p, ¬ SectionalBoundedBelowAt s.metric z 0) →
        (∀ q ∈ riemannianBallOf s.metric p ρ,
          SectionalBoundedBelowAt s.metric q (-(ρ ^ 2)⁻¹)) →
        ENNReal.ofReal (w * ρ ^ 3) ≤ ballVolume s.metric p ρ →
        (∀ x ∈ riemannianBallOf s.metric p (2 * ρ), metricScalarAt s.metric x ≤ C0 / ρ ^ 2) →
        ∀ q ∈ riemannianBallOf s.metric p ρ,
          ¬ (∃ (j : Fin (sliceHistoryR_O3 F s).eventCount)
            (hj : T₀ - θ ≤ (sliceHistoryR_O3 F s).time j.succ)
            (hl : j.succ ≤ Fin.last (sliceHistoryR_O3 F s).eventCount)
            (B : BackwardPointTrace (sliceHistoryR_O3 F s).toHistory j.succ
              (Fin.last (sliceHistoryR_O3 F s).eventCount) hl q)
            (b : ((sliceHistoryR_O3 F s).toHistory.event j).RetainedBoundaryIndex)
            (x : standardCapWindow pp.modelRadius),
            B.point j.succ le_rfl hl = ((records j hj).static b).window x ∧
              ‖x.val‖ < Dcap + 1 ∧
              s.time - (sliceHistoryR_O3 F s).time j.succ ≤
                θ * (((records j hj).static b).neck.scale)⁻¹) →
          ∀ θ' : ℝ, 0 < θ' → θ' ≤ θ₂ → ∀ τ : ℝ, 0 < τ → Real.exp (9 * K₀ * τ) < 2 →
          ∀ q' : (s.history.stageAt (sliceTop_S8 s)).Carrier, HEq q' q →
          (∀ v : Icc (0 : ℝ) s.history.horizon, s.time - τ * (θ' * ρ) ^ 2 ≤ v.val →
            ∃ yv : (s.history.stageAt v).Carrier,
              hasSmallParabolicCurvature s.history v yv (a₀ * (θ' * ρ)) ∧
              ENNReal.ofReal (c₁ * (a₀ * (θ' * ρ)) ^ 3) ≤
                ballVolume (s.history.stageMetric (s.history.activeStage v) v) yv (a₀ * (θ' * ρ)) ∧
              ∃ A : BackwardPointTrace s.history (s.history.activeStage v)
                  (s.history.activeStage (sliceTop_S8 s)) (s.history.activeStage_mono
                    (show v ≤ sliceTop_S8 s from v.property.2)) q',
                A.point (s.history.activeStage v) le_rfl
                  (s.history.activeStage_mono (show v ≤ sliceTop_S8 s from v.property.2)) = yv) →
          (∀ v : Icc (0 : ℝ) s.history.horizon, s.time - τ * (θ' * ρ) ^ 2 ≤ v.val →
            T₀' ≤ v.val ∧ θ' * ρ ≤ ρ₀ * Real.sqrt v) →
          s.history.isTracedRegion (sliceTop_S8 s) q' (2 * (θ' * ρ)) (τ * (θ' * ρ) ^ 2)
            (K₀ / (θ' * ρ) ^ 2) := by
  intro w hw Λ hΛ θ Dcap C0 hθ hC0 hDcap a₀ c₁ ha₀ hc₁
  obtain ⟨T₀S, ρ₀S, K₀S, hT₀S, hρ₀S, hK₀S, hSeed⟩ := traced_of_seeds_ball_S95 Hp ha₀ hc₁
  obtain ⟨ε₀', c₀, hε₀', hc₀, hscaleR⟩ := hscale_of_record_S105.{u}
  obtain ⟨Tf, εFr, hεFr, hFr⟩ := hFront θ Dcap hDcap
  obtain ⟨T₁, hT₁, hmic⟩ := micro_scale_le_neckRadius_O13 Hp Λ 1 (by linarith) one_pos
  obtain ⟨bH, TH, θH, εH, hbH, hθH, hεH, hHs⟩ :=
    hshift w hw Λ hΛ θ Dcap C0 hθ hC0 hDcap K₀S hK₀S
  have hte := StandardCap.transitionEnd_pos
  have hD3 : 3 < Dcap := by linarith
  set K₁ : ℝ := K₀S + K₀S / (c₀ * θ) with hK₁
  have hK₁pos : 0 < K₁ := by positivity
  have hK₀K₁ : K₀S ≤ K₁ := by
    have : 0 ≤ K₀S / (c₀ * θ) := by positivity
    linarith
  set R : ℝ := max (Hp.parameters.neckRadius 0) 1 with hR
  have hRpos : 0 < R := lt_max_of_lt_right one_pos
  set θ₂ : ℝ := min θH (min 1 (9 * K₁ * θ / R ^ 2)) with hθ₂
  have hθ₂pos : 0 < θ₂ := lt_min hθH (lt_min one_pos (by positivity))
  refine ⟨bH, max (max (max Tf TH) T₁) 1, T₀S, ρ₀S, K₁, θ₂,
    min (min (3 / 4) ε₀') (min εFr εH), hbH, lt_max_of_lt_right one_pos, hT₀S, hρ₀S, hK₁pos,
    hθ₂pos, lt_min (lt_min (by norm_num) hε₀') (lt_min hεFr hεH), ?_⟩
  intro s hs T₀ hT₀a hT₀b pp records h1 h2 h3 h4 hmr hacc hord hlink p ρ hρ hρb hev hnn hsec hvol
    hRb q hq hnc θ' hθ' hθ'₂ τ hτ hexp q' hq' hseed hwin
  obtain ⟨hs3, -⟩ := max_le_iff.mp hs
  obtain ⟨hs4, hsT₁⟩ := max_le_iff.mp hs3
  obtain ⟨hsTf, hsTH⟩ := max_le_iff.mp hs4
  obtain ⟨hT3, -⟩ := max_le_iff.mp hT₀a
  obtain ⟨hT4, -⟩ := max_le_iff.mp hT3
  obtain ⟨hTf₀, hTH₀⟩ := max_le_iff.mp hT4
  have hacc₁ : pp.modelAccuracy ≤ 3 / 4 := hacc.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hacc₂ : pp.modelAccuracy ≤ ε₀' := hacc.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hacc₃ : pp.modelAccuracy ≤ εFr := hacc.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hacc₄ : pp.modelAccuracy ≤ εH := hacc.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hr : 0 < θ' * ρ := mul_pos hθ' hρ
  -- the scale ρ is bounded by the (antitone) canonical radius at time 0
  have hρR : ρ ≤ R := by
    have h0 := hmic s hsT₁ ρ hev
    have h2 : Hp.parameters.neckRadius s.time ≤ Hp.parameters.neckRadius 0 :=
      Hp.radius_antitone (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr s.positive.le) s.positive.le
    have h3 : Hp.parameters.neckRadius 0 ≤ R := le_max_left _ _
    linarith only [h0, h2, h3]
  -- constants: τ small, so every window event is young; 9 K₀ τ ≤ c₀ θ
  have hτ1 : 9 * K₁ * τ < 1 := by
    have := Real.add_one_le_exp (9 * K₁ * τ)
    linarith only [this, hexp]
  have hτK : 9 * K₀S * τ ≤ c₀ * θ := by
    have hu : 0 ≤ 9 * K₀S * τ := by positivity
    have hv : 0 < c₀ * θ := by positivity
    have h9 : 9 * K₁ * τ = 9 * K₀S * τ + 9 * K₀S * τ / (c₀ * θ) := by
      rw [hK₁]; field_simp
    have h10 : 9 * K₀S * τ / (c₀ * θ) < 1 := by linarith only [h9, hτ1, hu]
    have := (div_lt_one hv).mp h10
    exact this.le
  have hτ9 : 9 * K₀S * τ ≤ 1 := by
    have : 9 * K₀S * τ ≤ 9 * K₁ * τ := by gcongr
    linarith only [this, hτ1]
  have hexp0 : Real.exp (9 * K₀S * τ) < 2 :=
    lt_of_le_of_lt (Real.exp_le_exp.mpr (by gcongr)) hexp
  have hτr : τ * (θ' * ρ) ^ 2 ≤ θ := by
    have hθ'1 : θ' ≤ 1 := hθ'₂.trans ((min_le_right _ _).trans (min_le_left _ _))
    have hθ'9 : θ' ≤ 9 * K₁ * θ / R ^ 2 :=
      hθ'₂.trans ((min_le_right _ _).trans (min_le_right _ _))
    have hRR : ρ ^ 2 ≤ R ^ 2 := by gcongr
    have hθ'sq : θ' ^ 2 ≤ θ' := by nlinarith only [hθ', hθ'1]
    have hA : θ' ^ 2 * R ^ 2 ≤ 9 * K₁ * θ := by
      have h1' : θ' * R ^ 2 ≤ 9 * K₁ * θ := (le_div_iff₀ (by positivity)).mp hθ'9
      nlinarith only [h1', hθ'sq, sq_nonneg R]
    have hB : (θ' * ρ) ^ 2 ≤ 9 * K₁ * θ := by
      calc (θ' * ρ) ^ 2 = θ' ^ 2 * ρ ^ 2 := by ring
        _ ≤ θ' ^ 2 * R ^ 2 := by gcongr
        _ ≤ 9 * K₁ * θ := hA
    calc τ * (θ' * ρ) ^ 2 ≤ τ * (9 * K₁ * θ) := by gcongr
      _ = (9 * K₁ * τ) * θ := by ring
      _ ≤ 1 * θ := by gcongr
      _ = θ := one_mul θ
  -- endpoint identification: the tower-restricted endpoint is `q`
  have hqe : restrictPoint_CX2 (sliceTowerHistory_CX2 s) (sliceTowerTime_CX2 s) (sliceTop_S8 s) q' = q :=
    eq_of_heq ((restrictPoint_heq_CX2 _ _ _ q').trans hq')
  subst hqe
  -- the start time `l = s.time - τ r²` lies in the time interval
  have hhor : (0 : ℝ) ≤ s.history.horizon :=
    (sliceTop_S8 s).property.1.trans (sliceTop_S8 s).property.2
  have hl0 : 0 ≤ s.time - τ * (θ' * ρ) ^ 2 := by
    by_contra hneg
    push Not at hneg
    have h0 := (hwin ⟨0, le_rfl, hhor⟩ (by change s.time - τ * (θ' * ρ) ^ 2 ≤ 0; linarith only [hneg])).1
    have h0' : T₀S ≤ 0 := h0
    linarith only [h0', hT₀S]
  let l : Icc (0 : ℝ) s.history.horizon :=
    ⟨s.time - τ * (θ' * ρ) ^ 2, hl0,
      (sub_le_self _ (by positivity)).trans (sliceTop_S8 s).property.2⟩
  have hlt : l ≤ sliceTop_S8 s := by
    have h0 : 0 ≤ τ * (θ' * ρ) ^ 2 := by positivity
    change s.time - τ * (θ' * ρ) ^ 2 ≤ s.time
    linarith only [h0]
  have hDc : (Dcap - 1) + 2 ≤ pp.modelRadius := by linarith only [hmr, hD3]
  have hFr' := hFr s hsTf T₀ hTf₀ hT₀b pp records h1 h2 h3 h4 hmr hacc₃ hord hlink
  have hno' : ¬ ∃ (j : Fin (sliceHistoryR_O3 F s).eventCount)
      (hj : T₀ - θ ≤ (sliceHistoryR_O3 F s).time j.succ)
      (hl : j.succ ≤ Fin.last (sliceHistoryR_O3 F s).eventCount)
      (B : BackwardPointTrace (sliceHistoryR_O3 F s).toHistory j.succ
        (Fin.last (sliceHistoryR_O3 F s).eventCount) hl
        (restrictPoint_CX2 (sliceTowerHistory_CX2 s) (sliceTowerTime_CX2 s) (sliceTop_S8 s) q'))
      (b : ((sliceHistoryR_O3 F s).toHistory.event j).RetainedBoundaryIndex)
      (x : standardCapWindow pp.modelRadius),
      B.point j.succ le_rfl hl = ((records j hj).static b).window x ∧
        ‖x.val‖ < (Dcap - 1) + 2 ∧
        s.time - (sliceHistoryR_O3 F s).time j.succ ≤
          θ * (((records j hj).static b).neck.scale)⁻¹ :=
    fun ⟨j, hj, hl, B, b, x, he, hx, hag⟩ =>
      hnc ⟨j, hj, hl, B, b, x, he, by linarith only [hx], hag⟩
  have hbarP := hbarP_S113 s (Dc := Dcap - 1) (K := K₀S) (c₀ := c₀) records
    (restrictPoint_CX2 (sliceTowerHistory_CX2 s) (sliceTowerTime_CX2 s) (sliceTop_S8 s) q')
    hT₀b hτr hr hτ hc₀ hτK hDc hacc₁ hFr'
    (fun j hj b x hx => hscaleR hacc₂ hord (records j hj) b x
      (by linarith only [hx, hmr, hD3]))
    (fun j hj B b x hx hmem hsc hage' =>
      hHs s hsTH T₀ hTH₀ hT₀b pp records h1 h2 h3 h4 hmr hacc₄ hord hlink p ρ hρ hρb hev hnn hsec
        hvol hRb _ hq hnc θ' hθ' (hθ'₂.trans (min_le_left _ _)) τ hτ hτ9 j hj B b x hx hmem hsc
        hage')
    hno'
  have htr := hSeed s l hlt q' (θ' * ρ) τ hr hτ hexp0 rfl
    (fun v hv => hwin v hv)
    (fun v hv => hseed v hv)
    (fun A _ => hbar_tower_of_prefix_S106 s hlt A hbarP)
  exact htr.mono_bound (by positivity) (by gcongr)

end GC.LongTime.Ch12
