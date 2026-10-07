import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HTraceBall_S138

/-!
# CH12-S138, group 2c: `hFEcore_S138`, `hFE_S138` -- the hFE glue with the hTrace producer plugged in

`hFEcore_S138 Hp hP2 hFront hshift hCapWin hBall := hFEcore_of_trace_S133 Hp hFront hshift (hTrace_S138 Hp hP2 hCapWin hBall)`,
`hFE_S138 … := hFE_of_core_S127 Hp (hFEcore_S138 …)`.  The remaining inline binders: `hFront` (S113 text, discharged by
`hFront_of_collar_S95`), `hshift` (v4; producer `hshift_of_hbirth_S131` after regeneration / hbirth -> hsurv), `hCapWin`
(`[FROZEN] CH12-S133 hCapWin`, ch11 candidate RFC-c), `hBall` (`[FROZEN] CH12-S138 hBall`, group 2).
-/

set_option autoImplicit false

noncomputable section

open Set Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
  DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
  DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
  DifferentialGeometry.Geometry.Riemannian
open scoped Manifold ContDiff ENNReal NNReal

namespace GC.LongTime.Ch12

universe u

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ}

theorem hFEcore_S138
    (Hp : GC.LongTime.AnalyticSurgeryProfile F δ) {Ctime : ℝ≥0} (hP2 : P2_O2 Hp Ctime)
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
                (B.point j.succ le_rfl (Fin.le_last _)) (20 * (θ' * ρ / 40)) →
            metricScalarAt ((sliceHistoryR_O3 F s).toHistory.event j).outputMetric
              (((records j hj).static b).window x) ≤ 9 * K / (θ' * ρ / 40) ^ 2 →
            s.time - (sliceHistoryR_O3 F s).time j.succ < τ * (θ' * ρ / 40) ^ 2 →
            40 * (θ' * ρ / 40) * Real.sqrt ((records j hj).static b).neck.scale ≤ 1)
    (hCapWin : ∀ (θ Dcap : ℝ), StandardCap.transitionEnd + 3 < Dcap → ∃ (Tc εc : ℝ), 0 < εc ∧
      ∀ s : RegularSlice F.observation, Tc ≤ s.time → ∀ T₀ : ℝ, Tc ≤ T₀ → T₀ ≤ s.time →
      ∀ (pp : CutoffParameters)
        (records : ∀ i : Fin (sliceHistoryR_O3 F s).eventCount,
          T₀ - θ ≤ (sliceHistoryR_O3 F s).time i.succ →
          GeometricCutoffRecord (sliceHistoryR_O3 F s).toHistory i pp),
        pp.delta = Hp.parameters.delta → pp.neckRadius = Hp.parameters.neckRadius →
        pp.fixed = Hp.parameters.fixed → pp.recenterConstant = Hp.parameters.recenterConstant →
        32 * (Dcap + 1) + 2 ≤ pp.modelRadius →
        pp.modelAccuracy ≤ εc → 4 ≤ pp.modelOrder →
        (∀ i hi b, linkedCanonicalWindow_O2 ((records i hi).static b)) →
      ∀ (j : Fin (sliceHistoryR_O3 F s).eventCount)
        (hj : T₀ - θ ≤ (sliceHistoryR_O3 F s).time j.succ)
        (b : ((sliceHistoryR_O3 F s).toHistory.event j).RetainedBoundaryIndex) (z : ThreeBall),
        ∃ x : standardCapWindow pp.modelRadius, ‖x.val‖ < Dcap - 1 + 1 ∧
          ((records j hj).static b).window x =
            ((records j hj).static b).inclusion (((records j hj).static b).witness.cap z))
    (hBall : ∀ w : ℝ, 0 < w → ∀ Λ : ℝ, 1 ≤ Λ → ∀ (θ Dcap C0 : ℝ), 0 < θ → 0 < C0 → StandardCap.transitionEnd + 3 < Dcap →
          ∃ (K' τ₀ : ℝ), 0 < K' ∧ 0 < τ₀ ∧ ∀ τ₁ τ₂ : ℝ, 0 < τ₁ → τ₁ ≤ τ₀ → 0 < τ₂ → τ₂ ≤ τ₀ →
          ∃ (bF TF θ₁ εF : ℝ), 0 < bF ∧ 0 < TF ∧ 0 < θ₁ ∧ 0 < εF ∧
          ∀ s : RegularSlice F.observation, TF ≤ s.time → ∀ T₀ : ℝ, TF ≤ T₀ → T₀ ≤ s.time →
          ∀ (pp : CutoffParameters)
            (records : ∀ i : Fin (sliceHistoryR_O3 F s).eventCount,
              T₀ - θ ≤ (sliceHistoryR_O3 F s).time i.succ →
              GeometricCutoffRecord (sliceHistoryR_O3 F s).toHistory i pp),
            pp.delta = Hp.parameters.delta → pp.neckRadius = Hp.parameters.neckRadius →
            pp.fixed = Hp.parameters.fixed → pp.recenterConstant = Hp.parameters.recenterConstant →
            32 * (Dcap + 1) + 2 ≤ pp.modelRadius →
            pp.modelAccuracy ≤ εF → 4 ≤ pp.modelOrder →
            (∀ i hi b, linkedCanonicalWindow_O2 ((records i hi).static b)) →
          ∀ (p : s.stage.Carrier) (ρ : ℝ), 0 < ρ → ρ ≤ bF * Real.sqrt s.time →
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
            ∀ θ' : ℝ, 0 < θ' → θ' ≤ θ₁ → ∀ q' : (s.history.stageAt (sliceTop_S8 s)).Carrier, HEq q' q →
              ∀ (a₀ : Icc (0 : ℝ) s.history.horizon) (hat : a₀ ≤ sliceTop_S8 s)
                (X : BackwardPointTrace s.history (s.history.activeStage a₀)
                  (s.history.activeStage (sliceTop_S8 s)) (s.history.activeStage_mono hat) q'),
                (a₀ : ℝ) = s.time - (τ₁ + τ₂) * (θ' * ρ) ^ 2 →
                (∀ (v : Icc (0 : ℝ) s.history.horizon) (hav : a₀ ≤ v) (hvt : v ≤ sliceTop_S8 s),
                  metricScalarAt (s.history.stageMetric (s.history.activeStage v) v)
                    (X.point (s.history.activeStage v) (s.history.activeStage_mono hav)
                      (s.history.activeStage_mono hvt)) ≤ 4 * max C0 1 / ρ ^ 2) →
                ∀ (v : Icc (0 : ℝ) s.history.horizon) (hav : a₀ ≤ v) (hvt : v ≤ sliceTop_S8 s),
                  ∀ z ∈ riemannianBallOf (s.history.stageMetric (s.history.activeStage v) v)
                    (X.point (s.history.activeStage v) (s.history.activeStage_mono hav)
                      (s.history.activeStage_mono hvt)) (20 * (θ' * ρ / 40)),
                    Real.sqrt (normSq0S (s.history.stageMetric (s.history.activeStage v) v) z 4
                      (metricRm04At (s.history.stageMetric (s.history.activeStage v) v) z)) ≤
                      K' / (θ' * ρ / 40) ^ 2) :
    ∀ w : ℝ, 0 < w → ∀ Λ : ℝ, 1 ≤ Λ → ∀ (θ Dcap C0 : ℝ), 0 < θ → 0 < C0 → StandardCap.transitionEnd + 3 < Dcap →
          ∃ (bF TF K τ₁ τ₂ θ₁ εF : ℝ), 0 < bF ∧ 0 < TF ∧ 0 < K ∧ 0 < τ₁ ∧ 0 < τ₂ ∧ 0 < θ₁ ∧ 0 < εF ∧
          ∀ s : RegularSlice F.observation, TF ≤ s.time → ∀ T₀ : ℝ, TF ≤ T₀ → T₀ ≤ s.time →
          ∀ (pp : CutoffParameters)
            (records : ∀ i : Fin (sliceHistoryR_O3 F s).eventCount,
              T₀ - θ ≤ (sliceHistoryR_O3 F s).time i.succ →
              GeometricCutoffRecord (sliceHistoryR_O3 F s).toHistory i pp),
            pp.delta = Hp.parameters.delta → pp.neckRadius = Hp.parameters.neckRadius →
            pp.fixed = Hp.parameters.fixed → pp.recenterConstant = Hp.parameters.recenterConstant →
            32 * (Dcap + 1) + 2 ≤ pp.modelRadius →
            pp.modelAccuracy ≤ εF → 4 ≤ pp.modelOrder →
            (∀ i hi b, linkedCanonicalWindow_O2 ((records i hi).static b)) →
          ∀ (p : s.stage.Carrier) (ρ : ℝ), 0 < ρ → ρ ≤ bF * Real.sqrt s.time →
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
            ∀ θ' : ℝ, 0 < θ' → θ' ≤ θ₁ → ∀ q' : (s.history.stageAt (sliceTop_S8 s)).Carrier, HEq q' q →
              ∃ (a' : Icc (0 : ℝ) s.history.horizon) (hat : a' ≤ sliceTop_S8 s)
                (X : BackwardPointTrace s.history (s.history.activeStage a')
                  (s.history.activeStage (sliceTop_S8 s)) (s.history.activeStage_mono hat) q'),
                (a' : ℝ) = s.time - τ₁ * (θ' * ρ) ^ 2 ∧
                (∀ (u : Icc (0 : ℝ) s.history.horizon) (hau : a' ≤ u) (hut : u ≤ sliceTop_S8 s),
                  s.history.isTracedRegion u
                    (X.point (s.history.activeStage u) (s.history.activeStage_mono hau)
                      (s.history.activeStage_mono hut))
                    (θ' * ρ / 40) (τ₂ * (θ' * ρ) ^ 2) (K * ((θ' * ρ) ^ 2)⁻¹)) :=
  hFEcore_of_trace_S133 Hp hFront hshift (hTrace_S138 Hp hP2 hCapWin hBall)

theorem hFE_S138
    (Hp : GC.LongTime.AnalyticSurgeryProfile F δ) {Ctime : ℝ≥0} (hP2 : P2_O2 Hp Ctime)
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
                (B.point j.succ le_rfl (Fin.le_last _)) (20 * (θ' * ρ / 40)) →
            metricScalarAt ((sliceHistoryR_O3 F s).toHistory.event j).outputMetric
              (((records j hj).static b).window x) ≤ 9 * K / (θ' * ρ / 40) ^ 2 →
            s.time - (sliceHistoryR_O3 F s).time j.succ < τ * (θ' * ρ / 40) ^ 2 →
            40 * (θ' * ρ / 40) * Real.sqrt ((records j hj).static b).neck.scale ≤ 1)
    (hCapWin : ∀ (θ Dcap : ℝ), StandardCap.transitionEnd + 3 < Dcap → ∃ (Tc εc : ℝ), 0 < εc ∧
      ∀ s : RegularSlice F.observation, Tc ≤ s.time → ∀ T₀ : ℝ, Tc ≤ T₀ → T₀ ≤ s.time →
      ∀ (pp : CutoffParameters)
        (records : ∀ i : Fin (sliceHistoryR_O3 F s).eventCount,
          T₀ - θ ≤ (sliceHistoryR_O3 F s).time i.succ →
          GeometricCutoffRecord (sliceHistoryR_O3 F s).toHistory i pp),
        pp.delta = Hp.parameters.delta → pp.neckRadius = Hp.parameters.neckRadius →
        pp.fixed = Hp.parameters.fixed → pp.recenterConstant = Hp.parameters.recenterConstant →
        32 * (Dcap + 1) + 2 ≤ pp.modelRadius →
        pp.modelAccuracy ≤ εc → 4 ≤ pp.modelOrder →
        (∀ i hi b, linkedCanonicalWindow_O2 ((records i hi).static b)) →
      ∀ (j : Fin (sliceHistoryR_O3 F s).eventCount)
        (hj : T₀ - θ ≤ (sliceHistoryR_O3 F s).time j.succ)
        (b : ((sliceHistoryR_O3 F s).toHistory.event j).RetainedBoundaryIndex) (z : ThreeBall),
        ∃ x : standardCapWindow pp.modelRadius, ‖x.val‖ < Dcap - 1 + 1 ∧
          ((records j hj).static b).window x =
            ((records j hj).static b).inclusion (((records j hj).static b).witness.cap z))
    (hBall : ∀ w : ℝ, 0 < w → ∀ Λ : ℝ, 1 ≤ Λ → ∀ (θ Dcap C0 : ℝ), 0 < θ → 0 < C0 → StandardCap.transitionEnd + 3 < Dcap →
          ∃ (K' τ₀ : ℝ), 0 < K' ∧ 0 < τ₀ ∧ ∀ τ₁ τ₂ : ℝ, 0 < τ₁ → τ₁ ≤ τ₀ → 0 < τ₂ → τ₂ ≤ τ₀ →
          ∃ (bF TF θ₁ εF : ℝ), 0 < bF ∧ 0 < TF ∧ 0 < θ₁ ∧ 0 < εF ∧
          ∀ s : RegularSlice F.observation, TF ≤ s.time → ∀ T₀ : ℝ, TF ≤ T₀ → T₀ ≤ s.time →
          ∀ (pp : CutoffParameters)
            (records : ∀ i : Fin (sliceHistoryR_O3 F s).eventCount,
              T₀ - θ ≤ (sliceHistoryR_O3 F s).time i.succ →
              GeometricCutoffRecord (sliceHistoryR_O3 F s).toHistory i pp),
            pp.delta = Hp.parameters.delta → pp.neckRadius = Hp.parameters.neckRadius →
            pp.fixed = Hp.parameters.fixed → pp.recenterConstant = Hp.parameters.recenterConstant →
            32 * (Dcap + 1) + 2 ≤ pp.modelRadius →
            pp.modelAccuracy ≤ εF → 4 ≤ pp.modelOrder →
            (∀ i hi b, linkedCanonicalWindow_O2 ((records i hi).static b)) →
          ∀ (p : s.stage.Carrier) (ρ : ℝ), 0 < ρ → ρ ≤ bF * Real.sqrt s.time →
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
            ∀ θ' : ℝ, 0 < θ' → θ' ≤ θ₁ → ∀ q' : (s.history.stageAt (sliceTop_S8 s)).Carrier, HEq q' q →
              ∀ (a₀ : Icc (0 : ℝ) s.history.horizon) (hat : a₀ ≤ sliceTop_S8 s)
                (X : BackwardPointTrace s.history (s.history.activeStage a₀)
                  (s.history.activeStage (sliceTop_S8 s)) (s.history.activeStage_mono hat) q'),
                (a₀ : ℝ) = s.time - (τ₁ + τ₂) * (θ' * ρ) ^ 2 →
                (∀ (v : Icc (0 : ℝ) s.history.horizon) (hav : a₀ ≤ v) (hvt : v ≤ sliceTop_S8 s),
                  metricScalarAt (s.history.stageMetric (s.history.activeStage v) v)
                    (X.point (s.history.activeStage v) (s.history.activeStage_mono hav)
                      (s.history.activeStage_mono hvt)) ≤ 4 * max C0 1 / ρ ^ 2) →
                ∀ (v : Icc (0 : ℝ) s.history.horizon) (hav : a₀ ≤ v) (hvt : v ≤ sliceTop_S8 s),
                  ∀ z ∈ riemannianBallOf (s.history.stageMetric (s.history.activeStage v) v)
                    (X.point (s.history.activeStage v) (s.history.activeStage_mono hav)
                      (s.history.activeStage_mono hvt)) (20 * (θ' * ρ / 40)),
                    Real.sqrt (normSq0S (s.history.stageMetric (s.history.activeStage v) v) z 4
                      (metricRm04At (s.history.stageMetric (s.history.activeStage v) v) z)) ≤
                      K' / (θ' * ρ / 40) ^ 2) :
    ∀ w : ℝ, 0 < w → ∀ Λ : ℝ, 1 ≤ Λ → ∀ (θ Dcap C0 : ℝ), 0 < θ → 0 < C0 → StandardCap.transitionEnd + 3 < Dcap →
          ∃ (bF TF K τ₁ τ₂ w₁ θ₁ εF : ℝ), 0 < bF ∧ 0 < TF ∧ 0 < K ∧ 0 < τ₁ ∧ 0 < τ₂ ∧ 0 < w₁ ∧ 0 < θ₁ ∧ 0 < εF ∧
          ∀ s : RegularSlice F.observation, TF ≤ s.time → ∀ T₀ : ℝ, TF ≤ T₀ → T₀ ≤ s.time →
          ∀ (pp : CutoffParameters)
            (records : ∀ i : Fin (sliceHistoryR_O3 F s).eventCount,
              T₀ - θ ≤ (sliceHistoryR_O3 F s).time i.succ →
              GeometricCutoffRecord (sliceHistoryR_O3 F s).toHistory i pp),
            pp.delta = Hp.parameters.delta → pp.neckRadius = Hp.parameters.neckRadius →
            pp.fixed = Hp.parameters.fixed → pp.recenterConstant = Hp.parameters.recenterConstant →
            32 * (Dcap + 1) + 2 ≤ pp.modelRadius →
            pp.modelAccuracy ≤ εF → 4 ≤ pp.modelOrder →
            (∀ i hi b, linkedCanonicalWindow_O2 ((records i hi).static b)) →
          ∀ (p : s.stage.Carrier) (ρ : ℝ), 0 < ρ → ρ ≤ bF * Real.sqrt s.time →
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
            ∀ θ' : ℝ, 0 < θ' → θ' ≤ θ₁ → ∀ q' : (s.history.stageAt (sliceTop_S8 s)).Carrier, HEq q' q →
              ∃ (a' : Icc (0 : ℝ) s.history.horizon) (hat : a' ≤ sliceTop_S8 s)
                (X : BackwardPointTrace s.history (s.history.activeStage a')
                  (s.history.activeStage (sliceTop_S8 s)) (s.history.activeStage_mono hat) q'),
                (a' : ℝ) = s.time - τ₁ * (θ' * ρ) ^ 2 ∧
                (∀ (u : Icc (0 : ℝ) s.history.horizon) (hau : a' ≤ u) (hut : u ≤ sliceTop_S8 s),
                  s.history.isTracedRegion u
                    (X.point (s.history.activeStage u) (s.history.activeStage_mono hau)
                      (s.history.activeStage_mono hut))
                    (θ' * ρ / 40) (τ₂ * (θ' * ρ) ^ 2) (K * ((θ' * ρ) ^ 2)⁻¹)) ∧
                (∀ ρ' : ℝ, 0 < ρ' → ρ' ≤ θ' * ρ →
                  ENNReal.ofReal (w₁ * ρ' ^ 3) ≤
                    ballVolume (s.history.stageMetric (s.history.activeStage (sliceTop_S8 s)) s.time) q' ρ') :=
  hFE_of_core_S127 Hp (hFEcore_S138 Hp hP2 hFront hshift hCapWin hBall)

end GC.LongTime.Ch12
