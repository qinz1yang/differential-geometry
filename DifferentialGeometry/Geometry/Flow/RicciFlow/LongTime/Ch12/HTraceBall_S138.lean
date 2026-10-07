import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.BridgeTrace_S138
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HFEGlue_S133
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HAbs_S105
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.MicroWholeBallShi_O13

/-!
# CH12-S138, group 2b: `hTrace_S138` -- the centre trace of `[FROZEN] CH12-S133 hTrace` from `hCapWin` and `hBall`

`hTrace_S138 Hp hP2 hCapWin hBall : <hTrace of hFEcore_of_trace_S133, verbatim>`.  Group 1 (`centreTrace_S138`) gives the trace
`X` of `q'` down to `a₀ = s.time - (τ₁+τ₂)(θ'ρ)²` with scalar `≤ 4 max(C0,1)/ρ²` on it; the |Rm| bound on the 20r-balls
is the inline binder `hBall` (`[FROZEN] CH12-S138 hBall`, group 2 of the S133 plan, producer open).
Constants: `τ₀ := min τ₀_B (min (1/(16 Cb C0')) (c₀θ/(8C0')))` (`Cb = Ctime+1`, `C0' = max C0 1`), `bF := bF_B`,
`θ₁ := min θ_B (min 1 (θ/((τ₁+τ₂)R²)))` (`R = max (neckRadius 0) 1`), `TF := max Tc T₁ θ TF_B 1`, `εF := min εF_B εc ε₀'`.
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

theorem hTrace_S138
    (Hp : GC.LongTime.AnalyticSurgeryProfile F δ) {Ctime : ℝ≥0} (hP2 : P2_O2 Hp Ctime)
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
              ∃ (a₀ : Icc (0 : ℝ) s.history.horizon) (hat : a₀ ≤ sliceTop_S8 s)
                (X : BackwardPointTrace s.history (s.history.activeStage a₀)
                  (s.history.activeStage (sliceTop_S8 s)) (s.history.activeStage_mono hat) q'),
                (a₀ : ℝ) = s.time - (τ₁ + τ₂) * (θ' * ρ) ^ 2 ∧
                ∀ (v : Icc (0 : ℝ) s.history.horizon) (hav : a₀ ≤ v) (hvt : v ≤ sliceTop_S8 s),
                  ∀ z ∈ riemannianBallOf (s.history.stageMetric (s.history.activeStage v) v)
                    (X.point (s.history.activeStage v) (s.history.activeStage_mono hav)
                      (s.history.activeStage_mono hvt)) (20 * (θ' * ρ / 40)),
                    Real.sqrt (normSq0S (s.history.stageMetric (s.history.activeStage v) v) z 4
                      (metricRm04At (s.history.stageMetric (s.history.activeStage v) v) z)) ≤
                      K' / (θ' * ρ / 40) ^ 2 := by
  intro w hw Λ hΛ θ Dcap C0 hθ hC0 hDcap
  obtain ⟨K', τB, hK', hτB, hB1⟩ := hBall w hw Λ hΛ θ Dcap C0 hθ hC0 hDcap
  obtain ⟨Tc, εc, hεc, hCW⟩ := hCapWin θ Dcap hDcap
  obtain ⟨ε₀', c₀, hε₀', hc₀, hscaleR⟩ := hscale_of_record_S105.{u}
  obtain ⟨T₁, hT₁, hmic⟩ := micro_scale_le_neckRadius_O13 Hp Λ 1 (by linarith) one_pos
  have hte := StandardCap.transitionEnd_pos
  have hD3 : 3 < Dcap := by linarith
  set C0' : ℝ := max C0 1 with hC0'
  have hC0'1 : 1 ≤ C0' := le_max_right _ _
  have hC0'p : 0 < C0' := by linarith
  have hC0C0' : C0 ≤ C0' := le_max_left _ _
  set Cb : ℝ := (Ctime : ℝ) + 1 with hCb
  have hCbp : 0 < Cb := by positivity
  set τG : ℝ := min (1 / (16 * Cb * C0')) (c₀ * θ / (8 * C0')) with hτG
  have hτGp : 0 < τG := lt_min (by positivity) (by positivity)
  have hτG1 : τG ≤ 1 / (16 * Cb * C0') := min_le_left _ _
  have hτG2 : τG ≤ c₀ * θ / (8 * C0') := min_le_right _ _
  refine ⟨K', min τB τG, hK', lt_min hτB hτGp, ?_⟩
  intro τ₁ τ₂ hτ₁ hτ₁₀ hτ₂ hτ₂₀
  have hτ₁B : τ₁ ≤ τB := hτ₁₀.trans (min_le_left _ _)
  have hτ₂B : τ₂ ≤ τB := hτ₂₀.trans (min_le_left _ _)
  have hτ₁G : τ₁ ≤ τG := hτ₁₀.trans (min_le_right _ _)
  have hτ₂G : τ₂ ≤ τG := hτ₂₀.trans (min_le_right _ _)
  obtain ⟨bF, TFB, θB, εB, hbF, hTFB, hθB, hεB, hmainB⟩ := hB1 τ₁ τ₂ hτ₁ hτ₁B hτ₂ hτ₂B
  set R : ℝ := max (Hp.parameters.neckRadius 0) 1 with hR
  have hRpos : 0 < R := lt_max_of_lt_right one_pos
  have hτ12 : 0 < τ₁ + τ₂ := by positivity
  refine ⟨bF, max (max (max (max Tc T₁) θ) TFB) 1, min θB (min 1 (θ / ((τ₁ + τ₂) * R ^ 2))),
    min (min εB εc) ε₀', hbF, lt_max_of_lt_right one_pos,
    lt_min hθB (lt_min one_pos (by positivity)), lt_min (lt_min hεB hεc) hε₀', ?_⟩
  intro s hs T₀ hT₀a hT₀b pp records h1 h2 h3 h4 hmr hacc hord hlink p ρ hρ hρb hev hnn hsec hvol
    hRb q hq hnc θ' hθ' hθ'₁ q' hq'
  have hdest : ∀ x : ℝ, max (max (max (max Tc T₁) θ) TFB) 1 ≤ x →
      Tc ≤ x ∧ T₁ ≤ x ∧ θ ≤ x ∧ TFB ≤ x := by
    intro x hx
    obtain ⟨h5, -⟩ := max_le_iff.mp hx
    obtain ⟨h6, hxt⟩ := max_le_iff.mp h5
    obtain ⟨h7, hxθ⟩ := max_le_iff.mp h6
    obtain ⟨hxc, hx1⟩ := max_le_iff.mp h7
    exact ⟨hxc, hx1, hxθ, hxt⟩
  obtain ⟨hsTc, hsT₁, hsθ, hsTB⟩ := hdest _ hs
  obtain ⟨hTc₀, -, -, hTB₀⟩ := hdest _ hT₀a
  obtain ⟨hA, haccS⟩ := le_min_iff.mp hacc
  obtain ⟨haccB, haccC⟩ := le_min_iff.mp hA
  obtain ⟨hθ'B, hθ'C⟩ := le_min_iff.mp hθ'₁
  obtain ⟨hθ'1, hθ'R⟩ := le_min_iff.mp hθ'C
  have hρN : ρ ≤ Hp.parameters.neckRadius s.time := by
    have h0 := hmic s hsT₁ ρ hev
    linarith only [h0]
  have hρR : ρ ≤ R := by
    have h2 : Hp.parameters.neckRadius s.time ≤ Hp.parameters.neckRadius 0 :=
      Hp.radius_antitone (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr s.positive.le) s.positive.le
    have h3 : Hp.parameters.neckRadius 0 ≤ R := le_max_left _ _
    linarith only [hρN, h2, h3]
  -- the window length `L = (τ₁+τ₂)(θ'ρ)²`
  set L : ℝ := (τ₁ + τ₂) * (θ' * ρ) ^ 2 with hL
  have hL0 : 0 ≤ L := by positivity
  have hθ'sq : θ' ^ 2 ≤ θ' := by nlinarith only [hθ', hθ'1]
  have hρ2 : ρ ^ 2 ≤ R ^ 2 := by gcongr
  have hLle : L ≤ 2 * τG * ρ ^ 2 := by
    have h1' : (θ' * ρ) ^ 2 ≤ ρ ^ 2 := by
      calc (θ' * ρ) ^ 2 = θ' ^ 2 * ρ ^ 2 := by ring
        _ ≤ 1 * ρ ^ 2 := by gcongr; nlinarith only [hθ'sq, hθ'1]
        _ = ρ ^ 2 := one_mul _
    calc L ≤ (2 * τG) * ρ ^ 2 := by
          rw [hL]; apply mul_le_mul (by linarith) h1' (by positivity) (by positivity)
      _ = 2 * τG * ρ ^ 2 := rfl
  have hLθ : L ≤ θ := by
    have h3 : θ' * ((τ₁ + τ₂) * R ^ 2) ≤ θ := (le_div_iff₀ (by positivity)).mp hθ'R
    calc L = (τ₁ + τ₂) * (θ' ^ 2 * ρ ^ 2) := by rw [hL]; ring
      _ ≤ (τ₁ + τ₂) * (θ' * R ^ 2) := by gcongr
      _ = θ' * ((τ₁ + τ₂) * R ^ 2) := by ring
      _ ≤ θ := h3
  have hLs : L ≤ s.time := hLθ.trans hsθ
  have hLy : T₀ - θ ≤ s.time - L := by linarith only [hT₀b, hLθ]
  have hLb : 2 * ((Ctime : ℝ) + 1) * L ≤ ρ ^ 2 / (4 * C0') := by
    have hρ2p : 0 < ρ ^ 2 := by positivity
    have h3 : 4 * Cb * τG ≤ 1 / (4 * C0') := by
      have : 4 * Cb * τG ≤ 4 * Cb * (1 / (16 * Cb * C0')) := by gcongr
      refine this.trans (le_of_eq ?_)
      field_simp; ring
    calc 2 * ((Ctime : ℝ) + 1) * L ≤ 2 * Cb * (2 * τG * ρ ^ 2) := by
          rw [← hCb]; gcongr
      _ = (4 * Cb * τG) * ρ ^ 2 := by ring
      _ ≤ (1 / (4 * C0')) * ρ ^ 2 := by gcongr
      _ = ρ ^ 2 / (4 * C0') := by ring
  have hLc : L * (4 * C0' / ρ ^ 2) ≤ c₀ * θ := by
    have hρ2p : 0 < ρ ^ 2 := by positivity
    have h3 : 8 * τG * C0' ≤ c₀ * θ := by
      have : 8 * τG * C0' ≤ 8 * (c₀ * θ / (8 * C0')) * C0' := by gcongr
      refine this.trans (le_of_eq ?_)
      field_simp
    calc L * (4 * C0' / ρ ^ 2) ≤ (2 * τG * ρ ^ 2) * (4 * C0' / ρ ^ 2) := by gcongr
      _ = 8 * τG * C0' := by field_simp; ring
      _ ≤ c₀ * θ := h3
  have hqe : restrictPoint_CX2 (sliceTowerHistory_CX2 s) (sliceTowerTime_CX2 s) (sliceTop_S8 s) q' = q :=
    eq_of_heq ((restrictPoint_heq_CX2 _ _ _ q').trans hq')
  subst hqe
  have hq2 : restrictPoint_CX2 (sliceTowerHistory_CX2 s) (sliceTowerTime_CX2 s) (sliceTop_S8 s) q' ∈
      riemannianBallOf s.metric p (2 * ρ) := by
    have hq0 := hq
    change riemannianEDistOf _ _ _ < ENNReal.ofReal ρ at hq0
    change riemannianEDistOf _ _ _ < ENNReal.ofReal (2 * ρ)
    exact lt_of_lt_of_le hq0 (ENNReal.ofReal_le_ofReal (by linarith))
  have hx0 : metricScalarAt ((sliceTowerHistory_CX2 s).stageMetric
      ((sliceTowerHistory_CX2 s).activeStage (sliceTowerTime_CX2 s)) (sliceTowerTime_CX2 s))
      (restrictPoint_CX2 (sliceTowerHistory_CX2 s) (sliceTowerTime_CX2 s) (sliceTop_S8 s) q') ≤
        C0' / ρ ^ 2 := by
    rw [← top_scalar_S138 s q' _ (restrictPoint_heq_CX2 _ _ _ q').symm]
    exact (hRb _ hq2).trans (by gcongr)
  have hcap := hCW s hsTc T₀ hTc₀ hT₀b pp records h1 h2 h3 h4 hmr haccC hord hlink
  have hscale : ∀ (j : Fin (sliceHistoryR_O3 F s).eventCount)
      (hj : T₀ - θ ≤ (sliceHistoryR_O3 F s).time j.succ)
      (b : ((sliceHistoryR_O3 F s).toHistory.event j).RetainedBoundaryIndex)
      (x : standardCapWindow pp.modelRadius), ‖x.val‖ < Dcap - 1 + 1 →
      c₀ * ((records j hj).static b).neck.scale ≤
        metricScalarAt ((sliceHistoryR_O3 F s).toHistory.event j).outputMetric
          (((records j hj).static b).window x) :=
    fun j hj b x hx => hscaleR haccS hord (records j hj) b x
      (by linarith only [hx, hmr, hD3])
  have hnc' : ¬ ∃ (j : Fin (sliceHistoryR_O3 F s).eventCount)
      (hj : T₀ - θ ≤ (sliceHistoryR_O3 F s).time j.succ)
      (hl : j.succ ≤ Fin.last (sliceHistoryR_O3 F s).eventCount)
      (B : BackwardPointTrace (sliceHistoryR_O3 F s).toHistory j.succ
        (Fin.last (sliceHistoryR_O3 F s).eventCount) hl
        (restrictPoint_CX2 (sliceTowerHistory_CX2 s) (sliceTowerTime_CX2 s) (sliceTop_S8 s) q'))
      (b : ((sliceHistoryR_O3 F s).toHistory.event j).RetainedBoundaryIndex)
      (x : standardCapWindow pp.modelRadius),
      B.point j.succ le_rfl hl = ((records j hj).static b).window x ∧
        ‖x.val‖ < Dcap - 1 + 1 ∧
        s.time - (sliceHistoryR_O3 F s).time j.succ ≤
          θ * (((records j hj).static b).neck.scale)⁻¹ :=
    fun ⟨j, hj, hl, B, b, x, he, hx, hag⟩ =>
      hnc ⟨j, hj, hl, B, b, x, he, by linarith only [hx], hag⟩
  obtain ⟨a, ha, hau, XT, hXT⟩ := centreTrace_S138 Hp hP2 s (Dc := Dcap - 1) (T₀ := T₀) (θ := θ)
    (c₀ := c₀) (ρ := ρ) (L := L) (C0 := C0') pp records hc₀ hC0'1 hρ hρN hL0 hLs hLy hLb hLc hcap
    hscale _ hx0 hnc'
  let a' : Icc (0 : ℝ) s.history.horizon :=
    ⟨s.time - L, by linarith, (sub_le_self _ hL0).trans (sliceTop_S8 s).property.2⟩
  have hat' : a' ≤ sliceTop_S8 s := show s.time - L ≤ s.time by linarith
  have hae : a = restrictTime_CX2 (sliceTowerHistory_CX2 s) (sliceTowerTime_CX2 s) a' :=
    Subtype.ext ha
  subst hae
  let X := traceAtToRestriction_CX2 (sliceTowerHistory_CX2 s) (sliceTowerTime_CX2 s)
    (a := a') (t := sliceTop_S8 s) (hat := hat') (x := q') XT
  refine ⟨a', hat', X, rfl, ?_⟩
  intro v hav hvt z hz
  refine hmainB s hsTB T₀ hTB₀ hT₀b pp records h1 h2 h3 h4 hmr haccB hord hlink p ρ hρ hρb hev hnn
    hsec hvol hRb _ hq hnc θ' hθ' hθ'B q' hq' a' hat' X rfl ?_ v hav hvt z hz
  intro v hav hvt
  exact (toRestriction_scalar_S138 (sliceTowerHistory_CX2 s) (sliceTowerTime_CX2 s) (hat := hat')
    XT v hav hvt).trans_le (hXT _ hav hvt)

end GC.LongTime.Ch12
