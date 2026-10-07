import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HShiftReduce_S131

/-!
# CH12-S137 G0: `hshift` at the v4 scale `θ'ρ/40` from the K-free cap-scale bound `hbirth`

`hshift_of_hbirth_v4_S137 Hp hbirth : <[FROZEN v4] CH12-S130 hshift, verbatim = HFEGlue_S133 l.51-98>`, where
`hbirth` is the S131 binder (old scale, `20 θ'ρ`-ball, `9K/(θ'ρ)²`, age `< τ(θ'ρ)²`) that `hbirth_of_hsurv_S134`
produces.  The v4 premises are the old-scale premises at `K'' = 1600 K`, `τ'' = τ/1600` (`r = θ'ρ/40`:
`9K/r² = 9 K''/(θ'ρ)²`, `τ r² = τ''(θ'ρ)²`, `9 K'' τ'' = 9 K τ`) and a smaller ball, so `hbirth` is instantiated at
`K'' = 1600 K`; `Cb` is then K-dependent but still `θ'`-free; `θH' := min θH (1/(√Cb + 1))`.
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

variable {δ : ℝ → ℝ}

theorem hshift_of_hbirth_v4_S137 {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    (Hp : GC.LongTime.AnalyticSurgeryProfile F δ)
    (hbirth : ∀ w : ℝ, 0 < w → ∀ Λ : ℝ, 1 ≤ Λ → ∀ (θ Dcap C0 : ℝ), 0 < θ → 0 < C0 →
      StandardCap.transitionEnd + 3 < Dcap → ∀ K : ℝ, 0 < K →
      ∃ (Cb bH TH θH εH : ℝ), 0 < Cb ∧ 0 < bH ∧ 0 < θH ∧ 0 < εH ∧
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
            ((records j hj).static b).neck.scale ≤ Cb / ρ ^ 2)
    :
    ∀ w : ℝ, 0 < w → ∀ Λ : ℝ, 1 ≤ Λ → ∀ (θ Dcap C0 : ℝ), 0 < θ → 0 < C0 →
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
            40 * (θ' * ρ / 40) * Real.sqrt ((records j hj).static b).neck.scale ≤ 1 := by
  intro w hw Λ hΛ θ Dcap C0 hθ hC0 hD K hK
  have hK' : 0 < 1600 * K := by positivity
  obtain ⟨Cb, bH, TH, θH, εH, hCb, hb, hθH, hεH, h⟩ :=
    hbirth w hw Λ hΛ θ Dcap C0 hθ hC0 hD (1600 * K) hK'
  have hpos : 0 < Real.sqrt Cb + 1 := by positivity
  refine ⟨bH, TH, min θH (1 / (Real.sqrt Cb + 1)), εH, hb, lt_min hθH (by positivity), hεH, ?_⟩
  intro s hs T₀ hT₀ hT₀s pp records e1 e2 e3 e4 hmr hacc hord hlink p ρ hρ hρb h2 h3 h4 h5 h6 q hq hno
    θ' hθ' hθ'H τ hτ hτK j hj B b x hx hmem hsc hage
  have hle : θ' ≤ 1 / (Real.sqrt Cb + 1) := hθ'H.trans (min_le_right _ _)
  have hball : riemannianBallOf ((sliceHistoryR_O3 F s).toHistory.event j).outputMetric
        (B.point j.succ le_rfl (Fin.le_last _)) (20 * (θ' * ρ / 40)) ⊆
      riemannianBallOf ((sliceHistoryR_O3 F s).toHistory.event j).outputMetric
        (B.point j.succ le_rfl (Fin.le_last _)) (20 * (θ' * ρ)) :=
    riemannianBallOf_mono _ _ (by nlinarith [mul_pos hθ' hρ])
  have hsc2 : 9 * (1600 * K) / (θ' * ρ) ^ 2 = 9 * K / (θ' * ρ / 40) ^ 2 := by
    have : θ' * ρ ≠ 0 := (mul_pos hθ' hρ).ne'
    field_simp
    ring
  have hage2 : τ * (θ' * ρ / 40) ^ 2 = τ / 1600 * (θ' * ρ) ^ 2 := by ring
  have hsc' := h s hs T₀ hT₀ hT₀s pp records e1 e2 e3 e4 hmr hacc hord hlink p ρ hρ hρb h2 h3 h4 h5 h6 q hq hno
    θ' hθ' (hθ'H.trans (min_le_left _ _)) (τ / 1600) (by positivity)
    (by have : 9 * (1600 * K) * (τ / 1600) = 9 * K * τ := by ring
        rw [this]; exact hτK)
    j hj B b x hx (hball hmem) (by rw [hsc2]; exact hsc) (by rw [← hage2]; exact hage)
  have ha : θ' / 40 * (40 * Real.sqrt Cb) ≤ 1 := by
    have h1 : θ' / 40 * (40 * Real.sqrt Cb) = θ' * Real.sqrt Cb := by ring
    rw [h1]
    calc θ' * Real.sqrt Cb ≤ 1 / (Real.sqrt Cb + 1) * Real.sqrt Cb :=
          mul_le_mul_of_nonneg_right hle (Real.sqrt_nonneg _)
      _ ≤ 1 := by
          rw [div_mul_eq_mul_div, one_mul, div_le_one hpos]
          linarith
  exact shift_le_of_Cb_S131 hρ hCb.le hsc' (by ring) (by positivity) ha

end GC.LongTime.Ch12
