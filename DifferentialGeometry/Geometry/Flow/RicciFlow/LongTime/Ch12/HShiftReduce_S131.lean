import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HTSAssembly_S113

/-!
# CH12-S131: reduction of the birth shift `hshift` of `hTS_S113` to the K-free cap-scale bound `hbirth`

`hshift_of_hbirth_S131`: if young caps whose window meets the `20 θ'ρ`-ball of the trace point at a low-scalar
point (the exact `hshift` hypotheses) satisfy `neck.scale ≤ Cb / ρ²` (the S77 "`h_j ≥ ρ/√Cb`" step; `Cb` independent of
`θ'`), then `hshift` holds with `θH' := min θH (1 / (40 √Cb + 1))`.  The binder `hbirth` is NOT proved here (it needs a
forward-persistence argument for the cap point, F-S106-3); this file only discharges the numerics, so the producer of
`hshift` is reduced to `hbirth`.
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

/-- `q ≤ Cb / ρ²`, `r = a ρ`, `a (40 √Cb) ≤ 1` give `40 r √q ≤ 1`. -/
theorem shift_le_of_Cb_S131 {q ρ r a Cb : ℝ} (hρ : 0 < ρ) (hCb : 0 ≤ Cb)
    (hq : q ≤ Cb / ρ ^ 2) (hr : r = a * ρ) (ha : 0 ≤ a) (ha' : a * (40 * Real.sqrt Cb) ≤ 1) :
    40 * r * Real.sqrt q ≤ 1 := by
  have hsq : Real.sqrt q ≤ Real.sqrt Cb / ρ := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    rw [div_pow, Real.sq_sqrt hCb]
    exact hq
  have h1 : 40 * r * Real.sqrt q ≤ 40 * r * (Real.sqrt Cb / ρ) :=
    mul_le_mul_of_nonneg_left hsq (by rw [hr]; positivity)
  refine h1.trans ?_
  rw [hr]
  have : 40 * (a * ρ) * (Real.sqrt Cb / ρ) = a * (40 * Real.sqrt Cb) := by
    field_simp
  rw [this]
  exact ha'

variable {δ : ℝ → ℝ}

theorem hshift_of_hbirth_S131 {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
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
                (B.point j.succ le_rfl (Fin.le_last _)) (20 * (θ' * ρ)) →
            metricScalarAt ((sliceHistoryR_O3 F s).toHistory.event j).outputMetric
              (((records j hj).static b).window x) ≤ 9 * K / (θ' * ρ) ^ 2 →
            s.time - (sliceHistoryR_O3 F s).time j.succ < τ * (θ' * ρ) ^ 2 →
            40 * (θ' * ρ) * Real.sqrt ((records j hj).static b).neck.scale ≤ 1 := by
  intro w hw Λ hΛ θ Dcap C0 hθ hC0 hD K hK
  obtain ⟨Cb, bH, TH, θH, εH, hCb, hb, hθH, hεH, h⟩ := hbirth w hw Λ hΛ θ Dcap C0 hθ hC0 hD K hK
  have hpos : 0 < 40 * Real.sqrt Cb + 1 := by positivity
  refine ⟨bH, TH, min θH (1 / (40 * Real.sqrt Cb + 1)), εH, hb, lt_min hθH (by positivity), hεH, ?_⟩
  intro s hs T₀ hT₀ hT₀s pp records e1 e2 e3 e4 hmr hacc hord hlink p ρ hρ hρb h2 h3 h4 h5 h6 q hq hno
    θ' hθ' hθ'H τ hτ hτK j hj B b x hx hmem hsc hage
  have hle : θ' ≤ 1 / (40 * Real.sqrt Cb + 1) := hθ'H.trans (min_le_right _ _)
  have hsc' := h s hs T₀ hT₀ hT₀s pp records e1 e2 e3 e4 hmr hacc hord hlink p ρ hρ hρb h2 h3 h4 h5 h6 q hq hno
    θ' hθ' (hθ'H.trans (min_le_left _ _)) τ hτ hτK j hj B b x hx hmem hsc hage
  refine shift_le_of_Cb_S131 hρ hCb.le hsc' rfl hθ'.le ?_
  calc θ' * (40 * Real.sqrt Cb) ≤ 1 / (40 * Real.sqrt Cb + 1) * (40 * Real.sqrt Cb) :=
        mul_le_mul_of_nonneg_right hle (by positivity)
    _ ≤ 1 := by
        rw [div_mul_eq_mul_div, one_mul, div_le_one hpos]
        linarith

end GC.LongTime.Ch12
