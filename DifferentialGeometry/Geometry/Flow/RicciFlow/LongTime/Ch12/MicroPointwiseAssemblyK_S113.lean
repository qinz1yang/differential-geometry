import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.MicroWholeBallShi_O13
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.MicroSliceKernelTheta_O13
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.MicroP5Linked_O13

/-!
# CH12-S113 (copy of `hptK_of_Z0_ZT_ZC_S64` whose `hZT` binder is `[FROZEN v2] CH12-S113`: three extra premises, constants `ε₀`; the call to `hP5` is at accuracy `ε₀`, order `4`, and `Dcap := 4 + |transitionEnd|`).  Previous header: CH12-S64 (copy of `hptK_of_Z0_ZT_ZC_S43` whose `hZC` binder carries the `transitionEnd < Dcap` premise of `hZC_S48_shape`; body otherwise verbatim, the call is at `Dcap := 1 + |transitionEnd|`), from CH12-S43 group 1: assembly of the K-indexed pointwise input `hptK` (S44's `hpt` with `∀ K` first)

`hptK_of_Z0_ZT_ZC_S113`: for every `q` in a micro test ball, either `q` is a recent-cap point
(`CAP` of `[FROZEN] CH12-S43 cap-predicate`, verbatim from `micro_slice_scalar_bound_theta_O13`)
and the cap-window jets (input `hZC`, lane S44, `[FROZEN v2] CH12-S44` with the records threshold
`T₀ ∈ [T, s.time]`) apply, or it is not and the traced region (input `hZT`, ZT) applies.  Zero order
`hZ0` is O13's `micro_zero_order_of_kernel_O13` conclusion on the DOUBLED ball.  The common data
`(pp, records)` are the `P5Linked_O13` data, built once per slice as in the proof of
`micro_slice_scalar_bound_theta_O13`.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian Set
open scoped Manifold ContDiff ENNReal NNReal

namespace GC.LongTime.Ch12

universe u

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
  {δ : ℝ → ℝ}

theorem hptK_of_Z0_ZT_ZC_S113 (Hp : GC.LongTime.AnalyticSurgeryProfile F δ) (hP5 : P5Linked_O13 Hp)
    (Ctime : ℝ≥0) (hP2 : P2_O2 Hp Ctime)
    (hZ0 : ∀ w : ℝ, 0 < w → ∀ Λ : ℝ, 1 ≤ Λ → ∃ C₀ T : ℝ, 0 < C₀ ∧
      ∀ s : RegularSlice F.observation, T ≤ s.time →
      ∀ (p : s.stage.Carrier) (ρ : ℝ), 0 < ρ →
        (∃ n, ∃ i : Fin (F.tower.history n).eventCount, ∃ h,
          (F.tower.history n).time i.succ ∈ Icc (s.time / 2) s.time ∧
          ρ < Λ * (Hp.records n i).nominalRadius h) →
        (∃ z ∈ connectedComponent p, ¬ SectionalBoundedBelowAt s.metric z 0) →
        (∀ q ∈ riemannianBallOf s.metric p ρ,
          SectionalBoundedBelowAt s.metric q (-(ρ ^ 2)⁻¹)) →
        ENNReal.ofReal (w * ρ ^ 3) ≤ ballVolume s.metric p ρ →
        ∀ q ∈ riemannianBallOf s.metric p (2 * ρ), metricScalarAt s.metric q ≤ C₀ / ρ ^ 2)
    (hZC : ∀ Ctime' : ℝ≥0, P2_O2 Hp Ctime' → ∃ θ : ℝ, 0 < θ ∧ ∀ Dcap C0 : ℝ, StandardCap.transitionEnd < Dcap → 0 < C0 → ∀ K : ℕ, ∃ (B : ℕ → ℝ) (T : ℝ),
      ∀ s : RegularSlice F.observation, T ≤ s.time → ∀ T₀ : ℝ, T ≤ T₀ → T₀ ≤ s.time →
      ∀ (pp : CutoffParameters)
        (records : ∀ i : Fin (sliceHistoryR_O3 F s).eventCount,
          T₀ - θ ≤ (sliceHistoryR_O3 F s).time i.succ →
          GeometricCutoffRecord (sliceHistoryR_O3 F s).toHistory i pp),
        pp.delta = Hp.parameters.delta → pp.neckRadius = Hp.parameters.neckRadius →
        pp.fixed = Hp.parameters.fixed → pp.recenterConstant = Hp.parameters.recenterConstant →
        32 * (Dcap + 1) + 2 ≤ pp.modelRadius →
        (∀ i hi b, linkedCanonicalWindow_O2 ((records i hi).static b)) →
      ∀ (y : s.stage.Carrier) (ρ : ℝ), 0 < ρ → metricScalarAt s.metric y ≤ C0 / ρ ^ 2 →
        (∃ (j : Fin (sliceHistoryR_O3 F s).eventCount)
            (hj : T₀ - θ ≤ (sliceHistoryR_O3 F s).time j.succ)
            (hl : j.succ ≤ Fin.last (sliceHistoryR_O3 F s).eventCount)
            (B : BackwardPointTrace (sliceHistoryR_O3 F s).toHistory j.succ
              (Fin.last (sliceHistoryR_O3 F s).eventCount) hl y)
            (b : ((sliceHistoryR_O3 F s).toHistory.event j).RetainedBoundaryIndex)
            (x : standardCapWindow pp.modelRadius),
            B.point j.succ le_rfl hl = ((records j hj).static b).window x ∧
              ‖x.val‖ < Dcap + 1 ∧
              s.time - (sliceHistoryR_O3 F s).time j.succ ≤
                θ * (((records j hj).static b).neck.scale)⁻¹) →
          ∀ k : ℕ, k ≤ K → curvatureDerivativeNorm s.metric k y ≤ B k * (ρ ^ (k + 2))⁻¹)
    (hZT : ∀ w : ℝ, 0 < w → ∀ Λ : ℝ, 1 ≤ Λ → ∀ (θ Dcap C0 : ℝ), 0 < θ → 0 < C0 → StandardCap.transitionEnd + 3 < Dcap →
      ∃ (b T a τ C ε₀ : ℝ), 0 < b ∧ 0 < a ∧ 0 < τ ∧ 0 < C ∧ 0 < ε₀ ∧
      ∀ s : RegularSlice F.observation, T ≤ s.time → ∀ T₀ : ℝ, T ≤ T₀ → T₀ ≤ s.time →
      ∀ (pp : CutoffParameters)
        (records : ∀ i : Fin (sliceHistoryR_O3 F s).eventCount,
          T₀ - θ ≤ (sliceHistoryR_O3 F s).time i.succ →
          GeometricCutoffRecord (sliceHistoryR_O3 F s).toHistory i pp),
        pp.delta = Hp.parameters.delta → pp.neckRadius = Hp.parameters.neckRadius →
        pp.fixed = Hp.parameters.fixed → pp.recenterConstant = Hp.parameters.recenterConstant →
        32 * (Dcap + 1) + 2 ≤ pp.modelRadius →
        pp.modelAccuracy ≤ ε₀ → 4 ≤ pp.modelOrder →
        (∀ i hi b, linkedCanonicalWindow_O2 ((records i hi).static b)) →
      ∀ (p : s.stage.Carrier) (ρ : ℝ), 0 < ρ → ρ ≤ b * Real.sqrt s.time →
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
          ∀ q' : (s.history.stageAt (sliceTop_S8 s)).Carrier, HEq q' q →
            s.history.isTracedRegion (sliceTop_S8 s) q' (2 * (a * ρ)) (τ * (a * ρ) ^ 2)
              (C / (a * ρ) ^ 2)) :
    ∀ w : ℝ, 0 < w → ∀ Λ : ℝ, 1 ≤ Λ → ∀ K : ℕ, ∃ (b T a τ C : ℝ) (B : ℕ → ℝ),
      0 < b ∧ 0 < a ∧ 0 < τ ∧ 0 < C ∧
      ∀ s : RegularSlice F.observation, T ≤ s.time →
      ∀ (p : s.stage.Carrier) (ρ : ℝ), 0 < ρ → ρ ≤ b * Real.sqrt s.time →
        (∃ n, ∃ i : Fin (F.tower.history n).eventCount, ∃ h,
          (F.tower.history n).time i.succ ∈ Icc (s.time / 2) s.time ∧
          ρ < Λ * (Hp.records n i).nominalRadius h) →
        (∃ z ∈ connectedComponent p, ¬ SectionalBoundedBelowAt s.metric z 0) →
        (∀ q ∈ riemannianBallOf s.metric p ρ,
          SectionalBoundedBelowAt s.metric q (-(ρ ^ 2)⁻¹)) →
        ENNReal.ofReal (w * ρ ^ 3) ≤ ballVolume s.metric p ρ →
        ∀ q ∈ riemannianBallOf s.metric p ρ,
          (∀ q' : (s.history.stageAt (sliceTop_S8 s)).Carrier, HEq q' q →
            s.history.isTracedRegion (sliceTop_S8 s) q' (2 * (a * ρ)) (τ * (a * ρ) ^ 2)
              (C / (a * ρ) ^ 2)) ∨
          ∀ k : ℕ, k ≤ K → curvatureDerivativeNorm s.metric k q ≤ B k * (ρ ^ (k + 2))⁻¹ := by
  intro w hw Λ hΛ K
  obtain ⟨C₀, Tz, hC₀, hz⟩ := hZ0 w hw Λ hΛ
  obtain ⟨θ, hθ, hC⟩ := hZC Ctime hP2
  set Dcap : ℝ := 4 + |StandardCap.transitionEnd| with hDcap
  have hDcap3 : StandardCap.transitionEnd + 3 < Dcap := by
    rw [hDcap]; linarith [le_abs_self StandardCap.transitionEnd]
  have hDcapT : StandardCap.transitionEnd < Dcap := by linarith
  obtain ⟨B, T₂, hCs⟩ := hC Dcap C₀ hDcapT hC₀ K
  obtain ⟨b, T₁, a, τ, C, ε₀, hb, ha, hτ, hCp, hε₀, hT⟩ := hZT w hw Λ hΛ θ Dcap C₀ hθ hC₀ hDcap3
  obtain ⟨T₅, hT₅⟩ := hP5 (32 * (Dcap + 1) + 2) ε₀ 4 hε₀
  refine ⟨b, max (max (max T₁ T₂) Tz) (T₅ + θ), a, τ, C, B, hb, ha, hτ, hCp, ?_⟩
  intro s hs p ρ hρ hρb hmic hneg hsec hvol q hq
  have hT₁ : T₁ ≤ s.time := (le_max_left _ _).trans ((le_max_left _ _).trans ((le_max_left _ _).trans hs))
  have hT₂ : T₂ ≤ s.time := (le_max_right _ _).trans ((le_max_left _ _).trans ((le_max_left _ _).trans hs))
  have hTz : Tz ≤ s.time := (le_max_right _ _).trans ((le_max_left _ _).trans hs)
  have hz0 := hz s hTz p ρ hρ hmic hneg hsec hvol
  obtain ⟨pp, hδp, hnp, hfp, hrc, hDp, hacc, hord, recs, hlin⟩ := hT₅ (sliceIndexR_O3 F s)
  let H₀ := F.tower.history (sliceIndexR_O3 F s)
  let k := sliceStageR_O3 F s
  let T₀ : ℝ := max (max T₁ T₂) (T₅ + θ)
  let records : ∀ i : Fin (sliceHistoryR_O3 F s).eventCount,
      T₀ - θ ≤ (sliceHistoryR_O3 F s).time i.succ →
      GeometricCutoffRecord (sliceHistoryR_O3 F s).toHistory i pp := fun i hi =>
    H₀.geometricCutoffRecordOfPrefix k
      (recs (Fin.castLE (Nat.le_of_lt_succ k.isLt) i) (by
        have h1 : T₅ ≤ T₀ - θ := by
          have := le_max_right (max T₁ T₂) (T₅ + θ)
          change T₅ ≤ max (max T₁ T₂) (T₅ + θ) - θ
          linarith
        exact h1.trans hi))
  have hlin' : ∀ i hi b, linkedCanonicalWindow_O2 ((records i hi).static b) :=
    fun i hi b => hlin _ _ b
  have hT₀₁ : T₁ ≤ T₀ := (le_max_left _ _).trans (le_max_left _ _)
  have hT₀₂ : T₂ ≤ T₀ := (le_max_right _ _).trans (le_max_left _ _)
  have hT₀s : T₀ ≤ s.time := (le_trans (max_le_max (le_max_left _ _) le_rfl) hs)
  by_cases hcap : (∃ (j : Fin (sliceHistoryR_O3 F s).eventCount)
            (hj : T₀ - θ ≤ (sliceHistoryR_O3 F s).time j.succ)
            (hl : j.succ ≤ Fin.last (sliceHistoryR_O3 F s).eventCount)
            (B : BackwardPointTrace (sliceHistoryR_O3 F s).toHistory j.succ
              (Fin.last (sliceHistoryR_O3 F s).eventCount) hl q)
            (b : ((sliceHistoryR_O3 F s).toHistory.event j).RetainedBoundaryIndex)
            (x : standardCapWindow pp.modelRadius),
            B.point j.succ le_rfl hl = ((records j hj).static b).window x ∧
              ‖x.val‖ < Dcap + 1 ∧
              s.time - (sliceHistoryR_O3 F s).time j.succ ≤
                θ * (((records j hj).static b).neck.scale)⁻¹)
  · refine Or.inr (fun k' hk' => ?_)
    refine hCs s hT₂ T₀ hT₀₂ hT₀s pp records hδp hnp hfp hrc hDp hlin' q ρ hρ ?_ hcap k' hk'
    exact hz0 q (lt_of_lt_of_le hq (ENNReal.ofReal_le_ofReal (by linarith)))
  · exact Or.inl (hT s hT₁ T₀ hT₀₁ hT₀s pp records hδp hnp hfp hrc hDp hacc hord hlin' p ρ hρ hρb
      hmic hneg hsec hvol hz0 q hq hcap)

end GC.LongTime.Ch12
