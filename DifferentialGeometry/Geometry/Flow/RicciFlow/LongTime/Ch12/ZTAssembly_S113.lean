import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedsCore_S96
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.MicroPointwiseAssemblyK_S64
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedsKL84Pinch_O16
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.WindowConstants_CX2

/-!
# CH12-S113, group 1: `hZT_of_kl82_S113` (= `hZT_of_kl82_S96` with the three premises of `[FROZEN v2] CH12-S113`)

`hZT v2` carries (i) `StandardCap.transitionEnd + 3 < Dcap` (before the `∃`, as `hZC`), (ii) `pp.modelAccuracy ≤ ε₀`
with `ε₀` one of the produced constants (absolute in practice: `min (3/4) ε₀'` of `hscale_of_record_S105`), and
(iii) `4 ≤ pp.modelOrder`.  The `hFE` / `hTS` binders get the same premises and one extra produced constant each
(`εF`, `εT`); the output constant is `min εF εT`.  Proof text of S96 otherwise unchanged.
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
variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ}

theorem hZT_of_kl82_S113 (Hp : GC.LongTime.AnalyticSurgeryProfile F δ)
    (_hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε) (Ctime : ℝ≥0) (_hP2 : P2_O2 Hp Ctime)
    (hKL82 : ∀ w : ℝ, 0 < w → ∃ τ₀ K₀ : ℝ, 0 < τ₀ ∧ τ₀ ≤ 1 ∧ 0 < K₀ ∧
      ∀ (H : ObservedHistory.{u}) (top : Icc (0 : ℝ) H.horizon) (x0 : (H.stageAt top).Carrier)
        (r0 τ K : ℝ) (a : Icc (0 : ℝ) H.horizon) (hat : a ≤ top)
        (X : BackwardPointTrace H (H.activeStage a) (H.activeStage top)
          (H.activeStage_mono hat) x0) {Phi : ℝ → ℝ},
        Perelman.AdmissiblePinchingFunction Phi →
        (∀ v : Icc (0 : ℝ) H.horizon, v ≤ top → ∀ x,
          curvatureOperatorLowerBoundAt (H.stageMetric (H.activeStage v) v) x
            (metricAlgebraicCurvatureTensorAt (H.stageMetric (H.activeStage v) v) x)
            (Phi (metricScalarAt (H.stageMetric (H.activeStage v) v) x))) →
        0 < r0 → 0 < τ → τ ≤ τ₀ → (a : ℝ) = top - τ * r0 ^ 2 →
        (∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ top),
          ∀ q ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
              (X.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) r0,
            ∃ A : BackwardPointTrace H (H.activeStage a) (H.activeStage v)
                (H.activeStage_mono hav) q, A.isRmBoundedBy (hat := hav) K) →
        (∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ top),
          ∀ q ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
              (X.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) r0,
            SectionalBoundedBelowAt (H.stageMetric (H.activeStage v) v) q (-(r0 ^ 2)⁻¹)) →
        ENNReal.ofReal (w * r0 ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage top) top) x0 r0 →
        (∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ top),
          (top : ℝ) - 3 / 4 * τ * r0 ^ 2 ≤ v →
          ∀ q ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
              (X.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt))
              (r0 / 4),
            metricScalarAt (H.stageMetric (H.activeStage v) v) q ≤ K₀ * τ⁻¹ * (r0 ^ 2)⁻¹) ∧
        ENNReal.ofReal (w * (r0 / 4) ^ 3 / 10) ≤
          ballVolume (H.stageMetric (H.activeStage a) a)
            (X.point (H.activeStage a) le_rfl (H.activeStage_mono hat)) (r0 / 4))
    (hFE : ∀ w : ℝ, 0 < w → ∀ Λ : ℝ, 1 ≤ Λ → ∀ (θ Dcap C0 : ℝ), 0 < θ → 0 < C0 → StandardCap.transitionEnd + 3 < Dcap →
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
                ballVolume (s.history.stageMetric (s.history.activeStage (sliceTop_S8 s)) s.time) q' ρ'))
    (hTS : ∀ w : ℝ, 0 < w → ∀ Λ : ℝ, 1 ≤ Λ → ∀ (θ Dcap C0 : ℝ), 0 < θ → 0 < C0 → StandardCap.transitionEnd + 3 < Dcap →
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
            (K₀ / (θ' * ρ) ^ 2)) :
    ∀ w : ℝ, 0 < w → ∀ Λ : ℝ, 1 ≤ Λ → ∀ (θ Dcap C0 : ℝ), 0 < θ → 0 < C0 → StandardCap.transitionEnd + 3 < Dcap →
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
              (C / (a * ρ) ^ 2) := by
  intro w hw Λ hΛ θ Dcap C0 hθ hC0 hDcap
  obtain ⟨bF, TF, K, τ₁, τ₂, w₁, θ₁, εF, hbF, hTF, hK, hτ₁, hτ₂, hw₁, hθ₁, hεF, hFEs⟩ :=
    hFE w hw Λ hΛ θ Dcap C0 hθ hC0 hDcap
  obtain ⟨Phi, hPhi, hpin⟩ := hpinchS_O16 Hp
  obtain ⟨a₀, c, c₁, ha₀, hac, hc₁, hcore⟩ := seeds_core_S96 hKL82 hPhi hw₁ hK hτ₁ hτ₂
  have hc : 0 < c := (by positivity : 0 ≤ 2 * a₀ ^ 2).trans_lt hac
  obtain ⟨bS, TS, T₀', ρ₀, K₀, θ₂, εT, hbS, hTS', hT₀', hρ₀, hK₀, hθ₂, hεT, hTSs⟩ :=
    hTS w hw Λ hΛ θ Dcap C0 hθ hC0 hDcap a₀ c₁ ha₀ hc₁
  obtain ⟨b, τ, hb, hτ, hbb₀, hbρ, hτc, hwindow, hexp⟩ :=
    exists_window_constants_CX2 (c := c) (b₀ := min bF bS) (ρ₀ := ρ₀) (K := K₀) hc
      (lt_min hbF hbS) hρ₀ hK₀
  have hbF' : b ≤ bF := hbb₀.trans (min_le_left _ _)
  have hbS' : b ≤ bS := hbb₀.trans (min_le_right _ _)
  set a : ℝ := min θ₁ (min θ₂ 1) with hadef
  have ha : 0 < a := lt_min hθ₁ (lt_min hθ₂ one_pos)
  have haθ₁ : a ≤ θ₁ := min_le_left _ _
  have haθ₂ : a ≤ θ₂ := (min_le_right _ _).trans (min_le_left _ _)
  have ha1 : a ≤ 1 := (min_le_right _ _).trans (min_le_right _ _)
  set T : ℝ := max TF (max TS (2 * T₀')) with hTdef
  refine ⟨b, T, a, τ, K₀, min εF εT, hb, ha, hτ, hK₀, lt_min hεF hεT, ?_⟩
  intro s hs T₀ hT₀a hT₀b pp records h1 h2 h3 h4 hmr hacc hord hlink p ρ hρ hρb hev hnn hsec hvol hR q hq hnc q' hq'
  have hsF : TF ≤ s.time := (le_max_left _ _).trans hs
  have hsS : TS ≤ s.time := ((le_max_left _ _).trans (le_max_right _ _)).trans hs
  have hs2 : 2 * T₀' ≤ s.time := ((le_max_right _ _).trans (le_max_right _ _)).trans hs
  have hTF₀ : TF ≤ T₀ := (le_max_left _ _).trans hT₀a
  have hTS₀ : TS ≤ T₀ := ((le_max_left _ _).trans (le_max_right _ _)).trans hT₀a
  have hρbF : ρ ≤ bF * Real.sqrt s.time :=
    hρb.trans (mul_le_mul_of_nonneg_right hbF' (Real.sqrt_nonneg _))
  have hρbS : ρ ≤ bS * Real.sqrt s.time :=
    hρb.trans (mul_le_mul_of_nonneg_right hbS' (Real.sqrt_nonneg _))
  obtain ⟨a', hat, X, haeq, hTFam, hvolq⟩ := hFEs s hsF T₀ hTF₀ hT₀b pp records h1 h2 h3 h4 hmr (hacc.trans (min_le_left _ _)) hord hlink
    p ρ hρ hρbF hev hnn hsec hvol hR q hq hnc a ha haθ₁ q' hq'
  have har : 0 < a * ρ := mul_pos ha hρ
  have hrb : a * ρ ≤ b * Real.sqrt s.time := by
    have : a * ρ ≤ ρ := (mul_le_mul_of_nonneg_right ha1 hρ.le).trans_eq (one_mul ρ)
    exact this.trans hρb
  refine hTSs s hsS T₀ hTS₀ hT₀b pp records h1 h2 h3 h4 hmr (hacc.trans (min_le_right _ _)) hord hlink
    p ρ hρ hρbS hev hnn hsec hvol hR q hq hnc a ha haθ₂ τ hτ hexp q' hq' ?_ ?_
  · intro v hv
    have hvt : v ≤ sliceTop_S8 s := v.property.2
    have hv' : s.time - c * (a * ρ) ^ 2 ≤ v.val := by
      have hm := mul_le_mul_of_nonneg_right hτc (sq_nonneg (a * ρ))
      linarith
    obtain ⟨yv, _, hsm, hvol', A, hA⟩ :=
      hcore s.history (sliceTop_S8 s) (hpin s) q' (a * ρ) har a' hat X haeq hTFam hvolq v hvt hv'
    exact ⟨yv, hsm, hvol', A, hA⟩
  · intro v hv
    have hvw := window_time_and_radius_CX2 hb hτ hbρ hwindow s.positive har hrb
      (show v.val ∈ Icc (s.time - τ * (a * ρ) ^ 2) s.time from ⟨hv, v.property.2⟩)
    exact ⟨by linarith [hvw.1], hvw.2.2⟩

end GC.LongTime.Ch12
