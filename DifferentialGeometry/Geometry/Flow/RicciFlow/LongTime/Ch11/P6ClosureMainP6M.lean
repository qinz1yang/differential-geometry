import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6ClosureFinalP6M
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6PinchingP6A

/-!
# `Pre841` ⇒ trace-local pinching；P6 收口主形（O-CH11-P6ANCH G4b，后缀 `_P6M`）

`false_of_selection_eventSlab_final_P6M`（G1y）的 `Phi` / `hPhi` / `hpinchK` 由同一个 `Pre841` 包的
native pinching（fixed Hamilton–Ivey，年龄 `pinchingShift + t`）给出：
`exists_tracedPinching_of_pre841_P6M`（树内
`exists_admissiblePinchingFunction_neg_le_of_fixedHamiltonIveyRegion`，`a₀ := pinchingShift`；
`(R, 2ν) ∈ region` ⇒ `-ν ≤ Φ R` 分 `ν` 的符号）。
主形 `false_of_selection_eventSlab_main_P6M`：显式前提 = 数据前提 + `Pre841` + `hctrl` + selection 输出 +
`hwin` + 相对 `hdist` + `hslice` + slab 位置。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Curvature.DimensionThree
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold NNReal Topology ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open Perelman.CanonicalNeighborhood.FiniteHorn (SpatialCanonicalWitness)

namespace ObservedHistory

/-- **`_P6M`（`Pre841` ⇒ trace-local pinching）**：`Pre841` native pinching（fixed Hamilton–Ivey，年龄
`pinchingShift + t ≥ pinchingShift`）+ 树内
`exists_admissiblePinchingFunction_neg_le_of_fixedHamiltonIveyRegion`（`a₀ := pinchingShift`）
⇒ 一个 admissible `Φ`，P6D G2 / G5c 形的 trace-local 曲率算子下界（处处成立，
故对任意 `D T` 平凡 eventually）。 -/
theorem exists_tracedPinching_of_pre841_P6M {H : ℕ → ObservedHistory.{u}}
    {t : ∀ n, Icc (0 : ℝ) (H n).horizon} {y : ∀ n, ((H n).stageAt (t n)).Carrier} {R : ℕ → ℝ}
    {hR : ∀ n, 0 < R n} (d : GC.LongTime.Ch11.Pre841Data_C11K H t y R hR) :
    ∃ Phi : ℝ → ℝ, Perelman.AdmissiblePinchingFunction Phi ∧
      ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((H n).stageMetric ((H n).activeStage (t n)) (t n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (H n).horizon) (hvt : v ≤ t n), (t n : ℝ) - T / R n ≤ v →
        ∀ tr : BackwardPointTrace (H n) ((H n).activeStage v) ((H n).activeStage (t n))
          ((H n).activeStage_mono hvt) x,
          curvatureOperatorLowerBoundAt ((H n).stageMetric ((H n).activeStage v) v)
            (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt))
            (metricAlgebraicCurvatureTensorAt ((H n).stageMetric ((H n).activeStage v) v)
              (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt)))
            (Phi (metricScalarAt ((H n).stageMetric ((H n).activeStage v) v)
              (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt)))) := by
  obtain ⟨Phi, hPhi, hbound⟩ :=
    Perelman.exists_admissiblePinchingFunction_neg_le_of_fixedHamiltonIveyRegion
      d.native.pinchingShift_pos
  refine ⟨Phi, hPhi, fun D T _ _ => Eventually.of_forall fun n x _ v hvt _ tr => ?_⟩
  have hfixed := d.native.pinching n v
    (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt))
  have hpair := (inFixedHamiltonIveyRegion_iff_mem_fixedHamiltonIveyRegion _ _ _).mp hfixed
  have hage : d.native.pinchingShift ≤ d.native.pinchingShift + (v : ℝ) :=
    le_add_of_nonneg_right v.2.1
  have h2 := hbound _ hage _ _ hpair
  have hpos := hPhi.pos (metricScalarAt ((H n).stageMetric ((H n).activeStage v) v)
    (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt)))
  obtain ⟨basis, horth⟩ := exists_orthonormalBasisAt ((H n).stageMetric ((H n).activeStage v) v)
    (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt)) (by
      change Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3
      simp)
  apply (curvatureOperatorLowerBoundAt_iff_neg_leastCurvatureOperatorEigenvalueAt_le
    basis horth).mpr
  rcases le_or_gt 0 (leastCurvatureOperatorEigenvalueAt ((H n).stageMetric ((H n).activeStage v) v)
      (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt))
      (metricAlgebraicCurvatureTensorAt ((H n).stageMetric ((H n).activeStage v) v)
        (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt)))) with h | h
  · linarith
  · linarith

/-- **P6 收口主形（event-slab，K-route）**：`false_of_selection_eventSlab_final_P6M` 中 pinching 三项
（`Phi`、`hPhi`、`hpinchK`）由 `Pre841` 给出。 -/
theorem false_of_selection_eventSlab_main_P6M :
    ∃ η₃ Cup Lc : ℝ, 0 < η₃ ∧ 0 < Cup ∧ 0 < Lc ∧
    ∃ epsW : ℝ, 0 < epsW ∧ ∀ ε : ℝ, 0 < ε → ε < 1 / 11 → ε ≤ epsW →
    ε ≤ crossingWindowNeckAccuracy.{u} → ε ≤ crossingNeckAccuracy.{u} → ε ≤ coneAccuracy →
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {C1' C2' : ℝ} {Ctime' : ℝ≥0}, C ≤ C1' → C ≤ C2' → C.toNNReal ≤ Ctime' →
      ∀ {P₀ : OrientedThreeStage.{u}} {g₀ : P₀.Metric} {Ctime : ℝ≥0} {phi : ℝ → ℝ},
      (hphi : Perelman.AdmissiblePinchingFunction phi) →
      {K : ℕ → RetainedCoreHistory.{u}} → {j : ∀ n, Fin (K n).eventCount} → {t : ℕ → ℝ} →
      (hjt : ∀ n, (K n).time (j n).castSucc < t n) → (htj : ∀ n, t n < (K n).time (j n).succ) →
      {D θcap qcan : ℕ → ℝ} → {p₀ p : ℕ → CutoffParameters} → {δb ρb : ℕ → ℝ} →
      {records : ∀ n i, GeometricCutoffRecord ((K n).prefixAt (j n).castSucc).toHistory i (p n)} →
      {yG : ∀ n, ((K n).stage (j n).castSucc).Carrier} →
      (hinit : ∀ n, Nonempty (InitialIdentification P₀ g₀
        ((K n).prefixAt (j n).castSucc).toHistory)) →
      (hrec : ∀ n, ((K n).prefixAt (j n).castSucc).IsCanonicalCutoffRecordFamily (p₀ n) (δb n)
        (ρb n) (records n)) →
      (hqcan : ∀ n : ℕ, (n : ℝ) + 1 ≤ qcan n) →
      (hpar : ∀ n : ℕ, (p₀ n).modelAccuracy ≤ 1 / ((n : ℝ) + 1) ∧ (n : ℝ) + 1 ≤ D n ∧
        D n ≤ (p₀ n).modelRadius ∧ n + 2 ≤ (p₀ n).modelOrder ∧ δb n ≤ 1 / ((n : ℝ) + 1)) →
      (hscale : ∀ (n : ℕ) i b, ((n : ℝ) + 1) * qcan n ≤ ((records n i).static b).neck.scale) →
      (hθcap : ∀ n : ℕ, 1 - 1 / ((n : ℝ) + 2) ≤ θcap n) →
      (hpinch : ∀ n, ((K n).prefixAt (j n).castSucc).EventSlabsPinched phi ∧
        Perelman.PhiAlmostNonnegative ((K n).toHistory.event (j n)).incoming.flow
          (Ico ((K n).time (j n).castSucc) ((K n).time (j n).succ)) phi) →
      (hslab : ∀ n, ((K n).prefixAt (j n).castSucc).EventSlabsDerivative Ctime (qcan n)
        (Fin.last ((K n).prefixAt (j n).castSucc).eventCount)) →
      (hderG : ∀ n, ((K n).toHistory.event (j n)).incoming.DerivativeBoundBefore (2 * Ctime)
        (2 * qcan n) (t n)) →
      (hqR : ∀ n, qcan n < ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n)) →
      (hnot : ∀ n, ¬ ((K n).prefixAt (j n).castSucc).CapWindowPoint (records n)
        (Fin.last ((K n).prefixAt (j n).castSucc).eventCount) (yG n) (t n) (D n) (θcap n)) →
      (hRt : Tendsto (fun n => ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n) *
        t n) atTop atTop) →
      (Kh : ℕ → ObservedHistory.{u}) → (hKh : Kh = fun n => (K n).toHistory) →
      (σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon) → (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) →
      (R : ℕ → ℝ) → (hσ : ∀ n, (σ n : ℝ) = t n) → (hyG : ∀ n, HEq (y n) (yG n)) →
      (hRn : ∀ n, R n = ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n)) →
      {r₀ : ℝ} → (hr₀ : 0 < r₀) → (hRpos : ∀ n, 0 < R n) →
      (d : GC.LongTime.Ch11.Pre841Data_C11K Kh σ y R hRpos) →
      (hctrl : ∀ᶠ n in atTop,
        (Kh n).isParabolicallyRmControlledBall (σ n) (y n) (r₀ / Real.sqrt (R n))) →
      (Tn aSeed : ∀ n, Icc (0 : ℝ) (Kh n).horizon) → (haT : ∀ n, aSeed n ≤ Tn n) →
      (hsT : ∀ n, σ n ≤ Tn n) → (has : ∀ n, aSeed n ≤ σ n) →
      (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier) →
      (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
        ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n)) →
      (L : ℕ → ℝ) → (hL : Tendsto L atTop atTop) →
      (hgood : ∀ n, ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
        (σ n : ℝ) - L n ^ 2 / R n ≤ (v : ℝ) →
        ∀ z : ((Kh n).stageAt v).Carrier,
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
              ((seedTrace n).point ((Kh n).activeStage v) ((Kh n).activeStage_mono hav)
                ((Kh n).activeStage_mono (hvs.trans (hsT n)))) z ≤
            riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
                ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                  ((Kh n).activeStage_mono (hsT n))) (y n) +
              ENNReal.ofReal (L n / Real.sqrt (R n)) →
          4 * R n ≤ metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v) z →
          (Kh n).HasSpatialCanonicalTimeControl ε C1' C2' Ctime' v z) →
      (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n) →
      (hdist : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
          (σ n : ℝ) - T / R n ≤ v →
        ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
            ((Kh n).activeStage_mono hvs) x,
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
              ((seedTrace n).point ((Kh n).activeStage v) ((Kh n).activeStage_mono hav)
                ((Kh n).activeStage_mono (hvs.trans (hsT n))))
              (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvs)) ≤
            riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
                ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                  ((Kh n).activeStage_mono (hsT n))) (y n) +
              ENNReal.ofReal (L n / Real.sqrt (R n))) →
      (hslice : ∀ A Dd : ℝ, 1 ≤ A → 0 < Dd → ∃ QB Dcap D₂ : ℝ, 0 ≤ QB ∧
        Dcap + 1 + (2 * Dd * Lc * Real.sqrt (2 * A) + 1) ≤ D₂ ∧
        ∀ σ' : ℝ, σ' < 0 → ∀ Dw : ℝ, 0 < Dw → ∀ᶠ n in atTop,
        ∀ x₁ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (Dw / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (v : ℝ) = σ n + σ' / R n →
        ∀ tr₁ : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
            ((Kh n).activeStage_mono hvt) x₁,
          metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
            (tr₁.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) ≤ A * R n →
          ∃ CWP : ((Kh n).stage ((Kh n).activeStage v)).Carrier → Prop,
            (∀ w, riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
                (tr₁.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) w <
                ENNReal.ofReal (Dd / Real.sqrt (R n)) → ¬ CWP w →
              R n ≤ metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v) w → ∀ x,
              riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v) w x <
                ENNReal.ofReal ((2 * Dd * Real.sqrt A + 1) /
                  Real.sqrt (metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v) w)) →
              metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v) x ≤
                QB * metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v) w) ∧
            (∀ w, riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
                (tr₁.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) w <
                ENNReal.ofReal (Dd / Real.sqrt (R n)) → CWP w →
              ∃ (Ξ : standardCapWindow D₂ → ((Kh n).stage ((Kh n).activeStage v)).Carrier)
                (hΞ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ξ) (z₀ : standardCapWindow D₂),
                Injective Ξ ∧ Ξ z₀ = w ∧ ‖z₀.val‖ < Dcap + 1 ∧
                ∃ (lam : ℝ) (hlam : 0 < lam) (Q : StandardSolution) (τw : ℝ),
                  τw ∈ Icc (0 : ℝ) (1 / 2) ∧
                  ∀ (u : standardCapWindow D₂) (m : ℕ), m ≤ 2 →
                    metricDerivNorm m (localPullMetric (scaleMetric lam hlam
                        ((Kh n).stageMetric ((Kh n).activeStage v) v)) Ξ hΞ)
                      ((Q.val.metric τw).restrictOpen (standardCapWindow D₂))
                      (StandardCap.metric.restrictOpen (standardCapWindow D₂)) u < η₃)) →
      (hsel : ∀ n, ¬ (Kh n).HasSpatialCanonicalTimeControl ε C1' C2' Ctime' (σ n) (y n)) →
      False := by
  obtain ⟨η₃, Cup, Lc, hη₃, hCup, hLc, epsW, hepsW, hB⟩ :=
    false_of_selection_eventSlab_final_P6M.{u}
  refine ⟨η₃, Cup, Lc, hη₃, hCup, hLc, epsW, hepsW,
    fun ε hε hsmall hεW hεX hεN hεcone => ?_⟩
  obtain ⟨C, hC, hB'⟩ := hB ε hε hsmall hεW hεX hεN hεcone
  refine ⟨C, hC, fun {C1' C2' Ctime'} hC1 hC2 hCt => ?_⟩
  intro P₀ g₀ Ctime phi hphi K j t hjt htj D θcap qcan p₀ p δb ρb records yG hinit hrec hqcan hpar
    hscale hθcap hpinch hslab hderG hqR hnot hRt Kh hKh σ y R hσ hyG hRn r₀ hr₀ hRpos d hctrl Tn
    aSeed haT hsT has pT seedTrace L hL hgood hwin hdist hslice hsel
  obtain ⟨Phi, hPhi, hpinchK⟩ := exists_tracedPinching_of_pre841_P6M d
  exact hB' hC1 hC2 hCt hphi hjt htj hinit hrec hqcan hpar hscale hθcap hpinch hslab hderG hqR hnot
    hRt Kh hKh σ y R hσ hyG hRn hr₀ hRpos d hctrl hPhi hpinchK Tn aSeed haT hsT has pT seedTrace L
    hL hgood hwin hdist hslice hsel

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
