import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6ClosureFinalSlabMainP6M
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6AnchorFinalSlabP6M
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6ClosureMainP6M

/-!
# P6 收口（final-slab 情形）：anchor 消去 + pinching ⇐ `Pre841`（O-CH11-P6ANCH G3g，后缀 `_P6M`）

`false_of_selection_finalSlab_slice_P6M` 的基点 anchor `hanchor0` 由 adapter-q
`hanchor0_of_closure_data_window_q_P6M`（与 slab 无关；`H n := (K n).prefixAt (Fin.last _)`、`G n` = final
slab incoming 形、`s n := horizon`，阈值 `q = 4R`、`Cq = 4`）给出，其 U 侧 / 窗口前提：
* `hW` ⇐ `hW_final_P6M`、`hgrad` ⇐ `hgrad_final_P6M`（selection，`Cgrad = C2'`）；
* 窗口 `hnc` ⇐ `hnc_window_final_P6M`（`Pre841` κ，`κ := d.kappa`、`ρ := ρnc`），`hρ` ⇐ `hradii`。
唯一新增：小性条件 `ε ≤ coneAccuracy`。主形 `false_of_selection_finalSlab_main_P6M` 再把 pinching 三项
（`Phi`、`hPhi`、`hpinchK`）由 `exists_tracedPinching_of_pre841_P6M`（与 slab 无关）给出。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold NNReal Topology ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open Perelman.CanonicalNeighborhood.FiniteHorn (SpatialCanonicalWitness)

namespace ObservedHistory

/-- **P6 收口（final-slab，K-route，anchor 消去）**：显式前提 = 数据前提（P6D2 G3 逐字，final slab 形）+
`Pre841` + `hctrl` + `hpinchK` + selection 输出 + `hwin` + 相对 `hdist` + 切片二分 `hslice`；
SLT / anchor 前提全部消去。 -/
theorem false_of_selection_finalSlab_final_P6M :
    ∃ η₃ Cup Lc : ℝ, 0 < η₃ ∧ 0 < Cup ∧ 0 < Lc ∧
    ∃ epsW : ℝ, 0 < epsW ∧ ∀ ε : ℝ, 0 < ε → ε < 1 / 11 → ε ≤ epsW →
    ε ≤ crossingWindowNeckAccuracy.{u} → ε ≤ crossingNeckAccuracy.{u} → ε ≤ coneAccuracy →
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {C1' C2' : ℝ} {Ctime' : ℝ≥0}, C ≤ C1' → C ≤ C2' → C.toNNReal ≤ Ctime' →
      ∀ {P₀ : OrientedThreeStage.{u}} {g₀ : P₀.Metric} {Ctime : ℝ≥0} {phi : ℝ → ℝ},
      (hphi : Perelman.AdmissiblePinchingFunction phi) →
      {K : ℕ → RetainedCoreHistory.{u}} → {t : ℕ → ℝ} →
      (htl : ∀ n, (K n).time (Fin.last (K n).eventCount) < t n) →
      (htK : ∀ n, t n < (K n).horizon) →
      {G : ∀ n, ((K n).stage (Fin.last (K n).eventCount)).IncomingSlab
        ((K n).time (Fin.last (K n).eventCount)) (K n).horizon} →
      (hG : ∀ n, G n = ((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
        ((htl n).trans (htK n)) le_rfl) →
      {D θcap qcan : ℕ → ℝ} → {p₀ p : ℕ → CutoffParameters} → {δb ρb : ℕ → ℝ} →
      {records : ∀ n i, GeometricCutoffRecord
        ((K n).prefixAt (Fin.last (K n).eventCount)).toHistory i (p n)} →
      {yG : ∀ n, ((K n).stage (Fin.last (K n).eventCount)).Carrier} →
      (hinit : ∀ n, Nonempty (InitialIdentification P₀ g₀
        ((K n).prefixAt (Fin.last (K n).eventCount)).toHistory)) →
      (hrec : ∀ n, ((K n).prefixAt (Fin.last (K n).eventCount)).IsCanonicalCutoffRecordFamily
        (p₀ n) (δb n) (ρb n) (records n)) →
      (hqcan : ∀ n : ℕ, (n : ℝ) + 1 ≤ qcan n) →
      (hpar : ∀ n : ℕ, (p₀ n).modelAccuracy ≤ 1 / ((n : ℝ) + 1) ∧ (n : ℝ) + 1 ≤ D n ∧
        D n ≤ (p₀ n).modelRadius ∧ n + 2 ≤ (p₀ n).modelOrder ∧ δb n ≤ 1 / ((n : ℝ) + 1)) →
      (hscale : ∀ (n : ℕ) i b, ((n : ℝ) + 1) * qcan n ≤ ((records n i).static b).neck.scale) →
      (hθcap : ∀ n : ℕ, 1 - 1 / ((n : ℝ) + 2) ≤ θcap n) →
      (hpinch : ∀ n, ((K n).prefixAt (Fin.last (K n).eventCount)).EventSlabsPinched phi ∧
        Perelman.PhiAlmostNonnegative (G n).flow
          (Ico ((K n).time (Fin.last (K n).eventCount)) (K n).horizon) phi) →
      (hslab : ∀ n, ((K n).prefixAt (Fin.last (K n).eventCount)).EventSlabsDerivative Ctime
        (qcan n) (Fin.last ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount)) →
      (hderG : ∀ n, (G n).DerivativeBoundBefore (2 * Ctime) (2 * qcan n) (t n)) →
      (hqR : ∀ n, qcan n < (G n).flow.scalar (t n) (yG n)) →
      (hnot : ∀ n, ¬ ((K n).prefixAt (Fin.last (K n).eventCount)).CapWindowPoint (records n)
        (Fin.last ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount) (yG n) (t n) (D n)
        (θcap n)) →
      (hRt : Tendsto (fun n => (G n).flow.scalar (t n) (yG n) * t n) atTop atTop) →
      (Kh : ℕ → ObservedHistory.{u}) → (hKh : Kh = fun n => (K n).toHistory) →
      (σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon) → (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) →
      (R : ℕ → ℝ) → (hσ : ∀ n, (σ n : ℝ) = t n) → (hyG : ∀ n, HEq (y n) (yG n)) →
      (hRn : ∀ n, R n = (G n).flow.scalar (t n) (yG n)) →
      {r₀ : ℝ} → (hr₀ : 0 < r₀) → (hRpos : ∀ n, 0 < R n) →
      (d : GC.LongTime.Ch11.Pre841Data_C11K Kh σ y R hRpos) →
      (hctrl : ∀ᶠ n in atTop,
        (Kh n).isParabolicallyRmControlledBall (σ n) (y n) (r₀ / Real.sqrt (R n))) →
      {Phi : ℝ → ℝ} → (hPhi : Perelman.AdmissiblePinchingFunction Phi) →
      (hpinchK : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (σ n : ℝ) - T / R n ≤ v →
        ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvt) x,
          curvatureOperatorLowerBoundAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt))
            (metricAlgebraicCurvatureTensorAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)))
            (Phi (metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt))))) →
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
    false_of_selection_finalSlab_slice_P6M.{u}
  refine ⟨η₃, Cup, Lc, hη₃, hCup, hLc, epsW, hepsW, fun ε hε hsmall hεW hεX hεN hεcone => ?_⟩
  obtain ⟨C, hC, hB'⟩ := hB ε hε hsmall hεW hεX hεN
  refine ⟨C, hC, fun {C1' C2' Ctime'} hC1 hC2 hCt => ?_⟩
  intro P₀ g₀ Ctime phi hphi K t htl htK G hG D θcap qcan p₀ p δb ρb records yG hinit hrec hqcan
    hpar hscale hθcap hpinch hslab hderG hqR hnot hRt Kh hKh σ y R hσ hyG hRn r₀ hr₀ hRpos d hctrl
    Phi hPhi hpinchK Tn aSeed haT hsT has pT seedTrace L hL hgood hwin hdist hslice hsel
  obtain ⟨ρnc, hradii, hkappa⟩ := exists_tracedKappa_of_kseq_P6D2 d.volume_ge
  subst hKh
  have hfin : ∀ n, (K n).time (Fin.last (K n).eventCount) < (K n).horizon :=
    fun n => (htl n).trans (htK n)
  have hC20 : 0 ≤ C2' := (zero_le_one.trans hC).trans hC2
  have hnc := hnc_window_final_P6M hfin hG htl σ hσ y yG hyG R hRpos hRn d.kappa_pos ρnc hkappa
  have hρ : Tendsto (fun n => ρnc n * Real.sqrt ((G n).flow.scalar (t n) (yG n))) atTop atTop :=
    hradii.congr fun n => by rw [hRn n]
  have hW := hW_final_P6M hfin hG htl σ hσ y yG hyG R hRpos hRn Tn aSeed haT hsT has pT
    seedTrace L hL hgood
  have hgrad := hgrad_final_P6M hC20 hfin hG htl σ hσ y yG hyG R hRpos hRn Tn aSeed haT hsT
    has pT seedTrace L hL hgood hwin hdist
  have hq2 : ∀ n, 2 * qcan n ≤ 4 * R n := fun n => by
    have h1 := hqR n
    have h2 := hqcan n
    have h3 : (0 : ℝ) ≤ n := n.cast_nonneg
    rw [hRn n]
    linarith
  have hqC : ∀ n, 4 * R n ≤ 4 * (G n).flow.scalar (t n) (yG n) := fun n => by
    rw [hRn n]
  have hanchor0 := RetainedCoreHistory.hanchor0_of_closure_data_window_q_P6M
    (H := fun n => (K n).prefixAt (Fin.last (K n).eventCount)) (G := G)
    (s := fun n => (K n).horizon) (y := yG) (ρ := ρnc) hεcone d.kappa_pos hphi
    (fun n => (K n).prefixAt_time_last _)
    (fun n => by rw [hG n]; exact (K n).final_initial (hfin n)) hrec hqcan hpar
    hθcap hpinch hslab htl htK hderG hqR hnot hRt (Cq := 4) (fun n => 4 * R n) hq2 hqC hW hgrad
    hnc hρ
  exact hB' hC1 hC2 hCt hphi htl htK hG hinit hrec hqcan hpar hscale hθcap hpinch hslab hderG hqR
    hnot hRt hanchor0 (fun n => (K n).toHistory) rfl σ y R hσ hyG hRn hr₀ hRpos d hctrl hPhi
    hpinchK Tn aSeed haT hsT has pT seedTrace L hL hgood hwin hdist hslice hsel

/-- **P6 收口主形（final-slab，K-route）**：`false_of_selection_finalSlab_final_P6M` 中 pinching 三项
（`Phi`、`hPhi`、`hpinchK`）由 `Pre841` 给出（`exists_tracedPinching_of_pre841_P6M`）。 -/
theorem false_of_selection_finalSlab_main_P6M :
    ∃ η₃ Cup Lc : ℝ, 0 < η₃ ∧ 0 < Cup ∧ 0 < Lc ∧
    ∃ epsW : ℝ, 0 < epsW ∧ ∀ ε : ℝ, 0 < ε → ε < 1 / 11 → ε ≤ epsW →
    ε ≤ crossingWindowNeckAccuracy.{u} → ε ≤ crossingNeckAccuracy.{u} → ε ≤ coneAccuracy →
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {C1' C2' : ℝ} {Ctime' : ℝ≥0}, C ≤ C1' → C ≤ C2' → C.toNNReal ≤ Ctime' →
      ∀ {P₀ : OrientedThreeStage.{u}} {g₀ : P₀.Metric} {Ctime : ℝ≥0} {phi : ℝ → ℝ},
      (hphi : Perelman.AdmissiblePinchingFunction phi) →
      {K : ℕ → RetainedCoreHistory.{u}} → {t : ℕ → ℝ} →
      (htl : ∀ n, (K n).time (Fin.last (K n).eventCount) < t n) →
      (htK : ∀ n, t n < (K n).horizon) →
      {G : ∀ n, ((K n).stage (Fin.last (K n).eventCount)).IncomingSlab
        ((K n).time (Fin.last (K n).eventCount)) (K n).horizon} →
      (hG : ∀ n, G n = ((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
        ((htl n).trans (htK n)) le_rfl) →
      {D θcap qcan : ℕ → ℝ} → {p₀ p : ℕ → CutoffParameters} → {δb ρb : ℕ → ℝ} →
      {records : ∀ n i, GeometricCutoffRecord
        ((K n).prefixAt (Fin.last (K n).eventCount)).toHistory i (p n)} →
      {yG : ∀ n, ((K n).stage (Fin.last (K n).eventCount)).Carrier} →
      (hinit : ∀ n, Nonempty (InitialIdentification P₀ g₀
        ((K n).prefixAt (Fin.last (K n).eventCount)).toHistory)) →
      (hrec : ∀ n, ((K n).prefixAt (Fin.last (K n).eventCount)).IsCanonicalCutoffRecordFamily
        (p₀ n) (δb n) (ρb n) (records n)) →
      (hqcan : ∀ n : ℕ, (n : ℝ) + 1 ≤ qcan n) →
      (hpar : ∀ n : ℕ, (p₀ n).modelAccuracy ≤ 1 / ((n : ℝ) + 1) ∧ (n : ℝ) + 1 ≤ D n ∧
        D n ≤ (p₀ n).modelRadius ∧ n + 2 ≤ (p₀ n).modelOrder ∧ δb n ≤ 1 / ((n : ℝ) + 1)) →
      (hscale : ∀ (n : ℕ) i b, ((n : ℝ) + 1) * qcan n ≤ ((records n i).static b).neck.scale) →
      (hθcap : ∀ n : ℕ, 1 - 1 / ((n : ℝ) + 2) ≤ θcap n) →
      (hpinch : ∀ n, ((K n).prefixAt (Fin.last (K n).eventCount)).EventSlabsPinched phi ∧
        Perelman.PhiAlmostNonnegative (G n).flow
          (Ico ((K n).time (Fin.last (K n).eventCount)) (K n).horizon) phi) →
      (hslab : ∀ n, ((K n).prefixAt (Fin.last (K n).eventCount)).EventSlabsDerivative Ctime
        (qcan n) (Fin.last ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount)) →
      (hderG : ∀ n, (G n).DerivativeBoundBefore (2 * Ctime) (2 * qcan n) (t n)) →
      (hqR : ∀ n, qcan n < (G n).flow.scalar (t n) (yG n)) →
      (hnot : ∀ n, ¬ ((K n).prefixAt (Fin.last (K n).eventCount)).CapWindowPoint (records n)
        (Fin.last ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount) (yG n) (t n) (D n)
        (θcap n)) →
      (hRt : Tendsto (fun n => (G n).flow.scalar (t n) (yG n) * t n) atTop atTop) →
      (Kh : ℕ → ObservedHistory.{u}) → (hKh : Kh = fun n => (K n).toHistory) →
      (σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon) → (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) →
      (R : ℕ → ℝ) → (hσ : ∀ n, (σ n : ℝ) = t n) → (hyG : ∀ n, HEq (y n) (yG n)) →
      (hRn : ∀ n, R n = (G n).flow.scalar (t n) (yG n)) →
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
    false_of_selection_finalSlab_final_P6M.{u}
  refine ⟨η₃, Cup, Lc, hη₃, hCup, hLc, epsW, hepsW,
    fun ε hε hsmall hεW hεX hεN hεcone => ?_⟩
  obtain ⟨C, hC, hB'⟩ := hB ε hε hsmall hεW hεX hεN hεcone
  refine ⟨C, hC, fun {C1' C2' Ctime'} hC1 hC2 hCt => ?_⟩
  intro P₀ g₀ Ctime phi hphi K t htl htK G hG D θcap qcan p₀ p δb ρb records yG hinit hrec hqcan
    hpar hscale hθcap hpinch hslab hderG hqR hnot hRt Kh hKh σ y R hσ hyG hRn r₀ hr₀ hRpos d hctrl
    Tn aSeed haT hsT has pT seedTrace L hL hgood hwin hdist hslice hsel
  obtain ⟨Phi, hPhi, hpinchK⟩ := exists_tracedPinching_of_pre841_P6M d
  exact hB' hC1 hC2 hCt hphi htl htK hG hinit hrec hqcan hpar hscale hθcap hpinch hslab hderG hqR
    hnot hRt Kh hKh σ y R hσ hyG hRn hr₀ hRpos d hctrl hPhi hpinchK Tn aSeed haT hsT has pT
    seedTrace L hL hgood hwin hdist hslice hsel

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
