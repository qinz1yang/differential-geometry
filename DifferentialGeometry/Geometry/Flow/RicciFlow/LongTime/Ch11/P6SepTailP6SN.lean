import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SepTnP6SN

/-!
# (SEP′) / (CWS) 的 eventually 版 ⇒ 主形：尾子列重套（S-CH11-SEPTN G2，后缀 `_P6SN`）

`sepK_eventually_of_smallness_P6CD` / `sepK_eventually_of_smallAtTn_P6SN` 只给 (SEP′) `hsepK` 体的
**eventually** 版（需要 `n` 足够大才有 `Tn/2 ≤ tᵢ`、`Tn ≥ Tε`）；(CWS) 的 diagonal 包（G3）里
`hbirthA : 1 ≤ a₀·scale` 在 P6SEL3 G5 也只是 eventually。closed 主形 `hsepK` / `hcws` 却是 `∀ n`。

* **`false_of_selection_eventSlab_late_closed_residual_cond_ev_P6SN`**：
  `false_of_selection_eventSlab_late_closed_residual_cond_P6CD` 的 binder 逐字，仅 `hcws`、`hsepK`
  由 `∀ n` 改 `∀ᶠ n in atTop`。证明：取共同尾起点 `N`，对子列 `n ↦ n + N` 重新应用 P6CD 主形——
  其余数据逐项平移；依赖 `n` 的主形 binder（`hacc 1/(n+1)`、`hrad n+1`、`hord n+2`、`hδF 1/(n+1)`、
  `hscaleK`、`hqR`、`hcws` 的 `‖x‖ < n+2` 与年龄 `1 − 1/(n+2)`）在 `n ↦ m + N`（`m+N ≥ m`）下**只变强**，故
  平移后仍成立；`d` 用 `Pre841Data_C11K.comp`。
* `hsepK_forall_of_eventually_P6SN`：`hsepK` 体的 eventually 版 ⇒ 存在 `N`，平移数据 `n ↦ m + N` 上
  `∀ m` 版（即 P6CD 主形 `hsepK` binder 对尾子列逐字成立）。
* consumer `example`：P6CD 残余形（`∀ n`）由 ev 形推出；`false_of_…_native_P6SN`：`hsepWK`、`hsepK` 换成
  native 输入（`hnomId`、`hsel4`、(DLT) `hδK`、`hlate`、`0 < η`；经 G1 `tendsto_Tn_atTop_P6SN` 与
  P6CD G3 `sepWK_of_smallness_P6CD` / `sepK_eventually_of_smallness_P6CD`）。
由 build-logs/scratch/S-CH11-SEPTN/mk_g2.py 生成。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open Perelman.CanonicalNeighborhood.FiniteHorn (SpatialCanonicalWitness)

namespace ObservedHistory

/-- **closed 主形残余形，条件化，(CWS) / (SEP′) eventually 版（`_P6SN`）**：见文件头。 -/
theorem false_of_selection_eventSlab_late_closed_residual_cond_ev_P6SN :
    ∃ epsW : ℝ, 0 < epsW ∧ ∀ ε : ℝ, 0 < ε → ε < 1 / 11 → ε ≤ epsW →
    ε ≤ crossingWindowNeckAccuracy.{u} → ε ≤ crossingNeckAccuracy.{u} → ε ≤ coneAccuracy →
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {C1' C2' : ℝ} {Ctime' : ℝ≥0}, C ≤ C1' → C ≤ C2' → C.toNNReal ≤ Ctime' →
      ∀ {Ctime : ℝ≥0} {phi : ℝ → ℝ}, (hphi : Perelman.AdmissiblePinchingFunction phi) →
      {K : ℕ → RetainedCoreHistory.{u}} → {j : ∀ n, Fin (K n).eventCount} → {t : ℕ → ℝ} →
      (hjt : ∀ n, (K n).time (j n).castSucc < t n) → (htj : ∀ n, t n < (K n).time (j n).succ) →
      {Q T₀ : ℕ → ℝ} → {p pF : ℕ → CutoffParameters} →
      {recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
        GeometricCutoffRecord (K n).toHistory i (p n)} →
      (recordsF : ∀ n i, GeometricCutoffRecord (K n).toHistory i (pF n)) →
      {yG : ∀ n, ((K n).stage (j n).castSucc).Carrier} →
      {a₀ : ℝ} → (ha₀ : 0 < a₀) →
      (hHI : ∀ n x, InFixedHamiltonIveyRegion ((K n).initialMetric 0) a₀ x ∧
        -3 / a₀ ≤ metricScalarAt ((K n).initialMetric 0) x) →
      (hcanK : ∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow) →
      (hδF : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
        (pF n).delta ((K n).time i.succ) ≤ 1 / ((n : ℝ) + 1)) →
      (hacc : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1)) →
      (hrad : ∀ n : ℕ, (n : ℝ) + 1 ≤ (p n).modelRadius) →
      (hord : ∀ n : ℕ, n + 2 ≤ (p n).modelOrder) →
      (hscaleK : ∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max ((n : ℝ) + 1) (Q n) ≤
        ((recordsK n i hi).static b).neck.scale) →
      (hpinchK0 : ∀ n, (K n).EventSlabsPinched phi) →
      (hslabK : ∀ n, (K n).EventSlabsDerivative Ctime (Q n) (Fin.last (K n).eventCount)) →
      (hqR : ∀ n : ℕ, max ((n : ℝ) + 1) (Q n) <
        ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n)) →
      {η : ℝ} →
      (hcws : ∀ᶠ n in atTop, ∀ (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ)
        (hl : i.succ ≤ (j n).castSucc) (z : ((K n).stage (j n).castSucc).Carrier)
        (A : BackwardPointTrace (K n).toHistory i.succ (j n).castSucc hl z)
        (b : ((K n).toHistory.event i).RetainedBoundaryIndex)
        (x : standardCapWindow (p n).modelRadius),
        A.point i.succ le_rfl hl = ((recordsK n i hi).static b).window x →
        ‖x.val‖ < ((n : ℝ) + 1) + 1 →
        t n - (K n).time i.succ ≤
          (1 - 1 / ((n : ℝ) + 2)) * (((recordsK n i hi).static b).neck.scale)⁻¹ →
        η * ((recordsK n i hi).static b).neck.scale ≤
          ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) z) →
      (Kh : ℕ → ObservedHistory.{u}) → (hKh : Kh = fun n => (K n).toHistory) →
      (σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon) → (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) →
      (R : ℕ → ℝ) → (hσ : ∀ n, (σ n : ℝ) = t n) → (hyG : ∀ n, HEq (y n) (yG n)) →
      (hRn : ∀ n, R n = ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n)) →
      (hRpos : ∀ n, 0 < R n) →
      (d : GC.LongTime.Ch11.Pre841Data_C11K Kh σ y R hRpos) →
      (hT₀ : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤ (σ n : ℝ) - B / R n) →
      (Tn aSeed : ∀ n, Icc (0 : ℝ) (Kh n).horizon) → (haT : ∀ n, aSeed n ≤ Tn n) →
      (hsT : ∀ n, σ n ≤ Tn n) → (has : ∀ n, aSeed n ≤ σ n) →
      (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier) →
      (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
        ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n)) →
      (L : ℕ → ℝ) → (hL : Tendsto L atTop atTop) →
      (Cg : ℝ) → (hCg : 2 ≤ Cg) →
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
          Cg * R n ≤ metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v) z →
          (Kh n).HasSpatialCanonicalTimeControl ε C1' C2' Ctime' v z) →
      (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n) →
      {κ Aκ : ℝ} → (hκ : 0 < κ) → (r ρV : ℕ → ℝ) →
      (hρV : Tendsto (fun n => ρV n * Real.sqrt (R n)) atTop atTop) →
      (hroom : ∀ n, (Tn n : ℝ) - r n ^ 2 / 2 ≤ σ n - L n ^ 2 / R n) →
      (htime : ∀ n, 2 * r n ^ 2 < (Tn n : ℝ)) →
      (hsmallS : ∀ n, GC.LongTime.hasSmallParabolicCurvature (Kh n) (Tn n) (pT n) (r n)) →
      (hclock : ∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - r n ^ 2) →
      (hsepWK : ∀ T : ℝ, 0 < T → ∀ C : ℝ, 0 ≤ C → ∀ᶠ n in atTop,
        ∀ (i : Fin (K n).eventCount) (_hij : i.val < (j n).val) (hi : T₀ n ≤ (K n).time i.succ) b,
          (σ n : ℝ) - T / R n < (K n).time i.succ →
          2 * max (3 / (r n / 100) ^ 2) (C * R n) < ((recordsK n i hi).static b).neck.scale) →
      (hdistW : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
          (σ n : ℝ) - T / R n ≤ v →
          (Kh n).activeStage v = (Kh n).activeStage (σ n) →
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
      (hsepK : ∀ᶠ n in atTop, ∀ (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ)
        (b : ((K n).toHistory.event i).RetainedBoundaryIndex),
        i.succ ≤ (j n).castSucc →
        t n - (K n).time i.succ ≤ (((recordsK n i hi).static b).neck.scale)⁻¹ →
        R n < η * ((recordsK n i hi).static b).neck.scale) →
      (hr : ∀ n, 0 < r n) → (A : ℝ) → (hA : 0 < A) → (hAκ : A + 3 ≤ Aκ) → (R0 : ℕ → ℝ) →
      (hR0 : ∀ n, 0 < R0 n) → (hR0R : ∀ n, R0 n ≤ R n) →
      (hLdef : ∀ n, L n = Real.sqrt (R0 n * r n ^ 2) / 4) →
      (hdiv : Tendsto (fun n => R0 n * r n ^ 2) atTop atTop) →
      (hball : ∀ n, y n ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
        ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
          ((Kh n).activeStage_mono (hsT n))) ((A + 1) * r n)) →
      (hκR : ∀ᶠ n in atTop, ∀ (j : Fin (Kh n).eventCount) (c : ((Kh n).stage j.castSucc).Carrier)
        (U : Set ((Kh n).stage j.castSucc).Carrier) (a t ρU : ℝ),
        (Tn n : ℝ) - r n ^ 2 / 2 ≤ a → t ≤ (Tn n : ℝ) →
        (∀ (τ : Icc (0 : ℝ) (Kh n).horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
          (Kh n).time j.castSucc < τ → (τ : ℝ) < (Kh n).time j.succ →
          ∀ z ∈ U, ∀ zz cc : ((Kh n).stageAt τ).Carrier, HEq zz z → HEq cc c →
            riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ) cc zz <
              ENNReal.ofReal ρU) →
        (∀ (τ : Icc (0 : ℝ) (Kh n).horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
          (Kh n).time j.castSucc < τ → (τ : ℝ) < (Kh n).time j.succ →
          ∀ (hav : aSeed n ≤ τ) (hvt : τ ≤ Tn n), ∀ cc : ((Kh n).stageAt τ).Carrier, HEq cc c →
            riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ)
                ((seedTrace n).point ((Kh n).activeStage τ) ((Kh n).activeStage_mono hav)
                  ((Kh n).activeStage_mono hvt)) cc + ENNReal.ofReal ρU ≤
              ENNReal.ofReal (Aκ * r n)) →
        ∀ (τ : Icc (0 : ℝ) (Kh n).horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
          (Kh n).time j.castSucc < τ → (τ : ℝ) < (Kh n).time j.succ →
          ∀ z ∈ U, ∀ zz : ((Kh n).stageAt τ).Carrier, HEq zz z →
          ∀ b : ℝ, 0 < b → b ≤ ρV n → (Kh n).isParabolicallyRmControlledBall τ zz b →
            ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
              riemannianVolumeMeasure ThreeModel ((Kh n).stageAt τ).Carrier
                ((Kh n).stageMetric ((Kh n).activeStage τ) τ)
                (riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ) zz b)) →
      (hclosG : ∀ Rad B σ₁ σ₂ : ℝ, σ₁ ≤ σ₂ → σ₂ < 0 → ∀ Dw Dd : ℝ, 0 < Dw → 0 < Dd →
        ∀ᶠ n in atTop,
        ∀ (j' : Fin (Kh n).eventCount) (v : ℝ), (Kh n).time j'.castSucc < v →
          v < (Kh n).time j'.succ → (σ n : ℝ) + σ₁ / R n ≤ v → v ≤ σ n + σ₂ / R n →
        ∀ x₁ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (Dw / Real.sqrt (R n)),
        ∀ (hjσ : j'.castSucc ≤ (Kh n).activeStage (σ n))
          (tr : BackwardPointTrace (Kh n) j'.castSucc ((Kh n).activeStage (σ n)) hjσ x₁),
        ∀ (h1 : (Kh n).activeStage (aSeed n) ≤ j'.castSucc)
          (h2 : j'.castSucc ≤ (Kh n).activeStage (Tn n)) (w : ((Kh n).stage j'.castSucc).Carrier),
          riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric v)
              ((seedTrace n).point j'.castSucc h1 h2) w ≤
            riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
                ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                  ((Kh n).activeStage_mono (hsT n))) (y n) +
              ENNReal.ofReal (L n / 2 / Real.sqrt (R n)) →
          riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric v)
              (tr.point j'.castSucc le_rfl hjσ) w < ENNReal.ofReal (Dd / Real.sqrt (R n)) →
          R n ≤ ((Kh n).event j').incoming.flow.scalar v w →
          ∀ x ∈ riemannianBallOf (((Kh n).event j').incoming.flow.base.metric v) w
              (Rad / Real.sqrt (((Kh n).event j').incoming.flow.scalar v w)),
          ∀ τ : ℝ, v - B / ((Kh n).event j').incoming.flow.scalar v w ≤ τ → τ ≤ v →
            (Kh n).time j'.castSucc < τ →
            riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric τ)
                ((seedTrace n).point j'.castSucc h1 h2) x ≤
              riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
                  ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                    ((Kh n).activeStage_mono (hsT n))) (y n) +
                ENNReal.ofReal (L n / Real.sqrt (R n))) →
      (hsel : ∀ n, ¬ (Kh n).HasSpatialCanonicalTimeControl ε C1' C2' Ctime' (σ n) (y n)) →
      False := by
  obtain ⟨epsW, hepsW, hB⟩ := false_of_selection_eventSlab_late_closed_residual_cond_P6CD.{u}
  refine ⟨epsW, hepsW, fun ε hε hsmall hεW hεX hεN hεcone => ?_⟩
  obtain ⟨C, hC, hB'⟩ := hB ε hε hsmall hεW hεX hεN hεcone
  refine ⟨C, hC, fun {C1' C2' Ctime'} hC1 hC2 hCt => ?_⟩
  intro Ctime phi hphi K j t hjt htj Q T₀ p pF recordsK recordsF yG a₀ ha₀ hHI hcanK hδF hacc hrad
    hord hscaleK hpinchK0 hslabK hqR η hcws Kh hKh σ y R hσ hyG hRn hRpos d hT₀ Tn aSeed haT hsT has
    pT seedTrace L hL Cg hCg hgood hwin κ Aκ hκ r ρV hρV hroom htime hsmallS hclock hsepWK
    hdistW hsepK hr A hA hAκ R0 hR0 hR0R hLdef hdiv hball hκR hclosG hsel
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (hcws.and hsepK)
  subst hKh
  have hψ : Tendsto (fun m : ℕ => m + N) atTop atTop := tendsto_add_atTop_nat N
  have hle : ∀ m : ℕ, (m : ℝ) + 1 ≤ ((m + N : ℕ) : ℝ) + 1 := fun m => by
    push_cast
    linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  have hinv : ∀ m : ℕ, 1 / (((m + N : ℕ) : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) := fun m =>
    one_div_le_one_div_of_le (by positivity) (hle m)
  exact @hB' C1' C2' Ctime' hC1 hC2 hCt Ctime phi hphi
    (fun m => K (m + N)) (fun m => j (m + N)) (fun m => t (m + N))
    (fun m => hjt (m + N)) (fun m => htj (m + N))
    (fun m => Q (m + N)) (fun m => T₀ (m + N)) (fun m => p (m + N)) (fun m => pF (m + N))
    (fun m => recordsK (m + N)) (fun m => recordsF (m + N)) (fun m => yG (m + N)) a₀ ha₀
    (fun m => hHI (m + N)) (fun m => hcanK (m + N))
    (fun m i hi => (hδF (m + N) i hi).trans (hinv m))
    (fun m => (hacc (m + N)).trans (hinv m))
    (fun m => (hle m).trans (hrad (m + N)))
    (fun m => (Nat.add_le_add_right (Nat.le_add_right m N) 2).trans (hord (m + N)))
    (fun m i hi b => le_trans (mul_le_mul (hle m) (max_le_max (hle m) le_rfl)
      (le_trans (by positivity) (le_max_left _ _)) (by positivity)) (hscaleK (m + N) i hi b))
    (fun m => hpinchK0 (m + N)) (fun m => hslabK (m + N))
    (fun m => lt_of_le_of_lt (max_le_max (hle m) le_rfl) (hqR (m + N)))
    η
    (fun m i hi hl z A' b x hx hxn hage =>
      (hN (m + N) (Nat.le_add_left N m)).1 i hi hl z A' b x hx
        (hxn.trans_le (by linarith [hle m]))
        (hage.trans (mul_le_mul_of_nonneg_right
          (by
            have h2 : (1 : ℝ) / (((m + N : ℕ) : ℝ) + 2) ≤ 1 / ((m : ℝ) + 2) :=
              one_div_le_one_div_of_le (by positivity)
                (by push_cast; linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)])
            linarith)
          (inv_nonneg.2 ((recordsK (m + N) i hi).static b).neck.scale_pos.le))))
    (fun m => (K (m + N)).toHistory) rfl (fun m => σ (m + N)) (fun m => y (m + N))
    (fun m => R (m + N)) (fun m => hσ (m + N)) (fun m => hyG (m + N)) (fun m => hRn (m + N))
    (fun m => hRpos (m + N)) (d.comp (fun m => m + N) hψ)
    (fun B => hψ.eventually (hT₀ B)) (fun m => Tn (m + N)) (fun m => aSeed (m + N))
    (fun m => haT (m + N)) (fun m => hsT (m + N)) (fun m => has (m + N)) (fun m => pT (m + N))
    (fun m => seedTrace (m + N)) (fun m => L (m + N))
    ((tendsto_add_atTop_iff_nat (f := L) N).2 hL) Cg hCg (fun m => hgood (m + N))
    (fun T hT => hψ.eventually (hwin T hT)) κ Aκ hκ (fun m => r (m + N)) (fun m => ρV (m + N))
    ((tendsto_add_atTop_iff_nat (f := fun n => ρV n * Real.sqrt (R n)) N).2 hρV)
    (fun m => hroom (m + N)) (fun m => htime (m + N)) (fun m => hsmallS (m + N))
    (fun m => hclock (m + N))
    (fun T hT C hC => hψ.eventually (hsepWK T hT C hC))
    (fun D T hD hT => hψ.eventually (hdistW D T hD hT))
    (fun m i hi b => (hN (m + N) (Nat.le_add_left N m)).2 i hi b)
    (fun m => hr (m + N)) A hA hAκ (fun m => R0 (m + N)) (fun m => hR0 (m + N))
    (fun m => hR0R (m + N)) (fun m => hLdef (m + N))
    ((tendsto_add_atTop_iff_nat (f := fun n => R0 n * r n ^ 2) N).2 hdiv)
    (fun m => hball (m + N)) (hψ.eventually hκR)
    (fun Rad B σ₁ σ₂ h12 h2 Dw Dd hDw hDd => hψ.eventually (hclosG Rad B σ₁ σ₂ h12 h2 Dw Dd hDw
        hDd))
    (fun m => hsel (m + N))

/-- **`hsepK` 的 eventually ⇒ 尾子列上的 `∀ m` 版（`_P6SN`）**：存在 `N`，对平移数据 `n ↦ m + N` 的
`hsepK` 体（P6CD 主形 `hsepK` binder 逐字，数据换成 `K (m+N)` 等）对所有 `m` 成立。 -/
theorem hsepK_forall_of_eventually_P6SN {K : ℕ → RetainedCoreHistory.{u}}
    {j : ∀ n, Fin (K n).eventCount} {t R T₀ : ℕ → ℝ} {p : ℕ → CutoffParameters}
    {recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (p n)} {η : ℝ}
    (hev : ∀ᶠ n in atTop, ∀ (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ)
      (b : ((K n).toHistory.event i).RetainedBoundaryIndex),
      i.succ ≤ (j n).castSucc →
      t n - (K n).time i.succ ≤ (((recordsK n i hi).static b).neck.scale)⁻¹ →
      R n < η * ((recordsK n i hi).static b).neck.scale) :
    ∃ N : ℕ, ∀ (m : ℕ) (i : Fin (K (m + N)).eventCount) (hi : T₀ (m + N) ≤ (K (m + N)).time i.succ)
      (b : ((K (m + N)).toHistory.event i).RetainedBoundaryIndex),
      i.succ ≤ (j (m + N)).castSucc →
      t (m + N) - (K (m + N)).time i.succ ≤ (((recordsK (m + N) i hi).static b).neck.scale)⁻¹ →
      R (m + N) < η * ((recordsK (m + N) i hi).static b).neck.scale := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hev
  exact ⟨N, fun m => hN (m + N) (Nat.le_add_left N m)⟩

/-- consumer（旧 ⇐ 新）：P6CD 残余形（`hcws`、`hsepK` 为 `∀ n`）由 ev 形推出——`∀ n ⇒ ∀ᶠ n`。 -/
example : type_of% @false_of_selection_eventSlab_late_closed_residual_cond_P6CD.{u} := by
  obtain ⟨epsW, hepsW, hB⟩ := false_of_selection_eventSlab_late_closed_residual_cond_ev_P6SN.{u}
  refine ⟨epsW, hepsW, fun ε hε hsmall hεW hεX hεN hεcone => ?_⟩
  obtain ⟨C, hC, hB'⟩ := hB ε hε hsmall hεW hεX hεN hεcone
  refine ⟨C, hC, fun {C1' C2' Ctime'} hC1 hC2 hCt => ?_⟩
  intro Ctime phi hphi K j t hjt htj Q T₀ p pF recordsK recordsF yG a₀ ha₀ hHI hcanK hδF hacc hrad
    hord hscaleK hpinchK0 hslabK hqR η hcws Kh hKh σ y R hσ hyG hRn hRpos d hT₀ Tn aSeed haT hsT has
    pT seedTrace L hL Cg hCg hgood hwin κ Aκ hκ r ρV hρV hroom htime hsmallS hclock hsepWK
    hdistW hsepK hr A hA hAκ R0 hR0 hR0R hLdef hdiv hball hκR hclosG hsel
  exact hB' hC1 hC2 hCt hphi hjt htj recordsF ha₀ hHI hcanK hδF hacc hrad hord hscaleK hpinchK0
    hslabK hqR (Filter.Eventually.of_forall hcws) Kh hKh σ y R hσ hyG hRn hRpos d hT₀ Tn aSeed haT
    hsT has pT seedTrace L hL Cg hCg hgood hwin hκ r ρV hρV hroom htime hsmallS hclock hsepWK hdistW
    (Filter.Eventually.of_forall hsepK) hr A hA hAκ R0 hR0 hR0R hLdef hdiv hball hκR hclosG hsel

/-- **closed 主形残余形，(SEP) / (SEP′) 换成 native 输入（`_P6SN`）**：ev 形的 `hsepWK`、`hsepK` 删去，
换 `hlate`（`Tn ≥ n+1`，G1）、`0 < η`、`hsel4`（selector ④，`ρ = d.native.params`）、(DLT) `hδK`、
neck 识别 `hnomId`；`Kh := (K n).toHistory`。残余显式义务：(CWS) `hcws`（eventually）、(TR₀) `hdistW`、
以及这些 native / 识别输入。 -/
theorem false_of_selection_eventSlab_late_closed_residual_cond_native_P6SN :
    ∃ epsW : ℝ, 0 < epsW ∧ ∀ ε : ℝ, 0 < ε → ε < 1 / 11 → ε ≤ epsW →
    ε ≤ crossingWindowNeckAccuracy.{u} → ε ≤ crossingNeckAccuracy.{u} → ε ≤ coneAccuracy →
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {C1' C2' : ℝ} {Ctime' : ℝ≥0}, C ≤ C1' → C ≤ C2' → C.toNNReal ≤ Ctime' →
      ∀ {Ctime : ℝ≥0} {phi : ℝ → ℝ}, (hphi : Perelman.AdmissiblePinchingFunction phi) →
      {K : ℕ → RetainedCoreHistory.{u}} → {j : ∀ n, Fin (K n).eventCount} → {t : ℕ → ℝ} →
      (hjt : ∀ n, (K n).time (j n).castSucc < t n) → (htj : ∀ n, t n < (K n).time (j n).succ) →
      {Q T₀ : ℕ → ℝ} → {p pF : ℕ → CutoffParameters} →
      {recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
        GeometricCutoffRecord (K n).toHistory i (p n)} →
      (recordsF : ∀ n i, GeometricCutoffRecord (K n).toHistory i (pF n)) →
      {yG : ∀ n, ((K n).stage (j n).castSucc).Carrier} →
      {a₀ : ℝ} → (ha₀ : 0 < a₀) →
      (hHI : ∀ n x, InFixedHamiltonIveyRegion ((K n).initialMetric 0) a₀ x ∧
        -3 / a₀ ≤ metricScalarAt ((K n).initialMetric 0) x) →
      (hcanK : ∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow) →
      (hδF : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
        (pF n).delta ((K n).time i.succ) ≤ 1 / ((n : ℝ) + 1)) →
      (hacc : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1)) →
      (hrad : ∀ n : ℕ, (n : ℝ) + 1 ≤ (p n).modelRadius) →
      (hord : ∀ n : ℕ, n + 2 ≤ (p n).modelOrder) →
      (hscaleK : ∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max ((n : ℝ) + 1) (Q n) ≤
        ((recordsK n i hi).static b).neck.scale) →
      (hpinchK0 : ∀ n, (K n).EventSlabsPinched phi) →
      (hslabK : ∀ n, (K n).EventSlabsDerivative Ctime (Q n) (Fin.last (K n).eventCount)) →
      (hqR : ∀ n : ℕ, max ((n : ℝ) + 1) (Q n) <
        ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n)) →
      {η : ℝ} →
      (hcws : ∀ᶠ n in atTop, ∀ (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ)
        (hl : i.succ ≤ (j n).castSucc) (z : ((K n).stage (j n).castSucc).Carrier)
        (A : BackwardPointTrace (K n).toHistory i.succ (j n).castSucc hl z)
        (b : ((K n).toHistory.event i).RetainedBoundaryIndex)
        (x : standardCapWindow (p n).modelRadius),
        A.point i.succ le_rfl hl = ((recordsK n i hi).static b).window x →
        ‖x.val‖ < ((n : ℝ) + 1) + 1 →
        t n - (K n).time i.succ ≤
          (1 - 1 / ((n : ℝ) + 2)) * (((recordsK n i hi).static b).neck.scale)⁻¹ →
        η * ((recordsK n i hi).static b).neck.scale ≤
          ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) z) →
      (σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon) → (y : ∀ n, ((K n).toHistory.stageAt (σ
          n)).Carrier) →
      (R : ℕ → ℝ) → (hσ : ∀ n, (σ n : ℝ) = t n) → (hyG : ∀ n, HEq (y n) (yG n)) →
      (hRn : ∀ n, R n = ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n)) →
      (hRpos : ∀ n, 0 < R n) →
      (d : GC.LongTime.Ch11.Pre841Data_C11K (fun n => (K n).toHistory) σ y R hRpos) →
      (hT₀ : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤ (σ n : ℝ) - B / R n) →
      (Tn aSeed : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon) → (haT : ∀ n, aSeed n ≤ Tn n) →
      (hsT : ∀ n, σ n ≤ Tn n) → (has : ∀ n, aSeed n ≤ σ n) →
      (pT : ∀ n, ((K n).toHistory.stageAt (Tn n)).Carrier) →
      (seedTrace : ∀ n, BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage (aSeed n))
        ((K n).toHistory.activeStage (Tn n)) ((K n).toHistory.activeStage_mono (haT n)) (pT n)) →
      (L : ℕ → ℝ) → (hL : Tendsto L atTop atTop) →
      (Cg : ℝ) → (hCg : 2 ≤ Cg) →
      (hgood : ∀ n, ∀ (v : Icc (0 : ℝ) (K n).toHistory.horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
        (σ n : ℝ) - L n ^ 2 / R n ≤ (v : ℝ) →
        ∀ z : ((K n).toHistory.stageAt v).Carrier,
          riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
              ((seedTrace n).point ((K n).toHistory.activeStage v) ((K
                  n).toHistory.activeStage_mono hav)
                ((K n).toHistory.activeStage_mono (hvs.trans (hsT n)))) z ≤
            riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ
                n))
                ((seedTrace n).point ((K n).toHistory.activeStage (σ n)) ((K
                    n).toHistory.activeStage_mono (has n))
                  ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
              ENNReal.ofReal (L n / Real.sqrt (R n)) →
          Cg * R n ≤ metricScalarAt ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v)
              v) z →
          (K n).toHistory.HasSpatialCanonicalTimeControl ε C1' C2' Ctime' v z) →
      (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n) →
      {κ Aκ : ℝ} → (hκ : 0 < κ) → (r ρV : ℕ → ℝ) →
      (hρV : Tendsto (fun n => ρV n * Real.sqrt (R n)) atTop atTop) →
      (hroom : ∀ n, (Tn n : ℝ) - r n ^ 2 / 2 ≤ σ n - L n ^ 2 / R n) →
      (htime : ∀ n, 2 * r n ^ 2 < (Tn n : ℝ)) →
      (hsmallS : ∀ n, GC.LongTime.hasSmallParabolicCurvature (K n).toHistory (Tn n) (pT n) (r n)) →
      (hclock : ∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - r n ^ 2) →
      (hlate : ∀ n : ℕ, (n : ℝ) + 1 ≤ (Tn n : ℝ)) → (hη : 0 < η) →
      (hsel4 : ∀ n, R n ≤ (d.native.params.neckRadius (Tn n) ^ 2)⁻¹) →
      (hδK : ∃ Tδ : ℝ, ∀ (n : ℕ) (τ : ℝ), Tδ ≤ τ →
        (p n).recenterConstant * (p n).delta τ ≤ 1 / 2) →
      (hnomId : ∀ n (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ) h,
        (recordsK n i hi).nominalRadius h = (d.native.records n i).nominalRadius h) →
      (hdistW : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ
            n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (K n).toHistory.horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
          (σ n : ℝ) - T / R n ≤ v →
          (K n).toHistory.activeStage v = (K n).toHistory.activeStage (σ n) →
        ∀ tr : BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage v) ((K
            n).toHistory.activeStage (σ n))
            ((K n).toHistory.activeStage_mono hvs) x,
          riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
              ((seedTrace n).point ((K n).toHistory.activeStage v) ((K
                  n).toHistory.activeStage_mono hav)
                ((K n).toHistory.activeStage_mono (hvs.trans (hsT n))))
              (tr.point ((K n).toHistory.activeStage v) le_rfl ((K n).toHistory.activeStage_mono
                  hvs)) ≤
            riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ
                n))
                ((seedTrace n).point ((K n).toHistory.activeStage (σ n)) ((K
                    n).toHistory.activeStage_mono (has n))
                  ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
              ENNReal.ofReal (L n / Real.sqrt (R n))) →
      (hr : ∀ n, 0 < r n) → (A : ℝ) → (hA : 0 < A) → (hAκ : A + 3 ≤ Aκ) → (R0 : ℕ → ℝ) →
      (hR0 : ∀ n, 0 < R0 n) → (hR0R : ∀ n, R0 n ≤ R n) →
      (hLdef : ∀ n, L n = Real.sqrt (R0 n * r n ^ 2) / 4) →
      (hdiv : Tendsto (fun n => R0 n * r n ^ 2) atTop atTop) →
      (hball : ∀ n, y n ∈ riemannianBallOf ((K n).toHistory.stageMetric ((K
          n).toHistory.activeStage (σ n)) (σ n))
        ((seedTrace n).point ((K n).toHistory.activeStage (σ n)) ((K n).toHistory.activeStage_mono
            (has n))
          ((K n).toHistory.activeStage_mono (hsT n))) ((A + 1) * r n)) →
      (hκR : ∀ᶠ n in atTop, ∀ (j : Fin (K n).toHistory.eventCount) (c : ((K n).toHistory.stage
          j.castSucc).Carrier)
        (U : Set ((K n).toHistory.stage j.castSucc).Carrier) (a t ρU : ℝ),
        (Tn n : ℝ) - r n ^ 2 / 2 ≤ a → t ≤ (Tn n : ℝ) →
        (∀ (τ : Icc (0 : ℝ) (K n).toHistory.horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
          (K n).toHistory.time j.castSucc < τ → (τ : ℝ) < (K n).toHistory.time j.succ →
          ∀ z ∈ U, ∀ zz cc : ((K n).toHistory.stageAt τ).Carrier, HEq zz z → HEq cc c →
            riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage τ) τ) cc
                zz <
              ENNReal.ofReal ρU) →
        (∀ (τ : Icc (0 : ℝ) (K n).toHistory.horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
          (K n).toHistory.time j.castSucc < τ → (τ : ℝ) < (K n).toHistory.time j.succ →
          ∀ (hav : aSeed n ≤ τ) (hvt : τ ≤ Tn n), ∀ cc : ((K n).toHistory.stageAt τ).Carrier, HEq
              cc c →
            riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage τ) τ)
                ((seedTrace n).point ((K n).toHistory.activeStage τ) ((K
                    n).toHistory.activeStage_mono hav)
                  ((K n).toHistory.activeStage_mono hvt)) cc + ENNReal.ofReal ρU ≤
              ENNReal.ofReal (Aκ * r n)) →
        ∀ (τ : Icc (0 : ℝ) (K n).toHistory.horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
          (K n).toHistory.time j.castSucc < τ → (τ : ℝ) < (K n).toHistory.time j.succ →
          ∀ z ∈ U, ∀ zz : ((K n).toHistory.stageAt τ).Carrier, HEq zz z →
          ∀ b : ℝ, 0 < b → b ≤ ρV n → (K n).toHistory.isParabolicallyRmControlledBall τ zz b →
            ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
              riemannianVolumeMeasure ThreeModel ((K n).toHistory.stageAt τ).Carrier
                ((K n).toHistory.stageMetric ((K n).toHistory.activeStage τ) τ)
                (riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage τ) τ)
                    zz b)) →
      (hclosG : ∀ Rad B σ₁ σ₂ : ℝ, σ₁ ≤ σ₂ → σ₂ < 0 → ∀ Dw Dd : ℝ, 0 < Dw → 0 < Dd →
        ∀ᶠ n in atTop,
        ∀ (j' : Fin (K n).toHistory.eventCount) (v : ℝ), (K n).toHistory.time j'.castSucc < v →
          v < (K n).toHistory.time j'.succ → (σ n : ℝ) + σ₁ / R n ≤ v → v ≤ σ n + σ₂ / R n →
        ∀ x₁ ∈ riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
            (σ n)) (y n)
            (Dw / Real.sqrt (R n)),
        ∀ (hjσ : j'.castSucc ≤ (K n).toHistory.activeStage (σ n))
          (tr : BackwardPointTrace (K n).toHistory j'.castSucc ((K n).toHistory.activeStage (σ n))
              hjσ x₁),
        ∀ (h1 : (K n).toHistory.activeStage (aSeed n) ≤ j'.castSucc)
          (h2 : j'.castSucc ≤ (K n).toHistory.activeStage (Tn n)) (w : ((K n).toHistory.stage
              j'.castSucc).Carrier),
          riemannianEDistOf (((K n).toHistory.event j').incoming.flow.base.metric v)
              ((seedTrace n).point j'.castSucc h1 h2) w ≤
            riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ
                n))
                ((seedTrace n).point ((K n).toHistory.activeStage (σ n)) ((K
                    n).toHistory.activeStage_mono (has n))
                  ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
              ENNReal.ofReal (L n / 2 / Real.sqrt (R n)) →
          riemannianEDistOf (((K n).toHistory.event j').incoming.flow.base.metric v)
              (tr.point j'.castSucc le_rfl hjσ) w < ENNReal.ofReal (Dd / Real.sqrt (R n)) →
          R n ≤ ((K n).toHistory.event j').incoming.flow.scalar v w →
          ∀ x ∈ riemannianBallOf (((K n).toHistory.event j').incoming.flow.base.metric v) w
              (Rad / Real.sqrt (((K n).toHistory.event j').incoming.flow.scalar v w)),
          ∀ τ : ℝ, v - B / ((K n).toHistory.event j').incoming.flow.scalar v w ≤ τ → τ ≤ v →
            (K n).toHistory.time j'.castSucc < τ →
            riemannianEDistOf (((K n).toHistory.event j').incoming.flow.base.metric τ)
                ((seedTrace n).point j'.castSucc h1 h2) x ≤
              riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
                  (σ n))
                  ((seedTrace n).point ((K n).toHistory.activeStage (σ n)) ((K
                      n).toHistory.activeStage_mono (has n))
                    ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
                ENNReal.ofReal (L n / Real.sqrt (R n))) →
      (hsel : ∀ n, ¬ (K n).toHistory.HasSpatialCanonicalTimeControl ε C1' C2' Ctime' (σ n) (y n)) →
      False := by
  obtain ⟨epsW, hepsW, hB⟩ := false_of_selection_eventSlab_late_closed_residual_cond_ev_P6SN.{u}
  refine ⟨epsW, hepsW, fun ε hε hsmall hεW hεX hεN hεcone => ?_⟩
  obtain ⟨C, hC, hB'⟩ := hB ε hε hsmall hεW hεX hεN hεcone
  refine ⟨C, hC, fun {C1' C2' Ctime'} hC1 hC2 hCt => ?_⟩
  intro Ctime phi hphi K j t hjt htj Q T₀ p pF recordsK recordsF yG a₀ ha₀ hHI hcanK hδF hacc hrad
    hord hscaleK hpinchK0 hslabK hqR η hcws σ y R hσ hyG hRn hRpos d hT₀ Tn aSeed haT hsT has
    pT seedTrace L hL Cg hCg hgood hwin κ Aκ hκ r ρV hρV hroom htime hsmallS hclock hlate hη hsel4
    hδK hnomId hdistW hr A hA hAκ R0 hR0 hR0R hLdef hdiv hball hκR hclosG hsel
  have hRr : Tendsto (fun n => R n * r n ^ 2) atTop atTop :=
    tendsto_atTop_mono (fun n => mul_le_mul_of_nonneg_right (hR0R n) (sq_nonneg _)) hdiv
  have hhalf : ∀ n, (Tn n : ℝ) - r n ^ 2 / 2 ≤ (σ n : ℝ) := fun n => by
    have : 0 ≤ L n ^ 2 / R n := div_nonneg (sq_nonneg _) (hRpos n).le
    linarith [hroom n]
  have htT : ∀ n, t n ≤ (Tn n : ℝ) := fun n => by
    rw [← hσ n]
    exact hsT n
  have hhalf' : ∀ n, (Tn n : ℝ) - r n ^ 2 / 2 ≤ t n := fun n => by
    rw [← hσ n]
    exact hhalf n
  have hTn := tendsto_Tn_atTop_P6SN Tn hlate
  have hsmallK := recordsK_smallness_of_native_P6CD recordsK d.native hnomId
  have hsepWK := sepWK_of_smallness_P6CD recordsK (s := fun n => (σ n : ℝ)) hjt htT hhalf htime
    hRpos hRr hTn hsel4 hδK hsmallK
  have hsepK := sepK_eventually_of_smallness_P6CD hjt htT hhalf' htime hRpos hTn hsel4 hscaleK hδK
    hsmallK hη
  exact hB' hC1 hC2 hCt hphi hjt htj recordsF ha₀ hHI hcanK hδF hacc hrad hord hscaleK hpinchK0
    hslabK hqR hcws (fun n => (K n).toHistory) rfl σ y R hσ hyG hRn hRpos d hT₀ Tn aSeed haT hsT
    has pT seedTrace L hL Cg hCg hgood hwin hκ r ρV hρV hroom htime hsmallS hclock hsepWK hdistW
    hsepK hr A hA hAκ R0 hR0 hR0R hLdef hdiv hball hκR hclosG hsel

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
