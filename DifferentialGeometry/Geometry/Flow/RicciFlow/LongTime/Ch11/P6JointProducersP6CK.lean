import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6NormalizePrefixKappaP6CK
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SepTnP6SN

/-!
# 联合主形 gap 喂 producer：`hdistC` ⇐ (SEP) at-Tn 核 + 原尺度 (DLT) / 小性
（O-CH11-P6CGK G3，后缀 `_P6CK`）

lead 14:2x：联合主形 `hgapJ` 以已交 producer 为输入。本文件接 **`hdistC`**（HDISTC 条件形）：
* `hdistC_of_sep_pin_P6CK`：P6COND `hdistC_of_sep_P6CD` 的 `d` 换成 pinching 三件
  `(a₀, 0 ≤ a₀, hpin)`（证明体只消费 `d.native.pinching(Shift_pos)`；逐字副本）；
* **`hdistC_rescaled_P6CK`**：重标度 frame 的 `hdistC` ⇐ `hpin_rescale_P6X3`（`a₀ = 0`）+ SEPTN
  `sepWK_of_smallAtTn_P6SN`（`r = 1`、`ρn = ρ̃(Tn)`，`hsel4` = prefix ceiling）+ **原尺度** `hδK`、`hsmO`；
* **`canonicalLateCore_of_jointP_P6CK`**：`hgapJP` = `hgapJ` 的 `hdistC` 槽换成 `hδK ∧ hsmO`（原尺度、
  `T₀w` late records；`hsmO` 是 `recordsK_smallness_of_native_P6CD` 的输出形 = native
    `recent_cutoff_smallness` + `hnomId`，
  NOMID `hnomId_of_ref_P6NI` 供 `hnomId`；`hδK` 是 P6CD `hdistC_of_native_P6CD` 的同名项）。
陈述由 build-logs/scratch/O-CH11-P6CGK/mk_g3.py 生成（`hdistC_of_sep_pin` 从 P6COND 文本复制）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.Geometry.Collapse
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open Perelman.CanonicalNeighborhood.FiniteHorn (SpatialCanonicalWitness)

/-- **`hdistC_of_sep_P6CD` 的 pinching-only 版（`_P6CK`）**：`d` → `(a₀, ha₀, hpin)`。 -/
theorem hdistC_of_sep_pin_P6CK {K : ℕ → RetainedCoreHistory.{u}}
    {j : ∀ n, Fin (K n).eventCount} {t : ℕ → ℝ}
    (hjt : ∀ n, (K n).time (j n).castSucc < t n) (htj : ∀ n, t n < (K n).time (j n).succ)
    {Kh : ℕ → ObservedHistory.{u}} (hKh : Kh = fun n => (K n).toHistory)
    (σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier)
    (R : ℕ → ℝ) (hσ : ∀ n, (σ n : ℝ) = t n) (hRpos : ∀ n, 0 < R n)
    {a₀ : ℝ} (ha₀ : 0 ≤ a₀)
    (hpin : ∀ n (τ' : Icc (0 : ℝ) (Kh n).horizon) (x : ((Kh n).stageAt τ').Carrier),
      InFixedHamiltonIveyRegion ((Kh n).stageMetric ((Kh n).activeStage τ') τ') (a₀ + τ') x)
    (Tn aSeed : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (haT : ∀ n, aSeed n ≤ Tn n)
    (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
      ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
    (r L : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (hroom : ∀ n, (Tn n : ℝ) - r n ^ 2 / 2 ≤ σ n - L n ^ 2 / R n)
    (htime : ∀ n, 2 * r n ^ 2 < (Tn n : ℝ))
    (hsmall : ∀ n, GC.LongTime.hasSmallParabolicCurvature (Kh n) (Tn n) (pT n) (r n))
    (hclock : ∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - r n ^ 2)
    (hRr : Tendsto (fun n => R n * r n ^ 2) atTop atTop)
    {p : ℕ → CutoffParameters} {T₀ : ℕ → ℝ}
    (recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (p n))
    (hcanK : ∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow)
    (hacc : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1))
    (hrad : ∀ n : ℕ, (n : ℝ) + 1 ≤ (p n).modelRadius)
    (hord : ∀ n : ℕ, n + 2 ≤ (p n).modelOrder)
    (hT₀ : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤ (σ n : ℝ) - B / R n)
    (hsepWK : ∀ T : ℝ, 0 < T → ∀ C : ℝ, 0 ≤ C → ∀ᶠ n in atTop,
      ∀ (i : Fin (K n).eventCount) (_hij : i.val < (j n).val) (hi : T₀ n ≤ (K n).time i.succ) b,
        (σ n : ℝ) - T / R n < (K n).time i.succ →
        2 * max (3 / (r n / 100) ^ 2) (C * R n) < ((recordsK n i hi).static b).neck.scale) :
    ∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T Kc : ℝ, 0 < D → 0 < T → 0 ≤ Kc →
      (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (σ n) (y n) (2 * D / Real.sqrt (R n))
        (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
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
            ENNReal.ofReal (L n / 4 / Real.sqrt (R n)) := by
  subst hKh
  obtain ⟨ε₀, hε₀, hC⟩ := hdistC_of_traced_anySeed_C11G3.{u}
  obtain ⟨N, hN⟩ := exists_tail_index_P6R2 hε₀ (StandardCap.transitionEnd + 10)
  have hhalf : ∀ n, (Tn n : ℝ) - r n ^ 2 / 2 ≤ (σ n : ℝ) := fun n => by
    have : 0 ≤ L n ^ 2 / R n := div_nonneg (sq_nonneg _) (hRpos n).le
    linarith [hroom n]
  have hLsh : Tendsto (fun m => L (m + N) / 4) atTop atTop :=
    (tendsto_add_atTop_iff_nat (f := fun n => L n / 4) N).2 (hL.atTop_div_const (by norm_num))
  have hRrsh : Tendsto (fun m => R (m + N) * r (m + N) ^ 2) atTop atTop :=
    (tendsto_add_atTop_iff_nat (f := fun n => R n * r n ^ 2) N).2 hRr
  have hacc' : ∀ m : ℕ, (p (m + N)).modelAccuracy ≤ ε₀ := fun m =>
    (hacc (m + N)).trans (hN m).1
  have hord' : ∀ m : ℕ, 2 ≤ (p (m + N)).modelOrder := fun m => by
    have := hord (m + N)
    omega
  have hrad' : ∀ m : ℕ, StandardCap.transitionEnd + 10 < (p (m + N)).modelRadius := fun m =>
    (hN m).2.trans_le (hrad (m + N))
  intro φ hφ D T Kc hD hT hKc htr
  have hφ' : StrictMono (fun m => φ (m + N) - N) := fun a b hab => by
    have h1 : φ (a + N) < φ (b + N) := hφ (Nat.add_lt_add_right hab N)
    have h2 : a + N ≤ φ (a + N) := hφ.id_le (a + N)
    exact Nat.sub_lt_sub_right ((Nat.le_add_left N a).trans h2) h1
  have htr' := (eventually_map_shift_P6CD N hφ).1 htr
  have key := hC (fun m => K (m + N)) (fun m => j (m + N)) (fun m => t (m + N))
    (fun m => hjt (m + N)) (fun m => htj (m + N)) (fun m => σ (m + N)) (fun m => y (m + N))
    (fun m => R (m + N)) (fun m => r (m + N)) (fun m => L (m + N) / 4) (fun m => Tn (m + N))
    (fun m => aSeed (m + N)) (fun m => haT (m + N)) (fun m => hsT (m + N))
    (fun m => has (m + N)) (fun m => pT (m + N)) (fun m => seedTrace (m + N))
    (fun m => (hσ (m + N)).le) (fun m => hhalf (m + N)) (fun m => htime (m + N))
    (Eventually.of_forall fun m => hRpos (m + N)) hLsh (fun m => hsmall (m + N))
    (fun m => hclock (m + N)) hRrsh ha₀
    (fun m => hpin (m + N)) (fun m => p (m + N)) (fun m => T₀ (m + N))
    (fun m => recordsK (m + N)) (fun m => hcanK (m + N)) hacc' hord' hrad'
    (fun T' hT' C hC' => (tendsto_add_atTop_nat N).eventually (hsepWK T' hT' C hC'))
    (fun T' _ => (tendsto_add_atTop_nat N).eventually (hT₀ T')) _ hφ' D T Kc hD hT hKc htr'
  refine (eventually_map_shift_P6CD N hφ).2 ?_
  exact key

/-- **`hdistC` 于重标度 history（`_P6CK`）**：HDISTC 条件形 `hdistC`（联合主形 gap 项）由
* pinching：G3 `hpin_rescale_P6X3`（`recordsF` + `hHI`，单 `a₀ = 0`）——`hdistC_of_sep_pin_P6CK`；
* (SEP) `hsepWK`：SEPTN at-Tn 核 `sepWK_of_smallAtTn_P6SN`（重标度 frame，`r = 1`、
  `ρn n = (q.rescale_P6N (c n)).neckRadius (Tn n)`；`hsel4` = prefix ceiling `hQρ`）；
  其 (DLT) `hδ` 与小性 `hsm` 由**原尺度** `hδK`（`∃ Tδ, ∀ n τ ≥ Tδ, C_rec·δ(τ) ≤ 1/2`）与
  **原尺度** `hsmO`（`recordsK_smallness_of_native_P6CD` 的输出形：`∀ ε, ∃ T, ∀ τ ≥ T`，原时刻
  `∈ [τ/2, τ]` 的 late records `nominal ≤ ε·q.neckRadius τ`）在原时刻 `τ = c·Tn → ∞` 处给出
  （`p̃.delta t = p.delta (c t)`、`nominal̃ = nominal/√c`、`ρ̃(Tn) = ρ(c Tn)/√c`，均定义式）。 -/
theorem hdistC_rescaled_P6CK {Ho : ℕ → RetainedCoreHistory.{u}} {c : ℕ → ℝ} (hc : ∀ n, 0 < c n)
    {q : CutoffParameters} {T₀ : ℕ → ℝ} {p pF : ℕ → CutoffParameters}
    (recordsK : ∀ n (i : Fin (Ho n).eventCount), T₀ n ≤ (Ho n).time i.succ →
      GeometricCutoffRecord (Ho n).toHistory i (p n))
    (recordsF : ∀ n i, GeometricCutoffRecord (Ho n).toHistory i (pF n)) {a₀ : ℕ → ℝ}
    (ha₀ : ∀ n, 0 < a₀ n)
    (hHI : ∀ n x, InFixedHamiltonIveyRegion ((Ho n).initialMetric 0) (a₀ n) x ∧
      -3 / a₀ n ≤ metricScalarAt ((Ho n).initialMetric 0) x)
    (hcanK : ∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow)
    (hacc : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1))
    (hrad : ∀ n : ℕ, (n : ℝ) + 1 ≤ (p n).modelRadius)
    (hord : ∀ n : ℕ, n + 2 ≤ (p n).modelOrder)
    (σ : ∀ n, Icc (0 : ℝ) ((Ho n).rescale_P6N (c n) (hc n)).toHistory.horizon)
    (y : ∀ n, (((Ho n).rescale_P6N (c n) (hc n)).toHistory.stageAt (σ n)).Carrier)
    (R : ℕ → ℝ) (hRpos : ∀ n, 0 < R n)
    (hev : ∀ n, ∃ j : Fin ((Ho n).rescale_P6N (c n) (hc n)).toHistory.eventCount,
      ((Ho n).rescale_P6N (c n) (hc n)).toHistory.time j.castSucc < (σ n : ℝ) ∧ (σ n : ℝ) < ((Ho
        n).rescale_P6N (c n) (hc n)).toHistory.time j.succ)
    (Tn aSeed : ∀ n, Icc (0 : ℝ) ((Ho n).rescale_P6N (c n) (hc n)).toHistory.horizon) (haT : ∀ n,
      aSeed n ≤ Tn n)
    (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, (((Ho n).rescale_P6N (c n) (hc n)).toHistory.stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace ((Ho n).rescale_P6N (c n) (hc n)).toHistory
      (((Ho n).rescale_P6N (c n) (hc n)).toHistory.activeStage (aSeed n)) (((Ho n).rescale_P6N (c n)
        (hc n)).toHistory.activeStage (Tn n))
      (((Ho n).rescale_P6N (c n) (hc n)).toHistory.activeStage_mono (haT n)) (pT n))
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (hroom : ∀ n, (Tn n : ℝ) - 1 ^ 2 / 2 ≤ σ n - L n ^ 2 / R n)
    (htime : ∀ n, 2 * (1 : ℝ) ^ 2 < (Tn n : ℝ))
    (hsmall : ∀ n, GC.LongTime.hasSmallParabolicCurvature ((Ho n).rescale_P6N (c n) (hc
      n)).toHistory (Tn n) (pT n) 1)
    (hclock : ∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - 1 ^ 2)
    (hRr : ∀ n : ℕ, (n : ℝ) + 1 ≤ R n)
    (hT₀ : ∀ B : ℝ, ∀ᶠ n in atTop, max 1 (T₀ n / c n) ≤ (σ n : ℝ) - B / R n)
    (hQρ : ∀ n, R n ≤ ((q.rescale_P6N (c n) (hc n)).neckRadius (Tn n) ^ 2)⁻¹)
    (hTno : Tendsto (fun n => c n * (Tn n : ℝ)) atTop atTop)
    (hδK : ∃ Tδ : ℝ, ∀ (n : ℕ) (τ : ℝ), Tδ ≤ τ → (p n).recenterConstant * (p n).delta τ ≤ 1 / 2)
    (hsmO : ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, 0 < T ∧ ∀ τ : ℝ, T ≤ τ → ∀ n (i : Fin (Ho n).eventCount),
      (Ho n).time i.succ ∈ Icc (τ / 2) τ → ∀ (hi : T₀ n ≤ (Ho n).time i.succ) h,
        (recordsK n i hi).nominalRadius h ≤ ε * q.neckRadius τ) :
    ∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T Kc : ℝ, 0 < D → 0 < T → 0 ≤ Kc →
      (∀ᶠ n in map φ atTop, ((Ho n).rescale_P6N (c n) (hc n)).toHistory.isTracedRegion (σ n) (y n)
        (2 * D / Real.sqrt (R n)) (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
      ∀ x ∈ riemannianBallOf (((Ho n).rescale_P6N (c n) (hc n)).toHistory.stageMetric
          (((Ho n).rescale_P6N (c n) (hc n)).toHistory.activeStage (σ n)) (σ n)) (y n) (D /
            Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) ((Ho n).rescale_P6N (c n) (hc n)).toHistory.horizon) (hav : aSeed n ≤ v)
        (hvs : v ≤ σ n),
        (σ n : ℝ) - T / R n ≤ v →
      ∀ tr : BackwardPointTrace ((Ho n).rescale_P6N (c n) (hc n)).toHistory (((Ho n).rescale_P6N (c
        n) (hc n)).toHistory.activeStage v)
          (((Ho n).rescale_P6N (c n) (hc n)).toHistory.activeStage (σ n)) (((Ho n).rescale_P6N (c n)
            (hc n)).toHistory.activeStage_mono hvs) x,
        riemannianEDistOf (((Ho n).rescale_P6N (c n) (hc n)).toHistory.stageMetric (((Ho
          n).rescale_P6N (c n) (hc n)).toHistory.activeStage v) v)
            ((seedTrace n).point (((Ho n).rescale_P6N (c n) (hc n)).toHistory.activeStage v)
              (((Ho n).rescale_P6N (c n) (hc n)).toHistory.activeStage_mono hav)
              (((Ho n).rescale_P6N (c n) (hc n)).toHistory.activeStage_mono (hvs.trans (hsT n))))
            (tr.point (((Ho n).rescale_P6N (c n) (hc n)).toHistory.activeStage v) le_rfl (((Ho
              n).rescale_P6N (c n) (hc n)).toHistory.activeStage_mono hvs)) ≤
          riemannianEDistOf (((Ho n).rescale_P6N (c n) (hc n)).toHistory.stageMetric (((Ho
            n).rescale_P6N (c n) (hc n)).toHistory.activeStage (σ n)) (σ n))
              ((seedTrace n).point (((Ho n).rescale_P6N (c n) (hc n)).toHistory.activeStage (σ n))
                (((Ho n).rescale_P6N (c n) (hc n)).toHistory.activeStage_mono (has n)) (((Ho
                  n).rescale_P6N (c n) (hc n)).toHistory.activeStage_mono (hsT n)))
              (y n) +
            ENNReal.ofReal (L n / 4 / Real.sqrt (R n)) := by
  obtain ⟨j, yG, hjt, htj, -, -⟩ :=
    RetainedCoreHistory.eventInterior_data_P6X (K := fun n => ((Ho n).rescale_P6N (c n) (hc n))) σ y
      hev
  have hR1 : Tendsto (fun n => R n * (fun _ : ℕ => (1 : ℝ)) n ^ 2) atTop atTop := by
    simp only [one_pow, mul_one]
    exact tendsto_atTop_mono hRr (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  have hhalf : ∀ n, (Tn n : ℝ) - (fun _ : ℕ => (1 : ℝ)) n ^ 2 / 2 ≤ (σ n : ℝ) := fun n => by
    have h0 : 0 ≤ L n ^ 2 / R n := div_nonneg (sq_nonneg _) (hRpos n).le
    have h1 := hroom n
    change (Tn n : ℝ) - 1 ^ 2 / 2 ≤ (σ n : ℝ)
    linarith
  have hδ' : ∀ᶠ n in atTop, ∀ (i : Fin ((Ho n).rescale_P6N (c n) (hc n)).eventCount),
      ((Ho n).rescale_P6N (c n) (hc n)).time i.succ ∈ Icc ((Tn n : ℝ) / 2) (Tn n) →
      ((p n).rescale_P6N (c n) (hc n)).recenterConstant *
        ((p n).rescale_P6N (c n) (hc n)).delta (((Ho n).rescale_P6N (c n) (hc n)).time i.succ) ≤ 1 /
          2 := by
    obtain ⟨Tδ, hTδ⟩ := hδK
    filter_upwards [hTno.eventually_ge_atTop (2 * Tδ)] with n hn i hi
    have e : c n * ((Ho n).rescale_P6N (c n) (hc n)).time i.succ = (Ho n).time i.succ := by
      change c n * ((Ho n).time i.succ / c n) = _
      exact mul_div_cancel₀ _ (hc n).ne'
    change (p n).recenterConstant * (p n).delta (c n * ((Ho n).rescale_P6N (c n) (hc n)).time
      i.succ) ≤ 1 / 2
    rw [e]
    refine hTδ n _ ?_
    have h1 : (Tn n : ℝ) / 2 * c n ≤ (Ho n).time i.succ := by
      have h := hi.1
      change (Tn n : ℝ) / 2 ≤ (Ho n).time i.succ / c n at h
      exact (le_div_iff₀ (hc n)).mp h
    have h2 : c n * (Tn n : ℝ) = (Tn n : ℝ) / 2 * c n * 2 := by ring
    linarith
  have hsm' : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ (i : Fin ((Ho n).rescale_P6N (c n) (hc
    n)).eventCount),
      ((Ho n).rescale_P6N (c n) (hc n)).time i.succ ∈ Icc ((Tn n : ℝ) / 2) (Tn n) →
      ∀ (hi : max 1 (T₀ n / c n) ≤ ((Ho n).rescale_P6N (c n) (hc n)).time i.succ) h,
        ((Ho n).recordsKRescale_P6X3 (hc n) (recordsK n) i hi).nominalRadius h ≤
          ε * (q.rescale_P6N (c n) (hc n)).neckRadius (Tn n) := by
    intro ε hε
    obtain ⟨T, -, hTsm⟩ := hsmO ε hε
    filter_upwards [hTno.eventually_ge_atTop T] with n hn i hi hi' h
    have hs : 0 < Real.sqrt (c n) := Real.sqrt_pos.mpr (hc n)
    have hti : (Ho n).time i.succ ∈ Icc (c n * (Tn n : ℝ) / 2) (c n * (Tn n : ℝ)) := by
      have h1 := hi.1
      have h2 := hi.2
      change (Tn n : ℝ) / 2 ≤ (Ho n).time i.succ / c n at h1
      change (Ho n).time i.succ / c n ≤ (Tn n : ℝ) at h2
      rw [le_div_iff₀ (hc n)] at h1
      rw [div_le_iff₀ (hc n)] at h2
      constructor
      · calc c n * (Tn n : ℝ) / 2 = (Tn n : ℝ) / 2 * c n := by ring
          _ ≤ _ := h1
      · calc (Ho n).time i.succ ≤ (Tn n : ℝ) * c n := h2
          _ = c n * (Tn n : ℝ) := by ring
    have key := hTsm _ hn n i hti
      (RetainedCoreHistory.le_time_of_rescale_P6X3 (hc n) (t := (Ho n).time i.succ) hi') h
    change (recordsK n i _).nominalRadius h / Real.sqrt (c n) ≤
      ε * (q.neckRadius (c n * (Tn n : ℝ)) / Real.sqrt (c n))
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right key hs.le
  exact hdistC_of_sep_pin_P6CK (K := fun n => ((Ho n).rescale_P6N (c n) (hc n))) hjt htj rfl σ y R
    (fun _ => rfl) hRpos
    (a₀ := 0) le_rfl
    (fun n => (Ho n).toHistory.hpin_rescale_P6X3 (hc n) (recordsF n) (ha₀ n) (hHI n))
    Tn aSeed haT hsT has pT seedTrace (fun _ => 1) L hL hroom htime hsmall hclock hR1
    (fun n => (Ho n).recordsKRescale_P6X3 (hc n) (recordsK n))
    (fun n => (Ho n).hcanK_rescale_P6X3 (hc n) (recordsK n) (hcanK n)) hacc hrad hord hT₀
    (sepWK_of_smallAtTn_P6SN (fun n => (Ho n).recordsKRescale_P6X3 (hc n) (recordsK n))
      (s := fun n => (σ n : ℝ)) (t := fun n => (σ n : ℝ)) (Tn := fun n => (Tn n : ℝ))
      (ρn := fun n => (q.rescale_P6N (c n) (hc n)).neckRadius (Tn n))
      hjt (fun n => hsT n) hhalf htime hRpos hR1 hQρ hδ' hsm')

namespace ObservedHistory

/-- **联合主形，`hdistC` 已接 producer（`_P6CK`）**：`canonicalLateCore_of_joint_P6CK` 的 `hdistC` 槽换成原尺度
(DLT) `hδK` 与小性 `hsmO`（G3 `hdistC_rescaled_P6CK`）。`hgapJP` 逐字：
build-logs/scratch/O-CH11-P6CGK/hgapJ.txt。 -/
theorem canonicalLateCore_of_jointP_P6CK :
    ∃ epsW : ℝ, 0 < epsW ∧ ∀ ε : ℝ, 0 < ε → ε < 1 / 11 → ε ≤ epsW →
    ε ≤ crossingWindowNeckAccuracy.{u} → ε ≤ crossingNeckAccuracy.{u} → ε ≤ coneAccuracy →
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {C1 C2 : ℝ} {Ctime : ℝ≥0}, C ≤ C1 → C ≤ C2 → C.toNNReal ≤ Ctime →
      ∀ {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
        {q : CutoffParameters},
      AntitoneOn q.neckRadius (Ici 0) →
      GC.LongTime.Ch11.HistoryCanonicalSupply_C11S F q.neckRadius ε C1 C2 →
      GC.LongTime.Ch11.TimeDerivativeSupply_C11E F q.neckRadius Ctime →
      ∀ (Ctime₀ : ℝ≥0) (T₀ Qt : ℕ → ℝ), Monotone T₀ → Monotone Qt →
      (hgapJP : ∀ A : ℝ, 1 < A → ∀ (ind : ℕ → ℕ),
        let Ho : ℕ → RetainedCoreHistory.{u} := fun k => F.tower.history (ind k)
        ∀ (Tno : ∀ k, Icc (0 : ℝ) (Ho k).toHistory.horizon)
          (pTo : ∀ k, ((Ho k).toHistory.stageAt (Tno k)).Carrier) (r : ℕ → ℝ)
          (hr : ∀ k, 0 < r k), (∀ k : ℕ, (k : ℝ) + 1 ≤ (Tno k : ℝ)) →
          (∀ k, 2 * r k ^ 2 < (Tno k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Ho k).toHistory (Tno k) (pTo k) (r k)) →
          (∀ k, ENNReal.ofReal (A⁻¹ * r k ^ 3) ≤ ballVolume ((Ho k).toHistory.stageMetric
            ((Ho k).toHistory.activeStage (Tno k)) (Tno k)) (pTo k) (r k)) →
        let c : ℕ → ℝ := fun k => r k ^ 2
        let hc : ∀ k, 0 < c k := fun k => pow_pos (hr k) 2
        let K : ℕ → RetainedCoreHistory.{u} := fun k => (Ho k).rescale_P6N (c k) (hc k)
        let Kh : ℕ → ObservedHistory.{u} := fun k => (K k).toHistory
        let Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon := fun k => (Ho k).rescaleTime_P6X (hc k) (Tno k)
        let pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier := fun k =>
          (Ho k).castRescale_P6X (hc k) (Tno k) (pTo k)
        ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
          (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ 2) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
          (∀ k, T₀ k ≤ c k * (aSeed k : ℝ)) →
        ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
            ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
          (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
          (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
          (∀ k, R k =
            metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
          ∀ (hRpos : ∀ k, 0 < R k), (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) → (∀ k, Qt k < R k) →
          Tendsto L atTop atTop →
          (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime (σ k) (y k)) →
          (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
            (σ k : ℝ) - L k ^ 2 / R k ≤ (v : ℝ) →
            ∀ z : ((Kh k).stageAt v).Carrier,
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                  ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                    ((Kh k).activeStage_mono (hvs.trans (hsT k)))) z ≤
                riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                    ((seedTrace k).point ((Kh k).activeStage (σ k))
                      ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                  ENNReal.ofReal (L k / Real.sqrt (R k)) →
              4 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
              (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (aSeed k : ℝ) ≤ σ k - T / R k) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ 2 / 2 ≤ (σ k : ℝ) - T / R k) →
          Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ 2 / 2))) atTop atTop →
          Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
          (∀ k, R k ≤ ((q.rescale_P6N (c k) (hc k)).neckRadius (Tn k) ^ 2)⁻¹) →
          (∀ k, (Tn k : ℝ) - 1 ^ 2 / 2 ≤ σ k - L k ^ 2 / R k) →
          (∀ k, y k ∈ riemannianBallOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
            ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
              ((Kh k).activeStage_mono (hsT k))) ((A + 1) * 1)) →
          (∀ᶠ k in atTop,
            riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
                  ((Kh k).activeStage_mono (hsT k))) (y k) +
              ENNReal.ofReal ((L k + 1) / Real.sqrt (R k)) ≤ ENNReal.ofReal ((A + 3) * 1)) →
          (∀ k, ∃ j : Fin (Kh k).eventCount, (Kh k).time j.castSucc < (σ k : ℝ) ∧
          (σ k : ℝ) < (Kh k).time j.succ) →
          (∀ k : ℕ, (k : ℝ) + 1 < R k) →
        ∃ (p pF : ℕ → CutoffParameters) (Qs : ℕ → ℝ)
          (recordsK : ∀ n (i : Fin (Ho n).eventCount),
            max (T₀ n) (c n * ((σ n : ℝ) - L n / R n)) ≤ (Ho n).time i.succ →
              GeometricCutoffRecord (Ho n).toHistory i (p n))
          (a₀ : ℕ → ℝ),
          Nonempty (∀ n i, GeometricCutoffRecord (Ho n).toHistory i (pF n)) ∧
          (∀ n, 0 < a₀ n) ∧
          (∀ n x, InFixedHamiltonIveyRegion ((Ho n).initialMetric 0) (a₀ n) x ∧
            -3 / a₀ n ≤ metricScalarAt ((Ho n).initialMetric 0) x) ∧
          (∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow) ∧
          (∀ n (i : Fin (Ho n).eventCount), max (T₀ n) (c n * ((σ n : ℝ) - L n / R n)) ≤ (Ho n).time
            i.succ →
            (pF n).delta ((Ho n).time i.succ) ≤ 1 / ((n : ℝ) + 1)) ∧
          (∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1)) ∧
          (∀ n : ℕ, (n : ℝ) + 1 ≤ (p n).modelRadius) ∧
          (∀ n : ℕ, n + 2 ≤ (p n).modelOrder) ∧
          (∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max (((n : ℝ) + 1) / c n) (Qs n) ≤
            ((recordsK n i hi).static b).neck.scale) ∧
          (∀ᶠ n in atTop, ∀ i hi b, 1 ≤ a₀ n * ((recordsK n i hi).static b).neck.scale) ∧
          (∀ n, (Ho n).EventSlabsDerivative Ctime₀ (Qs n) (Fin.last (Ho n).eventCount)) ∧
          (∀ n, c n * Qs n < R n) ∧
          (∀ (n : ℕ) (j' : Fin (K n).eventCount) (yG' : ((K n).stage j'.castSucc).Carrier),
        HEq (y n) yG' →
        (∃ (i : Fin (Ho n).eventCount) (hi : max (T₀ n) (c n * ((σ n : ℝ) - L n / R n)) ≤ (Ho
          n).time i.succ)
        (hl : i.succ ≤ j'.castSucc)
        (A : BackwardPointTrace (Ho n).toHistory i.succ j'.castSucc hl yG')
        (b : ((Ho n).toHistory.event i).RetainedBoundaryIndex)
        (x : standardCapWindow (p n).modelRadius),
        A.point i.succ le_rfl hl = ((recordsK n i hi).static b).window x ∧
          ‖x.val‖ < ((n : ℝ) + 1) + 1 ∧
          (σ n : ℝ) - (K n).time i.succ ≤
            (1 - 1 / ((n : ℝ) + 2)) * (c n * ((recordsK n i hi).static b).neck.scale)⁻¹) →
        (Kh n).HasSpatialCanonicalTimeControl ε C1 C2 Ctime (σ n) (y n)) ∧
          (∃ κd : ℝ, 0 < κd ∧ ∀ D Lv B : ℝ, 0 < D → 0 < Lv → 0 < B → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (σ n : ℝ) - B / R n ≤ v →
        ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvt) x,
        ∀ ϱ : ℝ, 0 < ϱ → ϱ ≤ Lv →
          (Kh n).isParabolicallyRmControlledBall v
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt))
            (ϱ / Real.sqrt (R n)) →
          ENNReal.ofReal (κd * ϱ ^ 3) ≤
            ballVolume (scaleMetric (R n) (hRpos n) ((Kh n).stageMetric ((Kh n).activeStage v) v))
              (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) ϱ) ∧
          (∃ Tδ : ℝ, ∀ (n : ℕ) (τ : ℝ), Tδ ≤ τ →
            (p n).recenterConstant * (p n).delta τ ≤ 1 / 2) ∧
          (∀ ε : ℝ, 0 < ε → ∃ T : ℝ, 0 < T ∧ ∀ τ : ℝ, T ≤ τ → ∀ n (i : Fin (Ho n).eventCount),
            (Ho n).time i.succ ∈ Icc (τ / 2) τ →
            ∀ (hi : max (T₀ n) (c n * ((σ n : ℝ) - L n / R n)) ≤ (Ho n).time i.succ) h,
              (recordsK n i hi).nominalRadius h ≤ ε * q.neckRadius τ) ∧
          (∀ D T : ℝ, 0 < D → 0 < T → ∃ C : ℝ, 1 ≤ C ∧ ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ s : ℝ, (σ n : ℝ) - T / R n < s → s < σ n → (Kh n).time ((Kh n).activeStage (σ n)) < s →
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) s)
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) x ≤
            riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
                ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                  ((Kh n).activeStage_mono (hsT n))) (y n) +
              ENNReal.ofReal (L n / Real.sqrt (R n)) →
          ∀ z : ((Kh n).stageAt (σ n)).Carrier,
            riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) s) x z <
                ENNReal.ofReal (1 / Real.sqrt (C * R n)) →
              metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage (σ n)) s) z ≤ C * R n) ∧
          (∃ (κ : ℝ) (ρV : ℕ → ℝ), 0 < κ ∧
            (Tendsto (fun n => ρV n * Real.sqrt (R n)) atTop atTop) ∧
            (∀ᶠ n in atTop, ∀ (j : Fin (Kh n).eventCount) (c : ((Kh n).stage j.castSucc).Carrier)
        (U : Set ((Kh n).stage j.castSucc).Carrier) (a t ρU : ℝ),
        (Tn n : ℝ) - 1 ^ 2 / 2 ≤ a → t ≤ (Tn n : ℝ) →
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
              ENNReal.ofReal ((A + 3) * 1)) →
        ∀ (τ : Icc (0 : ℝ) (Kh n).horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
          (Kh n).time j.castSucc < τ → (τ : ℝ) < (Kh n).time j.succ →
          ∀ z ∈ U, ∀ zz : ((Kh n).stageAt τ).Carrier, HEq zz z →
          ∀ b : ℝ, 0 < b → b ≤ ρV n → (Kh n).isParabolicallyRmControlledBall τ zz b →
            ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
              riemannianVolumeMeasure ThreeModel ((Kh n).stageAt τ).Carrier
                ((Kh n).stageMetric ((Kh n).activeStage τ) τ)
                (riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ) zz b))) ∧
          (∀ Rad B σ₁ σ₂ : ℝ, σ₁ ≤ σ₂ → σ₂ < 0 → ∀ Dw Dd : ℝ, 0 < Dw → 0 < Dd →
        ∃ C : ℝ, 1 ≤ C ∧ ∀ᶠ n in atTop,
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
          ∀ s : ℝ, v - B / ((Kh n).event j').incoming.flow.scalar v w ≤ s → s ≤ v →
            (Kh n).time j'.castSucc < s →
            riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric s)
                ((seedTrace n).point j'.castSucc h1 h2) x ≤
              riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
                  ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                    ((Kh n).activeStage_mono (hsT n))) (y n) +
                ENNReal.ofReal (L n / Real.sqrt (R n)) →
            ∀ z : ((Kh n).stage j'.castSucc).Carrier,
              riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric s) x z <
                  ENNReal.ofReal
                    (1 / Real.sqrt (C * ((Kh n).event j').incoming.flow.scalar v w)) →
                ((Kh n).event j').incoming.flow.scalar s z ≤
                  C * ((Kh n).event j').incoming.flow.scalar v w)) →
      (hrestP : ∀ A : ℝ, 1 < A → ∀ (ind : ℕ → ℕ),
        let Ho : ℕ → RetainedCoreHistory.{u} := fun k => F.tower.history (ind k)
        ∀ (Tno : ∀ k, Icc (0 : ℝ) (Ho k).toHistory.horizon)
          (pTo : ∀ k, ((Ho k).toHistory.stageAt (Tno k)).Carrier) (r : ℕ → ℝ)
          (hr : ∀ k, 0 < r k), (∀ k : ℕ, (k : ℝ) + 1 ≤ (Tno k : ℝ)) →
          (∀ k, 2 * r k ^ 2 < (Tno k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Ho k).toHistory (Tno k) (pTo k) (r k)) →
          (∀ k, ENNReal.ofReal (A⁻¹ * r k ^ 3) ≤ ballVolume ((Ho k).toHistory.stageMetric
            ((Ho k).toHistory.activeStage (Tno k)) (Tno k)) (pTo k) (r k)) →
        let c : ℕ → ℝ := fun k => r k ^ 2
        let hc : ∀ k, 0 < c k := fun k => pow_pos (hr k) 2
        let K : ℕ → RetainedCoreHistory.{u} := fun k => (Ho k).rescale_P6N (c k) (hc k)
        let Kh : ℕ → ObservedHistory.{u} := fun k => (K k).toHistory
        let Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon := fun k => (Ho k).rescaleTime_P6X (hc k) (Tno k)
        let pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier := fun k =>
          (Ho k).castRescale_P6X (hc k) (Tno k) (pTo k)
        ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
          (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ 2) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
          (∀ k, T₀ k ≤ c k * (aSeed k : ℝ)) →
        ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
            ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
          (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
          (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
          (∀ k, R k =
            metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
          (∀ k, 0 < R k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) → (∀ k, Qt k < R k) →
          Tendsto L atTop atTop →
          (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime (σ k) (y k)) →
          (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
            (σ k : ℝ) - L k ^ 2 / R k ≤ (v : ℝ) →
            ∀ z : ((Kh k).stageAt v).Carrier,
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                  ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                    ((Kh k).activeStage_mono (hvs.trans (hsT k)))) z ≤
                riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                    ((seedTrace k).point ((Kh k).activeStage (σ k))
                      ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                  ENNReal.ofReal (L k / Real.sqrt (R k)) →
              4 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
              (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (aSeed k : ℝ) ≤ σ k - T / R k) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ 2 / 2 ≤ (σ k : ℝ) - T / R k) →
          Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ 2 / 2))) atTop atTop →
          Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
          (∀ k, R k ≤ ((q.rescale_P6N (c k) (hc k)).neckRadius (Tn k) ^ 2)⁻¹) →
          (∀ k, (Tn k : ℝ) - 1 ^ 2 / 2 ≤ σ k - L k ^ 2 / R k) →
          (∀ k, y k ∈ riemannianBallOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
            ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
              ((Kh k).activeStage_mono (hsT k))) ((A + 1) * 1)) →
          (∀ᶠ k in atTop,
            riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
                  ((Kh k).activeStage_mono (hsT k))) (y k) +
              ENNReal.ofReal ((L k + 1) / Real.sqrt (R k)) ≤ ENNReal.ofReal ((A + 3) * 1)) →
        ((∀ k, (Kh k).time (Fin.last (Kh k).eventCount) < (σ k : ℝ) ∧ (σ k : ℝ) < (Kh k).horizon) ∨
          (∀ k, ¬ ∃ W : SpatialCanonicalWitness
            ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
            ε C1 C2 (y k), W.capTubeHasNeckChart ε)) → False) →
      GC.LongTime.Ch11.CanonicalLateCore_P6X F ε C1 C2 := by
  obtain ⟨epsW, hepsW, hB⟩ := canonicalLateCore_of_joint_P6CK.{u}
  refine ⟨epsW, hepsW, fun ε hε hsmall hεW hεX hεN hεcone => ?_⟩
  obtain ⟨C, hC, hB'⟩ := hB ε hε hsmall hεW hεX hεN hεcone
  refine ⟨C, hC, fun {C1 C2 Ctime} hC1 hC2 hCt => ?_⟩
  intro P g F q hanti hcan hder Ctime₀ T₀ Qt hT₀m hQm hgap hrest
  refine hB' hC1 hC2 hCt hanti hcan hder Ctime₀ T₀ Qt hT₀m hQm ?_ hrest
  intro A hA ind Ho Tno pTo r hr hlate htime hsmallo hvolo c hc K Kh Tn pT aSeed haT hclock h1
    hsm hT₀l seedTrace σ y R hsT has L hRdef hRpos hRr hQR hL hsel hgood hwin hwin' hroomT hradii
    hQρ hroom hball hdistσ hev hlt
  obtain ⟨p, pF, Qs, recordsK, a₀, ⟨recordsF⟩, ha₀, hHI, hcanK, hδF, hacc, hrad, hord, hscaleK,
    hbirthA, hslabK, hQs, hcwpL, hκd, hδK, hsmO, hscalW, hκg, hscalU⟩ :=
    hgap A hA ind Tno pTo r hr hlate htime hsmallo hvolo aSeed haT hclock h1 hsm hT₀l seedTrace
      σ y R hsT has L hRdef hRpos hRr hQR hL hsel hgood hwin hwin' hroomT hradii hQρ hroom hball
      hdistσ hev hlt
  have hT₀' : ∀ B : ℝ, ∀ᶠ n in atTop,
      max 1 (max (T₀ n) (c n * ((σ n : ℝ) - L n / R n)) / c n) ≤ (σ n : ℝ) - B / R n := by
    intro B
    filter_upwards [hwin (max B 1) (lt_of_lt_of_le one_pos (le_max_right _ _)),
      hL.eventually_ge_atTop (max B 1)] with n hn hLn
    have hB1 : B / R n ≤ max B 1 / R n :=
      div_le_div_of_nonneg_right (le_max_left _ _) (hRpos n).le
    have hLB : max B 1 / R n ≤ L n / R n := div_le_div_of_nonneg_right hLn (hRpos n).le
    have h2 : (aSeed n : ℝ) ≤ (σ n : ℝ) - B / R n := hn.trans (by linarith)
    refine max_le ((h1 n).trans h2) ?_
    rw [div_le_iff₀ (hc n)]
    refine max_le ?_ ?_
    · calc T₀ n ≤ c n * (aSeed n : ℝ) := hT₀l n
        _ ≤ c n * ((σ n : ℝ) - B / R n) := mul_le_mul_of_nonneg_left h2 (hc n).le
        _ = ((σ n : ℝ) - B / R n) * c n := mul_comm _ _
    · have h3 : (σ n : ℝ) - L n / R n ≤ (σ n : ℝ) - B / R n := by linarith
      exact (mul_le_mul_of_nonneg_left h3 (hc n).le).trans_eq (mul_comm _ _)
  have htime' : ∀ n, 2 * (1 : ℝ) ^ 2 < (Tn n : ℝ) := fun n => by
    rw [one_pow, mul_one]
    change 2 < (Tno n : ℝ) / r n ^ 2
    rw [lt_div_iff₀ (hc n)]
    linarith [htime n]
  have hTno : Tendsto (fun n => c n * (Tn n : ℝ)) atTop atTop := by
    refine tendsto_atTop_mono (fun n => ?_)
      (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
    rw [(Ho n).mul_rescaleTime_P6X (hc n) (Tno n)]
    exact hlate n
  exact ⟨p, pF, Qs, recordsK, a₀, ⟨recordsF⟩, ha₀, hHI, hcanK, hδF, hacc, hrad, hord, hscaleK,
    hbirthA, hslabK, hQs, hcwpL, hκd,
    hdistC_rescaled_P6CK (Ho := Ho) hc recordsK recordsF ha₀ hHI hcanK hacc hrad hord σ y R
      hRpos hev Tn aSeed haT hsT has pT seedTrace L hL hroom htime' hsm hclock (fun n => hRr n)
      hT₀' hQρ hTno hδK hsmO,
    hscalW, hκg, hscalU⟩

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
