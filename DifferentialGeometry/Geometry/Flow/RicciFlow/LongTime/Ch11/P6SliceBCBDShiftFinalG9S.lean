import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SliceBCBDGuardFinalAlignedG9S
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SliceBCBDAdaptA2B
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SliceBCBDShiftGG9S

/-!
# final slab 外壳 G9″（逐 `n` FRESH）的平移孪生（O-CH11-G9SHIFT G10，后缀 `_G9S`）

`P6SliceBCBDShiftSeqG9S` 的 final 换帧：底座 `sliceBCBD_final_fresh_sep_noProtC_alignedG_seq_G9S`
（`P6SliceBCBDGuardFinalAlignedG9S`）要 `∀ n` 的 `hsepT / hsep4`、严格 `hRlt`、`n + 2 ≤ modelRadius`、
`Tκ n ≤ Tn n`；本文件给 eventually 形：
* `hsepT_hsep4_ev_of_sepRhoF_G9S`：A2B 同名引理的 final 指标版（`i⁺ ≤ Fin.last`）；
* **`ObservedHistory.sliceBCBD_final_fresh_sep_noProtC_alignedG_seq_ev_G9S`**：同 `…ShiftSeqG9S` 的做法
  （平移量 `N0 + 1`、`ρs′` 构造、`eventually_of_shift_G9S`），`G` / `hG` / `hpinchF` 随之平移。
无新 binder。生成器 `gen/genH.py`。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Geometry.Collapse
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace ObservedHistory

/-- **final 版 `hsepT / hsep4` ⇐ `hsepρ` + 天花板（`_G9S`，PROVED）**：A2B 同名引理，指标 `i⁺ ≤ Fin.last`。 -/
theorem hsepT_hsep4_ev_of_sepRhoF_G9S {Ctime' : ℝ≥0} {Cg θ₀ : ℝ}
    {K : ℕ → RetainedCoreHistory.{u}} {t : ℕ → ℝ}
    {T₀ : ℕ → ℝ} {p : ℕ → CutoffParameters}
    {recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (p n)}
    (R : ℕ → ℝ) (hRpos : ∀ n, 0 < R n) (ρs : ℕ → ℝ → ℝ)
    (hceil : ∀ n, R n ≤ (ρs n (t n) ^ 2)⁻¹)
    (hsepρ : ∀ B : ℝ, 0 < B → ∀ᶠ n in atTop,
      ∀ (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ)
        (b : ((K n).toHistory.event i).RetainedBoundaryIndex),
        i.succ ≤ (Fin.last (K n).eventCount) →
        (t n - B / R n ≤ (K n).time i.succ ∨
          t n - (K n).time i.succ ≤ θ₀ * (((recordsK n i hi).static b).neck.scale)⁻¹) →
        ((n : ℝ) + 1) * max ((n : ℝ) + 1) (ρs n (t n) ^ 2)⁻¹ ≤
          ((recordsK n i hi).static b).neck.scale) :
    ∀ᶠ n in atTop, ∀ (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ)
      (b : ((K n).toHistory.event i).RetainedBoundaryIndex), i.succ ≤ (Fin.last (K n).eventCount) →
      t n - (K n).time i.succ ≤ θ₀ * (((recordsK n i hi).static b).neck.scale)⁻¹ →
      θ₀ * R n ≤ 1 / (2 * max (Ctime' : ℝ) 1) / max (max 1 Cg) 1 *
          ((recordsK n i hi).static b).neck.scale ∧
        2 * (2 * (max (max 1 Cg) 1 * R n)) < ((recordsK n i hi).static b).neck.scale := by
  set X : ℝ := max (4 * max (max 1 Cg) 1)
    (θ₀ * (max (max 1 Cg) 1 * (2 * max (Ctime' : ℝ) 1))) with hX
  filter_upwards [hsepρ 1 one_pos,
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_gt_atTop X] with n hs hn
  intro i hi b hij hy
  have hX1 : 4 * max (max 1 Cg) 1 ≤ X := le_max_left _ _
  have hX2 : θ₀ * (max (max 1 Cg) 1 * (2 * max (Ctime' : ℝ) 1)) ≤ X := le_max_right _ _
  exact sepT_sep4_of_sepRho_ceiling_A2B (hRpos n) (hceil n) (hs i hi b hij (Or.inr hy))
    (by linarith) (by linarith)

/-! ### §2 CXJD 族数值项 ⇐ hPN 字段 -/

/-- **G9″ 平移孪生（tower 帧逐 `n` FRESH，`_G9S`，PROVED ⇐ GuardSeqG9S + A2B G1；
前提同 GuardSeqG9S，`hsepT / hsep4 / hRlt / hrad2 / hTκ` 换 eventually 形 + 天花板 `hceil`）**。 -/
theorem sliceBCBD_final_fresh_sep_noProtC_alignedG_seq_ev_G9S
    {ε C1' C2' : ℝ} {Ctime' : ℝ≥0} (hεcone : ε ≤ coneAccuracy) (hC20 : 0 ≤ C2')
    {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi) {θ₀ : ℝ} (hθ₀ : 0 < θ₀)
    {K : ℕ → RetainedCoreHistory.{u}} {t : ℕ → ℝ} (htl : ∀ n, (K n).time (Fin.last (K n).eventCount)
        < t n)
    (htK : ∀ n, t n < (K n).horizon)
    (G : ∀ n, ((K n).stage (Fin.last (K n).eventCount)).IncomingSlab
      ((K n).time (Fin.last (K n).eventCount)) (K n).horizon)
    (hG : ∀ n, G n = ((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
      ((htl n).trans (htK n)) le_rfl)
    {T₀ : ℕ → ℝ} {p : ℕ → CutoffParameters}
    {recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (p n)}
    {yG : ∀ n, ((K n).stage (Fin.last (K n).eventCount)).Carrier}
    (hcanK : ∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow)
    (hacc : ∀ᶠ n : ℕ in atTop, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1))
    (hrad : ∀ᶠ n : ℕ in atTop, (n : ℝ) + 1 ≤ (p n).modelRadius)
    (hord : ∀ᶠ n : ℕ in atTop, n + 2 ≤ (p n).modelOrder)
    (hpinchK0 : ∀ n (i : Fin (K n).eventCount), Perelman.PhiAlmostNonnegative
      ((K n).toHistory.event i).incoming.flow
      (Ico ((K n).time i.castSucc) ((K n).time i.succ) ∩ Ici (T₀ n)) phi)
    (hpinchF : ∀ n, Perelman.PhiAlmostNonnegative (G n).flow
      (Ico ((K n).time (Fin.last (K n).eventCount)) ((K n).horizon) ∩ Ici (T₀ n)) phi)
    (Kh : ℕ → ObservedHistory.{u}) (hKh : Kh = fun n => (K n).toHistory)
    (σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (hσ : ∀ n, (σ n : ℝ) = t n)
    (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) (hyG : ∀ n, HEq (y n) (yG n))
    (R : ℕ → ℝ) (hRpos : ∀ n, 0 < R n)
    (hRn : ∀ n, R n = (G n).flow.scalar (t n) (yG n))
    (hRle : ∀ n : ℕ, (n : ℝ) + 1 ≤ R n)
    (hT₀ : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤ (σ n : ℝ) - B / R n)
    (Tn aSeed : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (haT : ∀ n, aSeed n ≤ Tn n)
    (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
      ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop) {Cg : ℝ} (hCg : 2 ≤ Cg)
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
        (Kh n).HasSpatialCanonicalTimeControl ε C1' C2' Ctime' v z)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n)
    {r : ℝ} (hr : 0 < r)
    (hsmall : ∀ n, GC.LongTime.hasSmallParabolicCurvature (Kh n) (Tn n) (pT n) r)
    (hclock : ∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - r ^ 2)
    (a₀ : ℕ → ℝ) (ha₀ : ∀ n, 0 ≤ a₀ n)
    (hpin : ∀ n (s : Icc (0 : ℝ) (Kh n).horizon)
      (x : ((Kh n).stageAt s).Carrier),
      InFixedHamiltonIveyRegion ((Kh n).stageMetric ((Kh n).activeStage s) s)
        (a₀ n + s) x)
    (hRa : ∀ n, 1 ≤ R n * aSeed n)
    (T₀X : ℕ → ℝ) (hT₀X : ∀ n, T₀X n ≤ aSeed n)
    (hOldX : ∀ n (e : Fin (Kh n).eventCount), T₀X n ≤ (Kh n).time e.succ →
      ((Kh n).event e).old = ((Kh n).event e).transition.trace.retainedCore)
    (hdσ : ∀ n, riemannianEDistOf ((Kh n).stageMetric
        ((Kh n).activeStage (σ n)) (σ n))
        ((seedTrace n).point ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono (has n))
          ((Kh n).activeStage_mono (hsT n))) (y n) ≠ ⊤)
    {nr : ℕ → ℝ → ℝ} {Tκ : ℕ → ℝ} {Aκ κ : ℝ} (hκ : 0 < κ)
    (hWK : ∀ n, KappaSeedWindowFwd_C11PK (nr n) Aκ κ (Tκ n) (Kh n))
    (hTκ : ∀ᶠ n in atTop, Tκ n ≤ (Tn n : ℝ)) (htimeS : ∀ n, 2 * r ^ 2 < (Tn n : ℝ))
    (hvolS : ∀ n, ENNReal.ofReal (Aκ⁻¹ * r ^ 3) ≤ Geometry.Collapse.ballVolume
      ((Kh n).stageMetric ((Kh n).activeStage (Tn n)) (Tn n)) (pT n) r)
    (hnrS : ∀ n (w : ℝ), (Tn n : ℝ) - r ^ 2 / 2 ≤ w → w ≤ (Tn n : ℝ) → nr n w ≤ r)
    (hwinF : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (Tn n : ℝ) - r ^ 2 / 2 ≤ (σ n : ℝ) - T / R n)
    (hgate : ∀ᶠ n in atTop,
      riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
          ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
            ((Kh n).activeStage_mono (hsT n))) (y n) +
        ENNReal.ofReal ((L n + 1) / Real.sqrt (R n)) ≤ ENNReal.ofReal (Aκ * r))
    (ρs : ℕ → ℝ → ℝ)
    (hceil : ∀ n, R n ≤ (ρs n (t n) ^ 2)⁻¹)
    (hsepρ : ∀ B : ℝ, 0 < B → ∀ᶠ n in atTop,
      ∀ (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ)
        (b : ((K n).toHistory.event i).RetainedBoundaryIndex),
        i.succ ≤ (Fin.last (K n).eventCount) →
        (t n - B / R n ≤ (K n).time i.succ ∨
          t n - (K n).time i.succ ≤ θ₀ * (((recordsK n i hi).static b).neck.scale)⁻¹) →
        ((n : ℝ) + 1) * max ((n : ℝ) + 1) (ρs n (t n) ^ 2)⁻¹ ≤
          ((recordsK n i hi).static b).neck.scale)
    (hpre1 : ∀ n, (K n).EventSlabsDerivative Ctime' (max ((n : ℝ) + 1) (ρs n (t n) ^ 2)⁻¹)
      (Fin.last (K n).eventCount))
    (hpre2 : ∀ n, (G n).DerivativeBoundBefore Ctime'
      (max ((n : ℝ) + 1) (ρs n (t n) ^ 2)⁻¹) (t n)) :
    ∀ A : ℝ, 0 < A → ∃ Q : ℝ, 2 ≤ Q ∧ ∀ᶠ n in atTop,
      ∀ z ∈ riemannianBallOf ((G n).flow.base.metric (t n))
          (yG n)
          (A / Real.sqrt ((G n).flow.scalar (t n) (yG n))),
        (G n).flow.scalar (t n) z ≤
          Q * (G n).flow.scalar (t n) (yG n) := by
  subst hKh
  have hsepEv := hsepT_hsep4_ev_of_sepRhoF_G9S (Ctime' := Ctime') (Cg := Cg) (θ₀ := θ₀)
    (recordsK := recordsK) R hRpos ρs hceil hsepρ
  obtain ⟨N0, hN⟩ := Filter.eventually_atTop.1
    (hsepEv.and (hacc.and (hrad.and (hord.and hTκ))))
  set N : ℕ := N0 + 1 with hNN
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
    rw [hNN]
    push_cast
    linarith [(Nat.cast_nonneg N0 : (0 : ℝ) ≤ N0)]
  have hsh : Tendsto (fun m : ℕ => m + N) atTop atTop := tendsto_add_atTop_nat N
  have hHN : ∀ m : ℕ, N0 ≤ m + N := fun m => by omega
  have hcast : ∀ m : ℕ, (m : ℝ) + 1 + 1 ≤ ((m + N : ℕ) : ℝ) + 1 := fun m => by
    push_cast
    linarith
  have hcast0 : ∀ m : ℕ, (m : ℝ) + 1 ≤ ((m + N : ℕ) : ℝ) + 1 := fun m => by
    linarith [hcast m]
  have hinv : ∀ m : ℕ, 1 / (((m + N : ℕ) : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) := fun m =>
    one_div_le_one_div_of_le (by positivity) (hcast0 m)
  have hXpos : ∀ (m : ℕ) (s : ℝ),
      0 < max (((m + N : ℕ) : ℝ) + 1) (ρs (m + N) s ^ 2)⁻¹ := fun m s =>
    lt_of_lt_of_le (by positivity) (le_max_left _ _)
  have hρinv : ∀ (m : ℕ) (s : ℝ),
      ((Real.sqrt (max (((m + N : ℕ) : ℝ) + 1) (ρs (m + N) s ^ 2)⁻¹))⁻¹ ^ 2)⁻¹ =
        max (((m + N : ℕ) : ℝ) + 1) (ρs (m + N) s ^ 2)⁻¹ := fun m s => by
    rw [inv_pow, Real.sq_sqrt (hXpos m s).le, inv_inv]
  have hmax : ∀ (m : ℕ) (s : ℝ),
      max ((m : ℝ) + 1) ((Real.sqrt (max (((m + N : ℕ) : ℝ) + 1)
        (ρs (m + N) s ^ 2)⁻¹))⁻¹ ^ 2)⁻¹ =
        max (((m + N : ℕ) : ℝ) + 1) (ρs (m + N) s ^ 2)⁻¹ := fun m s => by
    rw [hρinv]
    exact max_eq_right ((hcast0 m).trans (le_max_left _ _))
  intro A hA
  obtain ⟨Q, hQ, hev⟩ := sliceBCBD_final_fresh_sep_noProtC_alignedG_seq_G9S
    (K := fun m => K (m + N)) (t := fun m => t (m + N))
    (T₀ := fun m => T₀ (m + N)) (p := fun m => p (m + N))
    (recordsK := fun m => recordsK (m + N)) (yG := fun m => yG (m + N))
    (hεcone := hεcone) (hC20 := hC20) (hphi := hphi) (hθ₀ := hθ₀)
    (htl := fun m => htl (m + N)) (htK := fun m => htK (m + N)) (G := fun m => G (m + N))
    (hG := fun m => hG (m + N))
    (hcanK := fun m => hcanK (m + N))
    (hacc := fun m => (hN (m + N) (hHN m)).2.1.trans (hinv m))
    (hrad2 := fun m => le_trans (hcast m) (hN (m + N) (hHN m)).2.2.1)
    (hord := fun m => le_trans (by omega) (hN (m + N) (hHN m)).2.2.2.1)
    (hpinchK0 := fun m => hpinchK0 (m + N)) (hpinchF := fun m => hpinchF (m + N)) (Kh := fun m => (K
        (m + N)).toHistory) (hKh := rfl)
    (σ := fun m => σ (m + N)) (hσ := fun m => hσ (m + N)) (y := fun m => y (m + N))
    (hyG := fun m => hyG (m + N)) (R := fun m => R (m + N)) (hRpos := fun m => hRpos (m + N))
    (hRn := fun m => hRn (m + N))
    (hRlt := fun m => lt_of_lt_of_le (by linarith [hcast m]) (hRle (m + N)))
    (hT₀ := fun B => hsh.eventually (hT₀ B)) (Tn := fun m => Tn (m + N))
    (aSeed := fun m => aSeed (m + N)) (haT := fun m => haT (m + N)) (hsT := fun m => hsT (m + N))
    (has := fun m => has (m + N)) (pT := fun m => pT (m + N))
    (seedTrace := fun m => seedTrace (m + N)) (L := fun m => L (m + N)) (hL := hL.comp hsh)
    (hCg := hCg) (hgood := fun m => hgood (m + N)) (hwin := fun T hT => hsh.eventually (hwin T hT))
    (hr := hr)
    (hsmall := fun m => hsmall (m + N)) (hclock := fun m => hclock (m + N))
    (a₀ := fun m => a₀ (m + N)) (ha₀ := fun m => ha₀ (m + N)) (hpin := fun m => hpin (m + N))
    (hRa := fun m => hRa (m + N)) (T₀X := fun m => T₀X (m + N)) (hT₀X := fun m => hT₀X (m + N))
    (hOldX := fun m => hOldX (m + N)) (hdσ := fun m => hdσ (m + N)) (hκ := hκ)
    (nr := fun m => nr (m + N)) (Tκ := fun m => Tκ (m + N)) (hWK := fun m => hWK (m + N))
    (hTκ := fun m => (hN (m + N) (hHN m)).2.2.2.2) (htimeS := fun m => htimeS (m + N))
    (hvolS := fun m => hvolS (m + N)) (hnrS := fun m => hnrS (m + N))
    (hwinF := fun T hT => hsh.eventually (hwinF T hT)) (hgate := hsh.eventually hgate)
    (hsepT := fun m i hi b hl hage => ((hN (m + N) (hHN m)).1 i hi b hl hage).1)
    (hsep4 := fun m i hi b hl hage => ((hN (m + N) (hHN m)).1 i hi b hl hage).2)
    (ρs := fun m s => (Real.sqrt (max (((m + N : ℕ) : ℝ) + 1) (ρs (m + N) s ^ 2)⁻¹))⁻¹)
    (hsepρ := fun B hB => (hsh.eventually (hsepρ B hB)).mono fun m hm i hi b hij hor => by
      have h := hm i hi b hij hor
      rw [hmax]
      refine le_trans (mul_le_mul_of_nonneg_right (hcast0 m) (hXpos m _).le) h)
    (hpre1 := fun m => by
      have h := hpre1 (m + N)
      change (K (m + N)).EventSlabsDerivative Ctime' (max ((m : ℝ) + 1) ((Real.sqrt (max
        (((m + N : ℕ) : ℝ) + 1) (ρs (m + N) (t (m + N)) ^ 2)⁻¹))⁻¹ ^ 2)⁻¹) (Fin.last (K (m +
            N)).eventCount)
      rw [hmax]
      exact h)
    (hpre2 := fun m => by
      have h := hpre2 (m + N)
      change (G (m + N)).DerivativeBoundBefore Ctime'
        (max ((m : ℝ) + 1) ((Real.sqrt (max (((m + N : ℕ) : ℝ) + 1)
          (ρs (m + N) (t (m + N)) ^ 2)⁻¹))⁻¹ ^ 2)⁻¹) (t (m + N))
      rw [hmax]
      exact h) A hA
  exact ⟨Q, hQ, eventually_of_shift_G9S (P := fun n =>
    ∀ z ∈ riemannianBallOf ((G n).flow.base.metric (t n))
        (yG n)
        (A / Real.sqrt ((G n).flow.scalar (t n) (yG n))),
      (G n).flow.scalar (t n) z ≤
        Q * (G n).flow.scalar (t n) (yG n)) N hev⟩

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
