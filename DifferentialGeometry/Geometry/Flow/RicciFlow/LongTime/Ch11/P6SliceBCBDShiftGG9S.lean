import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SliceBCBDGuardAlignedA2B
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SliceBCBDAdaptA2B

/-!
# G9″ guarded 孪生的平移孪生（kernel 帧，统一 `nr / Tκ`）：`hsepT / hsep4 / hRlt / hrad2 / hTκ` 只需 eventually
（O-CH11-G9SHIFT G1，后缀 `_G9S`）

BCBD-A2 G6 guarded G9″ 孪生（`sliceBCBD_kernel_fresh_sep_noProtC_alignedG_A2B`）要 `∀ n` 的
`hsepT / hsep4`、严格 `hRlt`、`n + 2 ≤ modelRadius`、`Tκ ≤ Tn n`；
BCBD-A2 G1 只给 eventually（`hsepT_hsep4_ev_of_sepRho_A2B`）。
本文件照 SLICE-BCBD2 G6 的做法写**平移孪生**：
* `eventually_of_shift_G9S`（PROVED）：`∀ᶠ m, P (m + N)` ⇒ `∀ᶠ n, P n`；
* **`ObservedHistory.sliceBCBD_kernel_fresh_sep_noProtC_alignedG_ev_G9S`**（PROVED ⇐ BCBD-A2 G6 +
  A2B G1）：结论逐字；`hsepT / hsep4` 删掉，改为天花板 `hceil : R n ≤ (ρs n (t n) ^ 2)⁻¹`
  （hPN 合同字段，`ρs n := fun _ => ρ̂(Tn n)` 时逐字），由 A2B `hsepT_hsep4_ev_of_sepRho_A2B`
  在 (SEP-ρ⁺) `hsepρ` 上付（eventually）；`hRlt` 换成非严格 `hRle`（hPN `k+1 ≤ R k`），
  `hacc / hrad / hord / hTκ` 换成 eventually；取 `N ≥ 1` 使以上全部在 `n ↦ n + N` 上成立
  （`hRle` 在平移上严格）；`ρs` 同步换成
  `ρs′ m s := (max (m+N+1) (ρs (m+N) s ^ 2)⁻¹)^(-1/2)`，使平移后的前缀 Dt 阈值（`max (m+1) …`）
  与原阈值（`max (m+N+1) …`）逐字相同（较小阈值才是较强陈述，故不能直接换指标）。
其余前提与 G6 相同（G6 已无 `hdistW`）。无新 binder / Prop；
`hceil` 是原 `hsepT / hsep4` 的数值前提，由 hPN 字段付。生成器 `gen/genA.py`。
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

/-- **eventually 平移（`_G9S`，PROVED）**：`∀ᶠ m, P (m + N)` ⇒ `∀ᶠ n, P n`。 -/
theorem eventually_of_shift_G9S {P : ℕ → Prop} (N : ℕ) (h : ∀ᶠ m in atTop, P (m + N)) :
    ∀ᶠ n in atTop, P n := by
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.1 h
  refine Filter.eventually_atTop.2 ⟨M + N, fun n hn => ?_⟩
  have h1 := hM (n - N) (by omega)
  rwa [Nat.sub_add_cancel (by omega)] at h1

namespace ObservedHistory

/-- **G9″ guarded 平移孪生（`_G9S`，PROVED ⇐ A2B G6 + G1；
前提同 G6，`hsepT / hsep4 / hRlt / hrad2 / hTκ` 换 eventually 形 + 天花板 `hceil`）**。 -/
theorem sliceBCBD_kernel_fresh_sep_noProtC_alignedG_ev_G9S
    {ε C1' C2' : ℝ} {Ctime' : ℝ≥0} (hεcone : ε ≤ coneAccuracy) (hC20 : 0 ≤ C2')
    {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi) {θ₀ : ℝ} (hθ₀ : 0 < θ₀)
    {K : ℕ → RetainedCoreHistory.{u}} {j : ∀ n, Fin (K n).eventCount} {t : ℕ → ℝ}
    (hjt : ∀ n, (K n).time (j n).castSucc < t n) (htj : ∀ n, t n < (K n).time (j n).succ)
    {T₀ : ℕ → ℝ} {p : ℕ → CutoffParameters}
    {recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (p n)}
    {yG : ∀ n, ((K n).stage (j n).castSucc).Carrier}
    (hcanK : ∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow)
    (hacc : ∀ᶠ n : ℕ in atTop, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1))
    (hrad : ∀ᶠ n : ℕ in atTop, (n : ℝ) + 1 ≤ (p n).modelRadius)
    (hord : ∀ᶠ n : ℕ in atTop, n + 2 ≤ (p n).modelOrder)
    (hpinchK0 : ∀ n (i : Fin (K n).eventCount), Perelman.PhiAlmostNonnegative
      ((K n).toHistory.event i).incoming.flow
      (Ico ((K n).time i.castSucc) ((K n).time i.succ) ∩ Ici (T₀ n)) phi)
    (Kh : ℕ → ObservedHistory.{u}) (hKh : Kh = fun n => (K n).toHistory)
    (σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (hσ : ∀ n, (σ n : ℝ) = t n)
    (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) (hyG : ∀ n, HEq (y n) (yG n))
    (R : ℕ → ℝ) (hRpos : ∀ n, 0 < R n)
    (hRn : ∀ n, R n = ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))
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
    {nr : ℝ → ℝ} {Aκ κ Tκ : ℝ} (hκ : 0 < κ)
    (hWK : ∀ n, KappaSeedWindowFwd_C11PK nr Aκ κ Tκ (Kh n))
    (hTκ : ∀ᶠ n in atTop, Tκ ≤ (Tn n : ℝ)) (htimeS : ∀ n, 2 * r ^ 2 < (Tn n : ℝ))
    (hvolS : ∀ n, ENNReal.ofReal (Aκ⁻¹ * r ^ 3) ≤ Geometry.Collapse.ballVolume
      ((Kh n).stageMetric ((Kh n).activeStage (Tn n)) (Tn n)) (pT n) r)
    (hnrS : ∀ n (w : ℝ), (Tn n : ℝ) - r ^ 2 / 2 ≤ w → w ≤ (Tn n : ℝ) → nr w ≤ r)
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
        i.succ ≤ (j n).castSucc →
        (t n - B / R n ≤ (K n).time i.succ ∨
          t n - (K n).time i.succ ≤ θ₀ * (((recordsK n i hi).static b).neck.scale)⁻¹) →
        ((n : ℝ) + 1) * max ((n : ℝ) + 1) (ρs n (t n) ^ 2)⁻¹ ≤
          ((recordsK n i hi).static b).neck.scale)
    (hpre1 : ∀ n, (K n).EventSlabsDerivative Ctime' (max ((n : ℝ) + 1) (ρs n (t n) ^ 2)⁻¹)
      (j n).castSucc)
    (hpre2 : ∀ n, ((K n).toHistory.event (j n)).incoming.DerivativeBoundBefore Ctime'
      (max ((n : ℝ) + 1) (ρs n (t n) ^ 2)⁻¹) (t n)) :
    ∀ A : ℝ, 0 < A → ∃ Q : ℝ, 2 ≤ Q ∧ ∀ᶠ n in atTop,
      ∀ z ∈ riemannianBallOf (((K n).toHistory.event (j n)).incoming.flow.base.metric (t n))
          (yG n)
          (A / Real.sqrt (((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))),
        ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) z ≤
          Q * ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n) := by
  subst hKh
  have hsepEv := hsepT_hsep4_ev_of_sepRho_A2B (Ctime' := Ctime') (Cg := Cg) (θ₀ := θ₀)
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
  obtain ⟨Q, hQ, hev⟩ := sliceBCBD_kernel_fresh_sep_noProtC_alignedG_A2B
    (K := fun m => K (m + N)) (j := fun m => j (m + N)) (t := fun m => t (m + N))
    (T₀ := fun m => T₀ (m + N)) (p := fun m => p (m + N))
    (recordsK := fun m => recordsK (m + N)) (yG := fun m => yG (m + N))
    (hεcone := hεcone) (hC20 := hC20) (hphi := hphi) (hθ₀ := hθ₀)
    (hjt := fun m => hjt (m + N)) (htj := fun m => htj (m + N))
    (hcanK := fun m => hcanK (m + N))
    (hacc := fun m => (hN (m + N) (hHN m)).2.1.trans (hinv m))
    (hrad2 := fun m => le_trans (hcast m) (hN (m + N) (hHN m)).2.2.1)
    (hord := fun m => le_trans (by omega) (hN (m + N) (hHN m)).2.2.2.1)
    (hpinchK0 := fun m => hpinchK0 (m + N)) (Kh := fun m => (K (m + N)).toHistory) (hKh := rfl)
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
    (nr := nr) (Tκ := Tκ) (hWK := fun m => hWK (m + N))
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
        (((m + N : ℕ) : ℝ) + 1) (ρs (m + N) (t (m + N)) ^ 2)⁻¹))⁻¹ ^ 2)⁻¹) (j (m + N)).castSucc
      rw [hmax]
      exact h)
    (hpre2 := fun m => by
      have h := hpre2 (m + N)
      change ((K (m + N)).toHistory.event (j (m + N))).incoming.DerivativeBoundBefore Ctime'
        (max ((m : ℝ) + 1) ((Real.sqrt (max (((m + N : ℕ) : ℝ) + 1)
          (ρs (m + N) (t (m + N)) ^ 2)⁻¹))⁻¹ ^ 2)⁻¹) (t (m + N))
      rw [hmax]
      exact h) A hA
  exact ⟨Q, hQ, eventually_of_shift_G9S (P := fun n =>
    ∀ z ∈ riemannianBallOf (((K n).toHistory.event (j n)).incoming.flow.base.metric (t n))
        (yG n)
        (A / Real.sqrt (((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))),
      ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) z ≤
        Q * ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n)) N hev⟩

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
