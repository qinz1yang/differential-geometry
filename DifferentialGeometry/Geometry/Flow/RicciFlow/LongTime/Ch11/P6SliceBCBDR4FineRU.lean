import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SliceBCBDGuardR4A2B
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HanchorFineRecordsRU

/-!
# R4 中心 guarded 切片 BCBD：K 帧细 records 内部化（O-CH11-RECUP G2，`_RU`）

lead R32 U3/U4（G8 侧）。`sliceBCBD_kernel_R4center_G_A2B`（G8）要逐 `n` 的 K 帧参数 `p n` 与 records，
带对角条款 `hacc : acc(p n) ≤ 1/(n+1)`、`hrad2 : n + 2 ≤ radius(p n)`、`hord`
（R27 BLOCKED 的参数级障碍）。
本文件：
* `ObservedHistory.sliceBCBD_kernel_R4center_fine_RU`（PROVED ⇐ G8）：结论逐字；删去
  `p / recordsK / hcanK / hacc / hrad2 / hord`，换成粗 records `recordsK0`
  （`hsepT / hsep4 / hsepρ` 改述于其上）
  加 `hfineK`：每档 `l`，eventually 在 `n` 上有第 `l` 档精度的晚 records（canonical window，neck scale
  与粗 record 相同）。证明：结论 `∀ A ∃ Q ∀ᶠ n` 反证 + 子列（`Filter.extraction_forall_of_frequently`），
  子列第 `l` 项取第 `l` 档细 records ⇒ G8 的对角条款对全部 `l` 成立；`hRlt` 因 `l ≤ φ l`；
  `ρs′ l s := (√(max (φ l + 1) (ρs (φ l) s ^ 2)⁻¹))⁻¹` 使 `max (l+1) (ρs′⁻²)` 与原阈值逐字相同
  （`hpre1/2` 原样），
  `hsepρ` 由 `(l+1) ≤ (φ l + 1)` 单调；其余前提随 `φ → ∞` 保持。
* `hfineK_of_tower_RU`（PROVED）：塔原尺度的 `hfine`（= `GC.LongTime.Ch11.hfine_of_scrsPlus_RU` 的输出）
  + K 帧 = 塔层 `ind n` 按 `c n` 重标度 + `c n · T₀ n → ∞` ⇒ `hfineK`
  （records / 粗 records 均经 `rescale_P6M`）。
无新 binder / Prop。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Integral.Measure
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- **塔 `hfine` ⇒ K 帧 `hfineK`（`_RU`，PROVED）**：见模块文档。 -/
theorem hfineK_of_tower_RU {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {pF : CutoffParameters}
    (records : ∀ n (e : Fin (F.tower.history n).eventCount),
      GeometricCutoffRecord (F.tower.history n).toHistory e pF)
    (hfine : ∀ (D ζ : ℝ) (m : ℕ), 0 < ζ → ∃ T₀ : ℝ, ∀ n, ∃ p : CutoffParameters,
      D ≤ p.modelRadius ∧ p.modelAccuracy ≤ ζ ∧ m ≤ p.modelOrder ∧
      ∃ records' : ∀ i : Fin (F.tower.history n).eventCount,
          T₀ ≤ (F.tower.history n).time i.succ →
          GeometricCutoffRecord (F.tower.history n).toHistory i p,
        (∀ i hi b, ((records' i hi).static b).hasCanonicalWindow) ∧
        ∀ i hi b, ((records' i hi).static b).neck.scale = ((records n i).static b).neck.scale)
    (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ n, 0 < c n) (T₀ : ℕ → ℝ)
    (hT₀ : Tendsto (fun n => c n * T₀ n) atTop atTop) :
    ∀ l : ℕ, ∀ᶠ n in atTop, ∃ p : CutoffParameters,
      ((l : ℝ) + 1) + 1 ≤ p.modelRadius ∧ p.modelAccuracy ≤ 1 / ((l : ℝ) + 1) ∧
      l + 2 ≤ p.modelOrder ∧
      ∃ rec : ∀ i : Fin ((F.tower.history (ind n)).rescale_P6N (c n) (hc n)).eventCount,
          T₀ n ≤ ((F.tower.history (ind n)).rescale_P6N (c n) (hc n)).time i.succ →
          GeometricCutoffRecord ((F.tower.history (ind n)).rescale_P6N (c n) (hc n)).toHistory
            i p,
        (∀ i hi b, ((rec i hi).static b).hasCanonicalWindow) ∧
        ∀ i hi b, ((rec i hi).static b).neck.scale =
          (((records (ind n) i).rescale_P6M (c n) (hc n)).static b).neck.scale := by
  intro l
  obtain ⟨T₁, hT₁⟩ := hfine (((l : ℝ) + 1) + 1) (1 / ((l : ℝ) + 1)) (l + 2) (by positivity)
  filter_upwards [hT₀.eventually_ge_atTop T₁] with n hn
  obtain ⟨p, hD, hζ, hm, rec', hcan, hsc⟩ := hT₁ (ind n)
  have hlate : ∀ i : Fin ((F.tower.history (ind n)).rescale_P6N (c n) (hc n)).eventCount,
      T₀ n ≤ ((F.tower.history (ind n)).rescale_P6N (c n) (hc n)).time i.succ →
      T₁ ≤ (F.tower.history (ind n)).time i.succ := fun i hi => by
    have htk : ((F.tower.history (ind n)).rescale_P6N (c n) (hc n)).time i.succ =
        (F.tower.history (ind n)).time i.succ / c n := rfl
    rw [htk, le_div_iff₀ (hc n), mul_comm] at hi
    linarith
  refine ⟨p.rescale_P6N (c n) (hc n), hD, hζ, hm,
    fun i hi => (rec' i (hlate i hi)).rescale_P6M (c n) (hc n), fun i hi b => ?_,
    fun i hi b => ?_⟩
  · exact ((rec' i (hlate i hi)).static b).hasCanonicalWindow_rescale_P6M (hcan i _ b) _ _
  · have e1 := ((rec' i (hlate i hi)).static b).rescale_P6M_scale (c n) (hc n)
    have e2 := ((records (ind n) i).static b).rescale_P6M_scale (c n) (hc n)
    rw [hsc i (hlate i hi) b] at e1
    exact e1.trans e2.symm

/-- **R4 中心 guarded 切片 BCBD，K 帧细 records 内部化（`_RU`，PROVISIONAL[G8 清单去掉
`p / recordsK / hcanK / hacc / hrad2 / hord`；`hfineK` 由 `hfineK_of_tower_RU` ∘ SCRS⁺ 付]）**：见模块文档。 -/
theorem ObservedHistory.sliceBCBD_kernel_R4center_fine_RU
    {ε C1' C2' : ℝ} {Ctime' : ℝ≥0} (hεcone : ε ≤ coneAccuracy) (hC20 : 0 ≤ C2')
    {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi) {θ₀ : ℝ} (hθ₀ : 0 < θ₀)
    {K : ℕ → RetainedCoreHistory.{u}} {j : ∀ n, Fin (K n).eventCount} {t : ℕ → ℝ}
    (hjt : ∀ n, (K n).time (j n).castSucc < t n) (htj : ∀ n, t n < (K n).time (j n).succ)
    {T₀ : ℕ → ℝ} {p0 : ℕ → CutoffParameters}
    {recordsK0 : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (p0 n)}
    {yG : ∀ n, ((K n).stage (j n).castSucc).Carrier}
    (hfineK : ∀ l : ℕ, ∀ᶠ n in atTop, ∃ p : CutoffParameters,
      ((l : ℝ) + 1) + 1 ≤ p.modelRadius ∧ p.modelAccuracy ≤ 1 / ((l : ℝ) + 1) ∧
      l + 2 ≤ p.modelOrder ∧
      ∃ rec : ∀ i : Fin (K n).eventCount, T₀ n ≤ (K n).time i.succ →
          GeometricCutoffRecord (K n).toHistory i p,
        (∀ i hi b, ((rec i hi).static b).hasCanonicalWindow) ∧
        ∀ i hi b, ((rec i hi).static b).neck.scale = ((recordsK0 n i hi).static b).neck.scale)
    (hpinchK0 : ∀ n (i : Fin (K n).eventCount), Perelman.PhiAlmostNonnegative
      ((K n).toHistory.event i).incoming.flow
      (Ico ((K n).time i.castSucc) ((K n).time i.succ) ∩ Ici (T₀ n)) phi)
    (Kh : ℕ → ObservedHistory.{u}) (hKh : Kh = fun n => (K n).toHistory)
    (σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (hσ : ∀ n, (σ n : ℝ) = t n)
    (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) (hyG : ∀ n, HEq (y n) (yG n))
    (R : ℕ → ℝ) (hRpos : ∀ n, 0 < R n)
    (hRn : ∀ n, R n = ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))
    (hRlt : ∀ n : ℕ, (n : ℝ) + 1 < R n)
    (Rt : ℕ → ℝ) (hRtpos : ∀ n, 0 < Rt n) (hcmpL : ∀ n, Rt n / 2 < R n)
    (hT₀ : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤ (σ n : ℝ) - B / Rt n)
    (Tn aSeed : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (haT : ∀ n, aSeed n ≤ Tn n)
    (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
      ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
    (Lt : ℕ → ℝ) (hL : Tendsto Lt atTop atTop) (L : ℕ → ℝ)
    (hLdef : ∀ n, L n = (Lt n - 2) / 2) {Cg : ℝ} (hCg : 8 ≤ Cg)
    (hgood' : ∀ n, ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
      (σ n : ℝ) - (Lt n - 2) ^ 2 / Rt n ≤ (v : ℝ) →
      ∀ z : ((Kh n).stageAt v).Carrier,
        riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
            ((seedTrace n).point ((Kh n).activeStage v) ((Kh n).activeStage_mono hav)
              ((Kh n).activeStage_mono (hvs.trans (hsT n)))) z ≤
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal ((Lt n - 2) / Real.sqrt (Rt n)) →
        4 * Rt n ≤ metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v) z →
        (Kh n).HasSpatialCanonicalTimeControl ε C1' C2' Ctime' v z)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / Rt n)
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
    (hTκ : ∀ n, Tκ ≤ (Tn n : ℝ)) (htimeS : ∀ n, 2 * r ^ 2 < (Tn n : ℝ))
    (hvolS : ∀ n, ENNReal.ofReal (Aκ⁻¹ * r ^ 3) ≤ Geometry.Collapse.ballVolume
      ((Kh n).stageMetric ((Kh n).activeStage (Tn n)) (Tn n)) (pT n) r)
    (hnrS : ∀ n (w : ℝ), (Tn n : ℝ) - r ^ 2 / 2 ≤ w → w ≤ (Tn n : ℝ) → nr w ≤ r)
    (hwinF : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (Tn n : ℝ) - r ^ 2 / 2 ≤ (σ n : ℝ) - T / Rt n)
    (hgate : ∀ᶠ n in atTop,
      riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
          ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
            ((Kh n).activeStage_mono (hsT n))) (y n) +
        ENNReal.ofReal ((L n + 1) / Real.sqrt (R n)) ≤ ENNReal.ofReal (Aκ * r))
    (hsepT : ∀ n (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ)
      (b : ((K n).toHistory.event i).RetainedBoundaryIndex), i.succ ≤ (j n).castSucc →
      t n - (K n).time i.succ ≤ θ₀ * (((recordsK0 n i hi).static b).neck.scale)⁻¹ →
      θ₀ * R n ≤ 1 / (2 * max (Ctime' : ℝ) 1) / max (max 1 Cg) 1 *
        ((recordsK0 n i hi).static b).neck.scale)
    (hsep4 : ∀ n (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ)
      (b : ((K n).toHistory.event i).RetainedBoundaryIndex), i.succ ≤ (j n).castSucc →
      t n - (K n).time i.succ ≤ θ₀ * (((recordsK0 n i hi).static b).neck.scale)⁻¹ →
      2 * (2 * (max (max 1 Cg) 1 * R n)) < ((recordsK0 n i hi).static b).neck.scale)
    (ρs : ℕ → ℝ → ℝ)
    (hsepρ : ∀ B : ℝ, 0 < B → ∀ᶠ n in atTop,
      ∀ (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ)
        (b : ((K n).toHistory.event i).RetainedBoundaryIndex),
        i.succ ≤ (j n).castSucc →
        (t n - B / R n ≤ (K n).time i.succ ∨
          t n - (K n).time i.succ ≤ θ₀ * (((recordsK0 n i hi).static b).neck.scale)⁻¹) →
        ((n : ℝ) + 1) * max ((n : ℝ) + 1) (ρs n (t n) ^ 2)⁻¹ ≤
          ((recordsK0 n i hi).static b).neck.scale)
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
  intro A hA
  by_contra hneg
  have hfreq : ∀ Q : ℝ, 2 ≤ Q → ∃ᶠ n in atTop,
      ¬ ∀ z ∈ riemannianBallOf (((K n).toHistory.event (j n)).incoming.flow.base.metric (t n))
          (yG n)
          (A / Real.sqrt (((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))),
        ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) z ≤
          Q * ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n) :=
    fun Q hQ => Filter.not_eventually.mp fun h => hneg ⟨Q, hQ, h⟩
  obtain ⟨φ, hφ, hφP⟩ := Filter.extraction_forall_of_frequently fun l : ℕ =>
    (hfreq ((l : ℝ) + 2) (by have := (Nat.cast_nonneg l : (0 : ℝ) ≤ l); linarith)).and_eventually
      (hfineK l)
  choose pf hradf haccf hordf recf hcanf hscf using fun l => (hφP l).2
  have hφle : ∀ l, l ≤ φ l := hφ.id_le
  have hφt : Tendsto φ atTop atTop := hφ.tendsto_atTop
  have hφ1 : ∀ l : ℕ, (l : ℝ) + 1 ≤ (φ l : ℝ) + 1 := fun l => by
    have := (Nat.cast_le (α := ℝ)).mpr (hφle l)
    linarith
  have hXpos : ∀ (l : ℕ) (s : ℝ), 0 < max ((φ l : ℝ) + 1) (ρs (φ l) s ^ 2)⁻¹ := fun l s =>
    lt_of_lt_of_le (by positivity) (le_max_left _ _)
  have hmax : ∀ (l : ℕ) (s : ℝ),
      max ((l : ℝ) + 1) ((Real.sqrt (max ((φ l : ℝ) + 1) (ρs (φ l) s ^ 2)⁻¹))⁻¹ ^ 2)⁻¹ =
        max ((φ l : ℝ) + 1) (ρs (φ l) s ^ 2)⁻¹ := fun l s => by
    rw [inv_pow, Real.sq_sqrt (hXpos l s).le, inv_inv]
    exact max_eq_right ((hφ1 l).trans (le_max_left _ _))
  obtain ⟨Q₀, -, hev⟩ := sliceBCBD_kernel_R4center_G_A2B
    (K := fun l => K (φ l)) (j := fun l => j (φ l)) (t := fun l => t (φ l))
    (T₀ := fun l => T₀ (φ l)) (p := pf) (recordsK := recf) (yG := fun l => yG (φ l))
    (hεcone := hεcone) (hC20 := hC20) (hphi := hphi) (hθ₀ := hθ₀)
    (hjt := fun l => hjt (φ l)) (htj := fun l => htj (φ l)) (hcanK := hcanf)
    (hacc := haccf) (hrad2 := hradf) (hord := hordf)
    (hpinchK0 := fun l => hpinchK0 (φ l)) (Kh := fun l => (K (φ l)).toHistory) (hKh := rfl)
    (σ := fun l => σ (φ l)) (hσ := fun l => hσ (φ l)) (y := fun l => y (φ l))
    (hyG := fun l => hyG (φ l)) (R := fun l => R (φ l)) (hRpos := fun l => hRpos (φ l))
    (hRn := fun l => hRn (φ l)) (hRlt := fun l => lt_of_le_of_lt (hφ1 l) (hRlt (φ l)))
    (Rt := fun l => Rt (φ l)) (hRtpos := fun l => hRtpos (φ l))
    (hcmpL := fun l => hcmpL (φ l)) (hT₀ := fun B => hφt.eventually (hT₀ B))
    (Tn := fun l => Tn (φ l)) (aSeed := fun l => aSeed (φ l)) (haT := fun l => haT (φ l))
    (hsT := fun l => hsT (φ l)) (has := fun l => has (φ l)) (pT := fun l => pT (φ l))
    (seedTrace := fun l => seedTrace (φ l)) (Lt := fun l => Lt (φ l)) (hL := hL.comp hφt)
    (L := fun l => L (φ l)) (hLdef := fun l => hLdef (φ l)) (hCg := hCg)
    (hgood' := fun l => hgood' (φ l)) (hwin := fun T hT => hφt.eventually (hwin T hT))
    (hr := hr) (hsmall := fun l => hsmall (φ l)) (hclock := fun l => hclock (φ l))
    (a₀ := fun l => a₀ (φ l)) (ha₀ := fun l => ha₀ (φ l)) (hpin := fun l => hpin (φ l))
    (hRa := fun l => hRa (φ l)) (T₀X := fun l => T₀X (φ l)) (hT₀X := fun l => hT₀X (φ l))
    (hOldX := fun l => hOldX (φ l)) (hdσ := fun l => hdσ (φ l)) (hκ := hκ)
    (hWK := fun l => hWK (φ l)) (hTκ := fun l => hTκ (φ l)) (htimeS := fun l => htimeS (φ l))
    (hvolS := fun l => hvolS (φ l)) (hnrS := fun l => hnrS (φ l))
    (hwinF := fun T hT => hφt.eventually (hwinF T hT)) (hgate := hφt.eventually hgate)
    (hsepT := fun l i hi b hle hcond => by
      have e := hscf l i hi b
      rw [e] at hcond ⊢
      exact hsepT (φ l) i hi b hle hcond)
    (hsep4 := fun l i hi b hle hcond => by
      have e := hscf l i hi b
      rw [e] at hcond ⊢
      exact hsep4 (φ l) i hi b hle hcond)
    (ρs := fun l s => (Real.sqrt (max ((φ l : ℝ) + 1) (ρs (φ l) s ^ 2)⁻¹))⁻¹)
    (hsepρ := fun B hB => (hφt.eventually (hsepρ B hB)).mono fun l hl i hi b hle hcond => by
      have e := hscf l i hi b
      rw [e] at hcond ⊢
      rw [hmax l]
      exact le_trans (mul_le_mul_of_nonneg_right (hφ1 l) (hXpos l _).le) (hl i hi b hle hcond))
    (hpre1 := fun l => by
      rw [hmax l]
      exact hpre1 (φ l))
    (hpre2 := fun l => by
      rw [hmax l]
      exact hpre2 (φ l)) A hA
  obtain ⟨l, hl1, hl2⟩ := (hev.and (eventually_ge_atTop ⌈Q₀⌉₊)).exists
  apply (hφP l).1
  intro z hz
  refine (hl1 z hz).trans ?_
  have h2 : ((⌈Q₀⌉₊ : ℕ) : ℝ) ≤ (l : ℝ) + 2 := by exact_mod_cast (show ⌈Q₀⌉₊ ≤ l + 2 by omega)
  have hR0 : 0 < ((K (φ l)).toHistory.event (j (φ l))).incoming.flow.scalar (t (φ l)) (yG (φ l)) :=
    (hRn (φ l)) ▸ hRpos (φ l)
  exact mul_le_mul_of_nonneg_right ((Nat.le_ceil Q₀).trans h2) hR0.le

/-- consumer：塔 bridge 的输出即 `hfineK`（K 帧 = 塔层重标度，粗 records = `rescale_P6M`）。 -/
example {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {pF : CutoffParameters}
    (records : ∀ n (e : Fin (F.tower.history n).eventCount),
      GeometricCutoffRecord (F.tower.history n).toHistory e pF)
    (hS : ∀ (D ζ : ℝ) (m : ℕ), 0 < ζ → ∃ T₀ : ℝ, ∀ n, ∃ p : CutoffParameters,
      D ≤ p.modelRadius ∧ p.modelAccuracy ≤ ζ ∧ m ≤ p.modelOrder ∧
      ∃ records' : ∀ i : Fin (F.tower.history n).eventCount,
          T₀ ≤ (F.tower.history n).time i.succ →
          GeometricCutoffRecord (F.tower.history n).toHistory i p,
        (∀ i hi b, ((records' i hi).static b).hasCanonicalWindow) ∧
        ∀ i hi b, ((records' i hi).static b).neck.scale = ((records n i).static b).neck.scale)
    (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ n, 0 < c n) (T₀ : ℕ → ℝ)
    (hT₀ : Tendsto (fun n => c n * T₀ n) atTop atTop) : True := by
  have _h := fun {ε C1' C2' : ℝ} {Ctime' : ℝ≥0} =>
    @ObservedHistory.sliceBCBD_kernel_R4center_fine_RU.{u} ε C1' C2' Ctime'
  have _k := hfineK_of_tower_RU records hS ind c hc T₀ hT₀
  trivial

/-- consumer：签名稳定。 -/
example : type_of% @ObservedHistory.sliceBCBD_kernel_R4center_fine_RU :=
  @ObservedHistory.sliceBCBD_kernel_R4center_fine_RU

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
