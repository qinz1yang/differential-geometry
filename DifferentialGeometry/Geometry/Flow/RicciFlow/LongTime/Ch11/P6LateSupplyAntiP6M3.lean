import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6LateSupplyP6LT
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.RadiusAntitoneC11RA

/-!
# P5L 供给的 `hρq : q.neckRadius → 0` ⇒ 换成树内的 `AntitoneOn q.neckRadius (Ici 0)`（O-CH11-P6ANCH3 G6）

P6LATE `exists_lateKdata_of_P5L_P6LT` 用 `hρq : Tendsto q.neckRadius atTop (𝓝 0)` 只为得到 late record 的
static neck scale 下界 `(n+1)·max(n+1, Q n) ≤ scale`。**`hρq` 不必要**：record 的 `nominal_small`
（`r < δ(t)²·ρ(t)`）已含 `δ²`，故 `δ(t) → 0`（`hδq`）+ `ρ(t) ≤ ρ(0)`（antitone）⇒ `r → 0` ⇒ scale → ∞。
* `inv_two_mul_sq_lt_static_scale_record_delta_P6M3`：单 record 静态 scale 下界的 `δ²` 版
  （`δ(t) ≤ δ₀`、`ρ(t) ≤ ρ₁`、`δ₀²ρ₁ ≤ ρ₀` ⇒ `(2ρ₀²)⁻¹ < scale`；原版用粗界 `δ² ≤ 1`）；
* **`exists_lateKdata_of_P5L_antitone_P6M3`**：`hρq` → `hρa : AntitoneOn q.neckRadius (Ici 0)`，结论逐字；
* `false_of_selection_eventSlab_late_suppliedA_P6M3`：P6LT `…_late_supplied_P6LT` 的同改副本。
**树内来源**：`hρa` 与 `hδq` 都由 S1+S2 `GC.LongTime.Ch11.chain_S1_S2_C11RA`（W1 narrow tuple 的 `q`）给出，
profile 侧 `AnalyticSurgeryProfile.radius_antitone`（`Hp.parameters`）亦是 `hρa` 逐字（见文件末 consumer）。
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

namespace RetainedCoreHistory

/-- 单 record 的 static neck scale 下界（`δ²` 版，`_P6M3`）：`p.recenterConstant · δ₀ ≤ 1/2`、该 event 的
`p.delta ≤ δ₀`、`p.neckRadius ≤ ρ₁`、`δ₀²ρ₁ ≤ ρ₀` ⇒ `(2ρ₀²)⁻¹ < scale`。 -/
theorem inv_two_mul_sq_lt_static_scale_record_delta_P6M3 {H : RetainedCoreHistory.{u}}
    {p : CutoffParameters} {i : Fin H.eventCount} (R : GeometricCutoffRecord H.toHistory i p)
    {δ₀ ρ₁ ρ₀ : ℝ} (hΛδ : p.recenterConstant * δ₀ ≤ 1 / 2) (hδ : p.delta (H.time i.succ) ≤ δ₀)
    (hρ : p.neckRadius (H.time i.succ) ≤ ρ₁) (hδρ : δ₀ ^ 2 * ρ₁ ≤ ρ₀)
    (b : (H.toHistory.event i).RetainedBoundaryIndex) :
    (2 * ρ₀ ^ 2)⁻¹ < (R.static b).neck.scale := by
  have ht : 0 ≤ H.time i.succ := H.toHistory.time_nonneg i.succ
  set α := b.1.1
  have hn := R.nominal_small ⟨α⟩
  have hnpos := R.nominal_pos ⟨α⟩
  have hdpos := p.delta_pos _ ht
  have hd1 := p.delta_lt_one _ ht
  have hρpos := p.neckRadius_pos _ ht
  have hcmp := R.recenter_scale_comparison b
  have hsc := R.scale_eq α
  have hdα := R.delta_le α
  have hdαpos := R.delta_pos α
  have hΛ : (4 : ℝ) ≤ p.recenterConstant := p.recenterConstant_ge_four
  set r := R.nominalRadius ⟨α⟩
  set N := (R.neck α).scale
  set S := (R.static b).neck.scale
  have hSpos : 0 < S := (R.static b).neck.scale_pos
  have hr : r < ρ₀ := by
    have h1 : p.delta (H.time i.succ) ^ 2 * p.neckRadius (H.time i.succ) ≤ δ₀ ^ 2 * ρ₁ := by
      have hsq : p.delta (H.time i.succ) ^ 2 ≤ δ₀ ^ 2 := by nlinarith
      have hρ₁ : 0 < ρ₁ := hρpos.trans_le hρ
      calc p.delta (H.time i.succ) ^ 2 * p.neckRadius (H.time i.succ)
          ≤ p.delta (H.time i.succ) ^ 2 * ρ₁ :=
            mul_le_mul_of_nonneg_left hρ (sq_nonneg _)
        _ ≤ δ₀ ^ 2 * ρ₁ := mul_le_mul_of_nonneg_right hsq hρ₁.le
    exact hn.trans_le (h1.trans hδρ)
  have hNlow : (ρ₀ ^ 2)⁻¹ < N := by
    rw [hsc]
    exact inv_strictAnti₀ (pow_pos hnpos 2) (by nlinarith)
  have hNpos : 0 < N := (inv_pos.mpr (pow_pos (hnpos.trans hr) 2)).trans hNlow
  have hΛδα : p.recenterConstant * R.delta α ≤ 1 / 2 :=
    (mul_le_mul_of_nonneg_left (hdα.trans hδ) (by linarith)).trans hΛδ
  have hhalf : 1 / 2 ≤ S / N := by
    have := (abs_le.mp (hcmp.trans hΛδα)).1
    linarith
  have hS : N / 2 ≤ S := by
    rw [le_div_iff₀ hNpos] at hhalf
    linarith
  have h2 : (2 * ρ₀ ^ 2)⁻¹ = (ρ₀ ^ 2)⁻¹ / 2 := by
    rw [mul_inv, div_eq_mul_inv]; ring
  rw [h2]
  linarith


/-- **P5L 形 ⇒ late 主形 (a) 组，`hρq` 换 antitone（`_P6M3`）**：见文件头。 -/
theorem exists_lateKdata_of_P5L_antitone_P6M3 {K : ℕ → RetainedCoreHistory.{u}}
    {q : CutoffParameters}
    (Q : ℕ → ℝ)
    (hP5L : ∀ (D ζ : ℝ) (m : ℕ), 0 < ζ → ∃ T : ℝ, ∀ n, ∃ p : CutoffParameters,
      p.delta = q.delta ∧ p.neckRadius = q.neckRadius ∧ p.fixed = q.fixed ∧
      p.recenterConstant = q.recenterConstant ∧ D ≤ p.modelRadius ∧ p.modelAccuracy ≤ ζ ∧
      m ≤ p.modelOrder ∧ ∃ records : ∀ i : Fin (K n).eventCount, T ≤ (K n).time i.succ →
        GeometricCutoffRecord (K n).toHistory i p,
      ∀ i hi b, GC.LongTime.Ch11.linkedCanonicalWindow_C11E ((records i hi).static b))
    (hδq : Tendsto q.delta atTop (𝓝 0)) (hρa : AntitoneOn q.neckRadius (Ici 0)) :
    ∃ (T₀ : ℕ → ℝ) (p : ℕ → CutoffParameters)
      (recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
        GeometricCutoffRecord (K n).toHistory i (p n)),
      (∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow) ∧
      (∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1)) ∧
      (∀ n : ℕ, (n : ℝ) + 1 ≤ (p n).modelRadius) ∧
      (∀ n : ℕ, n + 2 ≤ (p n).modelOrder) ∧
      (∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max ((n : ℝ) + 1) (Q n) ≤
        ((recordsK n i hi).static b).neck.scale) ∧
      (∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
        q.delta ((K n).time i.succ) ≤ 1 / ((n : ℝ) + 1)) := by
  have h1 : ∀ n : ℕ, ∃ T : ℝ, ∃ p : CutoffParameters, p.delta = q.delta ∧
      p.neckRadius = q.neckRadius ∧ p.recenterConstant = q.recenterConstant ∧
      (n : ℝ) + 1 ≤ p.modelRadius ∧ p.modelAccuracy ≤ 1 / ((n : ℝ) + 1) ∧
      n + 2 ≤ p.modelOrder ∧
      ∃ records : ∀ i : Fin (K n).eventCount, T ≤ (K n).time i.succ →
        GeometricCutoffRecord (K n).toHistory i p,
      ∀ i hi b, GC.LongTime.Ch11.linkedCanonicalWindow_C11E ((records i hi).static b) := by
    intro n
    have hζ : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    obtain ⟨T, hT⟩ := hP5L ((n : ℝ) + 1) (1 / ((n : ℝ) + 1)) (n + 2) hζ
    obtain ⟨p, hpδ, hpρ, -, hprc, hprad, hpacc, hpord, records, hlink⟩ := hT n
    exact ⟨T, p, hpδ, hpρ, hprc, hprad, hpacc, hpord, records, hlink⟩
  choose T₁ p hpδ hpρ hprc hprad hpacc hpord records hlink using h1
  have hrc : 0 < q.recenterConstant := by linarith [q.recenterConstant_ge_four]
  have hrc' : q.recenterConstant ≠ 0 := hrc.ne'
  have h2 : ∀ n : ℕ, ∃ T : ℝ, ∀ s ≥ T,
      q.delta s ≤ min (1 / ((n : ℝ) + 1)) (1 / (2 * q.recenterConstant)) := by
    intro n
    have hpos : (0 : ℝ) < min (1 / ((n : ℝ) + 1)) (1 / (2 * q.recenterConstant)) :=
      lt_min (by positivity) (by positivity)
    exact Filter.eventually_atTop.mp (hδq.eventually (ge_mem_nhds hpos))
  choose Tδ hTδ using h2
  have hcpos : ∀ n : ℕ, 0 < ((n : ℝ) + 1) * max ((n : ℝ) + 1) (Q n) := fun n =>
    mul_pos (by positivity) (lt_of_lt_of_le (by positivity) (le_max_left _ _))
  have hρ₁ : 0 < q.neckRadius 0 := q.neckRadius_pos 0 le_rfl
  have h3 : ∀ n : ℕ, ∃ T : ℝ, ∀ s ≥ T,
      q.delta s ≤ 1 / (2 * (((n : ℝ) + 1) * max ((n : ℝ) + 1) (Q n)) * q.neckRadius 0) := by
    intro n
    have hpos : (0 : ℝ) < 1 / (2 * (((n : ℝ) + 1) * max ((n : ℝ) + 1) (Q n)) * q.neckRadius 0) :=
      div_pos one_pos (mul_pos (mul_pos two_pos (hcpos n)) hρ₁)
    exact Filter.eventually_atTop.mp (hδq.eventually (ge_mem_nhds hpos))
  choose Tρ hTρ using h3
  have hle1 : ∀ n s, max (T₁ n) (max (Tδ n) (Tρ n)) ≤ s → T₁ n ≤ s := fun n s h =>
    (le_max_left _ _).trans h
  have hle2 : ∀ n s, max (T₁ n) (max (Tδ n) (Tρ n)) ≤ s → Tδ n ≤ s := fun n s h =>
    ((le_max_left _ _).trans (le_max_right _ _)).trans h
  have hle3 : ∀ n s, max (T₁ n) (max (Tδ n) (Tρ n)) ≤ s → Tρ n ≤ s := fun n s h =>
    ((le_max_right _ _).trans (le_max_right _ _)).trans h
  refine ⟨fun n => max (T₁ n) (max (Tδ n) (Tρ n)), p,
    fun n i hi => records n i (hle1 n _ hi),
    fun n i hi b => GC.LongTime.Ch11.linkedCanonicalWindow_hasCanonicalWindow_C11E _
      (hlink n i (hle1 n _ hi) b), hpacc, hprad, hpord, ?_, ?_⟩
  · intro n i hi b
    have hδs := hTδ n _ (hle2 n _ hi)
    have hρs := hTρ n _ (hle3 n _ hi)
    have hc1 : 1 ≤ ((n : ℝ) + 1) * max ((n : ℝ) + 1) (Q n) := by
      have h1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
      have h2 : (n : ℝ) + 1 ≤ max ((n : ℝ) + 1) (Q n) := le_max_left _ _
      nlinarith
    have hΛδ : (p n).recenterConstant * (1 / (2 * q.recenterConstant)) ≤ 1 / 2 :=
      le_of_eq (by rw [hprc n]; field_simp)
    have ht0 : 0 ≤ (K n).time i.succ := (K n).toHistory.time_nonneg i.succ
    have hdel1 : q.delta ((K n).time i.succ) < 1 := q.delta_lt_one _ ht0
    have hdel0 : 0 < q.delta ((K n).time i.succ) := q.delta_pos _ ht0
    have hρle : q.neckRadius ((K n).time i.succ) ≤ q.neckRadius 0 :=
      hρa (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht0) ht0
    have hδρ : q.delta ((K n).time i.succ) ^ 2 * q.neckRadius 0 ≤
        1 / (2 * (((n : ℝ) + 1) * max ((n : ℝ) + 1) (Q n))) := by
      have hc := hcpos n
      have h1 : q.delta ((K n).time i.succ) * q.neckRadius 0 ≤
          1 / (2 * (((n : ℝ) + 1) * max ((n : ℝ) + 1) (Q n))) := by
        have h2 := (le_div_iff₀ (by positivity)).1 hρs
        rw [le_div_iff₀ (by positivity)]
        nlinarith
      have h3 : q.delta ((K n).time i.succ) ^ 2 * q.neckRadius 0 ≤
          q.delta ((K n).time i.succ) * q.neckRadius 0 := by
        have : q.delta ((K n).time i.succ) ^ 2 ≤ q.delta ((K n).time i.succ) := by nlinarith
        exact mul_le_mul_of_nonneg_right this hρ₁.le
      exact h3.trans h1
    have hΛδ' : (p n).recenterConstant * q.delta ((K n).time i.succ) ≤ 1 / 2 := by
      rw [hprc n]
      have h1 : q.delta ((K n).time i.succ) ≤ 1 / (2 * q.recenterConstant) :=
        hδs.trans (min_le_right _ _)
      rw [le_div_iff₀ (by positivity)] at h1
      nlinarith
    have hlt := inv_two_mul_sq_lt_static_scale_record_delta_P6M3 (records n i (hle1 n _ hi))
      (δ₀ := q.delta ((K n).time i.succ)) (ρ₁ := q.neckRadius 0)
      (ρ₀ := 1 / (2 * (((n : ℝ) + 1) * max ((n : ℝ) + 1) (Q n)))) hΛδ'
      (by rw [hpδ n]) (by rw [hpρ n]; exact hρle) hδρ b
    have heq : (2 * (1 / (2 * (((n : ℝ) + 1) * max ((n : ℝ) + 1) (Q n)))) ^ 2)⁻¹ =
        2 * (((n : ℝ) + 1) * max ((n : ℝ) + 1) (Q n)) ^ 2 := by
      have := (hcpos n).ne'
      field_simp
    rw [heq] at hlt
    change ((n : ℝ) + 1) * max ((n : ℝ) + 1) (Q n) ≤
      ((records n i (hle1 n _ hi)).static b).neck.scale
    nlinarith
  · intro n i hi
    exact (hTδ n _ (hle2 n _ hi)).trans (min_le_left _ _)

end RetainedCoreHistory

namespace ObservedHistory

/-- **P6 收口 late 主形，(a) 组由 P5L 形 + antitone 供给（`_P6M3`）**：`…_late_supplied_P6LT` 的
`hρq` 换 `hρa`。 -/
theorem false_of_selection_eventSlab_late_suppliedA_P6M3 :
    ∃ epsW : ℝ, 0 < epsW ∧ ∀ ε : ℝ, 0 < ε → ε < 1 / 11 → ε ≤ epsW →
    ε ≤ crossingWindowNeckAccuracy.{u} → ε ≤ crossingNeckAccuracy.{u} → ε ≤ coneAccuracy →
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {C1' C2' : ℝ} {Ctime' : ℝ≥0}, C ≤ C1' → C ≤ C2' → C.toNNReal ≤ Ctime' →
      ∀ {Ctime : ℝ≥0} {phi : ℝ → ℝ}, (hphi : Perelman.AdmissiblePinchingFunction phi) →
      {K : ℕ → RetainedCoreHistory.{u}} → {Q : ℕ → ℝ} → {q : CutoffParameters} →
      (recordsF : ∀ n i, GeometricCutoffRecord (K n).toHistory i q) →
      {a₀ : ℝ} → (ha₀ : 0 < a₀) →
      (hHI : ∀ n x, InFixedHamiltonIveyRegion ((K n).initialMetric 0) a₀ x ∧
        -3 / a₀ ≤ metricScalarAt ((K n).initialMetric 0) x) →
      (hP5L : ∀ (D ζ : ℝ) (m : ℕ), 0 < ζ → ∃ T : ℝ, ∀ n, ∃ p : CutoffParameters,
        p.delta = q.delta ∧ p.neckRadius = q.neckRadius ∧ p.fixed = q.fixed ∧
        p.recenterConstant = q.recenterConstant ∧ D ≤ p.modelRadius ∧ p.modelAccuracy ≤ ζ ∧
        m ≤ p.modelOrder ∧ ∃ records : ∀ i : Fin (K n).eventCount, T ≤ (K n).time i.succ →
          GeometricCutoffRecord (K n).toHistory i p,
        ∀ i hi b, GC.LongTime.Ch11.linkedCanonicalWindow_C11E ((records i hi).static b)) →
      (hδq : Tendsto q.delta atTop (𝓝 0)) → (hρa : AntitoneOn q.neckRadius (Ici 0)) →
      (hpinchK0 : ∀ n, (K n).EventSlabsPinched phi) →
      (hslabK : ∀ n, (K n).EventSlabsDerivative Ctime (Q n) (Fin.last (K n).eventCount)) →
      ∃ (T₀ : ℕ → ℝ) (p : ℕ → CutoffParameters)
        (recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
          GeometricCutoffRecord (K n).toHistory i (p n)),
      ∀ {j : ∀ n, Fin (K n).eventCount} {t : ℕ → ℝ},
      (hjt : ∀ n, (K n).time (j n).castSucc < t n) → (htj : ∀ n, t n < (K n).time (j n).succ) →
      {yG : ∀ n, ((K n).stage (j n).castSucc).Carrier} →
      (hqR : ∀ n : ℕ, max ((n : ℝ) + 1) (Q n) <
        ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n)) →
      (hnotK : ∀ n, ¬ ∃ (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ)
        (hl : i.succ ≤ (j n).castSucc)
        (A : BackwardPointTrace (K n).toHistory i.succ (j n).castSucc hl (yG n))
        (b : ((K n).toHistory.event i).RetainedBoundaryIndex)
        (x : standardCapWindow (p n).modelRadius),
        A.point i.succ le_rfl hl = ((recordsK n i hi).static b).window x ∧
          ‖x.val‖ < ((n : ℝ) + 1) + 1 ∧
          t n - (K n).time i.succ ≤
            (1 - 1 / ((n : ℝ) + 2)) * (((recordsK n i hi).static b).neck.scale)⁻¹) →
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
      (hbcad : ∀ A Dd : ℝ, 0 < A → 0 < Dd → ∃ C : ℝ, ∀ σ' : ℝ, σ' < 0 → ∀ Dw : ℝ, 0 < Dw →
        ∀ᶠ n in atTop,
        ∀ x₁ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (Dw / Real.sqrt (R n)),
        ∀ x₂ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (Dw / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (v : ℝ) = σ n + σ' / R n →
        ∀ (tr₁ : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
            ((Kh n).activeStage_mono hvt) x₁)
          (tr₂ : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
            ((Kh n).activeStage_mono hvt) x₂),
          metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr₁.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) ≤ A * R n →
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr₁.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt))
              (tr₂.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) <
            ENNReal.ofReal (Dd / Real.sqrt (R n)) →
          metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr₂.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) ≤ C * R n) →
      (hsel : ∀ n, ¬ (Kh n).HasSpatialCanonicalTimeControl ε C1' C2' Ctime' (σ n) (y n)) →
      False := by
  obtain ⟨epsW, hepsW, hB⟩ := false_of_selection_eventSlab_late_P6LT.{u}
  refine ⟨epsW, hepsW, fun ε hε hsmall hεW hεX hεN hεcone => ?_⟩
  obtain ⟨C, hC, hB'⟩ := hB ε hε hsmall hεW hεX hεN hεcone
  refine ⟨C, hC, fun {C1' C2' Ctime'} hC1 hC2 hCt => ?_⟩
  intro Ctime phi hphi K Q q recordsF a₀ ha₀ hHI hP5L hδq hρa hpinchK0 hslabK
  obtain ⟨T₀, p, recordsK, hcanK, hacc, hrad, hord, hscaleK, hδF⟩ :=
    RetainedCoreHistory.exists_lateKdata_of_P5L_antitone_P6M3 Q hP5L hδq hρa
  refine ⟨T₀, p, recordsK, ?_⟩
  intro j t hjt htj yG hqR hnotK Kh hKh σ y R hσ hyG hRn hRpos d hT₀ Tn aSeed haT hsT has pT
    seedTrace L hL hgood hwin hdist hbcad hsel
  exact hB' hC1 hC2 hCt hphi hjt htj recordsF ha₀ hHI hcanK hδF hacc hrad hord hscaleK hpinchK0
    hslabK hqR hnotK Kh hKh σ y R hσ hyG hRn hRpos d hT₀ Tn aSeed haT hsT has pT seedTrace L hL
    hgood hwin hdist hbcad hsel

/-- consumer：W1 narrow tuple 的 S1+S2（`chain_S1_S2_C11RA`）同时给出 `hδq` 与 `hρa`。 -/
example (E : ℕ → ℝ) (hElt : ∀ n, E n < E (n + 1))
    (hEge : ∀ n : ℕ, (n : ℝ) ≤ E (n + 1)) (L : ℕ → CutoffParameters)
    (hpast : ∀ n : ℕ, ∀ t : ℝ, t ≤ E n →
      (L (n + 1)).delta t = (L n).delta t ∧
      (L (n + 1)).neckRadius t = (L n).neckRadius t ∧
      (L (n + 1)).protectedRadius t = (L n).protectedRadius t)
    (hanti : ∀ n : ℕ, AntitoneOn (L n).delta (Ici 0))
    (hradius : ∀ n : ℕ, AntitoneOn (L n).neckRadius (Ici 0))
    (a : ℕ → ℝ) (hafter : ∀ n : ℕ, ∀ t : ℝ, E n < t → (L (n + 1)).delta t = a n)
    (ha : ∀ n : ℕ, a n ≤ 1 / ((n : ℝ) + 2)) (q : CutoffParameters)
    (hqδ : ∀ n : ℕ, ∀ t ∈ Icc (0 : ℝ) (n : ℝ), q.delta t = (L (n + 1)).delta t)
    (hqρ : ∀ n : ℕ, ∀ t ∈ Icc (0 : ℝ) (n : ℝ), q.neckRadius t = (L (n + 1)).neckRadius t) :
    Tendsto q.delta atTop (𝓝 0) ∧ AntitoneOn q.neckRadius (Ici 0) := by
  obtain ⟨-, h2, h3, -, -⟩ := GC.LongTime.Ch11.chain_S1_S2_C11RA E hElt hEge L hpast hanti hradius
    a hafter ha q hqδ hqρ
  exact ⟨h3, h2⟩

/-- consumer：profile 的 `radius_antitone` 就是 `hρa`。 -/
example {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    {δ : ℝ → ℝ} (Hp : GC.LongTime.AnalyticSurgeryProfile F δ) :
    AntitoneOn Hp.parameters.neckRadius (Ici 0) :=
  Hp.radius_antitone

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
