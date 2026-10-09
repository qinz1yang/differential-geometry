import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6BandP6X
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.AdapterAgeObject_P6N

/-!
# D-17 seed normalization：种子尺度重标度 + 在重标度 history 上重跑 selection（O-CH11-P6SEL G4，后缀 `_P6X`）

R-C11-5 D-17：(b) 的反例只给 `R(x) r² → ∞`，不给 `R → ∞`；主形要 `n+1 < R`。本文件在 **selection 之前**
把每个坏种子的 history 抛物重标度 `c := r²`（`RetainedCoreHistory.rescale_P6N`：时间 `÷ c`、度量 `c⁻¹ g`、
`R ↦ c R`、距离 `÷ √c`），于是 `r̃ = 1`、`R̃(x̃) = R(x) r² ≥ k+1`，在重标度 history 上重跑 G1 selection，
得到的坏点 `R̃ ≥ R̃(x̃) ≥ k+1`——**不再有 `R` 有界类**。

* 基本搬运：`rescaleTime_P6X` / `unscaleTime_P6X`、`activeStage_rescaleTime_P6X`（树内
  `rescale_activeStage`）、`scalar_rescale_P6X`（`R̃ = c·R(c·)`）、`edist_rescale_P6X`（`√c⁻¹`）、
  `exists_witness_scale_iff_P6X`（witness 经 `scaleMetric` 双向）、`derivWithin_rescale_iff_P6X`
  （`∂R̃ = c²·∂R`，`Ctime` 不变）、`carrier_transfer_P6X`（stage 指标相等时的 HEq 搬运）；
* 供给搬运：`canonical_rescale_P6X`（S5 ⇒ 重标度 history 的 selector `hcanonical`，`ρ̃ = q.rescale_P6N c`）、
  `derivative_rescale_P6X`（S11 stage 形 ⇒ 重标度 `hderivative`）、`neckRadius_rescale_antitone_P6X`；
* 种子搬运：`trace_transfer_P6X`、`seed_rescale_P6X`（种子点 / 坏点 / 球 / 标量 / 无 witness）；
* **`lateCoreAt_of_normalized_P6X`** / **`canonicalLateCore_of_normalized_P6X`**：S5 + S11 + 缺口 `hPN`
  （重标度 history 上的 selected 坏序列反证，`k+1 ≤ R̃`、`1 ≤ ãSeed`）⇒ (b)。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold NNReal Topology ContDiff ENNReal Pointwise

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open Perelman.CanonicalNeighborhood.FiniteHorn (SpatialCanonicalWitness)

/-! ## 基本搬运 -/

/-- stage 指标相等时，依赖 carrier 的命题沿 HEq 搬运。 -/
theorem carrier_transfer_P6X {n : ℕ} {S : Fin n → OrientedThreeStage.{u}}
    {Pr : ∀ j, (S j).Carrier → Prop} {j j' : Fin n} (h : j = j') {z : (S j).Carrier}
    {z' : (S j').Carrier} (hz : HEq z z') : Pr j z ↔ Pr j' z' := by
  subst h
  obtain rfl := eq_of_heq hz
  exact Iff.rfl

/-- 两点版。 -/
theorem carrier_transfer2_P6X {n : ℕ} {S : Fin n → OrientedThreeStage.{u}}
    {Pr : ∀ j, (S j).Carrier → (S j).Carrier → Prop} {j j' : Fin n} (h : j = j')
    {z w : (S j).Carrier} {z' w' : (S j').Carrier} (hz : HEq z z') (hw : HEq w w') :
    Pr j z w ↔ Pr j' z' w' := by
  subst h
  obtain rfl := eq_of_heq hz
  obtain rfl := eq_of_heq hw
  exact Iff.rfl

/-- witness 经 `scaleMetric c⁻¹` 双向（`scaleMetric c (scaleMetric c⁻¹ g) = g`）。 -/
theorem exists_witness_scale_iff_P6X {P : OrientedThreeStage.{u}} {g : P.Metric} {c : ℝ}
    (hc : 0 < c) {z : P.Carrier} {eps C1 C2 : ℝ} :
    (∃ W : SpatialCanonicalWitness (scaleMetric c⁻¹ (inv_pos.mpr hc) g) eps C1 C2 z,
      W.capTubeHasNeckChart eps) ↔
      ∃ W : SpatialCanonicalWitness g eps C1 C2 z, W.capTubeHasNeckChart eps := by
  constructor
  · rintro ⟨W, hW⟩
    have heq : scaleMetric c hc (scaleMetric c⁻¹ (inv_pos.mpr hc) g) = g := by
      ext x v w
      simp only [scaleMetric_inner]
      rw [← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]
    exact heq ▸ ⟨W.scaleMetric c hc, hW.scaleMetric c hc⟩
  · rintro ⟨W, hW⟩
    exact ⟨W.scaleMetric c⁻¹ (inv_pos.mpr hc), hW.scaleMetric c⁻¹ (inv_pos.mpr hc)⟩

/-- 值版：stage 指标相等时，依赖 carrier 的量沿 HEq 相等。 -/
theorem carrier_congr_P6X {n : ℕ} {S : Fin n → OrientedThreeStage.{u}} {α : Type*}
    (f : ∀ j, (S j).Carrier → (S j).Carrier → α) {j j' : Fin n} (h : j = j')
    {z w : (S j).Carrier} {z' w' : (S j').Carrier} (hz : HEq z z') (hw : HEq w w') :
    f j z w = f j' z' w' := by
  subst h
  obtain rfl := eq_of_heq hz
  obtain rfl := eq_of_heq hw
  rfl

/-- trace 沿首末指标相等与端点 HEq 搬运。 -/
def trace_transfer_P6X {Hh : ObservedHistory.{u}} {f l f' l' : Fin (Hh.eventCount + 1)}
    (hf : f = f') (hl : l = l') {hle : f ≤ l} {hle' : f' ≤ l'} {x : (Hh.stage l).Carrier}
    {x' : (Hh.stage l').Carrier} (hx : HEq x x') (A : BackwardPointTrace Hh f l hle x) :
    BackwardPointTrace Hh f' l' hle' x' := by
  subst hf
  subst hl
  obtain rfl := eq_of_heq hx
  exact A

namespace RetainedCoreHistory

variable (H : RetainedCoreHistory.{u}) {c : ℝ} (hc : 0 < c)

/-- 原时刻 → 重标度时刻（`t ↦ t/c`）。 -/
def rescaleTime_P6X (v : Icc (0 : ℝ) H.toHistory.horizon) :
    Icc (0 : ℝ) (H.rescale_P6N c hc).toHistory.horizon :=
  ⟨(v : ℝ) / c, div_nonneg v.2.1 hc.le, (div_le_div_iff_of_pos_right hc).mpr v.2.2⟩

/-- 重标度时刻 → 原时刻（`t̃ ↦ c t̃`）。 -/
def unscaleTime_P6X (v : Icc (0 : ℝ) (H.rescale_P6N c hc).toHistory.horizon) :
    Icc (0 : ℝ) H.toHistory.horizon :=
  ⟨c * (v : ℝ), mul_nonneg hc.le v.2.1, by
    have h := v.2.2
    change (v : ℝ) ≤ H.horizon / c at h
    rw [le_div_iff₀ hc] at h
    change c * (v : ℝ) ≤ H.horizon
    linarith⟩

theorem rescaleTime_val_P6X (v : Icc (0 : ℝ) H.toHistory.horizon) :
    ((H.rescaleTime_P6X hc v : Icc (0 : ℝ) (H.rescale_P6N c hc).toHistory.horizon) : ℝ) =
      (v : ℝ) / c := rfl

theorem unscale_rescaleTime_P6X (v : Icc (0 : ℝ) H.toHistory.horizon) :
    H.unscaleTime_P6X hc (H.rescaleTime_P6X hc v) = v :=
  Subtype.ext (by
    change c * ((v : ℝ) / c) = v
    field_simp)

theorem rescale_unscaleTime_P6X (v : Icc (0 : ℝ) (H.rescale_P6N c hc).toHistory.horizon) :
    H.rescaleTime_P6X hc (H.unscaleTime_P6X hc v) = v :=
  Subtype.ext (by
    change c * (v : ℝ) / c = v
    field_simp)

/-- 重标度不改 `activeStage`（树内 `rescale_activeStage`）。 -/
theorem activeStage_rescaleTime_P6X (v : Icc (0 : ℝ) H.toHistory.horizon) :
    (H.rescale_P6N c hc).toHistory.activeStage (H.rescaleTime_P6X hc v) =
      H.toHistory.activeStage v :=
  H.toHistory.rescale_activeStage c hc v

theorem activeStage_unscale_P6X (v : Icc (0 : ℝ) (H.rescale_P6N c hc).toHistory.horizon) :
    (H.rescale_P6N c hc).toHistory.activeStage v =
      H.toHistory.activeStage (H.unscaleTime_P6X hc v) := by
  have h := H.activeStage_rescaleTime_P6X hc (H.unscaleTime_P6X hc v)
  rwa [H.rescale_unscaleTime_P6X hc v] at h

/-- `R̃(t, z) = c · R(c t, z)`。 -/
theorem scalar_rescale_P6X (j : Fin (H.eventCount + 1)) (t : ℝ) (z : (H.stage j).Carrier) :
    metricScalarAt ((H.rescale_P6N c hc).toHistory.stageMetric j t) z =
      c * metricScalarAt (H.toHistory.stageMetric j (c * t)) z := by
  rw [H.rescale_P6N_stageMetric c hc]
  exact (metricScalarAt_scaleMetric _ _ _ _).trans (congrArg (· * _) (inv_inv c))

/-- 距离 `÷ √c`。 -/
theorem edist_rescale_P6X (j : Fin (H.eventCount + 1)) (t : ℝ) (x y : (H.stage j).Carrier) :
    riemannianEDistOf ((H.rescale_P6N c hc).toHistory.stageMetric j t) x y =
      ENNReal.ofReal (Real.sqrt c⁻¹) *
        riemannianEDistOf (H.toHistory.stageMetric j (c * t)) x y := by
  rw [H.rescale_P6N_stageMetric c hc]
  exact edistOf_scale _ _ _ _ _

variable {H} in
/-- witness：重标度 stage 度量 ⇔ 原 stage 度量（同指标、同点）。 -/
theorem witness_rescale_iff_P6X {j : Fin (H.eventCount + 1)} {t : ℝ} {z : (H.stage j).Carrier}
    {eps C1 C2 : ℝ} :
    (∃ W : SpatialCanonicalWitness ((H.rescale_P6N c hc).toHistory.stageMetric j t) eps C1 C2 z,
      W.capTubeHasNeckChart eps) ↔
      ∃ W : SpatialCanonicalWitness (H.toHistory.stageMetric j (c * t)) eps C1 C2 z,
        W.capTubeHasNeckChart eps := by
  rw [H.rescale_P6N_stageMetric c hc]
  exact exists_witness_scale_iff_P6X hc

variable {H} in
/-- 时间导数：`∂R̃(t) = c² ∂R(c t)`，`Ctime` 不变。 -/
theorem derivWithin_rescale_iff_P6X {j : Fin (H.eventCount + 1)} {t : ℝ}
    {z : (H.stage j).Carrier} {Ctime : ℝ≥0} :
    |derivWithin (fun s => metricScalarAt ((H.rescale_P6N c hc).toHistory.stageMetric j s) z)
        (Iic t) t| ≤
        Ctime * metricScalarAt ((H.rescale_P6N c hc).toHistory.stageMetric j t) z ^ 2 ↔
      |derivWithin (fun s => metricScalarAt (H.toHistory.stageMetric j s) z) (Iic (c * t))
          (c * t)| ≤
        Ctime * metricScalarAt (H.toHistory.stageMetric j (c * t)) z ^ 2 := by
  have hfun : (fun s => metricScalarAt ((H.rescale_P6N c hc).toHistory.stageMetric j s) z) =
      fun s => c • (fun u => metricScalarAt (H.toHistory.stageMetric j u) z) (c * s) := by
    funext s
    rw [H.scalar_rescale_P6X hc, smul_eq_mul]
  rw [hfun, derivWithin_fun_const_smul_field,
    derivWithin_comp_mul_left c (fun u => metricScalarAt (H.toHistory.stageMetric j u) z),
    LinearOrderedField.smul_Iic hc, H.scalar_rescale_P6X hc, smul_eq_mul, smul_eq_mul]
  set D := derivWithin (fun u => metricScalarAt (H.toHistory.stageMetric j u) z)
    (Iic (c * t)) (c * t)
  set Rz := metricScalarAt (H.toHistory.stageMetric j (c * t)) z
  have hc2 : 0 < c ^ 2 := by positivity
  rw [show |c * (c * D)| = c ^ 2 * |D| by
      rw [abs_mul, abs_mul, abs_of_pos hc]; ring,
    show (Ctime : ℝ) * (c * Rz) ^ 2 = c ^ 2 * (Ctime * Rz ^ 2) by ring]
  exact mul_le_mul_iff_of_pos_left hc2

/-! ## 供给搬运（selector 的 `hcanonical` / `hderivative`） -/

/-- 重标度后 neck 半径 `ρ̃(t) = ρ(c t)/√c` 仍 antitone。 -/
theorem neckRadius_rescale_antitone_P6X {q : CutoffParameters}
    (hanti : AntitoneOn q.neckRadius (Ici 0)) :
    AntitoneOn (q.rescale_P6N c hc).neckRadius (Ici 0) := by
  intro a ha b hb hab
  change q.neckRadius (c * b) / Real.sqrt c ≤ q.neckRadius (c * a) / Real.sqrt c
  have ha' : c * a ∈ Ici (0 : ℝ) := mul_nonneg hc.le ha
  have hb' : c * b ∈ Ici (0 : ℝ) := mul_nonneg hc.le hb
  exact div_le_div_of_nonneg_right (hanti ha' hb' (mul_le_mul_of_nonneg_left hab hc.le))
    (Real.sqrt_nonneg c)

/-- `(ρ̃(t)²)⁻¹ = c · (ρ(c t)²)⁻¹`。 -/
theorem neckRadius_rescale_inv_sq_P6X (q : CutoffParameters) (t : ℝ) :
    ((q.rescale_P6N c hc).neckRadius t ^ 2)⁻¹ = c * (q.neckRadius (c * t) ^ 2)⁻¹ := by
  change ((q.neckRadius (c * t) / Real.sqrt c) ^ 2)⁻¹ = _
  rw [div_pow, Real.sq_sqrt hc.le, inv_div, div_eq_mul_inv]

/-- **S5 形 canonical 供给 ⇒ 重标度 history 的 selector `hcanonical`**（阈值 `ρ̃ = q.rescale_P6N c`）。 -/
theorem canonical_rescale_P6X {q : CutoffParameters} {eps C1 C2 : ℝ}
    (hcan : ∀ (v : Icc (0 : ℝ) H.toHistory.horizon) (z : (H.toHistory.stageAt v).Carrier),
      (q.neckRadius v ^ 2)⁻¹ <
        metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage v) v) z →
      ∃ W : SpatialCanonicalWitness (H.toHistory.stageMetric (H.toHistory.activeStage v) v)
        eps C1 C2 z, W.capTubeHasNeckChart eps)
    (v : Icc (0 : ℝ) (H.rescale_P6N c hc).toHistory.horizon)
    (z : ((H.rescale_P6N c hc).toHistory.stageAt v).Carrier)
    (hR : ((q.rescale_P6N c hc).neckRadius v ^ 2)⁻¹ < metricScalarAt
      ((H.rescale_P6N c hc).toHistory.stageMetric
        ((H.rescale_P6N c hc).toHistory.activeStage v) v) z) :
    ∃ W : SpatialCanonicalWitness ((H.rescale_P6N c hc).toHistory.stageMetric
        ((H.rescale_P6N c hc).toHistory.activeStage v) v) eps C1 C2 z,
      W.capTubeHasNeckChart eps := by
  have hj := H.activeStage_unscale_P6X hc v
  have hz : HEq z (cast (congrArg (fun j => (H.stage j).Carrier) hj) z) := (cast_heq _ _).symm
  refine (H.witness_rescale_iff_P6X hc (j := (H.rescale_P6N c hc).toHistory.activeStage v)
    (t := v) (z := z)).mpr ?_
  rw [H.scalar_rescale_P6X hc ((H.rescale_P6N c hc).toHistory.activeStage v) v z,
    RetainedCoreHistory.neckRadius_rescale_inv_sq_P6X hc q] at hR
  have hR1 := (mul_lt_mul_iff_of_pos_left hc).mp hR
  have hR2 := (carrier_transfer_P6X (S := H.stage)
    (Pr := fun j z => (q.neckRadius (c * v) ^ 2)⁻¹ <
      metricScalarAt (H.toHistory.stageMetric j (c * v)) z) hj hz).mp hR1
  exact (carrier_transfer_P6X (S := H.stage)
    (Pr := fun j z => ∃ W : SpatialCanonicalWitness (H.toHistory.stageMetric j (c * v)) eps C1 C2 z,
      W.capTubeHasNeckChart eps) hj hz).mpr (hcan (H.unscaleTime_P6X hc v) _ hR2)

/-- **S11 stage 形 ⇒ 重标度 history 的 selector `hderivative`**（`Ctime` 不变）。 -/
theorem derivative_rescale_P6X {q : CutoffParameters} {Ctime : ℝ≥0}
    (hder : ∀ (v : Icc (0 : ℝ) H.toHistory.horizon) (z : (H.toHistory.stageAt v).Carrier),
      H.toHistory.time (H.toHistory.activeStage v) < (v : ℝ) → (v : ℝ) < H.toHistory.horizon →
      (q.neckRadius v ^ 2)⁻¹ <
        metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage v) v) z →
      |derivWithin (fun t => metricScalarAt (H.toHistory.stageMetric
          (H.toHistory.activeStage v) t) z) (Iic (v : ℝ)) v| ≤
        Ctime * metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage v) v) z ^ 2)
    (v : Icc (0 : ℝ) (H.rescale_P6N c hc).toHistory.horizon)
    (z : ((H.rescale_P6N c hc).toHistory.stageAt v).Carrier)
    (hlo : (H.rescale_P6N c hc).toHistory.time ((H.rescale_P6N c hc).toHistory.activeStage v) <
      (v : ℝ))
    (hhi : (v : ℝ) < (H.rescale_P6N c hc).toHistory.horizon)
    (hR : ((q.rescale_P6N c hc).neckRadius v ^ 2)⁻¹ < metricScalarAt
      ((H.rescale_P6N c hc).toHistory.stageMetric
        ((H.rescale_P6N c hc).toHistory.activeStage v) v) z) :
    |derivWithin (fun t => metricScalarAt ((H.rescale_P6N c hc).toHistory.stageMetric
        ((H.rescale_P6N c hc).toHistory.activeStage v) t) z) (Iic (v : ℝ)) v| ≤
      Ctime * metricScalarAt ((H.rescale_P6N c hc).toHistory.stageMetric
        ((H.rescale_P6N c hc).toHistory.activeStage v) v) z ^ 2 := by
  have hj := H.activeStage_unscale_P6X hc v
  have hz : HEq z (cast (congrArg (fun j => (H.stage j).Carrier) hj) z) := (cast_heq _ _).symm
  refine (H.derivWithin_rescale_iff_P6X hc (j := (H.rescale_P6N c hc).toHistory.activeStage v)
    (t := v) (z := z) (Ctime := Ctime)).mpr ?_
  rw [H.scalar_rescale_P6X hc ((H.rescale_P6N c hc).toHistory.activeStage v) v z,
    RetainedCoreHistory.neckRadius_rescale_inv_sq_P6X hc q] at hR
  have hR1 := (mul_lt_mul_iff_of_pos_left hc).mp hR
  have hR2 := (carrier_transfer_P6X (S := H.stage)
    (Pr := fun j z => (q.neckRadius (c * v) ^ 2)⁻¹ <
      metricScalarAt (H.toHistory.stageMetric j (c * v)) z) hj hz).mp hR1
  have hlo' : H.toHistory.time (H.toHistory.activeStage (H.unscaleTime_P6X hc v)) < c * v := by
    rw [← hj]
    change H.time _ / c < (v : ℝ) at hlo
    rw [div_lt_iff₀ hc] at hlo
    change H.time _ < c * (v : ℝ)
    linarith
  have hhi' : c * (v : ℝ) < H.toHistory.horizon := by
    change (v : ℝ) < H.horizon / c at hhi
    rw [lt_div_iff₀ hc] at hhi
    change c * (v : ℝ) < H.horizon
    linarith
  exact (carrier_transfer_P6X (S := H.stage)
    (Pr := fun j z => |derivWithin (fun s => metricScalarAt (H.toHistory.stageMetric j s) z)
        (Iic (c * v)) (c * v)| ≤ Ctime * metricScalarAt (H.toHistory.stageMetric j (c * v)) z ^ 2)
    hj hz).mpr (hder (H.unscaleTime_P6X hc v) _ hlo' hhi' hR2)

/-! ## 种子搬运 -/

theorem rescaleTime_mono_P6X {a T : Icc (0 : ℝ) H.toHistory.horizon} (h : a ≤ T) :
    H.rescaleTime_P6X hc a ≤ H.rescaleTime_P6X hc T := by
  change (a : ℝ) / c ≤ (T : ℝ) / c
  exact div_le_div_of_nonneg_right h hc.le

theorem mul_rescaleTime_P6X (v : Icc (0 : ℝ) H.toHistory.horizon) :
    c * ((H.rescaleTime_P6X hc v : Icc (0 : ℝ) (H.rescale_P6N c hc).toHistory.horizon) : ℝ) =
      (v : ℝ) := by
  change c * ((v : ℝ) / c) = v
  field_simp

/-- 原 stage 点 → 重标度 stage 点（同一 carrier，沿 `activeStage` 等式 cast）。 -/
def castRescale_P6X (v : Icc (0 : ℝ) H.toHistory.horizon) (z : (H.toHistory.stageAt v).Carrier) :
    ((H.rescale_P6N c hc).toHistory.stageAt (H.rescaleTime_P6X hc v)).Carrier :=
  cast (congrArg (fun j => (H.stage j).Carrier) (H.activeStage_rescaleTime_P6X hc v).symm) z

theorem heq_castRescale_P6X (v : Icc (0 : ℝ) H.toHistory.horizon)
    (z : (H.toHistory.stageAt v).Carrier) : HEq (H.castRescale_P6X hc v z) z :=
  cast_heq _ _

/-- 标量：`R̃(ṽ, z̃) = c · R(v, z)`。 -/
theorem scalar_castRescale_P6X (v : Icc (0 : ℝ) H.toHistory.horizon)
    (z : (H.toHistory.stageAt v).Carrier) :
    metricScalarAt ((H.rescale_P6N c hc).toHistory.stageMetric
        ((H.rescale_P6N c hc).toHistory.activeStage (H.rescaleTime_P6X hc v))
        (H.rescaleTime_P6X hc v)) (H.castRescale_P6X hc v z) =
      c * metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage v) v) z := by
  rw [H.scalar_rescale_P6X hc _ _ (H.castRescale_P6X hc v z), H.mul_rescaleTime_P6X hc v]
  congr 1
  exact carrier_congr_P6X (S := H.stage)
    (fun j z _ => metricScalarAt (H.toHistory.stageMetric j v) z)
    (H.activeStage_rescaleTime_P6X hc v) (H.heq_castRescale_P6X hc v z)
    (H.heq_castRescale_P6X hc v z)

/-- 距离：`d̃(p̃, x̃) = √c⁻¹ · d(p, x)`。 -/
theorem edist_castRescale_P6X (v : Icc (0 : ℝ) H.toHistory.horizon)
    (p x : (H.toHistory.stageAt v).Carrier) :
    riemannianEDistOf ((H.rescale_P6N c hc).toHistory.stageMetric
        ((H.rescale_P6N c hc).toHistory.activeStage (H.rescaleTime_P6X hc v))
        (H.rescaleTime_P6X hc v)) (H.castRescale_P6X hc v p) (H.castRescale_P6X hc v x) =
      ENNReal.ofReal (Real.sqrt c⁻¹) *
        riemannianEDistOf (H.toHistory.stageMetric (H.toHistory.activeStage v) v) p x := by
  rw [H.edist_rescale_P6X hc _ _ (H.castRescale_P6X hc v p) (H.castRescale_P6X hc v x),
    H.mul_rescaleTime_P6X hc v]
  congr 1
  exact carrier_congr_P6X (S := H.stage)
    (fun j p x => riemannianEDistOf (H.toHistory.stageMetric j v) p x)
    (H.activeStage_rescaleTime_P6X hc v) (H.heq_castRescale_P6X hc v p)
    (H.heq_castRescale_P6X hc v x)

/-- 球：`x ∈ B(p, ρ)` ⇒ `x̃ ∈ B̃(p̃, ρ/√c)`。 -/
theorem ball_castRescale_P6X (v : Icc (0 : ℝ) H.toHistory.horizon)
    (p x : (H.toHistory.stageAt v).Carrier) {ρ : ℝ}
    (hx : x ∈ riemannianBallOf (H.toHistory.stageMetric (H.toHistory.activeStage v) v) p ρ) :
    H.castRescale_P6X hc v x ∈ riemannianBallOf ((H.rescale_P6N c hc).toHistory.stageMetric
        ((H.rescale_P6N c hc).toHistory.activeStage (H.rescaleTime_P6X hc v))
        (H.rescaleTime_P6X hc v)) (H.castRescale_P6X hc v p) (ρ / Real.sqrt c) := by
  change riemannianEDistOf _ _ _ < _
  have hx' : riemannianEDistOf (H.toHistory.stageMetric (H.toHistory.activeStage v) v) p x <
      ENNReal.ofReal ρ := hx
  rw [H.edist_castRescale_P6X hc v p x]
  have hρ : 0 < ρ := by
    by_contra hρ
    rw [ENNReal.ofReal_of_nonpos (not_lt.mp hρ)] at hx'
    exact ENNReal.not_lt_zero hx'
  have hs : 0 < Real.sqrt c⁻¹ := Real.sqrt_pos.mpr (inv_pos.mpr hc)
  have heq : ENNReal.ofReal (ρ / Real.sqrt c) =
      ENNReal.ofReal (Real.sqrt c⁻¹) * ENNReal.ofReal ρ := by
    rw [← ENNReal.ofReal_mul hs.le, Real.sqrt_inv, div_eq_mul_inv, mul_comm]
  rw [heq]
  have hm := ENNReal.mul_lt_mul_left (ENNReal.ofReal_pos.mpr hs).ne' ENNReal.ofReal_ne_top hx'
  rwa [mul_comm, mul_comm (ENNReal.ofReal ρ)] at hm

/-- 无 witness 的坏点重标度后仍无 witness。 -/
theorem noWitness_castRescale_P6X (v : Icc (0 : ℝ) H.toHistory.horizon)
    (x : (H.toHistory.stageAt v).Carrier) {eps C1 C2 : ℝ}
    (h : ¬ ∃ W : SpatialCanonicalWitness (H.toHistory.stageMetric (H.toHistory.activeStage v) v)
      eps C1 C2 x, W.capTubeHasNeckChart eps) :
    ¬ ∃ W : SpatialCanonicalWitness ((H.rescale_P6N c hc).toHistory.stageMetric
        ((H.rescale_P6N c hc).toHistory.activeStage (H.rescaleTime_P6X hc v))
        (H.rescaleTime_P6X hc v)) eps C1 C2 (H.castRescale_P6X hc v x),
      W.capTubeHasNeckChart eps := by
  intro hW
  have h1 := (H.witness_rescale_iff_P6X hc (t := H.rescaleTime_P6X hc v)
    (z := H.castRescale_P6X hc v x)).mp hW
  rw [H.mul_rescaleTime_P6X hc v] at h1
  exact h ((carrier_transfer_P6X (S := H.stage)
    (Pr := fun j z => ∃ W : SpatialCanonicalWitness (H.toHistory.stageMetric j v) eps C1 C2 z,
      W.capTubeHasNeckChart eps)
    (H.activeStage_rescaleTime_P6X hc v) (H.heq_castRescale_P6X hc v x)).mp h1)

/-- 种子 trace 重标度。 -/
def seedTrace_rescale_P6X {a T : Icc (0 : ℝ) H.toHistory.horizon} (haT : a ≤ T)
    {p : (H.toHistory.stageAt T).Carrier}
    (A : BackwardPointTrace H.toHistory (H.toHistory.activeStage a) (H.toHistory.activeStage T)
      (H.toHistory.activeStage_mono haT) p) :
    BackwardPointTrace (H.rescale_P6N c hc).toHistory
      ((H.rescale_P6N c hc).toHistory.activeStage (H.rescaleTime_P6X hc a))
      ((H.rescale_P6N c hc).toHistory.activeStage (H.rescaleTime_P6X hc T))
      ((H.rescale_P6N c hc).toHistory.activeStage_mono (H.rescaleTime_mono_P6X hc haT))
      (H.castRescale_P6X hc T p) :=
  trace_transfer_P6X (Hh := (H.rescale_P6N c hc).toHistory)
    (H.activeStage_rescaleTime_P6X hc a).symm
    (H.activeStage_rescaleTime_P6X hc T).symm (H.heq_castRescale_P6X hc T p).symm
    (H.traceToRescale_P6N c hc A)

end RetainedCoreHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace GC.LongTime.Ch11

universe u

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Geometry.Collapse

/-- **(b) 于单个 `A > 0` ⇐ S5 + S11 + 规范化 selected 反证 `hPN`**：`¬(b)(A)` 对 `K₁ = T = k+1` 取坏种子，
每个种子 history 以 `c := r²` 重标度（`r̃ = 1`、`R̃(x̃) = R(x) r² ≥ k+1`），在重标度 history 上跑 G1 selection，
输出喂 `hPN`（`k+1 ≤ R̃`、`1 ≤ ãSeed`、`k+1 ≤ c·T̃`）。 -/
theorem lateCoreAt_of_normalized_P6X {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters} {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
    (hanti : AntitoneOn q.neckRadius (Ici 0))
    (hcan : HistoryCanonicalSupply_C11S F q.neckRadius ε C1 C2)
    (hder : TimeDerivativeSupply_C11E F q.neckRadius Ctime)
    (hPN : ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
      let Kh : ℕ → ObservedHistory.{u} := fun k =>
        ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory
      ∀ (Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier),
        (∀ k : ℕ, (k : ℝ) + 1 ≤ c k * (Tn k : ℝ)) →
      ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
        (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ 2) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
      ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
          ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
        (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
        (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
        (∀ k, R k =
          metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
        (∀ k, 0 < R k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) →
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
      False)
    {A : ℝ} (hA : 0 < A) :
    LargerBallCanonicalLateAt_P6A F ε C1 C2 A := by
  by_contra hcon
  have hk : ∀ k : ℕ, ∃ (n : ℕ) (t : Icc (0 : ℝ) (F.tower.history n).toHistory.horizon)
      (p : ((F.tower.history n).toHistory.stageAt t).Carrier) (r : ℝ)
      (x : ((F.tower.history n).toHistory.stageAt t).Carrier),
      (k : ℝ) + 1 ≤ (t : ℝ) ∧ 2 * r ^ 2 < (t : ℝ) ∧
      hasSmallParabolicCurvature (F.tower.history n).toHistory t p r ∧
      x ∈ riemannianBallOf ((F.tower.history n).toHistory.stageMetric
        ((F.tower.history n).toHistory.activeStage t) t) p (A * r) ∧
      ((k : ℝ) + 1) * (r ^ 2)⁻¹ ≤ metricScalarAt ((F.tower.history n).toHistory.stageMetric
        ((F.tower.history n).toHistory.activeStage t) t) x ∧
      ¬ ∃ W : SpatialCanonicalWitness ((F.tower.history n).toHistory.stageMetric
          ((F.tower.history n).toHistory.activeStage t) t) ε C1 C2 x,
        W.capTubeHasNeckChart ε := by
    intro k
    by_contra hk
    refine hcon ⟨(k : ℝ) + 1, (k : ℝ) + 1, by positivity, by positivity, ?_⟩
    intro n _ t p r hT ht hs _ x hx hK
    by_contra hW
    exact hk ⟨n, t, p, r, x, hT, ht, hs, hx, hK, hW⟩
  choose ind Tn pT r x hlate htime hsmall hx hK hW using hk
  have hr : ∀ k, 0 < r k := fun k => (hsmall k).1
  have hseed : ∀ k, ∃ (a : Icc (0 : ℝ) (F.tower.history (ind k)).toHistory.horizon)
      (hat : a ≤ Tn k), (a : ℝ) = (Tn k : ℝ) - r k ^ 2 ∧
      Nonempty (BackwardPointTrace (F.tower.history (ind k)).toHistory
        ((F.tower.history (ind k)).toHistory.activeStage a)
        ((F.tower.history (ind k)).toHistory.activeStage (Tn k))
        ((F.tower.history (ind k)).toHistory.activeStage_mono hat) (pT k)) := fun k => by
    obtain ⟨hrk, a, hat, ha, htr⟩ := hsmall k
    have hp : pT k ∈ riemannianBallOf ((F.tower.history (ind k)).toHistory.stageMetric
        ((F.tower.history (ind k)).toHistory.activeStage (Tn k)) (Tn k)) (pT k) (r k) := by
      change riemannianEDistOf _ (pT k) (pT k) < ENNReal.ofReal (r k)
      rw [riemannianEDistOf_self]
      exact ENNReal.ofReal_pos.mpr hrk
    obtain ⟨tr, -⟩ := htr (pT k) hp
    exact ⟨a, hat, ha, ⟨tr⟩⟩
  choose aSeed haT hclock hst using hseed
  have hc : ∀ k, 0 < r k ^ 2 := fun k => pow_pos (hr k) 2
  have hsq : ∀ k, Real.sqrt (r k ^ 2) = r k := fun k => Real.sqrt_sq (hr k).le
  have hRx : ∀ k : ℕ, (k : ℝ) + 1 ≤ r k ^ 2 * metricScalarAt
      ((F.tower.history (ind k)).toHistory.stageMetric
        ((F.tower.history (ind k)).toHistory.activeStage (Tn k)) (Tn k)) (x k) := by
    intro k
    have := mul_le_mul_of_nonneg_left (hK k) (hc k).le
    rwa [← mul_assoc, mul_comm (r k ^ 2), mul_assoc, mul_inv_cancel₀ (hc k).ne', mul_one] at this
  have hRx' : ∀ k : ℕ, (k : ℝ) + 1 ≤ metricScalarAt
      (((F.tower.history (ind k)).rescale_P6N (r k ^ 2) (hc k)).toHistory.stageMetric
        (((F.tower.history (ind k)).rescale_P6N (r k ^ 2) (hc k)).toHistory.activeStage
          ((F.tower.history (ind k)).rescaleTime_P6X (hc k) (Tn k)))
        ((F.tower.history (ind k)).rescaleTime_P6X (hc k) (Tn k)))
      ((F.tower.history (ind k)).castRescale_P6X (hc k) (Tn k) (x k)) := fun k => by
    rw [(F.tower.history (ind k)).scalar_castRescale_P6X (hc k)]
    exact hRx k
  have hxb : ∀ k, (F.tower.history (ind k)).castRescale_P6X (hc k) (Tn k) (x k) ∈
      riemannianBallOf
        (((F.tower.history (ind k)).rescale_P6N (r k ^ 2) (hc k)).toHistory.stageMetric
        (((F.tower.history (ind k)).rescale_P6N (r k ^ 2) (hc k)).toHistory.activeStage
          ((F.tower.history (ind k)).rescaleTime_P6X (hc k) (Tn k)))
        ((F.tower.history (ind k)).rescaleTime_P6X (hc k) (Tn k)))
      ((F.tower.history (ind k)).castRescale_P6X (hc k) (Tn k) (pT k)) (A * 1) := fun k => by
    have h := (F.tower.history (ind k)).ball_castRescale_P6X (hc k) (Tn k) (pT k) (x k) (hx k)
    rwa [hsq k, mul_div_assoc, div_self (hr k).ne'] at h
  have hclock' : ∀ k, (((F.tower.history (ind k)).rescaleTime_P6X (hc k) (aSeed k) :
      Icc (0 : ℝ) ((F.tower.history (ind k)).rescale_P6N (r k ^ 2) (hc k)).toHistory.horizon) :
        ℝ) = ((F.tower.history (ind k)).rescaleTime_P6X (hc k) (Tn k) : ℝ) - 1 ^ 2 := fun k => by
    change (aSeed k : ℝ) / r k ^ 2 = (Tn k : ℝ) / r k ^ 2 - 1 ^ 2
    rw [hclock k, sub_div, div_self (hc k).ne', one_pow]
  have hsel := ObservedHistory.selection_of_bad_sequence_P6X
    (Kh := fun k => ((F.tower.history (ind k)).rescale_P6N (r k ^ 2) (hc k)).toHistory)
    (fun k => q.rescale_P6N (r k ^ 2) (hc k)) le_rfl le_rfl le_rfl
    (fun k => RetainedCoreHistory.neckRadius_rescale_antitone_P6X (hc k) hanti)
    (fun k => (F.tower.history (ind k)).canonical_rescale_P6X (hc k) (hcan (ind k)))
    (fun k => (F.tower.history (ind k)).derivative_rescale_P6X (hc k)
      (fun v z hlo hhi hR =>
        stageDerivative_of_timeDerivativeSupply_P6X hder (ind k) v z hlo hhi hR))
    (fun k => (F.tower.history (ind k)).rescaleTime_P6X (hc k) (Tn k))
    (fun k => (F.tower.history (ind k)).castRescale_P6X (hc k) (Tn k) (pT k))
    (fun _ => 1) A (fun _ => one_pos) hA
    (fun k => (F.tower.history (ind k)).rescaleTime_P6X (hc k) (aSeed k))
    (fun k => (F.tower.history (ind k)).rescaleTime_mono_P6X (hc k) (haT k)) hclock'
    (fun k => (F.tower.history (ind k)).seedTrace_rescale_P6X (hc k) (haT k) (hst k).some)
    (fun k => (F.tower.history (ind k)).castRescale_P6X (hc k) (Tn k) (x k)) hxb
    (fun k => lt_of_lt_of_le (by positivity) (hRx' k))
    (fun k hG => (F.tower.history (ind k)).noWitness_castRescale_P6X (hc k) (Tn k) (x k) (hW k)
      hG.1)
    (tendsto_atTop_mono (fun k : ℕ => by rw [one_pow, mul_one]; linarith [hRx' k])
      tendsto_natCast_atTop_atTop)
  obtain ⟨σ, y, R, hsT, has, L, hRdef, hRpos, hRle, -, hL, hbad, hgood, hwin, hwin', hroom,
    hradii⟩ := hsel
  refine hPN ind (fun k => r k ^ 2) hc
    (fun k => (F.tower.history (ind k)).rescaleTime_P6X (hc k) (Tn k))
    (fun k => (F.tower.history (ind k)).castRescale_P6X (hc k) (Tn k) (pT k))
    (fun k => by rw [(F.tower.history (ind k)).mul_rescaleTime_P6X (hc k)]; exact hlate k)
    (fun k => (F.tower.history (ind k)).rescaleTime_P6X (hc k) (aSeed k))
    (fun k => (F.tower.history (ind k)).rescaleTime_mono_P6X (hc k) (haT k)) hclock'
    (fun k => ?_)
    (fun k => (F.tower.history (ind k)).seedTrace_rescale_P6X (hc k) (haT k) (hst k).some)
    σ y R hsT has L hRdef hRpos (fun k => (hRx' k).trans (hRle k)) hL hbad hgood hwin hwin' hroom
    hradii
  rw [hclock' k]
  change 1 ≤ (Tn k : ℝ) / r k ^ 2 - 1 ^ 2
  rw [le_sub_iff_add_le, le_div_iff₀ (hc k)]
  linarith [htime k]

/-- **(b) 最小合同 ⇐ S5 + S11 + 规范化 selected 反证 `hPN`**（`hPN` 与 `A` 无关）。 -/
theorem canonicalLateCore_of_normalized_P6X {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters} {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
    (hanti : AntitoneOn q.neckRadius (Ici 0))
    (hcan : HistoryCanonicalSupply_C11S F q.neckRadius ε C1 C2)
    (hder : TimeDerivativeSupply_C11E F q.neckRadius Ctime)
    (hPN : ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
      let Kh : ℕ → ObservedHistory.{u} := fun k =>
        ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory
      ∀ (Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier),
        (∀ k : ℕ, (k : ℝ) + 1 ≤ c k * (Tn k : ℝ)) →
      ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
        (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ 2) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
      ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
          ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
        (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
        (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
        (∀ k, R k =
          metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
        (∀ k, 0 < R k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) →
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
      False) :
    CanonicalLateCore_P6X F ε C1 C2 :=
  fun _ hA => lateCoreAt_of_normalized_P6X hanti hcan hder hPN hA

end GC.LongTime.Ch11
