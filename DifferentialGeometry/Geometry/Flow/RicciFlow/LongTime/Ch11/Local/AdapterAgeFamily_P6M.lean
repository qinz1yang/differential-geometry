import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.AdapterAgeRecord_P6M
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalNeighborhoodContinuationLeaves

/-!
# G3c（AD-age 收尾，part 3）：canonical record family 与 `CapWindowPoint` 的 transport（`_P6M`）

`RetainedCoreHistory` 层（`(H.rescale_P6N μ).toHistory = H.toHistory.rescale μ`，`rfl`）：
* **`IsCanonicalCutoffRecordFamily.rescale_P6M`**：records 逐个 `GeometricCutoffRecord.rescale_P6M`；
  五个模型等式字段原样（`CutoffParameters.rescale_P6N` 不动模型数据）、`hasCanonicalWindow`
  由 part 1、`δ` 界原样（`delta' (T/μ) = delta T`）、`ρ` 界 `ρ₀ ↦ ρ₀/√μ`。
* `hasCanonicalCutoffRecords_rescale_P6M`（存在形，同上）。
* **`capWindowPoint_rescale_iff_P6M`**：`CapWindowPoint` 在重标度 history 的时刻 `t/μ` ⇔ 原 history
  的时刻 `t`（`Dcap`、`θcap` 不变；trace 用 G3a `traceOfRescale_P6N` / `traceToRescale_P6N`，
  `window` 不变，`t/μ − T/μ ≤ θ (μ s)⁻¹ ⇔ t − T ≤ θ s⁻¹`）。
-/

set_option autoImplicit false

noncomputable section

open Set

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace RetainedCoreHistory

variable {H : RetainedCoreHistory.{u}} {p : CutoffParameters}

/-- **`_P6M`**：canonical cutoff record family 的抛物重标度（`ρ₀ ↦ ρ₀/√μ`，其余界原样）。 -/
theorem IsCanonicalCutoffRecordFamily.rescale_P6M {p₀ : CutoffParameters} {δ₀ ρ₀ : ℝ}
    {records : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i p}
    (hrec : H.IsCanonicalCutoffRecordFamily p₀ δ₀ ρ₀ records) (μ : ℝ) (hμ : 0 < μ) :
    (H.rescale_P6N μ hμ).IsCanonicalCutoffRecordFamily p₀ δ₀ (ρ₀ / Real.sqrt μ)
      (fun i => (records i).rescale_P6M μ hμ) := by
  have h := hrec
  obtain ⟨hf, hD, hm, hε, hc, hcan, hδ, hρ⟩ := h
  refine ⟨hf, hD, hm, hε, hc,
    fun i b => ((records i).static b).hasCanonicalWindow_rescale_P6M (hcan i b) μ hμ,
    fun i => ?_, fun i => ?_⟩
  · exact (p.rescale_P6N_eval μ hμ (H.time i.succ)).1.trans_le (hδ i)
  · exact (p.rescale_P6N_eval μ hμ (H.time i.succ)).2.1.trans_le
      (div_le_div_of_nonneg_right (hρ i) (Real.sqrt_nonneg μ))

/-- `hasCanonicalCutoffRecords` 形：`(p, records) ↦ (p.rescale_P6N μ, records.rescale_P6M μ)`。 -/
theorem hasCanonicalCutoffRecords_rescale_P6M {p₀ : CutoffParameters} {δ₀ ρ₀ : ℝ}
    (h : H.hasCanonicalCutoffRecords p₀ δ₀ ρ₀) (μ : ℝ) (hμ : 0 < μ) :
    (H.rescale_P6N μ hμ).hasCanonicalCutoffRecords p₀ δ₀ (ρ₀ / Real.sqrt μ) := by
  have h' := (H.hasCanonicalCutoffRecords_iff_exists_isCanonicalCutoffRecordFamily p₀ δ₀ ρ₀).mp h
  obtain ⟨q, records, hrec⟩ := h'
  exact ((H.rescale_P6N μ hμ).hasCanonicalCutoffRecords_iff_exists_isCanonicalCutoffRecordFamily
    p₀ δ₀ _).mpr ⟨q.rescale_P6N μ hμ, fun i => (records i).rescale_P6M μ hμ,
      hrec.rescale_P6M μ hμ⟩

private theorem cap_time_iff_P6M {μ t T θ s s' : ℝ} (hμ : 0 < μ) (hs : s' = μ * s) :
    t / μ - T / μ ≤ θ * s'⁻¹ ↔ t - T ≤ θ * s⁻¹ := by
  rw [hs, ← sub_div, mul_inv, show θ * (μ⁻¹ * s⁻¹) = θ * s⁻¹ / μ by ring]
  exact div_le_div_iff_of_pos_right hμ

/-- **`_P6M`**：`CapWindowPoint` 的双向 transport（重标度时刻 `t/μ` ⇔ 原时刻 `t`；`Dcap`、`θcap`
不变）。 -/
theorem capWindowPoint_rescale_iff_P6M
    {records : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i p}
    (μ : ℝ) (hμ : 0 < μ) {k : Fin (H.eventCount + 1)} {y : (H.stage k).Carrier}
    {t Dcap θcap : ℝ} :
    (H.rescale_P6N μ hμ).CapWindowPoint (fun i => (records i).rescale_P6M μ hμ) k y (t / μ)
        Dcap θcap ↔ H.CapWindowPoint records k y t Dcap θcap := by
  constructor
  · rintro ⟨j, hl, A, b, x, hpt, hx, ht⟩
    refine ⟨j, hl, H.traceOfRescale_P6N μ hμ A, b, x, ?_, hx, ?_⟩
    · exact hpt.trans
        (DFunLike.congr_fun (((records j).static b).rescale_P6M_window μ hμ) x)
    · exact (cap_time_iff_P6M hμ (((records j).static b).rescale_P6M_scale μ hμ)).mp ht
  · rintro ⟨j, hl, A, b, x, hpt, hx, ht⟩
    refine ⟨j, hl, H.traceToRescale_P6N μ hμ A, b, x, ?_, hx, ?_⟩
    · exact hpt.trans
        (DFunLike.congr_fun (((records j).static b).rescale_P6M_window μ hμ) x).symm
    · exact (cap_time_iff_P6M hμ (((records j).static b).rescale_P6M_scale μ hμ)).mpr ht

end RetainedCoreHistory

/-- consumer：重标度 canonical family 上树内 `inv_two_mul_sq_lt_static_scale` 仍可用（`ρ₀/√μ`），
且 `¬ CapWindowPoint` 在 `t ↦ t/μ` 下保持。 -/
example {H : RetainedCoreHistory.{u}} {p₀ p : CutoffParameters} {δ₀ ρ₀ : ℝ}
    {records : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i p}
    (hrec : H.IsCanonicalCutoffRecordFamily p₀ δ₀ ρ₀ records)
    (hΛδ : p₀.recenterConstant * δ₀ ≤ 1 / 2) (μ : ℝ) (hμ : 0 < μ) (i : Fin H.eventCount)
    (b : (H.toHistory.event i).RetainedBoundaryIndex) (k : Fin (H.eventCount + 1))
    (y : (H.stage k).Carrier) (t Dcap θcap : ℝ)
    (hno : ¬ H.CapWindowPoint records k y t Dcap θcap) :
    (2 * (ρ₀ / Real.sqrt μ) ^ 2)⁻¹ < (((records i).rescale_P6M μ hμ).static b).neck.scale ∧
      ¬ (H.rescale_P6N μ hμ).CapWindowPoint (fun i => (records i).rescale_P6M μ hμ) k y (t / μ)
        Dcap θcap :=
  ⟨(hrec.rescale_P6M μ hμ).inv_two_mul_sq_lt_static_scale hΛδ i b,
    fun h => hno ((RetainedCoreHistory.capWindowPoint_rescale_iff_P6M μ hμ).mp h)⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
