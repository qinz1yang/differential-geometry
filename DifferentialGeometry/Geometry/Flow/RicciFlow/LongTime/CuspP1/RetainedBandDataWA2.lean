import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.RetainedConfinementWA2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.NeckBandPostNK2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.NeckBandShiftNK2

/-!
# c9a 的供给：S-W-NECK-2 的平移 band ⇒ `exists_retained_confinement_WA2` 的 band 前提
（O-W-ASSEMBLY-2 G9，第 3 部分，后缀 `_WA2`）

对 record `R`（晚期：`∀ b, R.delta b.1.1 ≤ 1/40000`）与 retained boundary `b`，取原 neck 的 backward
`B_b := R.backward b.1.1`、`c₀ := σ_b · 51`（S-W-NECK-2 G2：`Σ_b = {z_s = 50}` ↔ `Z = σ_b · 51`）：

* `N b := range (postSliceChart_TG … B_b)`、`Z b := postSliceHeight_TG … B_b − σ_b · 51`、
  `c_b := (r_b²)⁻¹`（`postSliceMetric_TG = scaleMetric (r_b²)⁻¹ g_post`，定义上相等）；
* 五联数据 ⇐ S-W-NECK-2 G3 `slice_band_estimates_center_post_NK2`（`w = 20`，`|c₀| + w = 71 ≤ δ⁻¹`；
  `R ≥ 3/5 ≥ 1/2`、`(dZ)² ≤ 2 g′ ≤ 4 g′`；`d(Z − c₀) = dZ`）；
* 切割球面 `e_s '' Σ_b ⊆ {Z b = 0}` ⇐ `neckSlab_fifty_height_NK2` + `e_s` 与 TOPGLUE 的 stage cast
  互逆（`carrierHomeo_cancel_TG`）。

`d` 对所有 `b` 一致（`exists_pos_le_of_finite_NK2`）。
-/

set_option autoImplicit false
noncomputable section

open Set Function Filter Manifold
open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.Endpoint GC.LongTime
open scoped Manifold ContDiff Topology

namespace GC.LongTime.CuspP1

universe u

/-- `d(f − c) = df`（实值函数，可微点）。 -/
theorem mfderiv_sub_const_WA2 {X : Type*} [TopologicalSpace X] [ChartedSpace ThreeSpace X]
    {f : X → ℝ} {x : X} (hf : MDifferentiableAt ThreeModel 𝓘(ℝ, ℝ) f x) (c : ℝ) :
    mfderiv ThreeModel 𝓘(ℝ, ℝ) (fun y => f y - c) x = mfderiv ThreeModel 𝓘(ℝ, ℝ) f x :=
  (hf.hasMFDerivAt.sub (hasMFDerivAt_const (I := ThreeModel) (I' := 𝓘(ℝ, ℝ)) c x)).mfderiv.trans
    (sub_zero _)

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}

/-- **c9a（逐 record）**：晚期 record `R` 的每个 retained boundary `b`，`s ∈ [τ₀ − d, τ₀)`
（`activeStage s = i.castSucc`）时给出 `exists_retained_confinement_WA2` 的 band 前提。 -/
theorem retained_band_data_WA2 (N : ℕ) (i : Fin (F.observation.history N).eventCount)
    {p : CutoffParameters} (R : GeometricCutoffRecord (F.observation.history N) i p)
    (hδ : ∀ b : ((F.observation.history N).event i).RetainedBoundaryIndex,
      R.delta b.1.1 ≤ 1 / 40000) :
    ∃ d : ℝ, 0 < d ∧ ∀ (s : ℝ) (hs0 : 0 ≤ s) (hsh : s ≤ (F.observation.history N).horizon)
      (hact : (F.observation.history N).activeStage ⟨s, hs0, hsh⟩ = i.castSucc),
      (F.observation.history N).time i.succ - d ≤ s → s < (F.observation.history N).time i.succ →
      ∀ b : ((F.observation.history N).event i).RetainedBoundaryIndex,
        ∃ (Nb : Set (postStage F.observation s).Carrier)
          (Zb : (postStage F.observation s).Carrier → ℝ) (c : ℝ) (hc : 0 < c),
        IsOpen Nb ∧ ContMDiffOn (𝓡 3) 𝓘(ℝ, ℝ) 1 Zb Nb ∧
        closure {x | x ∈ Nb ∧ |Zb x| < 20} ⊆ Nb ∧
        (∀ x ∈ Nb, |Zb x| < 20 → ∀ w : TangentSpace (𝓡 3) x,
          (show ℝ from mfderiv (𝓡 3) 𝓘(ℝ, ℝ) Zb x w) ^ 2 ≤
            4 * (scaleMetric c hc (postMetric F.observation s)).inner x w w) ∧
        (∀ x ∈ Nb, |Zb x| < 20 →
          1 / 2 ≤ metricScalarAt (scaleMetric c hc (postMetric F.observation s)) x) ∧
        sliceHomeo_SG2 F.observation N i s hs0 hsh hact '' neckSlab_SG2 R b {50} ⊆
          {x | x ∈ Nb ∧ Zb x = 0} := by
  have hex : ∀ b : ((F.observation.history N).event i).RetainedBoundaryIndex, ∃ d : ℝ, 0 < d ∧
      ∀ (s : ℝ) (h0 : (F.observation.history N).time i.castSucc ≤ s),
      (F.observation.history N).time i.succ - d ≤ s →
      ∀ h1 : s < (F.observation.history N).time i.succ,
      IsOpen (Set.range (postSliceChart_TG F N (R.backward b.1.1) h0 h1)) ∧
      ContMDiffOn ThreeModel 𝓘(ℝ, ℝ) ∞ (postSliceHeight_TG F N (R.backward b.1.1) h0 h1)
        (Set.range (postSliceChart_TG F N (R.backward b.1.1) h0 h1)) ∧
      ∀ c₀ w : ℝ, |c₀| + w ≤ (R.delta b.1.1)⁻¹ →
        closure {x : (postStage F.observation s).Carrier |
            x ∈ Set.range (postSliceChart_TG F N (R.backward b.1.1) h0 h1) ∧
              |postSliceHeight_TG F N (R.backward b.1.1) h0 h1 x - c₀| < w} ⊆
          Set.range (postSliceChart_TG F N (R.backward b.1.1) h0 h1) ∧
        (∀ x ∈ Set.range (postSliceChart_TG F N (R.backward b.1.1) h0 h1),
          |postSliceHeight_TG F N (R.backward b.1.1) h0 h1 x - c₀| < w →
          3 / 5 ≤ metricScalarAt (postSliceMetric_TG F N (R.backward b.1.1) s) x) ∧
        (∀ x ∈ Set.range (postSliceChart_TG F N (R.backward b.1.1) h0 h1),
          |postSliceHeight_TG F N (R.backward b.1.1) h0 h1 x - c₀| < w →
          ∀ v : TangentSpace ThreeModel x,
          (show ℝ from mfderiv ThreeModel 𝓘(ℝ, ℝ)
            (postSliceHeight_TG F N (R.backward b.1.1) h0 h1) x v) ^ 2 ≤
            2 * (postSliceMetric_TG F N (R.backward b.1.1) s).inner x v v) :=
    fun b => slice_band_estimates_center_post_NK2 F N (R.backward b.1.1)
      (R.two_le_order_NK b.1.1) (hδ b)
  choose d hd hband using hex
  obtain ⟨d₀, hd₀, hle⟩ := exists_pos_le_of_finite_NK2 d hd
  refine ⟨d₀, hd₀, fun s hs0 hsh hact hs1 hs2 b => ?_⟩
  have h0 : (F.observation.history N).time i.castSucc ≤ s := by
    have := (F.observation.history N).activeStage_time_le ⟨s, hs0, hsh⟩
    rwa [hact] at this
  have hsb : (F.observation.history N).time i.succ - d b ≤ s := by linarith [hle b]
  obtain ⟨hopen, hsmooth, hrest⟩ := hband b s h0 hsb hs2
  have hδb : (40000 : ℝ) ≤ (R.delta b.1.1)⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) (R.delta_pos b.1.1)]
    simpa using hδ b
  have hcw : |retainedSign_NK2 b * 51| + 20 ≤ (R.delta b.1.1)⁻¹ := by
    rw [abs_mul, abs_retainedSign_NK2, one_mul, abs_of_pos (by norm_num)]
    linarith
  obtain ⟨hcl, hR, hdz⟩ := hrest _ 20 hcw
  have hr : 0 < (R.nominalRadius ⟨b.1.1⟩ ^ 2)⁻¹ :=
    inv_pos.mpr (pow_pos (R.backward b.1.1).radius_pos 2)
  refine ⟨_, fun x => postSliceHeight_TG F N (R.backward b.1.1) h0 hs2 x -
    retainedSign_NK2 b * 51, _, hr, hopen, ?_, hcl, ?_, ?_, ?_⟩
  · exact (hsmooth.sub contMDiffOn_const).of_le (by exact_mod_cast le_top)
  · intro x hx hxb w
    rw [mfderiv_sub_const_WA2 ((hsmooth.contMDiffAt (hopen.mem_nhds hx)).mdifferentiableAt
      (by simp)) _]
    have hnn : 0 ≤ (postSliceMetric_TG F N (R.backward b.1.1) s).inner x w w := by
      rcases eq_or_ne w 0 with hw | hw
      · rw [hw]
        simp
      · exact ((postSliceMetric_TG F N (R.backward b.1.1) s).pos x w hw).le
    change _ ≤ 4 * (postSliceMetric_TG F N (R.backward b.1.1) s).inner x w w
    exact (hdz x hx hxb w).trans (by linarith)
  · intro x hx hxb
    have := hR x hx hxb
    change 1 / 2 ≤ metricScalarAt (postSliceMetric_TG F N (R.backward b.1.1) s) x
    linarith
  · rintro _ ⟨y, hy, rfl⟩
    obtain ⟨hyr, hyZ⟩ := neckSlab_fifty_height_NK2 R b hy
    have hcancel : carrierHomeo_CPD2 (postStage_eq_castSucc_TG F N i h0 hs2)
        (sliceHomeo_SG2 F.observation N i s hs0 hsh hact y) = y :=
      carrierHomeo_cancel_TG (postStage_eq_castSucc_TG F N i h0 hs2) y
    refine ⟨?_, ?_⟩
    · obtain ⟨y', rfl⟩ := hyr
      exact ⟨y', rfl⟩
    · change (R.backward b.1.1).sliceHeight_NK (carrierHomeo_CPD2
        (postStage_eq_castSucc_TG F N i h0 hs2)
        (sliceHomeo_SG2 F.observation N i s hs0 hsh hact y)) - retainedSign_NK2 b * 51 = 0
      rw [hcancel, hyZ]
      ring

end GC.LongTime.CuspP1
