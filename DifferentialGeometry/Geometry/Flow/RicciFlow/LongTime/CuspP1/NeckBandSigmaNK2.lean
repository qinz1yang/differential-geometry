import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.NeckBandPostNK2

/-!
# R3：切割球面 `Σ_b` 处的 band 数据与中间球面排除（S-W-NECK-2 G4，后缀 `_NK2`）

IMS06 的 `(N b, Z b)` 用 static 坐标的 `Z b = z_s − 50`，而 NECK 的高度是原 neck 坐标 `Z`，
`Z = σ_b(1 + z_s)`（G2），所以 `z_s − 50 = σ_b Z − 51`。本文件给仿射高度 `a·Z − b`（`a² = 1`）的
band 数据，`(a, b) = (σ_b, 51)` 即 `z_s − 50`，`(a, b) = (1, c₀)` 即 `Z − c₀`：

* `mfderiv_affine_height_NK2`、`contMDiffOn_affine_height_NK2`：仿射高度的导数与光滑性；
* **`slice_band_estimates_affine_post_NK2`**：G3 的 `center_post` 对 `a Z − b` 的形状
  （`ContMDiffOn`、`(d(aZ − b))² ≤ 2 g_slice`，`|b| + w ≤ δ⁻¹`）；
* **`not_mem_level_sphere_of_slice_post_NK2`**：`not_mem_middle_sphere_of_slice_post_TG` 的
  level `{aZ = b}` 版本（IMS05′ 仍是显式参数 `hIMS05`）：围绕 `Σ_b` 的盘不碰 `{σ_b Z = 51}`；
* `neckSlab_fifty_eq_level_NK2`：`neckSlab_SG2 R b {50} = {x ∈ range chart | σ_b Z x − 51 = 0}`
  （`hcol`：`50 < δ_s⁻¹`），即 `{Z b = 0} = Σ_b`。
-/

set_option autoImplicit false
noncomputable section
open Set Manifold Filter
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Topology
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.LongTime
open scoped Manifold ContDiff Topology
namespace GC.LongTime.CuspP1
universe u

section Affine

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]

/-- 仿射高度 `a · Z − b` 的导数：`d(aZ − b) = a · dZ`。 -/
theorem mfderiv_affine_height_NK2 (Z : M → ℝ) (a b : ℝ) {x : M}
    (hZ : MDifferentiableAt ThreeModel 𝓘(ℝ, ℝ) Z x) (v : TangentSpace ThreeModel x) :
    (show ℝ from mfderiv ThreeModel 𝓘(ℝ, ℝ) (fun y => a * Z y - b) x v) =
      a * (show ℝ from mfderiv ThreeModel 𝓘(ℝ, ℝ) Z x v) := by
  have h := (hZ.hasMFDerivAt.const_smul a).sub
    (hasMFDerivAt_const (I := ThreeModel) (I' := 𝓘(ℝ, ℝ)) b x)
  have h' := h.mfderiv
  have e : (fun y => a * Z y - b) = a • Z - fun _ => b := by
    ext y
    simp
  rw [e, h']
  change a * (show ℝ from mfderiv ThreeModel 𝓘(ℝ, ℝ) Z x v) - 0 =
    a * (show ℝ from mfderiv ThreeModel 𝓘(ℝ, ℝ) Z x v)
  exact sub_zero _

/-- 仿射高度的光滑性。 -/
theorem contMDiffOn_affine_height_NK2 {Z : M → ℝ} {S : Set M}
    (hZ : ContMDiffOn ThreeModel 𝓘(ℝ, ℝ) ∞ Z S) (a b : ℝ) :
    ContMDiffOn ThreeModel 𝓘(ℝ, ℝ) ∞ (fun y => a * Z y - b) S :=
  (contMDiffOn_const.mul hZ).sub contMDiffOn_const

end Affine

section Post

variable {P : OrientedThreeStage.{u}} {g : P.Metric} (F : GC.Interface.RawSurgery P g) (n : ℕ)
  {i : Fin (F.tower.history n).toHistory.eventCount} {δ : ℝ} {k : ℕ}
  {neck : NormalizedNeck ((F.tower.history n).toHistory.event i).terminal.metric δ k} {r : ℝ}
  (B : IncomingBackwardNeck (F.tower.history n).toHistory i neck r)

/-- **G4（仿射高度的 band 数据）**：`a² = 1`，`|b| + w ≤ δ⁻¹`；band `{|a Z − b| < w}`。 -/
theorem slice_band_estimates_affine_post_NK2 (hk : 2 ≤ k) (hδ : δ ≤ 1 / 40000) :
    ∃ d : ℝ, 0 < d ∧ ∀ (s : ℝ) (h0 : (F.tower.history n).toHistory.time i.castSucc ≤ s),
      (F.tower.history n).toHistory.time i.succ - d ≤ s →
      ∀ h1 : s < (F.tower.history n).toHistory.time i.succ,
      IsOpen (Set.range (postSliceChart_TG F n B h0 h1)) ∧
      ∀ a b w : ℝ, a * a = 1 → |b| + w ≤ δ⁻¹ →
        ContMDiffOn ThreeModel 𝓘(ℝ, ℝ) ∞
          (fun p => a * postSliceHeight_TG F n B h0 h1 p - b)
          (Set.range (postSliceChart_TG F n B h0 h1)) ∧
        closure {p : (postStage F.observation s).Carrier |
            p ∈ Set.range (postSliceChart_TG F n B h0 h1) ∧
              |a * postSliceHeight_TG F n B h0 h1 p - b| < w} ⊆
          Set.range (postSliceChart_TG F n B h0 h1) ∧
        (∀ p ∈ Set.range (postSliceChart_TG F n B h0 h1),
          |a * postSliceHeight_TG F n B h0 h1 p - b| < w →
          3 / 5 ≤ metricScalarAt (postSliceMetric_TG F n B s) p) ∧
        (∀ p ∈ Set.range (postSliceChart_TG F n B h0 h1),
          |a * postSliceHeight_TG F n B h0 h1 p - b| < w → ∀ v : TangentSpace ThreeModel p,
          (show ℝ from mfderiv ThreeModel 𝓘(ℝ, ℝ)
              (fun y => a * postSliceHeight_TG F n B h0 h1 y - b) p v) ^ 2 ≤
            2 * (postSliceMetric_TG F n B s).inner p v v) := by
  obtain ⟨d, hd, h⟩ := slice_band_estimates_center_post_NK2 F n B hk hδ
  refine ⟨d, hd, fun s h0 hs1 h1 => ?_⟩
  obtain ⟨hA, hB, hC⟩ := h s h0 hs1 h1
  refine ⟨hA, fun a b w ha hbw => ?_⟩
  have hab : ∀ z : ℝ, |a * z - b| = |z - a * b| := fun z => by
    have h2 : a * z - b = a * (z - a * b) := by linear_combination (b) * ha
    have ha1 : |a| = 1 := by
      have : |a| * |a| = 1 := by rw [← abs_mul, ha, abs_one]
      nlinarith [abs_nonneg a]
    rw [h2, abs_mul, ha1, one_mul]
  have hb : |a * b| = |b| := by
    have ha1 : |a| = 1 := by
      have : |a| * |a| = 1 := by rw [← abs_mul, ha, abs_one]
      nlinarith [abs_nonneg a]
    rw [abs_mul, ha1, one_mul]
  obtain ⟨hC1, hC2, hC3⟩ := hC (a * b) w (by rw [hb]; exact hbw)
  have hm : ∀ p ∈ Set.range (postSliceChart_TG F n B h0 h1),
      MDifferentiableAt ThreeModel 𝓘(ℝ, ℝ) (postSliceHeight_TG F n B h0 h1) p := fun p hp =>
    ((hB p hp).contMDiffAt (hA.mem_nhds hp)).mdifferentiableAt (by simp)
  refine ⟨contMDiffOn_affine_height_NK2 hB a b, ?_, ?_, ?_⟩
  · simpa only [hab] using hC1
  · intro p hp hz
    exact hC2 p hp (by rwa [hab] at hz)
  · intro p hp hz v
    have := hC3 p hp (by rwa [hab] at hz) v
    rw [mfderiv_affine_height_NK2 _ a b (hm p hp), mul_pow]
    nlinarith [sq_nonneg ((show ℝ from mfderiv ThreeModel 𝓘(ℝ, ℝ)
      (postSliceHeight_TG F n B h0 h1) p v))]

/-- **G4（切割球面处的 IMS06′）**：`a² = 1`，`|b| + 20 ≤ δ⁻¹`。`postStage F.observation s` 上开盘内光滑、
`q(∂D)` 与 band `{|a Z − b| < 20}` 的闭包不交、满足 IMS05′（`postSliceMetric_TG` 下，显式参数）
的盘 `q` 不碰 level 集 `{a Z = b}`。`(a, b) = (σ_b, 51)` 即切割球面 `Σ_b = {z_s = 50}`。 -/
theorem not_mem_level_sphere_of_slice_post_NK2 (hk : 2 ≤ k) (hδ : δ ≤ 1 / 40000) :
    ∃ d : ℝ, 0 < d ∧ ∀ (s : ℝ) (h0 : (F.tower.history n).toHistory.time i.castSucc ≤ s),
      (F.tower.history n).toHistory.time i.succ - d ≤ s →
      ∀ h1 : s < (F.tower.history n).toHistory.time i.succ,
      ∀ a b : ℝ, a * a = 1 → |b| + 20 ≤ δ⁻¹ →
      ∀ q : C(closedDisk, (postStage F.observation s).Carrier),
        DiskSmoothInterior (E := ThreeSpace) q →
        (∀ θ : loopCircle, diskTrace q θ ∉
          closure {p : (postStage F.observation s).Carrier |
            p ∈ Set.range (postSliceChart_TG F n B h0 h1) ∧
              |a * postSliceHeight_TG F n B h0 h1 p - b| < 20}) →
        (∀ (z₀ : ℂ) (ρ : ℝ), z₀ ∈ Metric.ball (0 : ℂ) 1 → 0 < ρ →
          IsCompact {z : ℂ | z ∈ Metric.ball (0 : ℂ) 1 ∧
            diskEDist_NK (postSliceMetric_TG F n B s) q z₀ z ≤ ENNReal.ofReal ρ} →
          (∃ z ∈ Metric.ball (0 : ℂ) 1,
            diskEDist_NK (postSliceMetric_TG F n B s) q z₀ z = ENNReal.ofReal ρ) →
          (∀ z ∈ Metric.ball (0 : ℂ) 1,
            diskEDist_NK (postSliceMetric_TG F n B s) q z₀ z ≤ ENNReal.ofReal ρ →
            ∀ᶠ w in 𝓝 z, 1 / 2 ≤
              metricScalarAt (postSliceMetric_TG F n B s) (diskExtension q w)) →
          ρ ≤ 2 * Real.pi * Real.sqrt (2 / (3 * (1 / 2)))) →
        ∀ ζ : closedDisk, ¬ (q ζ ∈ Set.range (postSliceChart_TG F n B h0 h1) ∧
          a * postSliceHeight_TG F n B h0 h1 (q ζ) - b = 0) := by
  obtain ⟨d, hd, h⟩ := slice_band_estimates_affine_post_NK2 F n B hk hδ
  refine ⟨d, hd, fun s h0 hs1 h1 a b ha hb q hq htrace hIMS05 => ?_⟩
  obtain ⟨hN, hrest⟩ := h s h0 hs1 h1
  obtain ⟨hZ, hcl, hR, hdz⟩ := hrest a b 20 ha hb
  refine not_mem_middle_sphere_of_stability_bound_NK (postSliceMetric_TG F n B s) hq hN
    (hZ.of_le (by exact_mod_cast le_top)) hcl ?_ ?_ htrace hIMS05
  · exact fun p hp hz w => by
      have h5 := hdz p hp hz w
      have h0' := metric_inner_self_nonneg (postSliceMetric_TG F n B s) p w
      linarith
  · exact fun p hp hz => (by norm_num : (1 : ℝ) / 2 ≤ 3 / 5).trans (hR p hp hz)

end Post

section Level

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {p : CutoffParameters}

/-- `Σ_b = {z_s = 50}` 是 NECK 坐标的 level 集 `{σ_b Z = 51}`（`hcol : 50 < δ_s⁻¹`）。 -/
theorem neckSlab_fifty_eq_level_NK2 (R : GeometricCutoffRecord H i p)
    (b : (H.event i).RetainedBoundaryIndex) (hcol : 50 < ((R.static b).delta)⁻¹) :
    neckSlab_SG2 R b {50} = {x | x ∈ Set.range (R.backward b.1.1).sliceChart_NK ∧
      retainedSign_NK2 b * (R.backward b.1.1).sliceHeight_NK x - 51 = 0} := by
  rw [neckSlab_eq_height_NK2 R b (S := {50}) (fun z hz => by
    rw [mem_singleton_iff.mp hz]
    constructor <;> linarith [inv_pos.mpr (R.static b).neck.delta_pos])]
  ext x
  constructor
  · rintro ⟨hx, h⟩
    exact ⟨hx, by rw [mem_singleton_iff] at h; linarith⟩
  · rintro ⟨hx, h⟩
    exact ⟨hx, by rw [mem_singleton_iff]; linarith⟩

end Level

end GC.LongTime.CuspP1
