import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.DiskConformalLengthIM6
import DifferentialGeometry.Geometry.MinimalSurface.Variation.DiskMetricVariation
import DifferentialGeometry.Geometry.Metric.Family.Stationary

/-!
# `d_q` ↔ O-W-GEO-MIN 的实值 d-接口（O-W-IMS06 G4，c3 收缩准备，后缀 `_IM6`）

O-W-GEO-MIN G1 `exists_minimizing_path_to_sphere_GM` 以实值 `d : ℂ → ℝ`、`ContinuousOn d Ω`、
`hseg : segment ℝ x y ⊆ Ω → d y ≤ d x + ∫ t in 0..1, √(lam (x + t•(y−x))) * ‖y − x‖`、`d p = 0`、
`IsCompact {z | z ∈ Ω ∧ d z ≤ r}` 进入（其 DELIVERIES 块注明 "toReal 桥接留给 IMS05′ 组装"）。
本文件对 `d := (diskEDist_NK g q z₀ ·).toReal`、`Ω = ball 0 1`、`lam = diskConformalFactor_IM6 g q`
给出全部桥接：

* `contDiffOn_diskConformalFactor_IM6`：`lam` 在开盘上 `C^∞`（`contDiffOn_metricFamilyDiskPairing`
  对常值族）；`diskConformalFactor_pos_IM6`：`mfderiv` 单射处 `lam > 0`（K16b）。
* `diskEDist_ne_top_IM6`、`continuousOn_diskEDist_toReal_IM6`：开盘内有限、`toReal` 连续
  （S-W-NECK 的局部 Lipschitz 界 `exists_diskEDist_le_NK`）。
* `diskEDist_toReal_le_add_IM6`：实值 `hseg`（G1 的 `ℝ≥0∞` 形 + `ofReal_integral_eq_lintegral_ofReal`）。
* `ims05_radius_bound_of_realDist_IM6`：GEO-MIN 实值形的 IMS05′（显式前提 `hGM`，O-W-GEO-MIN G3 +
  S-W-EIG + S-W-STAB 合成）⇒ S-W-NECK G4 的 `hIMS05`（`σ` 版）。
-/

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Filter Manifold
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Topology
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff ENNReal NNReal Topology

namespace GC.LongTime

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- `lam = g(∂₁U, ∂₁U)` 在开盘上光滑。 -/
theorem contDiffOn_diskConformalFactor_IM6 [FiniteDimensional ℝ E]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {q : C(closedDisk, M)}
    (hq : DiskSmoothInterior (E := E) q) :
    ContDiffOn ℝ ∞ (diskConformalFactor_IM6 g q) (Metric.ball (0 : ℂ) 1) := by
  have hG : MetricFamilySmoothOn (RealTimeInterval.univ 0) (fun _ : ℝ => g) :=
    metricFamilySmoothOn_stationary g (RealTimeInterval.univ 0)
  have h : ContDiffOn ℝ ∞ (fun p : ℝ × ℂ => g.inner (diskExtension q p.2)
      (diskMapPartial (diskExtension q) p.2 1) (diskMapPartial (diskExtension q) p.2 1))
      (univ ×ˢ Metric.ball (0 : ℂ) 1) :=
    contDiffOn_metricFamilyDiskPairing hG isOpen_univ (fun _ h => h) Metric.isOpen_ball hq 1 1
  have hmap : ContDiffOn ℝ ∞ (fun z : ℂ => ((0 : ℝ), z)) (Metric.ball (0 : ℂ) 1) :=
    contDiffOn_const.prodMk contDiffOn_id
  have h2 := h.comp hmap fun z hz => ⟨mem_univ _, hz⟩
  refine h2.congr fun z _ => ?_
  rfl

/-- `mfderiv` 单射处共形因子为正。 -/
theorem diskConformalFactor_pos_IM6 (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {q : C(closedDisk, M)} {z : ℂ}
    (hinj : Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension q) z)) :
    0 < diskConformalFactor_IM6 g q z := by
  refine g.pos _ _ fun h => (one_ne_zero : (1 : ℂ) ≠ 0) (hinj ?_)
  exact h.trans (map_zero (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension q) z)).symm

/-- 开盘内两点的 `d_q` 有限（线段在 `closedBall 0 (max ‖z₀‖ ‖z‖) ⊆ ball 0 1` 内）。 -/
theorem diskEDist_ne_top_IM6 (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {q : C(closedDisk, M)}
    (hq : DiskSmoothInterior (E := E) q) {z₀ z : ℂ} (h₀ : z₀ ∈ Metric.ball (0 : ℂ) 1)
    (hz : z ∈ Metric.ball (0 : ℂ) 1) : diskEDist_NK g q z₀ z ≠ ⊤ := by
  have hρ : max ‖z₀‖ ‖z‖ < 1 := max_lt (mem_ball_zero_iff.mp h₀) (mem_ball_zero_iff.mp hz)
  obtain ⟨C, hC⟩ := exists_diskEDist_le_NK g hq (Metric.closedBall_subset_ball hρ)
  exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top)
    (hC z₀ (mem_closedBall_zero_iff.mpr (le_max_left _ _)) z
      (mem_closedBall_zero_iff.mpr (le_max_right _ _)))

/-- 局部 Lipschitz：`closedBall z ρ ⊆ ball 0 1` 内 `|d p − d z| ≤ C ‖p − z‖`（`d = toReal ∘ d_q z₀`）。 -/
theorem exists_abs_toReal_sub_le_IM6 (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {q : C(closedDisk, M)} (hq : DiskSmoothInterior (E := E) q) {z₀ z : ℂ}
    (h₀ : z₀ ∈ Metric.ball (0 : ℂ) 1) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hS : Metric.closedBall z ρ ⊆ Metric.ball (0 : ℂ) 1) :
    ∃ C : ℝ≥0, ∀ p ∈ Metric.closedBall z ρ,
      |(diskEDist_NK g q z₀ p).toReal - (diskEDist_NK g q z₀ z).toReal| ≤ C * ‖p - z‖ := by
  obtain ⟨C, hC⟩ := exists_diskEDist_le_NK g hq hS
  refine ⟨C, fun p hp => ?_⟩
  have hz : z ∈ Metric.closedBall z ρ := Metric.mem_closedBall_self hρ
  have hfz := diskEDist_ne_top_IM6 g hq h₀ (hS hz)
  have hfp := diskEDist_ne_top_IM6 g hq h₀ (hS hp)
  have hfin : ∀ a b : ℂ, (C : ℝ≥0∞) * (‖b - a‖₊ : ℝ≥0∞) ≠ ⊤ := fun _ _ =>
    ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top
  have hreal : ∀ a b : ℂ, ((C : ℝ≥0∞) * (‖b - a‖₊ : ℝ≥0∞)).toReal = C * ‖b - a‖ := by
    intro a b
    rw [ENNReal.toReal_mul]
    simp
  have h1 : diskEDist_NK g q z₀ p ≤ diskEDist_NK g q z₀ z + (C : ℝ≥0∞) * (‖p - z‖₊ : ℝ≥0∞) :=
    (diskEDist_triangle_NK g q (w := z)).trans (add_le_add le_rfl (hC z hz p hp))
  have h2 : diskEDist_NK g q z₀ z ≤ diskEDist_NK g q z₀ p + (C : ℝ≥0∞) * (‖z - p‖₊ : ℝ≥0∞) :=
    (diskEDist_triangle_NK g q (w := p)).trans (add_le_add le_rfl (hC p hp z hz))
  have h1' := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hfz, hfin z p⟩) h1
  have h2' := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hfp, hfin p z⟩) h2
  rw [ENNReal.toReal_add hfz (hfin z p), hreal] at h1'
  rw [ENNReal.toReal_add hfp (hfin p z), hreal, norm_sub_rev] at h2'
  rw [abs_le]
  constructor <;> linarith

/-- `d = toReal ∘ d_q z₀` 在开盘上连续。 -/
theorem continuousOn_diskEDist_toReal_IM6 (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {q : C(closedDisk, M)} (hq : DiskSmoothInterior (E := E) q) {z₀ : ℂ}
    (h₀ : z₀ ∈ Metric.ball (0 : ℂ) 1) :
    ContinuousOn (fun z => (diskEDist_NK g q z₀ z).toReal) (Metric.ball (0 : ℂ) 1) := by
  intro z hz
  obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.mp Metric.isOpen_ball z hz
  have hS : Metric.closedBall z (ε / 2) ⊆ Metric.ball (0 : ℂ) 1 :=
    (Metric.closedBall_subset_ball (by linarith)).trans hεsub
  obtain ⟨C, hC⟩ := exists_abs_toReal_sub_le_IM6 g hq h₀ (by linarith) hS
  refine (Metric.continuousAt_iff.mpr fun η hη => ?_).continuousWithinAt
  refine ⟨min (ε / 2) (η / (C + 1)), lt_min (by linarith) (by positivity), fun p hp => ?_⟩
  have hp1 : p ∈ Metric.closedBall z (ε / 2) :=
    Metric.mem_closedBall.mpr (hp.le.trans (min_le_left _ _))
  have hp2 : ‖p - z‖ < η / (C + 1) := by
    rw [← dist_eq_norm]
    exact hp.trans_le (min_le_right _ _)
  rw [Real.dist_eq]
  have hC0 : (0 : ℝ) ≤ C := C.2
  calc |(diskEDist_NK g q z₀ p).toReal - (diskEDist_NK g q z₀ z).toReal| ≤ C * ‖p - z‖ :=
        hC p hp1
    _ ≤ (C + 1) * ‖p - z‖ := by nlinarith [norm_nonneg (p - z)]
    _ < (C + 1) * (η / (C + 1)) := mul_lt_mul_of_pos_left hp2 (by linarith)
    _ = η := by field_simp

/-- 实值 `hseg`（O-W-GEO-MIN 的 d-接口逐字）：`segment ℝ x y ⊆ ball` ⇒
`d y ≤ d x + ∫ t in 0..1, √(lam (x + t•(y−x))) * ‖y − x‖`。 -/
theorem diskEDist_toReal_le_add_IM6 [FiniteDimensional ℝ E]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {q : C(closedDisk, M)}
    (hq : DiskSmoothInterior (E := E) q)
    (hconf : ∀ z ∈ Metric.ball (0 : ℂ) 1, DiskMapConformalAt g (diskExtension q) z)
    {z₀ : ℂ} (h₀ : z₀ ∈ Metric.ball (0 : ℂ) 1) {x y : ℂ}
    (hxy : segment ℝ x y ⊆ Metric.ball (0 : ℂ) 1) :
    (diskEDist_NK g q z₀ y).toReal ≤ (diskEDist_NK g q z₀ x).toReal +
      ∫ t in (0 : ℝ)..1, Real.sqrt (diskConformalFactor_IM6 g q (x + t • (y - x))) * ‖y - x‖ := by
  have hx : x ∈ Metric.ball (0 : ℂ) 1 := hxy (left_mem_segment ℝ x y)
  have hy : y ∈ Metric.ball (0 : ℂ) 1 := hxy (right_mem_segment ℝ x y)
  set f : ℝ → ℝ := fun t => Real.sqrt (diskConformalFactor_IM6 g q (x + t • (y - x))) * ‖y - x‖
    with hf
  have hseg : ∀ t ∈ Icc (0 : ℝ) 1, x + t • (y - x) ∈ Metric.ball (0 : ℂ) 1 := by
    intro t ht
    apply hxy
    refine ⟨1 - t, t, by linarith [ht.2], ht.1, by ring, ?_⟩
    module
  have hfc : ContinuousOn f (Icc (0 : ℝ) 1) := by
    have hlam := (contDiffOn_diskConformalFactor_IM6 g hq).continuousOn
    have haff : Continuous (fun t : ℝ => x + t • (y - x)) := by fun_prop
    exact ((hlam.comp haff.continuousOn hseg).sqrt).mul continuousOn_const
  have hfn : ∀ t, 0 ≤ f t := fun t => mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  have hI : ∫⁻ t in Icc (0 : ℝ) 1, ENNReal.ofReal (f t) =
      ENNReal.ofReal (∫ t in (0 : ℝ)..1, f t) := by
    rw [intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc,
      ofReal_integral_eq_lintegral_ofReal (hfc.integrableOn_Icc)
        (Filter.Eventually.of_forall hfn)]
  have hle : diskEDist_NK g q z₀ y ≤ diskEDist_NK g q z₀ x +
      ∫⁻ t in Icc (0 : ℝ) 1, ENNReal.ofReal (f t) :=
    diskEDist_le_add_conformal_IM6 g hq hconf z₀ hx hy
  rw [hI] at hle
  have hfx := diskEDist_ne_top_IM6 g hq h₀ hx
  have hIn : 0 ≤ ∫ t in (0 : ℝ)..1, f t :=
    intervalIntegral.integral_nonneg zero_le_one fun t _ => hfn t
  have h' := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hfx, ENNReal.ofReal_ne_top⟩) hle
  rwa [ENNReal.toReal_add hfx ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hIn] at h'

/-- **c3 的 GEO-MIN 实值形**：`hGM`（O-W-GEO-MIN 的 d-接口逐字：`d z₀ = 0`、`ContinuousOn d Ω`、
`hseg`、`{z ∈ Ω | d z ≤ r}` 紧、球上邻域 `R ≥ σ` ⇒ `r ≤ 2π√(2/(3σ))`；`Ω = ball 0 1`）⇒
S-W-NECK G4 的 `hIMS05`（`σ` 版，`d_q = diskEDist_NK g q z₀`）。`d := toReal ∘ d_q z₀`。 -/
theorem ims05_radius_bound_of_realDist_IM6 [FiniteDimensional ℝ E]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {q : C(closedDisk, M)}
    (hq : DiskSmoothInterior (E := E) q)
    (hconf : ∀ z ∈ Metric.ball (0 : ℂ) 1, DiskMapConformalAt g (diskExtension q) z)
    {σ : ℝ}
    (hGM : ∀ (d : ℂ → ℝ) (z₀ : ℂ) (r : ℝ), z₀ ∈ Metric.ball (0 : ℂ) 1 → 0 < r → d z₀ = 0 →
      ContinuousOn d (Metric.ball (0 : ℂ) 1) →
      (∀ x y : ℂ, segment ℝ x y ⊆ Metric.ball (0 : ℂ) 1 → d y ≤ d x +
        ∫ t in (0 : ℝ)..1, Real.sqrt (diskConformalFactor_IM6 g q (x + t • (y - x))) * ‖y - x‖) →
      IsCompact {z : ℂ | z ∈ Metric.ball (0 : ℂ) 1 ∧ d z ≤ r} →
      (∀ z ∈ Metric.ball (0 : ℂ) 1, d z ≤ r →
        ∀ᶠ w in 𝓝 z, σ ≤ metricScalarAt g (diskExtension q w)) →
      r ≤ 2 * Real.pi * Real.sqrt (2 / (3 * σ))) :
    ∀ (z₀ : ℂ) (r : ℝ), z₀ ∈ Metric.ball (0 : ℂ) 1 → 0 < r →
      IsCompact {z : ℂ | z ∈ Metric.ball (0 : ℂ) 1 ∧
        diskEDist_NK g q z₀ z ≤ ENNReal.ofReal r} →
      (∃ z ∈ Metric.ball (0 : ℂ) 1, diskEDist_NK g q z₀ z = ENNReal.ofReal r) →
      (∀ z ∈ Metric.ball (0 : ℂ) 1, diskEDist_NK g q z₀ z ≤ ENNReal.ofReal r →
        ∀ᶠ w in 𝓝 z, σ ≤ metricScalarAt g (diskExtension q w)) →
      r ≤ 2 * Real.pi * Real.sqrt (2 / (3 * σ)) := by
  intro z₀ r h₀ hr hK _ hR
  have hiff : ∀ z ∈ Metric.ball (0 : ℂ) 1,
      (diskEDist_NK g q z₀ z).toReal ≤ r ↔ diskEDist_NK g q z₀ z ≤ ENNReal.ofReal r :=
    fun z hz => (ENNReal.le_ofReal_iff_toReal_le (diskEDist_ne_top_IM6 g hq h₀ hz) hr.le).symm
  have hset : {z : ℂ | z ∈ Metric.ball (0 : ℂ) 1 ∧ (diskEDist_NK g q z₀ z).toReal ≤ r} =
      {z : ℂ | z ∈ Metric.ball (0 : ℂ) 1 ∧ diskEDist_NK g q z₀ z ≤ ENNReal.ofReal r} := by
    ext z
    exact ⟨fun h => ⟨h.1, (hiff z h.1).mp h.2⟩, fun h => ⟨h.1, (hiff z h.1).mpr h.2⟩⟩
  refine hGM (fun z => (diskEDist_NK g q z₀ z).toReal) z₀ r h₀ hr ?_
    (continuousOn_diskEDist_toReal_IM6 g hq h₀)
    (fun x y hxy => diskEDist_toReal_le_add_IM6 g hq hconf h₀ hxy) (hset ▸ hK)
    (fun z hz hd => hR z hz ((hiff z hz).mp hd))
  rw [diskEDist_self_NK g q h₀]
  rfl

end GC.LongTime
