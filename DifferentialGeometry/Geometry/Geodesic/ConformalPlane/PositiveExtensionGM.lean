import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Topology.MetricSpace.Thickening

/-!
# 正函数从开集到全平面的光滑延拓（O-W-GEO-MIN G1，后缀 `_GM`）

Route W 的 IMS05′ 第 (5) 步要在 `ℂ` 上用 complete Riemannian 度量的 Hopf–Rinow，而共形因子
`ρ = u √lam` 只在开集 `Ω` 上光滑且为正。这里给出 cutoff 拼接：

* `exists_cutoff_GM`：紧 `K ⊆ Ω`（开）⇒ 光滑 `χ : ℂ → [0,1]`、开 `V`，`K ⊆ V ⊆ Ω`，`χ = 1` on `V`，
  `tsupport χ` 紧且 `⊆ Ω`；
* `posExt_GM χ f := χ f + (1 − χ)`：`f` 在 `Ω` 上光滑且为正 ⇒ `posExt_GM χ f` 在 `ℂ` 上光滑
  （`contDiff_posExt_GM`）、处处为正（`posExt_pos_GM`）、在 `{χ = 1}` 上等于 `f`、有全局上界
  （`exists_posExt_le_GM`）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric
open scoped Topology ContDiff Manifold

namespace DifferentialGeometry.Geometry

/-- cutoff：紧 `K ⊆ Ω` ⇒ 光滑 `χ ∈ [0,1]`，在 `K` 的开邻域 `V ⊆ Ω` 上 `χ = 1`，`tsupport χ` 紧 `⊆ Ω`。 -/
theorem exists_cutoff_GM {Ω K : Set ℂ} (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ (χ : ℂ → ℝ) (V : Set ℂ), ContDiff ℝ ∞ χ ∧ IsOpen V ∧ K ⊆ V ∧ V ⊆ Ω ∧
      (∀ z ∈ V, χ z = 1) ∧ (∀ z, 0 ≤ χ z ∧ χ z ≤ 1) ∧ IsCompact (tsupport χ) ∧
      tsupport χ ⊆ Ω := by
  obtain ⟨δ, hδ, hδΩ⟩ := hK.exists_cthickening_subset_open hΩ hKΩ
  have hdisj : Disjoint (thickening δ K)ᶜ K :=
    disjoint_compl_left_iff_subset.mpr (self_subset_thickening hδ K)
  obtain ⟨f, hf0, hf1, hf01⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed 𝓘(ℝ, ℂ)
    (n := (⊤ : ℕ∞)) isOpen_thickening.isClosed_compl hK.isClosed hdisj
  obtain ⟨U, hU, hKU, hUf⟩ := mem_nhdsSet_iff_exists.mp hf1
  have hsupp : tsupport f ⊆ cthickening δ K := by
    refine (closure_mono ?_).trans (closure_thickening_subset_cthickening δ K)
    intro z hz
    by_contra hzt
    exact hz (hf0.self_of_nhdsSet z hzt)
  refine ⟨f, U ∩ thickening δ K, contMDiff_iff_contDiff.mp f.contMDiff,
    hU.inter isOpen_thickening, subset_inter hKU (self_subset_thickening hδ K),
    fun z hz => hδΩ (thickening_subset_cthickening δ K hz.2), fun z hz => hUf hz.1,
    fun z => hf01 z, (hK.cthickening (r := δ)).of_isClosed_subset (isClosed_tsupport _) hsupp,
    hsupp.trans hδΩ⟩

/-- 拼接：`χ f + (1 − χ)`。 -/
def posExt_GM (χ f : ℂ → ℝ) (z : ℂ) : ℝ := χ z * f z + (1 - χ z)

theorem posExt_eq_GM {χ f : ℂ → ℝ} {z : ℂ} (h : χ z = 1) : posExt_GM χ f z = f z := by
  simp [posExt_GM, h]

theorem posExt_eq_one_GM {χ f : ℂ → ℝ} {Ω : Set ℂ} (hχΩ : tsupport χ ⊆ Ω) {z : ℂ}
    (hz : z ∉ Ω) : posExt_GM χ f z = 1 := by
  have : χ z = 0 := image_eq_zero_of_notMem_tsupport (fun h => hz (hχΩ h))
  simp [posExt_GM, this]

theorem contDiff_posExt_GM {χ f : ℂ → ℝ} {Ω : Set ℂ} (hΩ : IsOpen Ω) (hχ : ContDiff ℝ ∞ χ)
    (hχΩ : tsupport χ ⊆ Ω) (hf : ContDiffOn ℝ ∞ f Ω) : ContDiff ℝ ∞ (posExt_GM χ f) := by
  refine contDiff_iff_contDiffAt.mpr fun z => ?_
  by_cases hz : z ∈ Ω
  · exact (hχ.contDiffAt.mul (hf.contDiffAt (hΩ.mem_nhds hz))).add
      (contDiffAt_const.sub hχ.contDiffAt)
  · have hev : χ =ᶠ[𝓝 z] fun _ => (0 : ℝ) :=
      notMem_tsupport_iff_eventuallyEq.mp (fun h => hz (hχΩ h))
    have hev' : posExt_GM χ f =ᶠ[𝓝 z] fun _ => (1 : ℝ) := by
      filter_upwards [hev] with w hw
      simp [posExt_GM, hw]
    exact contDiffAt_const.congr_of_eventuallyEq hev'

theorem posExt_pos_GM {χ f : ℂ → ℝ} {Ω : Set ℂ} (hχΩ : tsupport χ ⊆ Ω)
    (hχ01 : ∀ z, 0 ≤ χ z ∧ χ z ≤ 1) (hf : ∀ z ∈ Ω, 0 < f z) (z : ℂ) :
    0 < posExt_GM χ f z := by
  by_cases hz : z ∈ Ω
  · have h0 := (hχ01 z).1
    have h1 := (hχ01 z).2
    have hfz := hf z hz
    unfold posExt_GM
    rcases le_total 1 (f z) with h | h
    · nlinarith
    · nlinarith
  · rw [posExt_eq_one_GM hχΩ hz]
    exact one_pos

theorem exists_posExt_le_GM {χ f : ℂ → ℝ} {Ω : Set ℂ} (hχΩ : tsupport χ ⊆ Ω)
    (hχc : IsCompact (tsupport χ)) (hχ01 : ∀ z, 0 ≤ χ z ∧ χ z ≤ 1)
    (hf : ContinuousOn f Ω) : ∃ C : ℝ, ∀ z, posExt_GM χ f z ≤ C := by
  obtain ⟨C, hC⟩ := hχc.exists_bound_of_continuousOn (hf.mono hχΩ)
  refine ⟨max C 1, fun z => ?_⟩
  by_cases hz : z ∈ tsupport χ
  · have h0 := (hχ01 z).1
    have h1 := (hχ01 z).2
    have hfz : f z ≤ max C 1 := ((le_abs_self _).trans (hC z hz)).trans (le_max_left _ _)
    have h1' : (1 : ℝ) ≤ max C 1 := le_max_right _ _
    unfold posExt_GM
    nlinarith
  · have : χ z = 0 := image_eq_zero_of_notMem_tsupport hz
    simp [posExt_GM, this]

/-- 正下界：`f > 0` 连续 on `Ω`、`tsupport χ` 紧 `⊆ Ω` ⇒ `posExt_GM χ f ≥ δ > 0` 处处成立
（于是 `posExt_GM χ ρ` 作共形因子给出 complete 度量）。 -/
theorem exists_le_posExt_GM {χ f : ℂ → ℝ} {Ω : Set ℂ} (hχΩ : tsupport χ ⊆ Ω)
    (hχc : IsCompact (tsupport χ)) (hχ01 : ∀ z, 0 ≤ χ z ∧ χ z ≤ 1)
    (hf : ContinuousOn f Ω) (hfpos : ∀ z ∈ Ω, 0 < f z) :
    ∃ δ > 0, ∀ z, δ ≤ posExt_GM χ f z := by
  have hpt : ∀ z, min (f z) 1 ≤ posExt_GM χ f z := by
    intro z
    have h0 := (hχ01 z).1
    have h1 := (hχ01 z).2
    unfold posExt_GM
    rcases le_total 1 (f z) with h | h
    · rw [min_eq_right h]
      nlinarith
    · rw [min_eq_left h]
      nlinarith
  rcases (tsupport χ).eq_empty_or_nonempty with he | hne
  · refine ⟨1, one_pos, fun z => ?_⟩
    have : χ z = 0 := image_eq_zero_of_notMem_tsupport (by rw [he]; exact notMem_empty z)
    simp [posExt_GM, this]
  · obtain ⟨z₀, hz₀, hmin⟩ := hχc.exists_isMinOn hne (hf.mono hχΩ)
    refine ⟨min (f z₀) 1, lt_min (hfpos z₀ (hχΩ hz₀)) one_pos, fun z => ?_⟩
    by_cases hz : z ∈ tsupport χ
    · exact (min_le_min_right 1 (isMinOn_iff.mp hmin z hz)).trans (hpt z)
    · have : χ z = 0 := image_eq_zero_of_notMem_tsupport hz
      simp [posExt_GM, this]

end DifferentialGeometry.Geometry
