/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Geometry.Measure.Area.PiecewiseReparametrization

/-!
# S-MY-AREA G1：没有全局左逆的面积换元（`area_precomp_of_local_bilipschitz_exhaustion_AREA`）

外审 R-MY3 Q4(a) / D-R-MY3-11：R9 的 `α : |T| ≅ D̄` 只有单向 Lipschitz，在顶点处退化（逆不 Lipschitz），
所以不能整块调用要求**全局** Lipschitz 左逆的 `riemannianArea_precomp`。本文件给的 adapter：

* `riemannianArea_precomp_subset_AREA`：`riemannianArea_precomp_on` 的 measurable 子集版——`φ` 只在
  开集 `W` 上 bi-Lipschitz，`s ⊆ W` 可测即可（树内版要求 `s` 本身是开集）。
* `integrableOn_density_comp_lipschitzOn_AREA`：`u` Lipschitz、`φ` 在开集 `U` 上 Lipschitz，
  `U` 有限测度 ⇒ `u ∘ φ` 的面积密度在 `U` 上可积（面积换元两边都是有限值，避开 junk 积分）。
* `area_precomp_of_local_bilipschitz_exhaustion_AREA`（**G1**）：`u` 全局 Riemannian-Lipschitz，
  `U` 有界开集，`α` 在 `U` 上 Lipschitz、`U` 上单射、**局部** bi-Lipschitz（每点有邻域使
  `edist y z ≤ L * edist (α y) (α z)`）⇒ `A(u ∘ α, U) = A(u, α '' U)`。证明：Lindelöf 取可数个
  bi-Lipschitz 开块覆盖 `U`，`disjointed` 切成互不相交的可测块，每块用 `riemannianArea_precomp_subset_AREA`，
  再用非负密度的可数可加性求和——这是「紧 exhaustion + 单调收敛」的等价形式（不需要紧性 / `CompactExhaustion`）。
  **没有**用 `α` 的全局左逆，也**没有**要求 `α` 在顶点附近 bi-Lipschitz（顶点不在 `U` 里）。
* `area_precomp_of_local_bilipschitz_null_AREA`：`K ⊇ U`、`K ∖ U` 零测（顶点 / 边等例外集）、`α` 在 `K` 上
  Lipschitz ⇒ `A(u ∘ α, K) = A(u, α '' K)`（例外集的像由 Lipschitz 映零测集到零测集，不影响右边）。
-/

set_option autoImplicit false
noncomputable section

open Manifold Set Filter MeasureTheory DifferentialGeometry
open scoped Topology Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T3Space M]

/-- `riemannianArea_precomp_on` 的 measurable 子集版：`φ` 在开集 `W` 上 Lipschitz 且有下界
`edist x y ≤ L * edist (φ x) (φ y)`，`s ⊆ W` 可测 ⇒ `A(u ∘ φ, s) = A(u, φ '' s)`。 -/
theorem riemannianArea_precomp_subset_AREA (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {u : ℂ → M} {φ : ℂ → ℂ} {W s : Set ℂ} {C K L : ℝ≥0}
    (hu : ∀ x y, riemannianEDistOf g (u x) (u y) ≤ (C : ℝ≥0∞) * edist x y)
    (hW : IsOpen W) (hs : MeasurableSet s) (hsW : s ⊆ W) (hφ : LipschitzOnWith K φ W)
    (hL : ∀ x ∈ W, ∀ y ∈ W, edist x y ≤ (L : ℝ≥0∞) * edist (φ x) (φ y)) :
    riemannianArea g (u ∘ φ) s = riemannianArea g u (φ '' s) := by
  have hinj : InjOn φ W := by
    intro x hx y hy heq
    apply edist_eq_zero.mp
    apply le_antisymm _ bot_le
    simpa only [heq, edist_self, mul_zero] using! hL x hx y hy
  let ψ := Function.invFunOn φ W
  have hi : ∀ x ∈ W, ψ (φ x) = x := hinj.leftInvOn_invFunOn
  have hψ : LipschitzOnWith L ψ (φ '' W) := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [hi x hx, hi y hy]
    exact hL x hx y hy
  obtain ⟨Φ, hΦ, heΦ⟩ := hφ.extend_finite_dimension
  obtain ⟨Ψ, hΨ, heΨ⟩ := hψ.extend_finite_dimension
  have hi' (x : ℂ) (hx : x ∈ s) : Ψ (Φ x) = x := by
    have hxW := hsW hx
    rw [← heΦ hxW, ← heΨ (mem_image_of_mem φ hxW), hi x hxW]
  calc
    riemannianArea g (u ∘ φ) s = riemannianArea g (u ∘ Φ) s := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem hs] with z hz
      refine riemannianAreaDensity_congr g ?_
      filter_upwards [hW.mem_nhds (hsW hz)] with w hw
      exact congrArg u (heΦ hw)
    _ = riemannianArea g u (Φ '' s) := riemannianArea_precomp g hu hΦ hΨ hs hi'
    _ = riemannianArea g u (φ '' s) := by rw [(heΦ.mono hsW).image_eq]

/-- `u` 全局 Riemannian-Lipschitz，`φ` 在开集 `U` 上 Lipschitz，`U` 有限测度 ⇒ `u ∘ φ` 的面积密度在
`U` 上可积（用 `φ` 的 Lipschitz 延拓把密度换成全局 Lipschitz 映射 `u ∘ Φ` 的密度）。 -/
theorem integrableOn_density_comp_lipschitzOn_AREA (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {u : ℂ → M} {φ : ℂ → ℂ} {U : Set ℂ} {C K : ℝ≥0}
    (hu : ∀ x y, riemannianEDistOf g (u x) (u y) ≤ (C : ℝ≥0∞) * edist x y)
    (hU : IsOpen U) (hφ : LipschitzOnWith K φ U) (hfin : volume U ≠ ⊤) :
    IntegrableOn (riemannianAreaDensity g (u ∘ φ)) U := by
  have : IsFiniteMeasure (volume.restrict U) := isFiniteMeasure_restrict.mpr hfin
  obtain ⟨Φ, hΦ, heΦ⟩ := hφ.extend_finite_dimension
  obtain ⟨KΦ, hKΦ⟩ : ∃ KΦ : ℝ≥0, LipschitzWith KΦ Φ := ⟨_, hΦ⟩
  have huΦ : ∀ x y, riemannianEDistOf g ((u ∘ Φ) x) ((u ∘ Φ) y) ≤
      ((C * KΦ : ℝ≥0) : ℝ≥0∞) * edist x y := by
    intro x y
    calc
      _ ≤ (C : ℝ≥0∞) * edist (Φ x) (Φ y) := hu _ _
      _ ≤ (C : ℝ≥0∞) * ((KΦ : ℝ≥0∞) * edist x y) := by
        gcongr
        exact hKΦ x y
      _ = _ := by rw [ENNReal.coe_mul, mul_assoc]
  apply (integrableOn_riemannianAreaDensity_of_lipschitz g huΦ U).congr
  filter_upwards [ae_restrict_mem hU.measurableSet] with z hz
  refine (riemannianAreaDensity_congr g ?_).symm
  filter_upwards [hU.mem_nhds hz] with w hw
  exact congrArg u (heΦ hw)

/-- 有界集的 Lipschitz 像仍有有限测度（延拓成全局 Lipschitz 后像有界）。 -/
theorem volume_image_ne_top_of_lipschitzOn_AREA {α : ℂ → ℂ} {U : Set ℂ} {K : ℝ≥0}
    (hα : LipschitzOnWith K α U) (hUb : Bornology.IsBounded U) : volume (α '' U) ≠ ⊤ := by
  obtain ⟨Φ, hΦ, heΦ⟩ := hα.extend_finite_dimension
  rw [heΦ.image_eq]
  exact (hΦ.isBounded_image hUb).measure_lt_top.ne

/-- **G1**（`area_precomp_of_local_bilipschitz_exhaustion_AREA`）：没有全局左逆的面积换元。
`u` 全局 Riemannian-Lipschitz；`U` 有界开集（避开顶点的 2-面内部）；`α` 在 `U` 上 Lipschitz 且单射，
并且**局部** bi-Lipschitz（每点 `x ∈ U` 有邻域 `W` 与常数 `L` 使 `edist y z ≤ L * edist (α y) (α z)`
对 `y z ∈ W` 成立）⇒ `A(u ∘ α, U) = A(u, α '' U)`。 -/
theorem area_precomp_of_local_bilipschitz_exhaustion_AREA
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {u : ℂ → M} {C K : ℝ≥0}
    (hu : ∀ x y, riemannianEDistOf g (u x) (u y) ≤ (C : ℝ≥0∞) * edist x y)
    {α : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hα : LipschitzOnWith K α U) (hinj : InjOn α U)
    (hloc : ∀ x ∈ U, ∃ W ∈ 𝓝 x, ∃ L : ℝ≥0, ∀ y ∈ W, ∀ z ∈ W,
      edist y z ≤ (L : ℝ≥0∞) * edist (α y) (α z)) :
    riemannianArea g (u ∘ α) U = riemannianArea g u (α '' U) := by
  classical
  have hUfin : volume U ≠ ⊤ := hUb.measure_lt_top.ne
  have himfin : volume (α '' U) ≠ ⊤ := volume_image_ne_top_of_lipschitzOn_AREA hα hUb
  have hiL : IntegrableOn (riemannianAreaDensity g (u ∘ α)) U :=
    integrableOn_density_comp_lipschitzOn_AREA g hu hU hα hUfin
  have hiR : IntegrableOn (riemannianAreaDensity g u) (α '' U) := by
    have : IsFiniteMeasure (volume.restrict (α '' U)) := isFiniteMeasure_restrict.mpr himfin
    exact integrableOn_riemannianAreaDensity_of_lipschitz g hu _
  rcases U.eq_empty_or_nonempty with rfl | hne
  · simp [riemannianArea]
  -- 局部 bi-Lipschitz 开块 `O x ⊆ U`
  choose! Wf hWf Lf hLf using hloc
  let O : ℂ → Set ℂ := fun x => interior (Wf x ∩ U)
  have hOnhds : ∀ x ∈ U, O x ∈ 𝓝[U] x := fun x hx =>
    mem_nhdsWithin_of_mem_nhds
      (interior_mem_nhds.mpr (Filter.inter_mem (hWf x hx) (hU.mem_nhds hx)))
  obtain ⟨t, htU, htc, htcov⟩ := TopologicalSpace.countable_cover_nhdsWithin hOnhds
  have htne : t.Nonempty := by
    obtain ⟨x, hx⟩ := hne
    obtain ⟨y, hy, -⟩ := mem_iUnion₂.mp (htcov hx)
    exact ⟨y, hy⟩
  obtain ⟨c, hc⟩ := htc.exists_eq_range htne
  let P : ℕ → Set ℂ := fun n => O (c n)
  have hcU : ∀ n, c n ∈ U := fun n => htU (by rw [hc]; exact mem_range_self n)
  have hPopen : ∀ n, IsOpen (P n) := fun n => isOpen_interior
  have hPU : ∀ n, P n ⊆ U := fun n => interior_subset.trans inter_subset_right
  have hUP : U = ⋃ n, P n := by
    refine Subset.antisymm ?_ (iUnion_subset hPU)
    intro x hx
    obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (htcov hx)
    rw [hc] at hy
    obtain ⟨n, rfl⟩ := hy
    exact mem_iUnion.mpr ⟨n, hxy⟩
  let s : ℕ → Set ℂ := disjointed P
  have hsm : ∀ n, MeasurableSet (s n) := MeasurableSet.disjointed fun n => (hPopen n).measurableSet
  have hsd : Pairwise (Function.onFun Disjoint s) := disjoint_disjointed P
  have hsP : ∀ n, s n ⊆ P n := disjointed_subset P
  have hsU : ⋃ n, s n = U := by rw [iUnion_disjointed, ← hUP]
  have hsUn : ∀ n, s n ⊆ U := fun n => (hsP n).trans (hPU n)
  have hcell : ∀ n, riemannianArea g (u ∘ α) (s n) = riemannianArea g u (α '' s n) := by
    intro n
    refine riemannianArea_precomp_subset_AREA g hu (hPopen n) (hsm n) (hsP n)
      (hα.mono (hPU n)) (L := Lf (c n)) ?_
    intro x hx y hy
    exact hLf (c n) (hcU n) x (interior_subset.trans inter_subset_left hx) y
      (interior_subset.trans inter_subset_left hy)
  have himm : ∀ n, MeasurableSet (α '' s n) := fun n =>
    (hsm n).image_of_continuousOn_injOn (hα.continuousOn.mono (hsUn n)) (hinj.mono (hsUn n))
  have himd : Pairwise (Function.onFun Disjoint fun n => α '' s n) := by
    intro m n hmn
    rw [Function.onFun, Set.disjoint_iff_inter_eq_empty, ← hinj.image_inter (hsUn m) (hsUn n),
      (Set.disjoint_iff_inter_eq_empty.mp (hsd hmn)), image_empty]
  have himU : ⋃ n, α '' s n = α '' U := by rw [← image_iUnion, hsU]
  calc
    riemannianArea g (u ∘ α) U = riemannianArea g (u ∘ α) (⋃ n, s n) := by rw [hsU]
    _ = ∑' n, riemannianArea g (u ∘ α) (s n) := by
      unfold riemannianArea
      exact integral_iUnion hsm hsd (by rw [hsU]; exact hiL)
    _ = ∑' n, riemannianArea g u (α '' s n) := tsum_congr hcell
    _ = riemannianArea g u (⋃ n, α '' s n) := by
      unfold riemannianArea
      exact (integral_iUnion himm himd (by rw [himU]; exact hiR)).symm
    _ = riemannianArea g u (α '' U) := by rw [himU]

/-- **G1 的例外集版本**：`K ⊇ U`，`K ∖ U` 零测（顶点 / 边等），`α` 在 `K` 上 Lipschitz ⇒
`A(u ∘ α, K) = A(u, α '' K)`。例外集在 `α` 下的像是零测的（Lipschitz 映零测到零测），不影响右边。 -/
theorem area_precomp_of_local_bilipschitz_null_AREA
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {u : ℂ → M} {C K : ℝ≥0}
    (hu : ∀ x y, riemannianEDistOf g (u x) (u y) ≤ (C : ℝ≥0∞) * edist x y)
    {α : ℂ → ℂ} {U S : Set ℂ} (hU : IsOpen U) (hUS : U ⊆ S) (hnull : volume (S \ U) = 0)
    (hSb : Bornology.IsBounded S) (hα : LipschitzOnWith K α S) (hinj : InjOn α U)
    (hloc : ∀ x ∈ U, ∃ W ∈ 𝓝 x, ∃ L : ℝ≥0, ∀ y ∈ W, ∀ z ∈ W,
      edist y z ≤ (L : ℝ≥0∞) * edist (α y) (α z)) :
    riemannianArea g (u ∘ α) S = riemannianArea g u (α '' S) := by
  have hmain := area_precomp_of_local_bilipschitz_exhaustion_AREA g hu hU (hSb.subset hUS)
    (hα.mono hUS) hinj hloc
  have hSU : S =ᵐ[volume] U :=
    EventuallyLE.antisymm (ae_le_set.mpr hnull) (LE.le.eventuallySubset hUS)
  obtain ⟨Φ, hΦ, heΦ⟩ := hα.extend_finite_dimension
  have hz : volume (α '' (S \ U)) = 0 := by
    rw [(heΦ.mono sdiff_subset).image_eq]
    exact DifferentialGeometry.Analysis.volume_image_eq_zero_of_lipschitz hΦ hnull
  have himg : α '' S =ᵐ[volume] α '' U := by
    refine EventuallyLE.antisymm (ae_le_set.mpr ?_) (LE.le.eventuallySubset
      (image_mono hUS))
    refine measure_mono_null ?_ hz
    rintro _ ⟨⟨x, hxS, rfl⟩, hxn⟩
    exact ⟨x, ⟨hxS, fun hxU => hxn ⟨x, hxU, rfl⟩⟩, rfl⟩
  calc
    riemannianArea g (u ∘ α) S = riemannianArea g (u ∘ α) U := setIntegral_congr_set hSU
    _ = riemannianArea g u (α '' U) := hmain
    _ = riemannianArea g u (α '' S) := setIntegral_congr_set himg.symm

end DifferentialGeometry.Geometry
