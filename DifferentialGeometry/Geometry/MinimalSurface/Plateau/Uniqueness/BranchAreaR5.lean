import DifferentialGeometry.Geometry.Measure.Area.PiecewiseAreaAREA
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# O-MY-R5：R5-B 的面积重数与连通性工具（"可测单射分支集"）

* `isPreconnected_ball_diff_countable_R5`：开球去掉可数集仍连通（经 `univBall` 同胚到 `ℂ`，再用
  Mathlib `Set.Countable.isPathConnected_compl_of_one_lt_rank`）。用于 `R = D° \ B`（`B` = branch points）
  与 `D_{r₂} \ C`。
* `riemannianArea_image_le_R5`：**不要求单射**的面积下界 `A(u, α '' U) ≤ A(u ∘ α, U)`——`α` 在开集 `U`
  上连续、局部 bi-Lipschitz（局部 Lipschitz + 局部下界）。证明：Lindelöf 取可数 bi-Lipschitz 开块 `P n`，
  在**像**上 `disjointed`（`T n := α '' P n \ ⋃_{k<n} α '' P k`），回拉 `s n := P n ∩ α⁻¹(T n)` 得互不相交、
  `α` 在每块上单射且 `α '' s n = T n` 的可测分支集；每块用 S-MY-AREA 的 `riemannianArea_precomp_subset_AREA`，
  再用非负密度单调性。R5 的 crossing 排除与 degree one 都只用这一条。
-/

set_option autoImplicit false
noncomputable section

open Manifold Set Filter MeasureTheory DifferentialGeometry
open scoped Topology Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry.Geometry

/-- 开球去掉可数集仍（预）连通。 -/
theorem isPreconnected_ball_diff_countable_R5 {c : ℂ} {r : ℝ} {C : Set ℂ} (hC : C.Countable) :
    IsPreconnected (Metric.ball c r \ C) := by
  rcases le_or_gt r 0 with hr | hr
  · rw [Metric.ball_eq_empty.mpr hr, empty_sdiff]
    exact isPreconnected_empty
  let e := OpenPartialHomeomorph.univBall c r
  have htarget : e.target = Metric.ball c r := OpenPartialHomeomorph.univBall_target c hr
  have hsource : e.source = univ := OpenPartialHomeomorph.univBall_source c r
  let S : Set ℂ := (e.symm '' (C ∩ Metric.ball c r))ᶜ
  have hrank : 1 < Module.rank ℝ ℂ := by
    rw [Complex.rank_real_complex]
    norm_num
  have hS : IsPathConnected S :=
    ((hC.mono inter_subset_left).image _).isPathConnected_compl_of_one_lt_rank hrank
  have himage : e '' S = Metric.ball c r \ C := by
    ext y
    constructor
    · rintro ⟨x, hxS, rfl⟩
      have hxsrc : x ∈ e.source := by rw [hsource]; exact mem_univ x
      have hyt : e x ∈ Metric.ball c r := htarget ▸ e.map_source hxsrc
      refine ⟨hyt, fun hyC => hxS ⟨e x, ⟨hyC, hyt⟩, e.left_inv hxsrc⟩⟩
    · rintro ⟨hyB, hyC⟩
      have hyt : y ∈ e.target := htarget ▸ hyB
      refine ⟨e.symm y, ?_, e.right_inv hyt⟩
      rintro ⟨y', ⟨hy'C, hy'B⟩, hy'⟩
      have hy't : y' ∈ e.target := htarget ▸ hy'B
      have : y' = y := by
        rw [← e.right_inv hy't, hy', e.right_inv hyt]
      exact hyC (this ▸ hy'C)
  rw [← himage]
  exact (hS.image (OpenPartialHomeomorph.continuous_univBall c r)).isConnected.isPreconnected

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T3Space M]

/-- **面积下界（不要求单射）**：`u` 全局 Riemannian-Lipschitz；`α` 在开集 `U` 上连续、局部 bi-Lipschitz；
`α '' U` 有界；`u ∘ α` 的面积密度在 `U` 上可积 ⇒ `A(u, α '' U) ≤ A(u ∘ α, U)`。 -/
theorem riemannianArea_image_le_R5 (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {u : ℂ → M} {C : ℝ≥0}
    (hu : ∀ x y, riemannianEDistOf g (u x) (u y) ≤ (C : ℝ≥0∞) * edist x y)
    {α : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded (α '' U))
    (hint : IntegrableOn (riemannianAreaDensity g (u ∘ α)) U)
    (hcont : ContinuousOn α U)
    (hloc : ∀ x ∈ U, ∃ W ∈ 𝓝 x, ∃ K L : ℝ≥0, LipschitzOnWith K α W ∧
      ∀ y ∈ W, ∀ z ∈ W, edist y z ≤ (L : ℝ≥0∞) * edist (α y) (α z)) :
    riemannianArea g u (α '' U) ≤ riemannianArea g (u ∘ α) U := by
  classical
  rcases U.eq_empty_or_nonempty with rfl | hne
  · simp [riemannianArea]
  have himfin : volume (α '' U) ≠ ⊤ := hUb.measure_lt_top.ne
  have hiR : IntegrableOn (riemannianAreaDensity g u) (α '' U) := by
    have : IsFiniteMeasure (volume.restrict (α '' U)) := isFiniteMeasure_restrict.mpr himfin
    exact integrableOn_riemannianAreaDensity_of_lipschitz g hu _
  choose! Wf hWf Kf Lf hKf hLf using hloc
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
  have hPW : ∀ n, P n ⊆ Wf (c n) := fun n => interior_subset.trans inter_subset_left
  have hUP : U = ⋃ n, P n := by
    refine Subset.antisymm ?_ (iUnion_subset hPU)
    intro x hx
    obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (htcov hx)
    rw [hc] at hy
    obtain ⟨n, rfl⟩ := hy
    exact mem_iUnion.mpr ⟨n, hxy⟩
  have hPlip : ∀ n, LipschitzOnWith (Kf (c n)) α (P n) := fun n =>
    (hKf (c n) (hcU n)).mono (hPW n)
  have hPlow : ∀ n, ∀ y ∈ P n, ∀ z ∈ P n,
      edist y z ≤ (Lf (c n) : ℝ≥0∞) * edist (α y) (α z) := fun n y hy z hz =>
    hLf (c n) (hcU n) y (hPW n hy) z (hPW n hz)
  have hPinj : ∀ n, InjOn α (P n) := by
    intro n x hx y hy hxy
    apply edist_eq_zero.mp
    have h := hPlow n x hx y hy
    rw [hxy, edist_self, mul_zero] at h
    exact le_antisymm h zero_le
  have hPim : ∀ n, MeasurableSet (α '' P n) := fun n =>
    (hPopen n).measurableSet.image_of_continuousOn_injOn (hcont.mono (hPU n)) (hPinj n)
  -- 像上的 disjointed 分块
  let T : ℕ → Set ℂ := disjointed fun n => α '' P n
  have hTm : ∀ n, MeasurableSet (T n) := MeasurableSet.disjointed hPim
  have hTd : Pairwise (Function.onFun Disjoint T) := disjoint_disjointed _
  have hTsub : ∀ n, T n ⊆ α '' P n := disjointed_subset _
  have hTU : ⋃ n, T n = α '' U := by
    rw [iUnion_disjointed, hUP, image_iUnion]
  -- 回拉成源上的可测单射分支集
  let αt : ℂ → ℂ := U.piecewise α (fun _ => 0)
  have hαt : Measurable αt :=
    hcont.measurable_piecewise continuousOn_const hU.measurableSet
  have hαtU : ∀ x ∈ U, αt x = α x := fun x hx => U.piecewise_eq_of_mem _ _ hx
  let s : ℕ → Set ℂ := fun n => P n ∩ αt ⁻¹' T n
  have hsm : ∀ n, MeasurableSet (s n) := fun n =>
    (hPopen n).measurableSet.inter (hαt (hTm n))
  have hsP : ∀ n, s n ⊆ P n := fun n => inter_subset_left
  have hsU : ∀ n, s n ⊆ U := fun n => (hsP n).trans (hPU n)
  have hsim : ∀ n, α '' s n = T n := by
    intro n
    ext y
    constructor
    · rintro ⟨x, ⟨hxP, hxT⟩, rfl⟩
      have : αt x = α x := hαtU x (hPU n hxP)
      rw [mem_preimage, this] at hxT
      exact hxT
    · intro hy
      obtain ⟨x, hxP, rfl⟩ := hTsub n hy
      refine ⟨x, ⟨hxP, ?_⟩, rfl⟩
      rw [mem_preimage, hαtU x (hPU n hxP)]
      exact hy
  have hsd : Pairwise (Function.onFun Disjoint s) := by
    intro m n hmn
    rw [Function.onFun, Set.disjoint_left]
    intro x hxm hxn
    have hm : α x ∈ T m := by rw [← hsim m]; exact mem_image_of_mem α hxm
    have hn : α x ∈ T n := by rw [← hsim n]; exact mem_image_of_mem α hxn
    exact Set.disjoint_left.mp (hTd hmn) hm hn
  have hcell : ∀ n, riemannianArea g (u ∘ α) (s n) = riemannianArea g u (T n) := by
    intro n
    rw [← hsim n]
    exact riemannianArea_precomp_subset_AREA g hu (hPopen n) (hsm n) (hsP n) (hPlip n)
      (hPlow n)
  have hsUU : (⋃ n, s n) ⊆ U := iUnion_subset hsU
  calc
    riemannianArea g u (α '' U) = riemannianArea g u (⋃ n, T n) := by rw [hTU]
    _ = ∑' n, riemannianArea g u (T n) := by
      unfold riemannianArea
      exact integral_iUnion hTm hTd (by rw [hTU]; exact hiR)
    _ = ∑' n, riemannianArea g (u ∘ α) (s n) := tsum_congr fun n => (hcell n).symm
    _ = riemannianArea g (u ∘ α) (⋃ n, s n) := by
      unfold riemannianArea
      exact (integral_iUnion hsm hsd (hint.mono_set hsUU)).symm
    _ ≤ riemannianArea g (u ∘ α) U := by
      unfold riemannianArea
      apply setIntegral_mono_set hint
      · exact Filter.Eventually.of_forall fun z => riemannianAreaDensity_nonneg g _ z
      · exact Filter.Eventually.of_forall hsUU

end DifferentialGeometry.Geometry
