import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Restriction
import DifferentialGeometry.Topology.Embedding.TransverseIntersectionLimit

/-!
# S-MY-R15T：外审 R15 的 transport adapter（D-R-MY2a-4）

trimmed 盘 `q_r := affineSubdisk q 0 r` 的 K13 no-transverse 谓词（在 `diskExtension q_r` 的开盘
`ball 0 1` 上）经「R1 singleton collar + source 缩放 + `diskExtension` 的内部 equality 搬导数」回传到
原盘 `diskExtension q` 上逐字的 K13 `hNoTransverse` 谓词（`IsMorreyDisk.isEmbedding_of_no_transverse`
的同名前提；`hNT` 的结论，sheet-MY-hNT §1）。

外审公式：`(D(q∘s_r)_u).coprod (−D(q∘s_r)_v) = ((Dq_x).coprod (−Dq_y)) ∘ (Ds_r × Ds_r)`，
`x = r u`、`y = r v`，`s_r z = r • z`。

* `diskExtension_affineSubdisk_zero_apply_R15T`：`ball 0 1` 内 `dE q_r w = dE q (r • w)`；
  `…_eventuallyEq_R15T`：同一等式作为 `𝓝 u` 上的 eventual equality（用于搬导数）。
* `mfderiv_diskExtension_affineSubdisk_zero_R15T`：`D(dE q_r)_u = D(dE q)_{r u} ∘ (r • id)`
  （`D(dE q)_{r u}` 单射 ⇒ `MDifferentiableAt`，否则 `mfderiv = 0` 不单射；不要 smooth extension）。
* `surjective_coprod_comp_smul_R15T`：`A.coprod (−B)` 满射 ⇒ `(A∘T).coprod (−(B∘T))` 满射
  （`T = r • id`，`r ≠ 0`；线性同构复合保持 surjectivity）。
* **G1** `noTransverse_of_trimmed_R15T`：collar `∀ z w, ρ₀ < ‖z‖ → q z = q w → z = w`
  （R1 的 G1 结论形）+ `0 < r`、`ρ₀ < r` + trimmed 盘的 K13 谓词 ⇒ 原盘 `diskExtension q` 的 K13
  谓词。碰撞点都在 `closedBall 0 ρ₀`（collar）⇒ `u = x / r` 在 `ball 0 1`。**前提最少**：
  `IsMorreyDisk` / `SmoothDiskExtension` / 闭盘 rank 都只用来产生 collar（R1 已做），这里不需要；
  `r < 1` 也不需要。
* **G1b** `contMDiffOn_diskExtension_affineSubdisk_zero_R15T`：`SmoothDiskExtension q Q`、
  `0 ≤ r ≤ 1` ⇒ `dE q_r` 在 `ball 0 1` 上 `C¹`（MY-13 的 `hf₀`）。
* **G1c** `noTransverse_of_c1_limit_trimmed_R15T`：MY-13（`Topology.Manifold` 版）对 `dE q_r` 在
  `S = ball 0 1` 上给 trimmed 谓词（只要 `v n` 在 `ball 0 1` 上单射、chart 内 `C¹` 收敛到 `dE q_r`）
  ⇒ G1 ⇒ 原盘谓词。这是 R8 + R15 到 `hNT` 结论的终端接口；**不**证 approximants 存在。

只传递 no-transverse；不声称极限 embedded；不碰 analytic。
-/

set_option autoImplicit false
noncomputable section

open Set Filter Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Topology
open scoped Topology ContDiff Manifold

namespace DifferentialGeometry.Geometry

section Transport

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

/-- `ball 0 1` 内 `diskExtension (affineSubdisk q 0 r) w = diskExtension q (r • w)`。 -/
theorem diskExtension_affineSubdisk_zero_apply_R15T (q : C(closedDisk, M)) (r : ℝ) {w : ℂ}
    (hw : w ∈ Metric.ball (0 : ℂ) 1) :
    diskExtension (affineSubdisk q 0 r) w = diskExtension q (r • w) := by
  have hw' : w ∈ Metric.closedBall (0 : ℂ) 1 := Metric.ball_subset_closedBall hw
  refine (diskExtension_coe (affineSubdisk q 0 r) ⟨w, hw'⟩).trans ?_
  change diskExtension q (0 + r • w) = _
  rw [zero_add]

/-- 同一等式作为 `𝓝 u` 上的 eventual equality（`u ∈ ball 0 1`）。 -/
theorem diskExtension_affineSubdisk_zero_eventuallyEq_R15T (q : C(closedDisk, M)) (r : ℝ)
    {u : ℂ} (hu : u ∈ Metric.ball (0 : ℂ) 1) :
    diskExtension (affineSubdisk q 0 r) =ᶠ[𝓝 u] fun w => diskExtension q (r • w) := by
  filter_upwards [Metric.isOpen_ball.mem_nhds hu] with w hw
  exact diskExtension_affineSubdisk_zero_apply_R15T q r hw

/-- source 缩放的链式法则：`D(dE q_r)_u = D(dE q)_{r u} ∘ (r • id)`。`D(dE q)_{r u}` 单射
给出 `MDifferentiableAt`（否则 `mfderiv = 0`，在非平凡的 `ℂ` 上不单射），故不需要 smooth extension。 -/
theorem mfderiv_diskExtension_affineSubdisk_zero_R15T {q : C(closedDisk, M)} {r : ℝ}
    {u : ℂ} (hu : u ∈ Metric.ball (0 : ℂ) 1)
    (hinj : Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension q) (r • u))) :
    mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension (affineSubdisk q 0 r)) u =
      (show ℂ →L[ℝ] E from
        mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension q) (r • u)).comp
        (r • ContinuousLinearMap.id ℝ ℂ) := by
  have hdiff : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension q) (r • u) := by
    by_contra h
    rw [mfderiv_zero_of_not_mdifferentiableAt h] at hinj
    have h01 : (0 : ℂ) = (1 : ℂ) := hinj (a₁ := (0 : ℂ)) (a₂ := (1 : ℂ)) rfl
    exact zero_ne_one h01
  have hS : HasMFDerivAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (fun z : ℂ => r • z) u
      (r • ContinuousLinearMap.id ℝ ℂ) :=
    ((hasFDerivAt_id u).const_smul r).hasMFDerivAt
  have hcomp := hdiff.hasMFDerivAt.comp u hS
  exact (hcomp.congr_of_eventuallyEq
    (diskExtension_affineSubdisk_zero_eventuallyEq_R15T q r hu)).mfderiv

/-- 线性同构复合保持 surjectivity：`A.coprod (−B)` 满射 ⇒ `(A∘T).coprod (−(B∘T))` 满射，
`T = r • id`、`r ≠ 0`。 -/
theorem surjective_coprod_comp_smul_R15T {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {r : ℝ} (hr : r ≠ 0) (A B : ℂ →L[ℝ] F) (h : Function.Surjective (A.coprod (-B))) :
    Function.Surjective
      ((A.comp (r • ContinuousLinearMap.id ℝ ℂ)).coprod
        (-(B.comp (r • ContinuousLinearMap.id ℝ ℂ)))) := by
  intro y
  obtain ⟨⟨z₁, z₂⟩, hz⟩ := h y
  refine ⟨⟨r⁻¹ • z₁, r⁻¹ • z₂⟩, ?_⟩
  simp only [ContinuousLinearMap.coprod_apply, ContinuousLinearMap.comp_apply,
    neg_apply, smul_apply, ContinuousLinearMap.id_apply, smul_inv_smul₀ hr] at hz ⊢
  exact hz

/-- **G1**（R15T）：R1 的 singleton collar + `0 < r`、`ρ₀ < r` + trimmed 盘
`affineSubdisk q 0 r` 的 K13 no-transverse 谓词（`diskExtension` 在 `ball 0 1` 上）⇒ 原盘
`diskExtension q` 上逐字的 K13 `hNoTransverse`（`IsMorreyDisk.isEmbedding_of_no_transverse`
的同名前提）。证明：碰撞点都在 `closedBall 0 ρ₀`（collar）；`u = x / r`、`v = y / r ∈ ball 0 1`；
`dE q_r (u) = dE q (x)`；`D(dE q_r)_u = D(dE q)_x ∘ (r • id)`；surjectivity 经线性同构等价。 -/
theorem noTransverse_of_trimmed_R15T {q : C(closedDisk, M)} {ρ₀ r : ℝ}
    (hcol : ∀ z w : closedDisk, ρ₀ < ‖(z : ℂ)‖ → q z = q w → z = w)
    (hr : 0 < r) (hρr : ρ₀ < r)
    (htrim : ∀ u ∈ Metric.ball (0 : ℂ) 1, ∀ v ∈ Metric.ball (0 : ℂ) 1,
      u ≠ v → diskExtension (affineSubdisk q 0 r) u = diskExtension (affineSubdisk q 0 r) v →
      Function.Injective
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension (affineSubdisk q 0 r)) u) →
      Function.Injective
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension (affineSubdisk q 0 r)) v) →
      ¬ Function.Surjective
        ((show ℂ →L[ℝ] E from
            mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension (affineSubdisk q 0 r)) u).coprod
          (-(show ℂ →L[ℝ] E from
            mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension (affineSubdisk q 0 r)) v)))) :
    ∀ x ∈ Metric.ball (0 : ℂ) 1, ∀ y ∈ Metric.ball (0 : ℂ) 1,
      x ≠ y → diskExtension q x = diskExtension q y →
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension q) x) →
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension q) y) →
      ¬ Function.Surjective
        ((show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension q) x).coprod
          (-(show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension q) y))) := by
  intro x hx y hy hxy hxyv hDx hDy hsurj
  -- collar：碰撞点（同像的不同点）都在 `closedBall 0 ρ₀` 内
  have key : ∀ a ∈ Metric.ball (0 : ℂ) 1, ∀ b ∈ Metric.ball (0 : ℂ) 1,
      diskExtension q a = diskExtension q b → ρ₀ < ‖a‖ → a = b := by
    intro a ha b hb hab hρa
    have ha' : a ∈ Metric.closedBall (0 : ℂ) 1 := Metric.ball_subset_closedBall ha
    have hb' : b ∈ Metric.closedBall (0 : ℂ) 1 := Metric.ball_subset_closedBall hb
    have hq : q ⟨a, ha'⟩ = q ⟨b, hb'⟩ :=
      (diskExtension_coe q ⟨a, ha'⟩).symm.trans (hab.trans (diskExtension_coe q ⟨b, hb'⟩))
    exact congrArg Subtype.val (hcol ⟨a, ha'⟩ ⟨b, hb'⟩ hρa hq)
  have hxc : ‖x‖ ≤ ρ₀ := by
    by_contra h
    exact hxy (key x hx y hy hxyv (not_le.mp h))
  have hyc : ‖y‖ ≤ ρ₀ := by
    by_contra h
    exact hxy (key y hy x hx hxyv.symm (not_le.mp h)).symm
  -- 缩放：`x = r • u`、`y = r • v`
  obtain ⟨u, rfl⟩ : ∃ u : ℂ, x = r • u := ⟨r⁻¹ • x, (smul_inv_smul₀ hr.ne' x).symm⟩
  obtain ⟨v, rfl⟩ : ∃ v : ℂ, y = r • v := ⟨r⁻¹ • y, (smul_inv_smul₀ hr.ne' y).symm⟩
  have hnorm : ∀ w : ℂ, ‖r • w‖ ≤ ρ₀ → w ∈ Metric.ball (0 : ℂ) 1 := by
    intro w hw
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr] at hw
    rw [Metric.mem_ball, dist_zero_right]
    by_contra h
    nlinarith [not_lt.mp h]
  have hu := hnorm u hxc
  have hv := hnorm v hyc
  have huv : u ≠ v := fun h => hxy (by rw [h])
  have hTinj : Function.Injective (fun z : ℂ => r • z) := smul_right_injective ℂ hr.ne'
  have hvalue : diskExtension (affineSubdisk q 0 r) u = diskExtension (affineSubdisk q 0 r) v := by
    rw [diskExtension_affineSubdisk_zero_apply_R15T q r hu,
      diskExtension_affineSubdisk_zero_apply_R15T q r hv]
    exact hxyv
  have hcu := mfderiv_diskExtension_affineSubdisk_zero_R15T hu hDx
  have hcv := mfderiv_diskExtension_affineSubdisk_zero_R15T hv hDy
  refine htrim u hu v hv huv hvalue ?_ ?_ ?_
  · rw [hcu]
    exact hDx.comp hTinj
  · rw [hcv]
    exact hDy.comp hTinj
  · have h := surjective_coprod_comp_smul_R15T hr.ne' _ _ hsurj
    rw [← hcu, ← hcv] at h
    exact h

end Transport

section C1Limit

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- **G1b**（R15T）：`SmoothDiskExtension q Q` + `0 ≤ r ≤ 1` ⇒ trimmed 盘的 `diskExtension` 在
`ball 0 1` 上 `C¹`（实际 `C^∞`）：`ball 0 1` 内 `dE q_r = Q ∘ (r • ·)` 局部成立。 -/
theorem contMDiffOn_diskExtension_affineSubdisk_zero_R15T {q : C(closedDisk, M)} {Q : ℂ → M}
    (hQ : SmoothDiskExtension (E := E) q Q) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 1 (diskExtension (affineSubdisk q 0 r))
      (Metric.ball (0 : ℂ) 1) := by
  intro u hu
  have hru : r • u ∈ Metric.ball (0 : ℂ) 1 := by
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_nonneg hr0]
    have hu' : ‖u‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using hu
    nlinarith [norm_nonneg u]
  have hevQ := hQ.eventuallyEq_diskExtension hru
  obtain ⟨-, N, hN, hDN, hQs⟩ := hQ
  have hQat : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ Q (r • u) :=
    hQs.contMDiffAt (hN.mem_nhds (hDN (Metric.ball_subset_closedBall hru)))
  have hsm : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (fun z : ℂ => r • z) u :=
    (contDiff_const_smul r).contMDiff.contMDiffAt
  have hcomp : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (Q ∘ fun z : ℂ => r • z) u := hQat.comp u hsm
  have heq : diskExtension (affineSubdisk q 0 r) =ᶠ[𝓝 u] Q ∘ fun z : ℂ => r • z := by
    filter_upwards [diskExtension_affineSubdisk_zero_eventuallyEq_R15T q r hu,
      ((continuous_const_smul r).tendsto u).eventually hevQ] with w hw1 hw2
    exact hw1.trans hw2.symm
  exact ((hcomp.congr_of_eventuallyEq heq).of_le (by simp)).contMDiffWithinAt

/-- **G1c**（R15T）：R8 + R15 到 `hNT` 结论的终端接口。trimmed 盘 `q_r = affineSubdisk q 0 r`
（`ρ₀ < r ≤ 1`，`ρ₀` 是 R1 collar）的 `diskExtension` 在 `ball 0 1` 上是某列 `ball 0 1` 上单射映射
`v n` 的 chartwise `C¹` 极限（MY-13 的 `hval / hchart / hder`，对每个 target chart `p`）⇒
原盘 `diskExtension q` 上逐字的 K13 `hNoTransverse`。MY-13 取 `Topology.Manifold` 版（全名引用）。 -/
theorem noTransverse_of_c1_limit_trimmed_R15T {q : C(closedDisk, M)} {Q : ℂ → M}
    (hQ : SmoothDiskExtension (E := E) q Q) {ρ₀ r : ℝ}
    (hcol : ∀ z w : closedDisk, ρ₀ < ‖(z : ℂ)‖ → q z = q w → z = w)
    (hr : 0 < r) (hρr : ρ₀ < r) (hr1 : r ≤ 1)
    {v : ℕ → ℂ → M}
    (hv : ∀ᶠ n in atTop, MDifferentiableOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (v n) (Metric.ball (0 : ℂ) 1))
    (hinj : ∀ᶠ n in atTop, InjOn (v n) (Metric.ball (0 : ℂ) 1))
    (hval : ∀ p : M, ∀ x ∈ Metric.ball (0 : ℂ) 1,
      diskExtension (affineSubdisk q 0 r) x ∈ (extChartAt 𝓘(ℝ, E) p).source →
      Tendsto (fun n => extChartAt 𝓘(ℝ, E) p (v n x)) atTop
        (𝓝 (extChartAt 𝓘(ℝ, E) p (diskExtension (affineSubdisk q 0 r) x))))
    (hchart : ∀ p : M, ∀ K : Set ℂ, IsCompact K →
      K ⊆ Metric.ball (0 : ℂ) 1 ∩
        diskExtension (affineSubdisk q 0 r) ⁻¹' (extChartAt 𝓘(ℝ, E) p).source →
      ∀ᶠ n in atTop, MapsTo (v n) K (extChartAt 𝓘(ℝ, E) p).source)
    (hder : ∀ p : M, ∀ K : Set ℂ, IsCompact K →
      K ⊆ Metric.ball (0 : ℂ) 1 ∩
        diskExtension (affineSubdisk q 0 r) ⁻¹' (extChartAt 𝓘(ℝ, E) p).source →
      TendstoUniformlyOn
        (fun n x => fderiv ℝ (fun z => extChartAt 𝓘(ℝ, E) p (v n z)) x)
        (fun x => fderiv ℝ
          (fun z => extChartAt 𝓘(ℝ, E) p (diskExtension (affineSubdisk q 0 r) z)) x)
        atTop K) :
    ∀ x ∈ Metric.ball (0 : ℂ) 1, ∀ y ∈ Metric.ball (0 : ℂ) 1,
      x ≠ y → diskExtension q x = diskExtension q y →
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension q) x) →
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension q) y) →
      ¬ Function.Surjective
        ((show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension q) x).coprod
          (-(show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension q) y))) :=
  noTransverse_of_trimmed_R15T hcol hr hρr fun _ hu _ hv' huv heq _ _ =>
    DifferentialGeometry.Topology.Manifold.not_surjective_coprod_mfderiv_of_injective_c1_limit
      Metric.isOpen_ball hv
      (contMDiffOn_diskExtension_affineSubdisk_zero_R15T hQ hr.le hr1) hinj hval hchart hder
      hu hv' huv heq

end C1Limit

end DifferentialGeometry.Geometry
