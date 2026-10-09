import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Regularity.BoundarySmoothness
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.SmoothTraceLift
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.AngleTrace
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.DiskBoundaryMetric
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.DiskMetricCoefficient
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.MorreyDiskExtension

/-!
# S-MY-ADAPT G5（rev2 A-8 = R5-F1b）：Morrey 盘的 regular boundary arc + F1a 搬入

外审 R5-F1（D-R-MY2-7）选 (a)：边界正则 producer 直接用树里定理（F1a），F1b 只在 F1a 的闭盘延拓上
选一段 regular boundary arc。合同来源 scratch `contracts/MYD3/R03R05.lean:132/145`。

* `morrey_disk_closed_extension_lipschitz_ADP`（F1a，scratch `…_MYD3` 逐字，原 [PF]）：任意 Morrey 盘
  （trace 是 smooth embedded loop 的 weak Jordan 重参数化）有**全闭盘** `SmoothDiskExtension` 与
  **全局** metric-Lipschitz；证明 = `exists_smooth_extension_of_conformal_harmonic_disk`
  （`Regularity/BoundarySmoothness.lean:20`）+ `SmoothDiskExtension.lipschitz`。
* `morrey_disk_regular_boundary_arc_ADP`（F1b，scratch `morrey_disk_regular_boundary_arc_MYD3`）：
  给定任一 `SmoothDiskExtension u U`，存在 `z₀ ∈ S¹`、`δ > 0`，`U` 在 `ball z₀ δ ∩ D̄` 上 `mfderiv` 单射。
  **不用 `q` 的 rank、不假设任何边界 rank**（不走 `exists_regular_signed_trace_lift`，它要整圈 rank 前提）：
  `contDiff_weakTraceLift` 给光滑 lift `ψ`；`ψ (t+1) = ψ t ± 1` ⇒ 某点 `ψ' ≠ 0`；
  `U ∘ circleMap = γ ∘ φ` ⇒ `diskMapPartial U z₀ (i z₀) = γ' · φ' ≠ 0`（`γ` immersed）；共形关系在
  `closedBall` 上成立 ⇒ 系数 `≠ 0`、`mfderiv` 在该点单射；系数连续（`contDiffOn_diskMapConformalCoefficient`）
  ⇒ 开条件给一段弧。
* `morrey_disk_closed_extension_regular_arc_ADP`：F1 打包（consumer）：同一个 `U` 同时给全局 Lipschitz 与
  regular arc——正是 splice `actual_morrey_oriented_forward_phase_splice` 要的 `haOrigLip` / 全闭盘
  `SmoothDiskExtension` 加上 F1b 的局部 rank。

branch points（R5-B）**不在此**：本文件不声称 `U` 在内部 immersion。
-/

set_option autoImplicit false
noncomputable section

open Manifold Set Metric Filter
open DifferentialGeometry.Topology
open scoped Manifold ContDiff NNReal ENNReal Topology

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- **F1a**（scratch `morrey_disk_closed_extension_lipschitz_MYD3` 逐字，树里两条定理）：Morrey 盘有全闭盘
smooth extension 与全局 metric-Lipschitz。不要求闭盘 rank。 -/
theorem morrey_disk_closed_extension_lipschitz_ADP
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {Γ : freeLoop M}
    (hΓ : IsSmoothEmbeddedLoop (E := E) Γ) {u : C(closedDisk, M)} (hu : IsMorreyDisk g Γ u) :
    ∃ U : ℂ → M, SmoothDiskExtension (E := E) u U ∧ ∃ L : ℝ≥0, ∀ z w : closedDisk,
      riemannianEDistOf g (u z) (u w) ≤ (L : ℝ≥0∞) * edist z w := by
  obtain ⟨σ, -, htr⟩ := hu.trace
  obtain ⟨U, hU⟩ := exists_smooth_extension_of_conformal_harmonic_disk g hΓ u hu.smoothInterior
    hu.conformal hu.harmonic σ htr
  exact ⟨U, hU, hU.lipschitz g⟩

omit [FiniteDimensional ℝ E] in
/-- 共形点上 `mfderiv ≠ 0`（⇔ 共形系数 `≠ 0`）⇒ `mfderiv` 单射（满秩 2）。 -/
theorem injective_mfderiv_of_conformal_coefficient_ne_zero_ADP
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {U : ℂ → M} {z : ℂ}
    (hc : DiskMapConformalAt g U z) (hne : diskMapConformalCoefficient g U z ≠ 0) :
    Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z) := by
  let L : ℂ →L[ℝ] E := mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z
  change Function.Injective L
  intro v w hvw
  have hzero : diskMapPartial (E := E) U z (v - w) = 0 := by
    change L (v - w) = 0
    exact (map_sub L v w).trans (sub_eq_zero.mpr hvw)
  have hinner := hc.inner_partials (v - w) (v - w)
  rw [hzero] at hinner
  have hmul : diskMapConformalCoefficient g U z * inner ℝ (v - w) (v - w) = 0 := by
    simpa using hinner.symm
  exact sub_eq_zero.mp (inner_self_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left hne))

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- 边界相位：`U ∘ circleMap 0 1 = Γ ∘ φ`、`φ' θ ≠ 0`、`Γ` immersed ⇒ `mfderiv U` 在
`circleMap 0 1 θ` 处非零（切向导数 `Γ' · φ' ≠ 0`）。 -/
theorem mfderiv_ne_zero_of_boundary_phase_ADP {Γ : freeLoop M}
    (hΓ : IsSmoothEmbeddedLoop (E := E) Γ) {U : ℂ → M} {φ : ℝ → ℝ} {θ : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hUd : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U (circleMap 0 1 θ))
    (hangle : U ∘ circleMap 0 1 = (fun t : ℝ => Γ (t : loopCircle)) ∘ φ)
    (hφ' : deriv φ θ ≠ 0) :
    mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U (circleMap 0 1 θ) ≠ 0 := by
  intro hzero
  have hchain := mfderiv_comp (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, ℝ))
    (I'' := 𝓘(ℝ, E)) θ (hΓ.smooth.mdifferentiable (by simp) (φ θ))
      (hφ.contMDiff.mdifferentiable (by simp) θ)
  have hvalue := congrArg (fun D : ℝ →L[ℝ] E => D 1) hchain
  change mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E)
      ((fun s : ℝ => Γ (s : loopCircle)) ∘ φ) θ (1 : ℝ) =
    mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun s : ℝ => Γ (s : loopCircle)) (φ θ)
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) φ θ (1 : ℝ)) at hvalue
  have hφm : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) φ θ (1 : ℝ) = deriv φ θ := by
    rw [mfderiv_eq_fderiv]
    exact fderiv_apply_one_eq_deriv
  rw [← hangle, mfderiv_diskMapBoundary hUd, hφm] at hvalue
  have hlin : ∀ (L : ℝ →L[ℝ] E) (c : ℝ), L c = c • L 1 := fun L c => by
    simpa using L.map_smul c 1
  have hfin : diskMapPartial (E := E) U (circleMap 0 1 θ) (Complex.I * circleMap 0 1 θ) =
      deriv φ θ • mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun s : ℝ => Γ (s : loopCircle)) (φ θ) 1 :=
    hvalue.trans (hlin (show ℝ →L[ℝ] E from
      mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun s : ℝ => Γ (s : loopCircle)) (φ θ)) (deriv φ θ))
  have hzp : diskMapPartial (E := E) U (circleMap 0 1 θ) (Complex.I * circleMap 0 1 θ) = 0 := by
    change mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U (circleMap 0 1 θ) _ = 0
    rw [hzero]
    rfl
  rw [hzp] at hfin
  exact smul_ne_zero hφ' (hΓ.immersed (φ θ)) hfin.symm

/-- **F1b**（scratch `morrey_disk_regular_boundary_arc_MYD3`）：Morrey 盘的任一闭盘 smooth extension `U`
在某段 regular boundary arc 上满秩。不用 `q` 的 rank、不假设边界 rank。 -/
theorem morrey_disk_regular_boundary_arc_ADP
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {Γ : freeLoop M}
    (hΓ : IsSmoothEmbeddedLoop (E := E) Γ) {u : C(closedDisk, M)} (hu : IsMorreyDisk g Γ u)
    {U : ℂ → M} (hU : SmoothDiskExtension (E := E) u U) :
    ∃ (z₀ : ℂ) (δ : ℝ), ‖z₀‖ = 1 ∧ 0 < δ ∧
      ∀ z ∈ Metric.ball z₀ δ ∩ Metric.closedBall 0 1,
        Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z) := by
  obtain ⟨σ, ⟨ψ, hψc, hlift, hsign⟩, htrace⟩ := hu.trace
  have hψ : ContDiff ℝ ∞ ψ := hΓ.contDiff_weakTraceLift hU.smoothUpToBoundary htrace hψc hlift
  -- degree ±1 ⇒ 某点 `ψ' ≠ 0`
  obtain ⟨t, ht⟩ : ∃ t : ℝ, deriv ψ t ≠ 0 := by
    by_contra hall'
    have hall : ∀ t, deriv ψ t = 0 := fun t => by
      by_contra h
      exact hall' ⟨t, h⟩
    have hconst : ψ 1 = ψ 0 :=
      is_const_of_deriv_eq_zero (hψ.differentiable (by simp)) hall 1 0
    rcases hsign with ⟨-, hp⟩ | ⟨-, hp⟩
    · have := hp 0
      rw [zero_add] at this
      linarith
    · have := hp 0
      rw [zero_add] at this
      linarith
  let φ : ℝ → ℝ := fun θ => ψ (θ / (2 * Real.pi))
  have hφ : ContDiff ℝ ∞ φ := hψ.comp (contDiff_id.div_const _)
  have hangle := hU.angle_trace htrace (fun θ => hlift (θ / (2 * Real.pi)))
  let θ : ℝ := 2 * Real.pi * t
  have hquot : θ / (2 * Real.pi) = t := by
    dsimp only [θ]
    field_simp
  have hφ' : deriv φ θ ≠ 0 := by
    have hψd : HasDerivAt ψ (deriv ψ t) ((fun s : ℝ => s / (2 * Real.pi)) θ) := by
      change HasDerivAt ψ (deriv ψ t) (θ / (2 * Real.pi))
      rw [hquot]
      exact (hψ.differentiable (by simp) t).hasDerivAt
    have h1 : HasDerivAt (fun s : ℝ => s / (2 * Real.pi)) (1 / (2 * Real.pi)) θ :=
      (hasDerivAt_id θ).div_const _
    have h2 := hψd.scomp θ h1
    have h3 : HasDerivAt φ ((1 / (2 * Real.pi)) • deriv ψ t) θ := h2
    rw [h3.deriv, smul_eq_mul]
    exact mul_ne_zero (by positivity) ht
  have hz : circleMap 0 1 θ ∈ sphere (0 : ℂ) 1 := by
    simp only [mem_sphere_zero_iff_norm, norm_circleMap_zero, abs_one]
  obtain ⟨N, hN, hDN, hUs⟩ := hU.2
  have hUd : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U (circleMap 0 1 θ) :=
    (hUs.contMDiffAt (hN.mem_nhds (hDN (sphere_subset_closedBall hz)))).mdifferentiableAt
      (by simp)
  have hne := mfderiv_ne_zero_of_boundary_phase_ADP hΓ hφ hUd hangle hφ'
  have hconf := hu.conformal_of_extension_closedBall hU
  have hcoef : diskMapConformalCoefficient g U (circleMap 0 1 θ) ≠ 0 := fun h =>
    hne ((hconf _ (sphere_subset_closedBall hz)).coefficient_eq_zero_iff.mp h)
  have hcont : ContinuousAt (diskMapConformalCoefficient g U) (circleMap 0 1 θ) :=
    (contDiffOn_diskMapConformalCoefficient g hN hUs).continuousOn.continuousAt
      (hN.mem_nhds (hDN (sphere_subset_closedBall hz)))
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp (hcont.eventually_ne hcoef)
  refine ⟨circleMap 0 1 θ, δ, mem_sphere_zero_iff_norm.mp hz, hδ, fun z hzz => ?_⟩
  exact injective_mfderiv_of_conformal_coefficient_ne_zero_ADP (hconf z hzz.2)
    (hball (mem_ball.mp hzz.1))

/-- **consumer（R5-F1 打包）**：F1a 的全闭盘 `U` 同时有全局 metric-Lipschitz 与 F1b 的 regular boundary
arc。这是 splice `actual_morrey_oriented_forward_phase_splice` 的 `haOrigLip` / 全闭盘
`SmoothDiskExtension` 加上「某段边界弧上满秩」。 -/
theorem morrey_disk_closed_extension_regular_arc_ADP
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {Γ : freeLoop M}
    (hΓ : IsSmoothEmbeddedLoop (E := E) Γ) {u : C(closedDisk, M)} (hu : IsMorreyDisk g Γ u) :
    ∃ U : ℂ → M, SmoothDiskExtension (E := E) u U ∧
      (∃ L : ℝ≥0, ∀ z w : closedDisk,
        riemannianEDistOf g (u z) (u w) ≤ (L : ℝ≥0∞) * edist z w) ∧
      ∃ (z₀ : ℂ) (δ : ℝ), ‖z₀‖ = 1 ∧ 0 < δ ∧
        ∀ z ∈ Metric.ball z₀ δ ∩ Metric.closedBall 0 1,
          Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z) := by
  obtain ⟨U, hU, hL⟩ := morrey_disk_closed_extension_lipschitz_ADP g hΓ hu
  exact ⟨U, hU, hL, morrey_disk_regular_boundary_arc_ADP hΓ hu hU⟩

end DifferentialGeometry.Geometry
