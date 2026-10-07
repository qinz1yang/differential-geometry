import DifferentialGeometry.Geometry.MinimalSurface.Plateau.VaryingMetricCompactnessR7CBoundaryCap
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.Rotation

/-!
# R7C L5（二）：局部 quasi-minimality 在盘旋转下不变

边界 cap 引理（`boundary_lens_hole_filling_qm_R7C`）固定在边界点 `−1`；一般边界点 `c = ζ·(−1)` 用旋转
`rotatedDiskMap u ζ`（`ζ = exp(2πi d)`）搬过去。本文件证明：若 `u` 对**一切**中心 `c`、半径 `s` 局部
`Λ`-quasi-minimal（competitor 在 `B̄_s(c)` 外与 `u` 相同、trace 类为 `γ`、Lipschitz），则旋转后的盘同样如此。
competitor 反向旋转（`ζ⁻¹`）后是 `u` 的 competitor；能量经树内
`integral_diskMapEnergyDensity_rotatedDiskMap_preimage`
换元；trace 类经 `IsWeaklyMonotoneOnce.comp` 与圆周平移。
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Metric Manifold
open DifferentialGeometry.Topology
open scoped Topology ContDiff Manifold ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace N] [ChartedSpace E N] [IsManifold 𝓘(ℝ, E) ∞ N]

/-- 圆周平移 `t ↦ t + d` 作为 `C(loopCircle, loopCircle)`（R7C 辅助）。 -/
def loopShift_R7C (d : ℝ) : C(loopCircle, loopCircle) :=
  ⟨fun t => t + (d : loopCircle), continuous_id.add continuous_const⟩

theorem isWeaklyMonotoneOnce_loopShift_R7C (d : ℝ) :
    IsWeaklyMonotoneOnce (loopShift_R7C d) := by
  refine ⟨fun t => t + d, continuous_id.add continuous_const, fun t => ?_,
    Or.inl ⟨fun a b hab => by linarith, fun t => by ring⟩⟩
  change ((t + d : ℝ) : loopCircle) = (t : loopCircle) + (d : loopCircle)
  rfl

theorem rotation_exp_neg_cancel_R7C (d : ℝ) (z : ℂ) :
    rotation (Circle.exp (2 * Real.pi * -d)) (rotation (Circle.exp (2 * Real.pi * d)) z) = z := by
  rw [rotation_apply, rotation_apply, ← mul_assoc, Circle.coe_exp, Circle.coe_exp,
    ← Complex.exp_add]
  have h : (↑(2 * Real.pi * -d) * Complex.I + ↑(2 * Real.pi * d) * Complex.I : ℂ) = 0 := by
    push_cast
    ring
  rw [h, Complex.exp_zero, one_mul]

theorem rotation_exp_cancel_neg_R7C (d : ℝ) (z : ℂ) :
    rotation (Circle.exp (2 * Real.pi * d)) (rotation (Circle.exp (2 * Real.pi * -d)) z) = z := by
  have h := rotation_exp_neg_cancel_R7C (-d) z
  rwa [neg_neg] at h

/-- 旋转回去（R7C 辅助）：`rotatedDiskMap (rotatedDiskMap w ζ⁻¹) ζ = w`。 -/
theorem rotatedDiskMap_rotatedDiskMap_neg_R7C (w : C(closedDisk, N)) (d : ℝ) :
    rotatedDiskMap (rotatedDiskMap w (Circle.exp (2 * Real.pi * -d)))
      (Circle.exp (2 * Real.pi * d)) = w := by
  ext z
  rw [rotatedDiskMap_apply, rotatedDiskMap_apply]
  congr 1
  apply Subtype.ext
  exact rotation_exp_neg_cancel_R7C d z

/-- **旋转不变的局部 quasi-minimality**（R7C）：见文件头。 -/
theorem rotated_local_quasi_min_R7C (g : SmoothRiemannianMetric 𝓘(ℝ, E) N) (γ : freeLoop N)
    (u : C(closedDisk, N)) {Λ : ℝ}
    (hqm : ∀ (c : ℂ) (s : ℝ) (w : C(closedDisk, N)) (Lw : ℝ≥0),
      (∀ z z', riemannianEDistOf g (w z) (w z') ≤ (Lw : ℝ≥0∞) * edist z z') →
      DiskWeakJordanTrace γ w → (∀ z : closedDisk, s ≤ dist (z : ℂ) c → w z = u z) →
      (∫ z in closedBall (0 : ℂ) 1 ∩ closedBall c s,
        diskMapEnergyDensity g (diskExtension u) z) ≤
        Λ * ∫ z in closedBall (0 : ℂ) 1 ∩ closedBall c s,
          diskMapEnergyDensity g (diskExtension w) z) (d : ℝ) :
    ∀ (c : ℂ) (s : ℝ) (w : C(closedDisk, N)) (Lw : ℝ≥0),
      (∀ z z', riemannianEDistOf g (w z) (w z') ≤ (Lw : ℝ≥0∞) * edist z z') →
      DiskWeakJordanTrace γ w →
      (∀ z : closedDisk, s ≤ dist (z : ℂ) c →
        w z = rotatedDiskMap u (Circle.exp (2 * Real.pi * d)) z) →
      (∫ z in closedBall (0 : ℂ) 1 ∩ closedBall c s,
        diskMapEnergyDensity g (diskExtension (rotatedDiskMap u (Circle.exp (2 * Real.pi * d))))
          z) ≤
        Λ * ∫ z in closedBall (0 : ℂ) 1 ∩ closedBall c s,
          diskMapEnergyDensity g (diskExtension w) z := by
  intro c s w Lw hwL hwΓ hwout
  set ζ := Circle.exp (2 * Real.pi * d) with hζ
  set ζ' := Circle.exp (2 * Real.pi * -d) with hζ'
  set w' := rotatedDiskMap w ζ' with hw'
  have hw'L := riemannian_lipschitz_rotatedDiskMap g hwL ζ'
  have hw'Γ : DiskWeakJordanTrace γ w' := by
    obtain ⟨σ, hσ, htr⟩ := hwΓ
    refine ⟨σ.comp (loopShift_R7C (-d)), hσ.comp (isWeaklyMonotoneOnce_loopShift_R7C (-d)), ?_⟩
    ext θ
    obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective θ
    change w' (diskBoundary (t : loopCircle)) = γ (σ ((t : loopCircle) + ((-d : ℝ) : loopCircle)))
    rw [hw', rotatedDiskMap_diskBoundary]
    have h := congrArg (fun f : freeLoop N => f ((-d + t : ℝ) : loopCircle)) htr
    change w (diskBoundary ((-d + t : ℝ) : loopCircle)) = γ (σ ((-d + t : ℝ) : loopCircle)) at h
    rw [h]
    congr 2
    rw [add_comm (-d) t]
    rfl
  have hw'out : ∀ z : closedDisk, s ≤ dist (z : ℂ) (rotation ζ c) → w' z = u z := by
    intro z hz
    rw [hw', rotatedDiskMap_apply]
    have hd : s ≤ dist (rotation ζ' (z : ℂ)) c := by
      have hiso := (rotation ζ').isometry.dist_eq (z : ℂ) (rotation ζ c)
      rw [hζ', hζ, rotation_exp_neg_cancel_R7C] at hiso
      rw [hζ']
      linarith
    rw [hwout _ hd, rotatedDiskMap_apply]
    congr 1
    apply Subtype.ext
    exact rotation_exp_cancel_neg_R7C d z
  have hmain := hqm (rotation ζ c) s w' Lw hw'L hw'Γ hw'out
  have hpre : rotation ζ ⁻¹' (closedBall (0 : ℂ) 1 ∩ closedBall (rotation ζ c) s) =
      closedBall (0 : ℂ) 1 ∩ closedBall c s := by
    ext z
    simp only [mem_preimage, mem_inter_iff, mem_closedBall, dist_zero_right,
      LinearIsometryEquiv.norm_map, (rotation ζ).isometry.dist_eq]
  have hsub : closedBall (0 : ℂ) 1 ∩ closedBall (rotation ζ c) s ⊆ closedBall (0 : ℂ) 1 :=
    inter_subset_left
  have hu := integral_diskMapEnergyDensity_rotatedDiskMap_preimage g u ζ hsub
  have hw := integral_diskMapEnergyDensity_rotatedDiskMap_preimage g w' ζ hsub
  rw [hpre] at hu hw
  rw [hw', rotatedDiskMap_rotatedDiskMap_neg_R7C] at hw
  rw [hu, hw]
  exact hmain

end DifferentialGeometry.Geometry
