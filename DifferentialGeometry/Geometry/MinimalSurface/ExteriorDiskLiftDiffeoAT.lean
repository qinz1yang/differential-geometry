import DifferentialGeometry.Geometry.MinimalSurface.ExteriorDiskReparametrization

/-!
# S-A08-ATTAIN G1 (零件 1)：由 smooth 单调 lift 造 closed-disk 的 diffeomorphism

`Circle.exists_diffeomorph_extension` 需要先有 circle 的 `Diffeomorph`（要 inverse 的光滑性）。
这里直接从 `ψ : ℝ → ℝ` 的 lift 数据（`ContDiff`、`ψ' ≠ 0`、单调且 `ψ (t+1) = ψ t ± 1`）
造 `Φ : ℂ ≃ₘ[ℝ] ℂ`，使 `Φ (exp (2π i t)) = exp (2π i ψ t)` 且 `Φ` 保持 closed ball。
不需要 inverse function theorem：之后用 `Φ.symm` 即得 `σ⁻¹` 在边界上的延拓。
-/

set_option autoImplicit false
noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.MinimalSurface

/-- 连续且 `g (x+1) = g x + 1` 的 `g : ℝ → ℝ` 是满射（IVT）。 -/
theorem surjective_of_periodic_lift_AT {g : ℝ → ℝ} (hc : Continuous g)
    (hp : ∀ x, g (x + 1) = g x + 1) : Function.Surjective g := by
  have hper : Function.Periodic (fun x => g x - x) 1 := fun x => by
    simp only [hp]
    ring
  have hn : ∀ n : ℤ, g n = g 0 + n := fun n => by
    have h := hper.int_mul n 0
    simp only [zero_add, mul_one, sub_zero] at h
    linarith
  intro y
  have h1 : ∃ a, g a ≤ y := by
    obtain ⟨n, hn'⟩ := exists_int_gt (g 0 - y)
    exact ⟨-(n : ℝ), by
      have := hn (-n)
      push_cast at this
      linarith⟩
  have h2 : ∃ b, y ≤ g b := by
    obtain ⟨n, hn'⟩ := exists_int_gt (y - g 0)
    exact ⟨(n : ℝ), by
      have := hn n
      linarith⟩
  exact mem_range_of_exists_le_of_exists_ge hc h1 h2

/-- `diskBoundary θ` 的模长为 1。 -/
theorem norm_diskBoundary_AT (θ : loopCircle) : ‖(diskBoundary θ : ℂ)‖ = 1 :=
  Circle.norm_coe (AddCircle.toCircle θ)

/-- 单位圆上的每个点都是某个 `diskBoundary (s : loopCircle)`。 -/
theorem exists_diskBoundary_eq_of_norm_eq_one_AT {z : ℂ} (hz : ‖z‖ = 1) :
    ∃ s : ℝ, (diskBoundary (s : loopCircle) : ℂ) = z := by
  let c : Circle := ⟨z, mem_sphere_zero_iff_norm.mpr hz⟩
  obtain ⟨θ, hθ⟩ := (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).surjective c
  obtain ⟨s, rfl⟩ := QuotientAddGroup.mk_surjective θ
  refine ⟨s, ?_⟩
  have hc := congrArg (fun x : Circle => (x : ℂ)) hθ
  simpa only [AddCircle.homeomorphCircle_apply] using! hc

open DifferentialGeometry.Topology.PeriodicCurve
  (exists_compactly_supported_ambient_isotopy_of_increasing_lift) in
/-- 增的 smooth lift `g`（`g (x+1) = g x + 1`，`g' > 0`）诱导 `ℂ` 的 diffeomorphism `D`：
`D (exp (2π i x)) = exp (2π i g x)`，`D` 保持 closed ball。
证明沿用 `Circle.exists_diffeomorph_extension`，但从 lift 出发而不经 circle diffeomorphism。 -/
theorem exists_disk_diffeomorph_of_increasing_lift_AT {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    (hp : ∀ x, g (x + 1) = g x + 1) (hder : ∀ x, 0 < deriv g x) :
    ∃ D : ℂ ≃ₘ[ℝ] ℂ,
      (∀ t : ℝ, D (diskBoundary (t : loopCircle) : ℂ) = (diskBoundary (g t : loopCircle) : ℂ)) ∧
      D '' Metric.closedBall (0 : ℂ) 1 = Metric.closedBall 0 1 := by
  let _ : Fact (Module.finrank ℝ ℂ = 1 + 1) := ⟨by simp⟩
  let A := AddCircle.diffeomorphCircle
  let f : AddCircle (1 : ℝ) → ℂ := fun θ => A θ
  have hA : Manifold.IsSmoothEmbedding 𝓘(ℝ, ℝ) (𝓡 1) ∞ A :=
    DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_of_isLocalDiffeomorph_of_injective
      A.isLocalDiffeomorph A.injective
  have hf : Manifold.IsSmoothEmbedding 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ f :=
    (isSmoothEmbedding_coe_sphere (E := ℂ) (n := 1)).comp_of_boundarylessManifold hA (by simp)
  obtain ⟨Φ, _, _, _, htrack, K, _, hK, hfix⟩ :=
    exists_compactly_supported_ambient_isotopy_of_increasing_lift
      hf hg hp hder isOpen_compl_singleton
      (show range f ⊆ ({0} : Set ℂ)ᶜ from by
        rintro _ ⟨θ, rfl⟩
        exact ne_zero_of_mem_unit_sphere (A θ))
  have hΦzero : Φ 1 0 = 0 := (hfix 1).1 (by
    intro hz
    exact hK hz rfl)
  have htrack1 (x : ℝ) : Φ 1 (f (x : AddCircle (1 : ℝ))) = f (g x : AddCircle (1 : ℝ)) := by
    simpa only [sub_self, zero_mul, one_mul, zero_add] using htrack 1 ⟨zero_le_one, le_rfl⟩ x
  have hA' (x : loopCircle) : (A x : ℂ) = (diskBoundary x : ℂ) := by
    congr 1
    exact AddCircle.homeomorphCircle_apply one_ne_zero x
  have hbd (t : ℝ) : Φ 1 (diskBoundary (t : loopCircle) : ℂ) =
      (diskBoundary (g t : loopCircle) : ℂ) := by
    rw [← hA', ← hA']
    exact htrack1 t
  refine ⟨Φ 1, hbd, ?_⟩
  have hsurj := surjective_of_periodic_lift_AT hg.continuous hp
  apply (Φ 1).toHomeomorph.image_closedBall_of_image_sphere_eq_of_map_center
    zero_lt_one zero_lt_one ?_ hΦzero
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨s, rfl⟩ := exists_diskBoundary_eq_of_norm_eq_one_AT (mem_sphere_zero_iff_norm.mp hx)
    change (Φ 1) _ ∈ Metric.sphere (0 : ℂ) 1
    rw [hbd s, mem_sphere_zero_iff_norm]
    exact norm_diskBoundary_AT _
  · intro hz
    obtain ⟨y, rfl⟩ := exists_diskBoundary_eq_of_norm_eq_one_AT (mem_sphere_zero_iff_norm.mp hz)
    obtain ⟨s, rfl⟩ := hsurj y
    exact ⟨_, mem_sphere_zero_iff_norm.mpr (norm_diskBoundary_AT _), hbd s⟩

/-- 复共轭把 `diskBoundary s` 变成 `diskBoundary (-s)`。 -/
theorem conj_diskBoundary_AT (s : ℝ) :
    starRingEnd ℂ (diskBoundary (s : loopCircle) : ℂ) =
      (diskBoundary ((-s : ℝ) : loopCircle) : ℂ) := by
  rw [diskBoundary_coe, diskBoundary_coe, ← Complex.exp_conj]
  congr 1
  rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-- 单调（增或减）的 smooth lift `ψ`，`ψ' ≠ 0`，诱导 `ℂ` 的 diffeomorphism `Φ`：
`Φ (exp (2π i t)) = exp (2π i ψ t)` 且 `Φ` 保持 closed ball。减的情形用复共轭。 -/
theorem exists_disk_diffeomorph_of_lift_AT {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hder : ∀ t, deriv ψ t ≠ 0)
    (hsign : (Monotone ψ ∧ ∀ t, ψ (t + 1) = ψ t + 1) ∨
      (Antitone ψ ∧ ∀ t, ψ (t + 1) = ψ t - 1)) :
    ∃ Φ : ℂ ≃ₘ[ℝ] ℂ,
      (∀ t : ℝ, Φ (diskBoundary (t : loopCircle) : ℂ) = (diskBoundary (ψ t : loopCircle) : ℂ)) ∧
      Φ '' Metric.closedBall (0 : ℂ) 1 = Metric.closedBall 0 1 := by
  rcases hsign with ⟨hm, hp⟩ | ⟨hm, hp⟩
  · exact exists_disk_diffeomorph_of_increasing_lift_AT hψ hp
      (fun t => lt_of_le_of_ne hm.deriv_nonneg (Ne.symm (hder t)))
  · have hm' : Monotone fun t => -ψ t := hm.neg
    obtain ⟨D, hD, hDB⟩ := exists_disk_diffeomorph_of_increasing_lift_AT (g := fun t => -ψ t)
      hψ.neg (fun t => by simp only [hp]; ring)
      (fun t => by
        have h1 : deriv (fun t => -ψ t) t = -deriv ψ t := deriv.fun_neg
        rw [h1]
        have h2 : 0 ≤ deriv (fun t => -ψ t) t := hm'.deriv_nonneg
        rw [h1] at h2
        exact lt_of_le_of_ne (by linarith) (by have := hder t; intro h; apply this; linarith))
    refine ⟨D.trans Complex.conjCLE.toDiffeomorph, fun t => ?_, ?_⟩
    · change starRingEnd ℂ (D (diskBoundary (t : loopCircle) : ℂ)) = _
      rw [hD, conj_diskBoundary_AT, neg_neg]
    · rw [Diffeomorph.coe_trans, Set.image_comp, hDB]
      ext z
      constructor
      · rintro ⟨x, hx, rfl⟩
        simpa using hx
      · intro hz
        exact ⟨starRingEnd ℂ z, by simpa using hz, by simp⟩

end DifferentialGeometry.Geometry.MinimalSurface
