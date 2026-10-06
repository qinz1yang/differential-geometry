import DifferentialGeometry.Geometry.MinimalSurface.Plateau.SmoothExtension
import DifferentialGeometry.Geometry.Measure.Area.Manifold
import DifferentialGeometry.Geometry.Measure.Area.Riemannian

/-!
# Smooth 映射下的 disk area comparison（IMS08 kernel，G2，S-A14-KERNEL）

`u` 带 `SmoothDiskExtension U`，`φ` 在 open `V ⊇ range u` 上 smooth，且在 `u` 的 range 附近
有逐点 metric 不等式 `g₂(dφ w, dφ w) ≤ c * g₁(w, w)`，则
`riemannianDiskArea g₂ (φ ∘ u) ≤ c * riemannianDiskArea g₁ u`。

不使用全局 Lipschitz（`riemannianDiskArea_comp_le` 要的是 `M₁` 上全局的 edist 比较）：
逐点 `mfderiv_comp` + `tangentTwoJacobian_le_of_combinations`，再对 `closedBall 0 1` 积分。
注意方向：`φ^*g₂ ≤ c * g₁` ⇒ `area g₂ (φ ∘ u) ≤ c * area g₁ u`（`c = exp ε` 对应
`hcomparison` 里的 `Real.exp ε` 因子；metric 比值 `e^{2ε'}` 取 `c = exp (2 * ε')`）。
-/

set_option autoImplicit false
noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology Set MeasureTheory Bundle
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M₁ M₂ : Type*}
  [TopologicalSpace M₁] [ChartedSpace E M₁] [IsManifold 𝓘(ℝ, E) ∞ M₁]
  [TopologicalSpace M₂] [ChartedSpace E M₂] [IsManifold 𝓘(ℝ, E) ∞ M₂]

/-- 逐点 density comparison：在 `U z` 处 `g₂(dφ w, dφ w) ≤ c * g₁(w, w)` ⇒
`riemannianAreaDensity g₂ (φ ∘ U) z ≤ c * riemannianAreaDensity g₁ U z`。 -/
theorem riemannianAreaDensity_map_le_K8
    (g₁ : SmoothRiemannianMetric 𝓘(ℝ, E) M₁) (g₂ : SmoothRiemannianMetric 𝓘(ℝ, E) M₂)
    {U : ℂ → M₁} {φ : M₁ → M₂} {z : ℂ}
    (hU : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z)
    (hφ : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) φ (U z)) {c : ℝ} (hc : 0 < c)
    (hmetric : ∀ w : TangentSpace 𝓘(ℝ, E) (U z),
      g₂.inner (φ (U z)) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ (U z) w)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ (U z) w) ≤ c * g₁.inner (U z) w w) :
    riemannianAreaDensity g₂ (φ ∘ U) z ≤ c * riemannianAreaDensity g₁ U z := by
  unfold riemannianAreaDensity
  rw [mfderiv_comp z hφ hU]
  have h := tangentTwoJacobian_le_of_combinations g₁ g₂
    (v := mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z (1 : ℂ)) (w := mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z Complex.I)
    (v' := (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ (U z)) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z (1 : ℂ)))
    (w' := (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ (U z)) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z Complex.I))
    (L := Real.sqrt c) (Real.sqrt_nonneg c) (fun a b => by
      rw [← Real.sqrt_mul hc.le]
      apply Real.sqrt_le_sqrt
      have h1 := hmetric (a • mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z (1 : ℂ) +
        b • mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z Complex.I)
      simpa only [map_add, map_smul] using h1)
  rw [Real.sq_sqrt hc.le] at h
  exact h

/-- G2 主定理：`u` 带 `SmoothDiskExtension U`，`φ` 在 open `V ⊇ range u` 上 smooth，
`range u ⊆ S` 上逐点 `φ^*g₂ ≤ c * g₁` ⇒ `area g₂ v ≤ c * area g₁ u`（`v = φ ∘ u`）。 -/
theorem riemannianDiskArea_map_le_K8
    (g₁ : SmoothRiemannianMetric 𝓘(ℝ, E) M₁) (g₂ : SmoothRiemannianMetric 𝓘(ℝ, E) M₂)
    {u : C(closedDisk, M₁)} {U : ℂ → M₁} (hU : SmoothDiskExtension (E := E) u U)
    {φ : M₁ → M₂} {V : Set M₁} (hV : IsOpen V) (hrange : range u ⊆ V)
    (hφ : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ φ V)
    {S : Set M₁} (hS : range u ⊆ S) {c : ℝ} (hc : 0 < c)
    (hmetric : ∀ p ∈ S, ∀ w : TangentSpace 𝓘(ℝ, E) p,
      g₂.inner (φ p) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ p w) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ p w) ≤
        c * g₁.inner p w w)
    (v : C(closedDisk, M₂)) (hv : ∀ z, v z = φ (u z)) :
    riemannianDiskArea g₂ v ≤ c * riemannianDiskArea g₁ u := by
  obtain ⟨heq, N, hN, hDN, hUN⟩ := hU
  have hv' : ∀ z : closedDisk, (φ ∘ U) z = v z := fun z => by
    rw [hv z, Function.comp_apply, heq z]
  have hUz : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, U z ∈ range u := fun z hz => by
    rw [heq ⟨z, hz⟩]
    exact ⟨⟨z, hz⟩, rfl⟩
  have hN' : IsOpen (N ∩ U ⁻¹' V) := hUN.continuousOn.isOpen_inter_preimage hN hV
  have hDN' : Metric.closedBall (0 : ℂ) 1 ⊆ N ∩ U ⁻¹' V := fun z hz =>
    ⟨hDN hz, hrange (hUz z hz)⟩
  have hφU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (φ ∘ U) (N ∩ U ⁻¹' V) :=
    hφ.comp (hUN.mono inter_subset_left) (fun z hz => hz.2)
  rw [riemannianDiskArea_eq_of_extension g₂ v (φ ∘ U) hv',
    riemannianDiskArea_eq_of_extension g₁ u U heq]
  unfold riemannianArea
  rw [← integral_const_mul]
  refine setIntegral_mono_on
    (integrableOn_riemannianAreaDensity_of_contMDiffOn g₂ hN' (hφU.of_le (by simp))
      (isCompact_closedBall (0 : ℂ) 1) hDN')
    ((integrableOn_riemannianAreaDensity_of_contMDiffOn g₁ hN (hUN.of_le (by simp))
      (isCompact_closedBall (0 : ℂ) 1) hDN).const_mul c)
    measurableSet_closedBall (fun z hz => ?_)
  have hUd : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z :=
    (hUN.mdifferentiableOn (by simp)).mdifferentiableAt (hN.mem_nhds (hDN hz))
  have hφd : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) φ (U z) :=
    (hφ.mdifferentiableOn (by simp)).mdifferentiableAt (hV.mem_nhds (hrange (hUz z hz)))
  exact riemannianAreaDensity_map_le_K8 g₁ g₂ hUd hφd hc (hmetric _ (hS (hUz z hz)))

/-- 因子取 `Real.exp (2 * ε)` 的形式（metric 比值 `e^{2ε}`、面积比 `e^{2ε}`）。 -/
theorem riemannianDiskArea_map_le_exp_K8
    (g₁ : SmoothRiemannianMetric 𝓘(ℝ, E) M₁) (g₂ : SmoothRiemannianMetric 𝓘(ℝ, E) M₂)
    {u : C(closedDisk, M₁)} {U : ℂ → M₁} (hU : SmoothDiskExtension (E := E) u U)
    {φ : M₁ → M₂} {V : Set M₁} (hV : IsOpen V) (hrange : range u ⊆ V)
    (hφ : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ φ V)
    {S : Set M₁} (hS : range u ⊆ S) (ε : ℝ)
    (hmetric : ∀ p ∈ S, ∀ w : TangentSpace 𝓘(ℝ, E) p,
      g₂.inner (φ p) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ p w) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ p w) ≤
        Real.exp (2 * ε) * g₁.inner p w w)
    (v : C(closedDisk, M₂)) (hv : ∀ z, v z = φ (u z)) :
    riemannianDiskArea g₂ v ≤ Real.exp (2 * ε) * riemannianDiskArea g₁ u :=
  riemannianDiskArea_map_le_K8 g₁ g₂ hU hV hrange hφ hS (Real.exp_pos _) hmetric v hv

/-- Consumer / non-vacuity：`φ = id`、`g₂ = scaleMetric c g₁` 满足 G2 的 hypotheses，
得到 `area (c • g) u ≤ c * area g u`（与 `riemannianDiskArea_scaleMetric` 一致）。 -/
example (g : SmoothRiemannianMetric 𝓘(ℝ, E) M₁) {u : C(closedDisk, M₁)} {U : ℂ → M₁}
    (hU : SmoothDiskExtension (E := E) u U) {c : ℝ} (hc : 0 < c) :
    riemannianDiskArea (scaleMetric c hc g) u ≤ c * riemannianDiskArea g u := by
  refine riemannianDiskArea_map_le_K8 g (scaleMetric c hc g) hU (φ := id) isOpen_univ
    (subset_univ _) contMDiffOn_id (S := univ) (subset_univ _) hc ?_ u (fun z => rfl)
  intro p _ w
  rw [mfderiv_id]
  exact le_of_eq (scaleMetric_inner c hc g p w w)

end DifferentialGeometry.Geometry

end
