import DifferentialGeometry.Geometry.MinimalSurface.Plateau.CollisionNodalF4AChart
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.CollisionNodalF4ATang

/-!
# F4-a（`_F4A`）模块 8：模型空间的弧对二分 + `coprod` 满射的 chart 搬运

* `coprod_surjective_transfer_F4A`：chart `e` 下 `coprod` 满射 ⇒ 原映射 `mfderiv F` 的 `coprod` 满射
  （碰撞点同值 ⇒ 同一个 `D(e.symm)`，且 `D(e.symm)` 双射）。
* **`collision_arcs_model_F4A`**：模型空间 `(g', X)`、碰撞 `a ≠ b` ⇒ 弧对（横截：`transverse_collision_arcs_F4A`；
  切向：`tangent_collision_arcs_F4A`），输出同形，直接喂 `ballify_F4A`。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Manifold Metric
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.Geometry

open DifferentialGeometry.Geometry.Analytic

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- chart `e` 下 `coprod` 满射 ⇒ 原映射的 `coprod` 满射（同一点值，同一 `D(e.symm)`）。 -/
theorem coprod_surjective_transfer_F4A {e : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) {F : ℂ → M} {z w : ℂ}
    (hFz : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ F z) (hFw : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ F w)
    (hzs : F z ∈ e.source) (hws : F w ∈ e.source) (hFeq : F z = F w)
    (hsurj : Function.Surjective ((fderiv ℝ (e ∘ F) z).coprod (-(fderiv ℝ (e ∘ F) w)))) :
    Function.Surjective ((show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F z).coprod
      (-(show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F w))) := by
  let A : E →L[ℝ] E := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm (e (F z))
  have hAinj : Function.Injective A := mfderiv_symm_injective_F3A he (e.map_source hzs)
  have hAsurj : Function.Surjective A := by
    have : Function.Injective (A : E →ₗ[ℝ] E) := hAinj
    exact LinearMap.surjective_of_injective this
  have hz : ∀ v : ℂ, (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F z) v =
      A (fderiv ℝ (e ∘ F) z v) := fun v => (mfderiv_symm_comp_F4A he hFz hzs v).symm
  have hw : ∀ v : ℂ, (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F w) v =
      A (fderiv ℝ (e ∘ F) w v) := by
    intro v
    have h := (mfderiv_symm_comp_F4A he hFw hws v).symm
    have hew : e (F w) = e (F z) := by rw [hFeq]
    rw [hew] at h
    exact h
  intro y
  obtain ⟨x, hx⟩ := hAsurj y
  obtain ⟨⟨u, u'⟩, hu⟩ := hsurj x
  refine ⟨(u, u'), ?_⟩
  rw [ContinuousLinearMap.coprod_apply] at hu ⊢
  rw [neg_apply] at hu ⊢
  dsimp only
  dsimp only at hu
  have h1 : A (fderiv ℝ (e ∘ F) z u) + -A (fderiv ℝ (e ∘ F) w u') = y := by
    rw [← map_neg, ← map_add, hu, hx]
  exact (congrArg₂ (fun p q : E => p + q) (hz u) (congrArg (fun p : E => -p) (hw u'))).trans h1

/-- 模型空间里的碰撞弧对（横截 / 切向二分）。 -/
theorem collision_arcs_model_F4A (hd3 : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) E) {X : ℂ → E} {s : Set ℂ} (hs : IsOpen s)
    (hXs : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ X s) (hXa : AnalyticOnNhd ℝ X s)
    (hconf : ∀ z ∈ s, DiskMapConformalAt g X z) (hharm : ∀ z ∈ s, diskMapTension g X z = 0)
    (hrank : ∀ z ∈ s, Function.Injective (fderiv ℝ X z))
    (hncX : ∀ V₁ V₂ : Set ℂ, IsOpen V₁ → IsOpen V₂ → V₁.Nonempty → Disjoint V₁ V₂ → V₁ ⊆ s →
      V₂ ⊆ s → InjOn X V₁ → InjOn X V₂ → ¬ X '' V₁ ⊆ X '' V₂)
    {a b : ℂ} (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b) (hv : X a = X b)
    {r₁ : ℝ} (hr₁ : 0 < r₁) :
    ∃ (k : ℕ) (r₂ S : ℝ) (c d : Fin (2 * k) → ℝ → ℂ) (v v' : Fin (2 * k) → ℂ),
      1 ≤ k ∧ 0 < r₂ ∧ r₂ ≤ r₁ ∧ 0 < S ∧ (∀ m, c m 0 = a) ∧ (∀ m, d m 0 = b) ∧
      (∀ m, ContDiffOn ℝ 1 (c m) (Icc 0 S)) ∧ (∀ m, InjOn (c m) (Icc 0 S)) ∧
      (∀ m, v m ≠ 0 ∧ HasDerivWithinAt (c m) (v m) (Icc 0 S) 0) ∧
      (∀ m, ContDiffOn ℝ 1 (d m) (Icc 0 S)) ∧
      (∀ m, v' m ≠ 0 ∧ HasDerivWithinAt (d m) (v' m) (Icc 0 S) 0) ∧
      (∀ m m', m ≠ m' → ¬ SameRay ℝ (v m) (v m') ∧
        ∀ s ∈ Icc 0 S, ∀ s' ∈ Icc 0 S, c m s = c m' s' → s = 0 ∧ s' = 0) ∧
      (∀ m, ∀ s ∈ Ico 0 S, X (c m s) = X (d m s)) ∧
      (∀ z' ∈ ball a r₂, ∀ w' ∈ ball b r₂, X z' = X w' →
        ∃ m, ∃ s ∈ Ico 0 S, z' = c m s ∧ w' = d m s) ∧
      (∀ z' ∈ ball a r₂, ∀ w' ∈ ball b r₂, X z' = X w' → z' ≠ a →
        Function.Surjective ((fderiv ℝ X z').coprod (-(fderiv ℝ X w')))) ∧
      (∀ m, ∀ t ∈ Icc 0 S, c m t ∈ s ∧ d m t ∈ s) ∧
      (∀ m, ContDiffOn ℝ ∞ (c m) (Icc 0 S)) := by
  by_cases htr : Function.Surjective ((fderiv ℝ X a).coprod (-(fderiv ℝ X b)))
  · have hX : ContDiffOn ℝ ∞ X s := contMDiffOn_iff_contDiffOn.mp hXs
    obtain ⟨r₂, S, c, d, v, v', h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15,
      h16⟩ :=
      transverse_collision_arcs_F4A hd3 hs hX ha hb hv (hrank a ha) (hrank b hb) htr hr₁
    exact ⟨1, r₂, S, c, d, v, v', le_rfl, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13,
      h14, h15, h16⟩
  · exact tangent_collision_arcs_F4A hd3 g hs hXs hXa hconf hharm hrank hncX ha hb hab hv htr hr₁

end DifferentialGeometry.Geometry
