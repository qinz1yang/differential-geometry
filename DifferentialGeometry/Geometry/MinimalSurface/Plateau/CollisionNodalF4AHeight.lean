import DifferentialGeometry.Geometry.MinimalSurface.Plateau.CollisionNodalF4AChart
import DifferentialGeometry.Geometry.HarmonicMap.TangentGraphGerms
import DifferentialGeometry.Geometry.HarmonicMap.MinimalGraphDifference

/-!
# F4-a（`_F4A`）模块 3：模型空间里的解析 height difference（G1 的欧氏核心）

`(g', X)`：`X : ℂ → E` 在开集 `s` 上解析、conformal、harmonic（对全局光滑度量 `g'`），`E` 作为 `chartAt = refl`
的流形。两个碰撞点 `a ≠ b`、`X a = X b`、同一切平面（非横截）。套树里的黑盒
`chartLeadingPlaneProjection_exists_tangent_collision_germs` +
`chartLeadingPlaneProjection_two_graphs_height_difference`
（`M := E`，`extChartAt = id`），得 `e₁ e₂ : ℂ ≃ₚ ℂ`、`O`、height difference
`w y = Q N (X (e₁.symm y) - X a) - Q N (X (e₂.symm y) - X a)` 和它的光滑系数椭圆方程；
再用 Mathlib 的多元解析反函数 `OpenPartialHomeomorph.analyticAt_symm` 得 `w` 解析。

* `analyticAt_symm_of_analytic_F4A`：`e` 在 source 上解析、逆 `C^∞` ⇒ 逆解析。
* **`height_difference_model_F4A`**：G1 欧氏核心。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Manifold Metric Bundle
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.Geometry

open DifferentialGeometry.Tensor.Coordinates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]


/-- 局部同胚 `e : ℂ → ℂ` 在 source 上解析、逆 `C^∞` ⇒ 逆在 target 上解析（多元解析反函数定理）。 -/
theorem analyticAt_symm_of_analytic_F4A {e : OpenPartialHomeomorph ℂ ℂ}
    (hei : ContDiffOn ℝ ∞ e.symm e.target) (hana : ∀ z ∈ e.source, AnalyticAt ℝ e z) {y : ℂ}
    (hy : y ∈ e.target) : AnalyticAt ℝ e.symm y := by
  have hz : e.symm y ∈ e.source := e.map_target hy
  have hdiff : DifferentiableAt ℝ e (e.symm y) := (hana _ hz).differentiableAt
  have hdiff' : DifferentiableAt ℝ e.symm y :=
    (hei.contDiffAt (e.open_target.mem_nhds hy)).differentiableAt (by simp)
  have h1 : ∀ᶠ x in 𝓝 (e.symm y), e.symm (e x) = x := by
    filter_upwards [e.open_source.mem_nhds hz] with x hx using e.left_inv hx
  have h2 : ∀ᶠ x in 𝓝 y, e (e.symm x) = x := by
    filter_upwards [e.open_target.mem_nhds hy] with x hx using e.right_inv hx
  have hL : ∀ v, fderiv ℝ e.symm y (fderiv ℝ e (e.symm y) v) = v := by
    intro v
    have hc : HasFDerivAt (e.symm ∘ e)
        ((fderiv ℝ e.symm (e (e.symm y))).comp (fderiv ℝ e (e.symm y))) (e.symm y) := by
      refine HasFDerivAt.comp (e.symm y) ?_ hdiff.hasFDerivAt
      rw [e.right_inv hy]
      exact hdiff'.hasFDerivAt
    have hid : HasFDerivAt (e.symm ∘ e) (ContinuousLinearMap.id ℝ ℂ) (e.symm y) :=
      (hasFDerivAt_id (e.symm y)).congr_of_eventuallyEq (by
        filter_upwards [h1] with x hx using hx)
    have := hc.unique hid
    rw [e.right_inv hy] at this
    exact congrArg (fun L : ℂ →L[ℝ] ℂ => L v) this
  have hR : ∀ v, fderiv ℝ e (e.symm y) (fderiv ℝ e.symm y v) = v := by
    intro v
    have hc : HasFDerivAt (e ∘ e.symm)
        ((fderiv ℝ e (e.symm y)).comp (fderiv ℝ e.symm y)) y :=
      HasFDerivAt.comp y hdiff.hasFDerivAt hdiff'.hasFDerivAt
    have hid : HasFDerivAt (e ∘ e.symm) (ContinuousLinearMap.id ℝ ℂ) y :=
      (hasFDerivAt_id y).congr_of_eventuallyEq (by filter_upwards [h2] with x hx using hx)
    have := hc.unique hid
    exact congrArg (fun L : ℂ →L[ℝ] ℂ => L v) this
  let i : ℂ ≃L[ℝ] ℂ := ContinuousLinearEquiv.equivOfInverse (fderiv ℝ e (e.symm y))
    (fderiv ℝ e.symm y) hL hR
  exact e.analyticAt_symm (i := i) hy (hana _ hz) rfl

theorem height_difference_model_F4A (hd3 : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) E)
    {X : ℂ → E} {s : Set ℂ} (hs : IsOpen s)
    (hXs : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ X s) (hXa : AnalyticOnNhd ℝ X s)
    (hconf : ∀ z ∈ s, DiskMapConformalAt g X z)
    (hharm : ∀ z ∈ s, diskMapTension g X z = 0)
    {a b : ℂ} (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b) (hvalue : X a = X b)
    (hDa : Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) X a))
    (hDb : Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) X b))
    (hnot : ¬ Function.Surjective
      ((show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) X a).coprod
        (-(show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) X b)))) :
    ∃ (proj : E →L[ℝ] ℂ) (N : E) (lift : ℂ →L[ℝ] E) (Q : E →L[ℝ] E →L[ℝ] ℝ)
      (e₁ e₂ : OpenPartialHomeomorph ℂ ℂ) (O : Set ℂ),
      Q N N = 1 ∧ proj N = 0 ∧
      (e₁ : ℂ → ℂ) = proj ∘ X ∧ (e₂ : ℂ → ℂ) = proj ∘ X ∧
      a ∈ e₁.source ∧ b ∈ e₂.source ∧ e₁.source ⊆ s ∧ e₂.source ⊆ s ∧
      Disjoint e₁.source e₂.source ∧
      ContDiffOn ℝ ∞ e₁.symm e₁.target ∧ ContDiffOn ℝ ∞ e₂.symm e₂.target ∧
      IsOpen O ∧ proj (X a) ∈ O ∧ O ⊆ e₁.target ∩ e₂.target ∧
      (∀ y ∈ O, X (e₁.symm y) = X a + lift (y - proj (X a)) + (Q N (X (e₁.symm y) - X a)) • N ∧
        X (e₂.symm y) = X a + lift (y - proj (X a)) + (Q N (X (e₂.symm y) - X a)) • N) ∧
      ContDiffOn ℝ ∞ (fun y => Q N (X (e₁.symm y) - X a) - Q N (X (e₂.symm y) - X a)) O ∧
      AnalyticOnNhd ℝ (fun y => Q N (X (e₁.symm y) - X a) - Q N (X (e₂.symm y) - X a)) O ∧
      ∃ (A : ℂ → Matrix (Fin 2) (Fin 2) ℝ) (beta : ℂ → Fin 2 → ℝ) (c : ℂ → ℝ),
        (∀ i j : Fin 2, ContDiffOn ℝ ∞ (fun y => A y i j) O) ∧
        (∀ i : Fin 2, ContDiffOn ℝ ∞ (fun y => beta y i) O) ∧ ContDiffOn ℝ ∞ c O ∧
        ∀ y ∈ O, (A y).PosDef ∧
          (∑ i : Fin 2, ∑ j : Fin 2, A y i j *
            fderiv ℝ (fderiv ℝ (fun y => Q N (X (e₁.symm y) - X a) - Q N (X (e₂.symm y) - X a))) y
              ((![1, Complex.I] : Fin 2 → ℂ) i) ((![1, Complex.I] : Fin 2 → ℂ) j)) +
            (∑ i : Fin 2, beta y i * fderiv ℝ
              (fun y => Q N (X (e₁.symm y) - X a) - Q N (X (e₂.symm y) - X a)) y
                ((![1, Complex.I] : Fin 2 → ℂ) i)) +
            c y * (Q N (X (e₁.symm y) - X a) - Q N (X (e₂.symm y) - X a)) = 0 := by
  classical
  have hchart : ∀ z ∈ s, X z ∈ (chartAt E (X a)).source := by
    intro z _
    rw [chartAt_self_eq]
    exact mem_univ _
  have hXc : ∀ z, extChartAt 𝓘(ℝ, E) (X a) (X z) = X z := fun z => by
    rw [extChartAt_model_space_eq_id]
    rfl
  with_reducible
    obtain ⟨N, e₁, e₂, O, hNN, hPN, hsplit, hae₁, hbe₂, he₁s, he₂s, hdisj, he₁, he₂, hei₁, hei₂,
      hOo, haO, hOsub, hsegment⟩ :=
      chartLeadingPlaneProjection_exists_tangent_collision_germs g hd3 hs hXs hconf ha hb hab
        hvalue hchart hDa hDb hnot
  have hO₁ : O ⊆ e₁.target := hOsub.trans inter_subset_left
  have hO₂ : O ⊆ e₂.target := hOsub.trans inter_subset_right
  with_reducible
    have hdata := chartLeadingPlaneProjection_two_graphs_height_difference g hs hXs hconf hharm
      (a := a) (p := X a) hchart
      (b := fun i => chartComplexGradient (X a) X i a) N hNN hPN hsplit
      e₁ e₂ he₁s he₂s he₁ he₂ hei₁ hei₂ hOo hO₁ hO₂ hsegment
  obtain ⟨hh₁, hh₂, hw, hrecon, -, hA, hbeta, hc, hpde⟩ := hdata
  let Lℓ : ℂ →ₗ[ℝ] E :=
    { toFun := fun w => (chartModelBasis E).equivFunL.symm
        (fun i => (2 : ℝ) * (w * chartComplexGradient (X a) X i a).re)
      map_add' := fun w w' => by
        rw [← map_add]
        congr 1
        funext i
        simp only [Pi.add_apply, add_mul, Complex.add_re]
        ring
      map_smul' := fun r w => by
        rw [RingHom.id_apply, ← map_smul]
        congr 1
        funext i
        simp only [Pi.smul_apply, smul_eq_mul, Complex.real_smul, Complex.re_ofReal_mul, mul_assoc]
        ring_nf }
  refine ⟨chartLeadingPlaneProjection g (X a) (X a) (fun i => chartComplexGradient (X a) X i a), N,
    LinearMap.toContinuousLinearMap Lℓ,
    chartGramBilin g (X a) (X a), e₁, e₂, O, hNN, hPN, he₁, he₂, hae₁, hbe₂, he₁s, he₂s, hdisj,
    hei₁, hei₂, hOo, haO, hOsub, ?_, hw, ?_, ?_⟩
  · intro y hy
    obtain ⟨h1, h2, -, -⟩ := hrecon y hy
    exact ⟨h1.symm, h2.symm⟩
  · let proj : E →L[ℝ] ℂ :=
      chartLeadingPlaneProjection g (X a) (X a) (fun i => chartComplexGradient (X a) X i a)
    have he₁' : (e₁ : ℂ → ℂ) = proj ∘ X := he₁
    have he₂' : (e₂ : ℂ → ℂ) = proj ∘ X := he₂
    have hXe : ∀ e' : OpenPartialHomeomorph ℂ ℂ, (e' : ℂ → ℂ) = proj ∘ X →
        ContDiffOn ℝ ∞ e'.symm e'.target → e'.source ⊆ s → ∀ y ∈ e'.target,
        AnalyticAt ℝ (fun y => X (e'.symm y)) y := by
      intro e' he' hei hsub y hy
      have hana : ∀ z ∈ e'.source, AnalyticAt ℝ e' z := by
        intro z hz
        rw [he']
        exact (proj.analyticAt (X z)).comp (hXa z (hsub hz))
      have hsy := analyticAt_symm_of_analytic_F4A hei hana hy
      exact (hXa _ (hsub (e'.map_target hy))).comp hsy
    intro y hy
    have h1 := hXe e₁ he₁' hei₁ he₁s y (hO₁ hy)
    have h2 := hXe e₂ he₂' hei₂ he₂s y (hO₂ hy)
    exact (((chartGramBilin g (X a) (X a)) N).analyticAt _).comp (h1.sub analyticAt_const) |>.sub
      ((((chartGramBilin g (X a) (X a)) N).analyticAt _).comp (h2.sub analyticAt_const))
  · refine ⟨_, _, _, fun i j => (hA i j).1, hbeta, hc, ?_⟩
    intro y hy
    obtain ⟨-, -, hpos, -, -, -, -, -, hEq⟩ := hpde y hy
    exact ⟨hpos, hEq⟩

end DifferentialGeometry.Geometry
