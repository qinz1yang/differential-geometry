import DifferentialGeometry.Geometry.MinimalSurface.Plateau.CollisionNodalF4AHeight

/-!
# F4-a（`_F4A`）模块 4：height difference 的横截性 adapter

* `range_le_of_not_transverse_F4A`：非横截 ⇒ `range K ≤ range L`（树里同名引理 private，这里重证）。
* `fderiv_symm_fderiv_F4A`：`e.symm ∘ e = id` 的导数版。
* **`fderiv_height_diff_eq_zero_F4A`**：两张 sheet 在 `e₁.symm y`、`e₂.symm y` 碰撞且切平面重合 ⇒
  height difference `w` 在 `y` 处 `dw = 0`；逆否：`dw ≠ 0` ⇒ `Surjective coprod`（横截），
  供 R3AW 的 `fderiv w ≠ 0`（regular zero）换回 S8 的横截条款。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Manifold Metric Bundle
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- 非横截 ⇒ 值域包含（树里的同名引理是 private，这里重证）。 -/
theorem range_le_of_not_transverse_F4A (L K : ℂ →L[ℝ] E) (hd3 : Module.finrank ℝ E = 3)
    (hL : Function.Injective L) (hnot : ¬ Function.Surjective (L.coprod (-K))) :
    LinearMap.range K.toLinearMap ≤ LinearMap.range L.toLinearMap := by
  let S := LinearMap.range (L.coprod (-K)).toLinearMap
  have hLS : LinearMap.range L.toLinearMap ≤ S := by
    rintro v ⟨w, rfl⟩
    refine ⟨(w, 0), ?_⟩
    simp
  have hKS : LinearMap.range K.toLinearMap ≤ S := by
    rintro v ⟨w, rfl⟩
    refine ⟨(0, -w), ?_⟩
    simp
  have hSne : S ≠ ⊤ := fun h => hnot (LinearMap.range_eq_top.mp h)
  have hSdim : Module.finrank ℝ S < 3 := by
    have h := Submodule.finrank_lt_finrank_of_lt (lt_top_iff_ne_top.mpr hSne)
    simpa only [finrank_top, hd3] using h
  have hLdim : Module.finrank ℝ (LinearMap.range L.toLinearMap) = 2 := by
    rw [LinearMap.finrank_range_of_inj hL]
    rw [Module.finrank_eq_card_basis Complex.basisOneI, Fintype.card_fin]
  have hEq : LinearMap.range L.toLinearMap = S :=
    Submodule.eq_of_le_of_finrank_eq hLS (by
      have hle := Submodule.finrank_mono hLS
      omega)
  exact hKS.trans hEq.ge

/-- `e.symm ∘ e = id` 的导数版。 -/
theorem fderiv_symm_fderiv_F4A {e : OpenPartialHomeomorph ℂ ℂ}
    (hei : ContDiffOn ℝ ∞ e.symm e.target) {z : ℂ} (hz : z ∈ e.source)
    (hdiff : DifferentiableAt ℝ e z) (v : ℂ) :
    fderiv ℝ e.symm (e z) (fderiv ℝ e z v) = v := by
  have hy : e z ∈ e.target := e.map_source hz
  have hdiff' : DifferentiableAt ℝ e.symm (e z) :=
    (hei.contDiffAt (e.open_target.mem_nhds hy)).differentiableAt (by simp)
  have h1 : ∀ᶠ x in 𝓝 z, e.symm (e x) = x := by
    filter_upwards [e.open_source.mem_nhds hz] with x hx using e.left_inv hx
  have hc : HasFDerivAt (e.symm ∘ e) ((fderiv ℝ e.symm (e z)).comp (fderiv ℝ e z)) z :=
    HasFDerivAt.comp z hdiff'.hasFDerivAt hdiff.hasFDerivAt
  have hid : HasFDerivAt (e.symm ∘ e) (ContinuousLinearMap.id ℝ ℂ) z :=
    (hasFDerivAt_id z).congr_of_eventuallyEq (by filter_upwards [h1] with x hx using hx)
  exact congrArg (fun L : ℂ →L[ℝ] ℂ => L v) (hc.unique hid)

/-- **dw = 0 ⇐ 非横截**：两张 sheet 在 `z₁ = e₁.symm y`、`z₂ = e₂.symm y` 处碰撞且切平面重合，
则 height difference 在 `y` 处导数为零。逆否：`dw ≠ 0` ⇒ 横截（`Surjective coprod`）。 -/
theorem fderiv_height_diff_eq_zero_F4A (hd3 : Module.finrank ℝ E = 3)
    {X : ℂ → E} {s : Set ℂ} (hXd : ∀ z ∈ s, DifferentiableAt ℝ X z)
    (hrank : ∀ z ∈ s, Function.Injective (fderiv ℝ X z))
    {proj : E →L[ℝ] ℂ} {N : E} {lift : ℂ →L[ℝ] E} {Q : E →L[ℝ] E →L[ℝ] ℝ} {x₀ : E} {y₀ : ℂ}
    (hNN : Q N N = 1) (hPN : proj N = 0)
    {e₁ e₂ : OpenPartialHomeomorph ℂ ℂ} (he₁ : (e₁ : ℂ → ℂ) = proj ∘ X)
    (he₁s : e₁.source ⊆ s) (he₂s : e₂.source ⊆ s)
    (hei₁ : ContDiffOn ℝ ∞ e₁.symm e₁.target) (hei₂ : ContDiffOn ℝ ∞ e₂.symm e₂.target)
    {O : Set ℂ} (hOo : IsOpen O) (hO₁ : O ⊆ e₁.target) (hO₂ : O ⊆ e₂.target)
    (hrecon : ∀ y ∈ O,
      X (e₁.symm y) = x₀ + lift (y - y₀) + (Q N (X (e₁.symm y) - x₀)) • N ∧
      X (e₂.symm y) = x₀ + lift (y - y₀) + (Q N (X (e₂.symm y) - x₀)) • N)
    {y : ℂ} (hy : y ∈ O)
    (hnot : ¬ Function.Surjective
      ((fderiv ℝ X (e₁.symm y)).coprod (-(fderiv ℝ X (e₂.symm y))))) :
    fderiv ℝ (fun y => Q N (X (e₁.symm y) - x₀) - Q N (X (e₂.symm y) - x₀)) y = 0 := by
  have hz₁ : e₁.symm y ∈ e₁.source := e₁.map_target (hO₁ hy)
  have hz₂ : e₂.symm y ∈ e₂.source := e₂.map_target (hO₂ hy)
  have hXd₁ := hXd _ (he₁s hz₁)
  have hXd₂ := hXd _ (he₂s hz₂)
  have hsd₁ : DifferentiableAt ℝ e₁.symm y :=
    (hei₁.contDiffAt (e₁.open_target.mem_nhds (hO₁ hy))).differentiableAt (by simp)
  have hsd₂ : DifferentiableAt ℝ e₂.symm y :=
    (hei₂.contDiffAt (e₂.open_target.mem_nhds (hO₂ hy))).differentiableAt (by simp)
  have hrange := range_le_of_not_transverse_F4A _ _ hd3 (hrank _ (he₁s hz₁)) hnot
  -- 两张 sheet 的切向量
  have key : ∀ (e' : OpenPartialHomeomorph ℂ ℂ) (hsub : e'.source ⊆ s)
      (hd : DifferentiableAt ℝ e'.symm y) (hOe : O ⊆ e'.target)
      (hr : ∀ y ∈ O, X (e'.symm y) = x₀ + lift (y - y₀) + (Q N (X (e'.symm y) - x₀)) • N),
      ∀ v, fderiv ℝ X (e'.symm y) (fderiv ℝ e'.symm y v) =
        lift v + fderiv ℝ (fun y => Q N (X (e'.symm y) - x₀)) y v • N := by
    intro e' hsub hd hOe hr v
    have hz : e'.symm y ∈ e'.source := e'.map_target (hOe hy)
    have hXdz := hXd _ (hsub hz)
    have hLHS : HasFDerivAt (fun y => X (e'.symm y))
        ((fderiv ℝ X (e'.symm y)).comp (fderiv ℝ e'.symm y)) y :=
      HasFDerivAt.comp y hXdz.hasFDerivAt hd.hasFDerivAt
    have hh : HasFDerivAt (fun y => Q N (X (e'.symm y) - x₀))
        ((Q N).comp ((fderiv ℝ X (e'.symm y)).comp (fderiv ℝ e'.symm y))) y :=
      (Q N).hasFDerivAt.comp y (hLHS.sub_const x₀)
    have hRHS : HasFDerivAt (fun y => x₀ + lift (y - y₀) + (Q N (X (e'.symm y) - x₀)) • N)
        (lift + (fderiv ℝ (fun y => Q N (X (e'.symm y) - x₀)) y).smulRight N) y := by
      have h1 : HasFDerivAt (fun y : ℂ => lift (y - y₀)) lift y :=
        lift.hasFDerivAt.comp y ((hasFDerivAt_id y).sub_const y₀)
      have h2 := (hh.differentiableAt.hasFDerivAt).smul_const N
      exact (h1.const_add x₀).add h2
    have heq : (fun y => X (e'.symm y)) =ᶠ[𝓝 y]
        (fun y => x₀ + lift (y - y₀) + (Q N (X (e'.symm y) - x₀)) • N) := by
      filter_upwards [hOo.mem_nhds hy] with y' hy' using hr y' hy'
    have := (hLHS.congr_of_eventuallyEq heq.symm).unique hRHS
    have := congrArg (fun L : ℂ →L[ℝ] E => L v) this
    simpa using this
  have h₁ := key e₁ he₁s hsd₁ hO₁ (fun y hy => (hrecon y hy).1)
  have h₂ := key e₂ he₂s hsd₂ hO₂ (fun y hy => (hrecon y hy).2)
  -- 差
  have hd₁ : DifferentiableAt ℝ (fun y => Q N (X (e₁.symm y) - x₀)) y :=
    ((Q N).differentiableAt).comp y ((hXd₁.comp y hsd₁).sub_const x₀)
  have hd₂ : DifferentiableAt ℝ (fun y => Q N (X (e₂.symm y) - x₀)) y :=
    ((Q N).differentiableAt).comp y ((hXd₂.comp y hsd₂).sub_const x₀)
  rw [fderiv_fun_sub hd₁ hd₂]
  ext v
  simp only [sub_apply, zero_apply]
  rw [sub_eq_zero]
  by_contra hne
  have hc : fderiv ℝ (fun y => Q N (X (e₂.symm y) - x₀)) y v -
      fderiv ℝ (fun y => Q N (X (e₁.symm y) - x₀)) y v ≠ 0 := by
    intro h
    exact hne (sub_eq_zero.mp h).symm
  have ht₁ : fderiv ℝ X (e₁.symm y) (fderiv ℝ e₁.symm y v) ∈
      LinearMap.range (fderiv ℝ X (e₁.symm y)).toLinearMap := ⟨_, rfl⟩
  have ht₂ : fderiv ℝ X (e₂.symm y) (fderiv ℝ e₂.symm y v) ∈
      LinearMap.range (fderiv ℝ X (e₁.symm y)).toLinearMap :=
    hrange ⟨_, rfl⟩
  have hdiffN : (fderiv ℝ (fun y => Q N (X (e₂.symm y) - x₀)) y v -
      fderiv ℝ (fun y => Q N (X (e₁.symm y) - x₀)) y v) • N ∈
      LinearMap.range (fderiv ℝ X (e₁.symm y)).toLinearMap := by
    have : (fderiv ℝ (fun y => Q N (X (e₂.symm y) - x₀)) y v -
        fderiv ℝ (fun y => Q N (X (e₁.symm y) - x₀)) y v) • N =
        fderiv ℝ X (e₂.symm y) (fderiv ℝ e₂.symm y v) -
          fderiv ℝ X (e₁.symm y) (fderiv ℝ e₁.symm y v) := by
      rw [h₁ v, h₂ v, sub_smul]
      abel
    rw [this]
    exact Submodule.sub_mem _ ht₂ ht₁
  have hN : N ∈ LinearMap.range (fderiv ℝ X (e₁.symm y)).toLinearMap := by
    have := Submodule.smul_mem _ (fderiv ℝ (fun y => Q N (X (e₂.symm y) - x₀)) y v -
      fderiv ℝ (fun y => Q N (X (e₁.symm y) - x₀)) y v)⁻¹ hdiffN
    rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this
  obtain ⟨u, hu⟩ := hN
  have hdiffe₁ : DifferentiableAt ℝ e₁ (e₁.symm y) := by
    rw [he₁]
    exact proj.differentiableAt.comp _ hXd₁
  have hfe : fderiv ℝ e₁ (e₁.symm y) = proj.comp (fderiv ℝ X (e₁.symm y)) := by
    rw [he₁]
    exact (proj.hasFDerivAt.comp _ hXd₁.hasFDerivAt).fderiv
  have hu1 : fderiv ℝ e₁ (e₁.symm y) u = 0 := by
    rw [hfe]
    change proj (fderiv ℝ X (e₁.symm y) u) = 0
    have hu' : fderiv ℝ X (e₁.symm y) u = N := hu
    rw [hu', hPN]
  have hu0 : u = 0 := by
    have := fderiv_symm_fderiv_F4A hei₁ hz₁ hdiffe₁ u
    rw [hu1, map_zero] at this
    exact this.symm
  have hN0 : N = 0 := by
    have hu' : fderiv ℝ X (e₁.symm y) u = N := hu
    rw [← hu', hu0, map_zero]
  rw [hN0] at hNN
  simp at hNN

/-- 逆否（consumer）：`dw(y) ≠ 0`（R3AW 的 regular zero）⇒ `coprod` 满射，即 S8 的横截条款。 -/
theorem surjective_coprod_of_fderiv_height_diff_ne_zero_F4A (hd3 : Module.finrank ℝ E = 3)
    {X : ℂ → E} {s : Set ℂ} (hXd : ∀ z ∈ s, DifferentiableAt ℝ X z)
    (hrank : ∀ z ∈ s, Function.Injective (fderiv ℝ X z))
    {proj : E →L[ℝ] ℂ} {N : E} {lift : ℂ →L[ℝ] E} {Q : E →L[ℝ] E →L[ℝ] ℝ} {x₀ : E} {y₀ : ℂ}
    (hNN : Q N N = 1) (hPN : proj N = 0)
    {e₁ e₂ : OpenPartialHomeomorph ℂ ℂ} (he₁ : (e₁ : ℂ → ℂ) = proj ∘ X)
    (he₁s : e₁.source ⊆ s) (he₂s : e₂.source ⊆ s)
    (hei₁ : ContDiffOn ℝ ∞ e₁.symm e₁.target) (hei₂ : ContDiffOn ℝ ∞ e₂.symm e₂.target)
    {O : Set ℂ} (hOo : IsOpen O) (hO₁ : O ⊆ e₁.target) (hO₂ : O ⊆ e₂.target)
    (hrecon : ∀ y ∈ O,
      X (e₁.symm y) = x₀ + lift (y - y₀) + (Q N (X (e₁.symm y) - x₀)) • N ∧
      X (e₂.symm y) = x₀ + lift (y - y₀) + (Q N (X (e₂.symm y) - x₀)) • N)
    {y : ℂ} (hy : y ∈ O)
    (hdw : fderiv ℝ (fun y => Q N (X (e₁.symm y) - x₀) - Q N (X (e₂.symm y) - x₀)) y ≠ 0) :
    Function.Surjective ((fderiv ℝ X (e₁.symm y)).coprod (-(fderiv ℝ X (e₂.symm y)))) := by
  by_contra hns
  exact hdw (fderiv_height_diff_eq_zero_F4A hd3 hXd hrank hNN hPN he₁ he₁s he₂s hei₁ hei₂ hOo
    hO₁ hO₂ hrecon hy hns)

end DifferentialGeometry.Geometry
