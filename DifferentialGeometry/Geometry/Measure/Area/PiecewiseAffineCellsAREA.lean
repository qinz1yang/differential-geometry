/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Geometry.Measure.Area.PiecewiseAreaAREA

/-!
# S-MY-AREA G2：有限 a.e. disjoint affine cells 的面积 multiplicity 恒等式（`_AREA`）

外审 R-MY3 Q4(a) / D-R-MY3-16：R10.3 的 cap `a± = f ∘ α ∘ λ±`，`λ±` 在有限个 cells 上 affine
（跨 sheet 处可不连续，但复合后连续）。这里的 `V` 是全局 Riemannian-Lipschitz 映射
（取 `V = diskExtension f ∘ α'`，`α'` 是 `α|_{|T|}` 的 Lipschitz 延拓），`Λ` 是只在每个开 cell 上
与一个 affine map `z ↦ A i z + b i` 重合的映射。

* `area_affine_cell_AREA`：满秩（`A i` 单射）的开 cell：`A(V ∘ Λ, s) = A(V, Λ '' s)`。
* `area_affine_cell_degenerate_AREA`：低秩（`A i` 不单射）的开 cell：`A(V ∘ Λ, s) = 0`——
  这里**不**对 `V` 在 `Λ` 的像（一条线段）上求导：`V ∘ aff` 在沿 `ker A` 的方向上是常数，
  所以它在 `z` 处若可微则导数把 `ker A` 的非零向量映到 0，面积密度（Gram 行列式）为 0；
  不可微处面积密度按约定为 0。
* `area_piecewise_affine_cells_AREA`（**G2**）：有限个开 cells `s i`，两两 a.e. disjoint，并集 a.e. 等于
  `P`（不能只要有限覆盖）⇒ `A(V ∘ Λ, P) = ∑_{i : A i 单射} A(V, Λ '' s i)`，且面积密度在 `P` 上可积。
* `area_piecewise_affine_cells_multiplicity_AREA`：每个满秩 cell 的像 a.e. 等于目标 cell `τ (σ i)` 时，
  `A(V ∘ Λ, P) = ∑_k m_k * A(V, τ k)`，`m_k` = 满秩且 `σ i = k` 的 cell 个数（覆盖次数）。
  `m₊,σ + m₋,σ` 的和恒等式 `A(a₊) + A(a₋) = ∑_σ (m₊,σ + m₋,σ) A_σ` 是对两个 cap 各用一次，
  再 `Finset.sum_add_distrib`（见 `PiecewiseAreaConsumerAREA.lean` 的 `cap_area_pair_AREA`）。
-/

set_option autoImplicit false
noncomputable section

open Bundle Manifold Set Filter MeasureTheory DifferentialGeometry
open scoped Topology Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry.Geometry

section Degenerate

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- 两个切向量线性相关（`a • p + b • q = 0`，`(a, b) ≠ 0`）⇒ `tangentTwoJacobian = 0`。 -/
theorem tangentTwoJacobian_eq_zero_of_dependent_AREA (g : SmoothRiemannianMetric I M) {x : M}
    (p q : TangentSpace I x) (a b : ℝ) (h : a • p + b • q = 0) (hab : a ≠ 0 ∨ b ≠ 0) :
    tangentTwoJacobian g p q = 0 := by
  by_cases hb : b = 0
  · have ha : a ≠ 0 := hab.resolve_right (not_not.mpr hb)
    subst hb
    have hp : p = 0 := by simpa [ha] using h
    simp [hp, tangentTwoJacobian]
  · have hq : q = (-a / b) • p := by
      have : b • q = -(a • p) := eq_neg_of_add_eq_zero_right h
      rw [div_eq_inv_mul, mul_smul, neg_smul, ← this, smul_smul, inv_mul_cancel₀ hb, one_smul]
    rw [hq, tangentTwoJacobian_smul_self]

end Degenerate

section Cells

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T3Space M]

/-- `z ↦ A z + b` 是 `‖A‖`-Lipschitz。 -/
theorem lipschitzWith_affine_AREA (A : ℂ →L[ℝ] ℂ) (b : ℂ) :
    LipschitzWith ‖A‖₊ (fun z => A z + b) := by
  intro x y
  simpa only [edist_add_right] using A.lipschitzWith x y

/-- `A` 单射 ⇒ `z ↦ A z + b` 有下界 `edist x y ≤ L * edist (A x + b) (A y + b)`（有限维线性单射反 Lipschitz）。 -/
theorem exists_lower_bound_affine_AREA {A : ℂ →L[ℝ] ℂ} (hA : Function.Injective A) (b : ℂ) :
    ∃ L : ℝ≥0, ∀ x y : ℂ, edist x y ≤ (L : ℝ≥0∞) * edist (A x + b) (A y + b) := by
  obtain ⟨L, -, hL⟩ := (LinearMap.injective_iff_antilipschitz A.toLinearMap).mp hA
  refine ⟨L, fun x y => ?_⟩
  have h := hL x y
  rw [edist_add_right]
  exact h

/-- 满秩 affine 开 cell：`A(V ∘ Λ, s) = A(V, Λ '' s)`。 -/
theorem area_affine_cell_AREA (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {V : ℂ → M} {C : ℝ≥0}
    (hV : ∀ x y, riemannianEDistOf g (V x) (V y) ≤ (C : ℝ≥0∞) * edist x y)
    {Λ : ℂ → ℂ} {s : Set ℂ} (hs : IsOpen s) {A : ℂ →L[ℝ] ℂ} {b : ℂ}
    (hΛ : EqOn Λ (fun z => A z + b) s) (hA : Function.Injective A) :
    riemannianArea g (V ∘ Λ) s = riemannianArea g V (Λ '' s) := by
  obtain ⟨L, hL⟩ := exists_lower_bound_affine_AREA hA b
  calc
    riemannianArea g (V ∘ Λ) s = riemannianArea g (V ∘ fun z => A z + b) s :=
      riemannianArea_congr_on_open g hs (fun z hz => by simp only [Function.comp_apply, hΛ hz])
    _ = riemannianArea g V ((fun z => A z + b) '' s) :=
      riemannianArea_precomp_on g hV hs (lipschitzWith_affine_AREA A b).lipschitzOnWith
        (fun x _ y _ => hL x y)
    _ = riemannianArea g V (Λ '' s) := by rw [hΛ.image_eq]

end Cells

section Degenerate2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- 低秩 affine 映射的复合在每点的面积密度为 0（不对 `V` 在像线段上求导）。 -/
theorem riemannianAreaDensity_comp_degenerate_affine_AREA
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {V : ℂ → M} {A : ℂ →L[ℝ] ℂ} (b : ℂ)
    (hA : ¬ Function.Injective A) (z : ℂ) :
    riemannianAreaDensity g (V ∘ fun w => A w + b) z = 0 := by
  rw [Function.Injective] at hA
  push Not at hA
  obtain ⟨x, y, hxy, hne⟩ := hA
  obtain ⟨v, hv0, hAv⟩ : ∃ v : ℂ, v ≠ 0 ∧ A v = 0 :=
    ⟨x - y, sub_ne_zero.mpr hne, by rw [map_sub, hxy, sub_self]⟩
  set w : ℂ → M := V ∘ fun w => A w + b with hw
  by_cases hd : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) w z
  swap
  · exact riemannianAreaDensity_eq_zero_of_not_mdifferentiableAt g hd
  let γ : ℝ → ℂ := fun t => z + t • v
  have hconst : w ∘ γ = fun _ => w z := by
    funext t
    change V (A (z + t • v) + b) = V (A z + b)
    rw [map_add, map_smul, hAv, smul_zero, add_zero]
  have hγd : HasDerivAt γ v 0 := by
    have h := ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add z
    rwa [one_smul] at h
  have hγm : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) γ 0 := hγd.differentiableAt.mdifferentiableAt
  have hγ0 : γ 0 = z := by simp [γ]
  let B : ℂ →L[ℝ] TangentSpace 𝓘(ℝ, E) (w z) := mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) w z
  let Dγ : ℝ →L[ℝ] ℂ := mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) γ 0
  have hDγ : Dγ 1 = v := by
    have h : Dγ = fderiv ℝ γ 0 := mfderiv_eq_fderiv
    rw [h, hγd.hasFDerivAt.fderiv]
    simp
  have hc : (w ∘ γ) =ᶠ[𝓝 (0 : ℝ)] fun _ => w z :=
    Eventually.of_forall (fun t => congrFun hconst t)
  have hHas : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (w ∘ γ) 0 (0 : ℝ →L[ℝ] E) :=
    (hasMFDerivAt_const (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, E)) (w z) (0 : ℝ)).congr_of_eventuallyEq hc
  have hzero : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (w ∘ γ) 0 (1 : ℝ) = 0 := by
    rw [hHas.mfderiv]
    rfl
  have hB : B v = 0 := by
    have h2 : B (Dγ 1) = mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (w ∘ γ) 0 (1 : ℝ) :=
      (mfderiv_comp_apply_of_eq (I := 𝓘(ℝ, ℝ)) (x := (0 : ℝ)) hd hγm hγ0 (1 : ℝ)).symm
    rw [← hDγ]
    exact h2.trans hzero
  have hv (c : ℂ) : B c = c.re • B 1 + c.im • B Complex.I := by
    rw [← map_smul, ← map_smul, ← map_add]
    congr 1
    simp [Complex.real_smul, Complex.re_add_im]
  unfold riemannianAreaDensity
  refine tangentTwoJacobian_eq_zero_of_dependent_AREA g (B 1) (B Complex.I) v.re v.im ?_ ?_
  · rw [← hv v]
    exact hB
  · by_contra hcon
    push Not at hcon
    exact hv0 (Complex.ext (by simpa using hcon.1) (by simpa using hcon.2))

/-- 低秩 affine 开 cell 的面积为 0（`V` 任意，不需要 Lipschitz）。 -/
theorem area_affine_cell_degenerate_AREA (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {V : ℂ → M}
    {Λ : ℂ → ℂ} {s : Set ℂ} (hs : IsOpen s) {A : ℂ →L[ℝ] ℂ} {b : ℂ}
    (hΛ : EqOn Λ (fun z => A z + b) s) (hA : ¬ Function.Injective A) :
    riemannianArea g (V ∘ Λ) s = 0 := by
  refine setIntegral_eq_zero_of_forall_eq_zero fun z hz => ?_
  rw [riemannianAreaDensity_congr g (u := V ∘ Λ) (v := V ∘ fun w => A w + b) ?_]
  · exact riemannianAreaDensity_comp_degenerate_affine_AREA g b hA z
  · filter_upwards [hs.mem_nhds hz] with w hw
    simp only [Function.comp_apply, hΛ hw]

end Degenerate2

section Assembly

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T3Space M]

open scoped Classical in
/-- **G2**（`area_piecewise_affine_cells_AREA`）：有限个开 affine cells `s i`（两两 a.e. disjoint，
并集 a.e. 等于 `P`），`Λ` 在 `s i` 上与 `z ↦ A i z + b i` 重合 ⇒ 面积密度在 `P` 上可积，且
`A(V ∘ Λ, P) = ∑_{i : A i 单射} A(V, Λ '' s i)`（低秩 cell 贡献 0；不需要 `Λ` 全局连续）。 -/
theorem area_piecewise_affine_cells_AREA (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {V : ℂ → M} {C : ℝ≥0}
    (hV : ∀ x y, riemannianEDistOf g (V x) (V y) ≤ (C : ℝ≥0∞) * edist x y)
    {ι : Type*} [Fintype ι] {P : Set ℂ} (hP : volume P ≠ ⊤) (s : ι → Set ℂ)
    (hs : ∀ i, IsOpen (s i)) (hsP : ∀ i, s i ⊆ P)
    (hsdisj : Pairwise (fun i j => AEDisjoint volume (s i) (s j)))
    (hcover : (⋃ i, s i) =ᵐ[volume] P) {Λ : ℂ → ℂ}
    (A : ι → ℂ →L[ℝ] ℂ) (b : ι → ℂ) (hΛ : ∀ i, EqOn Λ (fun z => A i z + b i) (s i)) :
    IntegrableOn (riemannianAreaDensity g (V ∘ Λ)) P ∧
      riemannianArea g (V ∘ Λ) P =
        ∑ i with Function.Injective (A i), riemannianArea g V (Λ '' s i) := by
  have hLip (i : ι) : LipschitzOnWith ‖A i‖₊ Λ (s i) := by
    intro x hx y hy
    rw [hΛ i hx, hΛ i hy]
    exact lipschitzWith_affine_AREA (A i) (b i) x y
  have hcellInt (i : ι) : IntegrableOn (riemannianAreaDensity g (V ∘ Λ)) (s i) :=
    integrableOn_density_comp_lipschitzOn_AREA g hV (hs i) (hLip i)
      (ne_top_of_le_ne_top hP (measure_mono (hsP i)))
  have hUnion : IntegrableOn (riemannianAreaDensity g (V ∘ Λ)) (⋃ i, s i) :=
    integrableOn_finite_iUnion.mpr hcellInt
  refine ⟨hUnion.congr_set_ae hcover.symm, ?_⟩
  calc
    riemannianArea g (V ∘ Λ) P = riemannianArea g (V ∘ Λ) (⋃ i, s i) :=
      setIntegral_congr_set hcover.symm
    _ = ∑ i, riemannianArea g (V ∘ Λ) (s i) :=
      riemannianArea_finite_decomposition g _ s (fun i => (hs i).measurableSet) hsdisj hUnion
    _ = ∑ i, if Function.Injective (A i) then riemannianArea g V (Λ '' s i) else 0 := by
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases hA : Function.Injective (A i)
      · simp only [hA, ↓reduceIte]
        exact area_affine_cell_AREA g hV (hs i) (hΛ i) hA
      · simp only [hA, ↓reduceIte]
        exact area_affine_cell_degenerate_AREA g (hs i) (hΛ i) hA
    _ = _ := (Finset.sum_filter _ _).symm

open scoped Classical in
/-- **multiplicity 恒等式**：每个满秩 cell `i` 的像 a.e. 等于目标 cell `τ (σ i)` 时，
`A(V ∘ Λ, P) = ∑_k m_k * A(V, τ k)`，`m_k` 是满秩且 `σ i = k` 的 cell 个数（覆盖次数）。 -/
theorem area_piecewise_affine_cells_multiplicity_AREA (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {V : ℂ → M} {C : ℝ≥0}
    (hV : ∀ x y, riemannianEDistOf g (V x) (V y) ≤ (C : ℝ≥0∞) * edist x y)
    {ι : Type*} [Fintype ι] {P : Set ℂ} (hP : volume P ≠ ⊤) (s : ι → Set ℂ)
    (hs : ∀ i, IsOpen (s i)) (hsP : ∀ i, s i ⊆ P)
    (hsdisj : Pairwise (fun i j => AEDisjoint volume (s i) (s j)))
    (hcover : (⋃ i, s i) =ᵐ[volume] P) {Λ : ℂ → ℂ}
    (A : ι → ℂ →L[ℝ] ℂ) (b : ι → ℂ) (hΛ : ∀ i, EqOn Λ (fun z => A i z + b i) (s i))
    {κ : Type*} [Fintype κ] (τ : κ → Set ℂ) (σ : ι → κ)
    (hmatch : ∀ i, Function.Injective (A i) → Λ '' s i =ᵐ[volume] τ (σ i)) :
    riemannianArea g (V ∘ Λ) P =
      ∑ k, ((Finset.univ.filter fun i => Function.Injective (A i) ∧ σ i = k).card : ℝ) *
        riemannianArea g V (τ k) := by
  rw [(area_piecewise_affine_cells_AREA g hV hP s hs hsP hsdisj hcover A b hΛ).2]
  have hcell : ∀ i ∈ Finset.univ.filter (fun i => Function.Injective (A i)),
      riemannianArea g V (Λ '' s i) = riemannianArea g V (τ (σ i)) := fun i hi =>
    setIntegral_congr_set (hmatch i (Finset.mem_filter.mp hi).2)
  rw [Finset.sum_congr rfl hcell, ← Finset.sum_fiberwise_of_maps_to
    (s := Finset.univ.filter fun i => Function.Injective (A i)) (t := Finset.univ) (g := σ)
    (fun _ _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hk : ∀ i ∈ (Finset.univ.filter fun i => Function.Injective (A i)).filter
      (fun i => σ i = k), riemannianArea g V (τ (σ i)) = riemannianArea g V (τ k) :=
    fun i hi => by rw [(Finset.mem_filter.mp hi).2]
  rw [Finset.sum_congr rfl hk, Finset.sum_const, Finset.filter_filter, nsmul_eq_mul]

end Assembly

end DifferentialGeometry.Geometry
