import DifferentialGeometry.Geometry.MinimalSurface.Plateau.CollisionNodalF4ATransv
import DifferentialGeometry.Analysis.Elliptic.Planar.AnalyticNodalR3AW
import DifferentialGeometry.Analysis.Elliptic.Planar.AnalyticNodalSmoothF4A
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.PreparedSheetComplexR3AWAlignFIX2
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.CollisionNodalF4ABallify
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.CollisionNodalF4ACross

/-!
# F4-a（`_F4A`）模块 7：切向碰撞（非横截）的弧对

模型空间 `(g', X)` 下，非横截碰撞 `(a, b)`：
1. `height_difference_model_F4A`（G1 欧氏核心）给解析 height difference `w`、光滑系数椭圆方程；
2. `no open sheet coincidence`（`hncX`）⇒ `w` 在 `y₀ = proj (X a)` 的芽非零；
3. `two_sheet_nodal_structure_analytic_R3AW` ⇒ `2k` 条 half-arcs `Γ'`（`IsNodalHalfArcsAt_R3AW`）；
4. 经 `e₁.symm`、`e₂.symm` 拉回源坐标得弧对 `(c m, d m) = (e₁.symm ∘ Γ' m, e₂.symm ∘ Γ' m)`，
   覆盖（含配对 sheet 侧的 `w'`）与横截性（`dw ≠ 0` ⇒ `Surjective coprod`，`fderiv_height_diff_eq_zero_F4A`）。
输出与 `transverse_collision_arcs_F4A` 同形，直接喂 `ballify_F4A`。

* `posDef_quad_F4A` / `posDef_symm_F4A`：`Matrix.PosDef` ⇒ 椭圆二次型 / 对称。
* `nodal_shape_align_reg_F4A`：`nodal_shape_align_FIX2` 加上 `V ⊆ O` 与 regular zeros 条款。
* `fderiv_fderiv_symm_F4A` / `injective_fderiv_symm_F4A`。
* **`tangent_collision_arcs_F4A`**。
-/

set_option autoImplicit false
noncomputable section
open Set Filter Metric Manifold
open scoped Topology ContDiff Manifold

namespace DifferentialGeometry.Geometry

theorem posDef_quad_F4A {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.PosDef) (ξ : Fin 2 → ℝ)
    (hξ : ξ ≠ 0) : 0 < ∑ i, ∑ j, A i j * ξ i * ξ j := by
  have h := hA.dotProduct_mulVec_pos hξ
  simp only [dotProduct, Matrix.mulVec, star_trivial, Fin.sum_univ_two] at h ⊢
  linarith

theorem posDef_symm_F4A {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.PosDef) (i j : Fin 2) :
    A i j = A j i := by
  have := hA.isHermitian
  have h2 := congrFun (congrFun this j) i
  simpa [Matrix.conjTranspose_apply] using h2

open DifferentialGeometry.Analysis in
theorem nodal_shape_align_reg_F4A {O : Set ℂ} {a : Fin 2 → Fin 2 → ℂ → ℝ} {w : ℂ → ℝ} {p : ℂ}
    (h : DifferentialGeometry.Analysis.IsNodalHalfArcsAt_F4A O a w p) :
    ∃ (V : Set ℂ) (ρ : ℝ) (k : ℕ) (Γ : Fin (2 * k) → ℝ → ℂ) (v : Fin (2 * k) → ℂ),
      IsOpen V ∧ p ∈ V ∧ V ⊆ O ∧ 0 < ρ ∧ 1 ≤ k ∧
      (∀ m, Γ m 0 = p ∧ ContDiffOn ℝ 1 (Γ m) (Icc 0 ρ) ∧ InjOn (Γ m) (Icc 0 ρ) ∧ v m ≠ 0 ∧
        HasDerivWithinAt (Γ m) (v m) (Icc 0 ρ) 0 ∧ MapsTo (Γ m) (Ico 0 ρ) V) ∧
      (∀ m m', m ≠ m' → ¬ SameRay ℝ (v m) (v m') ∧
        ∀ r ∈ Icc 0 ρ, ∀ r' ∈ Icc 0 ρ, Γ m r = Γ m' r' → r = 0 ∧ r' = 0) ∧
      (∀ z ∈ V, w z = 0 ↔ ∃ m, ∃ r ∈ Ico 0 ρ, z = Γ m r) ∧
      (∀ z ∈ V, w z = 0 → z ≠ p → fderiv ℝ w z ≠ 0) ∧
      (∀ m, ContDiffOn ℝ ∞ (Γ m) (Icc 0 ρ)) := by
  obtain ⟨k, hk, -, -, V, T, lam, θ₀, ρ, Γ, hVo, hpV, hVO, -, hρ, -, harc, hpair, hcover, hreg,
    hsm⟩ := h
  refine ⟨V, ρ, k, Γ, fun m => T (Complex.exp (((θ₀ + ((m : ℕ) : ℝ) * Real.pi / k : ℝ) : ℂ) *
    Complex.I)), hVo, hpV, hVO, hρ, hk, ?_, ?_, hcover, hreg, hsm⟩
  · intro m
    obtain ⟨h0, hc, hi, -, hd, hm⟩ := harc m
    refine ⟨h0, hc, hi, ?_, hd, hm⟩
    intro h0'
    have h0'' : T (Complex.exp (((θ₀ + ((m : ℕ) : ℝ) * Real.pi / k : ℝ) : ℂ) * Complex.I)) =
        0 := h0'
    exact Complex.exp_ne_zero _ (T.injective (h0''.trans (map_zero T).symm))
  · intro m m' hmm'
    refine ⟨?_, hpair m m' hmm'⟩
    intro hsr
    have hne : ∀ x : ℝ, T (Complex.exp ((x : ℂ) * Complex.I)) ≠ 0 := fun x h0 =>
      Complex.exp_ne_zero _ (T.injective (by rw [h0, map_zero]))
    obtain ⟨r₁, r₂, hr₁, hr₂, he⟩ := hsr.exists_pos (hne _) (hne _)
    rw [← map_smul, ← map_smul] at he
    have he' := T.injective he
    have hn := congrArg norm he'
    rw [norm_smul, norm_smul, Complex.norm_exp_ofReal_mul_I, Complex.norm_exp_ofReal_mul_I,
      mul_one, mul_one, Real.norm_of_nonneg hr₁.le, Real.norm_of_nonneg hr₂.le] at hn
    subst hn
    have he'' : Complex.exp (((θ₀ + ((m : ℕ) : ℝ) * Real.pi / k : ℝ) : ℂ) * Complex.I) =
        Complex.exp (((θ₀ + ((m' : ℕ) : ℝ) * Real.pi / k : ℝ) : ℂ) * Complex.I) :=
      smul_right_injective ℂ hr₁.ne' he'
    rw [mul_comm _ Complex.I, mul_comm _ Complex.I] at he''
    have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
    have hmlt : ((m : ℕ) : ℝ) < 2 * k := by exact_mod_cast m.isLt
    have hm'lt : ((m' : ℕ) : ℝ) < 2 * k := by exact_mod_cast m'.isLt
    have hm0 : (0 : ℝ) ≤ ((m : ℕ) : ℝ) := Nat.cast_nonneg _
    have hm'0 : (0 : ℝ) ≤ ((m' : ℕ) : ℝ) := Nat.cast_nonneg _
    have hd : |((m : ℕ) : ℝ) - ((m' : ℕ) : ℝ)| < 2 * k := by
      rw [abs_lt]
      constructor <;> linarith
    have h1 : (θ₀ + ((m : ℕ) : ℝ) * Real.pi / k) - (θ₀ + ((m' : ℕ) : ℝ) * Real.pi / k) =
        (((m : ℕ) : ℝ) - ((m' : ℕ) : ℝ)) * (Real.pi / k) := by ring
    have hxy : |(θ₀ + ((m : ℕ) : ℝ) * Real.pi / k) - (θ₀ + ((m' : ℕ) : ℝ) * Real.pi / k)| <
        2 * Real.pi := by
      rw [h1, abs_mul, abs_of_pos (div_pos Real.pi_pos hkpos)]
      calc |((m : ℕ) : ℝ) - ((m' : ℕ) : ℝ)| * (Real.pi / k) < 2 * k * (Real.pi / k) :=
            mul_lt_mul_of_pos_right hd (div_pos Real.pi_pos hkpos)
        _ = 2 * Real.pi := by field_simp
    have hx := exp_I_inj_FIX2 he'' hxy
    have hx2 : ((m : ℕ) : ℝ) * (Real.pi / k) = ((m' : ℕ) : ℝ) * (Real.pi / k) := by
      have : θ₀ + ((m : ℕ) : ℝ) * (Real.pi / k) = θ₀ + ((m' : ℕ) : ℝ) * (Real.pi / k) := by
        rw [← mul_div_assoc, ← mul_div_assoc]
        exact hx
      linarith
    have hx3 := mul_right_cancel₀ (div_pos Real.pi_pos hkpos).ne' hx2
    exact hmm' (Fin.ext (by exact_mod_cast hx3))

theorem fderiv_fderiv_symm_F4A {e : OpenPartialHomeomorph ℂ ℂ}
    (hei : ContDiffOn ℝ ∞ e.symm e.target) {y : ℂ} (hy : y ∈ e.target)
    (hdiff : DifferentiableAt ℝ e (e.symm y)) (v : ℂ) :
    fderiv ℝ e (e.symm y) (fderiv ℝ e.symm y v) = v := by
  have hdiff' : DifferentiableAt ℝ e.symm y :=
    (hei.contDiffAt (e.open_target.mem_nhds hy)).differentiableAt (by simp)
  have h2 : ∀ᶠ x in 𝓝 y, e (e.symm x) = x := by
    filter_upwards [e.open_target.mem_nhds hy] with x hx using e.right_inv hx
  have hc : HasFDerivAt (e ∘ e.symm)
      ((fderiv ℝ e (e.symm y)).comp (fderiv ℝ e.symm y)) y :=
    HasFDerivAt.comp y hdiff.hasFDerivAt hdiff'.hasFDerivAt
  have hid : HasFDerivAt (e ∘ e.symm) (ContinuousLinearMap.id ℝ ℂ) y :=
    (hasFDerivAt_id y).congr_of_eventuallyEq (by filter_upwards [h2] with x hx using hx)
  exact congrArg (fun L : ℂ →L[ℝ] ℂ => L v) (hc.unique hid)

theorem injective_fderiv_symm_F4A {e : OpenPartialHomeomorph ℂ ℂ}
    (hei : ContDiffOn ℝ ∞ e.symm e.target) {y : ℂ} (hy : y ∈ e.target)
    (hdiff : DifferentiableAt ℝ e (e.symm y)) : Function.Injective (fderiv ℝ e.symm y) := by
  intro v v' h
  have h1 := fderiv_fderiv_symm_F4A hei hy hdiff v
  have h2 := fderiv_fderiv_symm_F4A hei hy hdiff v'
  rw [← h1, ← h2, h]

open DifferentialGeometry.Analysis in
/-- 切向碰撞（非横截）：模型空间里的 `X`，由解析 height difference + R3AW 得到弧对。 -/
theorem tangent_collision_arcs_F4A {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (hd3 : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) E) {X : ℂ → E} {s : Set ℂ} (hs : IsOpen s)
    (hXs : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ X s) (hXa : AnalyticOnNhd ℝ X s)
    (hconf : ∀ z ∈ s, DiskMapConformalAt g X z) (hharm : ∀ z ∈ s, diskMapTension g X z = 0)
    (hrank : ∀ z ∈ s, Function.Injective (fderiv ℝ X z))
    (hncX : ∀ V₁ V₂ : Set ℂ, IsOpen V₁ → IsOpen V₂ → V₁.Nonempty → Disjoint V₁ V₂ → V₁ ⊆ s →
      V₂ ⊆ s → InjOn X V₁ → InjOn X V₂ → ¬ X '' V₁ ⊆ X '' V₂)
    {a b : ℂ} (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b) (hv : X a = X b)
    (hnot : ¬ Function.Surjective ((fderiv ℝ X a).coprod (-(fderiv ℝ X b))))
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
  classical
  have hmf : ∀ z, (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) X z : ℂ →L[ℝ] E) = fderiv ℝ X z := fun z => by
    rw [mfderiv_eq_fderiv]; rfl
  have hXd : ∀ z ∈ s, DifferentiableAt ℝ X z := fun z hz =>
    ((hXs.contMDiffAt (hs.mem_nhds hz)).contDiffAt).differentiableAt (by simp)
  obtain ⟨proj, N, lift, Q, e₁, e₂, O, hNN, hPN, he₁, he₂, hae₁, hbe₂, he₁s, he₂s, hdisj, hei₁,
    hei₂, hOo, haO, hOsub, hrecon, hw, hwan, A, beta, c, hA, hbeta, hc, hpde⟩ :=
    height_difference_model_F4A hd3 g hs hXs hXa hconf hharm ha hb hab hv
      (by rw [hmf]; exact hrank a ha) (by rw [hmf]; exact hrank b hb)
      (by rw [hmf, hmf]; exact hnot)
  set y₀ : ℂ := proj (X a) with hy₀
  let w : ℂ → ℝ := fun y => Q N (X (e₁.symm y) - X a) - Q N (X (e₂.symm y) - X a)
  have hN0 : N ≠ 0 := by
    rintro rfl
    simp at hNN
  have he₁a : e₁ a = y₀ := congrFun he₁ a
  have he₂b : e₂ b = y₀ := by
    have := congrFun he₂ b
    rw [this]
    simp only [Function.comp_apply, ← hv]
    rfl
  have hsa : e₁.symm y₀ = a := by rw [← he₁a]; exact e₁.left_inv hae₁
  have hsb : e₂.symm y₀ = b := by rw [← he₂b]; exact e₂.left_inv hbe₂
  have hwiff : ∀ y ∈ O, X (e₁.symm y) = X (e₂.symm y) ↔ w y = 0 := by
    intro y hy
    obtain ⟨h1, h2⟩ := hrecon y hy
    have e1 : X (e₁.symm y) - X (e₂.symm y) = (w y) • N := by
      calc X (e₁.symm y) - X (e₂.symm y)
          = (X a + lift (y - y₀) + (Q N (X (e₁.symm y) - X a)) • N) -
            (X a + lift (y - y₀) + (Q N (X (e₂.symm y) - X a)) • N) := by rw [← h1, ← h2]
        _ = (w y) • N := by simp only [w]; rw [sub_smul]; abel
    constructor
    · intro h
      rw [h, sub_self] at e1
      exact (smul_eq_zero.mp e1.symm).resolve_right hN0
    · intro h
      rw [h, zero_smul] at e1
      exact sub_eq_zero.mp e1
  have hwz : w y₀ = 0 := by
    simp only [w, hsa, hsb, ← hv, sub_self, map_zero]
  have hnz : ¬ (w =ᶠ[𝓝 y₀] 0) := by
    intro hw0
    obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp (hw0.and (hOo.mem_nhds haO))
    have hw0' : ∀ y ∈ ball y₀ δ, w y = 0 ∧ y ∈ O := fun y hy => hδsub hy
    have hsub₁ : ∀ y ∈ ball y₀ δ, e₁.symm y ∈ e₁.source := fun y hy =>
      e₁.map_target (hOsub (hw0' y hy).2).1
    have hsub₂ : ∀ y ∈ ball y₀ δ, e₂.symm y ∈ e₂.source := fun y hy =>
      e₂.map_target (hOsub (hw0' y hy).2).2
    have hopen₁ : IsOpen (e₁.symm '' ball y₀ δ) :=
      e₁.symm.isOpen_image_of_subset_source isOpen_ball (fun y hy => (hOsub (hw0' y hy).2).1)
    have hopen₂ : IsOpen (e₂.symm '' ball y₀ δ) :=
      e₂.symm.isOpen_image_of_subset_source isOpen_ball (fun y hy => (hOsub (hw0' y hy).2).2)
    have hinj : ∀ (e' : OpenPartialHomeomorph ℂ ℂ), (e' : ℂ → ℂ) = proj ∘ X →
        InjOn X e'.source := by
      intro e' he' z₁ hz₁ z₂ hz₂ h
      apply e'.injOn hz₁ hz₂
      rw [he']
      simp only [Function.comp_apply, h]
    refine hncX (e₁.symm '' ball y₀ δ) (e₂.symm '' ball y₀ δ) hopen₁ hopen₂
      ⟨e₁.symm y₀, y₀, mem_ball_self hδ, rfl⟩ ?_ ?_ ?_ ?_ ?_ ?_
    · refine Set.disjoint_left.mpr ?_
      rintro _ ⟨y, hy, rfl⟩ ⟨y', hy', h⟩
      exact Set.disjoint_left.mp hdisj (hsub₁ y hy) (h ▸ hsub₂ y' hy')
    · rintro _ ⟨y, hy, rfl⟩
      exact he₁s (hsub₁ y hy)
    · rintro _ ⟨y, hy, rfl⟩
      exact he₂s (hsub₂ y hy)
    · exact (hinj e₁ he₁).mono (by rintro _ ⟨y, hy, rfl⟩; exact hsub₁ y hy)
    · exact (hinj e₂ he₂).mono (by rintro _ ⟨y, hy, rfl⟩; exact hsub₂ y hy)
    · rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨e₂.symm y, ⟨y, hy, rfl⟩, ((hwiff y (hw0' y hy).2).mpr (hw0' y hy).1).symm⟩
  -- R3AW
  let a' : Fin 2 → Fin 2 → ℂ → ℝ := fun i j y => (A y i j + A y j i) / 2
  have ha'eq : ∀ y ∈ O, ∀ i j, a' i j y = A y i j := by
    intro y hy i j
    simp only [a']
    rw [← posDef_symm_F4A (hpde y hy).1 i j]
    ring
  have ha' : ∀ i j, ContDiffOn ℝ ∞ (a' i j) O := fun i j =>
    ((hA i j).add (hA j i)).div_const 2
  have hβ' : ∀ i, ContDiffOn ℝ ∞ (fun y => beta y i) O := hbeta
  have hsymm' : ∀ i j y, a' i j y = a' j i y := fun i j y => by simp only [a']; ring
  have hell : ∀ y ∈ O, ∀ ξ : Fin 2 → ℝ, ξ ≠ 0 → 0 < ∑ i, ∑ j, a' i j y * ξ i * ξ j := by
    intro y hy ξ hξ
    simp only [ha'eq y hy]
    exact posDef_quad_F4A (hpde y hy).1 ξ hξ
  have heq : ∀ y ∈ O, ∑ i, ∑ j, a' i j y *
        iteratedFDeriv ℝ 2 w y ![planeBasisR3AW i, planeBasisR3AW j] +
      ∑ i, (fun y => beta y i) y * fderiv ℝ w y (planeBasisR3AW i) + c y * w y = 0 := by
    intro y hy
    simp only [ha'eq y hy, iteratedFDeriv_two_apply]
    exact (hpde y hy).2
  have hR3 := two_sheet_nodal_structure_smooth_F4A hOo ha' hβ' hc hsymm' hell hwan heq haO hwz
    hnz
  obtain ⟨V, ρ, k, Γ', v₀, hVo, hy₀V, hVO, hρ, hk, harc, hpair, hcov, hreg, hsm⟩ :=
    nodal_shape_align_reg_F4A hR3
  set S : ℝ := ρ / 2 with hSdef
  have hSpos : 0 < S := half_pos hρ
  have hSρ : S < ρ := half_lt_self hρ
  have hΓV : ∀ m, ∀ r ∈ Icc 0 S, Γ' m r ∈ V := fun m r hr =>
    (harc m).2.2.2.2.2 ⟨hr.1, hr.2.trans_lt hSρ⟩
  have hdiff₁ : DifferentiableAt ℝ e₁ (e₁.symm y₀) := by
    rw [hsa, he₁]
    exact proj.differentiableAt.comp _ (hXd a ha)
  have hdiff₂ : DifferentiableAt ℝ e₂ (e₂.symm y₀) := by
    rw [hsb, he₂]
    exact proj.differentiableAt.comp _ (hXd b hb)
  have hy₀T₁ : y₀ ∈ e₁.target := hOsub haO |>.1
  have hy₀T₂ : y₀ ∈ e₂.target := hOsub haO |>.2
  have hL₁ := injective_fderiv_symm_F4A hei₁ hy₀T₁ hdiff₁
  have hL₂ := injective_fderiv_symm_F4A hei₂ hy₀T₂ hdiff₂
  have hsd₁ : DifferentiableAt ℝ e₁.symm y₀ :=
    (hei₁.contDiffAt (e₁.open_target.mem_nhds hy₀T₁)).differentiableAt (by simp)
  have hsd₂ : DifferentiableAt ℝ e₂.symm y₀ :=
    (hei₂.contDiffAt (e₂.open_target.mem_nhds hy₀T₂)).differentiableAt (by simp)
  have hmaps₁ : ∀ m, MapsTo (Γ' m) (Icc 0 S) e₁.target := fun m r hr => (hOsub (hVO (hΓV m r hr))).1
  have hmaps₂ : ∀ m, MapsTo (Γ' m) (Icc 0 S) e₂.target := fun m r hr => (hOsub (hVO (hΓV m r hr))).2
  have hΓ0 : ∀ m, Γ' m 0 = y₀ := fun m => (harc m).1
  have : Nonempty (Fin (2 * k)) := ⟨⟨0, by omega⟩⟩
  have hK : ∀ m, ∃ δ > 0, ∀ r ∈ Icc S ρ, Γ' m r ∉ ball y₀ δ := by
    intro m
    have hcompact : IsCompact (Γ' m '' Icc S ρ) := isCompact_Icc.image_of_continuousOn
      ((harc m).2.1.continuousOn.mono (Icc_subset_Icc hSpos.le le_rfl))
    have hy₀notin : y₀ ∉ Γ' m '' Icc S ρ := by
      rintro ⟨r, hr, h⟩
      have := (harc m).2.2.1 ⟨hSpos.le.trans hr.1, hr.2⟩ ⟨le_rfl, hρ.le⟩ (h.trans (hΓ0 m).symm)
      linarith [hr.1]
    obtain ⟨δ, hδ, hδsub⟩ := Metric.isOpen_iff.mp hcompact.isClosed.isOpen_compl y₀ hy₀notin
    exact ⟨δ, hδ, fun r hr h => hδsub h ⟨r, hr, rfl⟩⟩
  choose δm hδm hδmsub using hK
  obtain ⟨δ, hδ0, hδle⟩ := exists_pos_le_finite_F4A δm hδm
  have hnhd₁ : {z' | z' ∈ e₁.source ∧ e₁ z' ∈ V ∩ ball y₀ δ} ∈ 𝓝 a := by
    refine Filter.inter_mem (e₁.open_source.mem_nhds hae₁) ?_
    have hcont : ContinuousAt e₁ a := e₁.continuousAt hae₁
    refine hcont.preimage_mem_nhds ?_
    rw [he₁a]
    exact (hVo.inter isOpen_ball).mem_nhds ⟨hy₀V, mem_ball_self hδ0⟩
  obtain ⟨ε₁, hε₁, hε₁sub⟩ := Metric.mem_nhds_iff.mp hnhd₁
  obtain ⟨ε₂, hε₂, hε₂sub⟩ := Metric.mem_nhds_iff.mp (e₂.open_source.mem_nhds hbe₂)
  set r₂ : ℝ := min r₁ (min ε₁ ε₂) with hr₂def
  have hr₂pos : 0 < r₂ := lt_min hr₁ (lt_min hε₁ hε₂)
  have hr₂₁ : r₂ ≤ r₁ := min_le_left _ _
  have hr₂ε₁ : r₂ ≤ ε₁ := (min_le_right _ _).trans (min_le_left _ _)
  have hr₂ε₂ : r₂ ≤ ε₂ := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨k, r₂, S, fun m s => e₁.symm (Γ' m s), fun m s => e₂.symm (Γ' m s),
    fun m => fderiv ℝ e₁.symm y₀ (v₀ m), fun m => fderiv ℝ e₂.symm y₀ (v₀ m), hk, hr₂pos, hr₂₁,
    hSpos, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro m; simp only [hΓ0, hsa]
  · intro m; simp only [hΓ0, hsb]
  · intro m
    exact (hei₁.of_le (by norm_num)).comp
      ((harc m).2.1.mono (Icc_subset_Icc le_rfl hSρ.le)) (hmaps₁ m)
  · intro m s hs s' hs' h
    have := e₁.symm.injOn (hmaps₁ m hs) (hmaps₁ m hs') h
    exact (harc m).2.2.1 ⟨hs.1, hs.2.trans hSρ.le⟩ ⟨hs'.1, hs'.2.trans hSρ.le⟩ this
  · intro m
    refine ⟨fun h => (harc m).2.2.2.1 (hL₁ (h.trans (map_zero _).symm)), ?_⟩
    have hd : HasDerivWithinAt (Γ' m) (v₀ m) (Icc 0 S) 0 :=
      (harc m).2.2.2.2.1.mono (Icc_subset_Icc le_rfl hSρ.le)
    have hfd : HasFDerivAt e₁.symm (fderiv ℝ e₁.symm y₀) (Γ' m 0) := by
      rw [hΓ0 m]; exact hsd₁.hasFDerivAt
    exact hfd.comp_hasDerivWithinAt 0 hd
  · intro m
    exact (hei₂.of_le (by norm_num)).comp
      ((harc m).2.1.mono (Icc_subset_Icc le_rfl hSρ.le)) (hmaps₂ m)
  · intro m
    refine ⟨fun h => (harc m).2.2.2.1 (hL₂ (h.trans (map_zero _).symm)), ?_⟩
    have hd : HasDerivWithinAt (Γ' m) (v₀ m) (Icc 0 S) 0 :=
      (harc m).2.2.2.2.1.mono (Icc_subset_Icc le_rfl hSρ.le)
    have hfd : HasFDerivAt e₂.symm (fderiv ℝ e₂.symm y₀) (Γ' m 0) := by
      rw [hΓ0 m]; exact hsd₂.hasFDerivAt
    exact hfd.comp_hasDerivWithinAt 0 hd
  · intro m m' hmm'
    obtain ⟨hray, hmeet⟩ := hpair m m' hmm'
    refine ⟨fun h => hray ?_, ?_⟩
    · exact (hL₁.sameRay_map_iff (f := fderiv ℝ e₁.symm y₀)).mp h
    · intro s hs s' hs' h
      have := e₁.symm.injOn (hmaps₁ m hs) (hmaps₁ m' hs') h
      exact hmeet s ⟨hs.1, hs.2.trans hSρ.le⟩ s' ⟨hs'.1, hs'.2.trans hSρ.le⟩ this
  · intro m s hs
    have hsI : s ∈ Icc 0 S := ⟨hs.1, hs.2.le⟩
    have hyV := hΓV m s hsI
    have hw0 : w (Γ' m s) = 0 := (hcov _ hyV).mpr ⟨m, s, ⟨hs.1, hs.2.trans hSρ⟩, rfl⟩
    exact (hwiff _ (hVO hyV)).mpr hw0
  · intro z' hz' w' hw' hXzw
    have hz'1 : z' ∈ {z' | z' ∈ e₁.source ∧ e₁ z' ∈ V ∩ ball y₀ δ} :=
      hε₁sub (ball_subset_ball hr₂ε₁ hz')
    have hw'1 : w' ∈ e₂.source := hε₂sub (ball_subset_ball hr₂ε₂ hw')
    obtain ⟨hz'src, hyV, hyδ⟩ := hz'1
    set y : ℂ := e₁ z' with hy
    have hye₂ : e₂ w' = y := by
      rw [he₂, hy, he₁]
      simp only [Function.comp_apply, hXzw]
    have hz'eq : e₁.symm y = z' := e₁.left_inv hz'src
    have hw'eq : e₂.symm y = w' := by rw [← hye₂]; exact e₂.left_inv hw'1
    have hyO : y ∈ O := hVO hyV
    have hwy : w y = 0 := (hwiff y hyO).mp (by rw [hz'eq, hw'eq]; exact hXzw)
    obtain ⟨m, r, hr, hyr⟩ := (hcov y hyV).mp hwy
    have hrS : r < S := by
      by_contra hge
      push Not at hge
      exact hδmsub m r ⟨hge, hr.2.le⟩ (by
        rw [← hyr]
        exact ball_subset_ball (hδle m) hyδ)
    refine ⟨m, r, ⟨hr.1, hrS⟩, ?_, ?_⟩
    · rw [← hz'eq, hyr]
    · rw [← hw'eq, hyr]
  · intro z' hz' w' hw' hXzw hz'a
    have hz'1 : z' ∈ {z' | z' ∈ e₁.source ∧ e₁ z' ∈ V ∩ ball y₀ δ} :=
      hε₁sub (ball_subset_ball hr₂ε₁ hz')
    have hw'1 : w' ∈ e₂.source := hε₂sub (ball_subset_ball hr₂ε₂ hw')
    obtain ⟨hz'src, hyV, hyδ⟩ := hz'1
    set y : ℂ := e₁ z' with hy
    have hye₂ : e₂ w' = y := by
      rw [he₂, hy, he₁]
      simp only [Function.comp_apply, hXzw]
    have hz'eq : e₁.symm y = z' := e₁.left_inv hz'src
    have hw'eq : e₂.symm y = w' := by rw [← hye₂]; exact e₂.left_inv hw'1
    have hyO : y ∈ O := hVO hyV
    have hwy : w y = 0 := (hwiff y hyO).mp (by rw [hz'eq, hw'eq]; exact hXzw)
    have hyne : y ≠ y₀ := by
      intro h
      apply hz'a
      have : e₁ z' = e₁ a := by rw [← hy, h, he₁a]
      exact e₁.injOn hz'src hae₁ this
    have hdw := hreg y hyV hwy hyne
    by_contra hns
    apply hdw
    rw [← hz'eq, ← hw'eq] at hns
    exact fderiv_height_diff_eq_zero_F4A hd3 hXd hrank hNN hPN he₁ he₁s he₂s hei₁ hei₂ hOo
      (fun y hy => (hOsub hy).1) (fun y hy => (hOsub hy).2) hrecon hyO hns
  · intro m t ht
    exact ⟨he₁s (e₁.map_target (hmaps₁ m ht)), he₂s (e₂.map_target (hmaps₂ m ht))⟩
  · intro m
    exact hei₁.comp ((hsm m).mono (Icc_subset_Icc le_rfl hSρ.le)) (hmaps₁ m)

end DifferentialGeometry.Geometry
