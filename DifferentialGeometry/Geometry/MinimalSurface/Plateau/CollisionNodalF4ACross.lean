import DifferentialGeometry.Analysis.Calculus.Inverse.LocalSubmersion
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# F4-a（`_F4A`）模块 6：横截碰撞的弧（`k = 1`，隐函数）

`X : ℂ → E`（`dim E = 3`）光滑、`X a = X b`、`fderiv X a`、`fderiv X b` 单射、`coprod` 满射（横截）。
用树里的局部拉直 `exists_localProjection_of_hasRightInverse`（`f (z', w') = X z' - X w'` 的 submersion）得
`C^∞` 曲线 `γ(t) = (c t, d t)`，`γ(0) = (a, b)`，`f ∘ γ = 0`，`γ'(0) = (u₁, u₂)` 两个分量都 `≠ 0`。
两条半弧 `c 0 s = c (s)`、`c 1 s = c (-s)`（`k = 1`，方向 `u₁`、`-u₁`）；在 `ball a r₂ × ball b r₂`
里碰撞集恰是曲线，横截性由满射的开性保持。输出正是 `ballify_F4A` 需要的 `(c, d, v, v', hR, hcover, hT)`。

* `exists_injOn_ball_of_injective_fderiv_F4A`：浸入局部单射。
* `eventually_surjective_F4A`：满射在连续族下局部保持。
* **`transverse_collision_arcs_F4A`**。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric
open scoped Topology ContDiff

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- 浸入的局部单射性：`X` 在 `z` 处 `C¹`、`fderiv` 单射 ⇒ 某球上单射。 -/
theorem exists_injOn_ball_of_injective_fderiv_F4A {X : ℂ → E} {z : ℂ}
    (hX : ContDiffAt ℝ 1 X z) (hD : Function.Injective (fderiv ℝ X z)) :
    ∃ r > 0, InjOn X (ball z r) := by
  obtain ⟨Pℓ, hP⟩ := (fderiv ℝ X z).toLinearMap.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr hD)
  let P : E →L[ℝ] ℂ := LinearMap.toContinuousLinearMap Pℓ
  have hPL : P.comp (fderiv ℝ X z) = ContinuousLinearMap.id ℝ ℂ := by
    ext v
    exact congrArg (fun f => f v) hP
  have hg : ContDiffAt ℝ 1 (fun w => P (X w)) z := P.contDiff.contDiffAt.comp z hX
  have hstrict : HasStrictFDerivAt (fun w => P (X w))
      ((ContinuousLinearEquiv.refl ℝ ℂ : ℂ →L[ℝ] ℂ)) z := by
    have h1 := hg.hasStrictFDerivAt (by norm_num)
    have h2 : fderiv ℝ (fun w => P (X w)) z = P.comp (fderiv ℝ X z) :=
      (P.hasFDerivAt.comp z (hX.differentiableAt (by norm_num)).hasFDerivAt).fderiv
    rw [h2, hPL] at h1
    exact h1
  let e := hstrict.toOpenPartialHomeomorph (fun w => P (X w))
  have hze : z ∈ e.source := hstrict.mem_toOpenPartialHomeomorph_source
  obtain ⟨r, hr, hrsub⟩ := Metric.isOpen_iff.mp e.open_source z hze
  refine ⟨r, hr, fun a ha b hb hab => ?_⟩
  have : e a = e b := by
    change P (X a) = P (X b)
    rw [hab]
  exact e.injOn (hrsub ha) (hrsub hb) this

/-- 满射在连续族下局部保持（有限维）。 -/
theorem eventually_surjective_F4A {α V : Type*} [TopologicalSpace α]
    [NormedAddCommGroup V] [NormedSpace ℝ V] {x : α}
    {Pf : α → (V →L[ℝ] E)} (hc : ContinuousAt Pf x) (hs : Function.Surjective (Pf x)) :
    ∀ᶠ y in 𝓝 x, Function.Surjective (Pf y) := by
  obtain ⟨Rℓ, hR⟩ := (Pf x).toLinearMap.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr hs)
  let R₀ : E →L[ℝ] V := LinearMap.toContinuousLinearMap Rℓ
  have hid : (Pf x).comp R₀ = ContinuousLinearMap.id ℝ E := by
    ext v
    exact congrArg (fun f => f v) hR
  have hg : ContinuousAt (fun y => (Pf y).comp R₀) x :=
    (ContinuousLinearMap.compL ℝ E V E).flip R₀ |>.continuous.continuousAt.comp hc
  have hset : {L : E →L[ℝ] E | ∃ D : E ≃L[ℝ] E, (D : E →L[ℝ] E) = L} ∈
      𝓝 ((Pf x).comp R₀) := by
    rw [hid]
    exact (ContinuousLinearEquiv.refl ℝ E).nhds
  filter_upwards [hg hset] with y ⟨D, hD⟩
  intro e
  refine ⟨R₀ (D.symm e), ?_⟩
  have := congrArg (fun L : E →L[ℝ] E => L (D.symm e)) hD
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply] at this
  exact this.symm

open DifferentialGeometry.Analysis in
/-- 横截碰撞：`X a = X b`、`coprod` 满射 ⇒ 碰撞集是过 `(a, b)` 的 `C^∞` 曲线（隐函数），用 `k = 1` 的两条半弧
（`t ≥ 0` 与 `t ≤ 0`）写成 `ballify_F4A` 的输入。 -/
theorem transverse_collision_arcs_F4A (hd3 : Module.finrank ℝ E = 3)
    {X : ℂ → E} {s : Set ℂ} (hs : IsOpen s) (hX : ContDiffOn ℝ ∞ X s)
    {a b : ℂ} (ha : a ∈ s) (hb : b ∈ s) (hv : X a = X b)
    (hDa : Function.Injective (fderiv ℝ X a)) (hDb : Function.Injective (fderiv ℝ X b))
    (htr : Function.Surjective ((fderiv ℝ X a).coprod (-(fderiv ℝ X b))))
    {r₁ : ℝ} (hr₁ : 0 < r₁) :
∃ (r₂ S : ℝ) (c d : Fin (2 * 1) → ℝ → ℂ) (v v' : Fin (2 * 1) → ℂ),
      0 < r₂ ∧ r₂ ≤ r₁ ∧ 0 < S ∧ (∀ m, c m 0 = a) ∧ (∀ m, d m 0 = b) ∧
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
  let P : ℂ × ℂ →L[ℝ] E := (fderiv ℝ X a).coprod (-(fderiv ℝ X b))
  let f : ℂ × ℂ → E := fun p => X p.1 - X p.2
  have hf : ContDiffOn ℝ ∞ f (s ×ˢ s) :=
    (hX.comp contDiff_fst.contDiffOn (fun p hp => hp.1)).sub
      (hX.comp contDiff_snd.contDiffOn (fun p hp => hp.2))
  have hXa : HasFDerivAt X (fderiv ℝ X a) a :=
    ((hX.contDiffAt (hs.mem_nhds ha)).differentiableAt (by norm_num)).hasFDerivAt
  have hXb : HasFDerivAt X (fderiv ℝ X b) b :=
    ((hX.contDiffAt (hs.mem_nhds hb)).differentiableAt (by norm_num)).hasFDerivAt
  have hdf : HasFDerivAt f P (a, b) := by
    have h1 : HasFDerivAt (fun p : ℂ × ℂ => X p.1)
        ((fderiv ℝ X a).comp (ContinuousLinearMap.fst ℝ ℂ ℂ)) (a, b) :=
      hXa.comp (a, b) (hasFDerivAt_fst)
    have h2 : HasFDerivAt (fun p : ℂ × ℂ => X p.2)
        ((fderiv ℝ X b).comp (ContinuousLinearMap.snd ℝ ℂ ℂ)) (a, b) :=
      hXb.comp (a, b) (hasFDerivAt_snd)
    convert h1.sub h2 using 1
    ext p <;> simp [P]
  obtain ⟨ε, hxε, hεU, hεC, hεinv, hε1, hε2⟩ := exists_localProjection_of_hasRightInverse hf
    (hs.prod hs) ⟨ha, hb⟩ hdf
    (ContinuousLinearMap.HasRightInverse.of_surjective_of_finiteDimensional htr)
  have hker : Module.finrank ℝ P.ker = 1 := by
    have h := LinearMap.finrank_range_add_finrank_ker P.toLinearMap
    have hr : LinearMap.range P.toLinearMap = ⊤ := LinearMap.range_eq_top.mpr htr
    rw [hr, finrank_top, hd3, Module.finrank_prod, Complex.finrank_real_complex] at h
    omega
  obtain ⟨κ, hκ0, hκspan⟩ := finrank_eq_one_iff'.mp hker
  -- 局部坐标 `ε`：`(ε p).1 = f p`
  have hεab1 : (ε (a, b)).1 = 0 := by rw [hε1]; simp [f, hv]
  obtain ⟨t₀, ht₀⟩ := hκspan (ε (a, b)).2
  have hεab : ε (a, b) = (0, t₀ • κ) := Prod.ext hεab1 ht₀.symm
  have hεabT : (0, t₀ • κ) ∈ ε.target := hεab ▸ ε.map_source hxε
  -- 曲线
  let γ : ℝ → ℂ × ℂ := fun t => ε.symm (0, (t₀ + t) • κ)
  have hcurve : Continuous fun t : ℝ => ((0 : E), (t₀ + t) • κ) :=
    continuous_const.prodMk ((continuous_const.add continuous_id).smul continuous_const)
  have hT0open : IsOpen {t : ℝ | ((0 : E), (t₀ + t) • κ) ∈ ε.target} :=
    ε.open_target.preimage hcurve
  have h0T0 : (0 : ℝ) ∈ {t : ℝ | ((0 : E), (t₀ + t) • κ) ∈ ε.target} := by
    simpa using hεabT
  have hγ0 : γ 0 = (a, b) := by
    change ε.symm (0, (t₀ + 0) • κ) = (a, b)
    rw [add_zero, ← hεab]
    exact ε.left_inv hxε
  have hγsmooth : ∀ t ∈ {t : ℝ | ((0 : E), (t₀ + t) • κ) ∈ ε.target}, ContDiffAt ℝ ∞ γ t := by
    intro t ht
    have h1 : ContDiffAt ℝ ∞ ε.symm ((0 : E), (t₀ + t) • κ) :=
      hεinv.contDiffAt (ε.open_target.mem_nhds ht)
    exact h1.comp t (contDiffAt_const.prodMk
      ((contDiffAt_const.add contDiffAt_id).smul contDiffAt_const))
  have hfγ : ∀ t ∈ {t : ℝ | ((0 : E), (t₀ + t) • κ) ∈ ε.target},
      X (γ t).1 = X (γ t).2 := by
    intro t ht
    have := hε2 _ ht
    exact sub_eq_zero.mp this
  have hεγ : ∀ t ∈ {t : ℝ | ((0 : E), (t₀ + t) • κ) ∈ ε.target},
      ε (γ t) = (0, (t₀ + t) • κ) := fun t ht => ε.right_inv ht
  -- 速度非零
  have hγd : HasDerivAt γ (deriv γ 0) 0 :=
    ((hγsmooth 0 h0T0).differentiableAt (by simp)).hasDerivAt
  set u : ℂ × ℂ := deriv γ 0 with hu
  have hεd : HasFDerivAt ε (fderiv ℝ ε (a, b)) (a, b) :=
    ((hεC.contDiffAt (ε.open_source.mem_nhds hxε)).differentiableAt (by simp)).hasFDerivAt
  have hεd' : HasFDerivAt ε (fderiv ℝ ε (a, b)) (γ 0) := by rw [hγ0]; exact hεd
  have hcomp : HasDerivAt (fun t => ε (γ t)) (fderiv ℝ ε (a, b) u) 0 :=
    hεd'.comp_hasDerivAt 0 hγd
  have hcomp2 : HasDerivAt (fun t : ℝ => ε (γ t)) ((0 : E), (1 : ℝ) • κ) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => ((0 : E), (t₀ + t) • κ)) ((0 : E), (1 : ℝ) • κ) 0 :=
      (hasDerivAt_const (0 : ℝ) (0 : E)).prodMk
        (((hasDerivAt_id (0 : ℝ)).const_add t₀).smul_const κ)
    refine h1.congr_of_eventuallyEq ?_
    filter_upwards [hT0open.mem_nhds h0T0] with t ht using hεγ t ht
  have huε : fderiv ℝ ε (a, b) u = ((0 : E), (1 : ℝ) • κ) := hcomp.unique hcomp2
  have hu0 : u ≠ 0 := by
    intro h
    rw [h, map_zero] at huε
    have := congrArg Prod.snd huε
    simp only [Prod.snd_zero, one_smul] at this
    exact hκ0 (by simpa using this.symm)
  have hdf' : HasFDerivAt f P (γ 0) := by rw [hγ0]; exact hdf
  have hfcomp : HasDerivAt (fun t => f (γ t)) (P u) 0 := hdf'.comp_hasDerivAt 0 hγd
  have hPu : P u = 0 := by
    have h0 : HasDerivAt (fun t => f (γ t)) 0 0 := by
      refine (hasDerivAt_const (0 : ℝ) (0 : E)).congr_of_eventuallyEq ?_
      filter_upwards [hT0open.mem_nhds h0T0] with t ht
      exact sub_eq_zero.mpr (hfγ t ht)
    exact hfcomp.unique h0
  have hPu' : fderiv ℝ X a u.1 = fderiv ℝ X b u.2 := by
    have : P u = fderiv ℝ X a u.1 + (-(fderiv ℝ X b)) u.2 := by
      simp only [P, ContinuousLinearMap.coprod_apply]
    rw [this, neg_apply, ← sub_eq_add_neg, sub_eq_zero] at hPu
    exact hPu
  have hu1 : u.1 ≠ 0 := by
    intro h1
    rw [h1, map_zero] at hPu'
    have : u.2 = 0 := hDb (by rw [map_zero]; exact hPu'.symm)
    exact hu0 (Prod.ext h1 this)
  have hu2 : u.2 ≠ 0 := by
    intro h2
    rw [h2, map_zero] at hPu'
    have : u.1 = 0 := hDa (by rw [map_zero]; exact hPu')
    exact hu0 (Prod.ext this h2)
  -- 取 `S`
  obtain ⟨rb, hrb, hinjb⟩ := exists_injOn_ball_of_injective_fderiv_F4A
    ((hX.contDiffAt (hs.mem_nhds hb)).of_le (by norm_num)) hDb
  have hγcont : ContinuousAt γ 0 := (hγsmooth 0 h0T0).continuousAt
  have hnbhd : {t : ℝ | ((0 : E), (t₀ + t) • κ) ∈ ε.target ∧ (γ t).2 ∈ ball b rb} ∈ 𝓝 (0 : ℝ) := by
    refine Filter.inter_mem (hT0open.mem_nhds h0T0) ?_
    have hc2 : ContinuousAt (fun t => (γ t).2) 0 := continuous_snd.continuousAt.comp hγcont
    have hball : ball b rb ∈ 𝓝 ((γ 0).2) := by
      rw [hγ0]
      exact ball_mem_nhds b hrb
    exact hc2.preimage_mem_nhds hball
  obtain ⟨S₀, hS₀, hS₀sub⟩ := Metric.mem_nhds_iff.mp hnbhd
  set S : ℝ := S₀ / 2 with hSdef
  have hSpos : 0 < S := half_pos hS₀
  have hIS : ∀ t ∈ Icc (-S) S, ((0 : E), (t₀ + t) • κ) ∈ ε.target ∧ (γ t).2 ∈ ball b rb := by
    intro t ht
    apply hS₀sub
    rw [mem_ball, Real.dist_eq, sub_zero]
    exact lt_of_le_of_lt (abs_le.mpr ht) (by linarith)
  have hγinj : ∀ t ∈ Icc (-S) S, ∀ t' ∈ Icc (-S) S, (γ t).1 = (γ t').1 → t = t' := by
    intro t ht t' ht' h
    have e1 := hfγ t (hIS t ht).1
    have e2 := hfγ t' (hIS t' ht').1
    have h2 : (γ t).2 = (γ t').2 := by
      apply hinjb (hIS t ht).2 (hIS t' ht').2
      rw [← e1, ← e2, h]
    have hγeq : γ t = γ t' := Prod.ext h h2
    have := congrArg ε hγeq
    rw [hεγ t (hIS t ht).1, hεγ t' (hIS t' ht').1] at this
    have h3 := congrArg Prod.snd this
    simp only at h3
    have h4 : (t - t') • κ = 0 := by
      rw [sub_smul]
      have : (t₀ + t) • κ = (t₀ + t') • κ := h3
      rw [add_smul, add_smul] at this
      exact sub_eq_zero.mpr (add_left_cancel this)
    rcases smul_eq_zero.mp h4 with h5 | h5
    · linarith
    · exact absurd h5 hκ0
  -- 两条半弧
  let sg : Fin (2 * 1) → ℝ := fun m => if (m : ℕ) = 0 then 1 else -1
  have hsgne : ∀ m, sg m ≠ 0 := fun m => by simp only [sg]; split_ifs <;> norm_num
  have hsgIcc : ∀ m, ∀ s ∈ Icc 0 S, sg m * s ∈ Icc (-S) S := by
    intro m s hs
    simp only [sg]
    split_ifs
    · rw [one_mul]; exact ⟨by linarith [hs.1], hs.2⟩
    · rw [neg_one_mul]; exact ⟨by linarith [hs.2], by linarith [hs.1]⟩
  have hgamC : ∀ m, ∀ s ∈ Icc 0 S, ContDiffAt ℝ ∞ (fun s => γ (sg m * s)) s := fun m s hs =>
    (hγsmooth _ (hIS _ (hsgIcc m s hs)).1).comp s (contDiffAt_const.mul contDiffAt_id)
  have hderiv : ∀ m, HasDerivAt (fun s : ℝ => γ (sg m * s)) (sg m • u) 0 := by
    intro m
    have hh : HasDerivAt (fun s : ℝ => sg m * s) (sg m) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_mul (sg m)
    have hg : HasDerivAt γ u (sg m * 0) := by rw [mul_zero]; exact hγd
    exact hg.scomp (0 : ℝ) hh
  have hderiv1 : ∀ m, HasDerivAt (fun s : ℝ => (γ (sg m * s)).1) (sg m • u.1) 0 := by
    intro m
    have := (hasFDerivAt_fst (𝕜 := ℝ) (p := (γ (sg m * 0)))).comp_hasDerivAt (0 : ℝ) (hderiv m)
    exact this
  have hderiv2 : ∀ m, HasDerivAt (fun s : ℝ => (γ (sg m * s)).2) (sg m • u.2) 0 := by
    intro m
    have := (hasFDerivAt_snd (𝕜 := ℝ) (p := (γ (sg m * 0)))).comp_hasDerivAt (0 : ℝ) (hderiv m)
    exact this
  -- 选 `r₂`
  have hκn : 0 < ‖κ‖ := norm_pos_iff.mpr hκ0
  obtain ⟨δ₁, hδ₁, hδ₁sub⟩ := Metric.isOpen_iff.mp ε.open_source (a, b) hxε
  obtain ⟨δ₂, hδ₂, hδ₂h⟩ := Metric.continuousAt_iff.mp (ε.continuousAt hxε) (S * ‖κ‖)
    (mul_pos hSpos hκn)
  have hfdX : ContinuousOn (fderiv ℝ X) s := hX.continuousOn_fderiv_of_isOpen hs (by norm_num)
  have hPf : ContinuousAt (fun p : ℂ × ℂ => (fderiv ℝ X p.1).coprod (-(fderiv ℝ X p.2)))
      (a, b) := by
    have h1 : ContinuousAt (fun p : ℂ × ℂ => fderiv ℝ X p.1) (a, b) :=
      (hfdX.continuousAt (hs.mem_nhds ha)).comp (f := fun p : ℂ × ℂ => p.1)
        continuous_fst.continuousAt
    have h2 : ContinuousAt (fun p : ℂ × ℂ => fderiv ℝ X p.2) (a, b) :=
      (hfdX.continuousAt (hs.mem_nhds hb)).comp (f := fun p : ℂ × ℂ => p.2)
        continuous_snd.continuousAt
    have hcp : ∀ p : ℂ × ℂ, (fderiv ℝ X p.1).coprod (-(fderiv ℝ X p.2)) =
        (fderiv ℝ X p.1).comp (ContinuousLinearMap.fst ℝ ℂ ℂ) +
          (-(fderiv ℝ X p.2)).comp (ContinuousLinearMap.snd ℝ ℂ ℂ) := fun p =>
      ContinuousLinearMap.ext fun q => by simp
    simp_rw [hcp]
    have hA : Continuous fun L : ℂ →L[ℝ] E => L.comp (ContinuousLinearMap.fst ℝ ℂ ℂ) :=
      ((ContinuousLinearMap.compL ℝ (ℂ × ℂ) ℂ E).flip
        (ContinuousLinearMap.fst ℝ ℂ ℂ)).continuous
    have hB : Continuous fun L : ℂ →L[ℝ] E => L.comp (ContinuousLinearMap.snd ℝ ℂ ℂ) :=
      ((ContinuousLinearMap.compL ℝ (ℂ × ℂ) ℂ E).flip
        (ContinuousLinearMap.snd ℝ ℂ ℂ)).continuous
    exact (hA.continuousAt.comp h1).add ((hB.continuousAt.comp (h2.neg)))
  have hsurj := eventually_surjective_F4A hPf htr
  obtain ⟨δ₃, hδ₃, hδ₃h⟩ := Metric.eventually_nhds_iff.mp hsurj
  set r₂ : ℝ := min r₁ (min δ₁ (min δ₂ δ₃)) with hr₂def
  have hr₂pos : 0 < r₂ := lt_min hr₁ (lt_min hδ₁ (lt_min hδ₂ hδ₃))
  have hr₂₁ : r₂ ≤ r₁ := min_le_left _ _
  have hr₂δ₁ : r₂ ≤ δ₁ := (min_le_right _ _).trans (min_le_left _ _)
  have hr₂δ₂ : r₂ ≤ δ₂ := ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hr₂δ₃ : r₂ ≤ δ₃ := ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)
  have hdist : ∀ z' ∈ ball a r₂, ∀ w' ∈ ball b r₂, dist (z', w') (a, b) < r₂ := by
    intro z' hz' w' hw'
    rw [Prod.dist_eq]
    exact max_lt hz' hw'
  have hsg0 : sg 0 = 1 := by simp [sg]
  have hsg1 : sg 1 = -1 := by simp [sg]
  have hsgneg : ∀ m m' : Fin (2 * 1), m ≠ m' → sg m = - sg m' := by
    intro m m' hmm'
    have hm : ∀ m : Fin (2 * 1), m = 0 ∨ m = 1 := by
      intro m
      fin_cases m <;> simp
    rcases hm m with rfl | rfl <;> rcases hm m' with rfl | rfl
    · exact absurd rfl hmm'
    · simp [hsg0, hsg1]
    · simp [hsg0, hsg1]
    · exact absurd rfl hmm'
  refine ⟨r₂, S, fun m s => (γ (sg m * s)).1, fun m s => (γ (sg m * s)).2,
    fun m => sg m • u.1, fun m => sg m • u.2, hr₂pos, hr₂₁, hSpos, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro m
    simp [hγ0]
  · intro m
    simp [hγ0]
  · intro m s hs
    exact ((contDiffAt_fst (𝕜 := ℝ)).comp s (hgamC m s hs)).of_le (by norm_num)
      |>.contDiffWithinAt
  · intro m s hs s' hs' h
    have := hγinj _ (hsgIcc m s hs) _ (hsgIcc m s' hs') h
    exact mul_left_cancel₀ (hsgne m) this
  · intro m
    exact ⟨smul_ne_zero (hsgne m) hu1, (hderiv1 m).hasDerivWithinAt⟩
  · intro m s hs
    exact ((contDiffAt_snd (𝕜 := ℝ)).comp s (hgamC m s hs)).of_le (by norm_num)
      |>.contDiffWithinAt
  · intro m
    exact ⟨smul_ne_zero (hsgne m) hu2, (hderiv2 m).hasDerivWithinAt⟩
  · intro m m' hmm'
    have hneg := hsgneg m m' hmm'
    refine ⟨?_, ?_⟩
    · intro hsr
      have hw : sg m • u.1 ≠ 0 := smul_ne_zero (hsgne m) hu1
      have hw' : sg m' • u.1 ≠ 0 := smul_ne_zero (hsgne m') hu1
      obtain ⟨r₁', r₂', hr₁', hr₂', hr⟩ := hsr.exists_pos hw hw'
      have hsm : sg m • u.1 = -(sg m' • u.1) := by rw [hneg, neg_smul]
      have hr' : (r₁' + r₂') • (sg m' • u.1) = 0 := by
        have hr2 : r₁' • (sg m • u.1) = r₂' • (sg m' • u.1) := hr
        rw [hsm, smul_neg] at hr2
        rw [add_smul, ← hr2]
        exact add_neg_cancel _
      rcases smul_eq_zero.mp hr' with h | h
      · linarith
      · exact hw' h
    · intro s hs s' hs' h
      have := hγinj _ (hsgIcc m s hs) _ (hsgIcc m' s' hs') h
      rw [hneg] at this
      have h1 : sg m' * (s + s') = 0 := by linarith
      rcases mul_eq_zero.mp h1 with h2 | h2
      · exact absurd h2 (hsgne m')
      · constructor <;> linarith [hs.1, hs'.1]
  · intro m s hs
    exact hfγ _ (hIS _ (hsgIcc m s ⟨hs.1, hs.2.le⟩)).1
  · intro z' hz' w' hw' hXzw
    have hp : (z', w') ∈ ε.source := hδ₁sub (by
      rw [Metric.mem_ball]; exact (hdist z' hz' w' hw').trans_le hr₂δ₁)
    have hf0 : (ε (z', w')).1 = 0 := by rw [hε1]; simp [f, hXzw]
    obtain ⟨τ, hτ⟩ := hκspan (ε (z', w')).2
    have hεp : ε (z', w') = (0, τ • κ) := Prod.ext hf0 hτ.symm
    have hdy : dist (ε (z', w')) (ε (a, b)) < S * ‖κ‖ :=
      hδ₂h ((hdist z' hz' w' hw').trans_le hr₂δ₂)
    have hd2 : |τ - t₀| * ‖κ‖ < S * ‖κ‖ := by
      have h1 : dist (ε (z', w')).2 (ε (a, b)).2 ≤ dist (ε (z', w')) (ε (a, b)) := by
        rw [Prod.dist_eq]; exact le_max_right _ _
      have h2 : dist (ε (z', w')).2 (ε (a, b)).2 = |τ - t₀| * ‖κ‖ := by
        rw [← hτ, ← ht₀, dist_eq_norm, ← sub_smul, norm_smul, Real.norm_eq_abs]
      linarith
    have hτS : |τ - t₀| < S := lt_of_mul_lt_mul_right hd2 hκn.le
    have hmemT : ((0 : E), (t₀ + (τ - t₀)) • κ) ∈ ε.target := by
      rw [show t₀ + (τ - t₀) = τ by ring, ← hεp]
      exact ε.map_source hp
    have hγt : γ (τ - t₀) = (z', w') := by
      change ε.symm ((0 : E), (t₀ + (τ - t₀)) • κ) = (z', w')
      rw [show t₀ + (τ - t₀) = τ by ring, ← hεp]
      exact ε.left_inv hp
    by_cases ht : 0 ≤ τ - t₀
    · refine ⟨0, τ - t₀, ⟨ht, ?_⟩, ?_, ?_⟩
      · have := (abs_lt.mp hτS).2; linarith
      · simp only [hsg0, one_mul, hγt]
      · simp only [hsg0, one_mul, hγt]
    · push Not at ht
      refine ⟨1, -(τ - t₀), ⟨by linarith, ?_⟩, ?_, ?_⟩
      · have := (abs_lt.mp hτS).1; linarith
      · simp only [hsg1, neg_mul, one_mul, neg_neg, hγt]
      · simp only [hsg1, neg_mul, one_mul, neg_neg, hγt]
  · intro z' hz' w' hw' hXzw hz'a
    exact hδ₃h ((hdist z' hz' w' hw').trans_le hr₂δ₃)
  · intro m t ht
    have hmem : γ (sg m * t) ∈ ε.source := ε.map_target (hIS _ (hsgIcc m t ht)).1
    exact ⟨(hεU hmem).1, (hεU hmem).2⟩
  · intro m s hs
    exact ((contDiffAt_fst (𝕜 := ℝ)).comp s (hgamC m s hs)).contDiffWithinAt

end DifferentialGeometry.Geometry
