import DifferentialGeometry.Analysis.Calculus.Inverse.LocalDiffeomorphStraightening
import DifferentialGeometry.Analysis.Calculus.Inverse.IntervalInverseDerivative

open Set Filter
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Topology

private theorem exists_diffeomorph_realizing_scalar_germ
    {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hd : deriv f 0 ≠ 0) :
    ∃ D : ℝ ≃ₘ[ℝ] ℝ, (D : ℝ → ℝ) =ᶠ[𝓝 0] f := by
  let A := ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 (deriv f 0) hd)
  have hA : HasFDerivAt f (A : ℝ →L[ℝ] ℝ) 0 := by
    have h : (A : ℝ →L[ℝ] ℝ) = ContinuousLinearMap.toSpanSingleton ℝ (deriv f 0) := rfl
    rw [h]
    exact ((hf.differentiable (by simp)) 0).hasDerivAt.hasFDerivAt
  obtain ⟨J, hJ, _⟩ :=
    DifferentialGeometry.Analysis.exists_compact_diffeomorph_realizing_germ_up_to_derivative
    isOpen_univ (mem_univ 0) hf.contDiffOn A hA isOpen_univ (mem_univ (f 0))
  let D := (A.toDiffeomorph.trans (translateDiffeomorph (f 0))).trans J
  exact ⟨D, hJ⟩

private theorem contDiff_glue_curves_of_germ
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f g : ℝ → F} {a : ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (heq : f =ᶠ[𝓝 a] g) :
    ContDiff ℝ ∞ (fun t => if t < a then f t else g t) := by
  apply contDiff_iff_contDiffAt.mpr
  intro t
  rcases lt_trichotomy t a with ht | rfl | ht
  · apply hf.contDiffAt.congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds ht] with u hu
    change u < a at hu
    simp only [if_pos hu]
  · apply hg.contDiffAt.congr_of_eventuallyEq
    filter_upwards [heq] with u hu
    split_ifs <;> first | assumption | rfl
  · apply hg.contDiffAt.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds ht] with u hu
    change a < u at hu
    simp only [if_neg (not_lt.mpr hu.le)]

private theorem exists_contDiff_curve_attaching_ends
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f α₀ α₁ : ℝ → F} (hf : ContDiff ℝ ∞ f)
    (hα₀ : ContDiff ℝ ∞ α₀) (hα₁ : ContDiff ℝ ∞ α₁)
    (D₀ D₁ : ℝ ≃ₘ[ℝ] ℝ)
    (h₀ : (fun t => α₀ (D₀ t)) =ᶠ[𝓝 0] f)
    (h₁ : (fun t => α₁ (D₁ t)) =ᶠ[𝓝 1] f) :
    ∃ g : ℝ → F, ContDiff ℝ ∞ g ∧
      (∀ t ≤ 0, g t = α₀ (D₀ t)) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, g t = f t) ∧
      (∀ t ≥ 1, g t = α₁ (D₁ t)) ∧
      g =ᶠ[𝓝 0] (fun t => α₀ (D₀ t)) ∧
      g =ᶠ[𝓝 1] (fun t => α₁ (D₁ t)) := by
  let l : ℝ → F := fun t => if t < 0 then α₀ (D₀ t) else f t
  have hl : ContDiff ℝ ∞ l := contDiff_glue_curves_of_germ
    (hα₀.comp D₀.contMDiff.contDiff) hf h₀
  have hl₁ : l =ᶠ[𝓝 (1 : ℝ)] f := by
    filter_upwards [Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1)] with t ht
    change 0 < t at ht
    simp only [l, if_neg (not_lt.mpr ht.le)]
  let g : ℝ → F := fun t => if t < 1 then l t else α₁ (D₁ t)
  have hg : ContDiff ℝ ∞ g := contDiff_glue_curves_of_germ hl
    (hα₁.comp D₁.contMDiff.contDiff) (hl₁.trans h₁.symm)
  refine ⟨g, hg, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    have ht1 : t < 1 := lt_of_le_of_lt ht (by norm_num)
    dsimp only [g, l]
    rw [if_pos ht1]
    rcases ht.eq_or_lt with rfl | ht
    · rw [if_neg (lt_irrefl 0)]
      exact h₀.self_of_nhds.symm
    · rw [if_pos ht]
  · intro t ht
    dsimp only [g, l]
    rw [if_neg (not_lt.mpr ht.1)]
    split_ifs with ht1
    · rfl
    · have ht' : t = 1 := le_antisymm ht.2 (not_lt.mp ht1)
      subst t
      exact h₁.self_of_nhds
  · intro t ht
    exact if_neg (not_lt.mpr ht)
  · filter_upwards [Iio_mem_nhds (by norm_num : (0 : ℝ) < 1), h₀] with t ht he
    change t < 1 at ht
    dsimp only [g, l]
    rw [if_pos ht]
    split_ifs <;> first | rfl | exact he.symm
  · filter_upwards [hl₁, h₁] with t hl hf
    dsimp only [g]
    split_ifs <;> first | rfl | exact hl.trans hf.symm

private theorem deriv_ne_zero_of_regular_curve_coordinate
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f α : ℝ → F} {R : F → ℝ} {a : ℝ}
    (hf : ContDiff ℝ ∞ f) (hα : ContDiff ℝ ∞ α) (hR : ContDiff ℝ ∞ R)
    (hdf : deriv f a ≠ 0) (hcoord : f =ᶠ[𝓝 a] fun t => α (R (f t))) :
    deriv (fun t => R (f t)) a ≠ 0 := by
  intro hzero
  have hread : ContDiff ℝ ∞ (fun t => R (f t)) := hR.comp hf
  have hd := ((hα.differentiable (by simp)) (R (f a))).hasFDerivAt.comp_hasDerivAt a
    ((hread.differentiable (by simp)) a).hasDerivAt
  have hcomp : deriv (fun t => α (R (f t))) a = 0 := by
    change deriv (α ∘ fun t => R (f t)) a = 0
    rw [hd.deriv, hzero, map_zero]
  exact hdf (hcoord.deriv_eq.trans hcomp)

private theorem strictMono_diffeomorph_of_arc_attachment
    {F : Type*} {f α : ℝ → F} {a b : ℝ} (hab : a < b)
    (D : ℝ ≃ₘ[ℝ] ℝ) (hD₀ : D 0 = b)
    (hgerm : (fun t => α (D t)) =ᶠ[𝓝 0] f)
    (hmeet : ∀ v ∈ Icc a b, ∀ t ∈ Icc (0 : ℝ) 1, α v = f t → t = 0) :
    StrictMono D := by
  rcases D.continuous.strictMono_of_inj D.injective with hm | hm
  · exact hm
  · have hDa : a < D 0 := hD₀ ▸ hab
    have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ),
        t < 1 ∧ a < D t ∧ α (D t) = f t := by
      filter_upwards [((show ∀ᶠ t in 𝓝 (0 : ℝ), t < 1 from
        Iio_mem_nhds (by norm_num)).filter_mono inf_le_left),
        ((D.continuous.continuousAt.eventually (Ioi_mem_nhds hDa)).filter_mono inf_le_left),
        hgerm.filter_mono inf_le_left] with t ht hDt heq
      exact ⟨ht, hDt, heq⟩
    obtain ⟨t, ⟨ht1, hDt, heq⟩, ht0⟩ := (hev.and self_mem_nhdsWithin).exists
    change 0 < t at ht0
    have hDb : D t < b := hD₀ ▸ hm ht0
    have ht := hmeet (D t) ⟨hDt.le, hDb.le⟩ t ⟨ht0.le, ht1.le⟩ heq
    exact (ht0.ne' ht).elim

private theorem strictAnti_diffeomorph_of_arc_attachment
    {F : Type*} {f α : ℝ → F} {a b : ℝ} (hab : a < b)
    (D : ℝ ≃ₘ[ℝ] ℝ) (hD₁ : D 1 = b)
    (hgerm : (fun t => α (D t)) =ᶠ[𝓝 1] f)
    (hmeet : ∀ v ∈ Icc a b, ∀ t ∈ Icc (0 : ℝ) 1, α v = f t → t = 1) :
    StrictAnti D := by
  rcases D.continuous.strictMono_of_inj D.injective with hm | hm
  · have hDa : a < D 1 := hD₁ ▸ hab
    have hev : ∀ᶠ t in 𝓝[<] (1 : ℝ),
        0 < t ∧ a < D t ∧ α (D t) = f t := by
      filter_upwards [((show ∀ᶠ t in 𝓝 (1 : ℝ), 0 < t from
        Ioi_mem_nhds (by norm_num)).filter_mono inf_le_left),
        ((D.continuous.continuousAt.eventually (Ioi_mem_nhds hDa)).filter_mono inf_le_left),
        hgerm.filter_mono inf_le_left] with t ht hDt heq
      exact ⟨ht, hDt, heq⟩
    obtain ⟨t, ⟨ht0, hDt, heq⟩, ht1⟩ := (hev.and self_mem_nhdsWithin).exists
    change t < 1 at ht1
    have hDb : D t < b := hD₁ ▸ hm ht1
    have ht := hmeet (D t) ⟨hDt.le, hDb.le⟩ t ⟨ht0.le, ht1.le⟩ heq
    exact (ht1.ne ht).elim
  · exact hm

private theorem deriv_ne_zero_of_smooth_left_inverse
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {α : ℝ → F} {R : F → ℝ} (hα : ContDiff ℝ ∞ α) (hR : ContDiff ℝ ∞ R)
    (hleft : Function.LeftInverse R α) (t : ℝ) : deriv α t ≠ 0 := by
  intro hzero
  have hd := ((hR.differentiable (by simp)) (α t)).hasFDerivAt.comp_hasDerivAt t
    ((hα.differentiable (by simp)) t).hasDerivAt
  have hid : HasDerivAt (R ∘ α) 1 t := by
    have he : R ∘ α = id := funext hleft
    rw [he]
    exact hasDerivAt_id t
  have he := hd.unique hid
  rw [hzero, map_zero] at he
  exact zero_ne_one he

theorem exists_smooth_arc_attaching_ends
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f α₀ α₁ : ℝ → F} {R₀ R₁ : F → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ContDiff ℝ ∞ f) (hdf : ∀ t, deriv f t ≠ 0) (hfinj : InjOn f (Icc 0 1))
    (hα₀ : ContDiff ℝ ∞ α₀) (hα₁ : ContDiff ℝ ∞ α₁) (hR₀ : ContDiff ℝ ∞ R₀) (hR₁ : ContDiff ℝ ∞ R₁)
    (hleft₀ : Function.LeftInverse R₀ α₀) (hleft₁ : Function.LeftInverse R₁ α₁)
    (hf₀ : f 0 = α₀ b) (hf₁ : f 1 = α₁ b)
    (hgerm₀ : f =ᶠ[𝓝 0] fun t => α₀ (R₀ (f t)))
    (hgerm₁ : f =ᶠ[𝓝 1] fun t => α₁ (R₁ (f t)))
    (hmeet₀ : ∀ v ∈ Icc a b, ∀ t ∈ Icc (0 : ℝ) 1, α₀ v = f t → t = 0)
    (hmeet₁ : ∀ v ∈ Icc a b, ∀ t ∈ Icc (0 : ℝ) 1, α₁ v = f t → t = 1)
    (hdisjoint : ∀ v ∈ Icc a b, ∀ w ∈ Icc a b, α₀ v ≠ α₁ w) :
    ∃ g : ℝ → F, ∃ u v : ℝ, u < 0 ∧ 1 < v ∧ ContDiff ℝ ∞ g ∧
      (∀ t, deriv g t ≠ 0) ∧ InjOn g (Icc u v) ∧ g u = α₀ a ∧ g v = α₁ a ∧
      g '' Icc u v = α₀ '' Icc a b ∪ f '' Icc 0 1 ∪ α₁ '' Icc a b ∧
      (∃ D₀ D₁ : ℝ ≃ₘ[ℝ] ℝ, StrictMono D₀ ∧ StrictAnti D₁ ∧
        D₀ u = a ∧ D₁ v = a ∧
        g =ᶠ[𝓝 u] (fun t => α₀ (D₀ t)) ∧
        g =ᶠ[𝓝 v] (fun t => α₁ (D₁ t))) := by
  let read₀ : ℝ → ℝ := fun t => R₀ (f t)
  let read₁ : ℝ → ℝ := fun t => R₁ (f t)
  have hread₀ : ContDiff ℝ ∞ read₀ := hR₀.comp hf
  have hread₁ : ContDiff ℝ ∞ read₁ := hR₁.comp hf
  have hd₀ : deriv read₀ 0 ≠ 0 :=
    deriv_ne_zero_of_regular_curve_coordinate hf hα₀ hR₀ (hdf 0) hgerm₀
  have hd₁ : deriv read₁ 1 ≠ 0 :=
    deriv_ne_zero_of_regular_curve_coordinate hf hα₁ hR₁ (hdf 1) hgerm₁
  obtain ⟨D₀, hD₀⟩ := exists_diffeomorph_realizing_scalar_germ hread₀ hd₀
  have hreadshift : ContDiff ℝ ∞ (fun t : ℝ => read₁ (t + 1)) :=
    hread₁.comp (contDiff_id.add contDiff_const)
  have hreadshiftder : deriv (fun t : ℝ => read₁ (t + 1)) 0 = deriv read₁ 1 := by
    have hd := ((hread₁.differentiable (by simp)) ((0 : ℝ) + 1)).hasDerivAt.comp (0 : ℝ)
      ((hasDerivAt_id (0 : ℝ)).add_const 1)
    simpa only [Function.comp_def, id_eq, zero_add, mul_one] using hd.deriv
  obtain ⟨D, hD⟩ := exists_diffeomorph_realizing_scalar_germ hreadshift
    (hreadshiftder ▸ hd₁)
  let D₁ := (translateDiffeomorph (-1 : ℝ)).trans D
  have hD₁ : (D₁ : ℝ → ℝ) =ᶠ[𝓝 1] read₁ := by
    have ht : Tendsto (fun t : ℝ => t - 1) (𝓝 1) (𝓝 0) := by
      have ht := (show Continuous (fun t : ℝ => t - 1) by fun_prop).tendsto 1
      simpa only [sub_self] using ht
    filter_upwards [hD.comp_tendsto ht] with t ht
    change D (t + -1) = read₁ t
    simpa only [Function.comp_apply, sub_add_cancel, sub_eq_add_neg, neg_add_cancel_right] using ht
  have hDb₀ : D₀ 0 = b := by rw [hD₀.self_of_nhds]; exact congrArg R₀ hf₀ |>.trans (hleft₀ b)
  have hDb₁ : D₁ 1 = b := by rw [hD₁.self_of_nhds]; exact congrArg R₁ hf₁ |>.trans (hleft₁ b)
  have h₀ : (fun t => α₀ (D₀ t)) =ᶠ[𝓝 0] f :=
    (hD₀.fun_comp α₀).trans hgerm₀.symm
  have h₁ : (fun t => α₁ (D₁ t)) =ᶠ[𝓝 1] f :=
    (hD₁.fun_comp α₁).trans hgerm₁.symm
  have hm₀ := strictMono_diffeomorph_of_arc_attachment hab D₀ hDb₀ h₀ hmeet₀
  have hm₁ := strictAnti_diffeomorph_of_arc_attachment hab D₁ hDb₁ h₁ hmeet₁
  obtain ⟨g, hg, hgL, hgM, hgR, hg₀, hg₁⟩ :=
    exists_contDiff_curve_attaching_ends hf hα₀ hα₁ D₀ D₁ h₀ h₁
  have hregL (t : ℝ) : deriv (fun t => α₀ (D₀ t)) t ≠ 0 := by
    apply deriv_ne_zero_of_smooth_left_inverse (hα₀.comp D₀.contMDiff.contDiff)
      (D₀.symm.contMDiff.contDiff.comp hR₀) (R := fun y => D₀.symm (R₀ y))
    intro t
    change D₀.symm (R₀ (α₀ (D₀ t))) = t
    rw [hleft₀, D₀.symm_apply_apply]
  have hregR (t : ℝ) : deriv (fun t => α₁ (D₁ t)) t ≠ 0 := by
    apply deriv_ne_zero_of_smooth_left_inverse (hα₁.comp D₁.contMDiff.contDiff)
      (D₁.symm.contMDiff.contDiff.comp hR₁) (R := fun y => D₁.symm (R₁ y))
    intro t
    change D₁.symm (R₁ (α₁ (D₁ t))) = t
    rw [hleft₁, D₁.symm_apply_apply]
  have hgreg (t : ℝ) : deriv g t ≠ 0 := by
    rcases lt_trichotomy t 0 with ht | rfl | ht
    · have he : g =ᶠ[𝓝 t] fun s => α₀ (D₀ s) := by
        filter_upwards [Iio_mem_nhds ht] with s hs
        exact hgL s (show s < 0 from hs).le
      rw [he.deriv_eq]
      exact hregL t
    · rw [hg₀.deriv_eq]
      exact hregL 0
    · rcases lt_trichotomy t 1 with ht1 | rfl | ht1
      · have he : g =ᶠ[𝓝 t] f := by
          filter_upwards [Ioo_mem_nhds ht ht1] with s hs
          exact hgM s ⟨hs.1.le, hs.2.le⟩
        rw [he.deriv_eq]
        exact hdf t
      · rw [hg₁.deriv_eq]
        exact hregR 1
      · have he : g =ᶠ[𝓝 t] fun s => α₁ (D₁ s) := by
          filter_upwards [Ioi_mem_nhds ht1] with s hs
          exact hgR s (show 1 < s from hs).le
        rw [he.deriv_eq]
        exact hregR t
  let u := D₀.symm a
  let v := D₁.symm a
  have huD : D₀ u = a := D₀.apply_symm_apply a
  have hvD : D₁ v = a := D₁.apply_symm_apply a
  have hu : u < 0 := hm₀.lt_iff_lt.mp (by rw [huD, hDb₀]; exact hab)
  have hv : 1 < v := hm₁.lt_iff_gt.mp (by rw [hvD, hDb₁]; exact hab)
  have hLmap {t : ℝ} (ht : t ∈ Icc u 0) : D₀ t ∈ Icc a b := by
    rw [← huD, ← hDb₀]
    exact ⟨hm₀.monotone ht.1, hm₀.monotone ht.2⟩
  have hRmap {t : ℝ} (ht : t ∈ Icc 1 v) : D₁ t ∈ Icc a b := by
    rw [← hvD, ← hDb₁]
    exact ⟨hm₁.antitone ht.2, hm₁.antitone ht.1⟩
  have hGL : InjOn g (Icc u 0) := by
    intro x hx y hy hxy
    rw [hgL x hx.2, hgL y hy.2] at hxy
    exact D₀.injective (hleft₀.injective hxy)
  have hGM : InjOn g (Icc 0 1) := by
    intro x hx y hy hxy
    exact hfinj hx hy ((hgM x hx).symm.trans (hxy.trans (hgM y hy)))
  have hGR : InjOn g (Icc 1 v) := by
    intro x hx y hy hxy
    rw [hgR x hx.1, hgR y hy.1] at hxy
    exact D₁.injective (hleft₁.injective hxy)
  have hLM {x y : ℝ} (hx : x ∈ Icc u 0) (hy : y ∈ Icc 0 1) (heq : g x = g y) : x = y := by
    have he : α₀ (D₀ x) = f y := (hgL x hx.2).symm.trans (heq.trans (hgM y hy))
    have hy₀ := hmeet₀ (D₀ x) (hLmap hx) y hy he
    subst y
    have hx₀ : D₀ x = D₀ 0 := by
      apply hleft₀.injective
      rw [hDb₀, ← hf₀]
      exact he
    exact D₀.injective hx₀
  have hMR {x y : ℝ} (hx : x ∈ Icc 0 1) (hy : y ∈ Icc 1 v) (heq : g x = g y) : x = y := by
    have he : α₁ (D₁ y) = f x := (hgR y hy.1).symm.trans (heq.symm.trans (hgM x hx))
    have hx₁ := hmeet₁ (D₁ y) (hRmap hy) x hx he
    subst x
    have hy₁ : D₁ y = D₁ 1 := by
      apply hleft₁.injective
      rw [hDb₁, ← hf₁]
      exact he
    exact (D₁.injective hy₁).symm
  have hLR {x y : ℝ} (hx : x ∈ Icc u 0) (hy : y ∈ Icc 1 v) : g x ≠ g y := by
    rw [hgL x hx.2, hgR y hy.1]
    exact hdisjoint (D₀ x) (hLmap hx) (D₁ y) (hRmap hy)
  have hi : InjOn g (Icc u v) := by
    intro x hx y hy hxy
    rcases le_or_gt x 0 with hx0 | hx0
    · rcases le_or_gt y 0 with hy0 | hy0
      · exact hGL ⟨hx.1, hx0⟩ ⟨hy.1, hy0⟩ hxy
      · rcases le_or_gt y 1 with hy1 | hy1
        · exact hLM ⟨hx.1, hx0⟩ ⟨hy0.le, hy1⟩ hxy
        · exact (hLR ⟨hx.1, hx0⟩ ⟨hy1.le, hy.2⟩ hxy).elim
    · rcases le_or_gt x 1 with hx1 | hx1
      · rcases le_or_gt y 0 with hy0 | hy0
        · exact (hLM ⟨hy.1, hy0⟩ ⟨hx0.le, hx1⟩ hxy.symm).symm
        · rcases le_or_gt y 1 with hy1 | hy1
          · exact hGM ⟨hx0.le, hx1⟩ ⟨hy0.le, hy1⟩ hxy
          · exact hMR ⟨hx0.le, hx1⟩ ⟨hy1.le, hy.2⟩ hxy
      · rcases le_or_gt y 0 with hy0 | hy0
        · exact (hLR ⟨hy.1, hy0⟩ ⟨hx1.le, hx.2⟩ hxy.symm).elim
        · rcases le_or_gt y 1 with hy1 | hy1
          · exact (hMR ⟨hy0.le, hy1⟩ ⟨hx1.le, hx.2⟩ hxy.symm).symm
          · exact hGR ⟨hx1.le, hx.2⟩ ⟨hy1.le, hy.2⟩ hxy
  have hleftimage : g '' Icc u 0 = α₀ '' Icc a b := by
    rw [image_congr (fun t ht => hgL t ht.2), ← image_image,
      D₀.continuous.continuousOn.image_Icc_of_monotoneOn hu.le (hm₀.monotone.monotoneOn _),
      huD, hDb₀]
  have hrightimage : g '' Icc 1 v = α₁ '' Icc a b := by
    rw [image_congr (fun t ht => hgR t ht.1), ← image_image,
      D₁.continuous.continuousOn.image_Icc_of_antitoneOn hv.le (hm₁.antitone.antitoneOn _),
      hvD, hDb₁]
  refine ⟨g, u, v, hu, hv, hg, hgreg, hi, by rw [hgL u hu.le, huD],
    by rw [hgR v hv.le, hvD], ?_, D₀, D₁, hm₀, hm₁, huD, hvD, ?_, ?_⟩
  · rw [← Icc_union_Icc_eq_Icc hu.le (zero_le_one.trans hv.le),
      ← Icc_union_Icc_eq_Icc zero_le_one hv.le, image_union, image_union,
      hleftimage, hrightimage, image_congr hgM, union_assoc]
  · filter_upwards [Iio_mem_nhds hu] with t ht
    exact hgL t (show t < 0 from ht).le
  · filter_upwards [Ioi_mem_nhds hv] with t ht
    exact hgR t (show 1 < t from ht).le


private theorem deriv_neg_of_antitone_diffeomorph
    (D : ℝ ≃ₘ[ℝ] ℝ) (hD : Antitone D) (x : ℝ) : deriv D x < 0 := by
  have hd := D.contDiff.differentiable (by simp)
  have hi := D.symm.contDiff.differentiable (by simp)
  have he := ((hi (D x)).hasDerivAt.comp x (hd x).hasDerivAt).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun y => (D.symm_apply_apply y).symm)
  have hn : deriv D x ≠ 0 := by
    intro h
    have hh := he.unique (hasDerivAt_id x)
    rw [h, mul_zero] at hh
    exact zero_ne_one hh
  exact lt_of_le_of_ne hD.deriv_nonpos hn

private theorem exists_increasing_affine_diffeomorph
    {a b u v : ℝ} (hab : a < b) (huv : u < v) :
    ∃ L : ℝ ≃ₘ[ℝ] ℝ, StrictMono L ∧ L a = u ∧ L b = v := by
  let c := (v - u) / (b - a)
  have hc : 0 < c := div_pos (sub_pos.mpr huv) (sub_pos.mpr hab)
  let A := ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 c hc.ne')
  let L := A.toDiffeomorph.trans (DifferentialGeometry.Topology.translateDiffeomorph (u - c * a))
  have hL (x : ℝ) : L x = x * c + (u - c * a) := rfl
  refine ⟨L, fun x y hxy => by
      rw [hL, hL];
      have hh := mul_lt_mul_of_pos_right hxy hc;
      linarith only [hh],
    ?_, ?_⟩
  · rw [hL]; ring
  · rw [hL]
    dsimp only [c]
    field_simp [sub_ne_zero.mpr hab.ne']
    ring

theorem exists_smooth_arc_eq_endpoint_parameters
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g α₀ α₁ : ℝ → F} {f : ℝ → ℝ} {a b u v : ℝ} {V : Set ℝ}
    (hab : a < b) (huv : u < v) (hg : ContDiff ℝ ∞ g)
    (hgderiv : ∀ t, deriv g t ≠ 0) (hginj : InjOn g (Icc u v))
    (D₀ D₁ : ℝ ≃ₘ[ℝ] ℝ) (hm₀ : StrictMono D₀) (hm₁ : StrictAnti D₁)
    (hV : IsOpen V) (haV : a ∈ V) (hbV : b ∈ V) (hf : ContDiffOn ℝ ∞ f V)
    (hfa : f a = D₀ u) (hfb : f b = D₁ v)
    (hd₀ : 0 < deriv f a) (hd₁ : deriv f b < 0)
    (hga : g =ᶠ[𝓝 u] (fun x => α₀ (D₀ x)))
    (hgb : g =ᶠ[𝓝 v] (fun x => α₁ (D₁ x))) :
    ∃ β : ℝ → F, ContDiff ℝ ∞ β ∧ (∀ t, deriv β t ≠ 0) ∧
      InjOn β (Icc a b) ∧ β '' Icc a b = g '' Icc u v ∧
      β =ᶠ[𝓝 a] (fun x => α₀ (f x)) ∧ β =ᶠ[𝓝 b] (fun x => α₁ (f x)) := by
  obtain ⟨L, hLmono, hLa, hLb⟩ := exists_increasing_affine_diffeomorph hab huv
  let f₀ : ℝ → ℝ := fun x => L.symm (D₀.symm (f x))
  let f₁ : ℝ → ℝ := fun x => L.symm (D₁.symm (f x))
  have hLmi : StrictMono L.symm := by
    intro x y hxy
    apply hLmono.lt_iff_lt.mp
    simpa only [L.apply_symm_apply] using hxy
  have hDmi : StrictMono D₀.symm := by
    intro x y hxy
    apply hm₀.lt_iff_lt.mp
    simpa only [D₀.apply_symm_apply] using hxy
  have hDai : StrictAnti D₁.symm := by
    intro x y hxy
    apply hm₁.lt_iff_gt.mp
    simpa only [D₁.apply_symm_apply] using hxy
  have hLf (x : ℝ) : 0 < deriv L.symm x :=
    DifferentialGeometry.Analysis.deriv_pos_of_monotone_left_inverse
      (L.symm.contDiff.differentiable (by simp))
      (L.contDiff.differentiable (by simp)) L.apply_symm_apply hLmi.monotone x
  have hD₀f (x : ℝ) : 0 < deriv D₀.symm x :=
    DifferentialGeometry.Analysis.deriv_pos_of_monotone_left_inverse
      (D₀.symm.contDiff.differentiable (by simp))
      (D₀.contDiff.differentiable (by simp)) D₀.apply_symm_apply hDmi.monotone x
  have hD₁f (x : ℝ) : deriv D₁.symm x < 0 :=
    deriv_neg_of_antitone_diffeomorph D₁.symm hDai.antitone x
  have hf₀ : ContDiffOn ℝ ∞ f₀ V := L.symm.contDiff.comp_contDiffOn
    (D₀.symm.contDiff.comp_contDiffOn hf)
  have hf₁ : ContDiffOn ℝ ∞ f₁ V := L.symm.contDiff.comp_contDiffOn
    (D₁.symm.contDiff.comp_contDiffOn hf)
  have he₀ : f₀ a = a := by simp only [f₀, hfa, D₀.symm_apply_apply, ← hLa, L.symm_apply_apply]
  have he₁ : f₁ b = b := by simp only [f₁, hfb, D₁.symm_apply_apply, ← hLb, L.symm_apply_apply]
  have hdf₀ : 0 < deriv f₀ a := by
    have hfda := ((hf.contDiffAt (hV.mem_nhds haV)).differentiableAt (by simp)).hasDerivAt
    have he := (((L.symm.contDiff.differentiable (by simp)) _).hasDerivAt.comp a
      (((D₀.symm.contDiff.differentiable (by simp)) _).hasDerivAt.comp a hfda)).deriv
    rw [show deriv f₀ a = _ from he]
    exact mul_pos (hLf _) (mul_pos (hD₀f _) hd₀)
  have hdf₁ : 0 < deriv f₁ b := by
    have hfdb := ((hf.contDiffAt (hV.mem_nhds hbV)).differentiableAt (by simp)).hasDerivAt
    have he := (((L.symm.contDiff.differentiable (by simp)) _).hasDerivAt.comp b
      (((D₁.symm.contDiff.differentiable (by simp)) _).hasDerivAt.comp b hfdb)).deriv
    rw [show deriv f₁ b = _ from he]
    exact mul_pos (hLf _) (mul_pos_of_neg_of_neg (hD₁f _) hd₁)
  obtain ⟨E, hEmono, hEa, hEb, hEI⟩ :=
    DifferentialGeometry.Analysis.exists_diffeomorph_eq_endpoint_germs hab
    hV haV hf₀ hV hbV hf₁ he₀ he₁ hdf₀ hdf₁
  let ρ := E.trans L
  have hρa : ρ a = u := by change L (E a) = u; rw [hEa.self_of_nhds, he₀, hLa]
  have hρb : ρ b = v := by change L (E b) = v; rw [hEb.self_of_nhds, he₁, hLb]
  have hρmono : StrictMono ρ := hLmono.comp hEmono
  have hρI : ρ '' Icc a b = Icc u v := by
    rw [ρ.continuous.continuousOn.image_Icc_of_monotoneOn hab.le
      (hρmono.monotone.monotoneOn _), hρa, hρb]
  let β : ℝ → F := fun x => g (ρ x)
  have hβ : ContDiff ℝ ∞ β := hg.comp ρ.contDiff
  refine ⟨β, hβ, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    have hdρ : 0 < deriv ρ x := DifferentialGeometry.Analysis.deriv_pos_of_monotone_left_inverse
      (ρ.contDiff.differentiable (by simp)) (ρ.symm.contDiff.differentiable (by simp))
      ρ.symm_apply_apply hρmono.monotone x
    rw [show deriv β x = deriv ρ x • deriv g (ρ x) from
      ((hg.differentiable (by simp) _).hasDerivAt.scomp x
        (ρ.contDiff.differentiable (by simp) _).hasDerivAt).deriv]
    exact smul_ne_zero hdρ.ne' (hgderiv _)
  · exact hginj.comp ρ.injective.injOn (fun x hx => hρI ▸ mem_image_of_mem ρ hx)
  · exact (image_comp g ρ (Icc a b)).trans (congrArg (image g) hρI)
  · have ht : Tendsto ρ (𝓝 a) (𝓝 u) := hρa ▸ ρ.continuous.continuousAt.tendsto
    filter_upwards [hga.comp_tendsto ht, hEa] with x hx he
    change g (ρ x) = α₀ (f x)
    dsimp only [Function.comp_def] at hx
    rw [hx]
    change α₀ (D₀ (L (E x))) = _
    rw [he]
    simp only [f₀, L.apply_symm_apply, D₀.apply_symm_apply]
  · have ht : Tendsto ρ (𝓝 b) (𝓝 v) := hρb ▸ ρ.continuous.continuousAt.tendsto
    filter_upwards [hgb.comp_tendsto ht, hEb] with x hx he
    change g (ρ x) = α₁ (f x)
    dsimp only [Function.comp_def] at hx
    rw [hx]
    change α₁ (D₁ (L (E x))) = _
    rw [he]
    simp only [f₁, L.apply_symm_apply, D₁.apply_symm_apply]


end DifferentialGeometry.Topology
