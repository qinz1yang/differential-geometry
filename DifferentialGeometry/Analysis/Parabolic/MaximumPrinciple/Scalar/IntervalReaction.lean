import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.PeriodicComparison
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Real.Sqrt

open Set Filter
open scoped Topology

namespace DifferentialGeometry.Analysis.Parabolic

private theorem second_deriv_mul_at {f g : ℝ → ℝ} {x : ℝ}
    (hf : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ f y)
    (hg : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ g y)
    (hf' : DifferentiableAt ℝ (deriv f) x)
    (hg' : DifferentiableAt ℝ (deriv g) x) :
    HasDerivAt (deriv (fun y => f y * g y))
      (deriv (deriv f) x * g x + 2 * deriv f x * deriv g x +
        f x * deriv (deriv g) x) x := by
  have heq : deriv (fun y => f y * g y) =ᶠ[𝓝 x]
      fun y => deriv f y * g y + f y * deriv g y := by
    filter_upwards [hf, hg] with y hfy hgy
    exact deriv_fun_mul hfy hgy
  have hd := ((hf'.hasDerivAt.mul hg.self_of_nhds.hasDerivAt).add
    (hf.self_of_nhds.hasDerivAt.mul hg'.hasDerivAt)).congr_of_eventuallyEq heq
  have he : deriv (deriv f) x * g x + 2 * deriv f x * deriv g x +
      f x * deriv (deriv g) x =
      (deriv (deriv f) x * g x + deriv f x * deriv g x) +
        (deriv f x * deriv g x + f x * deriv (deriv g) x) := by ring
  rw [he]
  exact hd

private theorem cutoff_inequality_at_spatial_max {f g : ℝ → ℝ} {x a : ℝ}
    (hf : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ f y)
    (hg : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ g y)
    (hf' : DifferentiableAt ℝ (deriv f) x)
    (hg' : DifferentiableAt ℝ (deriv g) x)
    (hmax : IsLocalMax (fun y => f y * g y) x)
    (ha : 0 ≤ a) (hfx : 0 ≤ f x) :
    a * f x ^ 2 * deriv (deriv g) x +
      a * f x * g x * deriv (deriv f) x -
      2 * a * g x * deriv f x ^ 2 ≤ 0 := by
  have hfirst := hmax.hasDerivAt_eq_zero
    (hf.self_of_nhds.hasDerivAt.mul hg.self_of_nhds.hasDerivAt)
  have hsecond := second_deriv_mul_at hf hg hf' hg'
  have hnegsecond : HasDerivAt (deriv (fun y => -(f y * g y)))
      (-(deriv (deriv f) x * g x + 2 * deriv f x * deriv g x +
        f x * deriv (deriv g) x)) x := by
    apply hsecond.neg.congr_of_eventuallyEq
    exact Filter.Eventually.of_forall (fun y => deriv.fun_neg)
  have hnonpos := IsLocalMin.second_deriv_nonneg hmax.neg
    (hf.self_of_nhds.hasDerivAt.mul hg.self_of_nhds.hasDerivAt).neg hnegsecond
  have hscale := mul_nonneg (mul_nonneg ha hfx) hnonpos
  have hcross := congrArg (fun z : ℝ => 2 * a * deriv f x * z) hfirst
  nlinarith only [hscale, hcross]

private theorem cutoff_quadratic_bound_at_maximum
    {t φ u ut uxx φx φxx a c D E : ℝ}
    (ht : 0 < t) (hφ : 0 < φ) (hφle : φ ≤ 1) (hu : 0 < u) (hc : 0 < c)
    (htime : 0 ≤ φ * u + t * φ * ut)
    (hspace : a * φ ^ 2 * uxx + a * φ * u * φxx - 2 * a * u * φx ^ 2 ≤ 0)
    (hpde : ut - a * uxx ≤ -c * u ^ 2)
    (hcut : -a * φxx ≤ D) (hgrad : a * φx ^ 2 ≤ E * φ) :
    t * (φ * u) ≤ (1 + t * (D + 2 * E)) / c := by
  have htime' := mul_nonneg hφ.le htime
  have hspace' := mul_le_mul_of_nonneg_left hspace ht.le
  have hpde' := mul_le_mul_of_nonneg_left hpde (mul_nonneg ht.le (sq_nonneg φ))
  have hcut' := mul_le_mul_of_nonneg_left hcut
    (mul_nonneg (mul_nonneg ht.le hφ.le) hu.le)
  have hgrad' := mul_le_mul_of_nonneg_left hgrad (by positivity : 0 ≤ 2 * t * u)
  have hineq : c * t * φ ^ 2 * u ^ 2 ≤ φ ^ 2 * u + t * φ * u * (D + 2 * E) := by
    nlinarith only [htime', hspace', hpde', hcut', hgrad']
  have hscaled := mul_le_mul_of_nonneg_left hineq ht.le
  have hv : 0 < t * (φ * u) := mul_pos ht (mul_pos hφ hu)
  have hplateau := mul_le_mul_of_nonneg_left hφle hv.le
  have hfactor : (t * (φ * u)) * (c * (t * (φ * u)) - (1 + t * (D + 2 * E))) ≤ 0 := by
    nlinarith only [hscaled, hplateau]
  have hnonpos := nonpos_of_mul_nonpos_right hfactor hv
  apply (le_div_iff₀ hc).2
  nlinarith only [hnonpos]

theorem cutoff_quadratic_reaction_upper_bound_on_interval_of_reaction_on_pos
    {u a : ℝ → ℝ → ℝ} {φ : ℝ → ℝ} {l r T c D E : ℝ}
    (hc : 0 < c) (herror : 0 ≤ D + 2 * E)
    (hcont : ContinuousOn (fun p : ℝ × ℝ => u p.1 p.2) (Icc l r ×ˢ Ico 0 T))
    (hφcont : ContinuousOn φ (Icc l r))
    (hφ : ∀ x ∈ Icc l r, φ x ∈ Icc 0 1) (hl : φ l = 0) (hr : φ r = 0)
    (hφ₁ : DifferentiableOn ℝ φ (Ioo l r))
    (hφ₂ : DifferentiableOn ℝ (deriv φ) (Ioo l r))
    (hu₁ : ∀ t ∈ Ioo 0 T, DifferentiableOn ℝ (fun x => u x t) (Ioo l r))
    (hu₂ : ∀ t ∈ Ioo 0 T, DifferentiableOn ℝ (deriv (fun x => u x t)) (Ioo l r))
    (hut : ∀ x ∈ Ioo l r, ∀ t ∈ Ioo 0 T,
      DifferentiableAt ℝ (fun s => u x s) t)
    (ha : ∀ x ∈ Ioo l r, ∀ t ∈ Ioo 0 T, 0 ≤ a x t)
    (hpde : ∀ x ∈ Ioo l r, ∀ t ∈ Ioo 0 T, 0 < u x t →
      deriv (fun s => u x s) t - a x t * deriv (deriv (fun y => u y t)) x ≤
        -c * u x t ^ 2)
    (hcut : ∀ x ∈ Ioo l r, ∀ t ∈ Ioo 0 T, -a x t * deriv (deriv φ) x ≤ D)
    (hgrad : ∀ x ∈ Ioo l r, ∀ t ∈ Ioo 0 T, a x t * deriv φ x ^ 2 ≤ E * φ x) :
    ∀ t ∈ Ioo 0 T, ∀ x ∈ Icc l r,
      t * (φ x * u x t) ≤ (1 + t * (D + 2 * E)) / c := by
  intro S hS x hx
  let F : ℝ × ℝ → ℝ := fun p => p.2 * (φ p.1 * u p.1 p.2)
  have hcontF : ContinuousOn F (Icc l r ×ˢ Icc 0 S) := by
    apply continuousOn_snd.mul
    apply ContinuousOn.mul
    · exact hφcont.comp continuousOn_fst (fun p hp => hp.1)
    · exact hcont.mono (fun p hp => ⟨hp.1, hp.2.1, hp.2.2.trans_lt hS.2⟩)
  obtain ⟨⟨y, s⟩, hmem, hmax⟩ := (isCompact_Icc.prod isCompact_Icc).exists_isMaxOn
    (show (Icc l r ×ˢ Icc 0 S).Nonempty from ⟨(x, 0), hx, le_rfl, hS.1.le⟩) hcontF
  have hmax' : ∀ p ∈ Icc l r ×ˢ Icc 0 S, F p ≤ F (y, s) := hmax
  have hboundpos : 0 < (1 + S * (D + 2 * E)) / c :=
    div_pos (by nlinarith [mul_nonneg hS.1.le herror]) hc
  by_cases hpos : 0 < F (y, s)
  swap
  · exact (hmax' (x, S) ⟨hx, hS.1.le, le_rfl⟩).trans
      ((le_of_not_gt hpos).trans hboundpos.le)
  have hs : 0 < s := by
    by_contra h
    have hs0 : s = 0 := le_antisymm (le_of_not_gt h) hmem.2.1
    simp [F, hs0] at hpos
  have hst : s ∈ Ioo 0 T := ⟨hs, hmem.2.2.trans_lt hS.2⟩
  have hy : y ∈ Ioo l r := by
    constructor
    · by_contra h
      have heq : y = l := le_antisymm (le_of_not_gt h) hmem.1.1
      simp [F, heq, hl] at hpos
    · by_contra h
      have heq : y = r := le_antisymm hmem.1.2 (le_of_not_gt h)
      simp [F, heq, hr] at hpos
  have hφy : 0 < φ y := by
    by_contra h
    have heq : φ y = 0 := le_antisymm (le_of_not_gt h) (hφ y hmem.1).1
    simp [F, heq] at hpos
  have huy : 0 < u y s := by
    have hprod : 0 < φ y * u y s := (mul_pos_iff_of_pos_left hs).mp hpos
    exact (mul_pos_iff_of_pos_left hφy).mp hprod
  have hspacemax : IsLocalMax (fun z => φ z * u z s) y := by
    filter_upwards [Ioo_mem_nhds hy.1 hy.2] with z hz
    have h := hmax' (z, s) ⟨⟨hz.1.le, hz.2.le⟩, hmem.2⟩
    exact (mul_le_mul_iff_right₀ hs).mp h
  have hφdiff : ∀ᶠ z in 𝓝 y, DifferentiableAt ℝ φ z := by
    filter_upwards [Ioo_mem_nhds hy.1 hy.2] with z hz
    exact (hφ₁ z hz).differentiableAt (isOpen_Ioo.mem_nhds hz)
  have hudiff : ∀ᶠ z in 𝓝 y, DifferentiableAt ℝ (fun z => u z s) z := by
    filter_upwards [Ioo_mem_nhds hy.1 hy.2] with z hz
    exact (hu₁ s hst z hz).differentiableAt (isOpen_Ioo.mem_nhds hz)
  have hspace := cutoff_inequality_at_spatial_max hφdiff hudiff
    ((hφ₂ y hy).differentiableAt (isOpen_Ioo.mem_nhds hy))
    ((hu₂ s hst y hy).differentiableAt (isOpen_Ioo.mem_nhds hy))
    hspacemax (ha y hy s hst) hφy.le
  have hleft : ∀ᶠ τ in 𝓝[<] s, -(s * (φ y * u y s)) ≤ -(τ * (φ y * u y τ)) := by
    filter_upwards [Ioo_mem_nhdsLT hs] with τ hτ
    exact neg_le_neg (hmax' (y, τ) ⟨hmem.1, hτ.1.le, hτ.2.le.trans hmem.2.2⟩)
  have hd := (hasDerivAt_id s).mul ((hut y hy s hst).hasDerivAt.const_mul (φ y))
  have htime := deriv_nonpos_of_eventually_le_left hd.neg.differentiableAt hleft
  rw [hd.neg.deriv] at htime
  have hlocal := cutoff_quadratic_bound_at_maximum hs hφy (hφ y hmem.1).2 huy hc
    (by simpa only [one_mul, neg_nonpos, id_eq, mul_assoc] using htime) hspace
    (hpde y hy s hst huy) (hcut y hy s hst) (hgrad y hy s hst)
  have hmono : (1 + s * (D + 2 * E)) / c ≤ (1 + S * (D + 2 * E)) / c := by
    apply div_le_div_of_nonneg_right _ hc.le
    linarith [mul_le_mul_of_nonneg_right hmem.2.2 herror]
  exact (hmax' (x, S) ⟨hx, hS.1.le, le_rfl⟩).trans (hlocal.trans hmono)

theorem cutoff_quadratic_reaction_upper_bound_on_interval
    {u a : ℝ → ℝ → ℝ} {φ : ℝ → ℝ} {l r T c D E : ℝ}
    (hc : 0 < c) (herror : 0 ≤ D + 2 * E)
    (hcont : ContinuousOn (fun p : ℝ × ℝ => u p.1 p.2) (Icc l r ×ˢ Ico 0 T))
    (hφcont : ContinuousOn φ (Icc l r))
    (hφ : ∀ x ∈ Icc l r, φ x ∈ Icc 0 1) (hl : φ l = 0) (hr : φ r = 0)
    (hφ₁ : DifferentiableOn ℝ φ (Ioo l r))
    (hφ₂ : DifferentiableOn ℝ (deriv φ) (Ioo l r))
    (hu₁ : ∀ t ∈ Ioo 0 T, DifferentiableOn ℝ (fun x => u x t) (Ioo l r))
    (hu₂ : ∀ t ∈ Ioo 0 T, DifferentiableOn ℝ (deriv (fun x => u x t)) (Ioo l r))
    (hut : ∀ x ∈ Ioo l r, ∀ t ∈ Ioo 0 T,
      DifferentiableAt ℝ (fun s => u x s) t)
    (ha : ∀ x ∈ Ioo l r, ∀ t ∈ Ioo 0 T, 0 ≤ a x t)
    (hpde : ∀ x ∈ Ioo l r, ∀ t ∈ Ioo 0 T,
      deriv (fun s => u x s) t - a x t * deriv (deriv (fun y => u y t)) x ≤
        -c * u x t ^ 2)
    (hcut : ∀ x ∈ Ioo l r, ∀ t ∈ Ioo 0 T, -a x t * deriv (deriv φ) x ≤ D)
    (hgrad : ∀ x ∈ Ioo l r, ∀ t ∈ Ioo 0 T, a x t * deriv φ x ^ 2 ≤ E * φ x) :
    ∀ t ∈ Ioo 0 T, ∀ x ∈ Icc l r,
      t * (φ x * u x t) ≤ (1 + t * (D + 2 * E)) / c := by
  exact cutoff_quadratic_reaction_upper_bound_on_interval_of_reaction_on_pos hc herror hcont
    hφcont hφ hl hr hφ₁ hφ₂ hu₁ hu₂ hut ha (fun x hx t ht _ => hpde x hx t ht) hcut hgrad

private noncomputable def intervalCutoff (R x : ℝ) : ℝ := (1 - (x / R) ^ 2) ^ 2

private theorem hasDerivAt_intervalCutoff (R x : ℝ) :
    HasDerivAt (intervalCutoff R) (-4 * x / R ^ 2 * (1 - (x / R) ^ 2)) x := by
  have h := ((((hasDerivAt_id x).div_const R).pow 2).const_sub 1).pow 2
  convert h using 1 <;> first | rfl | (simp only [Pi.pow_apply, id_eq]; ring)

private theorem deriv_intervalCutoff (R : ℝ) :
    deriv (intervalCutoff R) = fun x => -4 * x / R ^ 2 * (1 - (x / R) ^ 2) := by
  funext x
  exact (hasDerivAt_intervalCutoff R x).deriv

private theorem hasDerivAt_deriv_intervalCutoff (R x : ℝ) :
    HasDerivAt (deriv (intervalCutoff R))
      (-4 / R ^ 2 + 12 * x ^ 2 / R ^ 4) x := by
  rw [deriv_intervalCutoff]
  have h := (((hasDerivAt_id x).const_mul (-4)).div_const (R ^ 2)).mul
    ((((hasDerivAt_id x).div_const R).pow 2).const_sub 1)
  convert h using 1 <;> first | rfl | (simp only [Pi.pow_apply, id_eq]; ring)

private theorem intervalCutoff_bounds {R x : ℝ} (hR : 0 < R) (hx : x ∈ Icc (-R) R) :
    intervalCutoff R x ∈ Icc 0 1 := by
  have hz : x / R ∈ Icc (-1 : ℝ) 1 := by
    constructor
    · apply (le_div_iff₀ hR).2
      linarith [hx.1]
    · exact (div_le_one hR).2 hx.2
  have hzsq : (x / R) ^ 2 ≤ 1 := by nlinarith [hz.1, hz.2]
  dsimp [intervalCutoff]
  constructor
  · positivity
  · nlinarith [sq_nonneg (x / R)]

private theorem intervalCutoff_derivative_bounds {R x a Λ : ℝ}
    (hR : 0 < R) (hx : x ∈ Icc (-R) R) (ha : 0 ≤ a) (haΛ : a ≤ Λ) :
    -a * deriv (deriv (intervalCutoff R)) x ≤ 4 * Λ / R ^ 2 ∧
      a * deriv (intervalCutoff R) x ^ 2 ≤ 16 * Λ / R ^ 2 * intervalCutoff R x := by
  rw [(hasDerivAt_deriv_intervalCutoff R x).deriv,
    (hasDerivAt_intervalCutoff R x).deriv]
  have hΛ : 0 ≤ Λ := ha.trans haΛ
  have hx2 : x ^ 2 ≤ R ^ 2 := by nlinarith [hx.1, hx.2]
  have hR2 : 0 < R ^ 2 := sq_pos_of_pos hR
  constructor
  · have hneg : 0 ≤ a * (12 * x ^ 2 / R ^ 4) := by positivity
    have hmul := mul_le_mul_of_nonneg_right haΛ (by positivity : 0 ≤ 4 / R ^ 2)
    simp only [div_eq_mul_inv] at hneg hmul ⊢
    nlinarith only [hneg, hmul]
  · have hax : a * x ^ 2 ≤ Λ * R ^ 2 :=
      (mul_le_mul_of_nonneg_left hx2 ha).trans (mul_le_mul_of_nonneg_right haΛ hR2.le)
    have hscaled := mul_le_mul_of_nonneg_right hax
      (show 0 ≤ 16 * (1 - (x / R) ^ 2) ^ 2 / R ^ 4 by positivity)
    dsimp [intervalCutoff]
    convert hscaled using 1 <;> first | rfl | (field_simp [hR.ne'] <;> ring)

theorem quadratic_reaction_interior_upper_bound_of_reaction_on_pos
    {u a : ℝ → ℝ → ℝ} {R T c Λ : ℝ}
    (hR : 0 < R) (hc : 0 < c) (hΛ : 0 ≤ Λ)
    (hcont : ContinuousOn (fun p : ℝ × ℝ => u p.1 p.2) (Icc (-R) R ×ˢ Ico 0 T))
    (hu₁ : ∀ t ∈ Ioo 0 T, DifferentiableOn ℝ (fun x => u x t) (Ioo (-R) R))
    (hu₂ : ∀ t ∈ Ioo 0 T, DifferentiableOn ℝ (deriv (fun x => u x t)) (Ioo (-R) R))
    (hut : ∀ x ∈ Ioo (-R) R, ∀ t ∈ Ioo 0 T,
      DifferentiableAt ℝ (fun s => u x s) t)
    (ha : ∀ x ∈ Ioo (-R) R, ∀ t ∈ Ioo 0 T, a x t ∈ Icc 0 Λ)
    (hpde : ∀ x ∈ Ioo (-R) R, ∀ t ∈ Ioo 0 T, 0 < u x t →
      deriv (fun s => u x s) t - a x t * deriv (deriv (fun y => u y t)) x ≤
        -c * u x t ^ 2) :
    ∀ t ∈ Ioo 0 T, ∀ x ∈ Icc (-R / 2) (R / 2),
      u x t ≤ 16 / (9 * c * t) + 64 * Λ / (c * R ^ 2) := by
  have hφcont : ContinuousOn (intervalCutoff R) (Icc (-R) R) :=
    (show Differentiable ℝ (intervalCutoff R) from
      fun x => (hasDerivAt_intervalCutoff R x).differentiableAt).continuous.continuousOn
  have hbound := cutoff_quadratic_reaction_upper_bound_on_interval_of_reaction_on_pos
    (u := u) (a := a) (φ := intervalCutoff R)
    (D := 4 * Λ / R ^ 2) (E := 16 * Λ / R ^ 2) hc (by positivity) hcont hφcont
    (fun x hx => intervalCutoff_bounds hR hx)
    (by simp [intervalCutoff, hR.ne']) (by simp [intervalCutoff, hR.ne'])
    (fun x _ => (hasDerivAt_intervalCutoff R x).differentiableAt.differentiableWithinAt)
    (fun x _ => (hasDerivAt_deriv_intervalCutoff R x).differentiableAt.differentiableWithinAt)
    hu₁ hu₂ hut (fun x hx t ht => (ha x hx t ht).1) hpde
    (fun x hx t ht => (intervalCutoff_derivative_bounds hR ⟨hx.1.le, hx.2.le⟩
      (ha x hx t ht).1 (ha x hx t ht).2).1)
    (fun x hx t ht => (intervalCutoff_derivative_bounds hR ⟨hx.1.le, hx.2.le⟩
      (ha x hx t ht).1 (ha x hx t ht).2).2)
  intro t ht x hx
  have htpos : 0 < t := ht.1
  have hxR : x ∈ Icc (-R) R := ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hz : -(1 / 2 : ℝ) ≤ x / R ∧ x / R ≤ 1 / 2 := by
    constructor
    · apply (le_div_iff₀ hR).2
      linarith [hx.1]
    · apply (div_le_iff₀ hR).2
      linarith [hx.2]
  have hcentral : (9 / 16 : ℝ) ≤ intervalCutoff R x := by
    have hzsq : (x / R) ^ 2 ≤ 1 / 4 := by nlinarith [hz.1, hz.2]
    dsimp [intervalCutoff]
    nlinarith [sq_nonneg (x / R)]
  by_cases hu : 0 ≤ u x t
  swap
  · exact (le_of_not_ge hu).trans (by positivity)
  have hprod := mul_le_mul_of_nonneg_right hcentral
    (mul_nonneg (mul_nonneg ht.1.le hu) hc.le)
  have hmax := (le_div_iff₀ hc).mp (hbound t ht x hxR)
  have hintermediate : u x t ≤
      (16 / 9) * (1 + t * (4 * Λ / R ^ 2 + 2 * (16 * Λ / R ^ 2))) / (c * t) := by
    apply (le_div_iff₀ (mul_pos hc ht.1)).2
    nlinarith only [hprod, hmax]
  calc
    u x t ≤ (16 / 9) * (1 + t * (4 * Λ / R ^ 2 + 2 * (16 * Λ / R ^ 2))) /
        (c * t) := hintermediate
    _ = 16 / (9 * c * t) + 64 * Λ / (c * R ^ 2) := by
      field_simp [ht.1.ne', hc.ne', hR.ne']
      ring

theorem quadratic_reaction_interior_upper_bound
    {u a : ℝ → ℝ → ℝ} {R T c Λ : ℝ}
    (hR : 0 < R) (hc : 0 < c) (hΛ : 0 ≤ Λ)
    (hcont : ContinuousOn (fun p : ℝ × ℝ => u p.1 p.2) (Icc (-R) R ×ˢ Ico 0 T))
    (hu₁ : ∀ t ∈ Ioo 0 T, DifferentiableOn ℝ (fun x => u x t) (Ioo (-R) R))
    (hu₂ : ∀ t ∈ Ioo 0 T, DifferentiableOn ℝ (deriv (fun x => u x t)) (Ioo (-R) R))
    (hut : ∀ x ∈ Ioo (-R) R, ∀ t ∈ Ioo 0 T,
      DifferentiableAt ℝ (fun s => u x s) t)
    (ha : ∀ x ∈ Ioo (-R) R, ∀ t ∈ Ioo 0 T, a x t ∈ Icc 0 Λ)
    (hpde : ∀ x ∈ Ioo (-R) R, ∀ t ∈ Ioo 0 T,
      deriv (fun s => u x s) t - a x t * deriv (deriv (fun y => u y t)) x ≤
        -c * u x t ^ 2) :
    ∀ t ∈ Ioo 0 T, ∀ x ∈ Icc (-R / 2) (R / 2),
      u x t ≤ 16 / (9 * c * t) + 64 * Λ / (c * R ^ 2) := by
  exact quadratic_reaction_interior_upper_bound_of_reaction_on_pos hR hc hΛ hcont hu₁ hu₂ hut ha
    (fun x hx t ht _ => hpde x hx t ht)

theorem quadratic_reaction_interior_upper_bound_on_closed_time_interval_of_reaction_on_pos
    {u a : ℝ → ℝ → ℝ} {R T c Λ : ℝ}
    (hR : 0 < R) (hc : 0 < c) (hΛ : 0 ≤ Λ)
    (hcont : ContinuousOn (fun p : ℝ × ℝ => u p.1 p.2) (Icc (-R) R ×ˢ Icc 0 T))
    (hu₁ : ∀ t ∈ Ioo 0 T, DifferentiableOn ℝ (fun x => u x t) (Ioo (-R) R))
    (hu₂ : ∀ t ∈ Ioo 0 T, DifferentiableOn ℝ (deriv (fun x => u x t)) (Ioo (-R) R))
    (hut : ∀ x ∈ Ioo (-R) R, ∀ t ∈ Ioo 0 T,
      DifferentiableAt ℝ (fun s => u x s) t)
    (ha : ∀ x ∈ Ioo (-R) R, ∀ t ∈ Ioo 0 T, a x t ∈ Icc 0 Λ)
    (hpde : ∀ x ∈ Ioo (-R) R, ∀ t ∈ Ioo 0 T, 0 < u x t →
      deriv (fun s => u x s) t - a x t * deriv (deriv (fun y => u y t)) x ≤
        -c * u x t ^ 2) :
    ∀ t ∈ Ioc 0 T, ∀ x ∈ Icc (-R / 2) (R / 2),
      u x t ≤ 16 / (9 * c * t) + 64 * Λ / (c * R ^ 2) := by
  have hinner := quadratic_reaction_interior_upper_bound_of_reaction_on_pos hR hc hΛ
    (hcont.mono (fun p hp => ⟨hp.1, hp.2.1, hp.2.2.le⟩)) hu₁ hu₂ hut ha hpde
  intro t ht x hx
  rcases lt_or_eq_of_le ht.2 with hlt | heq
  · exact hinner t ⟨ht.1, hlt⟩ x hx
  subst t
  have hT : 0 < T := ht.1
  have hxR : x ∈ Icc (-R) R := ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hfilter : 𝓝[<] T ≤ 𝓝[Icc 0 T] T := by
    apply le_inf nhdsWithin_le_nhds
    apply le_principal_iff.mpr
    filter_upwards [Ioo_mem_nhdsLT hT] with s hs
    exact ⟨hs.1.le, hs.2.le⟩
  have huc : ContinuousOn (fun s => u x s) (Icc 0 T) :=
    hcont.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun s hs => ⟨hxR, hs⟩)
  have huT := (huc T ⟨hT.le, le_rfl⟩).tendsto.mono_left hfilter
  have hbc : ContinuousAt (fun s : ℝ => 16 / (9 * c * s) + 64 * Λ / (c * R ^ 2)) T :=
    (continuousAt_const.div (continuousAt_const.mul continuousAt_id)
      (by positivity : (9 : ℝ) * c * T ≠ 0)).add continuousAt_const
  exact le_of_tendsto_of_tendsto huT (hbc.tendsto.mono_left nhdsWithin_le_nhds)
    (by
      filter_upwards [Ioo_mem_nhdsLT hT] with s hs
      exact hinner s hs x hx)

theorem quadratic_reaction_interior_upper_bound_on_closed_time_interval
    {u a : ℝ → ℝ → ℝ} {R T c Λ : ℝ}
    (hR : 0 < R) (hc : 0 < c) (hΛ : 0 ≤ Λ)
    (hcont : ContinuousOn (fun p : ℝ × ℝ => u p.1 p.2) (Icc (-R) R ×ˢ Icc 0 T))
    (hu₁ : ∀ t ∈ Ioo 0 T, DifferentiableOn ℝ (fun x => u x t) (Ioo (-R) R))
    (hu₂ : ∀ t ∈ Ioo 0 T, DifferentiableOn ℝ (deriv (fun x => u x t)) (Ioo (-R) R))
    (hut : ∀ x ∈ Ioo (-R) R, ∀ t ∈ Ioo 0 T,
      DifferentiableAt ℝ (fun s => u x s) t)
    (ha : ∀ x ∈ Ioo (-R) R, ∀ t ∈ Ioo 0 T, a x t ∈ Icc 0 Λ)
    (hpde : ∀ x ∈ Ioo (-R) R, ∀ t ∈ Ioo 0 T,
      deriv (fun s => u x s) t - a x t * deriv (deriv (fun y => u y t)) x ≤
        -c * u x t ^ 2) :
    ∀ t ∈ Ioc 0 T, ∀ x ∈ Icc (-R / 2) (R / 2),
      u x t ≤ 16 / (9 * c * t) + 64 * Λ / (c * R ^ 2) := by
  exact quadratic_reaction_interior_upper_bound_on_closed_time_interval_of_reaction_on_pos
    hR hc hΛ hcont hu₁ hu₂ hut ha
    (fun x hx t ht _ => hpde x hx t ht)

private theorem quadratic_reaction_shift_le {c K D u : ℝ}
    (hc : 0 < c) (hK : 0 ≤ K) (hD : 0 ≤ D)
    (hu : 0 < u - (K / c + Real.sqrt (D / c))) :
    -c * u ^ 2 + K * u + D ≤ -c * (u - (K / c + Real.sqrt (D / c))) ^ 2 := by
  let q := Real.sqrt (D / c)
  let S := K / c + q
  have hq : 0 ≤ q := Real.sqrt_nonneg _
  have hq2 : c * q ^ 2 = D := by
    rw [Real.sq_sqrt (div_nonneg hD hc.le)]
    exact mul_div_cancel₀ D hc.ne'
  have hS : c * S = K + c * q := by
    dsimp [S]
    field_simp
  have hp : c * S ^ 2 - K * S - D = K * q := by
    nlinarith only [congrArg (fun z : ℝ => z * S) hS,
      congrArg (fun z : ℝ => z * q) hS, hq2]
  have hcross : 0 ≤ (2 * c * S - K) * (u - S) :=
    mul_nonneg (by nlinarith only [hS, hK, mul_nonneg hc.le hq]) hu.le
  change -c * u ^ 2 + K * u + D ≤ -c * (u - S) ^ 2
  nlinarith only [hp, hcross, mul_nonneg hK hq]

theorem quadratic_reaction_with_source_interior_upper_bound_on_closed_time_interval
    {u a : ℝ → ℝ → ℝ} {R T c Λ K D : ℝ}
    (hR : 0 < R) (hc : 0 < c) (hΛ : 0 ≤ Λ) (hK : 0 ≤ K) (hD : 0 ≤ D)
    (hcont : ContinuousOn (fun p : ℝ × ℝ => u p.1 p.2) (Icc (-R) R ×ˢ Icc 0 T))
    (hu₁ : ∀ t ∈ Ioo 0 T, DifferentiableOn ℝ (fun x => u x t) (Ioo (-R) R))
    (hu₂ : ∀ t ∈ Ioo 0 T, DifferentiableOn ℝ (deriv (fun x => u x t)) (Ioo (-R) R))
    (hut : ∀ x ∈ Ioo (-R) R, ∀ t ∈ Ioo 0 T,
      DifferentiableAt ℝ (fun s => u x s) t)
    (ha : ∀ x ∈ Ioo (-R) R, ∀ t ∈ Ioo 0 T, a x t ∈ Icc 0 Λ)
    (hpde : ∀ x ∈ Ioo (-R) R, ∀ t ∈ Ioo 0 T,
      deriv (fun s => u x s) t - a x t * deriv (deriv (fun y => u y t)) x ≤
        -c * u x t ^ 2 + K * u x t + D) :
    ∀ t ∈ Ioc 0 T, ∀ x ∈ Icc (-R / 2) (R / 2),
      u x t ≤ K / c + Real.sqrt (D / c) + 16 / (9 * c * t) + 64 * Λ / (c * R ^ 2) := by
  let S := K / c + Real.sqrt (D / c)
  have hb := quadratic_reaction_interior_upper_bound_on_closed_time_interval_of_reaction_on_pos
    (u := fun x t => u x t - S) (a := a) hR hc hΛ
    (hcont.sub continuousOn_const)
    (fun t ht => (hu₁ t ht).sub_const S)
    (fun t ht => by simpa only [deriv_sub_const_fun] using hu₂ t ht)
    (fun x hx t ht => (hut x hx t ht).sub_const S) ha
    (by
      intro x hx t ht hpos
      simp only [deriv_sub_const, deriv_sub_const_fun]
      exact (hpde x hx t ht).trans (quadratic_reaction_shift_le hc hK hD hpos))
  intro t ht x hx
  have h := hb t ht x hx
  dsimp only [S] at h
  linarith only [h]

theorem quadratic_reaction_with_source_interior_upper_bound
    {u a : ℝ → ℝ → ℝ} {R T c Λ K D : ℝ}
    (hR : 0 < R) (hc : 0 < c) (hΛ : 0 ≤ Λ) (hK : 0 ≤ K) (hD : 0 ≤ D)
    (hcont : ContinuousOn (fun p : ℝ × ℝ => u p.1 p.2) (Icc (-R) R ×ˢ Ico 0 T))
    (hu₁ : ∀ t ∈ Ioo 0 T, DifferentiableOn ℝ (fun x => u x t) (Ioo (-R) R))
    (hu₂ : ∀ t ∈ Ioo 0 T, DifferentiableOn ℝ (deriv (fun x => u x t)) (Ioo (-R) R))
    (hut : ∀ x ∈ Ioo (-R) R, ∀ t ∈ Ioo 0 T,
      DifferentiableAt ℝ (fun s => u x s) t)
    (ha : ∀ x ∈ Ioo (-R) R, ∀ t ∈ Ioo 0 T, a x t ∈ Icc 0 Λ)
    (hpde : ∀ x ∈ Ioo (-R) R, ∀ t ∈ Ioo 0 T,
      deriv (fun s => u x s) t - a x t * deriv (deriv (fun y => u y t)) x ≤
        -c * u x t ^ 2 + K * u x t + D) :
    ∀ t ∈ Ioo 0 T, ∀ x ∈ Icc (-R / 2) (R / 2),
      u x t ≤ K / c + Real.sqrt (D / c) + 16 / (9 * c * t) + 64 * Λ / (c * R ^ 2) := by
  intro t ht x hx
  have hsub {s : ℝ} (hs : s ∈ Ioo 0 t) : s ∈ Ioo 0 T := ⟨hs.1, hs.2.trans ht.2⟩
  exact quadratic_reaction_with_source_interior_upper_bound_on_closed_time_interval
    (T := t) hR hc hΛ hK hD
    (hcont.mono (fun p hp => ⟨hp.1, hp.2.1, hp.2.2.trans_lt ht.2⟩))
    (fun s hs => hu₁ s (hsub hs)) (fun s hs => hu₂ s (hsub hs))
    (fun y hy s hs => hut y hy s (hsub hs)) (fun y hy s hs => ha y hy s (hsub hs))
    (fun y hy s hs => hpde y hy s (hsub hs)) t ⟨ht.1, le_rfl⟩ x hx

end DifferentialGeometry.Analysis.Parabolic
