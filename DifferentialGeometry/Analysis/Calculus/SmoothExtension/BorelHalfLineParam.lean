import DifferentialGeometry.Analysis.Calculus.SmoothExtension.BorelHalfLine
import DifferentialGeometry.Analysis.Calculus.SmoothExtension.IteratedFDerivProdMatch
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.TangentCone.Prod
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Parametrized Borel half-line extension

This is the parameter-uniform generalization of `borel_halfLine_extend`. Given a family
`g : ℝ → E → F` that is jointly `C^∞` on the closed-half-line slab `Set.Ici 0 ×ˢ K` (with `K`
compact and `z₀` in its interior), we build a single function `gext : ℝ → E → F` that is jointly
`C^∞` at every point `(t₀, z₀)` and agrees with `g` for all `t ≥ 0` near `z₀`.

## Construction

Write `cₙ z := iteratedDerivWithin n (g · z) (Set.Ici 0) 0` for the one-sided `t`-jet of `g(·, z)`.
The first non-trivial fact (`param_jet_contDiffOn`) is that `cₙ` is `C^∞` in the parameter `z`,
obtained by inducting `ContDiffWithinAt.fderivWithin_apply` over the joint slice
`(z, t) ↦ iteratedDerivWithin n (g · z) (Set.Ici 0) t`.

We then run the Borel series jointly on `ℝ × E`: the `n`-th term is
`fₙ(t, z) = ((λₙ)⁻ⁿ · borelBumpMono n (λₙ t)) • (ρ z • cₙ z)`, where `ρ` is a smooth cutoff equal
to `1` at `z₀` and supported in `interior K` (this is where finite-dimensionality of `E` enters —
it is needed for a smooth compactly-supported bump), and `λₙ ≥ 1` is a rapidly increasing scale.
The scale is chosen (`paramScale`) to dominate `4ⁿ · Gₙ · (1 + Aₙ)`, where `Gₙ` bounds the
bump-monomial derivatives and `Aₙ` bounds all `z`-derivatives of `ρ · cₙ` (finite by compact
support). The key joint estimate `paramTerm_iteratedFDeriv_bound` then gives
`‖iteratedFDeriv ℝ k fₙ (t, z)‖ ≤ 2⁻ⁿ` for all `k < n`, uniformly in `(t, z)`, by expanding the
product via `norm_iteratedFDeriv_smul_le` and pre-composition with the coordinate projections.
Summability of these bounds feeds `contDiff_tsum`, so the series is globally `C^∞` on `ℝ × E`.

Away from the seam `t = 0` the extension `gext t z := if 0 ≤ t then g t z else ∑' n, fₙ(t, z)` is
`C^∞` because it locally agrees with either `g` (on the open upper half) or the smooth series (on
the open lower half).

## The seam

The seam case `t₀ = 0` is the *joint* analogue of `contDiff_if_le_of_jet_match` across the
hyperplane `{0} × E`: it requires that the globally-smooth series and `g` share their full joint
Taylor jet at `(0, z₀)`. The series matches `g`'s one-sided `t`-jet `cₙ` for every parameter `z`
near `z₀` by construction (`paramSeries_slice_iteratedDeriv_zero`, the parametrized analogue of
`borel_jet_realize`'s jet identity, fibre by fibre), so on the common closed slab `Ici 0 ×ˢ V` both
`Φ` and `uncurry g` are `C∞` and share their entire one-sided `t`-jet at every seam parameter.
`Analysis.iteratedFDerivWithin_prod_match` turns that common `t`-jet into the matching joint iterated
Fréchet derivative, closing the seam coefficient match. The file is `sorry`-free.
-/

noncomputable section
open Set Filter Topology
open scoped ContDiff Pointwise

namespace DifferentialGeometry
namespace Analysis

section Bridge

variable {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Joint smoothness of the partial `t`-jet of a jointly-smooth family. If `uncurry g` is `C∞`
on `Ici 0 ×ˢ U`, then `(z, t) ↦ iteratedDerivWithin n (g · z) (Ici 0) t` is `C∞`
on `U ×ˢ Ici 0`, for every order `n`. -/
private theorem param_iteratedDerivWithin_contDiffOn
    (g : ℝ → E → F) (U : Set E)
    (hg : ContDiffOn ℝ ∞ (Function.uncurry g) ((Set.Ici (0:ℝ)) ×ˢ U)) :
    ∀ n : ℕ, ContDiffOn ℝ ∞
      (fun p : E × ℝ => iteratedDerivWithin n (fun s => g s p.1) (Set.Ici 0) p.2)
      (U ×ˢ (Set.Ici (0:ℝ))) := by
  have hgswap : ContDiffOn ℝ ∞ (fun p : E × ℝ => g p.2 p.1) (U ×ˢ Set.Ici 0) := by
    have hswap : ContDiffOn ℝ ∞ (fun p : E × ℝ => (p.2, p.1)) (U ×ˢ Set.Ici 0) :=
      (contDiff_snd.prodMk contDiff_fst).contDiffOn
    have hmaps : Set.MapsTo (fun p : E × ℝ => (p.2, p.1)) (U ×ˢ Set.Ici 0) (Set.Ici 0 ×ˢ U) := by
      intro p hp; exact ⟨hp.2, hp.1⟩
    exact hg.comp hswap hmaps
  intro n
  induction n with
  | zero =>
    simp only [iteratedDerivWithin_zero]
    exact hgswap
  | succ n IH =>
    have hUDt : UniqueDiffOn ℝ (Set.Ici (0:ℝ)) := uniqueDiffOn_Ici 0
    have hrw : ∀ p : E × ℝ, p ∈ U ×ˢ Set.Ici (0:ℝ) →
        iteratedDerivWithin (n+1) (fun s => g s p.1) (Set.Ici 0) p.2 =
          fderivWithin ℝ (fun s => iteratedDerivWithin n (fun s => g s p.1) (Set.Ici 0) s)
            (Set.Ici 0) p.2 (1:ℝ) := by
      intro p _
      rw [iteratedDerivWithin_succ, derivWithin]
    refine ContDiffOn.congr ?_ hrw
    intro q hq
    have hf : ContDiffWithinAt ℝ ∞
        (Function.uncurry (fun (p : E × ℝ) (s : ℝ) =>
          iteratedDerivWithin n (fun s => g s p.1) (Set.Ici 0) s))
        ((U ×ˢ Set.Ici (0:ℝ)) ×ˢ Set.Ici 0) (q, q.2) := by
      have hproj : ContDiffWithinAt ℝ ∞ (fun r : (E × ℝ) × ℝ => (r.1.1, r.2))
          ((U ×ˢ Set.Ici (0:ℝ)) ×ˢ Set.Ici 0) (q, q.2) :=
        ((contDiff_fst.fst).prodMk contDiff_snd).contDiffWithinAt
      have hmaps : Set.MapsTo (fun r : (E × ℝ) × ℝ => (r.1.1, r.2))
          ((U ×ˢ Set.Ici (0:ℝ)) ×ˢ Set.Ici 0) (U ×ˢ Set.Ici 0) := by
        intro r hr; exact ⟨hr.1.1, hr.2⟩
      exact (IH.contDiffWithinAt ⟨hq.1, hq.2⟩).comp (q, q.2) hproj hmaps
    have hgsec : ContDiffWithinAt ℝ ∞ (fun p : E × ℝ => p.2) (U ×ˢ Set.Ici (0:ℝ)) q :=
      contDiff_snd.contDiffWithinAt
    have hksec : ContDiffWithinAt ℝ ∞ (fun _ : E × ℝ => (1:ℝ)) (U ×ˢ Set.Ici (0:ℝ)) q :=
      contDiffWithinAt_const
    have hst : (U ×ˢ Set.Ici (0:ℝ)) ⊆ (fun p : E × ℝ => p.2) ⁻¹' Set.Ici 0 := fun p hp => hp.2
    have hmn : (∞ : WithTop ℕ∞) + 1 ≤ ∞ := by simp
    exact ContDiffWithinAt.fderivWithin_apply hf hgsec hksec hUDt hmn hq hst

/-- The `t = 0` slice: `z ↦ iteratedDerivWithin n (g · z) (Ici 0) 0` is `C∞` on `U`. -/
private theorem param_jet_contDiffOn
    (g : ℝ → E → F) (U : Set E)
    (hg : ContDiffOn ℝ ∞ (Function.uncurry g) ((Set.Ici (0:ℝ)) ×ˢ U)) (n : ℕ) :
    ContDiffOn ℝ ∞ (fun z : E => iteratedDerivWithin n (fun s => g s z) (Set.Ici 0) 0) U := by
  have hsec : ContDiffOn ℝ ∞ (fun z : E => (z, (0:ℝ))) U :=
    (contDiff_id.prodMk contDiff_const).contDiffOn
  have hmaps : Set.MapsTo (fun z : E => (z, (0:ℝ))) U (U ×ˢ Set.Ici 0) :=
    fun z hz => ⟨hz, Set.self_mem_Ici⟩
  exact (param_iteratedDerivWithin_contDiffOn g U hg n).comp hsec hmaps

end Bridge

section Engine

variable {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A uniform-over-`j ≤ n` global bound on the iterated Fréchet derivatives of a compactly
supported `C∞` coefficient `a : E → F`. -/
private theorem param_coeff_deriv_bound (a : E → F) (ha : ContDiff ℝ ∞ a)
    (hsupp : HasCompactSupport a) (n : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ j ≤ n, ∀ z : E, ‖iteratedFDeriv ℝ j a z‖ ≤ A := by
  have hbnd : ∀ j, ∃ C : ℝ, ∀ z : E, ‖iteratedFDeriv ℝ j a z‖ ≤ C := by
    intro j
    have hcs : HasCompactSupport (iteratedFDeriv ℝ j a) := hsupp.iteratedFDeriv j
    have hcont : Continuous (iteratedFDeriv ℝ j a) :=
      ha.continuous_iteratedFDeriv (by exact_mod_cast le_top : (j : WithTop ℕ∞) ≤ ∞)
    obtain ⟨C, hC⟩ := hcs.exists_bound_of_continuous hcont
    exact ⟨C, hC⟩
  choose C hC using hbnd
  refine ⟨(Finset.range (n + 1)).sup' (by simp) (fun j => max (C j) 0), ?_, ?_⟩
  · exact le_trans (le_max_right _ _)
      (Finset.le_sup' (fun j => max (C j) 0) (by simp : (0 : ℕ) ∈ Finset.range (n + 1)))
  · intro j hj z
    refine le_trans (hC j z) ?_
    refine le_trans (le_max_left (C j) 0) ?_
    exact Finset.le_sup' (fun j => max (C j) 0)
      (Finset.mem_range.2 (Nat.lt_succ_of_le hj))

variable (a : ℕ → E → F)
    (ha : ∀ n, ContDiff ℝ ∞ (a n)) (hsupp : ∀ n, HasCompactSupport (a n))

/-- The scale `λₙ ≥ 1` for the `n`-th parametrized term: large enough that the joint
`k`-th derivative (`k < n`) of the term is `≤ 2⁻ⁿ`. It dominates `4ⁿ · Gₙ · (1 + Aₙ)`, where
`Gₙ` bounds the bump-monomial derivatives and `Aₙ` bounds the `z`-derivatives of `a n`. -/
private def paramScale (n : ℕ) : ℝ :=
  max 1 ((4:ℝ) ^ n * Classical.choose (borelBumpMono_deriv_bound n) *
    (1 + Classical.choose (param_coeff_deriv_bound (a n) (ha n) (hsupp n) n)))

private theorem one_le_paramScale (n : ℕ) : 1 ≤ paramScale a ha hsupp n :=
  le_max_left _ _

private theorem paramScale_pos (n : ℕ) : 0 < paramScale a ha hsupp n :=
  lt_of_lt_of_le one_pos (one_le_paramScale a ha hsupp n)

/-- The `n`-th parametrized Borel term on `ℝ × E`:
`fₙ(t,z) = ((λₙ)⁻ⁿ · borelBumpMono n (λₙ t)) • a n z`. The `t`-scalar is exactly the fixed-case
scalar; the constant vector is replaced by the smooth coefficient `a n z`. -/
private def paramTerm (n : ℕ) (p : ℝ × E) : F :=
  ((paramScale a ha hsupp n)⁻¹ ^ n * borelBumpMono n (paramScale a ha hsupp n * p.1)) • a n p.2

private theorem paramTerm_contDiff (n : ℕ) : ContDiff ℝ ∞ (paramTerm a ha hsupp n) := by
  have hb : ContDiff ℝ ∞ (fun p : ℝ × E =>
      (paramScale a ha hsupp n)⁻¹ ^ n * borelBumpMono n (paramScale a ha hsupp n * p.1)) :=
    contDiff_const.mul ((borelBumpMono_comp_smul_contDiff n (paramScale a ha hsupp n)).comp
      contDiff_fst)
  have ha' : ContDiff ℝ ∞ (fun p : ℝ × E => a n p.2) := (ha n).comp contDiff_snd
  exact hb.smul ha'

/-- The `t`-scalar of the `n`-th parametrized term:
`sₙ(t) = (λₙ)⁻ⁿ · borelBumpMono n (λₙ t)`. -/
private def paramScalar (n : ℕ) (t : ℝ) : ℝ :=
  (paramScale a ha hsupp n)⁻¹ ^ n * borelBumpMono n (paramScale a ha hsupp n * t)

private theorem paramScalar_contDiff (n : ℕ) : ContDiff ℝ ∞ (paramScalar a ha hsupp n) :=
  contDiff_const.mul (borelBumpMono_comp_smul_contDiff n (paramScale a ha hsupp n))

private theorem paramScalar_hasCompactSupport (n : ℕ) :
    HasCompactSupport (paramScalar a ha hsupp n) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (K := Set.Icc (-(2 / paramScale a ha hsupp n)) (2 / paramScale a ha hsupp n)) isCompact_Icc
  intro t ht
  by_contra hmem
  apply ht
  have hL0 : 0 < paramScale a ha hsupp n := paramScale_pos a ha hsupp n
  have h2 : 2 ≤ (paramScale a ha hsupp n * t) ^ 2 := by
    rcases not_and_or.1 hmem with h | h
    · have ht' : t < -(2 / paramScale a ha hsupp n) := lt_of_not_ge h
      have hlt : paramScale a ha hsupp n * t <
          paramScale a ha hsupp n * (-(2 / paramScale a ha hsupp n)) :=
        mul_lt_mul_of_pos_left ht' hL0
      rw [mul_neg, mul_div_cancel₀ _ hL0.ne'] at hlt
      nlinarith
    · have ht' : 2 / paramScale a ha hsupp n < t := lt_of_not_ge h
      have hlt : paramScale a ha hsupp n * (2 / paramScale a ha hsupp n) <
          paramScale a ha hsupp n * t := mul_lt_mul_of_pos_left ht' hL0
      rw [mul_div_cancel₀ _ hL0.ne'] at hlt
      nlinarith
  simp only [paramScalar, borelBumpMono, borelCutoff_eq_zero h2, zero_mul, zero_div, mul_zero]

/-- Pointwise iterated derivative of the `t`-scalar. -/
private theorem paramScalar_iteratedDeriv (n i : ℕ) (t : ℝ) :
    iteratedDeriv i (paramScalar a ha hsupp n) t =
      (paramScale a ha hsupp n)⁻¹ ^ n * (paramScale a ha hsupp n) ^ i *
        iteratedDeriv i (borelBumpMono n) (paramScale a ha hsupp n * t) := by
  set L : ℝ := paramScale a ha hsupp n with hLdef
  have hcd : ContDiffAt ℝ i (fun s => borelBumpMono n (L * s)) t :=
    (borelBumpMono_comp_smul_contDiff (N := (i : ℕ∞)) n L).contDiffAt
  have hconst : iteratedDeriv i (paramScalar a ha hsupp n) t =
      L⁻¹ ^ n • iteratedDeriv i (fun s => borelBumpMono n (L * s)) t := by
    have := iteratedDeriv_const_smul (𝕜 := ℝ) (R := ℝ) (n := i) (x := t)
      (f := fun s => borelBumpMono n (L * s)) hcd (L⁻¹ ^ n)
    simpa only [paramScalar, hLdef, Pi.smul_apply, smul_eq_mul] using this
  rw [hconst]
  have hcomp : iteratedDeriv i (fun s => borelBumpMono n (L * s)) t =
      L ^ i • iteratedDeriv i (borelBumpMono n) (L * t) := by
    have h := iteratedDeriv_comp_const_smul (n := i) (f := borelBumpMono n)
      (borelBumpMono_contDiff (N := (i : ℕ∞)) n) L
    exact congrFun h t
  rw [hcomp]; simp only [smul_eq_mul]; ring

/-- For `i < n`, the `i`-th derivative of the `t`-scalar is bounded by `Gₙ / λₙ`, where `Gₙ` is
the bump-monomial derivative bound. -/
private theorem paramScalar_iteratedDeriv_bound {n i : ℕ} (hin : i < n) (t : ℝ) :
    ‖iteratedDeriv i (paramScalar a ha hsupp n) t‖ ≤
      Classical.choose (borelBumpMono_deriv_bound n) / paramScale a ha hsupp n := by
  set G : ℝ := Classical.choose (borelBumpMono_deriv_bound n) with hGdef
  have hGspec := Classical.choose_spec (borelBumpMono_deriv_bound n)
  rw [← hGdef] at hGspec
  obtain ⟨hGnn, hGbound⟩ := hGspec
  set L : ℝ := paramScale a ha hsupp n with hLdef
  have hL1 : 1 ≤ L := one_le_paramScale a ha hsupp n
  have hL0 : 0 < L := paramScale_pos a ha hsupp n
  rw [paramScalar_iteratedDeriv]
  have hD : ‖iteratedDeriv i (borelBumpMono n) (L * t)‖ ≤ G := hGbound i (le_of_lt hin) (L * t)
  have hpow : L⁻¹ ^ n * L ^ i ≤ L⁻¹ := by
    rw [inv_pow, inv_mul_le_iff₀ (by positivity)]
    have hrw : L ^ n * L⁻¹ = L ^ (n - 1) := by
      have : L ^ n = L ^ (n - 1) * L := by
        rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ n)]
      rw [this, mul_assoc, mul_inv_cancel₀ hL0.ne', mul_one]
    rw [hrw]; exact pow_le_pow_right₀ hL1 (by omega)
  have hcoeff_nn : (0:ℝ) ≤ L⁻¹ ^ n * L ^ i := by positivity
  rw [show L⁻¹ ^ n * L ^ i * iteratedDeriv i (borelBumpMono n) (L * t)
      = (L⁻¹ ^ n * L ^ i) • iteratedDeriv i (borelBumpMono n) (L * t) from by
        rw [smul_eq_mul], norm_smul, Real.norm_eq_abs, abs_of_nonneg hcoeff_nn]
  calc (L⁻¹ ^ n * L ^ i) * ‖iteratedDeriv i (borelBumpMono n) (L * t)‖
      ≤ L⁻¹ * G := mul_le_mul hpow hD (norm_nonneg _) (by positivity)
    _ = G / L := by rw [inv_mul_eq_div]

/-- Pre-composing with the first projection does not increase the iterated-derivative norm. -/
private theorem norm_iteratedFDeriv_comp_fst_le {b : ℝ → F} (hb : ContDiff ℝ ∞ b) (i : ℕ)
    (p : ℝ × E) : ‖iteratedFDeriv ℝ i (fun q : ℝ × E => b q.1) p‖ ≤ ‖iteratedFDeriv ℝ i b p.1‖ := by
  have hcomp : (fun q : ℝ × E => b q.1) = b ∘ (ContinuousLinearMap.fst ℝ ℝ E) := rfl
  rw [hcomp, (ContinuousLinearMap.fst ℝ ℝ E).iteratedFDeriv_comp_right hb p
    (by exact_mod_cast le_top : (i : WithTop ℕ∞) ≤ ∞)]
  refine le_trans (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _) ?_
  have hfst : ‖ContinuousLinearMap.fst ℝ ℝ E‖ ≤ 1 := ContinuousLinearMap.norm_fst_le ℝ ℝ E
  have hprod : ∏ _j : Fin i, ‖ContinuousLinearMap.fst ℝ ℝ E‖ ≤ 1 := by
    calc ∏ _j : Fin i, ‖ContinuousLinearMap.fst ℝ ℝ E‖ ≤ ∏ _j : Fin i, (1:ℝ) :=
          Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun _ _ => hfst)
      _ = 1 := by simp
  have hpval : (ContinuousLinearMap.fst ℝ ℝ E) p = p.1 := rfl
  rw [hpval]
  calc ‖iteratedFDeriv ℝ i b p.1‖ * ∏ _j : Fin i, ‖ContinuousLinearMap.fst ℝ ℝ E‖
      ≤ ‖iteratedFDeriv ℝ i b p.1‖ * 1 :=
        mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
    _ = ‖iteratedFDeriv ℝ i b p.1‖ := mul_one _

/-- Pre-composing with the second projection does not increase the iterated-derivative norm. -/
private theorem norm_iteratedFDeriv_comp_snd_le {b : E → F} (hb : ContDiff ℝ ∞ b) (j : ℕ)
    (p : ℝ × E) : ‖iteratedFDeriv ℝ j (fun q : ℝ × E => b q.2) p‖ ≤ ‖iteratedFDeriv ℝ j b p.2‖ := by
  have hcomp : (fun q : ℝ × E => b q.2) = b ∘ (ContinuousLinearMap.snd ℝ ℝ E) := rfl
  rw [hcomp, (ContinuousLinearMap.snd ℝ ℝ E).iteratedFDeriv_comp_right hb p
    (by exact_mod_cast le_top : (j : WithTop ℕ∞) ≤ ∞)]
  refine le_trans (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _) ?_
  have hsnd : ‖ContinuousLinearMap.snd ℝ ℝ E‖ ≤ 1 := ContinuousLinearMap.norm_snd_le ℝ ℝ E
  have hprod : ∏ _j : Fin j, ‖ContinuousLinearMap.snd ℝ ℝ E‖ ≤ 1 := by
    calc ∏ _j : Fin j, ‖ContinuousLinearMap.snd ℝ ℝ E‖ ≤ ∏ _j : Fin j, (1:ℝ) :=
          Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun _ _ => hsnd)
      _ = 1 := by simp
  have hpval : (ContinuousLinearMap.snd ℝ ℝ E) p = p.2 := rfl
  rw [hpval]
  calc ‖iteratedFDeriv ℝ j b p.2‖ * ∏ _j : Fin j, ‖ContinuousLinearMap.snd ℝ ℝ E‖
      ≤ ‖iteratedFDeriv ℝ j b p.2‖ * 1 :=
        mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
    _ = ‖iteratedFDeriv ℝ j b p.2‖ := mul_one _

/-- **The joint Borel decay estimate.** By the scale choice, the joint `k`-th Fréchet derivative
of the `n`-th parametrized term on `ℝ × E` is bounded by `2⁻ⁿ` whenever `k < n`, uniformly in
`(t, z)`. -/
private theorem paramTerm_iteratedFDeriv_bound {n k : ℕ} (hkn : k < n) (p : ℝ × E) :
    ‖iteratedFDeriv ℝ k (paramTerm a ha hsupp n) p‖ ≤ (2 : ℝ)⁻¹ ^ n := by
  set L : ℝ := paramScale a ha hsupp n with hLdef
  set G : ℝ := Classical.choose (borelBumpMono_deriv_bound n) with hGdef
  set A : ℝ := Classical.choose (param_coeff_deriv_bound (a n) (ha n) (hsupp n) n) with hAdef
  have hGnn : 0 ≤ G := (Classical.choose_spec (borelBumpMono_deriv_bound n)).1
  have hAspec := Classical.choose_spec (param_coeff_deriv_bound (a n) (ha n) (hsupp n) n)
  rw [← hAdef] at hAspec
  obtain ⟨hAnn, hAbound⟩ := hAspec
  have hL0 : 0 < L := paramScale_pos a ha hsupp n
  have hLmax : (4:ℝ) ^ n * G * (1 + A) ≤ L := le_max_right _ _
  -- paramTerm n = (paramScalar∘fst) • (a∘snd)
  have hterm_eq : paramTerm a ha hsupp n =
      fun q : ℝ × E => (fun r : ℝ × E => paramScalar a ha hsupp n r.1) q •
        (fun r : ℝ × E => a n r.2) q := by
    funext q; rfl
  rw [hterm_eq]
  have hsmul := norm_iteratedFDeriv_smul_le (𝕜 := ℝ) (𝕜' := ℝ)
    (f := fun r : ℝ × E => paramScalar a ha hsupp n r.1)
    (g := fun r : ℝ × E => a n r.2)
    ((paramScalar_contDiff a ha hsupp n).comp contDiff_fst)
    ((ha n).comp contDiff_snd) p (by exact_mod_cast le_top : (k : WithTop ℕ∞) ≤ ∞)
  refine le_trans hsmul ?_
  -- Bound each summand by C(k,i) * (G/L) * A.
  have hsummand : ∀ i ∈ Finset.range (k + 1),
      (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun r : ℝ × E => paramScalar a ha hsupp n r.1) p‖ *
        ‖iteratedFDeriv ℝ (k - i) (fun r : ℝ × E => a n r.2) p‖
      ≤ (k.choose i : ℝ) * (G / L) * A := by
    intro i hi
    have hik : i ≤ k := by have := Finset.mem_range.1 hi; omega
    have hilt : i < n := lt_of_le_of_lt hik hkn
    have hib : ‖iteratedFDeriv ℝ i (fun r : ℝ × E => paramScalar a ha hsupp n r.1) p‖ ≤ G / L := by
      refine le_trans (norm_iteratedFDeriv_comp_fst_le (paramScalar_contDiff a ha hsupp n) i p) ?_
      rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
      have hb := paramScalar_iteratedDeriv_bound a ha hsupp hilt p.1
      rwa [← hLdef, ← hGdef] at hb
    have hjb : ‖iteratedFDeriv ℝ (k - i) (fun r : ℝ × E => a n r.2) p‖ ≤ A := by
      refine le_trans (norm_iteratedFDeriv_comp_snd_le (ha n) (k - i) p) ?_
      exact hAbound (k - i) (by omega) p.2
    gcongr
  refine le_trans (Finset.sum_le_sum hsummand) ?_
  -- ∑ C(k,i) * (G/L) * A = 2^k * (G/L) * A
  have hsum_eq : ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * (G / L) * A
      = (2:ℝ) ^ k * (G / L) * A := by
    rw [← Finset.sum_mul, ← Finset.sum_mul]
    congr 2
    rw [← Nat.cast_sum, Nat.sum_range_choose]
    push_cast; ring
  rw [hsum_eq]
  -- Now finish: 2^k * (G/L) * A ≤ 2⁻ⁿ.
  rcases eq_or_lt_of_le hGnn with hG0 | hGpos
  · rw [← hG0]; simp
  · have h1A : (0:ℝ) < 1 + A := by positivity
    have h2n : (0:ℝ) < (2:ℝ) ^ n := by positivity
    -- Step 1: G / L ≤ 1 / (4^n * (1 + A)).
    have hGL : G / L ≤ 1 / ((4:ℝ) ^ n * (1 + A)) := by
      rw [div_le_div_iff₀ hL0 (by positivity)]
      have hrw : G * ((4:ℝ) ^ n * (1 + A)) = (4:ℝ) ^ n * G * (1 + A) := by ring
      rw [hrw, one_mul]; exact hLmax
    have h2kn : (2:ℝ) ^ k ≤ (2:ℝ) ^ n := pow_le_pow_right₀ (by norm_num) (by omega)
    have h4n : (4:ℝ) ^ n = (2:ℝ) ^ n * (2:ℝ) ^ n := by rw [← mul_pow]; norm_num
    -- Reduce `2⁻ⁿ` to `1 / 2^n` and clear denominators.
    rw [inv_pow, inv_eq_one_div, le_div_iff₀ h2n]
    have hstep1 : (2:ℝ) ^ k * (G / L) * A * (2:ℝ) ^ n
        ≤ (2:ℝ) ^ n * (1 / ((4:ℝ) ^ n * (1 + A))) * A * (2:ℝ) ^ n := by
      have hAnn' : (0:ℝ) ≤ A := hAnn
      gcongr
    refine le_trans hstep1 ?_
    have hsimp : (2:ℝ) ^ n * (1 / ((4:ℝ) ^ n * (1 + A))) * A * (2:ℝ) ^ n = A / (1 + A) := by
      rw [h4n]; field_simp
    rw [hsimp, div_le_one h1A]; linarith

/-- For every derivative order `k`, the `k`-th joint Fréchet derivative of the `n`-th term is
globally bounded (compact support + continuity). -/
private theorem paramTerm_hasCompactSupport (n : ℕ) :
    HasCompactSupport (paramTerm a ha hsupp n) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (K := tsupport (paramScalar a ha hsupp n) ×ˢ tsupport (a n))
    ((paramScalar_hasCompactSupport a ha hsupp n).prod (hsupp n))
  intro p hp
  rw [Function.mem_support] at hp
  have hterm_eq : paramTerm a ha hsupp n p = paramScalar a ha hsupp n p.1 • a n p.2 := rfl
  refine ⟨subset_tsupport _ ?_, subset_tsupport _ ?_⟩
  · intro hz
    apply hp
    rw [hterm_eq, hz, zero_smul]
  · intro hz
    apply hp
    rw [hterm_eq, hz, smul_zero]

private theorem paramTerm_iteratedFDeriv_global_bound (n k : ℕ) :
    ∃ B : ℝ, ∀ p : ℝ × E, ‖iteratedFDeriv ℝ k (paramTerm a ha hsupp n) p‖ ≤ B := by
  have hcs : HasCompactSupport (iteratedFDeriv ℝ k (paramTerm a ha hsupp n)) :=
    (paramTerm_hasCompactSupport a ha hsupp n).iteratedFDeriv k
  have hcont : Continuous (iteratedFDeriv ℝ k (paramTerm a ha hsupp n)) :=
    (paramTerm_contDiff a ha hsupp n).continuous_iteratedFDeriv
      (by exact_mod_cast le_top : (k : WithTop ℕ∞) ≤ ∞)
  obtain ⟨B, hB⟩ := hcs.exists_bound_of_continuous hcont
  exact ⟨B, hB⟩

/-- Summable dominating function for the parametrized Borel series: `2⁻ⁿ` for `k < n`, and a
global bound otherwise. -/
private def paramDomBound (k n : ℕ) : ℝ :=
  if k < n then (2 : ℝ)⁻¹ ^ n
  else Classical.choose (paramTerm_iteratedFDeriv_global_bound a ha hsupp n k)

private theorem paramDomBound_summable (k : ℕ) : Summable (paramDomBound a ha hsupp k) := by
  have hgeom : Summable (fun n : ℕ => (2 : ℝ)⁻¹ ^ n) := by
    simpa only [one_div] using summable_geometric_two
  refine Summable.congr_cofinite hgeom ?_
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [eventually_gt_atTop k] with n hn
  rw [paramDomBound, if_pos hn]

private theorem paramDomBound_bound (k n : ℕ) (p : ℝ × E) :
    ‖iteratedFDeriv ℝ k (paramTerm a ha hsupp n) p‖ ≤ paramDomBound a ha hsupp k n := by
  rw [paramDomBound]
  by_cases hkn : k < n
  · rw [if_pos hkn]; exact paramTerm_iteratedFDeriv_bound a ha hsupp hkn p
  · rw [if_neg hkn]
    exact Classical.choose_spec (paramTerm_iteratedFDeriv_global_bound a ha hsupp n k) p

/-- Near `0`, the `t`-scalar `sₙ` of the `n`-th term equals `tⁿ / n!`, so its `k`-th derivative at
`0` is `1` if `n = k` and `0` otherwise. -/
private theorem paramScalar_iteratedDeriv_zero (n k : ℕ) :
    iteratedDeriv k (paramScalar a ha hsupp n) 0 = if n = k then (1 : ℝ) else 0 := by
  have hL0 : 0 < paramScale a ha hsupp n := paramScale_pos a ha hsupp n
  have hev : paramScalar a ha hsupp n =ᶠ[𝓝 (0 : ℝ)]
      fun t => (paramScale a ha hsupp n)⁻¹ ^ n *
        ((paramScale a ha hsupp n * t) ^ n / (Nat.factorial n : ℝ)) := by
    refine eventuallyEq_of_mem (Ioo_mem_nhds (a := -(1 / paramScale a ha hsupp n))
      (b := 1 / paramScale a ha hsupp n) (by simpa using by positivity) (by positivity)) ?_
    intro t ht
    have h1 : (paramScale a ha hsupp n * t) ^ 2 ≤ 1 := by
      rw [mul_pow]
      have htabs : |t| < 1 / paramScale a ha hsupp n := by
        rw [abs_lt]; exact ⟨by simpa using ht.1, ht.2⟩
      have ht2 : t ^ 2 ≤ (1 / paramScale a ha hsupp n) ^ 2 := by
        rw [← sq_abs t]; exact pow_le_pow_left₀ (abs_nonneg t) htabs.le 2
      calc paramScale a ha hsupp n ^ 2 * t ^ 2
          ≤ paramScale a ha hsupp n ^ 2 * (1 / paramScale a ha hsupp n) ^ 2 :=
            mul_le_mul_of_nonneg_left ht2 (by positivity)
        _ = 1 := by field_simp
    simp only [paramScalar, borelBumpMono, borelCutoff_eq_one h1, one_mul]
  rw [Filter.EventuallyEq.iteratedDeriv_eq k hev]
  have hcd : ContDiffAt ℝ k
      (fun t => (paramScale a ha hsupp n)⁻¹ ^ n *
        ((paramScale a ha hsupp n * t) ^ n / (Nat.factorial n : ℝ))) 0 := by
    fun_prop
  have hfun : (fun t => (paramScale a ha hsupp n)⁻¹ ^ n *
      ((paramScale a ha hsupp n * t) ^ n / (Nat.factorial n : ℝ))) =
      (fun t => ((paramScale a ha hsupp n)⁻¹ ^ n * (paramScale a ha hsupp n) ^ n /
        (Nat.factorial n : ℝ)) * t ^ n) := by
    funext t; rw [mul_pow]; ring
  rw [hfun]
  simp only [iteratedDeriv_const_mul_field, iteratedDeriv_fun_pow_zero]
  have hLn : (paramScale a ha hsupp n)⁻¹ ^ n * paramScale a ha hsupp n ^ n = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hL0.ne', one_pow]
  rcases eq_or_ne n k with h | h
  · subst h
    rw [if_pos rfl, if_pos rfl]
    have hfac : (Nat.factorial n : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
    rw [div_mul_cancel₀ _ hfac, hLn]
  · rw [if_neg (fun h' => h h'.symm), if_neg h]
    simp

/-- The `n`-th term restricted to the fibre over `w` is the scalar `sₙ` times the vector `a n w`. -/
private theorem paramTerm_slice_eq (n : ℕ) (w : E) :
    (fun t => paramTerm a ha hsupp n (t, w)) = fun t => paramScalar a ha hsupp n t • a n w :=
  rfl

private theorem paramTerm_slice_contDiff (n : ℕ) (w : E) :
    ContDiff ℝ ∞ (fun t => paramTerm a ha hsupp n (t, w)) := by
  rw [paramTerm_slice_eq]
  exact (paramScalar_contDiff a ha hsupp n).smul_const (a n w)

/-- The `k`-th derivative at `0` of the `n`-th term over the fibre `w`: `a n w` if `n = k`, else `0`. -/
private theorem paramTerm_slice_iteratedDeriv_zero (n k : ℕ) (w : E) :
    iteratedDeriv k (fun t => paramTerm a ha hsupp n (t, w)) 0 =
      (if n = k then (1 : ℝ) else 0) • a n w := by
  rw [paramTerm_slice_eq,
    iteratedDeriv_smul_const ((paramScalar_contDiff a ha hsupp n).contDiffAt.of_le
      (by exact_mod_cast le_top)),
    paramScalar_iteratedDeriv_zero]

/-- A uniform bound on the fibre-slice term derivatives that dominates the `k`-th derivative of the
`n`-th fibre-slice term, summably in `n`: `2⁻ⁿ` for `k < n` and a global bound otherwise. -/
private theorem paramTerm_slice_iteratedFDeriv_bound {n k : ℕ} (hkn : k < n) (w : E) (t : ℝ) :
    ‖iteratedFDeriv ℝ k (fun s => paramTerm a ha hsupp n (s, w)) t‖ ≤ (2 : ℝ)⁻¹ ^ n := by
  set L : ℝ := paramScale a ha hsupp n with hLdef
  set G : ℝ := Classical.choose (borelBumpMono_deriv_bound n) with hGdef
  set A : ℝ := Classical.choose (param_coeff_deriv_bound (a n) (ha n) (hsupp n) n) with hAdef
  have hGnn : 0 ≤ G := (Classical.choose_spec (borelBumpMono_deriv_bound n)).1
  have hAspec := Classical.choose_spec (param_coeff_deriv_bound (a n) (ha n) (hsupp n) n)
  rw [← hAdef] at hAspec
  obtain ⟨hAnn, hAbound⟩ := hAspec
  have hL0 : 0 < L := paramScale_pos a ha hsupp n
  have hLmax : (4 : ℝ) ^ n * G * (1 + A) ≤ L := le_max_right _ _
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, paramTerm_slice_eq,
    iteratedDeriv_smul_const ((paramScalar_contDiff a ha hsupp n).contDiffAt.of_le
      (by exact_mod_cast le_top)), norm_smul]
  -- The scalar derivative is `≤ G/L`; the constant vector is `≤ A`.
  have hsb : ‖iteratedDeriv k (paramScalar a ha hsupp n) t‖ ≤ G / L := by
    have hb := paramScalar_iteratedDeriv_bound a ha hsupp hkn t
    rwa [← hLdef, ← hGdef] at hb
  have hab : ‖a n w‖ ≤ A := by
    have h0 := hAbound 0 (Nat.zero_le n) w
    rwa [norm_iteratedFDeriv_zero] at h0
  have hprod : ‖iteratedDeriv k (paramScalar a ha hsupp n) t‖ * ‖a n w‖ ≤ (G / L) * A :=
    mul_le_mul hsb hab (norm_nonneg _) (by positivity)
  refine le_trans hprod ?_
  -- `(G/L) * A ≤ 2⁻ⁿ` by the scale choice, exactly as in `paramTerm_iteratedFDeriv_bound`.
  rcases eq_or_lt_of_le hGnn with hG0 | hGpos
  · rw [← hG0]; simp
  · have h1A : (0 : ℝ) < 1 + A := by positivity
    have h2n : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
    have hGL : G / L ≤ 1 / ((4 : ℝ) ^ n * (1 + A)) := by
      rw [div_le_div_iff₀ hL0 (by positivity)]
      have hrw : G * ((4 : ℝ) ^ n * (1 + A)) = (4 : ℝ) ^ n * G * (1 + A) := by ring
      rw [hrw, one_mul]; exact hLmax
    have h4n : (4 : ℝ) ^ n = (2 : ℝ) ^ n * (2 : ℝ) ^ n := by rw [← mul_pow]; norm_num
    rw [inv_pow, inv_eq_one_div, le_div_iff₀ h2n]
    have hstep : G / L * A * (2 : ℝ) ^ n ≤ (1 / ((4 : ℝ) ^ n * (1 + A))) * A * (2 : ℝ) ^ n := by
      gcongr
    refine le_trans hstep ?_
    have heq : (1 / ((4 : ℝ) ^ n * (1 + A))) * A * (2 : ℝ) ^ n = A / ((2 : ℝ) ^ n * (1 + A)) := by
      rw [h4n]; field_simp
    rw [heq, div_le_one (by positivity)]
    have h1le : (1 : ℝ) ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
    nlinarith [mul_nonneg (sub_nonneg.mpr h1le) h1A.le, mul_nonneg hAnn (sub_nonneg.mpr h1le)]

/-- The fibre-slice term has compact support (the scalar `sₙ` does). -/
private theorem paramTerm_slice_hasCompactSupport (n : ℕ) (w : E) :
    HasCompactSupport (fun t => paramTerm a ha hsupp n (t, w)) := by
  rw [paramTerm_slice_eq]
  exact (paramScalar_hasCompactSupport a ha hsupp n).smul_right

private theorem paramTerm_slice_iteratedFDeriv_global_bound (n k : ℕ) (w : E) :
    ∃ B : ℝ, ∀ t : ℝ, ‖iteratedFDeriv ℝ k (fun s => paramTerm a ha hsupp n (s, w)) t‖ ≤ B := by
  have hcs : HasCompactSupport (iteratedFDeriv ℝ k (fun s => paramTerm a ha hsupp n (s, w))) :=
    (paramTerm_slice_hasCompactSupport a ha hsupp n w).iteratedFDeriv k
  have hcont : Continuous (iteratedFDeriv ℝ k (fun s => paramTerm a ha hsupp n (s, w))) :=
    (paramTerm_slice_contDiff a ha hsupp n w).continuous_iteratedFDeriv
      (by exact_mod_cast le_top : (k : WithTop ℕ∞) ≤ ∞)
  obtain ⟨B, hB⟩ := hcs.exists_bound_of_continuous hcont
  exact ⟨B, hB⟩

/-- Per-fibre summable dominating function for the fibre-slice Borel series. -/
private def paramSliceDomBound (w : E) (k n : ℕ) : ℝ :=
  if k < n then (2 : ℝ)⁻¹ ^ n
  else Classical.choose (paramTerm_slice_iteratedFDeriv_global_bound a ha hsupp n k w)

private theorem paramSliceDomBound_summable (w : E) (k : ℕ) :
    Summable (paramSliceDomBound a ha hsupp w k) := by
  have hgeom : Summable (fun n : ℕ => (2 : ℝ)⁻¹ ^ n) := by
    simpa only [one_div] using summable_geometric_two
  refine Summable.congr_cofinite hgeom ?_
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [eventually_gt_atTop k] with n hn
  rw [paramSliceDomBound, if_pos hn]

private theorem paramSliceDomBound_bound (w : E) (k n : ℕ) (t : ℝ) :
    ‖iteratedFDeriv ℝ k (fun s => paramTerm a ha hsupp n (s, w)) t‖ ≤
      paramSliceDomBound a ha hsupp w k n := by
  rw [paramSliceDomBound]
  by_cases hkn : k < n
  · rw [if_pos hkn]; exact paramTerm_slice_iteratedFDeriv_bound a ha hsupp hkn w t
  · rw [if_neg hkn]
    exact Classical.choose_spec (paramTerm_slice_iteratedFDeriv_global_bound a ha hsupp n k w) t

/-- The `k`-th `t`-derivative at `0` of the parametrized Borel series over the fibre `w` realizes
the prescribed coefficient `a k w`. This is the parametrized analogue of `borel_jet_realize`'s jet
identity, fibre by fibre. -/
private theorem paramSeries_slice_iteratedDeriv_zero [CompleteSpace F] (k : ℕ) (w : E) :
    iteratedDeriv k (fun t => ∑' n, paramTerm a ha hsupp n (t, w)) 0 = a k w := by
  have hFD : iteratedFDeriv ℝ k (fun t => ∑' n, paramTerm a ha hsupp n (t, w)) 0 =
      ∑' n, iteratedFDeriv ℝ k (fun t => paramTerm a ha hsupp n (t, w)) 0 :=
    iteratedFDeriv_tsum_apply (N := (⊤ : ℕ∞)) (v := paramSliceDomBound a ha hsupp w)
      (fun n => paramTerm_slice_contDiff a ha hsupp n w)
      (fun j _ => paramSliceDomBound_summable a ha hsupp w j)
      (fun j i t _ => paramSliceDomBound_bound a ha hsupp w j i t)
      (le_top : (k : ℕ∞) ≤ (⊤ : ℕ∞)) 0
  rw [iteratedDeriv_eq_equiv_comp, Function.comp_apply, hFD,
    ← LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    (ContinuousMultilinearMap.piFieldEquiv ℝ (Fin k) F).symm.toContinuousLinearEquiv.map_tsum]
  simp only [LinearIsometryEquiv.coe_toContinuousLinearEquiv]
  have hterm : ∀ n, (ContinuousMultilinearMap.piFieldEquiv ℝ (Fin k) F).symm
      (iteratedFDeriv ℝ k (fun t => paramTerm a ha hsupp n (t, w)) 0) =
      (if n = k then (1 : ℝ) else 0) • a n w := by
    intro n
    rw [← Function.comp_apply (f := (ContinuousMultilinearMap.piFieldEquiv ℝ (Fin k) F).symm),
      ← iteratedDeriv_eq_equiv_comp]
    exact paramTerm_slice_iteratedDeriv_zero a ha hsupp n k w
  rw [tsum_congr hterm, tsum_eq_single k (fun n hn => by rw [if_neg hn, zero_smul]),
    if_pos rfl, one_smul]

/-- The parametrized Borel series `(t,z) ↦ ∑' n, fₙ(t,z)` is globally `C∞` on `ℝ × E`. -/
private theorem paramSeries_contDiff [CompleteSpace F] :
    ContDiff ℝ ∞ (fun p : ℝ × E => ∑' n, paramTerm a ha hsupp n p) :=
  contDiff_tsum (N := (⊤ : ℕ∞)) (v := paramDomBound a ha hsupp)
    (fun n => paramTerm_contDiff a ha hsupp n)
    (fun k _ => paramDomBound_summable a ha hsupp k)
    (fun k n p _ => paramDomBound_bound a ha hsupp k n p)

end Engine

section Setup

variable {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Multiplying a function smooth on an open set by a smooth cutoff supported inside that set
produces a globally smooth function. -/
private theorem contDiff_cutoff_smul {ρ : E → ℝ} {c : E → F} {U : Set E} (hU : IsOpen U)
    (hρ : ContDiff ℝ ∞ ρ) (htsupp : tsupport ρ ⊆ U) (hc : ContDiffOn ℝ ∞ c U) :
    ContDiff ℝ ∞ (fun z => ρ z • c z) := by
  rw [← contDiffOn_univ]
  intro z _
  by_cases hz : z ∈ tsupport ρ
  · have hzU : z ∈ U := htsupp hz
    have h1 : ContDiffWithinAt ℝ ∞ ρ Set.univ z := hρ.contDiffAt.contDiffWithinAt
    have h2 : ContDiffWithinAt ℝ ∞ c Set.univ z :=
      (hc.contDiffAt (hU.mem_nhds hzU)).contDiffWithinAt
    exact h1.smul h2
  · -- z ∉ tsupport ρ: ρ ≡ 0 on the open complement, so the product is ≡ 0 near z.
    have hopen : (tsupport ρ)ᶜ ∈ 𝓝 z := (isClosed_tsupport ρ).isOpen_compl.mem_nhds hz
    have heq : (fun z => ρ z • c z) =ᶠ[𝓝 z] (fun _ => (0:F)) := by
      filter_upwards [hopen] with y hy
      have : ρ y = 0 := image_eq_zero_of_notMem_tsupport hy
      rw [this, zero_smul]
    exact (contDiffAt_const.congr_of_eventuallyEq heq).contDiffWithinAt

/-- Strengthening of `exists_contDiff_tsupport_subset`: a smooth, compactly supported cutoff with
range in `[0,1]`, support inside the given neighbourhood, and equal to `1` *on a whole
neighbourhood* of the base point (not merely at it). The last fact is what licenses replacing the
cutoff coefficient `ρ` by `1` near `z₀`. -/
private theorem exists_contDiff_tsupport_subset_eventuallyEq_one
    [FiniteDimensional ℝ E] {s : Set E} {x : E} (hs : s ∈ 𝓝 x) :
    ∃ ρ : E → ℝ, tsupport ρ ⊆ s ∧ HasCompactSupport ρ ∧ ContDiff ℝ ∞ ρ ∧
      Set.range ρ ⊆ Set.Icc 0 1 ∧ ρ x = 1 ∧ ρ =ᶠ[𝓝 x] (1 : E → ℝ) := by
  obtain ⟨d : ℝ, d_pos : 0 < d, hd : Euclidean.closedBall x d ⊆ s⟩ :=
    Euclidean.nhds_basis_closedBall.mem_iff.1 hs
  set c : ContDiffBump (toEuclidean x) :=
    { rIn := d / 2
      rOut := d
      rIn_pos := half_pos d_pos
      rIn_lt_rOut := half_lt_self d_pos } with hc_def
  set ρ : E → ℝ := c ∘ toEuclidean with hρ_def
  have ρ_supp : Function.support ρ ⊆ Euclidean.ball x d := by
    intro y hy
    have : toEuclidean y ∈ Function.support c := by
      simpa only [Function.mem_support, Function.comp_apply, Ne] using hy
    rwa [c.support_eq] at this
  have ρ_tsupp : tsupport ρ ⊆ Euclidean.closedBall x d := by
    rw [tsupport, ← Euclidean.closure_ball _ d_pos.ne']
    exact closure_mono ρ_supp
  refine ⟨ρ, ρ_tsupp.trans hd, ?_, ?_, ?_, ?_, ?_⟩
  · exact HasCompactSupport.of_support_subset_isCompact Euclidean.isCompact_closedBall
      (ρ_supp.trans Euclidean.ball_subset_closedBall)
  · exact c.contDiff.comp (ContinuousLinearEquiv.contDiff _)
  · rintro t ⟨y, rfl⟩
    exact ⟨c.nonneg, c.le_one⟩
  · exact c.one_of_mem_closedBall (by
      simpa only [Euclidean.closedBall_eq_preimage, Set.mem_preimage] using
        Metric.mem_closedBall_self (half_pos d_pos).le)
  · have hc1 : c =ᶠ[𝓝 (toEuclidean x)] (1 : EuclideanSpace ℝ (Fin _) → ℝ) := c.eventuallyEq_one
    have := hc1.comp_tendsto (toEuclidean.continuous.continuousAt
      (x := x) : Filter.Tendsto toEuclidean (𝓝 x) (𝓝 (toEuclidean x)))
    simpa only [hρ_def, Function.comp_def, Pi.one_apply] using this

set_option linter.unusedVariables false in
/-- **Parametrized Borel half-line extension.** Let `g : ℝ → E → F` be jointly `C∞` on
`Ici 0 ×ˢ K` for a compact `K` with `z₀` in its interior. Then there is a function `gext` and an
open neighbourhood `V` of `z₀` on which `gext` is jointly `C∞` on the full slab `univ ×ˢ V`
(*every* time, both sides of the seam), and `gext` agrees with `g` for all `t ≥ 0` and all `z ∈ V`.

This is the `z`-uniform generalization of `borel_halfLine_extend`: the fixed-parameter jet
coefficients are promoted to smooth functions of the parameter `z`, multiplied by a smooth cutoff
near `z₀`, and the Borel series is run jointly on `ℝ × E`. The model space `E` is finite-dimensional
(as in every intended application, where `E` is a chart/tangent model `ℝ^d`); this is required to
build the smooth cutoff `ρ`. The conclusion is the joint-smoothness-on-a-`z`-neighbourhood form
needed by the downstream time-extension consumer (not merely `ContDiffAt` on the central fibre).

The compactness hypothesis `hK` is retained because it is the mathematically natural condition for the
statement (a family smooth on a closed slab over a compact base), even though the present proof draws
its compact support from the finite-dimensional bump cutoff supported in `interior K` rather than from
`hK` directly. -/
theorem borel_halfLine_extend_param [FiniteDimensional ℝ E] [CompleteSpace F]
    (g : ℝ → E → F) (K : Set E) (hK : IsCompact K) (z₀ : E) (hz₀ : z₀ ∈ interior K)
    (hg : ContDiffOn ℝ ∞ (Function.uncurry g) ((Set.Ici (0:ℝ)) ×ˢ K)) :
    ∃ gext : ℝ → E → F, ∃ V ∈ nhds z₀,
      ContDiffOn ℝ ∞ (Function.uncurry gext) ((Set.univ : Set ℝ) ×ˢ V) ∧
      (∀ t : ℝ, 0 ≤ t → ∀ z ∈ V, gext t z = g t z) := by
  classical
  -- A smooth cutoff `ρ ≡ 1` on a neighbourhood of `z₀`, supported in the open set `interior K`.
  obtain ⟨ρ, hρ_tsupp, hρ_cs, hρ_smooth, _hρ_range, _hρ_one, hρ_eq1⟩ :=
    exists_contDiff_tsupport_subset_eventuallyEq_one (x := z₀) (isOpen_interior.mem_nhds hz₀)
  set U : Set E := interior K with hU_def
  have hUopen : IsOpen U := isOpen_interior
  -- The jet coefficients are smooth on `U`.
  have hg' : ContDiffOn ℝ ∞ (Function.uncurry g) ((Set.Ici (0:ℝ)) ×ˢ U) :=
    hg.mono (Set.prod_mono_right interior_subset)
  -- The parametrized coefficient family `a n z = ρ z • cₙ z`.
  set a : ℕ → E → F :=
    fun n z => ρ z • iteratedDerivWithin n (fun s => g s z) (Set.Ici 0) 0 with ha_def
  have ha : ∀ n, ContDiff ℝ ∞ (a n) := fun n =>
    contDiff_cutoff_smul hUopen hρ_smooth hρ_tsupp (param_jet_contDiffOn g U hg' n)
  have hsupp : ∀ n, HasCompactSupport (a n) := fun n => hρ_cs.smul_right
  -- The extension.
  set gext : ℝ → E → F :=
    fun t z => if 0 ≤ t then g t z else ∑' n, paramTerm a ha hsupp n (t, z) with hgext_def
  -- We exhibit a single open neighbourhood `V ∋ z₀` (where `ρ ≡ 1`) on which `uncurry gext` is
  -- jointly `C∞` on the *full* slab `univ ×ˢ V`. On `univ ×ˢ V`, `uncurry gext` is the piecewise
  -- glue of the globally-smooth Borel series `Φ` (lower closed side `t ≤ 0`) and `uncurry g` (upper
  -- closed side `t ≥ 0`), the two agreeing at the seam `{0} × V` because `Φ(0, z) = g(0, z)` there.
  -- This is the *joint* analogue of `contDiff_if_le_of_jet_match`: we build the joint candidate
  -- Taylor series piecewise from the two one-sided series and verify
  -- `HasFTaylorSeriesUpToOn ∞ · · (univ ×ˢ V)`, gluing the seam derivative with
  -- `HasFDerivWithinAt.union` over `(Iic 0 ×ˢ V) ∪ (Ici 0 ×ˢ V) = univ ×ˢ V`.
  -- The globally-smooth Borel series `Φ`.
  set Φ : ℝ × E → F := fun p => ∑' n, paramTerm a ha hsupp n p with hΦ_def
  have hΦ : ContDiff ℝ ∞ Φ := paramSeries_contDiff a ha hsupp
  -- An open neighbourhood `V ∋ z₀`, `V ⊆ U`, on which `ρ ≡ 1`.
  have hVnhds : {z : E | ρ z = 1} ∩ U ∈ nhds z₀ :=
    Filter.inter_mem hρ_eq1 (hUopen.mem_nhds hz₀)
  obtain ⟨V, hVsub, hVopen, hz₀V⟩ := mem_nhds_iff.1 hVnhds
  have hρV : ∀ z ∈ V, ρ z = 1 := fun z hz => (hVsub hz).1
  have hVU : V ⊆ U := fun z hz => (hVsub hz).2
  refine ⟨gext, V, hVopen.mem_nhds hz₀V, ?_, ?_⟩
  · -- Joint `C∞` of `uncurry gext` on the full slab `univ ×ˢ V`.
    -- `Φ(0, z) = g 0 z` for `z ∈ V`: only the `n = 0` term of the series survives at `t = 0`,
    -- and there `ρ z = 1`, `c₀ z = g 0 z`.
    have hΦ0 : ∀ z ∈ V, Φ (0, z) = g 0 z := by
      intro z hz
      have hbump0 : borelBumpMono 0 0 = 1 := by
        rw [borelBumpMono, borelCutoff_eq_one (by norm_num : (0:ℝ) ^ 2 ≤ 1)]
        norm_num
      have hterm0 : ∀ n, paramTerm a ha hsupp n (0, z) =
          (if n = 0 then (1:ℝ) else 0) • a n z := by
        intro n
        have hp1 : (((0:ℝ), z) : ℝ × E).1 = 0 := rfl
        rw [paramTerm, hp1, mul_zero]
        rcases Nat.eq_zero_or_pos n with hn | hn
        · subst hn
          rw [if_pos rfl, hbump0]
          simp
        · rw [if_neg (by omega : ¬ n = 0), borelBumpMono,
            zero_pow (by omega : n ≠ 0)]
          simp
      rw [hΦ_def]
      change (∑' n, paramTerm a ha hsupp n (0, z)) = g 0 z
      rw [tsum_congr hterm0, tsum_eq_single 0 (fun n hn => by rw [if_neg hn, zero_smul]),
        if_pos rfl, one_smul, ha_def]
      change ρ z • iteratedDerivWithin 0 (fun s => g s z) (Set.Ici 0) 0 = g 0 z
      rw [hρV z hz, one_smul, iteratedDerivWithin_zero]
    -- `uncurry gext` equals `Φ` on the closed lower half `Iic 0 ×ˢ V`.
    have hEqLower : Set.EqOn (Function.uncurry gext) Φ (Set.Iic (0:ℝ) ×ˢ V) := by
      rintro ⟨t, z⟩ ⟨ht, hz⟩
      simp only [Set.mem_Iic] at ht
      rcases eq_or_lt_of_le ht with ht0 | ht0
      · subst ht0
        simp only [Function.uncurry, hgext_def, if_pos (le_refl (0:ℝ))]
        exact (hΦ0 z hz).symm
      · simp only [Function.uncurry, hgext_def, if_neg (not_le.mpr ht0), hΦ_def]
    -- `uncurry gext` equals `uncurry g` on the closed upper half `Ici 0 ×ˢ V`.
    have hEqUpper : Set.EqOn (Function.uncurry gext) (Function.uncurry g)
        (Set.Ici (0:ℝ) ×ˢ V) := by
      rintro ⟨t, z⟩ ⟨ht, _⟩
      simp only [Set.mem_Ici] at ht
      simp only [Function.uncurry, hgext_def, if_pos ht]
    -- The unique-differentiability of the two closed half-slabs.
    have hUDl : UniqueDiffOn ℝ (Set.Iic (0:ℝ) ×ˢ V) :=
      UniqueDiffOn.prod (uniqueDiffOn_Iic 0) hVopen.uniqueDiffOn
    have hUDr : UniqueDiffOn ℝ (Set.Ici (0:ℝ) ×ˢ V) :=
      UniqueDiffOn.prod (uniqueDiffOn_Ici 0) hVopen.uniqueDiffOn
    -- The two one-sided Taylor series.
    set pL : ℝ × E → FormalMultilinearSeries ℝ (ℝ × E) F :=
      ftaylorSeriesWithin ℝ Φ (Set.Iic (0:ℝ) ×ˢ V) with hpL_def
    set pR : ℝ × E → FormalMultilinearSeries ℝ (ℝ × E) F :=
      ftaylorSeriesWithin ℝ (Function.uncurry g) (Set.Ici (0:ℝ) ×ˢ V) with hpR_def
    have hgR : ContDiffOn ℝ ∞ (Function.uncurry g) (Set.Ici (0:ℝ) ×ˢ V) :=
      hg.mono (Set.prod_mono_right (hVU.trans interior_subset))
    have hTL : HasFTaylorSeriesUpToOn ∞ Φ pL (Set.Iic (0:ℝ) ×ˢ V) :=
      hΦ.contDiffOn.ftaylorSeriesWithin hUDl
    have hTR : HasFTaylorSeriesUpToOn ∞ (Function.uncurry g) pR (Set.Ici (0:ℝ) ×ˢ V) :=
      hgR.ftaylorSeriesWithin hUDr
    -- The candidate joint series, assembled piecewise.
    set p : ℝ × E → FormalMultilinearSeries ℝ (ℝ × E) F :=
      fun q => if q.1 ≤ 0 then pL q else pR q with hp_def
    -- **THE SEAM COEFFICIENT MATCH**: the two one-sided joint Taylor coefficients agree at every
    -- seam point `(0, z)`, `z ∈ V`. Since `Φ` is globally smooth, its lower within-jet equals the
    -- full jet, which equals its *upper* within-jet, so the goal reduces to a common-domain
    -- (`Ici 0 ×ˢ V`) statement. Both `Φ` and `uncurry g` are `C∞` there and share their entire
    -- one-sided `t`-jet at every seam parameter `w ∈ V` (the Borel series realizes `cₙ` fibrewise by
    -- construction, and `ρ ≡ 1` on `V`); `iteratedFDerivWithin_prod_match` turns this common `t`-jet
    -- into the matching joint iterated Fréchet derivative.
    have htjet : ∀ i : ℕ, Set.EqOn
        (fun w => iteratedDerivWithin i (fun t => Φ (t, w)) (Set.Ici 0) 0)
        (fun w => iteratedDerivWithin i (fun t => Function.uncurry g (t, w)) (Set.Ici 0) 0) V := by
      intro i w hw
      simp only
      have hΦsliceAt : ContDiffAt ℝ (i : WithTop ℕ∞) (fun t => Φ (t, w)) 0 :=
        (hΦ.comp (contDiff_id.prodMk contDiff_const)).contDiffAt.of_le (by exact_mod_cast le_top)
      have hLHS : iteratedDerivWithin i (fun t => Φ (t, w)) (Set.Ici 0) 0 = a i w := by
        rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ici 0) hΦsliceAt Set.self_mem_Ici]
        have hΦeq : (fun t => Φ (t, w)) = fun t => ∑' n, paramTerm a ha hsupp n (t, w) := by
          funext t; rw [hΦ_def]
        rw [hΦeq, paramSeries_slice_iteratedDeriv_zero a ha hsupp i w]
      rw [hLHS]
      simp only [ha_def, hρV w hw, one_smul]
      rfl
    -- Apply the common-`t`-jet ⟹ matching-joint-jet lemma after collapsing the smooth left jet.
    have hjetF : ∀ (n : ℕ) (z : E), z ∈ V →
        iteratedFDerivWithin ℝ n Φ (Set.Iic (0:ℝ) ×ˢ V) (0, z) =
          iteratedFDerivWithin ℝ n (Function.uncurry g) (Set.Ici (0:ℝ) ×ˢ V) (0, z) := by
      intro n z hz
      have hmemL : ((0:ℝ), z) ∈ Set.Iic (0:ℝ) ×ˢ V := ⟨Set.self_mem_Iic, hz⟩
      have hmemR : ((0:ℝ), z) ∈ Set.Ici (0:ℝ) ×ˢ V := ⟨Set.self_mem_Ici, hz⟩
      have hΦn : ContDiffAt ℝ (n : WithTop ℕ∞) Φ (0, z) :=
        hΦ.contDiffAt.of_le (by exact_mod_cast le_top)
      rw [iteratedFDerivWithin_eq_iteratedFDeriv hUDl hΦn hmemL,
        ← iteratedFDerivWithin_eq_iteratedFDeriv hUDr hΦn hmemR]
      exact iteratedFDerivWithin_prod_match hVopen hΦ.contDiffOn hgR htjet n hz
    -- Hence the assembled series is well-defined at the seam: `pL (0,z) = pR (0,z)` on `V`.
    have hpLR : ∀ (n : ℕ) (z : E), z ∈ V → pL (0, z) n = pR (0, z) n := by
      intro n z hz
      simp only [hpL_def, hpR_def, ftaylorSeriesWithin]
      exact hjetF n z hz
    -- `p` agrees with `pL` on the lower half (guard true).
    have hEqpL : ∀ m : ℕ, Set.EqOn (fun q => p q m) (fun q => pL q m) (Set.Iic (0:ℝ) ×ˢ V) := by
      intro m q hq
      simp only [hp_def, if_pos (Set.mem_Iic.mp hq.1)]
    -- `p` agrees with `pR` on the upper half (`> 0` directly; at the seam via `hpLR`).
    have hEqpR : ∀ m : ℕ, Set.EqOn (fun q => p q m) (fun q => pR q m) (Set.Ici (0:ℝ) ×ˢ V) := by
      intro m q hq
      rcases eq_or_lt_of_le (Set.mem_Ici.mp hq.1) with hq0 | hq0
      · obtain ⟨t, z⟩ := q
        simp only at hq0
        subst hq0
        simp only [hp_def, if_pos (le_refl (0:ℝ))]
        exact hpLR m z hq.2
      · simp only [hp_def, if_neg (not_le.mpr hq0)]
    -- The zero-th coefficient yields the value of `uncurry gext`.
    have hzero : ∀ q ∈ Set.univ ×ˢ V, (p q 0).curry0 = Function.uncurry gext q := by
      rintro ⟨t, z⟩ ⟨_, hz⟩
      by_cases ht : t ≤ 0
      · have hmem : (t, z) ∈ Set.Iic (0:ℝ) ×ˢ V := ⟨Set.mem_Iic.mpr ht, hz⟩
        have hval : (pL (t, z) 0).curry0 = Φ (t, z) := hTL.zero_eq (t, z) hmem
        rw [hp_def]; simp only [if_pos ht]
        rw [hval, hEqLower hmem]
      · have ht' : (0:ℝ) ≤ t := le_of_lt (not_le.mp ht)
        have hmem : (t, z) ∈ Set.Ici (0:ℝ) ×ˢ V := ⟨Set.mem_Ici.mpr ht', hz⟩
        have hval : (pR (t, z) 0).curry0 = Function.uncurry g (t, z) := hTR.zero_eq (t, z) hmem
        rw [hp_def]; simp only [if_neg ht]
        rw [hval, hEqUpper hmem]
    -- The per-point derivative obligation for `p · m`, on `univ ×ˢ V`.
    have hm_lt : ∀ m : ℕ, (m : WithTop ℕ∞) < ∞ := fun m => by
      exact_mod_cast (Nat.cast_lt.mpr m.lt_succ_self).trans_le le_top
    have hderiv : ∀ (m : ℕ), ∀ q ∈ Set.univ ×ˢ V,
        HasFDerivWithinAt (fun y => p y m) (p q m.succ).curryLeft (Set.univ ×ˢ V) q := by
      intro m q hq
      obtain ⟨t, z⟩ := q
      have hz : z ∈ V := hq.2
      rcases lt_trichotomy t 0 with ht | ht | ht
      · -- Interior of the lower slab: upgrade the `Iic`-derivative to a full one.
        have hmem : (t, z) ∈ Set.Iic (0:ℝ) ×ˢ V := ⟨Set.mem_Iic.mpr (le_of_lt ht), hz⟩
        have hdL : HasFDerivWithinAt (fun y => pL y m) (pL (t, z) m.succ).curryLeft
            (Set.Iic (0:ℝ) ×ˢ V) (t, z) := hTL.fderivWithin m (hm_lt m) (t, z) hmem
        have hnhds : Set.Iio (0:ℝ) ×ˢ V ∈ nhds (t, z) :=
          prod_mem_nhds (Iio_mem_nhds ht) (hVopen.mem_nhds hz)
        have hsub : Set.Iio (0:ℝ) ×ˢ V ⊆ Set.Iic (0:ℝ) ×ˢ V :=
          Set.prod_mono_left Iio_subset_Iic_self
        have hdL' : HasFDerivAt (fun y => pL y m) (pL (t, z) m.succ).curryLeft (t, z) :=
          (hdL.mono hsub).hasFDerivAt hnhds
        have hee : (fun y => p y m) =ᶠ[nhds (t, z)] (fun y => pL y m) :=
          Filter.eventuallyEq_of_mem hnhds (fun y hy => hEqpL m (hsub hy))
        have hfd : HasFDerivAt (fun y => p y m) (pL (t, z) m.succ).curryLeft (t, z) :=
          hdL'.congr_of_eventuallyEq hee
        rw [hp_def]; simp only [if_pos (le_of_lt ht)]
        exact hfd.hasFDerivWithinAt
      · -- The seam `t = 0`: glue the two one-sided derivatives.
        subst ht
        have hmemL : ((0:ℝ), z) ∈ Set.Iic (0:ℝ) ×ˢ V := ⟨Set.self_mem_Iic, hz⟩
        have hmemR : ((0:ℝ), z) ∈ Set.Ici (0:ℝ) ×ˢ V := ⟨Set.self_mem_Ici, hz⟩
        have hdL0 : HasFDerivWithinAt (fun y => pL y m) (pL (0, z) m.succ).curryLeft
            (Set.Iic (0:ℝ) ×ˢ V) (0, z) := hTL.fderivWithin m (hm_lt m) (0, z) hmemL
        have hdL0' : HasFDerivWithinAt (fun y => p y m) (pL (0, z) m.succ).curryLeft
            (Set.Iic (0:ℝ) ×ˢ V) (0, z) := hdL0.congr (hEqpL m) (hEqpL m hmemL)
        have hdR0 : HasFDerivWithinAt (fun y => pR y m) (pR (0, z) m.succ).curryLeft
            (Set.Ici (0:ℝ) ×ˢ V) (0, z) := hTR.fderivWithin m (hm_lt m) (0, z) hmemR
        have hdR0' : HasFDerivWithinAt (fun y => p y m) (pL (0, z) m.succ).curryLeft
            (Set.Ici (0:ℝ) ×ˢ V) (0, z) := by
          have hval : (pR (0, z) m.succ).curryLeft = (pL (0, z) m.succ).curryLeft := by
            rw [hpLR m.succ z hz]
          rw [← hval]
          exact hdR0.congr (hEqpR m) (hEqpR m hmemR)
        have hunion : HasFDerivWithinAt (fun y => p y m) (pL (0, z) m.succ).curryLeft
            (Set.Iic (0:ℝ) ×ˢ V ∪ Set.Ici (0:ℝ) ×ˢ V) (0, z) := hdL0'.union hdR0'
        rw [← Set.union_prod, Set.Iic_union_Ici] at hunion
        rw [hp_def]; simp only [if_pos (le_refl (0:ℝ))]
        exact hunion
      · -- Interior of the upper slab: upgrade the `Ici`-derivative to a full one.
        have hmem : (t, z) ∈ Set.Ici (0:ℝ) ×ˢ V := ⟨Set.mem_Ici.mpr (le_of_lt ht), hz⟩
        have hdR : HasFDerivWithinAt (fun y => pR y m) (pR (t, z) m.succ).curryLeft
            (Set.Ici (0:ℝ) ×ˢ V) (t, z) := hTR.fderivWithin m (hm_lt m) (t, z) hmem
        have hnhds : Set.Ioi (0:ℝ) ×ˢ V ∈ nhds (t, z) :=
          prod_mem_nhds (Ioi_mem_nhds ht) (hVopen.mem_nhds hz)
        have hsub : Set.Ioi (0:ℝ) ×ˢ V ⊆ Set.Ici (0:ℝ) ×ˢ V :=
          Set.prod_mono_left Ioi_subset_Ici_self
        have hdR' : HasFDerivAt (fun y => pR y m) (pR (t, z) m.succ).curryLeft (t, z) :=
          (hdR.mono hsub).hasFDerivAt hnhds
        have hee : (fun y => p y m) =ᶠ[nhds (t, z)] (fun y => pR y m) :=
          Filter.eventuallyEq_of_mem hnhds (fun y hy => hEqpR m (hsub hy))
        have hfd : HasFDerivAt (fun y => p y m) (pR (t, z) m.succ).curryLeft (t, z) :=
          hdR'.congr_of_eventuallyEq hee
        rw [hp_def]; simp only [if_neg (not_le.mpr ht)]
        exact hfd.hasFDerivWithinAt
    -- Assemble the joint Taylor series on `univ ×ˢ V` (no continuity check needed at order `∞`).
    have hTaylor : HasFTaylorSeriesUpToOn ∞ (Function.uncurry gext) p (Set.univ ×ˢ V) :=
      (hasFTaylorSeriesUpToOn_top_iff' (le_refl _)).mpr ⟨hzero, hderiv⟩
    exact hTaylor.contDiffOn
  · -- Agreement with `g` for `t ≥ 0`, on all of `V`.
    intro t ht z _
    simp only [hgext_def, if_pos ht]

/-- The linear reflection `(a, b) ↦ (-a, b)` of `ℝ × E`, the derivative of the affine seam-swap
`(t, z) ↦ (T - t, z)`. -/
private def reflectFst : (ℝ × E) ≃L[ℝ] (ℝ × E) :=
  (ContinuousLinearEquiv.neg ℝ).prodCongr (ContinuousLinearEquiv.refl ℝ E)

/-- The unique-differentiability of a set is preserved by translation. -/
private theorem uniqueDiffOn_vadd {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (a : G) {s : Set G} (hs : UniqueDiffOn ℝ s) : UniqueDiffOn ℝ (a +ᵥ s) := by
  have himg : a +ᵥ s = (fun x => a + x) '' s := by
    ext y; simp only [Set.mem_vadd_set, Set.mem_image, vadd_eq_add]
  rw [himg]
  refine hs.image (f' := fun _ => ContinuousLinearMap.id ℝ G) (fun x _ => ?_) (fun x _ => ?_)
  · have h : HasFDerivWithinAt (fun y => a + y) (0 + ContinuousLinearMap.id ℝ G) s x :=
      (hasFDerivWithinAt_const a x s).add (hasFDerivWithinAt_id x s)
    rwa [zero_add] at h
  · exact Function.surjective_id.denseRange

/-- **Reflection transport.** The joint iterated Fréchet derivative of `G` on `s` at the seam image
`(T - x.1, x.2)` equals that of the reflected `G ∘ (t,z) ↦ (T-t,z)` on the reflected set at `x`,
post-composed with the (orientation-reversing) linear reflection `reflectFst`. The affine seam-swap
factors as `(· + (T,0)) ∘ reflectFst`; the translation is absorbed via
`iteratedFDerivWithin_comp_add_right` and the linear reflection via
`ContinuousLinearEquiv.iteratedFDerivWithin_comp_right`. -/
private theorem reflect_iteratedFDerivWithin (T : ℝ) (G : ℝ × E → F) (n : ℕ) (s : Set (ℝ × E))
    (x : ℝ × E) (hs : UniqueDiffOn ℝ s) (hx : (T - x.1, x.2) ∈ s) :
    iteratedFDerivWithin ℝ n (fun p => G (T - p.1, p.2))
        ((fun p : ℝ × E => (T - p.1, p.2)) ⁻¹' s) x =
      (iteratedFDerivWithin ℝ n G s (T - x.1, x.2)).compContinuousLinearMap
        (fun _ => ((reflectFst : (ℝ × E) ≃L[ℝ] (ℝ × E)) : (ℝ × E) →L[ℝ] (ℝ × E))) := by
  set φ : ℝ × E → ℝ × E := fun p => (T - p.1, p.2) with hφ
  set c : ℝ × E := ((T : ℝ), (0 : E)) with hc
  have hrefl : ∀ p : ℝ × E, (reflectFst : (ℝ × E) → (ℝ × E)) p + c = φ p := by
    intro p
    simp only [reflectFst, ContinuousLinearEquiv.prodCongr_apply, ContinuousLinearEquiv.neg_apply,
      ContinuousLinearEquiv.refl_apply, Prod.mk_add_mk, hφ, hc, add_zero]
    rw [neg_add_eq_sub]
  have hcomp : (fun p : ℝ × E => G (φ p))
      = (fun q : ℝ × E => G (q + c)) ∘ (reflectFst : (ℝ × E) → (ℝ × E)) := by
    funext p; simp only [Function.comp_apply, hrefl]
  set s'' : Set (ℝ × E) := (fun q : ℝ × E => q + c) ⁻¹' s with hs''
  have hpre : (reflectFst : (ℝ × E) → (ℝ × E)) ⁻¹' s'' = φ ⁻¹' s := by
    ext p; simp only [hs'', Set.mem_preimage, hrefl]
  have hvadd : c +ᵥ s'' = s := by
    rw [hs'']
    ext q
    simp only [Set.mem_vadd_set, Set.mem_preimage, vadd_eq_add]
    constructor
    · rintro ⟨w, hw, rfl⟩; rwa [add_comm c w]
    · intro hq; exact ⟨q - c, by rwa [sub_add_cancel], by rw [add_sub_cancel]⟩
  have hs''eq : s'' = (-c) +ᵥ s := by
    rw [hs'']
    ext q
    simp only [Set.mem_vadd_set, Set.mem_preimage, vadd_eq_add]
    constructor
    · intro hq; exact ⟨q + c, hq, by abel⟩
    · rintro ⟨w, hw, rfl⟩; rwa [show -c + w + c = w by abel]
  have hs''ud : UniqueDiffOn ℝ s'' := by
    rw [hs''eq]; exact uniqueDiffOn_vadd (-c) hs
  have hreflx : (reflectFst : (ℝ × E) → (ℝ × E)) x ∈ s'' := by
    simp only [hs'', Set.mem_preimage, hrefl]; exact hx
  rw [hcomp, ← hpre,
    reflectFst.iteratedFDerivWithin_comp_right (fun q : ℝ × E => G (q + c)) hs''ud hreflx n]
  congr 1
  rw [iteratedFDerivWithin_comp_add_right, hvadd, hrefl]

/-- The smooth `t`-cutoff: `1` on `(-∞, T/2]`, `0` on `[3T/4, ∞)`. Multiplying a family smooth on
the compact slab `Icc 0 T ×ˢ V` by this cutoff produces a family smooth on the half-line slab
`Ici 0 ×ˢ V` that is unchanged near the left seam `t = 0`. -/
private def intervalCutoff (T : ℝ) (t : ℝ) : ℝ :=
  Real.smoothTransition ((3 * T / 4 - t) / (T / 4))

private theorem intervalCutoff_contDiff (T : ℝ) : ContDiff ℝ ∞ (intervalCutoff T) :=
  Real.smoothTransition.contDiff.comp ((contDiff_const.sub contDiff_id).div_const _)

private theorem intervalCutoff_eq_one (T : ℝ) (hT : 0 < T) {t : ℝ} (ht : t ≤ T / 2) :
    intervalCutoff T t = 1 := by
  apply Real.smoothTransition.one_of_one_le
  rw [le_div_iff₀ (by positivity)]; linarith

private theorem intervalCutoff_eq_zero (T : ℝ) (hT : 0 < T) {t : ℝ} (ht : 3 * T / 4 ≤ t) :
    intervalCutoff T t = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  apply div_nonpos_of_nonpos_of_nonneg <;> [linarith; positivity]

omit [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] in
private theorem tsupport_intervalCutoff_fst (T : ℝ) (hT : 0 < T) :
    tsupport (fun p : ℝ × E => intervalCutoff T p.1) ⊆ {p : ℝ × E | p.1 ≤ 3 * T / 4} := by
  apply closure_minimal
  · intro p hp
    simp only [Function.mem_support] at hp
    simp only [Set.mem_setOf_eq]
    by_contra h
    exact hp (intervalCutoff_eq_zero T hT (le_of_lt (lt_of_not_ge h)))
  · exact isClosed_le continuous_fst continuous_const

/-- Multiplying a family `h` smooth on the compact slab `Icc 0 T ×ˢ V` by the smooth `t`-cutoff
`intervalCutoff T` gives a family smooth on the whole half-line slab `Ici 0 ×ˢ V`. -/
private theorem contDiffOn_intervalCutoff_smul (T : ℝ) (hT : 0 < T) (h : ℝ × E → F) {V : Set E}
    (hV : IsOpen V) (hh : ContDiffOn ℝ ∞ h (Set.Icc 0 T ×ˢ V)) :
    ContDiffOn ℝ ∞ (fun p : ℝ × E => intervalCutoff T p.1 • h p) (Set.Ici 0 ×ˢ V) := by
  intro p hp
  by_cases hsupp : p ∈ tsupport (fun q : ℝ × E => intervalCutoff T q.1)
  · have hp1 : p.1 ≤ 3 * T / 4 := tsupport_intervalCutoff_fst T hT hsupp
    have hp1' : p.1 < T := by linarith
    have hmemIcc : p ∈ Set.Icc 0 T ×ˢ V := ⟨⟨hp.1, le_of_lt hp1'⟩, hp.2⟩
    have hset : Set.Icc (0:ℝ) T ×ˢ V =ᶠ[𝓝 p] Set.Ici (0:ℝ) ×ˢ V := by
      filter_upwards [prod_mem_nhds (Iio_mem_nhds hp1') (hV.mem_nhds hp.2)] with q hq
      have hqT : q.1 < T := hq.1
      simp only [eq_iff_iff]
      exact ⟨fun hr => ⟨hr.1.1, hr.2⟩, fun hr => ⟨⟨hr.1, le_of_lt hqT⟩, hr.2⟩⟩
    have hhp : ContDiffWithinAt ℝ ∞ h (Set.Ici (0:ℝ) ×ˢ V) p :=
      (contDiffWithinAt_congr_set hset).mp (hh p hmemIcc)
    exact (((intervalCutoff_contDiff T).comp contDiff_fst).contDiffWithinAt).smul hhp
  · have hopen : (tsupport (fun q : ℝ × E => intervalCutoff T q.1))ᶜ ∈ 𝓝 p :=
      (isClosed_tsupport _).isOpen_compl.mem_nhds hsupp
    have heq : (fun q : ℝ × E => intervalCutoff T q.1 • h q) =ᶠ[𝓝 p] (fun _ => (0:F)) := by
      filter_upwards [hopen] with q hq
      rw [image_eq_zero_of_notMem_tsupport (f := fun r : ℝ × E => intervalCutoff T r.1) hq,
        zero_smul]
    exact (contDiffAt_const.congr_of_eventuallyEq heq).contDiffWithinAt

/-- **Seam jet match across a compact-interval seam.** A globally-`C∞` family `Φ` and a family `h`
smooth on the compact slab `Icc 0 T ×ˢ V` that share their entire one-sided `t`-jet at `t = 0` for
every parameter `w ∈ V` have the same joint iterated Fréchet derivative at every seam point `(0, z)`
— `Φ`'s computed on the *lower* slab `Iic 0 ×ˢ V`, `h`'s on the compact slab `Icc 0 T ×ˢ V`.

The compact slab is bridged to the half-line slab `Ici 0 ×ˢ V` near the seam (they agree on
`Iio T`), `Φ`'s lower jet is collapsed to its full jet (`Φ` global), and `h` is replaced by its
`intervalCutoff` truncation (globally `C∞` on `Ici 0 ×ˢ V`, unchanged near the seam) so that the
half-line `iteratedFDerivWithin_prod_match` applies. -/
private theorem prodMatch_intervalCutoff (T : ℝ) (hT : 0 < T) (Φ : ℝ × E → F)
    (hΦ : ContDiff ℝ ∞ Φ) (h : ℝ × E → F) {V : Set E} (hV : IsOpen V)
    (hh : ContDiffOn ℝ ∞ h (Set.Icc 0 T ×ˢ V))
    (hjet : ∀ i : ℕ, ∀ w ∈ V, iteratedDerivWithin i (fun t => Φ (t, w)) (Set.Ici 0) 0
                              = iteratedDerivWithin i (fun t => h (t, w)) (Set.Ici 0) 0)
    (n : ℕ) {z : E} (hz : z ∈ V) :
    iteratedFDerivWithin ℝ n Φ (Set.Iic (0:ℝ) ×ˢ V) (0, z)
      = iteratedFDerivWithin ℝ n h (Set.Icc 0 T ×ˢ V) (0, z) := by
  have hmem0 : ((0:ℝ), z) ∈ Set.Ici (0:ℝ) ×ˢ V := ⟨Set.self_mem_Ici, hz⟩
  have hUDl : UniqueDiffOn ℝ (Set.Iic (0:ℝ) ×ˢ V) :=
    UniqueDiffOn.prod (uniqueDiffOn_Iic 0) hV.uniqueDiffOn
  have hUDr : UniqueDiffOn ℝ (Set.Ici (0:ℝ) ×ˢ V) :=
    UniqueDiffOn.prod (uniqueDiffOn_Ici 0) hV.uniqueDiffOn
  have hΦat : ContDiffAt ℝ (n : WithTop ℕ∞) Φ (0, z) :=
    hΦ.contDiffAt.of_le (by exact_mod_cast le_top)
  have hLHS : iteratedFDerivWithin ℝ n Φ (Set.Iic (0:ℝ) ×ˢ V) (0, z)
      = iteratedFDerivWithin ℝ n Φ (Set.Ici (0:ℝ) ×ˢ V) (0, z) := by
    rw [iteratedFDerivWithin_eq_iteratedFDeriv hUDl hΦat ⟨Set.self_mem_Iic, hz⟩,
      ← iteratedFDerivWithin_eq_iteratedFDeriv hUDr hΦat hmem0]
  have hsetEq : Set.Icc (0:ℝ) T ×ˢ V =ᶠ[𝓝 ((0:ℝ), z)] Set.Ici (0:ℝ) ×ˢ V := by
    filter_upwards [prod_mem_nhds (Iio_mem_nhds hT) (hV.mem_nhds hz)] with q hq
    have hqT : q.1 < T := hq.1
    simp only [eq_iff_iff]
    exact ⟨fun hr => ⟨hr.1.1, hr.2⟩, fun hr => ⟨⟨hr.1, le_of_lt hqT⟩, hr.2⟩⟩
  rw [hLHS, iteratedFDerivWithin_congr_set hsetEq n]
  have hĥsmooth : ContDiffOn ℝ ∞ (fun p : ℝ × E => intervalCutoff T p.1 • h p)
      (Set.Ici (0:ℝ) ×ˢ V) := contDiffOn_intervalCutoff_smul T hT h hV hh
  have hĥeq : (fun p : ℝ × E => intervalCutoff T p.1 • h p)
      =ᶠ[𝓝[Set.Ici (0:ℝ) ×ˢ V] ((0:ℝ), z)] h := by
    have hu : {q : ℝ × E | q.1 < T / 2} ∈ 𝓝 ((0:ℝ), z) :=
      continuous_fst.continuousAt.preimage_mem_nhds (Iio_mem_nhds (by positivity))
    filter_upwards [mem_nhdsWithin_of_mem_nhds hu] with q hqlt
    show intervalCutoff T q.1 • h q = h q
    rw [intervalCutoff_eq_one T hT (le_of_lt hqlt), one_smul]
  have hĥval : (fun p : ℝ × E => intervalCutoff T p.1 • h p) ((0:ℝ), z) = h ((0:ℝ), z) := by
    change intervalCutoff T (0:ℝ) • h ((0:ℝ), z) = h ((0:ℝ), z)
    rw [intervalCutoff_eq_one T hT (by positivity), one_smul]
  rw [(hĥeq.iteratedFDerivWithin_eq hĥval n).symm]
  have htjet : ∀ i : ℕ, Set.EqOn
      (fun w => iteratedDerivWithin i (fun t => Φ (t, w)) (Set.Ici 0) 0)
      (fun w => iteratedDerivWithin i (fun t => intervalCutoff T t • h (t, w)) (Set.Ici 0) 0) V := by
    intro i w hw
    simp only
    rw [hjet i w hw]
    refine (Filter.EventuallyEq.iteratedDerivWithin_eq ?_ ?_).symm
    · filter_upwards [mem_nhdsWithin_of_mem_nhds
        (Iio_mem_nhds (show (0:ℝ) < T / 2 by positivity))] with t ht
      show intervalCutoff T t • h (t, w) = h (t, w)
      rw [intervalCutoff_eq_one T hT (le_of_lt ht), one_smul]
    · show intervalCutoff T (0:ℝ) • h ((0:ℝ), w) = h ((0:ℝ), w)
      rw [intervalCutoff_eq_one T hT (by positivity), one_smul]
  exact iteratedFDerivWithin_prod_match hV hΦ.contDiffOn hĥsmooth htjet n hz

set_option linter.unusedVariables false in
/-- **Parametrized Borel compact-interval extension.** The two-seam analogue of
`borel_halfLine_extend_param`. Let `g : ℝ → E → F` be jointly `C∞` on the compact slab
`Icc 0 T ×ˢ K` for a compact `K` with `z₀` in its interior. Then there is a function `gext` and an
open neighbourhood `V` of `z₀` on which `gext` is jointly `C∞` on the full slab `univ ×ˢ V` and
agrees with `g` for all `t ∈ [0, T]` and all `z ∈ V`.

The construction runs the parametrized Borel series twice, once at each endpoint: `Lext` matches
`g`'s one-sided `t`-jet at `t = 0` and supplies the extension for `t < 0`; `Rext (t, z) := RΦ(T-t,z)`
is the reflected Borel series matching `g`'s one-sided `t`-jet at `t = T` and supplies the extension
for `t > T`; on the middle `[0, T]` the extension is `g`. Joint `C∞` on `univ ×ˢ V` is the two-seam
`HasFTaylorSeriesUpToOn` glue: the assembled candidate Taylor series is the lower series on `t < 0`,
`g`'s on `0 ≤ t ≤ T`, the reflected series on `t > T`, with the two seam coefficient matches supplied
by `prodMatch_intervalCutoff` (left seam directly; right seam after the orientation-reversing
`reflect_iteratedFDerivWithin` transport). As in the half-line case, `E` is finite-dimensional (the
cutoff `ρ`) and the compactness of `K` provides the interior point. -/
theorem borel_interval_extend_param [FiniteDimensional ℝ E] [CompleteSpace F]
    (g : ℝ → E → F) (T : ℝ) (hT : 0 < T) (K : Set E) (hK : IsCompact K)
    (z₀ : E) (hz₀ : z₀ ∈ interior K)
    (hg : ContDiffOn ℝ ∞ (Function.uncurry g) (Set.Icc (0:ℝ) T ×ˢ K)) :
    ∃ gext : ℝ → E → F, ∃ V ∈ nhds z₀,
      ContDiffOn ℝ ∞ (Function.uncurry gext) ((Set.univ : Set ℝ) ×ˢ V) ∧
      (∀ t ∈ Set.Icc (0:ℝ) T, ∀ z ∈ V, gext t z = g t z) := by
  classical
  obtain ⟨ρ, hρ_tsupp, hρ_cs, hρ_smooth, _hρ_range, _hρ_one, hρ_eq1⟩ :=
    exists_contDiff_tsupport_subset_eventuallyEq_one (x := z₀) (isOpen_interior.mem_nhds hz₀)
  set U : Set E := interior K with hU_def
  have hUopen : IsOpen U := isOpen_interior
  have hg' : ContDiffOn ℝ ∞ (Function.uncurry g) (Set.Icc (0:ℝ) T ×ˢ U) :=
    hg.mono (Set.prod_mono_right interior_subset)
  -- The reflected family `(s, z) ↦ g (T - s) z`, smooth on `Icc 0 T ×ˢ U`.
  set gR : ℝ → E → F := fun s z => g (T - s) z with hgR_def
  have hgR' : ContDiffOn ℝ ∞ (Function.uncurry gR) (Set.Icc (0:ℝ) T ×ˢ U) := by
    have hmap : ContDiffOn ℝ ∞ (fun p : ℝ × E => ((T - p.1 : ℝ), p.2)) (Set.Icc (0:ℝ) T ×ˢ U) :=
      ((contDiff_const.sub contDiff_fst).prodMk contDiff_snd).contDiffOn
    have hmaps : Set.MapsTo (fun p : ℝ × E => ((T - p.1 : ℝ), p.2))
        (Set.Icc (0:ℝ) T ×ˢ U) (Set.Icc (0:ℝ) T ×ˢ U) := by
      rintro ⟨s, z⟩ ⟨hs, hz⟩
      simp only [Set.mem_Icc] at hs
      exact ⟨Set.mem_Icc.mpr ⟨by linarith [hs.1, hs.2], by linarith [hs.1, hs.2]⟩, hz⟩
    exact hg'.comp hmap hmaps
  -- The two curried cutoff families, smooth on the half-line slab `Ici 0 ×ˢ U`.
  set gLcut : ℝ → E → F := fun s z => intervalCutoff T s • g s z with hgLcut_def
  set gRcut : ℝ → E → F := fun s z => intervalCutoff T s • gR s z with hgRcut_def
  have hgLcut : ContDiffOn ℝ ∞ (Function.uncurry gLcut) (Set.Ici (0:ℝ) ×ˢ U) :=
    contDiffOn_intervalCutoff_smul T hT (Function.uncurry g) hUopen hg'
  have hgRcut : ContDiffOn ℝ ∞ (Function.uncurry gRcut) (Set.Ici (0:ℝ) ×ˢ U) :=
    contDiffOn_intervalCutoff_smul T hT (Function.uncurry gR) hUopen hgR'
  -- The two parametrized coefficient families.
  set aL : ℕ → E → F :=
    fun n z => ρ z • iteratedDerivWithin n (fun s => gLcut s z) (Set.Ici 0) 0 with haL_def
  set aR : ℕ → E → F :=
    fun n z => ρ z • iteratedDerivWithin n (fun s => gRcut s z) (Set.Ici 0) 0 with haR_def
  have haL : ∀ n, ContDiff ℝ ∞ (aL n) := fun n =>
    contDiff_cutoff_smul hUopen hρ_smooth hρ_tsupp (param_jet_contDiffOn gLcut U hgLcut n)
  have haR : ∀ n, ContDiff ℝ ∞ (aR n) := fun n =>
    contDiff_cutoff_smul hUopen hρ_smooth hρ_tsupp (param_jet_contDiffOn gRcut U hgRcut n)
  have hsuppL : ∀ n, HasCompactSupport (aL n) := fun n => hρ_cs.smul_right
  have hsuppR : ∀ n, HasCompactSupport (aR n) := fun n => hρ_cs.smul_right
  -- The two Borel series and the reflected right extension.
  set Lext : ℝ × E → F := fun p => ∑' n, paramTerm aL haL hsuppL n p with hLext_def
  set RΦ : ℝ × E → F := fun p => ∑' n, paramTerm aR haR hsuppR n p with hRΦ_def
  set Rext : ℝ → E → F := fun t z => RΦ (T - t, z) with hRext_def
  have hLextC : ContDiff ℝ ∞ Lext := paramSeries_contDiff aL haL hsuppL
  have hRΦC : ContDiff ℝ ∞ RΦ := paramSeries_contDiff aR haR hsuppR
  have hRextC : ContDiff ℝ ∞ (Function.uncurry Rext) := by
    have hmap : ContDiff ℝ ∞ (fun p : ℝ × E => ((T - p.1 : ℝ), p.2)) :=
      (contDiff_const.sub contDiff_fst).prodMk contDiff_snd
    exact hRΦC.comp hmap
  -- The extension.
  set gext : ℝ → E → F :=
    fun t z => if t < 0 then Lext (t, z) else if t ≤ T then g t z else Rext t z with hgext_def
  -- An open neighbourhood `V ∋ z₀`, `V ⊆ U`, on which `ρ ≡ 1`.
  have hVnhds : {z : E | ρ z = 1} ∩ U ∈ nhds z₀ :=
    Filter.inter_mem hρ_eq1 (hUopen.mem_nhds hz₀)
  obtain ⟨V, hVsub, hVopen, hz₀V⟩ := mem_nhds_iff.1 hVnhds
  have hρV : ∀ z ∈ V, ρ z = 1 := fun z hz => (hVsub hz).1
  have hVU : V ⊆ U := fun z hz => (hVsub hz).2
  -- `g` and the reflected extension are smooth on the relevant slabs over `V`.
  have hgV : ContDiffOn ℝ ∞ (Function.uncurry g) (Set.Icc (0:ℝ) T ×ˢ V) :=
    hg.mono (Set.prod_mono_right (hVU.trans interior_subset))
  have hgRV : ContDiffOn ℝ ∞ (Function.uncurry gR) (Set.Icc (0:ℝ) T ×ˢ V) :=
    hgR'.mono (Set.prod_mono_right hVU)
  -- The one-sided `t`-jet of the left series at `0` realizes `g`'s one-sided `t`-jet (`ρ ≡ 1`).
  have hjetL : ∀ i : ℕ, ∀ w ∈ V, iteratedDerivWithin i (fun t => Lext (t, w)) (Set.Ici 0) 0
      = iteratedDerivWithin i (fun t => Function.uncurry g (t, w)) (Set.Ici 0) 0 := by
    intro i w hw
    have hLHS : iteratedDerivWithin i (fun t => Lext (t, w)) (Set.Ici 0) 0 = aL i w := by
      have hsliceAt : ContDiffAt ℝ (i : WithTop ℕ∞) (fun t => Lext (t, w)) 0 :=
        (hLextC.comp (contDiff_id.prodMk contDiff_const)).contDiffAt.of_le (by exact_mod_cast le_top)
      rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ici 0) hsliceAt Set.self_mem_Ici]
      have heq : (fun t => Lext (t, w)) = fun t => ∑' n, paramTerm aL haL hsuppL n (t, w) := by
        funext t; rw [hLext_def]
      rw [heq, paramSeries_slice_iteratedDeriv_zero aL haL hsuppL i w]
    rw [hLHS, haL_def]
    simp only [hρV w hw, one_smul]
    refine Filter.EventuallyEq.iteratedDerivWithin_eq ?_ ?_
    · filter_upwards [mem_nhdsWithin_of_mem_nhds
        (Iio_mem_nhds (show (0:ℝ) < T / 2 by positivity))] with t ht
      change intervalCutoff T t • g t w = Function.uncurry g (t, w)
      rw [intervalCutoff_eq_one T hT (le_of_lt ht), one_smul]; rfl
    · change intervalCutoff T (0:ℝ) • g 0 w = Function.uncurry g (0, w)
      rw [intervalCutoff_eq_one T hT (by positivity), one_smul]; rfl
  -- The one-sided `t`-jet of the right series at `0` realizes `gR`'s one-sided `t`-jet (`ρ ≡ 1`).
  have hjetR : ∀ i : ℕ, ∀ w ∈ V, iteratedDerivWithin i (fun t => RΦ (t, w)) (Set.Ici 0) 0
      = iteratedDerivWithin i (fun t => Function.uncurry gR (t, w)) (Set.Ici 0) 0 := by
    intro i w hw
    have hLHS : iteratedDerivWithin i (fun t => RΦ (t, w)) (Set.Ici 0) 0 = aR i w := by
      have hsliceAt : ContDiffAt ℝ (i : WithTop ℕ∞) (fun t => RΦ (t, w)) 0 :=
        (hRΦC.comp (contDiff_id.prodMk contDiff_const)).contDiffAt.of_le (by exact_mod_cast le_top)
      rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ici 0) hsliceAt Set.self_mem_Ici]
      have heq : (fun t => RΦ (t, w)) = fun t => ∑' n, paramTerm aR haR hsuppR n (t, w) := by
        funext t; rw [hRΦ_def]
      rw [heq, paramSeries_slice_iteratedDeriv_zero aR haR hsuppR i w]
    rw [hLHS, haR_def]
    simp only [hρV w hw, one_smul]
    refine Filter.EventuallyEq.iteratedDerivWithin_eq ?_ ?_
    · filter_upwards [mem_nhdsWithin_of_mem_nhds
        (Iio_mem_nhds (show (0:ℝ) < T / 2 by positivity))] with t ht
      change intervalCutoff T t • gR t w = Function.uncurry gR (t, w)
      rw [intervalCutoff_eq_one T hT (le_of_lt ht), one_smul]; rfl
    · change intervalCutoff T (0:ℝ) • gR 0 w = Function.uncurry gR (0, w)
      rw [intervalCutoff_eq_one T hT (by positivity), one_smul]; rfl
  -- Value matches at the two seams: only the `n = 0` term survives at the seam, `ρ ≡ 1`, `χ(0) = 1`.
  have hbump0 : borelBumpMono 0 0 = 1 := by
    rw [borelBumpMono, borelCutoff_eq_one (by norm_num : (0:ℝ) ^ 2 ≤ 1)]; norm_num
  have hseamval : ∀ (a : ℕ → E → F) (ha : ∀ n, ContDiff ℝ ∞ (a n))
      (hsupp : ∀ n, HasCompactSupport (a n)) (w : E),
      (∑' n, paramTerm a ha hsupp n (0, w)) = a 0 w := by
    intro a ha hsupp w
    have hterm0 : ∀ n, paramTerm a ha hsupp n (0, w) = (if n = 0 then (1:ℝ) else 0) • a n w := by
      intro n
      have hp1 : (((0:ℝ), w) : ℝ × E).1 = 0 := rfl
      rw [paramTerm, hp1, mul_zero]
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn; rw [if_pos rfl, hbump0]; simp
      · rw [if_neg (by omega : ¬ n = 0), borelBumpMono, zero_pow (by omega : n ≠ 0)]; simp
    rw [tsum_congr hterm0, tsum_eq_single 0 (fun n hn => by rw [if_neg hn, zero_smul]),
      if_pos rfl, one_smul]
  have hLext0 : ∀ z ∈ V, Lext (0, z) = g 0 z := by
    intro z hz
    rw [hLext_def]
    change (∑' n, paramTerm aL haL hsuppL n (0, z)) = g 0 z
    rw [hseamval aL haL hsuppL z, haL_def]
    change ρ z • iteratedDerivWithin 0 (fun s => gLcut s z) (Set.Ici 0) 0 = g 0 z
    rw [hρV z hz, one_smul, iteratedDerivWithin_zero, hgLcut_def]
    change intervalCutoff T 0 • g 0 z = g 0 z
    rw [intervalCutoff_eq_one T hT (by positivity), one_smul]
  have hRextT : ∀ z ∈ V, Rext T z = g T z := by
    intro z hz
    rw [hRext_def]
    change RΦ (T - T, z) = g T z
    rw [sub_self, hRΦ_def]
    change (∑' n, paramTerm aR haR hsuppR n (0, z)) = g T z
    rw [hseamval aR haR hsuppR z, haR_def]
    change ρ z • iteratedDerivWithin 0 (fun s => gRcut s z) (Set.Ici 0) 0 = g T z
    rw [hρV z hz, one_smul, iteratedDerivWithin_zero, hgRcut_def]
    change intervalCutoff T 0 • gR 0 z = g T z
    rw [intervalCutoff_eq_one T hT (by positivity), one_smul, hgR_def]
    change g (T - 0) z = g T z
    rw [sub_zero]
  refine ⟨gext, V, hVopen.mem_nhds hz₀V, ?_, ?_⟩
  · -- Joint `C∞` of `uncurry gext` on the full slab `univ ×ˢ V`, via a three-piece, two-seam glue.
    have hUDl : UniqueDiffOn ℝ (Set.Iic (0:ℝ) ×ˢ V) :=
      UniqueDiffOn.prod (uniqueDiffOn_Iic 0) hVopen.uniqueDiffOn
    have hUDm : UniqueDiffOn ℝ (Set.Icc (0:ℝ) T ×ˢ V) :=
      UniqueDiffOn.prod (uniqueDiffOn_Icc hT) hVopen.uniqueDiffOn
    have hUDr : UniqueDiffOn ℝ (Set.Ici T ×ˢ V) :=
      UniqueDiffOn.prod (uniqueDiffOn_Ici T) hVopen.uniqueDiffOn
    -- The three one-sided Taylor series.
    set pL : ℝ × E → FormalMultilinearSeries ℝ (ℝ × E) F :=
      ftaylorSeriesWithin ℝ Lext (Set.Iic (0:ℝ) ×ˢ V) with hpL_def
    set pM : ℝ × E → FormalMultilinearSeries ℝ (ℝ × E) F :=
      ftaylorSeriesWithin ℝ (Function.uncurry g) (Set.Icc (0:ℝ) T ×ˢ V) with hpM_def
    set pR : ℝ × E → FormalMultilinearSeries ℝ (ℝ × E) F :=
      ftaylorSeriesWithin ℝ (Function.uncurry Rext) (Set.Ici T ×ˢ V) with hpR_def
    have hTL : HasFTaylorSeriesUpToOn ∞ Lext pL (Set.Iic (0:ℝ) ×ˢ V) :=
      hLextC.contDiffOn.ftaylorSeriesWithin hUDl
    have hTM : HasFTaylorSeriesUpToOn ∞ (Function.uncurry g) pM (Set.Icc (0:ℝ) T ×ˢ V) :=
      hgV.ftaylorSeriesWithin hUDm
    have hTR : HasFTaylorSeriesUpToOn ∞ (Function.uncurry Rext) pR (Set.Ici T ×ˢ V) :=
      hRextC.contDiffOn.ftaylorSeriesWithin hUDr
    -- **LEFT SEAM coefficient match**: `pL (0,z) = pM (0,z)` for `z ∈ V`.
    have hLM : ∀ (n : ℕ) (z : E), z ∈ V → pL (0, z) n = pM (0, z) n := by
      intro n z hz
      simp only [hpL_def, hpM_def, ftaylorSeriesWithin]
      exact prodMatch_intervalCutoff T hT Lext hLextC (Function.uncurry g) hVopen hgV hjetL n hz
    -- **RIGHT SEAM coefficient match**: `pM (T,z) = pR (T,z)` for `z ∈ V`.
    have hMR : ∀ (n : ℕ) (z : E), z ∈ V → pM (T, z) n = pR (T, z) n := by
      intro n z hz
      simp only [hpM_def, hpR_def, ftaylorSeriesWithin]
      -- Transport both seam coefficients through the reflection `(t,z) ↦ (T-t,z)`.
      have hpreM : (fun p : ℝ × E => ((T - p.1 : ℝ), p.2)) ⁻¹' (Set.Icc (0:ℝ) T ×ˢ V)
          = Set.Icc (0:ℝ) T ×ˢ V := by
        ext q
        simp only [Set.mem_preimage, Set.mem_prod, Set.mem_Icc]
        constructor
        · rintro ⟨⟨h1, h2⟩, hv⟩; exact ⟨⟨by linarith, by linarith⟩, hv⟩
        · rintro ⟨⟨h1, h2⟩, hv⟩; exact ⟨⟨by linarith, by linarith⟩, hv⟩
      have hpreR : (fun p : ℝ × E => ((T - p.1 : ℝ), p.2)) ⁻¹' (Set.Ici T ×ˢ V)
          = Set.Iic (0:ℝ) ×ˢ V := by
        ext q
        simp only [Set.mem_preimage, Set.mem_prod, Set.mem_Ici, Set.mem_Iic]
        exact ⟨fun ⟨h1, hv⟩ => ⟨by linarith, hv⟩, fun ⟨h1, hv⟩ => ⟨by linarith, hv⟩⟩
      have hmemTg : (T - ((0:ℝ), z).1, ((0:ℝ), z).2) ∈ Set.Icc (0:ℝ) T ×ˢ V := by
        simp only [sub_zero]
        exact ⟨Set.mem_Icc.mpr ⟨le_of_lt hT, le_refl T⟩, hz⟩
      have hmemTr : (T - ((0:ℝ), z).1, ((0:ℝ), z).2) ∈ Set.Ici T ×ˢ V := by
        simp only [sub_zero]
        exact ⟨Set.mem_Ici.mpr (le_refl T), hz⟩
      have hTg := reflect_iteratedFDerivWithin T (Function.uncurry g) n (Set.Icc (0:ℝ) T ×ˢ V)
        (0, z) hUDm hmemTg
      have hTr := reflect_iteratedFDerivWithin T (Function.uncurry Rext) n (Set.Ici T ×ˢ V)
        (0, z) hUDr hmemTr
      simp only [sub_zero] at hTg hTr
      rw [hpreM] at hTg
      rw [hpreR] at hTr
      -- `uncurry gR = fun p => uncurry g (T - p.1, p.2)` and `RΦ = fun p => uncurry Rext (T-p.1,p.2)`.
      have hgReq : (fun p : ℝ × E => Function.uncurry g (T - p.1, p.2)) = Function.uncurry gR := by
        funext p; rfl
      have hRΦeq : (fun p : ℝ × E => Function.uncurry Rext (T - p.1, p.2)) = RΦ := by
        funext p
        change RΦ (T - (T - p.1), p.2) = RΦ p
        rw [sub_sub_cancel]
      rw [hgReq] at hTg
      rw [hRΦeq] at hTr
      -- Reflected match via the left-seam bridge applied to `(RΦ, uncurry gR)`.
      have hM : iteratedFDerivWithin ℝ n RΦ (Set.Iic (0:ℝ) ×ˢ V) (0, z)
          = iteratedFDerivWithin ℝ n (Function.uncurry gR) (Set.Icc (0:ℝ) T ×ˢ V) (0, z) :=
        prodMatch_intervalCutoff T hT RΦ hRΦC (Function.uncurry gR) hVopen hgRV hjetR n hz
      -- Combine: the two reflected coefficients agree, hence (compCLM injective) the seam ones.
      have hcompeq : (iteratedFDerivWithin ℝ n (Function.uncurry g) (Set.Icc (0:ℝ) T ×ˢ V) (T, z)
            ).compContinuousLinearMap
            (fun _ => ((reflectFst : (ℝ × E) ≃L[ℝ] (ℝ × E)) : (ℝ × E) →L[ℝ] (ℝ × E)))
          = (iteratedFDerivWithin ℝ n (Function.uncurry Rext) (Set.Ici T ×ˢ V) (T, z)
            ).compContinuousLinearMap
            (fun _ => ((reflectFst : (ℝ × E) ≃L[ℝ] (ℝ × E)) : (ℝ × E) →L[ℝ] (ℝ × E))) := by
        rw [← hTg, ← hTr, hM]
      -- `·.compContinuousLinearMap reflectFst` is injective (it has the inverse `reflectFst.symm`).
      have hroundtrip : ∀ w : (ℝ × E) [×n]→L[ℝ] F,
          (w.compContinuousLinearMap
              (fun _ => ((reflectFst : (ℝ × E) ≃L[ℝ] (ℝ × E)) : (ℝ × E) →L[ℝ] (ℝ × E)))
            ).compContinuousLinearMap
              (fun _ => ((reflectFst.symm : (ℝ × E) ≃L[ℝ] (ℝ × E))
                : (ℝ × E) →L[ℝ] (ℝ × E))) = w := by
        intro w; ext1 m; simp
      have hcancel := congrArg (fun w : (ℝ × E) [×n]→L[ℝ] F =>
          w.compContinuousLinearMap
            (fun _ => ((reflectFst.symm : (ℝ × E) ≃L[ℝ] (ℝ × E)) : (ℝ × E) →L[ℝ] (ℝ × E))))
        hcompeq
      simp only at hcancel
      rwa [hroundtrip, hroundtrip] at hcancel
    -- The candidate joint series, assembled piecewise across the two seams.
    set p : ℝ × E → FormalMultilinearSeries ℝ (ℝ × E) F :=
      fun q => if q.1 < 0 then pL q else if q.1 ≤ T then pM q else pR q with hp_def
    -- `uncurry gext` agrees with the three pieces on their closed slabs.
    have hEqL : Set.EqOn (Function.uncurry gext) Lext (Set.Iic (0:ℝ) ×ˢ V) := by
      rintro ⟨t, z⟩ ⟨ht, hz⟩
      simp only [Set.mem_Iic] at ht
      rcases eq_or_lt_of_le ht with ht0 | ht0
      · subst ht0
        simp only [Function.uncurry, hgext_def, lt_irrefl, if_false, le_of_lt hT, ite_true]
        exact (hLext0 z hz).symm
      · simp only [Function.uncurry, hgext_def, if_pos ht0]
    have hEqM : Set.EqOn (Function.uncurry gext) (Function.uncurry g) (Set.Icc (0:ℝ) T ×ˢ V) := by
      rintro ⟨t, z⟩ ⟨ht, _⟩
      simp only [Set.mem_Icc] at ht
      simp only [Function.uncurry, hgext_def, if_neg (not_lt.mpr ht.1), if_pos ht.2]
    have hEqR : Set.EqOn (Function.uncurry gext) (Function.uncurry Rext) (Set.Ici T ×ˢ V) := by
      rintro ⟨t, z⟩ ⟨ht, hz⟩
      simp only [Set.mem_Ici] at ht
      rcases eq_or_lt_of_le ht with htT | htT
      · subst htT
        simp only [Function.uncurry, hgext_def, if_neg (not_lt.mpr (le_of_lt hT)),
          if_pos (le_refl T)]
        exact (hRextT z hz).symm
      · simp only [Function.uncurry, hgext_def, if_neg (not_lt.mpr (le_of_lt (lt_trans hT htT))),
          if_neg (not_le.mpr htT)]
    -- `p` agrees with each piece's series on the corresponding closed slab.
    have hEqpL : ∀ m : ℕ, Set.EqOn (fun q => p q m) (fun q => pL q m) (Set.Iic (0:ℝ) ×ˢ V) := by
      intro m q hq
      rcases lt_or_ge q.1 0 with hq0 | hq0
      · simp only [hp_def, if_pos hq0]
      · have hq0' : q.1 = 0 := le_antisymm (Set.mem_Iic.mp hq.1) hq0
        obtain ⟨t, z⟩ := q
        simp only at hq0'
        subst hq0'
        simp only [hp_def, lt_irrefl, if_false, le_of_lt hT, ite_true]
        exact (hLM m z hq.2).symm
    have hEqpM : ∀ m : ℕ, Set.EqOn (fun q => p q m) (fun q => pM q m) (Set.Icc (0:ℝ) T ×ˢ V) := by
      intro m q hq
      have ht := Set.mem_Icc.mp hq.1
      simp only [hp_def, if_neg (not_lt.mpr ht.1), if_pos ht.2]
    have hEqpR : ∀ m : ℕ, Set.EqOn (fun q => p q m) (fun q => pR q m) (Set.Ici T ×ˢ V) := by
      intro m q hq
      rcases eq_or_lt_of_le (Set.mem_Ici.mp hq.1) with hqT | hqT
      · have hq1 : q.1 = T := hqT.symm
        simp only [hp_def, hq1, if_neg (not_lt.mpr (le_of_lt hT)), if_pos (le_refl T)]
        have : q = (T, q.2) := by rw [← hq1]
        rw [this]; exact hMR m q.2 hq.2
      · simp only [hp_def, if_neg (not_lt.mpr (le_of_lt (lt_trans hT hqT))), if_neg (not_le.mpr hqT)]
    -- The zero-th coefficient yields the value of `uncurry gext`.
    have hzero : ∀ q ∈ Set.univ ×ˢ V, (p q 0).curry0 = Function.uncurry gext q := by
      rintro ⟨t, z⟩ ⟨_, hz⟩
      rcases lt_trichotomy t 0 with ht | ht | ht
      · have hmem : (t, z) ∈ Set.Iic (0:ℝ) ×ˢ V := ⟨Set.mem_Iic.mpr (le_of_lt ht), hz⟩
        rw [hp_def]; simp only [if_pos ht]
        rw [hTL.zero_eq (t, z) hmem, hEqL hmem]
      · subst ht
        have hmem : ((0:ℝ), z) ∈ Set.Icc (0:ℝ) T ×ˢ V :=
          ⟨Set.mem_Icc.mpr ⟨le_refl 0, le_of_lt hT⟩, hz⟩
        rw [hp_def]; simp only [lt_irrefl, if_false, le_of_lt hT, ite_true]
        rw [hTM.zero_eq (0, z) hmem, hEqM hmem]
      · rcases le_or_gt t T with htT | htT
        · have hmem : (t, z) ∈ Set.Icc (0:ℝ) T ×ˢ V :=
            ⟨Set.mem_Icc.mpr ⟨le_of_lt ht, htT⟩, hz⟩
          rw [hp_def]; simp only [if_neg (not_lt.mpr (le_of_lt ht)), if_pos htT]
          rw [hTM.zero_eq (t, z) hmem, hEqM hmem]
        · have hmem : (t, z) ∈ Set.Ici T ×ˢ V := ⟨Set.mem_Ici.mpr (le_of_lt htT), hz⟩
          rw [hp_def]
          simp only [if_neg (not_lt.mpr (le_of_lt (lt_trans hT htT))), if_neg (not_le.mpr htT)]
          rw [hTR.zero_eq (t, z) hmem, hEqR hmem]
    have hm_lt : ∀ m : ℕ, (m : WithTop ℕ∞) < ∞ := fun m => by
      exact_mod_cast (Nat.cast_lt.mpr m.lt_succ_self).trans_le le_top
    -- The per-order derivative obligation on `univ ×ˢ V`.
    have hderiv : ∀ (m : ℕ), ∀ q ∈ Set.univ ×ˢ V,
        HasFDerivWithinAt (fun y => p y m) (p q m.succ).curryLeft (Set.univ ×ˢ V) q := by
      intro m q hq
      obtain ⟨t, z⟩ := q
      have hz : z ∈ V := hq.2
      rcases lt_trichotomy t 0 with ht | ht | ht
      · -- t < 0: interior of the lower slab.
        have hmem : (t, z) ∈ Set.Iic (0:ℝ) ×ˢ V := ⟨Set.mem_Iic.mpr (le_of_lt ht), hz⟩
        have hdL : HasFDerivWithinAt (fun y => pL y m) (pL (t, z) m.succ).curryLeft
            (Set.Iic (0:ℝ) ×ˢ V) (t, z) := hTL.fderivWithin m (hm_lt m) (t, z) hmem
        have hnhds : Set.Iio (0:ℝ) ×ˢ V ∈ nhds (t, z) :=
          prod_mem_nhds (Iio_mem_nhds ht) (hVopen.mem_nhds hz)
        have hsub : Set.Iio (0:ℝ) ×ˢ V ⊆ Set.Iic (0:ℝ) ×ˢ V :=
          Set.prod_mono_left Iio_subset_Iic_self
        have hfd : HasFDerivAt (fun y => p y m) (pL (t, z) m.succ).curryLeft (t, z) :=
          ((hdL.mono hsub).hasFDerivAt hnhds).congr_of_eventuallyEq
            (Filter.eventuallyEq_of_mem hnhds (fun y hy => hEqpL m (hsub hy)))
        rw [hp_def]; simp only [if_pos ht]
        exact hfd.hasFDerivWithinAt
      · -- t = 0: LEFT seam. Work on the nbhd `Iio T ×ˢ V`, glue lower with middle.
        subst ht
        have hu : Set.Iio T ×ˢ V ∈ nhds ((0:ℝ), z) :=
          prod_mem_nhds (Iio_mem_nhds hT) (hVopen.mem_nhds hz)
        have hmemL : ((0:ℝ), z) ∈ Set.Iic (0:ℝ) ×ˢ V := ⟨Set.self_mem_Iic, hz⟩
        have hmemM : ((0:ℝ), z) ∈ Set.Icc (0:ℝ) T ×ˢ V :=
          ⟨Set.mem_Icc.mpr ⟨le_refl 0, le_of_lt hT⟩, hz⟩
        have hdL0 : HasFDerivWithinAt (fun y => p y m) (pL (0, z) m.succ).curryLeft
            (Set.Iic (0:ℝ) ×ˢ V) (0, z) :=
          (hTL.fderivWithin m (hm_lt m) (0, z) hmemL).congr (hEqpL m) (hEqpL m hmemL)
        have hdM0 : HasFDerivWithinAt (fun y => p y m) (pL (0, z) m.succ).curryLeft
            (Set.Icc (0:ℝ) T ×ˢ V) (0, z) := by
          have hval : (pM (0, z) m.succ).curryLeft = (pL (0, z) m.succ).curryLeft := by
            rw [hLM m.succ z hz]
          rw [← hval]
          exact (hTM.fderivWithin m (hm_lt m) (0, z) hmemM).congr (hEqpM m) (hEqpM m hmemM)
        have hunion := hdL0.union hdM0
        rw [← Set.union_prod, Set.Iic_union_Icc_eq_Iic (le_of_lt hT)] at hunion
        have hmono : HasFDerivWithinAt (fun y => p y m) (pL (0, z) m.succ).curryLeft
            (Set.Iio T ×ˢ V) (0, z) :=
          hunion.mono (Set.prod_mono_left Iio_subset_Iic_self)
        have hinter : (Set.univ ×ˢ V) ∩ (Set.Iio T ×ˢ V) = Set.Iio T ×ˢ V := by
          rw [Set.prod_inter_prod, Set.univ_inter, Set.inter_self]
        have hmono' : HasFDerivWithinAt (fun y => p y m) (pL (0, z) m.succ).curryLeft
            ((Set.univ ×ˢ V) ∩ (Set.Iio T ×ˢ V)) (0, z) := by rw [hinter]; exact hmono
        have hres := (hasFDerivWithinAt_inter hu).mp hmono'
        rw [hLM m.succ z hz] at hres
        rw [hp_def]; simp only [lt_irrefl, if_false, le_of_lt hT, ite_true]
        exact hres
      · -- t > 0.
        rcases lt_trichotomy t T with htT | htT | htT
        · -- 0 < t < T: interior of the middle slab.
          have hmem : (t, z) ∈ Set.Icc (0:ℝ) T ×ˢ V :=
            ⟨Set.mem_Icc.mpr ⟨le_of_lt ht, le_of_lt htT⟩, hz⟩
          have hdM : HasFDerivWithinAt (fun y => pM y m) (pM (t, z) m.succ).curryLeft
              (Set.Icc (0:ℝ) T ×ˢ V) (t, z) := hTM.fderivWithin m (hm_lt m) (t, z) hmem
          have hnhds : Set.Ioo (0:ℝ) T ×ˢ V ∈ nhds (t, z) :=
            prod_mem_nhds (Ioo_mem_nhds ht htT) (hVopen.mem_nhds hz)
          have hsub : Set.Ioo (0:ℝ) T ×ˢ V ⊆ Set.Icc (0:ℝ) T ×ˢ V :=
            Set.prod_mono_left Ioo_subset_Icc_self
          have hfd : HasFDerivAt (fun y => p y m) (pM (t, z) m.succ).curryLeft (t, z) :=
            ((hdM.mono hsub).hasFDerivAt hnhds).congr_of_eventuallyEq
              (Filter.eventuallyEq_of_mem hnhds (fun y hy => hEqpM m (hsub hy)))
          rw [hp_def]; simp only [if_neg (not_lt.mpr (le_of_lt ht)), if_pos (le_of_lt htT)]
          exact hfd.hasFDerivWithinAt
        · -- t = T: RIGHT seam. Work on the nbhd `Ioi 0 ×ˢ V`, glue middle with right.
          subst htT
          have hu : Set.Ioi (0:ℝ) ×ˢ V ∈ nhds (t, z) :=
            prod_mem_nhds (Ioi_mem_nhds hT) (hVopen.mem_nhds hz)
          have hmemM : (t, z) ∈ Set.Icc (0:ℝ) t ×ˢ V :=
            ⟨Set.mem_Icc.mpr ⟨le_of_lt hT, le_refl t⟩, hz⟩
          have hmemR : (t, z) ∈ Set.Ici t ×ˢ V := ⟨Set.self_mem_Ici, hz⟩
          have hdM0 : HasFDerivWithinAt (fun y => p y m) (pM (t, z) m.succ).curryLeft
              (Set.Icc (0:ℝ) t ×ˢ V) (t, z) :=
            (hTM.fderivWithin m (hm_lt m) (t, z) hmemM).congr (hEqpM m) (hEqpM m hmemM)
          have hdR0 : HasFDerivWithinAt (fun y => p y m) (pM (t, z) m.succ).curryLeft
              (Set.Ici t ×ˢ V) (t, z) := by
            have hval : (pR (t, z) m.succ).curryLeft = (pM (t, z) m.succ).curryLeft := by
              rw [hMR m.succ z hz]
            rw [← hval]
            exact (hTR.fderivWithin m (hm_lt m) (t, z) hmemR).congr (hEqpR m) (hEqpR m hmemR)
          have hunion := hdM0.union hdR0
          rw [← Set.union_prod, Set.Icc_union_Ici_eq_Ici (le_of_lt hT)] at hunion
          have hmono : HasFDerivWithinAt (fun y => p y m) (pM (t, z) m.succ).curryLeft
              (Set.Ioi (0:ℝ) ×ˢ V) (t, z) :=
            hunion.mono (Set.prod_mono_left Ioi_subset_Ici_self)
          rw [hp_def]; simp only [if_neg (not_lt.mpr (le_of_lt hT)), if_pos (le_refl t)]
          have hinter : (Set.univ ×ˢ V) ∩ (Set.Ioi (0:ℝ) ×ˢ V) = Set.Ioi (0:ℝ) ×ˢ V := by
            rw [Set.prod_inter_prod, Set.univ_inter, Set.inter_self]
          have hmono' : HasFDerivWithinAt (fun y => p y m) (pM (t, z) m.succ).curryLeft
              ((Set.univ ×ˢ V) ∩ (Set.Ioi (0:ℝ) ×ˢ V)) (t, z) := by rw [hinter]; exact hmono
          have hres := (hasFDerivWithinAt_inter hu).mp hmono'
          simpa only [hp_def, if_neg (not_lt.mpr (le_of_lt hT)), if_pos (le_refl t)] using hres
        · -- t > T: interior of the upper slab.
          have hmem : (t, z) ∈ Set.Ici T ×ˢ V := ⟨Set.mem_Ici.mpr (le_of_lt htT), hz⟩
          have hdR : HasFDerivWithinAt (fun y => pR y m) (pR (t, z) m.succ).curryLeft
              (Set.Ici T ×ˢ V) (t, z) := hTR.fderivWithin m (hm_lt m) (t, z) hmem
          have hnhds : Set.Ioi T ×ˢ V ∈ nhds (t, z) :=
            prod_mem_nhds (Ioi_mem_nhds htT) (hVopen.mem_nhds hz)
          have hsub : Set.Ioi T ×ˢ V ⊆ Set.Ici T ×ˢ V :=
            Set.prod_mono_left Ioi_subset_Ici_self
          have hfd : HasFDerivAt (fun y => p y m) (pR (t, z) m.succ).curryLeft (t, z) :=
            ((hdR.mono hsub).hasFDerivAt hnhds).congr_of_eventuallyEq
              (Filter.eventuallyEq_of_mem hnhds (fun y hy => hEqpR m (hsub hy)))
          rw [hp_def]
          simp only [if_neg (not_lt.mpr (le_of_lt (lt_trans hT htT))), if_neg (not_le.mpr htT)]
          exact hfd.hasFDerivWithinAt
    have hTaylor : HasFTaylorSeriesUpToOn ∞ (Function.uncurry gext) p (Set.univ ×ˢ V) :=
      (hasFTaylorSeriesUpToOn_top_iff' (le_refl _)).mpr ⟨hzero, hderiv⟩
    exact hTaylor.contDiffOn
  · -- Agreement with `g` on `[0, T]`, on all of `V`.
    intro t ht z _
    obtain ⟨ht0, htT⟩ := ht
    simp only [hgext_def, if_neg (not_lt.mpr ht0), if_pos htT]

end Setup

end Analysis
end DifferentialGeometry
