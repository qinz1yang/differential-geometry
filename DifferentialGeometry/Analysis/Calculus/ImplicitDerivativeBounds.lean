import DifferentialGeometry.Analysis.Calculus.RingInverseBounds

import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.FDeriv.Mul

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry
namespace Analysis

open scoped Topology
open Set

section ImplicitDerivativeBounds

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_fderiv_implicit_le
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (G : E → P → E) (z₀ : E) (params₀ : P)
    (f : P → E) (Df : P →L[ℝ] E)
    (Dj : (E × P) →L[ℝ] E) (L : E ≃L[ℝ] E) (Λ B : ℝ)
    (hf0 : f params₀ = z₀)
    (hf : HasFDerivAt f Df params₀)
    (hG : HasFDerivAt (fun w : E × P => G w.1 w.2) Dj (z₀, params₀))
    (hLd : HasFDerivAt (fun z : E => G z params₀) (L : E →L[ℝ] E) z₀)
    (hLinv : ‖(L.symm : E →L[ℝ] E)‖ ≤ Λ)
    (hB : ‖Dj‖ ≤ B)
    (hrel : ∀ᶠ params in nhds params₀, G (f params) params = 0) :
    ‖Df‖ ≤ Λ * B := by
  have hk : HasFDerivAt (fun z : E => (z, params₀))
      (ContinuousLinearMap.inl ℝ E P) z₀ :=
    (hasFDerivAt_id z₀).prodMk (hasFDerivAt_const params₀ z₀)
  have hLz : Dj.comp (ContinuousLinearMap.inl ℝ E P) = (L : E →L[ℝ] E) := by
    have h1 : HasFDerivAt ((fun w : E × P => G w.1 w.2) ∘
          (fun z : E => (z, params₀)))
        (Dj.comp (ContinuousLinearMap.inl ℝ E P)) z₀ := hG.comp z₀ hk
    exact h1.unique hLd
  have hDv : ∀ a : E, Dj (a, (0 : P)) = L a := by
    intro a
    have h := DFunLike.congr_fun hLz a
    simpa [ContinuousLinearMap.inl_apply] using h
  have hsplit : ∀ (a : E) (b : P), Dj (a, b) = L a + Dj ((0 : E), b) := by
    intro a b
    have hdecomp : ((a, b) : E × P)
        = (a, (0 : P)) + ((0 : E), b) :=
      Prod.ext (add_zero a).symm (zero_add b).symm
    rw [hdecomp, map_add, hDv]
  have hpair : HasFDerivAt (fun params : P => (f params, params))
      (Df.prod (ContinuousLinearMap.id ℝ P)) params₀ :=
    hf.prodMk (hasFDerivAt_id params₀)
  have hGf : HasFDerivAt (fun w : E × P => G w.1 w.2) Dj
    (f params₀, params₀) := by
    rw [hf0]; exact hG
  have hcomp := HasFDerivAt.comp (𝕜 := ℝ) (E := P)
      (F := E × P) (G := E)
      (f := fun params : P => (f params, params))
      (g := fun w : E × P => G w.1 w.2)
      params₀ hGf hpair
  have hc0 : HasFDerivAt (fun _ : P => (0 : E))
      (0 : P →L[ℝ] E) params₀ := hasFDerivAt_const (0 : E) params₀
  have hconst : HasFDerivAt ((fun w : E × P => G w.1 w.2) ∘
      (fun params : P => (f params, params)))
      (0 : P →L[ℝ] E) params₀ := by
    refine hc0.congr_of_eventuallyEq ?_
    filter_upwards [hrel] with params hp
    exact hp
  have hDeq : Dj.comp (Df.prod (ContinuousLinearMap.id ℝ P)) = 0 :=
    hcomp.unique hconst
  have hΛ0 : 0 ≤ Λ := le_trans (norm_nonneg _) hLinv
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) hB
  refine ContinuousLinearMap.opNorm_le_bound Df (mul_nonneg hΛ0 hB0) (fun v => ?_)
  have hzero : Dj (Df v, v) = 0 := by
    have hcf := DFunLike.congr_fun hDeq v
    simpa [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.id_apply] using hcf
  have hL0 : L (Df v) + Dj ((0 : E), v) = 0 := by rw [← hsplit (Df v) v]; exact hzero
  have hLval : L (Df v) = - Dj ((0 : E), v) := eq_neg_of_add_eq_zero_left hL0
  have hDfv : Df v = (L.symm : E →L[ℝ] E) (- Dj ((0 : E), v)) := by
    rw [ContinuousLinearEquiv.coe_coe, ← hLval, L.symm_apply_apply]
  rw [hDfv]
  calc ‖(L.symm : E →L[ℝ] E) (- Dj ((0 : E), v))‖
      ≤ ‖(L.symm : E →L[ℝ] E)‖ * ‖- Dj ((0 : E), v)‖ := (L.symm : E →L[ℝ] E).le_opNorm _
    _ = ‖(L.symm : E →L[ℝ] E)‖ * ‖Dj ((0 : E), v)‖ := by rw [norm_neg]
    _ ≤ Λ * (‖Dj‖ * ‖v‖) := by
        refine mul_le_mul hLinv ?_ (norm_nonneg _) hΛ0
        calc ‖Dj ((0 : E), v)‖ ≤ ‖Dj‖ * ‖((0 : E), v)‖ := Dj.le_opNorm _
          _ = ‖Dj‖ * ‖v‖ := by
              congr 1
              rw [Prod.norm_def]
              simp
    _ ≤ Λ * (B * ‖v‖) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hB (norm_nonneg _)) hΛ0
    _ = Λ * B * ‖v‖ := by ring

theorem implicit_fderiv_eq {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (G : E → P → E) (f : P → E) (p₀ : P)
    (Df : P →L[ℝ] E) (Dj : (E × P) →L[ℝ] E)
    (hf : HasFDerivAt f Df p₀)
    (hG : HasFDerivAt (fun w : E × P => G w.1 w.2) Dj (f p₀, p₀))
    (hrel : ∀ᶠ q in nhds p₀, G (f q) q = 0)
    (hinv : IsUnit (Dj.comp (ContinuousLinearMap.inl ℝ E P))) :
    Df = -(Ring.inverse (Dj.comp (ContinuousLinearMap.inl ℝ E P))).comp
        (Dj.comp (ContinuousLinearMap.inr ℝ E P)) := by
  have hpair : HasFDerivAt (fun q : P => (f q, q)) (Df.prod (ContinuousLinearMap.id ℝ P)) p₀ :=
    hf.prodMk (hasFDerivAt_id p₀)
  have hcomp := HasFDerivAt.comp (𝕜 := ℝ) (E := P) (F := E × P) (G := E)
      (f := fun q : P => (f q, q)) (g := fun w : E × P => G w.1 w.2) p₀ hG hpair
  have hconst : HasFDerivAt ((fun w : E × P => G w.1 w.2) ∘ (fun q : P => (f q, q)))
      (0 : P →L[ℝ] E) p₀ := by
    refine (hasFDerivAt_const (0 : E) p₀).congr_of_eventuallyEq ?_
    filter_upwards [hrel] with q hq; exact hq
  have hDeq : Dj.comp (Df.prod (ContinuousLinearMap.id ℝ P)) = 0 := hcomp.unique hconst
  have hADf : (Dj.comp (ContinuousLinearMap.inl ℝ E P)).comp Df
      = -(Dj.comp (ContinuousLinearMap.inr ℝ E P)) := by
    ext v
    have hv : Dj (Df v, v) = 0 := by
      have hcf := DFunLike.congr_fun hDeq v
      simpa [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
        ContinuousLinearMap.id_apply] using hcf
    have hsplit : Dj (Df v, v) = Dj (Df v, (0 : P)) + Dj ((0 : E), v) := by
      have hd : ((Df v, v) : E × P) = (Df v, (0 : P)) + ((0 : E), v) :=
        Prod.ext (add_zero _).symm (zero_add _).symm
      rw [hd, map_add]
    rw [hsplit] at hv
    have hval : Dj (Df v, (0 : P)) = -(Dj ((0 : E), v)) := eq_neg_of_add_eq_zero_left hv
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
      ContinuousLinearMap.inr_apply, neg_apply]
    exact hval
  have hcancel : (Ring.inverse (Dj.comp (ContinuousLinearMap.inl ℝ E P))).comp
      (Dj.comp (ContinuousLinearMap.inl ℝ E P)) = ContinuousLinearMap.id ℝ E := by
    rw [← ContinuousLinearMap.mul_def]
    exact (Ring.inverse_mul_cancel _ hinv).trans ContinuousLinearMap.one_def
  calc Df
      = (ContinuousLinearMap.id ℝ E).comp Df := (ContinuousLinearMap.id_comp Df).symm
    _ = ((Ring.inverse (Dj.comp (ContinuousLinearMap.inl ℝ E P))).comp
          (Dj.comp (ContinuousLinearMap.inl ℝ E P))).comp Df := by rw [hcancel]
    _ = (Ring.inverse (Dj.comp (ContinuousLinearMap.inl ℝ E P))).comp
          ((Dj.comp (ContinuousLinearMap.inl ℝ E P)).comp Df) :=
        ContinuousLinearMap.comp_assoc _ _ _
    _ = (Ring.inverse (Dj.comp (ContinuousLinearMap.inl ℝ E P))).comp
          (-(Dj.comp (ContinuousLinearMap.inr ℝ E P))) := by rw [hADf]
    _ = -(Ring.inverse (Dj.comp (ContinuousLinearMap.inl ℝ E P))).comp
          (Dj.comp (ContinuousLinearMap.inr ℝ E P)) := ContinuousLinearMap.comp_neg _ _

theorem implicit_fderiv_eventually_eq {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (G : E → P → E) (f : P → E) (params₀ : P)
    (Df : P → P →L[ℝ] E) (Dj : P → (E × P) →L[ℝ] E)
    (hf : ∀ᶠ p in nhds params₀, HasFDerivAt f (Df p) p)
    (hG : ∀ᶠ p in nhds params₀, HasFDerivAt (fun w : E × P => G w.1 w.2) (Dj p) (f p, p))
    (hrel : ∀ᶠ p in nhds params₀, G (f p) p = 0)
    (hinv : ∀ᶠ p in nhds params₀, IsUnit ((Dj p).comp (ContinuousLinearMap.inl ℝ E P))) :
    ∀ᶠ p in nhds params₀, fderiv ℝ f p
      = -(Ring.inverse ((Dj p).comp (ContinuousLinearMap.inl ℝ E P))).comp
          ((Dj p).comp (ContinuousLinearMap.inr ℝ E P)) := by
  filter_upwards [hf, hG, eventually_eventually_nhds.2 hrel, hinv] with p hfp hGp hrelp hinvp
  rw [hfp.fderiv]
  exact implicit_fderiv_eq G f p (Df p) (Dj p) hfp hGp hrelp hinvp

theorem exists_hasFDerivAt_graph_block_comp {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    (H : E × P → ((E × P) →L[ℝ] E)) (f : P → E) (params₀ : P) (Df₀ : P →L[ℝ] E)
    (H' : (E × P) →L[ℝ] ((E × P) →L[ℝ] E))
    (hfd : HasFDerivAt f Df₀ params₀)
    (hH : HasFDerivAt H H' (f params₀, params₀))
    (j : E' →L[ℝ] E × P) (hj : ‖j‖ ≤ 1) :
    ∃ D' : P →L[ℝ] (E' →L[ℝ] E),
      HasFDerivAt (fun p : P => (H (f p, p)).comp j) D' params₀ ∧
        ‖D'‖ ≤ ‖H'‖ * max ‖Df₀‖ 1 := by
  have hgraph : HasFDerivAt (fun p : P => (f p, p))
      (Df₀.prod (ContinuousLinearMap.id ℝ P)) params₀ :=
    hfd.prodMk (hasFDerivAt_id params₀)
  have hK := HasFDerivAt.comp (𝕜 := ℝ) (E := P) (F := E × P) (G := (E × P) →L[ℝ] E)
      (f := fun p : P => (f p, p)) (g := H) params₀ hH hgraph
  have hK' : HasFDerivAt (fun p : P => H (f p, p))
      (H'.comp (Df₀.prod (ContinuousLinearMap.id ℝ P))) params₀ := hK
  have hAd := hK'.clm_comp (hasFDerivAt_const j params₀)
  have hmax0 : (0 : ℝ) ≤ max ‖Df₀‖ 1 := le_trans zero_le_one (le_max_right _ _)
  refine ⟨_, hAd, ?_⟩
  refine ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (ContinuousLinearMap.opNorm_nonneg _) hmax0) fun v => ?_
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    zero_apply, map_zero, zero_add, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.compL_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.coe_id', id_eq]
  calc ‖(H' (Df₀ v, v)).comp j‖
      ≤ ‖H' (Df₀ v, v)‖ * ‖j‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖H' (Df₀ v, v)‖ * 1 := mul_le_mul_of_nonneg_left hj (norm_nonneg _)
    _ = ‖H' (Df₀ v, v)‖ := mul_one _
    _ ≤ ‖H'‖ * ‖((Df₀ v, v) : E × P)‖ := H'.le_opNorm _
    _ ≤ ‖H'‖ * (max ‖Df₀‖ 1 * ‖v‖) := by
        refine mul_le_mul_of_nonneg_left ?_ (ContinuousLinearMap.opNorm_nonneg H')
        rw [Prod.norm_def]
        refine max_le ?_ ?_
        · exact (Df₀.le_opNorm v).trans
            (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
        · calc ‖v‖ = 1 * ‖v‖ := (one_mul _).symm
            _ ≤ max ‖Df₀‖ 1 * ‖v‖ :=
                mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)
    _ = ‖H'‖ * max ‖Df₀‖ 1 * ‖v‖ := by ring

theorem norm_iteratedFDeriv_implicit_two_le {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [CompleteSpace E]
    (G : E → P → E) (f : P → E) (params₀ : P)
    (Df : P → P →L[ℝ] E) (Dj : P → (E × P) →L[ℝ] E)
    (A' : P →L[ℝ] (E →L[ℝ] E)) (B' : P →L[ℝ] (P →L[ℝ] E)) (Λ a₂ b₁ b₂ : ℝ)
    (hf : ∀ᶠ p in nhds params₀, HasFDerivAt f (Df p) p)
    (hG : ∀ᶠ p in nhds params₀, HasFDerivAt (fun w : E × P => G w.1 w.2) (Dj p) (f p, p))
    (hrel : ∀ᶠ p in nhds params₀, G (f p) p = 0)
    (hinv : ∀ᶠ p in nhds params₀, IsUnit ((Dj p).comp (ContinuousLinearMap.inl ℝ E P)))
    (hAd : HasFDerivAt (fun p : P => (Dj p).comp (ContinuousLinearMap.inl ℝ E P)) A' params₀)
    (hBd : HasFDerivAt (fun p : P => (Dj p).comp (ContinuousLinearMap.inr ℝ E P)) B' params₀)
    (hΛ : ‖Ring.inverse ((Dj params₀).comp (ContinuousLinearMap.inl ℝ E P))‖ ≤ Λ)
    (hb₁ : ‖(Dj params₀).comp (ContinuousLinearMap.inr ℝ E P)‖ ≤ b₁)
    (ha₂ : ‖A'‖ ≤ a₂) (hb₂ : ‖B'‖ ≤ b₂) :
    ‖iteratedFDeriv ℝ 2 f params₀‖ ≤ Λ ^ 2 * a₂ * b₁ + Λ * b₂ := by
  have hΛ0 : (0 : ℝ) ≤ Λ := le_trans (norm_nonneg _) hΛ
  have ha₂0 : (0 : ℝ) ≤ a₂ := le_trans (ContinuousLinearMap.opNorm_nonneg A') ha₂
  have hb₁0 : (0 : ℝ) ≤ b₁ := le_trans (norm_nonneg _) hb₁
  have hb₂0 : (0 : ℝ) ≤ b₂ := le_trans (ContinuousLinearMap.opNorm_nonneg B') hb₂
  have heq := implicit_fderiv_eventually_eq G f params₀ Df Dj hf hG hrel hinv
  obtain ⟨u, hu⟩ := hinv.self_of_nhds
  have hu_inv : ‖((↑u⁻¹ : E →L[ℝ] E))‖ ≤ Λ := by
    have h : Ring.inverse ((Dj params₀).comp (ContinuousLinearMap.inl ℝ E P))
        = (↑u⁻¹ : E →L[ℝ] E) := by rw [← hu, Ring.inverse_unit]
    rw [← h]; exact hΛ
  have hinv_d : HasFDerivAt (Ring.inverse : (E →L[ℝ] E) → (E →L[ℝ] E))
      (-(ContinuousLinearMap.mulLeftRight ℝ (E →L[ℝ] E) ↑u⁻¹ ↑u⁻¹))
      ((Dj params₀).comp (ContinuousLinearMap.inl ℝ E P)) := by
    rw [← hu]; exact hasFDerivAt_ringInverse (𝕜 := ℝ) u
  have hcA := HasFDerivAt.comp (𝕜 := ℝ) (E := P) (F := E →L[ℝ] E) (G := E →L[ℝ] E)
      (f := fun p : P => (Dj p).comp (ContinuousLinearMap.inl ℝ E P))
      (g := Ring.inverse) params₀ hinv_d hAd
  have hcA' : HasFDerivAt
      (fun p : P => Ring.inverse ((Dj p).comp (ContinuousLinearMap.inl ℝ E P)))
      ((-(ContinuousLinearMap.mulLeftRight ℝ (E →L[ℝ] E) ↑u⁻¹ ↑u⁻¹)).comp A') params₀ := hcA
  have hprod := hcA'.clm_comp hBd
  have hRHS := hprod.neg
  have hval := HasFDerivAt.fderiv (𝕜 := ℝ)
    (f := fun p : P =>
      -(Ring.inverse ((Dj p).comp (ContinuousLinearMap.inl ℝ E P))).comp
        ((Dj p).comp (ContinuousLinearMap.inr ℝ E P))) hRHS
  calc ‖iteratedFDeriv ℝ 2 f params₀‖
      = ‖fderiv ℝ (fderiv ℝ f) params₀‖ := by
        rw [← norm_iteratedFDeriv_one]
        exact (norm_iteratedFDeriv_fderiv).symm
    _ = ‖fderiv ℝ (fun p : P =>
          -(Ring.inverse ((Dj p).comp (ContinuousLinearMap.inl ℝ E P))).comp
            ((Dj p).comp (ContinuousLinearMap.inr ℝ E P))) params₀‖ := by
        rw [Filter.EventuallyEq.fderiv_eq heq]
    _ ≤ Λ ^ 2 * a₂ * b₁ + Λ * b₂ := by
        rw [hval]
        refine ContinuousLinearMap.opNorm_le_bound _
          (add_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hΛ0 2) ha₂0) hb₁0)
            (mul_nonneg hΛ0 hb₂0)) fun v => ?_
        simp only [neg_apply, add_apply,
          ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
          ContinuousLinearMap.compL_apply, norm_neg, ContinuousLinearMap.neg_comp]
        have h1 : ‖(Ring.inverse ((Dj params₀).comp (ContinuousLinearMap.inl ℝ E P))).comp
            (B' v)‖ ≤ Λ * (b₂ * ‖v‖) := by
          refine le_trans (ContinuousLinearMap.opNorm_comp_le _ _) ?_
          exact mul_le_mul hΛ
            (le_trans (B'.le_opNorm v) (mul_le_mul_of_nonneg_right hb₂ (norm_nonneg _)))
            (norm_nonneg _) hΛ0
        have h2 : ‖(ContinuousLinearMap.mulLeftRight ℝ (E →L[ℝ] E) ↑u⁻¹ ↑u⁻¹ (A' v)).comp
            ((Dj params₀).comp (ContinuousLinearMap.inr ℝ E P))‖
            ≤ Λ * Λ * (a₂ * ‖v‖) * b₁ := by
          refine le_trans (ContinuousLinearMap.opNorm_comp_le _ _) ?_
          refine mul_le_mul ?_ hb₁ (norm_nonneg _)
            (mul_nonneg (mul_nonneg hΛ0 hΛ0) (mul_nonneg ha₂0 (norm_nonneg _)))
          refine le_trans (ContinuousLinearMap.le_opNorm _ _) ?_
          exact mul_le_mul
            (le_trans (ContinuousLinearMap.opNorm_mulLeftRight_apply_apply_le ℝ _ _ _)
              (mul_le_mul hu_inv hu_inv (norm_nonneg _) hΛ0))
            (le_trans (A'.le_opNorm v) (mul_le_mul_of_nonneg_right ha₂ (norm_nonneg _)))
            (norm_nonneg _) (mul_nonneg hΛ0 hΛ0)
        calc ‖(Ring.inverse ((Dj params₀).comp (ContinuousLinearMap.inl ℝ E P))).comp (B' v)
              + -((ContinuousLinearMap.mulLeftRight ℝ (E →L[ℝ] E) ↑u⁻¹ ↑u⁻¹ (A' v)).comp
                  ((Dj params₀).comp (ContinuousLinearMap.inr ℝ E P)))‖
            ≤ ‖(Ring.inverse ((Dj params₀).comp (ContinuousLinearMap.inl ℝ E P))).comp (B' v)‖
              + ‖(ContinuousLinearMap.mulLeftRight ℝ (E →L[ℝ] E) ↑u⁻¹ ↑u⁻¹ (A' v)).comp
                  ((Dj params₀).comp (ContinuousLinearMap.inr ℝ E P))‖ := by
              refine le_trans (norm_add_le _ _) ?_
              rw [norm_neg]
          _ ≤ Λ * (b₂ * ‖v‖) + Λ * Λ * (a₂ * ‖v‖) * b₁ := add_le_add h1 h2
          _ = (Λ ^ 2 * a₂ * b₁ + Λ * b₂) * ‖v‖ := by ring

theorem ContinuousMultilinearMap.norm_prod_le_max {n : ℕ}
    {P F G : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (M : ContinuousMultilinearMap ℝ (fun _ : Fin n => P) F)
    (N : ContinuousMultilinearMap ℝ (fun _ : Fin n => P) G) :
    ‖M.prod N‖ ≤ max ‖M‖ ‖N‖ := by
  refine ContinuousMultilinearMap.opNorm_le_bound
    (le_max_of_le_left (norm_nonneg _)) fun m => ?_
  have hprod0 : (0 : ℝ) ≤ ∏ i, ‖m i‖ := Finset.prod_nonneg fun i _ => norm_nonneg _
  rw [ContinuousMultilinearMap.prod_apply, Prod.norm_def]
  refine max_le ?_ ?_
  · exact (M.le_opNorm m).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hprod0)
  · exact (N.le_opNorm m).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hprod0)

theorem norm_iteratedFDeriv_id_le_one {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (i : ℕ) (hi : 1 ≤ i) (x : P) :
    ‖iteratedFDeriv ℝ i (fun p : P => p) x‖ ≤ 1 := by
  obtain _ | k := i
  · omega
  · rw [← norm_iteratedFDeriv_fderiv]
    have hfd : (fderiv ℝ (fun p : P => p)) = fun _ : P => ContinuousLinearMap.id ℝ P := by
      funext y; exact fderiv_fun_id
    rw [hfd]
    obtain _ | l := k
    · rw [norm_iteratedFDeriv_zero]; exact ContinuousLinearMap.norm_id_le
    · rw [iteratedFDeriv_const_of_ne (Nat.succ_ne_zero l)]
      simp

theorem norm_iteratedFDeriv_graph_le {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {n : WithTop ℕ∞} (f : P → E) (x : P) (hf : ContDiffAt ℝ n f x)
    {i : ℕ} (hi : 1 ≤ i) (hin : (i : WithTop ℕ∞) ≤ n) :
    ‖iteratedFDeriv ℝ i (fun p : P => (f p, p)) x‖ ≤ max ‖iteratedFDeriv ℝ i f x‖ 1 := by
  have e := iteratedFDeriv_prodMk (𝕜 := ℝ) (f := f) (g := fun p : P => p)
    hf contDiffAt_id hin
  have e' : iteratedFDeriv ℝ i (fun p : P => (f p, p)) x
      = (iteratedFDeriv ℝ i f x).prod (iteratedFDeriv ℝ i (fun p : P => p) x) := e
  rw [e']
  exact (ContinuousMultilinearMap.norm_prod_le_max _ _).trans
    (max_le_max le_rfl (norm_iteratedFDeriv_id_le_one i hi x))

theorem norm_iteratedFDeriv_graph_comp_le {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
    (H : E × P → F') (f : P → E) (x : P) (m : ℕ) (C D : ℝ)
    (hH : ContDiffAt ℝ (m : WithTop ℕ∞) H (f x, x))
    (hf : ContDiffAt ℝ (m : WithTop ℕ∞) f x)
    (hC : ∀ i, i ≤ m → ‖iteratedFDeriv ℝ i H (f x, x)‖ ≤ C)
    (hD : ∀ i, 1 ≤ i → i ≤ m → ‖iteratedFDeriv ℝ i f x‖ ≤ D ^ i) (hD1 : 1 ≤ D) :
    ‖iteratedFDeriv ℝ m (fun p : P => H (f p, p)) x‖ ≤ (m.factorial : ℝ) * C * D ^ m := by
  have hgr : ContDiffAt ℝ (m : WithTop ℕ∞) (fun p : P => (f p, p)) x :=
    hf.prodMk contDiffAt_id
  obtain ⟨t, ht_mem, hHt⟩ := hH.contDiffOn le_rfl (by simp)
  obtain ⟨s₀, hs₀_mem, hgs⟩ := hgr.contDiffOn le_rfl (by simp)
  have hpre : (fun p : P => (f p, p)) ⁻¹' interior t ∈ nhds x :=
    hgr.continuousAt.preimage_mem_nhds
      (isOpen_interior.mem_nhds (mem_interior_iff_mem_nhds.2 ht_mem))
  set s : Set P := interior s₀ ∩ interior ((fun p : P => (f p, p)) ⁻¹' interior t) with hs_def
  have hs_open : IsOpen s := isOpen_interior.inter isOpen_interior
  have hxs : x ∈ s :=
    ⟨mem_interior_iff_mem_nhds.2 hs₀_mem, mem_interior_iff_mem_nhds.2 hpre⟩
  have hgs' : ContDiffOn ℝ (m : WithTop ℕ∞) (fun p : P => (f p, p)) s :=
    hgs.mono (Set.inter_subset_left.trans interior_subset)
  have hmaps : Set.MapsTo (fun p : P => (f p, p)) s (interior t) := fun p hp => by
    have h : p ∈ (fun p : P => (f p, p)) ⁻¹' interior t := interior_subset hp.2
    exact Set.mem_preimage.mp h
  have hgrx : ((f x, x) : E × P) ∈ interior t := hmaps hxs
  have hC' : ∀ i, i ≤ m →
      ‖iteratedFDerivWithin ℝ i H (interior t) ((f x, x) : E × P)‖ ≤ C := by
    intro i him
    rw [iteratedFDerivWithin_of_isOpen i isOpen_interior hgrx]
    exact hC i him
  have hD' : ∀ i, 1 ≤ i → i ≤ m →
      ‖iteratedFDerivWithin ℝ i (fun p : P => (f p, p)) s x‖ ≤ D ^ i := by
    intro i hi him
    rw [iteratedFDerivWithin_of_isOpen i hs_open hxs]
    refine (norm_iteratedFDeriv_graph_le f x hf hi (by exact_mod_cast him)).trans ?_
    exact max_le (hD i hi him) (one_le_pow₀ hD1)
  have hcomp : ‖iteratedFDerivWithin ℝ m (fun p : P => H (f p, p)) s x‖
      ≤ (m.factorial : ℝ) * C * D ^ m :=
    norm_iteratedFDerivWithin_comp_le (hHt.mono interior_subset) hgs' le_rfl
      isOpen_interior.uniqueDiffOn hs_open.uniqueDiffOn hmaps hxs hC' hD'
  rwa [iteratedFDerivWithin_of_isOpen m hs_open hxs] at hcomp

end ImplicitDerivativeBounds

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_iteratedFDeriv_clm_comp_le
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {E' F' G' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [NormedAddCommGroup F'] [NormedSpace ℝ F']
    [NormedAddCommGroup G'] [NormedSpace ℝ G']
    (X : P → (F' →L[ℝ] G')) (Y : P → (E' →L[ℝ] F')) (x : P) (m : ℕ)
    (hX : ContDiffAt ℝ (m : WithTop ℕ∞) X x)
    (hY : ContDiffAt ℝ (m : WithTop ℕ∞) Y x) :
    ‖iteratedFDeriv ℝ m (fun p : P => (X p).comp (Y p)) x‖ ≤
      ∑ i ∈ Finset.range (m + 1),
        (m.choose i : ℝ) * ‖iteratedFDeriv ℝ i X x‖ *
          ‖iteratedFDeriv ℝ (m - i) Y x‖ := by
  obtain ⟨u, hu_mem, hXu⟩ := hX.contDiffOn le_rfl (by simp)
  obtain ⟨v, hv_mem, hYv⟩ := hY.contDiffOn le_rfl (by simp)
  set s : Set P := interior u ∩ interior v with hs_def
  have hs_open : IsOpen s := isOpen_interior.inter isOpen_interior
  have hxs : x ∈ s :=
    ⟨mem_interior_iff_mem_nhds.2 hu_mem, mem_interior_iff_mem_nhds.2 hv_mem⟩
  have hXs : ContDiffOn ℝ (m : WithTop ℕ∞) X s :=
    hXu.mono (Set.inter_subset_left.trans interior_subset)
  have hYs : ContDiffOn ℝ (m : WithTop ℕ∞) Y s :=
    hYv.mono (Set.inter_subset_right.trans interior_subset)
  have h := (ContinuousLinearMap.compL ℝ E' F'
    G').norm_iteratedFDerivWithin_le_of_bilinear_of_le_one
    hXs hYs hs_open.uniqueDiffOn hxs le_rfl
    (ContinuousLinearMap.norm_compL_le ℝ E' F' G')
  calc ‖iteratedFDeriv ℝ m (fun p : P => (X p).comp (Y p)) x‖
      = ‖iteratedFDerivWithin ℝ m (fun p : P => (X p).comp (Y p)) s x‖ := by
        rw [iteratedFDerivWithin_of_isOpen m hs_open hxs]
    _ ≤ ∑ i ∈ Finset.range (m + 1),
        (m.choose i : ℝ) * ‖iteratedFDerivWithin ℝ i X s x‖ *
          ‖iteratedFDerivWithin ℝ (m - i) Y s x‖ := h
    _ = ∑ i ∈ Finset.range (m + 1),
        (m.choose i : ℝ) * ‖iteratedFDeriv ℝ i X x‖ *
          ‖iteratedFDeriv ℝ (m - i) Y x‖ := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [iteratedFDerivWithin_of_isOpen i hs_open hxs,
          iteratedFDerivWithin_of_isOpen (m - i) hs_open hxs]

theorem norm_iteratedFDeriv_implicit_succ_le
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace E]
    (f : P → E) (A : P → (E →L[ℝ] E)) (B : P → (P →L[ℝ] E)) (x : P) (m : ℕ)
    (Lambda DA CB : ℝ)
    (hform : fderiv ℝ f =ᶠ[nhds x]
      fun p => -((Ring.inverse (A p)).comp (B p)))
    (hA : ContDiffAt ℝ (m : WithTop ℕ∞) A x)
    (hB : ContDiffAt ℝ (m : WithTop ℕ∞) B x)
    (hunit : ∀ᶠ p in nhds x, IsUnit (A p))
    (hLambda : ‖Ring.inverse (A x)‖ ≤ Lambda)
    (hDA0 : 0 ≤ DA)
    (hDA : ∀ i, 1 ≤ i → i ≤ m → ‖iteratedFDeriv ℝ i A x‖ ≤ DA ^ i)
    (hCB : ∀ i, i ≤ m → ‖iteratedFDeriv ℝ i B x‖ ≤ CB) :
    ‖iteratedFDeriv ℝ (m + 1) f x‖ ≤
      (2 : ℝ) ^ m * ((m.factorial : ℝ) *
        ((m.factorial : ℝ) * max Lambda 1 ^ (m + 1)) * max DA 1 ^ m) * CB := by
  classical
  have hΛ0 : (0 : ℝ) ≤ max Lambda 1 := le_trans zero_le_one (le_max_right _ _)
  have hD0 : (0 : ℝ) ≤ max DA 1 := le_trans zero_le_one (le_max_right _ _)
  have hΛ1 : (1 : ℝ) ≤ max Lambda 1 := le_max_right _ _
  have hDA1 : (1 : ℝ) ≤ max DA 1 := le_max_right _ _
  obtain ⟨w, hw⟩ := hunit.self_of_nhds
  have hXc : ContDiffAt ℝ (m : WithTop ℕ∞) (fun p => Ring.inverse (A p)) x := by
    have hinv : ContDiffAt ℝ (m : WithTop ℕ∞) Ring.inverse
        ((w : E →L[ℝ] E) : E →L[ℝ] E) := contDiffAt_ringInverse ℝ w
    rw [hw] at hinv
    exact hinv.comp x hA
  have hfd : ‖iteratedFDeriv ℝ (m + 1) f x‖
      = ‖iteratedFDeriv ℝ m (fderiv ℝ f) x‖ :=
    (norm_iteratedFDeriv_fderiv (𝕜 := ℝ)).symm
  have hcongr : iteratedFDeriv ℝ m (fderiv ℝ f) x
      = iteratedFDeriv ℝ m
          (fun p => -((Ring.inverse (A p)).comp (B p))) x :=
    (Filter.EventuallyEq.iteratedFDeriv (𝕜 := ℝ) hform m).self_of_nhds
  have hneg : ‖iteratedFDeriv ℝ m
      (fun p => -((Ring.inverse (A p)).comp (B p))) x‖
      = ‖iteratedFDeriv ℝ m
          (fun p => (Ring.inverse (A p)).comp (B p)) x‖ := by
    rw [show (fun p => -((Ring.inverse (A p)).comp (B p)))
        = -(fun p => (Ring.inverse (A p)).comp (B p)) from rfl]
    rw [iteratedFDeriv_neg_apply, norm_neg]
  have hcollect := norm_iteratedFDeriv_clm_comp_le
    (fun p => Ring.inverse (A p)) B x m hXc hB
  set K : ℝ := (m.factorial : ℝ) *
    ((m.factorial : ℝ) * max Lambda 1 ^ (m + 1)) * max DA 1 ^ m with hK_def
  have hK0 : 0 ≤ K := by rw [hK_def]; positivity
  have hterm : ∀ i ∈ Finset.range (m + 1),
      (m.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun p => Ring.inverse (A p)) x‖ *
        ‖iteratedFDeriv ℝ (m - i) B x‖ ≤ (m.choose i : ℝ) * (K * CB) := by
    intro i hi
    have him : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hinv_i := norm_iteratedFDeriv_inverse_comp_le A x i Lambda DA
      (hA.of_le (by exact_mod_cast him)) hunit hLambda
      (fun j hj1 hjm => hDA j hj1 (hjm.trans him))
    have hfac : (i.factorial : ℝ) ≤ (m.factorial : ℝ) :=
      Nat.cast_le.mpr (Nat.factorial_le him)
    have hΛpow : max Lambda 1 ^ (i + 1) ≤ max Lambda 1 ^ (m + 1) :=
      pow_le_pow_right₀ hΛ1 (by omega)
    have hDApow : DA ^ i ≤ max DA 1 ^ m :=
      (pow_le_pow_left₀ hDA0 (le_max_left _ _) i).trans
        (pow_le_pow_right₀ hDA1 him)
    have hKi : (i.factorial : ℝ) *
        ((i.factorial : ℝ) * max Lambda 1 ^ (i + 1)) * DA ^ i ≤ K := by
      rw [hK_def]
      have h1 : (i.factorial : ℝ) * max Lambda 1 ^ (i + 1)
          ≤ (m.factorial : ℝ) * max Lambda 1 ^ (m + 1) :=
        mul_le_mul hfac hΛpow (by positivity) (by positivity)
      have h2 : (i.factorial : ℝ) *
          ((i.factorial : ℝ) * max Lambda 1 ^ (i + 1))
          ≤ (m.factorial : ℝ) * ((m.factorial : ℝ) * max Lambda 1 ^ (m + 1)) :=
        mul_le_mul hfac h1 (by positivity) (by positivity)
      exact mul_le_mul h2 hDApow (by positivity) (by positivity)
    have hB_i : ‖iteratedFDeriv ℝ (m - i) B x‖ ≤ CB := hCB (m - i) (by omega)
    have hchoose0 : (0 : ℝ) ≤ (m.choose i : ℝ) := Nat.cast_nonneg _
    calc (m.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun p => Ring.inverse (A p)) x‖ *
          ‖iteratedFDeriv ℝ (m - i) B x‖
        ≤ (m.choose i : ℝ) * K * CB := by
          refine mul_le_mul ?_ hB_i (norm_nonneg _) ?_
          · exact mul_le_mul_of_nonneg_left (hinv_i.trans hKi) hchoose0
          · positivity
      _ = (m.choose i : ℝ) * (K * CB) := by ring
  have hsum : ∑ i ∈ Finset.range (m + 1),
      (m.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun p => Ring.inverse (A p)) x‖ *
        ‖iteratedFDeriv ℝ (m - i) B x‖
      ≤ (2 : ℝ) ^ m * (K * CB) := by
    calc ∑ i ∈ Finset.range (m + 1),
          (m.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun p => Ring.inverse (A p)) x‖ *
            ‖iteratedFDeriv ℝ (m - i) B x‖
        ≤ ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * (K * CB) :=
          Finset.sum_le_sum hterm
      _ = (∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ)) * (K * CB) := by
          rw [Finset.sum_mul]
      _ = (2 : ℝ) ^ m * (K * CB) := by
          have h := Nat.sum_range_choose m
          have : (∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ))
              = ((2 ^ m : ℕ) : ℝ) := by
            rw [← h]
            push_cast
            rfl
          rw [this]
          push_cast
          rfl
  calc ‖iteratedFDeriv ℝ (m + 1) f x‖
      = ‖iteratedFDeriv ℝ m
          (fun p => (Ring.inverse (A p)).comp (B p)) x‖ := by
        rw [hfd, hcongr, hneg]
    _ ≤ ∑ i ∈ Finset.range (m + 1),
          (m.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun p => Ring.inverse (A p)) x‖ *
            ‖iteratedFDeriv ℝ (m - i) B x‖ := hcollect
    _ ≤ (2 : ℝ) ^ m * (K * CB) := hsum
    _ = (2 : ℝ) ^ m * K * CB := by ring

end Analysis
end DifferentialGeometry
