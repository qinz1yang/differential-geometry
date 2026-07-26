import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepCSmoothness
import DifferentialGeometry.Analysis.Calculus.RingInverseDeriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.FDeriv.Mul

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# MSM135 Chapter 4 Step C: C2 = `lbl430`(i), QUANTITATIVE derivative bounds of the center of mass

`centerOfMass_contDiffAt` (`lbl430`(ii)) proves the center of mass is `C^n` for every finite `n`.
That is *regularity*, not *bounds*: it gives no uniform-in-configuration constants.  This file is the
**quantitative half** — eq `lbl431`, `|∇_q^α ∇_μ^β cm| ≤ C̃_{|α|+|β|+1}` uniform over configurations
at the book scale (`r < c(n)/√C₀`, `inj(q) > 3r`) — which is needed to produce the arbitrary-order
metric bounds inside `StepB1RawInput`.

## Book route (chapter4.tex L2709+, proof of `lbl430`(i)) — mirrored, not a general IFT engine
The center of mass `cm` is the unique zero of `G(q) = Σ μᵢ exp_q⁻¹ qᵢ`.  The book:
1. `∇_q G` positive definite, smallest eigenvalue `≥ λ_min(C₀, Σμ)` (Lemma `lbl413`) ⟹
   `‖(∇_q G)⁻¹‖ ≤ Λ`.
2. `‖∇^{≤j} G‖ ≤ B_j` via Prop `lbl418`(i) (S6, `ExpInverseDerivBoundInput`); weights enter linearly.
3. Differentiate `G(cm(params), params) = 0` (eq `lbl432`): order 1 gives `D cm = −(∂_z G)⁻¹ ∂_p G`,
   `‖D cm‖ ≤ Λ B₁`; order `j` isolates `∂_z G · D^j cm = −(poly in D^{<j} cm and D^{≤j} G)` and bounds
   by induction with `Λ`, `B_{≤j}`.

This file proves the order-one and order-two bounds (`cmChartFDerivLe`, `cmChartDerivLe2`) and the
reusable higher-order Faà-di-Bruno bricks.  It deliberately does not state the arbitrary-order
endpoint until order-`p` regularity and a recursive numerical majorant are threaded honestly.
See `StepCDerivBounds.md`.
-/

noncomputable section

namespace DifferentialGeometry
namespace HCGCompactness

open scoped Topology

section AbstractOneBound

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Base case (order 1) of the `lbl430`(i) derivative-bound induction — abstract IFT form.**
For a family `G : E → P → E` (`P = (ι→ℝ)×(ι→E)`) with implicit solution `f` (`G(f params, params) =
0` near `params₀`, `f params₀ = z₀`), invertible `z`-block `∂_z G = L` at `(z₀, params₀)` with
`‖L⁻¹‖ ≤ Λ`, and joint derivative `Dⱼ` bounded `‖Dⱼ‖ ≤ B`, the implicit derivative satisfies
`‖Df‖ ≤ Λ · B`.  This is the book's `D cm = −(∂_z G)⁻¹ ∂_p G` estimate (eq `lbl432` at order 1),
proved by chain-ruling the constant relation `G(f, ·) = 0` and reading off the `z`-block. -/
theorem implicitDeriv_one_le
    {ι : Type} [Fintype ι]
    (G : E → ((ι → ℝ) × (ι → E)) → E) (z₀ : E) (params₀ : (ι → ℝ) × (ι → E))
    (f : ((ι → ℝ) × (ι → E)) → E) (Df : ((ι → ℝ) × (ι → E)) →L[ℝ] E)
    (Dj : (E × ((ι → ℝ) × (ι → E))) →L[ℝ] E) (L : E ≃L[ℝ] E) (Λ B : ℝ)
    (hf0 : f params₀ = z₀)
    (hf : HasFDerivAt f Df params₀)
    (hG : HasFDerivAt (fun w : E × ((ι → ℝ) × (ι → E)) => G w.1 w.2) Dj (z₀, params₀))
    (hLd : HasFDerivAt (fun z : E => G z params₀) (L : E →L[ℝ] E) z₀)
    (hLinv : ‖(L.symm : E →L[ℝ] E)‖ ≤ Λ)
    (hB : ‖Dj‖ ≤ B)
    (hrel : ∀ᶠ params in nhds params₀, G (f params) params = 0) :
    ‖Df‖ ≤ Λ * B := by
  -- The `z`-block of the joint derivative is `L` (chain rule + uniqueness), as in `implicitSol`.
  have hk : HasFDerivAt (fun z : E => (z, params₀))
      (ContinuousLinearMap.inl ℝ E ((ι → ℝ) × (ι → E))) z₀ :=
    (hasFDerivAt_id z₀).prodMk (hasFDerivAt_const params₀ z₀)
  have hLz : Dj.comp (ContinuousLinearMap.inl ℝ E ((ι → ℝ) × (ι → E))) = (L : E →L[ℝ] E) := by
    have h1 : HasFDerivAt ((fun w : E × ((ι → ℝ) × (ι → E)) => G w.1 w.2) ∘
          (fun z : E => (z, params₀)))
        (Dj.comp (ContinuousLinearMap.inl ℝ E ((ι → ℝ) × (ι → E)))) z₀ := hG.comp z₀ hk
    exact h1.unique hLd
  have hDv : ∀ a : E, Dj (a, (0 : (ι → ℝ) × (ι → E))) = L a := by
    intro a
    have h := DFunLike.congr_fun hLz a
    simpa [ContinuousLinearMap.inl_apply] using h
  have hsplit : ∀ (a : E) (b : (ι → ℝ) × (ι → E)), Dj (a, b) = L a + Dj ((0 : E), b) := by
    intro a b
    have hdecomp : ((a, b) : E × ((ι → ℝ) × (ι → E)))
        = (a, (0 : (ι → ℝ) × (ι → E))) + ((0 : E), b) :=
      Prod.ext (add_zero a).symm (zero_add b).symm
    rw [hdecomp, map_add, hDv]
  -- The relation `G(f, ·) = 0` has derivative `Dⱼ ∘ (Df, id) = 0`.  Ascribe the explicit
  -- composite `_ ∘ (fun params => (f params, params))` (as in `hLz` above) so `.comp` pins the
  -- inner map from the ascription rather than mis-guessing it from `hGf`'s point.
  have hpair : HasFDerivAt (fun params : (ι → ℝ) × (ι → E) => (f params, params))
      (Df.prod (ContinuousLinearMap.id ℝ ((ι → ℝ) × (ι → E)))) params₀ :=
    hf.prodMk (hasFDerivAt_id params₀)
  have hGf : HasFDerivAt (fun w : E × ((ι → ℝ) × (ι → E)) => G w.1 w.2) Dj (f params₀, params₀) := by
    rw [hf0]; exact hG
  have hcomp := HasFDerivAt.comp (𝕜 := ℝ) (E := (ι → ℝ) × (ι → E))
      (F := E × ((ι → ℝ) × (ι → E))) (G := E)
      (f := fun params : (ι → ℝ) × (ι → E) => (f params, params))
      (g := fun w : E × ((ι → ℝ) × (ι → E)) => G w.1 w.2)
      params₀ hGf hpair
  have hc0 : HasFDerivAt (fun _ : (ι → ℝ) × (ι → E) => (0 : E))
      (0 : ((ι → ℝ) × (ι → E)) →L[ℝ] E) params₀ := hasFDerivAt_const (0 : E) params₀
  have hconst : HasFDerivAt ((fun w : E × ((ι → ℝ) × (ι → E)) => G w.1 w.2) ∘
      (fun params : (ι → ℝ) × (ι → E) => (f params, params)))
      (0 : ((ι → ℝ) × (ι → E)) →L[ℝ] E) params₀ := by
    refine hc0.congr_of_eventuallyEq ?_
    filter_upwards [hrel] with params hp
    exact hp
  have hDeq : Dj.comp (Df.prod (ContinuousLinearMap.id ℝ ((ι → ℝ) × (ι → E)))) = 0 :=
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

/-- **Implicit-function derivative formula, at one point** (`lbl430`(i) ingredient (a), pointwise).
For `G(f q, q) = 0` near `p₀` with `f` differentiable (`hf`), `G` jointly differentiable (`hG`, joint
derivative `Dⱼ` at `(f p₀, p₀)`), and the `z`-block `∂_zG = Dⱼ∘inl` invertible in the Banach algebra
`E →L[ℝ] E` (`hinv`), the derivative of the implicit function is
`Df = −(∂_zG)⁻¹ ∘ ∂_pG`, where `∂_pG = Dⱼ∘inr`.  Chain-rule the constant relation `G(f,·) = 0`
(`Dⱼ∘(Df,id) = 0`), read off `∂_zG∘Df = −∂_pG`, and left-compose `Ring.inverse (∂_zG)` using
`Ring.inverse_mul_cancel`.  (`Ring.inverse` is the `E →L[ℝ] E` ring inverse; on the invertible set it
agrees with the genuine inverse.) -/
theorem implicitFDeriv_eq {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
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
      ContinuousLinearMap.inr_apply, ContinuousLinearMap.neg_apply]
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

/-- **Implicit-function derivative formula on a neighbourhood** (`lbl430`(i) ingredient (a)).  The
eventual (`=ᶠ[𝓝 params₀]`) form of `implicitFDeriv_eq`: `∇f =ᶠ fun p => −(∂_zG(f p,p))⁻¹ ∘ ∂_pG(f p,p)`,
from `f` eventually differentiable (`hf`, e.g. from `C^n` regularity), `G` eventually jointly
differentiable (`hG`), the IFT relation `G(f,·) = 0` (`hrel`), and eventual `z`-block invertibility
(`hinv`, the neighbourhood Hessian input).  This is the object the `j ≥ 2` induction differentiates. -/
theorem implicitFDeriv_eventuallyEq {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
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
  exact implicitFDeriv_eq G f p (Df p) (Dj p) hfp hGp hrelp hinvp

/-- **Graph-pulled derivative of a CLM-block family** (`lbl430`(i) step (1) engine).  A CLM-valued
map `H` (concretely: `fderiv` of the joint equation `G`) differentiated through the graph
`p ↦ (f p, p)` and post-restricted to a fixed slot `j` (concretely `inl`/`inr`) gives the block
family `p ↦ (H (f p, p)).comp j`, differentiable with the quantitative bound
`‖D'‖ ≤ ‖H'‖ · max ‖Df₀‖ 1` when `‖j‖ ≤ 1` — the book's `‖∇(∂G ∘ graph)‖ ≤ ‖∇²G‖·(‖∇f‖ + 1)`. -/
theorem graphBlockDeriv {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
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
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.zero_apply, map_zero, zero_add, ContinuousLinearMap.flip_apply,
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

/-- **Order-2 bound for the implicit function** (`lbl430`(i) step (3) at `j = 2`).  Differentiating
the neighbourhood formula `∇f =ᶠ −(∂_zG)⁻¹∘∂_pG` (`implicitFDeriv_eventuallyEq`) once more:
`‖∇²f‖ ≤ Λ²·a₂·b₁ + Λ·b₂`, where `Λ` bounds the inverse `z`-block at the base point, `b₁` bounds
`‖∂_pG‖`, and `a₂`, `b₂` bound the derivatives of the block families `p ↦ ∂_zG(f p, p)`,
`p ↦ ∂_pG(f p, p)` (supplied by `graphBlockDeriv` from `‖∇²G‖` in the concrete case).  The inverse
factor differentiates by Mathlib's `hasFDerivAt_ringInverse` (`∇(inverse) = −u⁻¹·(·)·u⁻¹`), giving
the `Λ²` — the `i = 1` case of the Neumann bound `norm_iteratedFDeriv_ringInverse_le`. -/
theorem implicitDeriv_two_le {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
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
  have heq := implicitFDeriv_eventuallyEq G f params₀ Df Dj hf hG hrel hinv
  obtain ⟨u, hu⟩ := hinv.self_of_nhds
  have hu_inv : ‖((↑u⁻¹ : E →L[ℝ] E))‖ ≤ Λ := by
    have h : Ring.inverse ((Dj params₀).comp (ContinuousLinearMap.inl ℝ E P))
        = (↑u⁻¹ : E →L[ℝ] E) := by rw [← hu, Ring.inverse_unit]
    rw [← h]; exact hΛ
  -- derivative of the inverse factor at the base `z`-block
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
        simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.add_apply,
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

/-! Bricks for the `j ≥ 3` recursion (step (c)): the pair-function iterated bound.  These feed the
`norm_iteratedFDeriv(Within)_comp_le` chain for `‖∇^i(∂G ∘ graph)‖` in the general induction. -/

/-- `‖M.prod N‖ ≤ max ‖M‖ ‖N‖` for continuous multilinear maps into a sup-norm product. -/
theorem multilinear_prod_opNorm_le {n : ℕ}
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

/-- The identity has all iterated derivatives of order `≥ 1` bounded by `1`. -/
theorem norm_iteratedFDeriv_id_le {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (i : ℕ) (hi : 1 ≤ i) (x : P) :
    ‖iteratedFDeriv ℝ i (fun p : P => p) x‖ ≤ 1 := by
  obtain _ | k := i
  · omega
  · rw [← norm_iteratedFDeriv_fderiv]
    have hfd : (fderiv ℝ (fun p : P => p)) = fun _ : P => ContinuousLinearMap.id ℝ P := by
      funext y; exact fderiv_id'
    rw [hfd]
    obtain _ | l := k
    · rw [norm_iteratedFDeriv_zero]; exact ContinuousLinearMap.norm_id_le
    · rw [iteratedFDeriv_const_of_ne (Nat.succ_ne_zero l)]
      simp

/-- **Graph iterated bound** (step (c) brick): the graph `p ↦ (f p, p)` inherits the iterated
bounds of `f` — `‖∇^i (f, id)‖ ≤ max ‖∇^i f‖ 1` for `1 ≤ i ≤ n` given `C^n`-at-the-point.  This is
the inner-function `D^i`-shape input of `norm_iteratedFDeriv_comp_le` for `∂G ∘ graph`. -/
theorem norm_iteratedFDeriv_graph_le {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {n : WithTop ℕ∞} (f : P → E) (x : P) (hf : ContDiffAt ℝ n f x)
    {i : ℕ} (hi : 1 ≤ i) (hin : (i : WithTop ℕ∞) ≤ n) :
    ‖iteratedFDeriv ℝ i (fun p : P => (f p, p)) x‖ ≤ max ‖iteratedFDeriv ℝ i f x‖ 1 := by
  have e := iteratedFDeriv_prodMk (𝕜 := ℝ) (f := f) (g := fun p : P => p)
    hf contDiffAt_id hin
  have e' : iteratedFDeriv ℝ i (fun p : P => (f p, p)) x
      = (iteratedFDeriv ℝ i f x).prod (iteratedFDeriv ℝ i (fun p : P => p) x) := e
  rw [e']
  exact (multilinear_prod_opNorm_le _ _).trans
    (max_le_max le_rfl (norm_iteratedFDeriv_id_le i hi x))

/-- **Iterated bound for a graph pullback `H ∘ (f, id)`** (step (c) brick, Faà-di-Bruno).  If `H`
is `C^m` at `(f x, x)` with `‖∇^i H (f x, x)‖ ≤ C` (`i ≤ m`), `f` is `C^m` at `x` with the
`D^i`-shape bounds (`1 ≤ i ≤ m`, `1 ≤ D`), then `‖∇^m (H(f·,·)) x‖ ≤ m!·C·D^m`.  The inner
`D^i`-shape for the graph comes from `norm_iteratedFDeriv_graph_le`.  Applied with
`H := fderiv (uncurried G)` this bounds the iterated derivatives of the block families `∂_zG`,
`∂_pG` from `‖∇^{i+1}G‖` and the induction hypotheses on `f`. -/
theorem norm_iteratedFDeriv_graphComp_le {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
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
  -- outer bounds within the open `interior t` = ambient bounds
  have hC' : ∀ i, i ≤ m →
      ‖iteratedFDerivWithin ℝ i H (interior t) ((f x, x) : E × P)‖ ≤ C := by
    intro i him
    rw [iteratedFDerivWithin_of_isOpen i isOpen_interior hgrx]
    exact hC i him
  -- inner `D^i`-shape for the graph, via the pair bound
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

end AbstractOneBound

section CmBounds

set_option synthInstance.maxHeartbeats 1000000

open Set Bundle Manifold
open scoped Topology Manifold ContDiff ENNReal
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [Module.Finite ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
  [ConnectedSpace M] [T3Space M]
variable [RiemannianBundle (fun x : M => TangentSpace I x)]
variable [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Honest input (1) — quantitative Hessian nondegeneracy (`lbl413`, the `‖L⁻¹‖` field).**
The qualitative `CmHessianInput` (invertible `∂_z G`) upgraded with the operator-norm bound
`‖L⁻¹‖ ≤ Λ` on the inverse `z`-block of the readout equation `chartCmEqn'`.

*Why true, at which scale, who discharges it* (audit rule): below the convexity radius the summands
`∂_z(exp_y⁻¹ qᵢ)` are close to `−id`, so `∂_z G = Σ μᵢ ∂_z(exp_y⁻¹ qᵢ) ≈ −(Σμᵢ)·id`; the Neumann
series gives invertibility with `‖L⁻¹‖ ≤ (Σμᵢ(1−ε))⁻¹`, uniformly in the `lbl413` regime
(`r < c(n)/√C₀`, `inj > 3r`).  This is a per-configuration honest input, discharged at D6 adjacent to
`Item3GpScaleInput` (the same `lbl413` curvature-comparison family); it is not proved natively. -/
structure CmHessianBoundInput
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) {ι : Type} [Fintype ι] (z₀ : E) (params₀ : (ι → ℝ) × (ι → E)) where
  /-- The book's `Λ` — an upper bound for `‖(∂_z G)⁻¹‖`. -/
  Λ : ℝ
  /-- The invertible `z`-block `∂_z G` of the readout equation at `(z₀, params₀)`. -/
  L : E ≃L[ℝ] E
  hL : HasFDerivAt (fun z : E => chartCmEqn' (I := I) g hEnorm p z params₀) (L : E →L[ℝ] E) z₀
  /-- The quantitative content: `‖L⁻¹‖ ≤ Λ` (the `lbl413` smallest-eigenvalue bound). -/
  hLinv : ‖(L.symm : E →L[ℝ] E)‖ ≤ Λ

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- The qualitative `hinv'` datum (readout-form `CmHessianInput`) underlying a
`CmHessianBoundInput` — the C^n endpoints (`readoutSol_contDiffAt`, …) consume exactly this. -/
theorem CmHessianBoundInput.toInv
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    {g : SmoothRiemannianMetric I M}
    {hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w))}
    {p : M} {ι : Type} [Fintype ι] {z₀ : E} {params₀ : (ι → ℝ) × (ι → E)}
    (hbd : CmHessianBoundInput (I := I) g hEnorm p z₀ params₀) :
    ∃ L : E ≃L[ℝ] E,
      HasFDerivAt (fun z : E => chartCmEqn' (I := I) g hEnorm p z params₀) (L : E →L[ℝ] E) z₀ :=
  ⟨hbd.L, hbd.hL⟩

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Honest input (2) — `G`-derivative bounds (`lbl418`/S6 threaded through the readout chain).**
`‖∇^j (chartCmEqn')‖ ≤ B j` for `j ≤ pOrd`, at the configuration `(z₀, params₀)`.

*Reduction to S6* (audit rule): `chartCmEqn' = Σ μᵢ • readoutᵢ`, with `readoutᵢ` the
trivialization-at-`p` readout of `diagExpInv`, i.e. (up to the trivialization CLE, a fixed linear
iso) the double-exponential `exp_{exp_p z}⁻¹(exp_p ξᵢ)`.  Weights enter linearly, so
`‖∇^j chartCmEqn'‖ ≤ (Σ|μᵢ|)·‖∇^j readout‖`.  `j = 0` reduces to `ExpInverseDerivBoundInput` (S6,
`lbl418`) at order 0 — boundedness on the `r₁`-capped ball.  `j ≥ 1` needs the readout-chain
comp-bound transfer (Faà-di-Bruno via `norm_iteratedFDeriv_comp_le`: the double-exp composition with
S6's `NormalTransitionDerivBound` and `lbl395` parametrization bounds, times the constant CLE
factor) — a minimal `MapConvergenceComp` bounds-sibling, deferred.  Carried here as an honest input
whose fields are the S6/`lbl395` quantities. -/
def CmGDerivBound
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) {ι : Type} [Fintype ι] (z₀ : E) (params₀ : (ι → ℝ) × (ι → E))
    (pOrd : ℕ) (B : ℕ → ℝ) : Prop :=
  ∀ j : ℕ, j ≤ pOrd →
    ‖iteratedFDeriv ℝ j
        (fun w : E × ((ι → ℝ) × (ι → E)) => chartCmEqn' (I := I) g hEnorm p w.1 w.2)
        (z₀, params₀)‖ ≤ B j

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Honest input (1') — neighbourhood Hessian nondegeneracy along the center family (`lbl413`).**
The neighbourhood strengthening of `CmHessianBoundInput`, bound to a center family `c`: at every
parameter `q` near `params₀`, the `z`-block `∂_zG = Dⱼ(q)∘inl` of the joint derivative of the
readout equation along the graph `q ↦ (chart(c q), q)` is invertible (in the Banach algebra
`E →L[ℝ] E`), with the inverse-norm bound `‖(∂_zG)⁻¹‖ ≤ Λ` at the base point.

*Why true, at which scale, who discharges it* (audit rule): identical in content to the pointwise
`CmHessianBoundInput` — below the convexity radius each summand `∂_z(exp_y⁻¹ qᵢ)` is close to
`−id`, so `∂_zG ≈ −(Σμᵢ)·id` and the Neumann series gives invertibility with
`‖(∂_zG)⁻¹‖ ≤ (Σμᵢ(1−ε))⁻¹`; nearby configurations `(chart(c q), q)` stay below the same radius, so
the *same* Neumann argument applies verbatim on a neighbourhood.  Scale: the `lbl413` regime
(`r < c(n)/√C₀`, `inj > 3r`).  Discharger: per-configuration honest input, D6-adjacent (the same
`lbl413` curvature-comparison family as `Item3GpScaleInput`); not proved natively. -/
structure CmHessianNbhdInput
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) {ι : Type} [Fintype ι]
    (c : ((ι → ℝ) × (ι → E)) → M) (params₀ : (ι → ℝ) × (ι → E)) where
  /-- The book's `Λ` — an upper bound for the inverse `z`-block norm at the base configuration. -/
  Λ : ℝ
  /-- Eventual invertibility of the `z`-block along the graph of the center family. -/
  ev_isUnit : ∀ᶠ q in nhds params₀,
    IsUnit ((fderiv ℝ (fun w : E × ((ι → ℝ) × (ι → E)) => chartCmEqn' (I := I) g hEnorm p w.1 w.2)
      ((NormalCoordinates.normalChartAt (I := I) g p (c q) : E), q)).comp
      (ContinuousLinearMap.inl ℝ E ((ι → ℝ) × (ι → E))))
  /-- The quantitative content at the base point: `‖(∂_zG)⁻¹‖ ≤ Λ`. -/
  inv_le : ‖Ring.inverse
      ((fderiv ℝ (fun w : E × ((ι → ℝ) × (ι → E)) => chartCmEqn' (I := I) g hEnorm p w.1 w.2)
        ((NormalCoordinates.normalChartAt (I := I) g p (c params₀) : E), params₀)).comp
      (ContinuousLinearMap.inl ℝ E ((ι → ℝ) × (ι → E))))‖ ≤ Λ

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Base case (order 1) of eq `lbl431` for the chart center of mass.**  Specializes
`implicitDeriv_one_le` to `G = chartCmEqn'`, `f = normalChartAt g p ∘ c`: for any center family `c`
solving the readout equation (`hc_solves`) with derivative `Df` (`hcderiv` — from
`center_hasStrictFDerivAt`), the first covariant derivative is bounded `‖∇(chart∘c)‖ ≤ Λ · B₁`, from
the quantitative Hessian input `hbd` and the joint-`G` order-1 bound `hB`. -/
theorem cmChartFDerivLe
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) {ι : Type} [Fintype ι] (z₀ : E) (params₀ : (ι → ℝ) × (ι → E))
    (hbd : CmHessianBoundInput (I := I) g hEnorm p z₀ params₀)
    (Dj : (E × ((ι → ℝ) × (ι → E))) →L[ℝ] E) (B1 : ℝ)
    (hG : HasFDerivAt (fun w : E × ((ι → ℝ) × (ι → E)) => chartCmEqn' (I := I) g hEnorm p w.1 w.2)
      Dj (z₀, params₀))
    (hB : ‖Dj‖ ≤ B1)
    (c : ((ι → ℝ) × (ι → E)) → M) (Df : ((ι → ℝ) × (ι → E)) →L[ℝ] E)
    (hcderiv : HasFDerivAt
      (fun params => (NormalCoordinates.normalChartAt (I := I) g p (c params) : E)) Df params₀)
    (hc0 : (NormalCoordinates.normalChartAt (I := I) g p (c params₀) : E) = z₀)
    (hc_solves : ∀ᶠ params in nhds params₀,
      chartCmEqn' (I := I) g hEnorm p
        (NormalCoordinates.normalChartAt (I := I) g p (c params)) params = 0) :
    ‖iteratedFDeriv ℝ 1
        (fun params => (NormalCoordinates.normalChartAt (I := I) g p (c params) : E)) params₀‖
      ≤ hbd.Λ * B1 := by
  rw [norm_iteratedFDeriv_one, hcderiv.fderiv]
  exact implicitDeriv_one_le (fun z params => chartCmEqn' (I := I) g hEnorm p z params) z₀ params₀
    (fun params => (NormalCoordinates.normalChartAt (I := I) g p (c params) : E)) Df Dj hbd.L hbd.Λ B1
    hc0 hcderiv hG hbd.hL hbd.hLinv hB hc_solves

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Order-two part of eq `lbl431`, quantitative derivative bounds of the center of mass.**
`‖D^j (normalChartAt g p ∘ cm)‖ ≤ C̃ j` for `j ≤ 2`, uniformly over configurations satisfying the
audited inputs `hbd` (`CmHessianBoundInput`, `Λ`) and `hGbd` (`CmGDerivBound`, `B`).

`j = 0` (`‖cm‖ ≤ C̃ 0`) and `j = 1` (`cmChartFDerivLe`, `‖D cm‖ ≤ Λ·B₁ ≤ C̃ 1`) are the base
cases.  The `j = 2` case uses the neighbourhood implicit-derivative formula
(`implicitFDeriv_eventuallyEq`, fed by the `C²` regularity `hf2`/`hG2` and the neighbourhood
Hessian input `hnbhd`) differentiates once more via `implicitDeriv_two_le`, with the block
derivatives supplied by `graphBlockDeriv` from `‖∇²G‖ ≤ B 2` and `‖∇f‖ ≤ Λ·B₁`; the constant is
`C̃₂ = Λ'²·a₂·B₁ + Λ'·a₂` with `a₂ = B₂·(Λ·B₁+1)` (`hC2`).  The arbitrary-order theorem is not
stated here: it additionally needs order-`p` regularity and an explicit recursive construction of
`C̃`; neither follows from the order-two hypotheses below. -/
theorem cmChartDerivLe2
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) {ι : Type} [Fintype ι] (z₀ : E) (params₀ : (ι → ℝ) × (ι → E))
    (hbd : CmHessianBoundInput (I := I) g hEnorm p z₀ params₀)
    (B : ℕ → ℝ)
    (Dj : (E × ((ι → ℝ) × (ι → E))) →L[ℝ] E)
    (hG : HasFDerivAt (fun w : E × ((ι → ℝ) × (ι → E)) => chartCmEqn' (I := I) g hEnorm p w.1 w.2)
      Dj (z₀, params₀))
    (hGbd : CmGDerivBound (I := I) g hEnorm p z₀ params₀ 2 B)
    (c : ((ι → ℝ) × (ι → E)) → M) (Df : ((ι → ℝ) × (ι → E)) →L[ℝ] E)
    (hcderiv : HasFDerivAt
      (fun params => (NormalCoordinates.normalChartAt (I := I) g p (c params) : E)) Df params₀)
    (hc0 : (NormalCoordinates.normalChartAt (I := I) g p (c params₀) : E) = z₀)
    (hc_solves : ∀ᶠ params in nhds params₀,
      chartCmEqn' (I := I) g hEnorm p
        (NormalCoordinates.normalChartAt (I := I) g p (c params)) params = 0)
    (hf2 : ContDiffAt ℝ 2
      (fun params => (NormalCoordinates.normalChartAt (I := I) g p (c params) : E)) params₀)
    (hG2 : ContDiffAt ℝ 2
      (fun w : E × ((ι → ℝ) × (ι → E)) => chartCmEqn' (I := I) g hEnorm p w.1 w.2) (z₀, params₀))
    (hnbhd : CmHessianNbhdInput (I := I) g hEnorm p c params₀)
    (Ctil : ℕ → ℝ)
    (hC0 : ‖z₀‖ ≤ Ctil 0)
    (hC1 : hbd.Λ * B 1 ≤ Ctil 1)
    (hC2 :
      hnbhd.Λ ^ 2 * (B 2 * (hbd.Λ * B 1 + 1)) * B 1
        + hnbhd.Λ * (B 2 * (hbd.Λ * B 1 + 1)) ≤ Ctil 2) :
    ∀ j : ℕ, j ≤ 2 →
      ‖iteratedFDeriv ℝ j
          (fun params => (NormalCoordinates.normalChartAt (I := I) g p (c params) : E)) params₀‖
        ≤ Ctil j := by
  intro j hj
  obtain _ | _ | _ | n := j
  · -- j = 0: `‖cm‖ = ‖z₀‖ ≤ C̃ 0`.
    rw [norm_iteratedFDeriv_zero, hc0]; exact hC0
  · -- j = 1: base case via `cmChartFDerivLe`.
    have hB : ‖Dj‖ ≤ B 1 := by
      have h := hGbd 1 hj
      rwa [norm_iteratedFDeriv_one, hG.fderiv] at h
    exact le_trans
      (cmChartFDerivLe (I := I) g hEnorm p z₀ params₀ hbd Dj (B 1) hG hB c Df hcderiv hc0 hc_solves)
      hC1
  · -- j = 2: Route A — the neighbourhood formula differentiated once (`implicitDeriv_two_le`).
    -- Eventual differentiability of `f = chart ∘ c` from the `C²` regularity.
    have hf_ev : ∀ᶠ q in nhds params₀,
        HasFDerivAt (fun q' => (NormalCoordinates.normalChartAt (I := I) g p (c q') : E))
          (fderiv ℝ (fun q' => (NormalCoordinates.normalChartAt (I := I) g p (c q') : E)) q) q := by
      filter_upwards [hf2.eventually (by simp)] with q hq
      exact (hq.differentiableAt (by norm_num)).hasFDerivAt
    -- The graph tends to the base configuration.
    have htend : Filter.Tendsto
        (fun q => ((NormalCoordinates.normalChartAt (I := I) g p (c q) : E), q))
        (nhds params₀) (nhds (z₀, params₀)) := by
      have hf_cont : Filter.Tendsto
          (fun q => (NormalCoordinates.normalChartAt (I := I) g p (c q) : E))
          (nhds params₀) (nhds z₀) := by
        rw [← hc0]; exact hf2.continuousAt
      exact hf_cont.prodMk_nhds Filter.tendsto_id
    -- Eventual joint differentiability of `G` along the graph.
    have hG_ev : ∀ᶠ q in nhds params₀,
        HasFDerivAt (fun w : E × ((ι → ℝ) × (ι → E)) => chartCmEqn' (I := I) g hEnorm p w.1 w.2)
          (fderiv ℝ (fun w : E × ((ι → ℝ) × (ι → E)) => chartCmEqn' (I := I) g hEnorm p w.1 w.2)
            ((NormalCoordinates.normalChartAt (I := I) g p (c q) : E), q))
          ((NormalCoordinates.normalChartAt (I := I) g p (c q) : E), q) := by
      filter_upwards [htend.eventually (hG2.eventually (by simp))] with q hq
      exact (hq.differentiableAt (by norm_num)).hasFDerivAt
    -- `‖∇f‖ ≤ Λ·B₁` (the `j = 1` content) and the second-derivative datum `H'` with `‖H'‖ ≤ B₂`.
    have hB1 : ‖Dj‖ ≤ B 1 := by
      have h := hGbd 1 (by omega)
      rwa [norm_iteratedFDeriv_one, hG.fderiv] at h
    have hDf_le : ‖Df‖ ≤ hbd.Λ * B 1 :=
      implicitDeriv_one_le (fun z params => chartCmEqn' (I := I) g hEnorm p z params) z₀ params₀
        (fun params => (NormalCoordinates.normalChartAt (I := I) g p (c params) : E)) Df Dj
        hbd.L hbd.Λ (B 1) hc0 hcderiv hG hbd.hL hbd.hLinv hB1 hc_solves
    have hmax_le : max ‖Df‖ 1 ≤ hbd.Λ * B 1 + 1 :=
      max_le (hDf_le.trans (le_add_of_nonneg_right zero_le_one))
        (le_add_of_nonneg_left (le_trans (norm_nonneg Df) hDf_le))
    have hG1 : ContDiffAt ℝ 1
        (fderiv ℝ (fun w : E × ((ι → ℝ) × (ι → E)) => chartCmEqn' (I := I) g hEnorm p w.1 w.2))
        (z₀, params₀) := hG2.fderiv_right (by norm_num)
    have hH0 : HasFDerivAt
        (fderiv ℝ (fun w : E × ((ι → ℝ) × (ι → E)) => chartCmEqn' (I := I) g hEnorm p w.1 w.2))
        (fderiv ℝ (fderiv ℝ
          (fun w : E × ((ι → ℝ) × (ι → E)) => chartCmEqn' (I := I) g hEnorm p w.1 w.2))
          (z₀, params₀))
        (z₀, params₀) := (hG1.differentiableAt (by norm_num)).hasFDerivAt
    have hH : HasFDerivAt
        (fderiv ℝ (fun w : E × ((ι → ℝ) × (ι → E)) => chartCmEqn' (I := I) g hEnorm p w.1 w.2))
        (fderiv ℝ (fderiv ℝ
          (fun w : E × ((ι → ℝ) × (ι → E)) => chartCmEqn' (I := I) g hEnorm p w.1 w.2))
          (z₀, params₀))
        ((NormalCoordinates.normalChartAt (I := I) g p (c params₀) : E), params₀) := by
      rw [hc0]; exact hH0
    have hH'le : ‖fderiv ℝ (fderiv ℝ
        (fun w : E × ((ι → ℝ) × (ι → E)) => chartCmEqn' (I := I) g hEnorm p w.1 w.2))
        (z₀, params₀)‖ ≤ B 2 := by
      have h := hGbd 2 hj
      have heq2 : ‖fderiv ℝ (fderiv ℝ
          (fun w : E × ((ι → ℝ) × (ι → E)) => chartCmEqn' (I := I) g hEnorm p w.1 w.2))
          (z₀, params₀)‖
          = ‖iteratedFDeriv ℝ 2
              (fun w : E × ((ι → ℝ) × (ι → E)) => chartCmEqn' (I := I) g hEnorm p w.1 w.2)
              (z₀, params₀)‖ := by
        rw [← norm_iteratedFDeriv_one]
        exact norm_iteratedFDeriv_fderiv
      rw [heq2]; exact h
    -- Block derivatives via `graphBlockDeriv` at `j = inl` and `j = inr`.
    obtain ⟨A', hAd, hA'le⟩ := graphBlockDeriv
      (fderiv ℝ (fun w : E × ((ι → ℝ) × (ι → E)) => chartCmEqn' (I := I) g hEnorm p w.1 w.2))
      (fun params => (NormalCoordinates.normalChartAt (I := I) g p (c params) : E)) params₀ Df _
      hcderiv hH (ContinuousLinearMap.inl ℝ E ((ι → ℝ) × (ι → E)))
      (ContinuousLinearMap.norm_inl_le_one ℝ E ((ι → ℝ) × (ι → E)))
    obtain ⟨B', hBd, hB'le⟩ := graphBlockDeriv
      (fderiv ℝ (fun w : E × ((ι → ℝ) × (ι → E)) => chartCmEqn' (I := I) g hEnorm p w.1 w.2))
      (fun params => (NormalCoordinates.normalChartAt (I := I) g p (c params) : E)) params₀ Df _
      hcderiv hH (ContinuousLinearMap.inr ℝ E ((ι → ℝ) × (ι → E)))
      (ContinuousLinearMap.norm_inr_le_one ℝ E ((ι → ℝ) × (ι → E)))
    have hB2nonneg : (0 : ℝ) ≤ B 2 :=
      le_trans (ContinuousLinearMap.opNorm_nonneg _) hH'le
    have ha₂ : ‖A'‖ ≤ B 2 * (hbd.Λ * B 1 + 1) :=
      hA'le.trans (mul_le_mul hH'le hmax_le
        (le_trans zero_le_one (le_max_right _ _)) hB2nonneg)
    have hb₂ : ‖B'‖ ≤ B 2 * (hbd.Λ * B 1 + 1) :=
      hB'le.trans (mul_le_mul hH'le hmax_le
        (le_trans zero_le_one (le_max_right _ _)) hB2nonneg)
    -- `∂_pG` bound at the base configuration.
    have hfam0 : fderiv ℝ
        (fun w : E × ((ι → ℝ) × (ι → E)) => chartCmEqn' (I := I) g hEnorm p w.1 w.2)
        ((NormalCoordinates.normalChartAt (I := I) g p (c params₀) : E), params₀) = Dj := by
      rw [hc0]; exact hG.fderiv
    have hb₁ : ‖(fderiv ℝ
        (fun w : E × ((ι → ℝ) × (ι → E)) => chartCmEqn' (I := I) g hEnorm p w.1 w.2)
        ((NormalCoordinates.normalChartAt (I := I) g p (c params₀) : E), params₀)).comp
        (ContinuousLinearMap.inr ℝ E ((ι → ℝ) × (ι → E)))‖ ≤ B 1 := by
      rw [hfam0]
      refine le_trans (ContinuousLinearMap.opNorm_comp_le _ _) ?_
      calc ‖Dj‖ * ‖ContinuousLinearMap.inr ℝ E ((ι → ℝ) × (ι → E))‖
          ≤ B 1 * 1 := mul_le_mul hB1
            (ContinuousLinearMap.norm_inr_le_one ℝ E ((ι → ℝ) × (ι → E))) (norm_nonneg _)
            (le_trans (norm_nonneg _) hB1)
        _ = B 1 := mul_one _
    -- Assemble via the abstract order-2 bound.
    have hmain := implicitDeriv_two_le
      (fun z params => chartCmEqn' (I := I) g hEnorm p z params)
      (fun params => (NormalCoordinates.normalChartAt (I := I) g p (c params) : E)) params₀
      (fun q => fderiv ℝ
        (fun q' => (NormalCoordinates.normalChartAt (I := I) g p (c q') : E)) q)
      (fun q => fderiv ℝ
        (fun w : E × ((ι → ℝ) × (ι → E)) => chartCmEqn' (I := I) g hEnorm p w.1 w.2)
        ((NormalCoordinates.normalChartAt (I := I) g p (c q) : E), q))
      A' B' hnbhd.Λ (B 2 * (hbd.Λ * B 1 + 1)) (B 1) (B 2 * (hbd.Λ * B 1 + 1))
      hf_ev hG_ev hc_solves hnbhd.ev_isUnit hAd hBd hnbhd.inv_le hb₁ ha₂ hb₂
    exact hmain.trans hC2
  · omega

end CmBounds

end HCGCompactness
end DifferentialGeometry
