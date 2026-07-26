import DifferentialGeometry.Analysis.Parabolic.Euclidean.HeatKernelSup
import DifferentialGeometry.Analysis.Parabolic.Euclidean.RoughCarleson
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Divergence refold and sup-norm bounds for a quasilinear flux

The rough Ricci--DeTurck equation contains the genuinely quasilinear arm

`A(u) · D²w`.

It cannot be discarded when proving `C⁰` stability.  This file records the
exact Euclidean divergence refold

`A(u) D_p D_q w = D_p (A(u) D_q w) - DA(u)[D_p u] D_q w`

and the corresponding coefficient-flux difference estimate in the spatial
supremum norm.  The first term is acted on by a first derivative of the heat
kernel; the second, compensating quadratic-gradient term is retained and gets
its own three-arm difference estimate below.

These lemmas are dimension- and fibre-generic.  They require no bound on a
spatial derivative of the initial slice.
-/

noncomputable section

open Real
open scoped NNReal RealInnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace Euclidean

section Refold

variable {V U F : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Exact directional divergence refold for a quasilinear second-order arm.

The scalar coefficient is written as `c ∘ u`; for Ricci--DeTurck, `u` is the
array of metric coefficients and `c` is one inverse-metric coefficient.  The
last term is the compensating `Dc(u)[Du] · Dw` arm and is not suppressed. -/
theorem coeffD2_refold
    (c : U → ℝ) (u : V → U) (w : V → F) (x p q : V)
    (hc : DifferentiableAt ℝ c (u x))
    (hu : DifferentiableAt ℝ u x)
    (hDq : DifferentiableAt ℝ (fun z => fderiv ℝ w z q) x) :
    c (u x) • fderiv ℝ (fun z => fderiv ℝ w z q) x p =
      fderiv ℝ (fun z => c (u z) • fderiv ℝ w z q) x p -
        (fderiv ℝ c (u x) (fderiv ℝ u x p)) • fderiv ℝ w x q := by
  have hcu : DifferentiableAt ℝ (fun z => c (u z)) x := hc.comp x hu
  have hprod := fderiv_fun_smul hcu hDq
  have hcomp := fderiv_comp' (x := x) hc hu
  have happ := congrArg (fun L : V →L[ℝ] F => L p) hprod
  rw [hcomp] at happ
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply] at happ
  rw [happ]
  abel

end Refold

section CoefficientFlux

variable {V U G F : Type*}
  [NormedAddCommGroup V]
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Pointwise two-arm difference estimate for a nonlinear coefficient acting
on a first derivative.  This is the algebraic estimate used for the divergence
flux `A(u) Du`. -/
theorem fluxDiff_norm (A : U → G →L[ℝ] F)
    (u₁ u₂ : U) (d₁ d₂ : G) {L K : ℝ}
    (hA : ‖A u₁ - A u₂‖ ≤ L * ‖u₁ - u₂‖)
    (hK : ‖A u₂‖ ≤ K) :
    ‖A u₁ d₁ - A u₂ d₂‖ ≤
      (L * ‖u₁ - u₂‖) * ‖d₁‖ + K * ‖d₁ - d₂‖ := by
  have hsplit :
      A u₁ d₁ - A u₂ d₂ =
        (A u₁ - A u₂) d₁ + A u₂ (d₁ - d₂) := by
    simp only [ContinuousLinearMap.sub_apply, map_sub]
    abel
  rw [hsplit]
  calc
    ‖(A u₁ - A u₂) d₁ + A u₂ (d₁ - d₂)‖
        ≤ ‖(A u₁ - A u₂) d₁‖ + ‖A u₂ (d₁ - d₂)‖ := norm_add_le _ _
    _ ≤ (‖A u₁ - A u₂‖ * ‖d₁‖) +
          (‖A u₂‖ * ‖d₁ - d₂‖) :=
      add_le_add ((A u₁ - A u₂).le_opNorm d₁) ((A u₂).le_opNorm (d₁ - d₂))
    _ ≤ (L * ‖u₁ - u₂‖) * ‖d₁‖ + K * ‖d₁ - d₂‖ := by
      exact add_le_add
        (mul_le_mul_of_nonneg_right hA (norm_nonneg _))
        (mul_le_mul_of_nonneg_right hK (norm_nonneg _))

/-- A continuous coefficient flux, packaged as a bounded continuous function.
Only a zeroth-order bound for the coefficient along the chosen path is used. -/
def coeffBCF (A : U → G →L[ℝ] F) (hA : Continuous A)
    (K : ℝ) (hK0 : 0 ≤ K) (u : V →ᵇ U) (d : V →ᵇ G)
    (hK : ∀ x, ‖A (u x)‖ ≤ K) : V →ᵇ F :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => A (u x) (d x))
    (by fun_prop)
    (K * ‖d‖)
    (fun x => by
      calc
        ‖A (u x) (d x)‖ ≤ ‖A (u x)‖ * ‖d x‖ := (A (u x)).le_opNorm _
        _ ≤ K * ‖d x‖ :=
          mul_le_mul_of_nonneg_right (hK x) (norm_nonneg _)
        _ ≤ K * ‖d‖ :=
          mul_le_mul_of_nonneg_left (d.norm_coe_le_norm x) hK0)

/-- Supremum norm of the packaged coefficient flux. -/
theorem coeffBCF_norm (A : U → G →L[ℝ] F) (hA : Continuous A)
    (K : ℝ) (hK0 : 0 ≤ K) (u : V →ᵇ U) (d : V →ᵇ G)
    (hK : ∀ x, ‖A (u x)‖ ≤ K) :
    ‖coeffBCF A hA K hK0 u d hK‖ ≤ K * ‖d‖ := by
  unfold coeffBCF
  exact BoundedContinuousFunction.norm_ofNormedAddCommGroup_le
    (by fun_prop) (mul_nonneg hK0 (norm_nonneg _)) (fun x => by
      calc
        ‖A (u x) (d x)‖ ≤ ‖A (u x)‖ * ‖d x‖ := (A (u x)).le_opNorm _
        _ ≤ K * ‖d x‖ :=
          mul_le_mul_of_nonneg_right (hK x) (norm_nonneg _)
        _ ≤ K * ‖d‖ :=
          mul_le_mul_of_nonneg_left (d.norm_coe_le_norm x) hK0)

/-- Supremum-norm nonlinear difference estimate for coefficient fluxes.

For the Ricci--DeTurck principal arm, `A` is the inverse-metric coefficient
map restricted to a small positive-definite `C⁰` ball.  The estimate uses only
its zeroth-order bound and Lipschitz dependence on the metric value. -/
theorem coeffBCF_diff (A : U → G →L[ℝ] F) {L : ℝ≥0}
    (hA : LipschitzWith L A) (K : ℝ) (hK0 : 0 ≤ K)
    (u₁ u₂ : V →ᵇ U) (d₁ d₂ : V →ᵇ G)
    (hK₁ : ∀ x, ‖A (u₁ x)‖ ≤ K)
    (hK₂ : ∀ x, ‖A (u₂ x)‖ ≤ K) :
    ‖coeffBCF A hA.continuous K hK0 u₁ d₁ hK₁ -
        coeffBCF A hA.continuous K hK0 u₂ d₂ hK₂‖ ≤
      (L : ℝ) * ‖u₁ - u₂‖ * ‖d₁‖ + K * ‖d₁ - d₂‖ := by
  refine (BoundedContinuousFunction.norm_le ?_).2 ?_
  · exact add_nonneg
      (mul_nonneg (mul_nonneg L.coe_nonneg (norm_nonneg _)) (norm_nonneg _))
      (mul_nonneg hK0 (norm_nonneg _))
  · intro x
    change ‖A (u₁ x) (d₁ x) - A (u₂ x) (d₂ x)‖ ≤ _
    have hLipx : ‖A (u₁ x) - A (u₂ x)‖ ≤
        (L : ℝ) * ‖u₁ x - u₂ x‖ := by
      simpa only [dist_eq_norm] using hA.dist_le_mul (u₁ x) (u₂ x)
    calc
      ‖A (u₁ x) (d₁ x) - A (u₂ x) (d₂ x)‖
          ≤ (L : ℝ) * ‖u₁ x - u₂ x‖ * ‖d₁ x‖ +
              K * ‖d₁ x - d₂ x‖ :=
        fluxDiff_norm A (u₁ x) (u₂ x) (d₁ x) (d₂ x) hLipx (hK₂ x)
      _ ≤ (L : ℝ) * ‖u₁ - u₂‖ * ‖d₁‖ + K * ‖d₁ - d₂‖ := by
        have hu : ‖u₁ x - u₂ x‖ ≤ ‖u₁ - u₂‖ := by
          simpa only [BoundedContinuousFunction.sub_apply] using
            (u₁ - u₂).norm_coe_le_norm x
        have hd₁ : ‖d₁ x‖ ≤ ‖d₁‖ := d₁.norm_coe_le_norm x
        have hd : ‖d₁ x - d₂ x‖ ≤ ‖d₁ - d₂‖ := by
          simpa only [BoundedContinuousFunction.sub_apply] using
            (d₁ - d₂).norm_coe_le_norm x
        gcongr

end CoefficientFlux

section WeightedFlux

variable {V U G F : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- `C⁰` stability of the divergence flux in the weighted pointwise part
of the rough norm.  The coefficient variation is controlled only by the
`C⁰` state difference; both first-derivative factors retain their
`sqrt(t)` weights. -/
theorem fluxDiffWt (A : U → G →L[ℝ] F) {L : ℝ≥0}
    (hA : LipschitzWith L A) {T K D A₁ AΔ : ℝ}
    (hK0 : 0 ≤ K) (hD0 : 0 ≤ D)
    {u₁ u₂ : ℝ × V → U} {d₁ d₂ : ℝ × V → G}
    (hK₂ : ∀ z, ‖A (u₂ z)‖ ≤ K)
    (hu : PathSup T D (fun z ↦ u₁ z - u₂ z))
    (hd₁ : GradWt T A₁ d₁)
    (hdΔ : GradWt T AΔ (fun z ↦ d₁ z - d₂ z)) :
    GradWt T ((L : ℝ) * D * A₁ + K * AΔ)
      (fun z ↦ A (u₁ z) (d₁ z) - A (u₂ z) (d₂ z)) := by
  intro t x ht hT
  have hLip : ‖A (u₁ (t, x)) - A (u₂ (t, x))‖ ≤
      (L : ℝ) * ‖u₁ (t, x) - u₂ (t, x)‖ := by
    simpa only [dist_eq_norm] using hA.dist_le_mul (u₁ (t, x)) (u₂ (t, x))
  have hpoint := fluxDiff_norm A (u₁ (t, x)) (u₂ (t, x))
    (d₁ (t, x)) (d₂ (t, x)) hLip (hK₂ (t, x))
  have hu' := hu t x ht hT
  have hd₁' := hd₁ t x ht hT
  have hdΔ' := hdΔ t x ht hT
  calc
    Real.sqrt t *
        ‖A (u₁ (t, x)) (d₁ (t, x)) - A (u₂ (t, x)) (d₂ (t, x))‖
        ≤ Real.sqrt t *
          (((L : ℝ) * ‖u₁ (t, x) - u₂ (t, x)‖) * ‖d₁ (t, x)‖ +
            K * ‖d₁ (t, x) - d₂ (t, x)‖) :=
      mul_le_mul_of_nonneg_left hpoint (Real.sqrt_nonneg _)
    _ = (L : ℝ) * ‖u₁ (t, x) - u₂ (t, x)‖ *
          (Real.sqrt t * ‖d₁ (t, x)‖) +
        K * (Real.sqrt t * ‖d₁ (t, x) - d₂ (t, x)‖) := by
      ring
    _ ≤ (L : ℝ) * D * (Real.sqrt t * ‖d₁ (t, x)‖) +
        K * (Real.sqrt t * ‖d₁ (t, x) - d₂ (t, x)‖) := by
      gcongr
    _ ≤ (L : ℝ) * D * A₁ + K * AΔ := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hd₁' (mul_nonneg L.coe_nonneg hD0))
        (mul_le_mul_of_nonneg_left hdΔ' hK0)

end WeightedFlux

section HeatFlux

variable {V U G F : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [Nontrivial V]
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Difference estimate for the spatial integrand of the divergence-form
Ricci--DeTurck Duhamel arm.  Time integration is intentionally left to the
rough parabolic solution norm; this lemma is the exact `D H * (A(u) Du)`
estimate at one positive time separation. -/
theorem heatCoeff_diff (A : U → G →L[ℝ] F) {L : ℝ≥0}
    (hA : LipschitzWith L A) (K : ℝ) (hK0 : 0 ≤ K)
    {t : ℝ} (ht : 0 < t) (v : V)
    (u₁ u₂ : V →ᵇ U) (d₁ d₂ : V →ᵇ G)
    (hK₁ : ∀ x, ‖A (u₁ x)‖ ≤ K)
    (hK₂ : ∀ x, ‖A (u₂ x)‖ ≤ K) (x : V) :
    ‖heatD1Sup t v (coeffBCF A hA.continuous K hK0 u₁ d₁ hK₁) x -
        heatD1Sup t v (coeffBCF A hA.continuous K hK0 u₂ d₂ hK₂) x‖ ≤
      (‖v‖ * (heatScale t)⁻¹ * heatC1 V) *
        ((L : ℝ) * ‖u₁ - u₂‖ * ‖d₁‖ + K * ‖d₁ - d₂‖) := by
  rw [← heatD1Sup_sub ht v]
  calc
    ‖heatD1Sup t v
        (coeffBCF A hA.continuous K hK0 u₁ d₁ hK₁ -
          coeffBCF A hA.continuous K hK0 u₂ d₂ hK₂) x‖
        ≤ (‖v‖ * (heatScale t)⁻¹ * heatC1 V) *
            ‖coeffBCF A hA.continuous K hK0 u₁ d₁ hK₁ -
              coeffBCF A hA.continuous K hK0 u₂ d₂ hK₂‖ :=
      heatD1Sup_norm ht v _ x
    _ ≤ (‖v‖ * (heatScale t)⁻¹ * heatC1 V) *
          ((L : ℝ) * ‖u₁ - u₂‖ * ‖d₁‖ + K * ‖d₁ - d₂‖) := by
      apply mul_le_mul_of_nonneg_left
        (coeffBCF_diff A hA K hK0 u₁ u₂ d₁ d₂ hK₁ hK₂)
      exact mul_nonneg
        (mul_nonneg (norm_nonneg _) (inv_nonneg.mpr (heatScale_pos ht).le))
        (heatC1_nonneg (V := V))

end HeatFlux

section Correction

variable {U G H F : Type*}
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Three-arm difference estimate for the compensating quadratic-gradient
term `DA(u)[Du] Dw` produced by `coeffD2_refold`.

Here `C u` is the bilinear map `(Du,Dw) ↦ DA(u)[Du] Dw`.  The hypotheses are
the pointwise Lipschitz bound for `DA` and a pointwise operator bound at the
second state. -/
theorem corrDiff_norm (C : U → G →L[ℝ] H →L[ℝ] F)
    (u₁ u₂ : U) (d₁ d₂ : G) (e₁ e₂ : H) {L K : ℝ}
    (hC : ‖C u₁ - C u₂‖ ≤ L * ‖u₁ - u₂‖)
    (hK : ‖C u₂‖ ≤ K) :
    ‖C u₁ d₁ e₁ - C u₂ d₂ e₂‖ ≤
      (L * ‖u₁ - u₂‖) * ‖d₁‖ * ‖e₁‖ +
        (K * ‖d₁ - d₂‖) * ‖e₁‖ +
        (K * ‖d₂‖) * ‖e₁ - e₂‖ := by
  have hsplit :
      C u₁ d₁ e₁ - C u₂ d₂ e₂ =
        (C u₁ - C u₂) d₁ e₁ +
          C u₂ (d₁ - d₂) e₁ + C u₂ d₂ (e₁ - e₂) := by
    simp only [ContinuousLinearMap.sub_apply, map_sub]
    abel
  rw [hsplit]
  calc
    ‖(C u₁ - C u₂) d₁ e₁ + C u₂ (d₁ - d₂) e₁ + C u₂ d₂ (e₁ - e₂)‖
        ≤ ‖(C u₁ - C u₂) d₁ e₁‖ + ‖C u₂ (d₁ - d₂) e₁‖ +
            ‖C u₂ d₂ (e₁ - e₂)‖ := by
          exact (norm_add_le _ _).trans
            (add_le_add_right (norm_add_le _ _) _)
    _ ≤ (‖C u₁ - C u₂‖ * ‖d₁‖) * ‖e₁‖ +
          (‖C u₂‖ * ‖d₁ - d₂‖) * ‖e₁‖ +
          (‖C u₂‖ * ‖d₂‖) * ‖e₁ - e₂‖ := by
      exact add_le_add
        (add_le_add
          (((C u₁ - C u₂) d₁).le_opNorm e₁ |>.trans
            (mul_le_mul_of_nonneg_right ((C u₁ - C u₂).le_opNorm d₁)
              (norm_nonneg _)))
          (((C u₂) (d₁ - d₂)).le_opNorm e₁ |>.trans
            (mul_le_mul_of_nonneg_right ((C u₂).le_opNorm (d₁ - d₂))
              (norm_nonneg _))))
        (((C u₂) d₂).le_opNorm (e₁ - e₂) |>.trans
          (mul_le_mul_of_nonneg_right ((C u₂).le_opNorm d₂) (norm_nonneg _)))
    _ ≤ (L * ‖u₁ - u₂‖) * ‖d₁‖ * ‖e₁‖ +
          (K * ‖d₁ - d₂‖) * ‖e₁‖ +
          (K * ‖d₂‖) * ‖e₁ - e₂‖ := by
      exact add_le_add
        (add_le_add
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hC (norm_nonneg _)) (norm_nonneg _))
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hK (norm_nonneg _)) (norm_nonneg _)))
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hK (norm_nonneg _)) (norm_nonneg _))

end Correction

section WeightedCorrection

variable {V U G H F : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- `C⁰` stability of the compensating quadratic-gradient arm in the
weighted source norm.  This is the time-weighted counterpart of
`corrDiff_norm`; none of its three arms is dropped. -/
theorem corrDiffWt (C : U → G →L[ℝ] H →L[ℝ] F) {L : ℝ≥0}
    (hC : LipschitzWith L C)
    {T K D A₁ A₂ AΔ E₁ EΔ : ℝ}
    (hK0 : 0 ≤ K) (hD0 : 0 ≤ D) (hA₁0 : 0 ≤ A₁)
    (hA₂0 : 0 ≤ A₂) (hAΔ0 : 0 ≤ AΔ)
    {u₁ u₂ : ℝ × V → U} {d₁ d₂ : ℝ × V → G}
    {e₁ e₂ : ℝ × V → H}
    (hK₂ : ∀ z, ‖C (u₂ z)‖ ≤ K)
    (hu : PathSup T D (fun z ↦ u₁ z - u₂ z))
    (hd₁ : GradWt T A₁ d₁) (hd₂ : GradWt T A₂ d₂)
    (hdΔ : GradWt T AΔ (fun z ↦ d₁ z - d₂ z))
    (he₁ : GradWt T E₁ e₁)
    (heΔ : GradWt T EΔ (fun z ↦ e₁ z - e₂ z)) :
    SrcWt T
      ((L : ℝ) * D * A₁ * E₁ + K * AΔ * E₁ + K * A₂ * EΔ)
      (fun z ↦ C (u₁ z) (d₁ z) (e₁ z) - C (u₂ z) (d₂ z) (e₂ z)) := by
  intro t x ht hT
  have hLip : ‖C (u₁ (t, x)) - C (u₂ (t, x))‖ ≤
      (L : ℝ) * ‖u₁ (t, x) - u₂ (t, x)‖ := by
    simpa only [dist_eq_norm] using hC.dist_le_mul (u₁ (t, x)) (u₂ (t, x))
  have hpoint := corrDiff_norm C (u₁ (t, x)) (u₂ (t, x))
    (d₁ (t, x)) (d₂ (t, x)) (e₁ (t, x)) (e₂ (t, x))
    hLip (hK₂ (t, x))
  have hu' := hu t x ht hT
  have hd₁' := hd₁ t x ht hT
  have hd₂' := hd₂ t x ht hT
  have hdΔ' := hdΔ t x ht hT
  have he₁' := he₁ t x ht hT
  have heΔ' := heΔ t x ht hT
  have hterm₁ :
      (L : ℝ) * ‖u₁ (t, x) - u₂ (t, x)‖ *
          (Real.sqrt t * ‖d₁ (t, x)‖) * (Real.sqrt t * ‖e₁ (t, x)‖) ≤
        (L : ℝ) * D * A₁ * E₁ := by
    calc
      (L : ℝ) * ‖u₁ (t, x) - u₂ (t, x)‖ *
          (Real.sqrt t * ‖d₁ (t, x)‖) * (Real.sqrt t * ‖e₁ (t, x)‖)
          ≤ (L : ℝ) * D * (Real.sqrt t * ‖d₁ (t, x)‖) *
              (Real.sqrt t * ‖e₁ (t, x)‖) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hu' L.coe_nonneg)
            (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)))
          (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
      _ ≤ (L : ℝ) * D * A₁ * (Real.sqrt t * ‖e₁ (t, x)‖) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hd₁' (mul_nonneg L.coe_nonneg hD0))
          (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
      _ ≤ (L : ℝ) * D * A₁ * E₁ :=
        mul_le_mul_of_nonneg_left he₁'
          (mul_nonneg (mul_nonneg L.coe_nonneg hD0) hA₁0)
  have hterm₂ :
      K * (Real.sqrt t * ‖d₁ (t, x) - d₂ (t, x)‖) *
          (Real.sqrt t * ‖e₁ (t, x)‖) ≤ K * AΔ * E₁ := by
    calc
      K * (Real.sqrt t * ‖d₁ (t, x) - d₂ (t, x)‖) *
          (Real.sqrt t * ‖e₁ (t, x)‖)
          ≤ K * AΔ * (Real.sqrt t * ‖e₁ (t, x)‖) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hdΔ' hK0)
          (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
      _ ≤ K * AΔ * E₁ :=
        mul_le_mul_of_nonneg_left he₁' (mul_nonneg hK0 hAΔ0)
  have hterm₃ :
      K * (Real.sqrt t * ‖d₂ (t, x)‖) *
          (Real.sqrt t * ‖e₁ (t, x) - e₂ (t, x)‖) ≤ K * A₂ * EΔ := by
    calc
      K * (Real.sqrt t * ‖d₂ (t, x)‖) *
          (Real.sqrt t * ‖e₁ (t, x) - e₂ (t, x)‖)
          ≤ K * A₂ * (Real.sqrt t * ‖e₁ (t, x) - e₂ (t, x)‖) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hd₂' hK0)
          (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
      _ ≤ K * A₂ * EΔ :=
        mul_le_mul_of_nonneg_left heΔ' (mul_nonneg hK0 hA₂0)
  calc
    t * ‖C (u₁ (t, x)) (d₁ (t, x)) (e₁ (t, x)) -
        C (u₂ (t, x)) (d₂ (t, x)) (e₂ (t, x))‖
        ≤ t *
          (((L : ℝ) * ‖u₁ (t, x) - u₂ (t, x)‖) * ‖d₁ (t, x)‖ * ‖e₁ (t, x)‖ +
            (K * ‖d₁ (t, x) - d₂ (t, x)‖) * ‖e₁ (t, x)‖ +
            (K * ‖d₂ (t, x)‖) * ‖e₁ (t, x) - e₂ (t, x)‖) :=
      mul_le_mul_of_nonneg_left hpoint ht.le
    _ = (L : ℝ) * ‖u₁ (t, x) - u₂ (t, x)‖ *
          (Real.sqrt t * ‖d₁ (t, x)‖) * (Real.sqrt t * ‖e₁ (t, x)‖) +
        K * (Real.sqrt t * ‖d₁ (t, x) - d₂ (t, x)‖) *
          (Real.sqrt t * ‖e₁ (t, x)‖) +
        K * (Real.sqrt t * ‖d₂ (t, x)‖) *
          (Real.sqrt t * ‖e₁ (t, x) - e₂ (t, x)‖) := by
      rw [← Real.sq_sqrt ht.le]
      ring
    _ ≤ (L : ℝ) * D * A₁ * E₁ + K * AΔ * E₁ + K * A₂ * EΔ := by
      exact add_le_add (add_le_add hterm₁ hterm₂) hterm₃

end WeightedCorrection

end Euclidean
end Parabolic
end Analysis
end DifferentialGeometry

end
