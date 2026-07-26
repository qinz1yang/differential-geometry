import Mathlib.Analysis.InnerProductSpace.LaxMilgram
import DifferentialGeometry.Analysis.Calculus.RingInverseDeriv

set_option autoImplicit false

/-!
# Quantitative inverse bound for a coercive bilinear form

An explicit quadratic coercivity constant bounds the inverse of the
Lax--Milgram equivalence.  This is the algebraic estimate used to turn a
uniform lower metric comparison into a uniform bound for the corresponding
sharp operator.
-/

noncomputable section

open RealInnerProductSpace

namespace IsCoercive

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [CompleteSpace E] [FiniteDimensional Real E]

instance : FiniteDimensional Real (StrongDual Real E) :=
  inferInstanceAs (FiniteDimensional Real (E →L[Real] Real))

/-- If `B v v` dominates `c * ||v||^2`, then the inverse Lax--Milgram map has
pointwise norm at most `c^{-1}`. -/
theorem symm_norm_le {B : E →L[Real] E →L[Real] Real}
    (hco : IsCoercive B) {c : Real} (hc : 0 < c)
    (hB : ∀ v : E, c * ‖v‖ * ‖v‖ ≤ B v v) (xi : E) :
    ‖hco.continuousLinearEquivOfBilin.symm xi‖ ≤ c⁻¹ * ‖xi‖ := by
  let u := hco.continuousLinearEquivOfBilin.symm xi
  have heu : hco.continuousLinearEquivOfBilin u = xi :=
    hco.continuousLinearEquivOfBilin.apply_symm_apply xi
  change ‖u‖ ≤ c⁻¹ * ‖xi‖
  by_cases hu : u = 0
  · rw [hu, norm_zero]
    exact mul_nonneg (inv_nonneg.mpr hc.le) (norm_nonneg xi)
  · have hupos : 0 < ‖u‖ := norm_pos_iff.mpr hu
    have hcu : c * ‖u‖ ≤ ‖xi‖ := by
      refine le_of_mul_le_mul_right ?_ hupos
      calc
        c * ‖u‖ * ‖u‖ ≤ B u u := hB u
        _ = inner Real (hco.continuousLinearEquivOfBilin u) u :=
          (hco.continuousLinearEquivOfBilin_apply u u).symm
        _ = inner Real xi u := by rw [heu]
        _ ≤ ‖xi‖ * ‖u‖ := real_inner_le_norm xi u
    calc
      ‖u‖ ≤ ‖xi‖ / c := (le_div_iff₀ hc).mpr (by simpa [mul_comm] using hcu)
      _ = c⁻¹ * ‖xi‖ := by rw [div_eq_mul_inv, mul_comm]

/-- The sharp map of a coercive bilinear form, from continuous covectors to
vectors, obtained from the Lax--Milgram equivalence and Riesz duality. -/
noncomputable def sharp {B : E →L[Real] E →L[Real] Real}
    (hco : IsCoercive B) (eta : E →L[Real] Real) : E :=
  hco.continuousLinearEquivOfBilin.symm
    ((InnerProductSpace.toDual Real E).symm eta)

/-- For a coercive bilinear form, `sharp` is the proof-independent ring
inverse of its Gram operator applied to the Riesz representative. -/
theorem sharp_eq_inverse {B : E →L[Real] E →L[Real] Real}
    (hco : IsCoercive B) (eta : E →L[Real] Real) :
    hco.sharp eta =
      Ring.inverse (InnerProductSpace.continuousLinearMapOfBilin (𝕜 := Real) B)
        ((InnerProductSpace.toDual Real E).symm eta) := by
  change hco.continuousLinearEquivOfBilin.symm _ =
    Ring.inverse
      (↑hco.continuousLinearEquivOfBilin.toUnit : E →L[Real] E) _
  rw [Ring.inverse_unit]
  rfl

/-- Applying the metric-flat map after `sharp` recovers the covector. -/
@[simp] theorem apply_sharp {B : E →L[Real] E →L[Real] Real}
    (hco : IsCoercive B) (eta : E →L[Real] Real) :
    B (hco.sharp eta) = eta := by
  apply ContinuousLinearMap.ext
  intro w
  rw [← hco.continuousLinearEquivOfBilin_apply]
  simp [sharp]

/-- Raising the covector obtained by lowering a vector recovers that vector. -/
@[simp] theorem sharp_apply {B : E →L[Real] E →L[Real] Real}
    (hco : IsCoercive B) (u : E) :
    hco.sharp (B u) = u := by
  apply hco.continuousLinearEquivOfBilin.injective
  apply ext_inner_right Real
  intro w
  rw [hco.continuousLinearEquivOfBilin_apply,
    hco.continuousLinearEquivOfBilin_apply]
  exact DFunLike.congr_fun (hco.apply_sharp (B u)) w

/-- The sharp operation is linear with respect to subtraction of covectors. -/
theorem sharp_sub {B : E →L[Real] E →L[Real] Real}
    (hco : IsCoercive B) (eta theta : E →L[Real] Real) :
    hco.sharp (eta - theta) = hco.sharp eta - hco.sharp theta := by
  simp [sharp]

/-- An explicit quadratic coercivity constant bounds the norm of the sharp
map on continuous covectors. -/
theorem sharp_norm_le {B : E →L[Real] E →L[Real] Real}
    (hco : IsCoercive B) {c : Real} (hc : 0 < c)
    (hB : ∀ v : E, c * ‖v‖ * ‖v‖ ≤ B v v) (eta : E →L[Real] Real) :
    ‖hco.sharp eta‖ ≤ c⁻¹ * ‖eta‖ := by
  have h := hco.symm_norm_le hc hB ((InnerProductSpace.toDual Real E).symm eta)
  unfold sharp
  rw [← (InnerProductSpace.toDual Real E).symm.norm_map eta]
  exact h

/-- The sharp operation packaged as a continuous linear map from covectors to
vectors.  This is the finite-Galerkin mass-matrix inverse in invariant form. -/
noncomputable def sharpCLM {B : E →L[Real] E →L[Real] Real}
    (hco : IsCoercive B) : (E →L[Real] Real) →L[Real] E :=
  hco.continuousLinearEquivOfBilin.symm.toContinuousLinearMap.comp
    (InnerProductSpace.toDual Real E).symm.toContinuousLinearEquiv.toContinuousLinearMap

@[simp] theorem sharpCLM_apply {B : E →L[Real] E →L[Real] Real}
    (hco : IsCoercive B) (eta : E →L[Real] Real) :
    hco.sharpCLM eta = hco.sharp eta := rfl

/-- A uniform quadratic coercivity constant gives the corresponding operator
norm bound for the packaged sharp map. -/
theorem sharpCLM_norm_le {B : E →L[Real] E →L[Real] Real}
    (hco : IsCoercive B) {c : Real} (hc : 0 < c)
    (hB : ∀ v : E, c * ‖v‖ * ‖v‖ ≤ B v v) :
    ‖hco.sharpCLM‖ ≤ c⁻¹ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr hc.le) ?_
  intro eta
  rw [sharpCLM_apply]
  exact hco.sharp_norm_le hc hB eta

/-- The canonical Gram construction, regarded as a bounded linear operation on
bilinear forms. -/
noncomputable def gramCLM :
    (E →L[Real] E →L[Real] Real) →L[Real] (E →L[Real] E) :=
  ContinuousLinearMap.compL Real E (E →L[Real] Real) E
    (InnerProductSpace.toDual Real E).symm.toContinuousLinearEquiv.toContinuousLinearMap

@[simp] theorem gramCLM_apply (B : E →L[Real] E →L[Real] Real) :
    gramCLM B = InnerProductSpace.continuousLinearMapOfBilin (𝕜 := Real) B := rfl

theorem gramCLM_isUnit {B : E →L[Real] E →L[Real] Real} (hB : IsCoercive B) :
    IsUnit (gramCLM B) := by
  rw [gramCLM_apply]
  exact ⟨hB.continuousLinearEquivOfBilin.toUnit, rfl⟩

/-- A continuous family of coercive bilinear forms has a continuous family of
packaged sharp maps.  This is the finite-dimensional moving-mass inverse
continuity bridge used by nonautonomous Galerkin systems. -/
theorem sharpCLM_contOn
    {X : Type*} [TopologicalSpace X] {S : Set X}
    (B : X → E →L[Real] E →L[Real] Real)
    (hB : ContinuousOn B S) (hco : ∀ x, IsCoercive (B x)) :
    ContinuousOn (fun x => (hco x).sharpCLM) S := by
  let G : (E →L[Real] E →L[Real] Real) →L[Real] (E →L[Real] E) := gramCLM
  have hG : ContinuousOn (fun x => G (B x)) S :=
    G.continuous.comp_continuousOn hB
  have hinv : ContinuousOn (fun x => Ring.inverse (G (B x))) S := by
    intro x hx
    obtain ⟨u, hu⟩ := gramCLM_isUnit (hco x)
    have hri : ContinuousAt (fun A : E →L[Real] E => Ring.inverse A) (G (B x)) := by
      rw [show G (B x) = (u : E →L[Real] E) from hu.symm]
      exact (contDiffAt_ringInverse (n := 1) Real u).continuousAt
    exact ContinuousAt.comp_continuousWithinAt (f := fun y => G (B y)) hri (hG x hx)
  let R : (E →L[Real] Real) →L[Real] E :=
    (InnerProductSpace.toDual Real E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hcomp : ContinuousOn
      (fun x => (Ring.inverse (G (B x))).comp R) S := by
    have hleft : ContinuousOn
        (fun x => ContinuousLinearMap.compL Real (E →L[Real] Real) E E
          (Ring.inverse (G (B x)))) S :=
      (ContinuousLinearMap.compL Real (E →L[Real] Real) E E).continuous.comp_continuousOn
        hinv
    simpa only [ContinuousLinearMap.compL_apply] using
      hleft.clm_apply (continuousOn_const : ContinuousOn (fun _ : X => R) S)
  refine hcomp.congr ?_
  intro x hx
  apply ContinuousLinearMap.ext
  intro eta
  rw [sharpCLM_apply, sharp_eq_inverse]
  rfl

/-- Restricted version of `sharpCLM_contOn`: coercivity is needed only at
points of the set on which the bilinear family is continuous. -/
theorem sharpCLM_cont_sub
    {X : Type*} [TopologicalSpace X] {S : Set X}
    (B : X → E →L[Real] E →L[Real] Real)
    (hB : ContinuousOn B S)
    (hco : ∀ x ∈ S, IsCoercive (B x)) :
    Continuous (fun x : S => (hco x x.2).sharpCLM) := by
  have hsub : ContinuousOn
      (fun x : S => B x) (Set.univ : Set S) := hB.restrict.continuousOn
  have h := sharpCLM_contOn (fun x : S => B x) hsub
    (fun x => hco x x.2)
  exact continuousOn_univ.mp h

/-- Resolvent estimate for the sharp maps of two coercive bilinear forms.
The inverse constants are kept explicit so callers can specialize them to
uniform metric lower bounds. -/
theorem sharp_sub_le
    {B C : E →L[Real] E →L[Real] Real}
    (hBco : IsCoercive B) (hCco : IsCoercive C)
    {cB cC : Real} (hcB : 0 < cB) (hcC : 0 < cC)
    (hB : ∀ u : E, cB * ‖u‖ * ‖u‖ ≤ B u u)
    (hC : ∀ u : E, cC * ‖u‖ * ‖u‖ ≤ C u u)
    (eta : E →L[Real] Real) :
    ‖hBco.sharp eta - hCco.sharp eta‖ ≤
      cB⁻¹ * (‖C - B‖ * (cC⁻¹ * ‖eta‖)) := by
  have heq :
      hBco.sharp eta - hCco.sharp eta =
        hBco.sharp ((C - B) (hCco.sharp eta)) := by
    calc
      hBco.sharp eta - hCco.sharp eta =
          hBco.sharp (B (hBco.sharp eta - hCco.sharp eta)) :=
        (hBco.sharp_apply _).symm
      _ = hBco.sharp (B (hBco.sharp eta) - B (hCco.sharp eta)) := by
        rw [map_sub]
      _ = hBco.sharp (eta - B (hCco.sharp eta)) := by
        rw [hBco.apply_sharp]
      _ = hBco.sharp (C (hCco.sharp eta) - B (hCco.sharp eta)) := by
        rw [hCco.apply_sharp]
      _ = hBco.sharp ((C - B) (hCco.sharp eta)) := by
        rw [ContinuousLinearMap.sub_apply]
  rw [heq]
  calc
    ‖hBco.sharp ((C - B) (hCco.sharp eta))‖ ≤
        cB⁻¹ * ‖(C - B) (hCco.sharp eta)‖ :=
      hBco.sharp_norm_le hcB hB _
    _ ≤ cB⁻¹ * (‖C - B‖ * ‖hCco.sharp eta‖) := by
      gcongr
      exact ContinuousLinearMap.le_opNorm (C - B) (hCco.sharp eta)
    _ ≤ cB⁻¹ * (‖C - B‖ * (cC⁻¹ * ‖eta‖)) := by
      gcongr
      exact hCco.sharp_norm_le hcC hC eta

/-- Joint resolvent estimate when both the coercive form and the covector
vary.  This is the quantitative continuity input for a moving Galerkin mass
matrix inverse. -/
theorem sharp_var_le
    {B C : E →L[Real] E →L[Real] Real}
    (hBco : IsCoercive B) (hCco : IsCoercive C)
    {cB cC : Real} (hcB : 0 < cB) (hcC : 0 < cC)
    (hB : ∀ u : E, cB * ‖u‖ * ‖u‖ ≤ B u u)
    (hC : ∀ u : E, cC * ‖u‖ * ‖u‖ ≤ C u u)
    (eta theta : E →L[Real] Real) :
    ‖hBco.sharp eta - hCco.sharp theta‖ ≤
      cB⁻¹ * ‖eta - theta‖ +
        cB⁻¹ * (‖C - B‖ * (cC⁻¹ * ‖theta‖)) := by
  have hsplit :
      hBco.sharp eta - hCco.sharp theta =
        (hBco.sharp eta - hBco.sharp theta) +
          (hBco.sharp theta - hCco.sharp theta) := by
    abel
  rw [hsplit]
  calc
    ‖(hBco.sharp eta - hBco.sharp theta) +
        (hBco.sharp theta - hCco.sharp theta)‖ ≤
        ‖hBco.sharp eta - hBco.sharp theta‖ +
          ‖hBco.sharp theta - hCco.sharp theta‖ := norm_add_le _ _
    _ ≤ cB⁻¹ * ‖eta - theta‖ +
        cB⁻¹ * (‖C - B‖ * (cC⁻¹ * ‖theta‖)) := by
      apply add_le_add
      · rw [← hBco.sharp_sub]
        exact hBco.sharp_norm_le hcB hB (eta - theta)
      · exact hBco.sharp_sub_le hCco hcB hcC hB hC theta

end IsCoercive
