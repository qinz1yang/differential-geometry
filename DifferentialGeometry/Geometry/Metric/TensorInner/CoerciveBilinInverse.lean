import Mathlib.Analysis.InnerProductSpace.LaxMilgram
import DifferentialGeometry.Analysis.Calculus.RingInverseDeriv

set_option autoImplicit false

noncomputable section
namespace DifferentialGeometry

open RealInnerProductSpace

class CoerciveBilinInverse (E : Type*) [NormedAddCommGroup E]
    [NormedSpace Real E] : Prop where
  surjective : ∀ {B : E →L[Real] E →L[Real] Real},
    IsCoercive B → Function.Surjective B

class ContinuousDualEquiv (E : Type*) [NormedAddCommGroup E]
    [NormedSpace Real E] where
  equiv : E ≃L[Real] (E →L[Real] Real)

namespace ContinuousDualEquiv

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace Real E]
  [ContinuousDualEquiv E]

noncomputable def normalization : Realˣ :=
  Units.mk0
    (1 + ‖((equiv (E := E)).symm : (E →L[Real] Real) →L[Real] E)‖)
    (by positivity)

noncomputable def normalizedEquiv : E ≃L[Real] (E →L[Real] Real) :=
  (ContinuousLinearEquiv.smulLeft (R₁ := Real) (M₁ := E)
      (normalization E)).trans (equiv (E := E))

theorem normalizedEquiv_symm_apply (eta : E →L[Real] Real) :
    (normalizedEquiv E).symm eta =
      (1 + ‖((equiv (E := E)).symm :
        (E →L[Real] Real) →L[Real] E)‖)⁻¹ •
        (equiv (E := E)).symm eta := by
  let s := ContinuousLinearEquiv.smulLeft (R₁ := Real) (M₁ := E)
    (normalization E)
  change s.symm ((equiv (E := E)).symm eta) = _
  apply s.injective
  rw [s.apply_symm_apply]
  simp only [s, normalization, ContinuousLinearEquiv.smulLeft_apply_apply,
    Units.smul_def, Units.val_mk0]
  exact (smul_inv_smul₀ (by positivity) _).symm

theorem normalizedEquiv_symm_norm_le_one :
    ‖((normalizedEquiv E).symm :
      (E →L[Real] Real) →L[Real] E)‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one ?_
  intro eta
  change ‖(normalizedEquiv E).symm eta‖ ≤ _
  rw [normalizedEquiv_symm_apply]
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (by positivity)]
  have he := ContinuousLinearMap.le_opNorm
    ((equiv (E := E)).symm : (E →L[Real] Real) →L[Real] E) eta
  calc
    (1 + ‖((equiv (E := E)).symm :
        (E →L[Real] Real) →L[Real] E)‖)⁻¹ *
        ‖(equiv (E := E)).symm eta‖ ≤
      (1 + ‖((equiv (E := E)).symm :
          (E →L[Real] Real) →L[Real] E)‖)⁻¹ *
        (‖((equiv (E := E)).symm :
          (E →L[Real] Real) →L[Real] E)‖ * ‖eta‖) :=
      mul_le_mul_of_nonneg_left (by simpa using he) (by positivity)
    _ ≤ 1 * ‖eta‖ := by
      have h :
          (1 + ‖((equiv (E := E)).symm :
              (E →L[Real] Real) →L[Real] E)‖)⁻¹ *
            ‖((equiv (E := E)).symm :
              (E →L[Real] Real) →L[Real] E)‖ ≤ 1 := by
        rw [inv_mul_le_one₀ (by positivity)]
        linarith [norm_nonneg
          ((equiv (E := E)).symm :
            (E →L[Real] Real) →L[Real] E)]
      nlinarith [norm_nonneg eta]

end ContinuousDualEquiv
end DifferentialGeometry

namespace IsCoercive
open DifferentialGeometry
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
instance [FiniteDimensional Real E] : FiniteDimensional Real (StrongDual Real E) :=
  inferInstanceAs (FiniteDimensional Real (E →L[Real] Real))

theorem bilin_injective {B : E →L[Real] E →L[Real] Real}
    (hco : IsCoercive B) : Function.Injective B := by
  intro u v huv
  rcases hco with ⟨c, hc, hB⟩
  have hzeroMap : B (u - v) = 0 := by rw [map_sub, huv, sub_self]
  have hbound := hB (u - v)
  have hzero : B (u - v) (u - v) = 0 := by rw [hzeroMap]; rfl
  rw [hzero] at hbound
  have hsub : u - v = 0 := by
    by_contra hne
    have hn : 0 < ‖u - v‖ := norm_pos_iff.mpr hne
    exact (not_lt_of_ge hbound) (mul_pos (mul_pos hc hn) hn)
  exact sub_eq_zero.mp hsub

noncomputable instance coerciveBilinInverseOfFiniteDimensional
    [FiniteDimensional Real E] : CoerciveBilinInverse E where
  surjective := by
    intro B hco
    exact (LinearEquiv.ofInjectiveOfFinrankEq B.toLinearMap
      (bilin_injective hco) (by
        rw [← LinearEquiv.finrank_eq LinearMap.toContinuousLinearMap]
        exact Subspace.dual_finrank_eq.symm)).surjective

noncomputable instance continuousDualEquivOfFiniteDimensional
    [FiniteDimensional Real E] : ContinuousDualEquiv E where
  equiv := ContinuousLinearEquiv.ofFinrankEq (by
    rw [← LinearEquiv.finrank_eq LinearMap.toContinuousLinearMap]
    exact Subspace.dual_finrank_eq.symm)

noncomputable instance (priority := 900) coerciveBilinInverseOfInnerProduct
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace Real F]
    [CompleteSpace F] : CoerciveBilinInverse F where
  surjective := by
    intro B hco eta
    refine ⟨hco.continuousLinearEquivOfBilin.symm
      ((InnerProductSpace.toDual Real F).symm eta), ?_⟩
    apply ContinuousLinearMap.ext
    intro w
    rw [← hco.continuousLinearEquivOfBilin_apply]
    simp

noncomputable instance (priority := 900) continuousDualEquivOfInnerProduct
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace Real F]
    [CompleteSpace F] : ContinuousDualEquiv F where
  equiv := (InnerProductSpace.toDual Real F).toContinuousLinearEquiv

variable [CompleteSpace E] [CoerciveBilinInverse E]

theorem symm_norm_le
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace Real F]
    [CompleteSpace F] {B : F →L[Real] F →L[Real] Real}
    (hco : IsCoercive B) {c : Real} (hc : 0 < c)
    (hB : ∀ v : F, c * ‖v‖ * ‖v‖ ≤ B v v) (xi : F) :
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

private noncomputable def toDualEquiv {B : E →L[Real] E →L[Real] Real}
    (hco : IsCoercive B) : E ≃L[Real] (E →L[Real] Real) :=
  ContinuousLinearEquiv.ofBijective B
    (LinearMap.ker_eq_bot.mpr (bilin_injective hco))
    (LinearMap.range_eq_top.mpr (CoerciveBilinInverse.surjective hco))

noncomputable def sharp {B : E →L[Real] E →L[Real] Real}
    (hco : IsCoercive B) (eta : E →L[Real] Real) : E :=
  (toDualEquiv hco).symm eta

theorem sharp_eq_inverse
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace Real F]
    [CompleteSpace F]
    {B : F →L[Real] F →L[Real] Real}
    (hco : IsCoercive B) (eta : F →L[Real] Real) :
    hco.sharp eta =
      Ring.inverse (InnerProductSpace.continuousLinearMapOfBilin (𝕜 := Real) B)
        ((InnerProductSpace.toDual Real F).symm eta) := by
  have heq : hco.sharp eta = hco.continuousLinearEquivOfBilin.symm
      ((InnerProductSpace.toDual Real F).symm eta) := by
    apply bilin_injective hco
    change B ((toDualEquiv hco).symm eta) = _
    have hlhs := (toDualEquiv hco).apply_symm_apply eta
    change B ((toDualEquiv hco).symm eta) = eta at hlhs
    rw [hlhs]
    symm
    apply ContinuousLinearMap.ext
    intro w
    rw [← hco.continuousLinearEquivOfBilin_apply]
    simp
  rw [heq]
  change hco.continuousLinearEquivOfBilin.symm _ =
    Ring.inverse
      (↑hco.continuousLinearEquivOfBilin.toUnit : F →L[Real] F) _
  rw [Ring.inverse_unit]
  rfl

@[simp] theorem apply_sharp {B : E →L[Real] E →L[Real] Real}
    (hco : IsCoercive B) (eta : E →L[Real] Real) :
    B (hco.sharp eta) = eta := by
  exact (toDualEquiv hco).apply_symm_apply eta

@[simp] theorem sharp_apply {B : E →L[Real] E →L[Real] Real}
    (hco : IsCoercive B) (u : E) :
    hco.sharp (B u) = u := by
  exact (toDualEquiv hco).symm_apply_apply u

theorem sharp_sub {B : E →L[Real] E →L[Real] Real}
    (hco : IsCoercive B) (eta theta : E →L[Real] Real) :
    hco.sharp (eta - theta) = hco.sharp eta - hco.sharp theta := by
  simp [sharp]

theorem sharp_norm_le {B : E →L[Real] E →L[Real] Real}
    (hco : IsCoercive B) {c : Real} (hc : 0 < c)
    (hB : ∀ v : E, c * ‖v‖ * ‖v‖ ≤ B v v) (eta : E →L[Real] Real) :
    ‖hco.sharp eta‖ ≤ c⁻¹ * ‖eta‖ := by
  let u := hco.sharp eta
  have heu : B u = eta := hco.apply_sharp eta
  by_cases hu : u = 0
  · change ‖u‖ ≤ c⁻¹ * ‖eta‖
    rw [hu, norm_zero]
    exact mul_nonneg (inv_nonneg.mpr hc.le) (norm_nonneg eta)
  · have hupos : 0 < ‖u‖ := norm_pos_iff.mpr hu
    have hcu : c * ‖u‖ ≤ ‖eta‖ := by
      refine le_of_mul_le_mul_right ?_ hupos
      calc
        c * ‖u‖ * ‖u‖ ≤ B u u := hB u
        _ = eta u := by rw [heu]
        _ ≤ ‖eta u‖ := by simpa [Real.norm_eq_abs] using le_abs_self (eta u)
        _ ≤ ‖eta‖ * ‖u‖ := eta.le_opNorm u
    calc
      ‖u‖ ≤ ‖eta‖ / c := (le_div_iff₀ hc).mpr (by simpa [mul_comm] using hcu)
      _ = c⁻¹ * ‖eta‖ := by rw [div_eq_mul_inv, mul_comm]

noncomputable def sharpCLM {B : E →L[Real] E →L[Real] Real}
    (hco : IsCoercive B) : (E →L[Real] Real) →L[Real] E :=
  (toDualEquiv hco).symm.toContinuousLinearMap
@[simp] theorem sharpCLM_apply {B : E →L[Real] E →L[Real] Real}
    (hco : IsCoercive B) (eta : E →L[Real] Real) :
    hco.sharpCLM eta = hco.sharp eta := rfl

theorem sharpCLM_norm_le {B : E →L[Real] E →L[Real] Real}
    (hco : IsCoercive B) {c : Real} (hc : 0 < c)
    (hB : ∀ v : E, c * ‖v‖ * ‖v‖ ≤ B v v) :
    ‖hco.sharpCLM‖ ≤ c⁻¹ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr hc.le) ?_
  intro eta
  rw [sharpCLM_apply]
  exact hco.sharp_norm_le hc hB eta
noncomputable def gramCLM
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace Real F]
    [CompleteSpace F] :
    (F →L[Real] F →L[Real] Real) →L[Real] (F →L[Real] F) :=
  ContinuousLinearMap.compL Real F (F →L[Real] Real) F
    (InnerProductSpace.toDual Real F).symm.toContinuousLinearEquiv.toContinuousLinearMap
@[simp] theorem gramCLM_apply
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace Real F]
    [CompleteSpace F] (B : F →L[Real] F →L[Real] Real) :
    gramCLM B = InnerProductSpace.continuousLinearMapOfBilin (𝕜 := Real) B := rfl
theorem gramCLM_isUnit
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace Real F]
    [CompleteSpace F] {B : F →L[Real] F →L[Real] Real} (hB : IsCoercive B) :
    IsUnit (gramCLM B) := by
  rw [gramCLM_apply]
  exact ⟨hB.continuousLinearEquivOfBilin.toUnit, rfl⟩

theorem sharpCLM_contOn
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace Real F]
    [CompleteSpace F]
    {X : Type*} [TopologicalSpace X] {S : Set X}
    (B : X → F →L[Real] F →L[Real] Real)
    (hB : ContinuousOn B S) (hco : ∀ x, IsCoercive (B x)) :
    ContinuousOn (fun x => (hco x).sharpCLM) S := by
  let G : (F →L[Real] F →L[Real] Real) →L[Real] (F →L[Real] F) := gramCLM
  have hG : ContinuousOn (fun x => G (B x)) S :=
    G.continuous.comp_continuousOn hB
  have hinv : ContinuousOn (fun x => Ring.inverse (G (B x))) S := by
    intro x hx
    obtain ⟨u, hu⟩ := gramCLM_isUnit (hco x)
    have hri : ContinuousAt (fun A : F →L[Real] F => Ring.inverse A) (G (B x)) := by
      rw [show G (B x) = (u : F →L[Real] F) from hu.symm]
      exact NormedRing.inverse_continuousAt u
    exact ContinuousAt.comp_continuousWithinAt (f := fun y => G (B y)) hri (hG x hx)
  let R : (F →L[Real] Real) →L[Real] F :=
    (InnerProductSpace.toDual Real F).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hcomp : ContinuousOn
      (fun x => (Ring.inverse (G (B x))).comp R) S := by
    have hleft : ContinuousOn
        (fun x => ContinuousLinearMap.compL Real (F →L[Real] Real) F F
          (Ring.inverse (G (B x)))) S :=
      (ContinuousLinearMap.compL Real (F →L[Real] Real) F F).continuous.comp_continuousOn
        hinv
    simpa only [ContinuousLinearMap.compL_apply] using
      hleft.clm_apply (continuousOn_const : ContinuousOn (fun _ : X => R) S)
  refine hcomp.congr ?_
  intro x hx
  apply ContinuousLinearMap.ext
  intro eta
  rw [sharpCLM_apply, sharp_eq_inverse]
  rfl

theorem sharpCLM_cont_sub
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace Real F]
    [CompleteSpace F]
    {X : Type*} [TopologicalSpace X] {S : Set X}
    (B : X → F →L[Real] F →L[Real] Real)
    (hB : ContinuousOn B S)
    (hco : ∀ x ∈ S, IsCoercive (B x)) :
    Continuous (fun x : S => (hco x x.2).sharpCLM) := by
  have hsub : ContinuousOn
      (fun x : S => B x) (Set.univ : Set S) := hB.restrict.continuousOn
  have h := sharpCLM_contOn (fun x : S => B x) hsub
    (fun x => hco x x.2)
  exact continuousOn_univ.mp h

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
