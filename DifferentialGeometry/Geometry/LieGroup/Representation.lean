import DifferentialGeometry.Bundle.PartialMfderiv.Composition
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Geometry.Manifold.Algebra.SMul
import Mathlib.Geometry.Manifold.GroupLieAlgebra
import Mathlib.RepresentationTheory.Continuous.Basic

noncomputable section

open scoped Manifold

namespace ContRepresentation

variable {k : Type*} [NontriviallyNormedField k]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace k E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners k E H}
  {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace k W]

private theorem mvfderiv_apply (ρ : ContRepresentation k G W) {a : G}
    (hρ : MDifferentiableAt I 𝓘(k, W →L[k] W) (fun g => ρ g) a)
    (U : TangentSpace I a) (w : W) :
    mvfderiv I (fun g => ρ g w) a U = mvfderiv I (fun g => ρ g) a U w := by
  have h := congrArg (fun L => L U)
    (hρ.mvfderiv_clm_apply (mdifferentiableAt_const (c := w)))
  simpa only [mvfderiv_const, ContinuousLinearMap.comp_apply,
    zero_apply, map_zero, zero_add, add_apply, ContinuousLinearMap.apply_apply] using h

theorem mvfderiv_conj_apply (ρ : ContRepresentation k G W) {a : G}
    (hρ : MDifferentiableAt I 𝓘(k, W →L[k] W) (fun g => ρ g) a)
    (g : G) (U : TangentSpace I a) (w : W) :
    mvfderiv I (fun h => ρ (g * h * g⁻¹) w) a U =
      ρ g (mvfderiv I (fun h => ρ h) a U (ρ g⁻¹ w)) := by
  have h := congrArg (fun L => L U)
    ((mdifferentiableAt_const (c := ρ g)).mvfderiv_clm_apply
      (hρ.clm_apply (mdifferentiableAt_const (c := ρ g⁻¹ w))))
  have heq : (fun h : G => ρ g (ρ h (ρ g⁻¹ w))) =
      fun h => ρ (g * h * g⁻¹) w := by
    funext h
    rw [map_mul, map_mul]
    rfl
  rw [heq] at h
  simp only [mvfderiv_const, ContinuousLinearMap.comp_zero, add_zero,
    ContinuousLinearMap.comp_apply, ρ.mvfderiv_apply hρ] at h
  exact h

theorem mdifferentiable_of_mdifferentiableAt [ContMDiffMul I 1 G] (ρ : ContRepresentation k G W) {a : G}
    (hρ : MDifferentiableAt I 𝓘(k, W →L[k] W) (fun g => ρ g) a) :
    MDifferentiable I 𝓘(k, W →L[k] W) (fun g => ρ g) := by
  intro b
  have hρ' : MDifferentiableAt I 𝓘(k, W →L[k] W) (fun g => ρ g)
      ((a * b⁻¹) * b) := by
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using hρ
  have hc : MDifferentiableAt I 𝓘(k, W →L[k] W)
      (fun x => ρ ((a * b⁻¹) * x)) b :=
    hρ'.comp b (mdifferentiableAt_mul_left (I := I))
  have hd := ((ContinuousLinearMap.compL k W W W (ρ (b * a⁻¹))).mdifferentiableAt).comp b hc
  apply hd.congr_of_eventuallyEq
  apply Filter.Eventually.of_forall
  intro x
  change ρ x = ρ (b * a⁻¹) * ρ ((a * b⁻¹) * x)
  rw [← map_mul]
  congr 1
  group

theorem mvfderiv_inv_apply [LieGroup I 1 G] (ρ : ContRepresentation k G W) {a : G}
    (hρ : MDifferentiableAt I 𝓘(k, W →L[k] W) (fun g => ρ g) a)
    (U : TangentSpace I a) (w : W) :
    mvfderiv I (fun g => ρ g⁻¹ w) a U =
      -(ρ a⁻¹ (mvfderiv I (fun g => ρ g) a U (ρ a⁻¹ w))) := by
  have hi : MDifferentiableAt I 𝓘(k, W →L[k] W) (fun g => ρ g⁻¹) a :=
    (ρ.mdifferentiable_of_mdifferentiableAt hρ a⁻¹).comp a
      ((contMDiffAt_id.inv (n := 1)).mdifferentiableAt (by simp))
  have hv := hi.clm_apply (mdifferentiableAt_const (c := w))
  have hd := congrArg (fun L => L U) (hρ.mvfderiv_clm_apply hv)
  have heq : (fun g : G => ρ g (ρ g⁻¹ w)) = fun _ => w := by
    funext g
    rw [← mul_apply_eq_comp, ← map_mul, mul_inv_cancel, map_one]
    rfl
  rw [heq] at hd
  simp only [mvfderiv_const, zero_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.apply_apply, add_apply] at hd
  have hh := congrArg (ρ a⁻¹) hd
  rw [map_zero, map_add] at hh
  have heq' : ρ a⁻¹ (ρ a (mvfderiv I (fun g => ρ g⁻¹ w) a U)) =
      mvfderiv I (fun g => ρ g⁻¹ w) a U := by
    rw [← mul_apply_eq_comp, ← map_mul, inv_mul_cancel, map_one]
    rfl
  rw [heq'] at hh
  exact eq_neg_of_add_eq_zero_left hh.symm

theorem mvfderiv_inv_apply_one [LieGroup I 1 G] (ρ : ContRepresentation k G W)
    (hρ : MDifferentiableAt I 𝓘(k, W →L[k] W) (fun g => ρ g) 1)
    (U : GroupLieAlgebra I G) (w : W) :
    mvfderiv I (fun g => ρ g⁻¹ w) 1 U =
      -(mvfderiv I (fun g => ρ g) 1 U w) := by
  simpa only [inv_one, map_one, one_apply_eq_self] using
    ρ.mvfderiv_inv_apply hρ U w

theorem mvfderiv_conj_one_apply [ContMDiffMul I 1 G] (ρ : ContRepresentation k G W)
    (hρ : MDifferentiableAt I 𝓘(k, W →L[k] W) (fun g => ρ g) 1)
    (g : G) (U : GroupLieAlgebra I G) (w : W) :
    mvfderiv I (fun h => ρ h) 1
        (mfderiv I I (fun h => g * h * g⁻¹) 1 U) w =
      ρ g (mvfderiv I (fun h => ρ h) 1 U (ρ g⁻¹ w)) := by
  have hg : MDifferentiableAt I I (fun h => g * h * g⁻¹) 1 :=
    ((contMDiffAt_const.mul contMDiffAt_id).mul contMDiffAt_const (n := 1)).mdifferentiableAt
      (by simp)
  have hρ' : MDifferentiableAt I 𝓘(k, W) (fun h => ρ h w) (g * 1 * g⁻¹) := by
    simpa only [mul_one, mul_inv_cancel] using
      hρ.clm_apply (mdifferentiableAt_const (c := w))
  have h := MDifferentiableAt.mvfderiv_comp_apply
    (f := fun h => g * h * g⁻¹) (g := fun h => ρ h w) (x := (1 : G)) hρ' hg U
  have he : mvfderiv I (fun h => ρ h w) (g * 1 * g⁻¹) =
      mvfderiv I (fun h => ρ h w) 1 := by
    unfold TangentSpace
    rw [mul_one, mul_inv_cancel]
  have hv := congrArg (fun L => L (mfderiv I I (fun h => g * h * g⁻¹) 1 U)) he
  have ha := ρ.mvfderiv_apply hρ (mfderiv I I (fun h => g * h * g⁻¹) 1 U) w
  exact (h.trans (hv.trans ha)).symm.trans (ρ.mvfderiv_conj_apply hρ g U w)

section Orthogonal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
  {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]

theorem inner_mvfderiv_one (ρ : ContRepresentation ℝ G W)
    (hρ : MDifferentiableAt I 𝓘(ℝ, W →L[ℝ] W) (fun g => ρ g) 1)
    (horth : ∀ g v w, inner ℝ (ρ g v) (ρ g w) = inner ℝ v w)
    (U : GroupLieAlgebra I G) (v w : W) :
    inner ℝ (mvfderiv I (fun g => ρ g) 1 U v) w +
      inner ℝ v (mvfderiv I (fun g => ρ g) 1 U w) = 0 := by
  let L : W →L[ℝ] W →L[ℝ] ℝ := innerSL ℝ
  have hv := hρ.clm_apply (mdifferentiableAt_const (c := v))
  have hw := hρ.clm_apply (mdifferentiableAt_const (c := w))
  have hA := (mdifferentiableAt_const (c := L)).clm_apply hv
  have hd := congrArg (fun L => L U) (hA.mvfderiv_clm_apply hw)
  have hD := congrArg (fun L => L U)
    ((mdifferentiableAt_const (c := L)).mvfderiv_clm_apply hv)
  simp only [mvfderiv_const, ContinuousLinearMap.comp_zero, add_zero,
    ContinuousLinearMap.comp_apply] at hD
  have heq : (fun g => L (ρ g v) (ρ g w)) = fun _ : G => inner ℝ v w := by
    funext g
    exact horth g v w
  rw [heq] at hd
  simp only [mvfderiv_const, zero_apply, add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.apply_apply, map_one, one_apply_eq_self, hD] at hd
  rw [ρ.mvfderiv_apply hρ U v, ρ.mvfderiv_apply hρ U w] at hd
  change 0 = inner ℝ v (mvfderiv I (fun g => ρ g) 1 U w) +
    inner ℝ (mvfderiv I (fun g => ρ g) 1 U v) w at hd
  exact (add_comm _ _).trans hd.symm

variable [CompleteSpace W]

theorem mvfderiv_one_mem_skewAdjoint (ρ : ContRepresentation ℝ G W)
    (hρ : MDifferentiableAt I 𝓘(ℝ, W →L[ℝ] W) (fun g => ρ g) 1)
    (horth : ∀ g v w, inner ℝ (ρ g v) (ρ g w) = inner ℝ v w)
    (U : GroupLieAlgebra I G) :
    mvfderiv I (fun g => ρ g) 1 U ∈ skewAdjoint.submodule ℝ (W →L[ℝ] W) := by
  change star (mvfderiv I (fun g => ρ g) 1 U) = -mvfderiv I (fun g => ρ g) 1 U
  apply ContinuousLinearMap.ext
  intro w
  apply ext_inner_left ℝ
  intro v
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right,
    neg_apply, inner_neg_right]
  exact eq_neg_of_add_eq_zero_left (ρ.inner_mvfderiv_one hρ horth U v w)

end Orthogonal

section Equivariant

variable {k : Type*} [NontriviallyNormedField k]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace k E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners k E H}
  {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace k W]
  {EP : Type*} [NormedAddCommGroup EP] [NormedSpace k EP]
  {HP : Type*} [TopologicalSpace HP] {IP : ModelWithCorners k EP HP}
  {P : Type*} [TopologicalSpace P] [ChartedSpace HP P] [MulAction G P]
  [ContMDiffSMul I IP 1 G P]

theorem mvfderiv_equivariant_fundamental (ρ : ContRepresentation k G W)
    (hρ : MDifferentiableAt I 𝓘(k, W →L[k] W) (fun g => ρ g) 1)
    {f : P → W} (heq : ∀ g p, f (g • p) = ρ g (f p)) {p : P}
    (hf : MDifferentiableAt IP 𝓘(k, W) f p) (U : GroupLieAlgebra I G) :
    mvfderiv IP f p (mfderiv I IP (fun g : G => g • p) 1 U) =
      mvfderiv I (fun g => ρ g) 1 U (f p) := by
  have hf' : MDifferentiableAt IP 𝓘(k, W) f ((1 : G) • p) := by
    simpa only [one_smul] using hf
  have hg : MDifferentiableAt I IP (fun g : G => g • p) 1 :=
    ((contMDiffAt_id.smul (contMDiffAt_const (c := p))) :
      ContMDiffAt I IP 1 (fun g : G => g • p) 1).mdifferentiableAt (by simp)
  have h := MDifferentiableAt.mvfderiv_comp_apply
    (f := fun g : G => g • p) (g := f) (x := (1 : G)) hf' hg U
  have hp : mvfderiv IP f ((1 : G) • p) = mvfderiv IP f p := by
    unfold TangentSpace
    rw [one_smul]
  have hh := congrArg (fun L => L (mfderiv I IP (fun g : G => g • p) 1 U)) hp
  have hh' : (f ∘ fun g : G => g • p) = fun g => ρ g (f p) := by
    funext g
    exact heq g p
  rw [hh', ρ.mvfderiv_apply hρ U (f p)] at h
  exact (h.trans hh).symm

end Equivariant

end ContRepresentation
