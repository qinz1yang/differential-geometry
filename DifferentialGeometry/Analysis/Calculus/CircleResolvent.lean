import DifferentialGeometry.Analysis.Integration.Integral.Circle
import DifferentialGeometry.Analysis.Calculus.IteratedDerivative.ResolventBounds
import Mathlib.Topology.ContinuousMap.Units

set_option autoImplicit false

noncomputable section

open Complex Metric
open scoped NNReal Topology

namespace ContinuousMap

private theorem ringInverse_apply {X A : Type*} [TopologicalSpace X]
    [NormedRing A] [CompleteSpace A] (f : C(X, A)) (hf : IsUnit f) (x : X) :
    Ring.inverse f x = Ring.inverse (f x) := by
  have hx := f.isUnit_iff_forall_isUnit.mp hf x
  have hi := congrArg (fun g : C(X, A) => g x) (Ring.inverse_mul_cancel f hf)
  change Ring.inverse f x * f x = 1 at hi
  simpa only [one_mul] using (Ring.eq_mul_inverse_iff_mul_eq _ 1 _ hx).mpr hi

end ContinuousMap

theorem isOpen_setOf_circle_subset_resolventSet {A : Type*}
    [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A] (c : ℂ) (r : ℝ) :
    IsOpen {a : A | sphere c |r| ⊆ resolventSet ℂ a} := by
  let Z : C(sphere c |r|, A) :=
    ⟨fun z => algebraMap ℂ A z, (continuous_algebraMap ℂ A).comp continuous_subtype_val⟩
  let K : A →L[ℂ] C(sphere c |r|, A) := ContinuousLinearMap.const ℂ _
  have heq : {a : A | sphere c |r| ⊆ resolventSet ℂ a} =
      (fun a => Z - K a) ⁻¹' {g : C(sphere c |r|, A) | IsUnit g} := by
    ext a
    change (∀ z, z ∈ sphere c |r| → IsUnit (algebraMap ℂ A z - a)) ↔ IsUnit (Z - K a)
    rw [ContinuousMap.isUnit_iff_forall_isUnit]
    exact ⟨fun h z => h z z.property, fun h z hz => h ⟨z, hz⟩⟩
  rw [heq]
  exact Units.isOpen.preimage (continuous_const.sub K.continuous)

variable {𝕜 A : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra 𝕜 ℂ]
  [NormedRing A] [NormedAlgebra ℂ A] [NormedAlgebra 𝕜 A]
  [IsScalarTower 𝕜 ℂ A] [CompleteSpace A]

theorem contDiffOn_circleIntegral_resolvent (c : ℂ) (r : ℝ) {n : WithTop ℕ∞} :
    ContDiffOn 𝕜 n (fun a : A => ∮ z in C(c, r), _root_.resolvent a z)
      {a : A | sphere c |r| ⊆ resolventSet ℂ a} := by
  let Z : C(sphere c |r|, A) :=
    ⟨fun z => algebraMap ℂ A z, (continuous_algebraMap ℂ A).comp continuous_subtype_val⟩
  let K : A →L[𝕜] C(sphere c |r|, A) := ContinuousLinearMap.const 𝕜 _
  have hg : ContDiff 𝕜 n (fun a => Z - K a) := contDiff_const.sub K.contDiff
  have hu (a : A) (ha : sphere c |r| ⊆ resolventSet ℂ a) : IsUnit (Z - K a) := by
    apply (ContinuousMap.isUnit_iff_forall_isUnit _).mpr
    intro z
    exact ha z.property
  have hi : ContDiffOn 𝕜 n (fun a => Ring.inverse (Z - K a))
      {a : A | sphere c |r| ⊆ resolventSet ℂ a} := by
    intro a ha
    have hd := contDiffAt_ringInverse 𝕜 (n := n) (hu a ha).unit
    rw [(hu a ha).unit_spec] at hd
    exact hd.comp_contDiffWithinAt a hg.contDiffWithinAt
  have hj := ((ContinuousMap.circleIntegralCLM (E := A) c r).restrictScalars 𝕜).contDiff.comp_contDiffOn hi
  apply hj.congr
  intro a ha
  symm
  change (∫ θ : ℝ in 0..2 * Real.pi, deriv (circleMap c r) θ •
    (Ring.inverse (Z - K a)) ⟨circleMap c r θ, circleMap_mem_sphere' c r θ⟩) = _
  apply intervalIntegral.integral_congr
  intro θ _
  exact congrArg (deriv (circleMap c r) θ • ·)
    (ContinuousMap.ringInverse_apply (Z - K a) (hu a ha) _)

theorem ContDiffOn.circleIntegral_resolvent {E : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] {f : E → A} {s : Set E} {n : WithTop ℕ∞}
    (hf : ContDiffOn 𝕜 n f s) (c : ℂ) (r : ℝ)
    (hs : ∀ x ∈ s, sphere c |r| ⊆ resolventSet ℂ (f x)) :
    ContDiffOn 𝕜 n (fun x => ∮ z in C(c, r), _root_.resolvent (f x) z) s :=
  (contDiffOn_circleIntegral_resolvent c r).comp hf hs

theorem DifferentiableAt.norm_fderiv_normalized_circleIntegral_resolvent_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {f : E → A} {x : E} (hf : DifferentiableAt 𝕜 f x) (c : ℂ) (r : ℝ)
    (hc : sphere c |r| ⊆ resolventSet ℂ (f x)) (K : ℝ≥0)
    (hK : ∀ z ∈ sphere c |r|, ‖_root_.resolvent (f x) z‖ ≤ K) :
    ‖fderiv 𝕜 (fun y => (2 * ↑Real.pi * I : ℂ)⁻¹ •
      (∮ z in C(c, r), _root_.resolvent (f y) z)) x‖ ≤
      |r| * (K : ℝ) ^ 2 * ‖fderiv 𝕜 f x‖ := by
  let Z : C(sphere c |r|, A) :=
    ⟨fun z => algebraMap ℂ A z, (continuous_algebraMap ℂ A).comp continuous_subtype_val⟩
  let C : A →L[𝕜] C(sphere c |r|, A) := ContinuousLinearMap.const 𝕜 _
  let g : E → C(sphere c |r|, A) := fun y => C (f y) - Z
  let L : C(sphere c |r|, A) →L[𝕜] A :=
    (((2 * ↑Real.pi * I : ℂ)⁻¹) • ContinuousMap.circleIntegralCLM (E := A) c r).restrictScalars 𝕜
  have happ (a : A) (z : sphere c |r|) : (Z - C a) z = algebraMap ℂ A z - a := rfl
  have hunit (y : E) (hy : sphere c |r| ⊆ resolventSet ℂ (f y)) : IsUnit (Z - C (f y)) := by
    apply (ContinuousMap.isUnit_iff_forall_isUnit _).mpr
    intro z
    exact hy z.property
  have hz : (0 : ℂ) ∈ resolventSet ℂ (g x) := by
    change IsUnit (algebraMap ℂ C(sphere c |r|, A) 0 - (C (f x) - Z))
    simpa only [map_zero, zero_sub, neg_sub] using hunit x hc
  have hdg : HasFDerivAt g (C.comp (fderiv 𝕜 f x)) x :=
    (C.hasFDerivAt.comp x hf.hasFDerivAt).sub_const Z
  have hd := L.hasFDerivAt.comp x (hdg.resolvent hz)
  have heq : (fun y => (2 * ↑Real.pi * I : ℂ)⁻¹ • (∮ z in C(c, r), _root_.resolvent (f y) z))
      =ᶠ[𝓝 x] (fun y => L (_root_.resolvent (g y) (0 : ℂ))) := by
    have hn := hf.continuousAt.eventually
      ((isOpen_setOf_circle_subset_resolventSet c r).mem_nhds hc)
    filter_upwards [hn] with y hy
    change (2 * ↑Real.pi * I : ℂ)⁻¹ • (∮ z in C(c, r), _root_.resolvent (f y) z) =
      (2 * ↑Real.pi * I : ℂ)⁻¹ • (∫ θ : ℝ in 0..2 * Real.pi, deriv (circleMap c r) θ •
        (_root_.resolvent (g y) (0 : ℂ)) ⟨circleMap c r θ, circleMap_mem_sphere' c r θ⟩)
    congr 1
    apply intervalIntegral.integral_congr
    intro θ _
    have hh := ContinuousMap.ringInverse_apply (Z - C (f y)) (hunit y hy)
      ⟨circleMap c r θ, circleMap_mem_sphere' c r θ⟩
    rw [happ] at hh
    simpa only [_root_.resolvent, map_zero, zero_sub, g, neg_sub] using
      congrArg (deriv (circleMap c r) θ • ·) hh.symm
  have hnormC : ‖C‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro a
    apply (ContinuousMap.norm_le _ (by positivity)).mpr
    intro z
    simp [C]
  have hnormR : ‖_root_.resolvent (g x) (0 : ℂ)‖ ≤ (K : ℝ) := by
    apply (ContinuousMap.norm_le _ K.coe_nonneg).mpr
    intro z
    have he : _root_.resolvent (g x) (0 : ℂ) z = _root_.resolvent (f x) (z : ℂ) := by
      have hh := ContinuousMap.ringInverse_apply (Z - C (f x)) (hunit x hc) z
      rw [happ] at hh
      simpa only [_root_.resolvent, map_zero, zero_sub, g, neg_sub] using hh
    rw [he]
    exact hK z z.property
  have hnormL : ‖L‖ ≤ |r| := by
    rw [show ‖L‖ = ‖(2 * ↑Real.pi * I : ℂ)⁻¹‖ * ‖ContinuousMap.circleIntegralCLM (E := A) c r‖ by
      simp only [L, ContinuousLinearMap.norm_restrictScalars, norm_smul]]
    have hi : ‖(2 * ↑Real.pi * I : ℂ)⁻¹‖ = (2 * Real.pi)⁻¹ := by simp
    rw [hi]
    calc
      _ ≤ (2 * Real.pi)⁻¹ * (2 * Real.pi * |r|) :=
        mul_le_mul_of_nonneg_left (ContinuousMap.norm_circleIntegralCLM_le c r) (by positivity)
      _ = |r| := by rw [← mul_assoc, inv_mul_cancel₀ Real.two_pi_pos.ne', one_mul]
  rw [(hd.congr_of_eventuallyEq heq).fderiv]
  calc
    _ ≤ ‖L‖ * (‖_root_.resolvent (g x) (0 : ℂ)‖ ^ 2 * ‖C.comp (fderiv 𝕜 f x)‖) := by
      apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
      exact mul_le_mul_of_nonneg_right
        (by simpa only [pow_two] using (ContinuousLinearMap.opNorm_mulLeftRight_apply_apply_le
          𝕜 C(sphere c |r|, A) (_root_.resolvent (g x) (0 : ℂ)) (_root_.resolvent (g x) (0 : ℂ)))) (norm_nonneg _)
    _ ≤ |r| * ((K : ℝ) ^ 2 * (1 * ‖fderiv 𝕜 f x‖)) := by
      gcongr
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_right hnormC (norm_nonneg _))
    _ = |r| * (K : ℝ) ^ 2 * ‖fderiv 𝕜 f x‖ := by ring

theorem ContDiffOn.norm_iteratedFDeriv_normalized_circleIntegral_resolvent_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {U : Set E} (hU : IsOpen U) {f : E → A} {m : ℕ} (hf : ContDiffOn 𝕜 m f U)
    (c : ℂ) (r : ℝ) (hc : ∀ y ∈ U, sphere c |r| ⊆ resolventSet ℂ (f y))
    {x : E} (hx : x ∈ U) {δ σ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hσ : 0 ≤ σ)
    (K B : ℝ≥0) (hK : ∀ z ∈ sphere c |r|, ‖_root_.resolvent (f x) z‖ ≤ K)
    (hD : ∀ j, 1 ≤ j → j ≤ m → ‖iteratedFDeriv 𝕜 j f x‖ ≤ δ * B * σ ^ j) :
    ∀ n, 1 ≤ n → n ≤ m →
      ‖iteratedFDeriv 𝕜 n (fun y => (2 * ↑Real.pi * I : ℂ)⁻¹ •
        (∮ z in C(c, r), _root_.resolvent (f y) z)) x‖ ≤
        |r| * δ * resolventDerivativeBound K B n * σ ^ n := by
  let Z : C(sphere c |r|, A) :=
    ⟨fun z => algebraMap ℂ A z, (continuous_algebraMap ℂ A).comp continuous_subtype_val⟩
  let C : A →L[𝕜] C(sphere c |r|, A) := ContinuousLinearMap.const 𝕜 _
  let g : E → C(sphere c |r|, A) := fun y => C (f y) - Z
  let L : C(sphere c |r|, A) →L[𝕜] A :=
    (((2 * ↑Real.pi * I : ℂ)⁻¹) • ContinuousMap.circleIntegralCLM (E := A) c r).restrictScalars 𝕜
  have happ (a : A) (z : sphere c |r|) : (Z - C a) z = algebraMap ℂ A z - a := rfl
  have hunit (y : E) (hy : y ∈ U) : IsUnit (Z - C (f y)) := by
    apply (ContinuousMap.isUnit_iff_forall_isUnit _).mpr
    intro z
    exact hc y hy z.property
  have hz (y : E) (hy : y ∈ U) : (0 : ℂ) ∈ resolventSet ℂ (g y) := by
    change IsUnit (algebraMap ℂ C(sphere c |r|, A) 0 - (C (f y) - Z))
    simpa only [map_zero, zero_sub, neg_sub] using hunit y hy
  have hg : ContDiffOn 𝕜 m g U := (hf.continuousLinearMap_comp C).sub contDiffOn_const
  have heq : Set.EqOn (fun y => (2 * ↑Real.pi * I : ℂ)⁻¹ •
      (∮ z in C(c, r), _root_.resolvent (f y) z))
      (fun y => L (_root_.resolvent (g y) (0 : ℂ))) U := by
    intro y hy
    change (2 * ↑Real.pi * I : ℂ)⁻¹ • (∮ z in C(c, r), _root_.resolvent (f y) z) =
      (2 * ↑Real.pi * I : ℂ)⁻¹ • (∫ θ : ℝ in 0..2 * Real.pi, deriv (circleMap c r) θ •
        (_root_.resolvent (g y) (0 : ℂ)) ⟨circleMap c r θ, circleMap_mem_sphere' c r θ⟩)
    congr 1
    apply intervalIntegral.integral_congr
    intro θ _
    have hh := ContinuousMap.ringInverse_apply (Z - C (f y)) (hunit y hy)
      ⟨circleMap c r θ, circleMap_mem_sphere' c r θ⟩
    rw [happ] at hh
    simpa only [_root_.resolvent, map_zero, zero_sub, g, neg_sub] using
      congrArg (deriv (circleMap c r) θ • ·) hh.symm
  have hnormC : ‖C‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro a
    apply (ContinuousMap.norm_le _ (by positivity)).mpr
    intro z
    simp [C]
  have hnormR : ‖_root_.resolvent (g x) (0 : ℂ)‖ ≤ (K : ℝ) := by
    apply (ContinuousMap.norm_le _ K.coe_nonneg).mpr
    intro z
    have he : _root_.resolvent (g x) (0 : ℂ) z = _root_.resolvent (f x) (z : ℂ) := by
      have hh := ContinuousMap.ringInverse_apply (Z - C (f x)) (hunit x hx) z
      rw [happ] at hh
      simpa only [_root_.resolvent, map_zero, zero_sub, g, neg_sub] using hh
    rw [he]
    exact hK z z.property
  have hnormL : ‖L‖ ≤ |r| := by
    rw [show ‖L‖ = ‖(2 * ↑Real.pi * I : ℂ)⁻¹‖ * ‖ContinuousMap.circleIntegralCLM (E := A) c r‖ by
      simp only [L, ContinuousLinearMap.norm_restrictScalars, norm_smul]]
    have hi : ‖(2 * ↑Real.pi * I : ℂ)⁻¹‖ = (2 * Real.pi)⁻¹ := by simp
    rw [hi]
    calc
      _ ≤ (2 * Real.pi)⁻¹ * (2 * Real.pi * |r|) :=
        mul_le_mul_of_nonneg_left (ContinuousMap.norm_circleIntegralCLM_le c r) (by positivity)
      _ = |r| := by rw [← mul_assoc, inv_mul_cancel₀ Real.two_pi_pos.ne', one_mul]
  have hdg (j : ℕ) (hj : 1 ≤ j) (hjm : j ≤ m) :
      ‖iteratedFDeriv 𝕜 j g x‖ ≤ δ * B * σ ^ j := by
    have hfj : ContDiffAt 𝕜 j f x :=
      ((hf x hx).contDiffAt (hU.mem_nhds hx)).of_le (by exact_mod_cast hjm)
    change ‖iteratedFDeriv 𝕜 j ((C ∘ f) - fun _ => Z) x‖ ≤ _
    rw [iteratedFDeriv_sub_apply (hfj.continuousLinearMap_comp C) contDiffAt_const,
      iteratedFDeriv_const_of_ne (by omega), Pi.zero_apply, sub_zero]
    apply (C.norm_iteratedFDeriv_comp_left hfj le_rfl).trans
    calc
      _ ≤ 1 * ‖iteratedFDeriv 𝕜 j f x‖ :=
        mul_le_mul_of_nonneg_right hnormC (norm_nonneg _)
      _ ≤ δ * B * σ ^ j := by simpa only [one_mul] using hD j hj hjm
  intro n hn hnm
  rw [← iteratedFDerivWithin_of_isOpen n hU hx, iteratedFDerivWithin_congr heq hx n,
    iteratedFDerivWithin_of_isOpen n hU hx]
  apply (L.norm_iteratedFDeriv_comp_left
    (((hg.resolvent hz) x hx).contDiffAt (hU.mem_nhds hx)) (by exact_mod_cast hnm)).trans
  calc
    _ ≤ |r| * (δ * resolventDerivativeBound K B n * σ ^ n) := by
      gcongr
      exact norm_iteratedFDeriv_resolvent_le_of_small_derivatives hU hg hz hx
        hδ hδ1 hσ K B hnormR hdg n hn hnm
    _ = |r| * δ * resolventDerivativeBound K B n * σ ^ n := by ring
