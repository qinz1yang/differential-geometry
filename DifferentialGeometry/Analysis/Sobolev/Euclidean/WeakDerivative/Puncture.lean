import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.HalfSpaceContinuousBoundary
import DifferentialGeometry.Analysis.Integration.Measure.EuclideanPlane
import DifferentialGeometry.Analysis.Calculus.Trace
import DifferentialGeometry.Analysis.Calculus.ContDiff.Support
import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative.ClassicalDivergence
import Mathlib.MeasureTheory.Group.Integral

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace DifferentialGeometry.Analysis

private def punctureReflection : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ) :=
  (ContinuousLinearEquiv.refl ℝ ℝ).prodCongr
    (LinearIsometryEquiv.neg ℝ (E := ℝ)).toContinuousLinearEquiv

private theorem punctureReflection_apply (p : ℝ × ℝ) :
    punctureReflection p = (p.1, -p.2) := rfl

private theorem punctureReflection_symm_apply (p : ℝ × ℝ) :
    punctureReflection.symm p = (p.1, -p.2) := rfl

private theorem punctureReflection_measurePreserving :
    MeasurePreserving punctureReflection volume volume := by
  rw [Measure.volume_eq_prod ℝ ℝ]
  exact (MeasurePreserving.id volume).prod (Measure.measurePreserving_neg volume)


private theorem puncture_integral_eq_zero_prod
    {β : ℝ × ℝ → ℝ × ℝ} {D : ℝ × ℝ → ℝ}
    (hβ : Continuous β) (hβc : HasCompactSupport β)
    (hβdiff : ContDiffOn ℝ 1 β ({0}ᶜ : Set (ℝ × ℝ)))
    (hD : Continuous D) (hDc : HasCompactSupport D)
    (hdiv : ∀ p : ℝ × ℝ, p ≠ 0 →
      D p = LinearMap.trace ℝ (ℝ × ℝ) (fderiv ℝ β p).toLinearMap) :
    (∫ p, D p) = 0 := by
  let U : Set (ℝ × ℝ) := univ ×ˢ Ioi 0
  let L : Set (ℝ × ℝ) := univ ×ˢ Iio 0
  have hUne (p : ℝ × ℝ) (hp : p ∈ U) : p ≠ 0 := by
    intro he
    have hs : 0 < p.2 := hp.2
    simp [he] at hs
  have hupper := integral_divergence_eq_neg_boundary_of_continuous_extension β D
    hβ.continuousOn (hβdiff.mono fun p hp => hUne p hp) hβc hD.continuousOn
    (fun p hp => hdiv p (hUne p ⟨mem_univ _, hp⟩))
  let r := punctureReflection
  let γ := r ∘ β ∘ r.symm
  have hγ : Continuous γ := r.continuous.comp (hβ.comp r.symm.continuous)
  have hγc : HasCompactSupport γ :=
    (hβc.comp_isClosedEmbedding r.symm.toHomeomorph.isClosedEmbedding).comp_left r.map_zero
  have hγdiff : ContDiffOn ℝ 1 γ U := by
    apply r.contDiff.comp_contDiffOn
    apply hβdiff.comp r.symm.contDiff.contDiffOn
    intro p hp
    change r.symm p ≠ 0
    intro he
    have he' := congrArg r he
    exact hUne p hp (by simpa using he')
  have hlower := integral_divergence_eq_neg_boundary_of_continuous_extension γ
    (D ∘ r.symm) hγ.continuousOn hγdiff hγc
    (hD.comp r.symm.continuous).continuousOn (by
      intro p hp
      rw [trace_fderiv_conj]
      apply hdiv
      intro he
      have he' := congrArg r he
      exact hUne p ⟨mem_univ _, hp⟩ (by simpa using he'))
  have hpre : r ⁻¹' L = U := by
    ext p
    simp [r, L, U, punctureReflection_apply]
  have hchange : (∫ p in U, D (r.symm p)) = ∫ p in L, D p := by
    have he := punctureReflection_measurePreserving.setIntegral_preimage_emb
      r.toHomeomorph.toMeasurableEquiv.measurableEmbedding D L
    rw [hpre] at he
    exact he
  have hlower' : (∫ p in L, D p) = ∫ s : ℝ, (β (s, 0)).2 := by
    rw [← hchange]
    simpa only [γ, Function.comp_apply, r, punctureReflection_apply,
      punctureReflection_symm_apply, neg_zero, integral_neg, neg_neg] using hlower
  have hI : Integrable D := hD.integrable_of_hasCompactSupport hDc
  have hmeas : MeasurableSet U := (isOpen_univ.prod isOpen_Ioi).measurableSet
  have haxis : ∀ᵐ p : ℝ × ℝ ∂volume, p.2 ≠ 0 := by
    rw [Measure.volume_eq_prod ℝ ℝ]
    apply (Measure.ae_prod_iff_ae_ae
      (isOpen_ne_fun continuous_snd continuous_const).measurableSet).mpr
    exact Filter.Eventually.of_forall fun _ => Measure.ae_ne volume 0
  have hcomplement : Uᶜ =ᵐ[volume] L := by
    filter_upwards [haxis] with p hp
    apply propext
    simp only [U, L, mem_compl_iff, mem_prod, mem_univ, true_and, mem_Ioi,
      mem_Iio, not_lt]
    exact le_iff_lt_or_eq.trans (or_iff_left hp)
  have hsum := integral_add_compl hmeas hI
  rw [setIntegral_congr_set hcomplement] at hsum
  rw [hupper, hlower'] at hsum
  linarith


private theorem puncture_integral_eq_zero_euclidean
    {a : EuclideanSpace ℝ (Fin 2)}
    {β : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    {D : EuclideanSpace ℝ (Fin 2) → ℝ}
    (hβ : Continuous β) (hβc : HasCompactSupport β)
    (hβdiff : ContDiffOn ℝ 1 β ({a}ᶜ : Set (EuclideanSpace ℝ (Fin 2))))
    (hD : Continuous D) (hDc : HasCompactSupport D)
    (hdiv : ∀ x, x ≠ a → D x = LinearMap.trace ℝ
      (EuclideanSpace ℝ (Fin 2)) (fderiv ℝ β x).toLinearMap) :
    (∫ x, D x) = 0 := by
  let e := euclideanPlaneProdEquiv
  let u := fun x => β (x + a)
  let d := fun x => D (x + a)
  let γ := e ∘ u ∘ e.symm
  have hu : Continuous u := hβ.comp (continuous_id.add continuous_const)
  have huc : HasCompactSupport u :=
    hβc.comp_isClosedEmbedding (Homeomorph.addRight a).isClosedEmbedding
  have huD : ContDiffOn ℝ 1 u ({0}ᶜ : Set (EuclideanSpace ℝ (Fin 2))) := by
    apply hβdiff.comp (contDiff_id.add contDiff_const).contDiffOn
    intro x hx
    change x + a ≠ a
    simpa using hx
  have hγ : Continuous γ := e.continuous.comp (hu.comp e.symm.continuous)
  have hγc : HasCompactSupport γ :=
    (huc.comp_isClosedEmbedding e.symm.toHomeomorph.isClosedEmbedding).comp_left e.map_zero
  have hγD : ContDiffOn ℝ 1 γ ({0}ᶜ : Set (ℝ × ℝ)) := by
    apply e.contDiff.comp_contDiffOn
    apply huD.comp e.symm.contDiff.contDiffOn
    intro p hp
    change e.symm p ≠ 0
    simpa using hp
  have hd : Continuous (d ∘ e.symm) :=
    (hD.comp (continuous_id.add continuous_const)).comp e.symm.continuous
  have hdc : HasCompactSupport (d ∘ e.symm) :=
    (hDc.comp_isClosedEmbedding (Homeomorph.addRight a).isClosedEmbedding).comp_isClosedEmbedding
      e.symm.toHomeomorph.isClosedEmbedding
  have hzero := puncture_integral_eq_zero_prod hγ hγc hγD hd hdc (by
    intro p hp
    rw [trace_fderiv_conj]
    change D (e.symm p + a) = LinearMap.trace ℝ
      (EuclideanSpace ℝ (Fin 2)) (fderiv ℝ (fun x => β (x + a)) (e.symm p)).toLinearMap
    rw [fderiv_comp_add_right]
    apply hdiv
    simpa using hp)
  have hmp : MeasurePreserving e.symm volume volume :=
    MeasurePreserving.symm e.toHomeomorph.toMeasurableEquiv measurePreserving_euclideanPlaneProdEquiv
  have he := hmp.integral_comp e.symm.toHomeomorph.toMeasurableEquiv.measurableEmbedding d
  change (∫ p, d (e.symm p)) = ∫ x, d x at he
  change (∫ p, d (e.symm p)) = 0 at hzero
  rw [he] at hzero
  simpa only [d, integral_add_right_eq_self] using hzero

end DifferentialGeometry.Analysis

namespace DeGiorgi

open DifferentialGeometry.Analysis

/-- A continuous planar flux with continuous classical divergence off one point has that
same weak divergence across the point. No derivative at the removed point is required. -/
theorem hasWeakDiv_of_continuous_divergence_off_point
    {Ω : Set (EuclideanSpace ℝ (Fin 2))} {a : EuclideanSpace ℝ (Fin 2)}
    {f : EuclideanSpace ℝ (Fin 2) → ℝ}
    {F : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    (hΩ : IsOpen Ω) (hf : ContinuousOn f Ω) (hF : ContinuousOn F Ω)
    (hFD : ContDiffOn ℝ 1 F (Ω \ {a}))
    (hdiv : ∀ x ∈ Ω, x ≠ a → (∑ i : Fin 2,
      fderiv ℝ (fun y => F y i) x (EuclideanSpace.single i 1)) = f x) :
    HasWeakDiv f F Ω := by
  intro φ hφ hφc hφs
  let β := fun x => φ x • F x
  let G := fun x => fderiv ℝ φ x (F x)
  let D := fun x => φ x * f x + G x
  have hβs : tsupport β ⊆ tsupport φ := tsupport_smul_subset_left φ F
  have hβ : Continuous β :=
    (hφ.continuous.continuousOn.smul hF).continuous_of_tsupport_subset hΩ (hβs.trans hφs)
  have hβc : HasCompactSupport β := hφc.smul_right
  have hβD : ContDiffOn ℝ 1 β ({a}ᶜ : Set (EuclideanSpace ℝ (Fin 2))) := by
    exact ContDiffOn.contDiffOn_of_tsupport_subset
      ((hφ.of_le (by simp)).contDiffOn.smul hFD) hΩ
      (fun x hx => hφs (hβs hx.1))
  have hGs : tsupport G ⊆ tsupport φ := by
    apply closure_minimal _ (isClosed_tsupport φ)
    intro x hx
    by_contra hnot
    exact hx (by simp [G, fderiv_of_notMem_tsupport ℝ hnot])
  have hGc : HasCompactSupport G :=
    hφc.of_isClosed_subset (isClosed_tsupport G) hGs
  have hG : Continuous G :=
    (((hφ.continuous_fderiv (by simp)).continuousOn).clm_apply hF).continuous_of_tsupport_subset
      hΩ (hGs.trans hφs)
  have hP : Continuous (fun x => φ x * f x) :=
    (hφ.continuous.continuousOn.mul hf).continuous_of_tsupport_subset hΩ
      (tsupport_mul_subset_left.trans hφs)
  have hD : Continuous D := hP.add hG
  have hDc : HasCompactSupport D := hφc.mul_right.add hGc
  have heq : ∀ x, x ≠ a → D x = LinearMap.trace ℝ
      (EuclideanSpace ℝ (Fin 2)) (fderiv ℝ β x).toLinearMap := by
    intro x hxa
    by_cases hx : x ∈ Ω
    · have hx' : x ∈ Ω \ {a} := ⟨hx, hxa⟩
      have hdiff := (hFD.contDiffAt ((hΩ.sdiff isClosed_singleton).mem_nhds hx')).differentiableAt_one
      have htrace : LinearMap.trace ℝ (EuclideanSpace ℝ (Fin 2))
          (fderiv ℝ F x).toLinearMap = f x := by
        have ht := trace_fderiv_eq_sum (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis hdiff
        calc
          _ = ∑ i : Fin 2, fderiv ℝ (fun y => F y i) x (EuclideanSpace.single i 1) := by
            simpa only [OrthonormalBasis.coe_toBasis,
              OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_apply,
              EuclideanSpace.basisFun_repr] using ht
          _ = f x := hdiv x hx hxa
      rw [show β = (fun y => φ y • F y) from rfl,
        fderiv_fun_smul (hφ.differentiable (by simp) x) hdiff]
      change D x = LinearMap.trace ℝ (EuclideanSpace ℝ (Fin 2))
        (φ x • (fderiv ℝ F x).toLinearMap + (fderiv ℝ φ x).toLinearMap.smulRight (F x))
      rw [map_add, map_smul, LinearMap.trace_smulRight, htrace]
      rfl
    · have hn : x ∉ tsupport φ := fun hs => hx (hφs hs)
      rw [fderiv_of_notMem_tsupport ℝ (fun hb => hn (hβs hb))]
      simp [D, G, image_eq_zero_of_notMem_tsupport hn, fderiv_of_notMem_tsupport ℝ hn]
  have hzero := puncture_integral_eq_zero_euclidean hβ hβc hβD hD hDc heq
  have hfi : Integrable (fun x => φ x * f x) := hP.integrable_of_hasCompactSupport hφc.mul_right
  have hGi : Integrable G := hG.integrable_of_hasCompactSupport hGc
  have hsum : (∫ x, φ x * f x) + (∫ x, G x) = 0 := by
    simpa only [D, integral_add hfi hGi] using hzero
  have hGsum (x : EuclideanSpace ℝ (Fin 2)) :
      (∑ i : Fin 2, F x i * fderiv ℝ φ x (EuclideanSpace.single i 1)) = G x := by
    have hh := congrArg (fderiv ℝ φ x)
      ((EuclideanSpace.basisFun (Fin 2) ℝ).sum_repr (F x))
    simpa only [G, map_sum, map_smul, smul_eq_mul, EuclideanSpace.basisFun_apply,
      EuclideanSpace.basisFun_repr] using hh
  simp_rw [hGsum]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx =>
    image_eq_zero_of_notMem_tsupport (fun hs => hx (hφs (hGs hs))))]
  have hright : (∫ x in Ω, f x * φ x) = ∫ x, φ x * f x := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
      rw [image_eq_zero_of_notMem_tsupport (fun hs => hx (hφs hs)), mul_zero])]
    simp only [mul_comm]
  rw [hright]
  linarith

/-- Filling one point preserves the actual weak divergence of a continuous planar flux. -/
theorem HasWeakDiv.of_remove_singleton
    {Ω : Set (EuclideanSpace ℝ (Fin 2))} {a : EuclideanSpace ℝ (Fin 2)}
    {f : EuclideanSpace ℝ (Fin 2) → ℝ}
    {F : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    (h : HasWeakDiv f F (Ω \ {a})) (hΩ : IsOpen Ω)
    (hf : ContinuousOn f Ω) (hF : ContinuousOn F Ω)
    (hFD : ContDiffOn ℝ 1 F (Ω \ {a})) : HasWeakDiv f F Ω := by
  apply hasWeakDiv_of_continuous_divergence_off_point hΩ hf hF hFD
  intro x hx hxa
  exact (h.eqOn_sum_fderiv (hΩ.sdiff isClosed_singleton) (hf.mono sdiff_subset)
    (fun i => (contDiff_piLp_apply (p := 2) (i := i)).comp_contDiffOn hFD) ⟨hx, hxa⟩).symm

/-- The standard complex coordinates preserve the actual two flux components when filling a
puncture. The divergence hypothesis is the literal `1`, `I` derivative sum, so no measure or
normalization factor enters the Euclidean weak equation. -/
theorem hasWeakDiv_of_complex_divergence_off_point
    {Ω : Set ℂ} {a : ℂ} {f : ℂ → ℝ} {P : ℂ → EuclideanSpace ℝ (Fin 2)}
    (hΩ : IsOpen Ω) (hf : ContinuousOn f Ω) (hP : ContinuousOn P Ω)
    (hPD : ContDiffOn ℝ 1 P (Ω \ {a}))
    (hdiv : ∀ z ∈ Ω, z ≠ a →
      fderiv ℝ (fun w => P w 0) z 1 +
        fderiv ℝ (fun w => P w 1) z Complex.I = f z) :
    HasWeakDiv (f ∘ Complex.orthonormalBasisOneI.repr.symm)
      (P ∘ Complex.orthonormalBasisOneI.repr.symm)
      (Complex.orthonormalBasisOneI.repr '' Ω) := by
  let e := Complex.orthonormalBasisOneI.repr.toContinuousLinearEquiv
  have hset : e '' Ω = e.symm ⁻¹' Ω := by
    ext x
    change (∃ z ∈ Ω, e z = x) ↔ e.symm x ∈ Ω
    constructor
    · rintro ⟨z, hz, rfl⟩
      simpa using hz
    · intro hx
      exact ⟨e.symm x, hx, e.apply_symm_apply x⟩
  change HasWeakDiv (f ∘ e.symm) (P ∘ e.symm) (e '' Ω)
  rw [hset]
  apply hasWeakDiv_of_continuous_divergence_off_point (a := e a)
    (hΩ.preimage e.symm.continuous)
    (hf.comp e.symm.continuous.continuousOn (fun _ hx => hx))
    (hP.comp e.symm.continuous.continuousOn (fun _ hx => hx))
  · apply hPD.comp e.symm.contDiff.contDiffOn
    intro x hx
    refine ⟨hx.1, ?_⟩
    change e.symm x ≠ a
    intro he
    exact hx.2 (by simpa using congrArg e he)
  · intro x hx hxa
    have hne : e.symm x ≠ a := by
      intro he
      exact hxa (by simpa using congrArg e he)
    have hzero : e.symm (EuclideanSpace.single 0 1) = 1 := by
      simp [e]
    have hone : e.symm (EuclideanSpace.single 1 1) = Complex.I := by
      simp [e]
    rw [Fin.sum_univ_two]
    change fderiv ℝ ((fun w => P w 0) ∘ e.symm) x (EuclideanSpace.single 0 1) +
      fderiv ℝ ((fun w => P w 1) ∘ e.symm) x (EuclideanSpace.single 1 1) = f (e.symm x)
    rw [e.symm.comp_right_fderiv, e.symm.comp_right_fderiv]
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      hzero, hone] using hdiv (e.symm x) hx hne

end DeGiorgi
