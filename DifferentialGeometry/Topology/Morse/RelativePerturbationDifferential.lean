import DifferentialGeometry.Topology.Morse.RelativePerturbationFamily
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.Normed.Ring.Units

set_option autoImplicit false
noncomputable section
open Set Function Filter
open scoped Manifold ContDiff Topology BigOperators
namespace Poincare.Morse
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {n : ℕ}

private theorem isOpen_surjective_clm
    {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B] : IsOpen {L : A →L[ℝ] B | Surjective L} := by
  let : CompleteSpace B := FiniteDimensional.complete ℝ B
  apply isOpen_iff_mem_nhds.mpr
  intro L hL
  obtain ⟨r,hr⟩ := L.toLinearMap.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hL)
  let R : B →L[ℝ] A := r.toContinuousLinearMap
  have hLR : L.comp R = ContinuousLinearMap.id ℝ B := by
    ext x
    exact DFunLike.congr_fun hr x
  have ho : IsOpen {T : A →L[ℝ] B | IsUnit (T.comp R)} :=
    Units.isOpen.preimage (show Continuous (fun T : A →L[ℝ] B => T.comp R) from
      continuous_id.clm_comp continuous_const)
  have hh : {T : A →L[ℝ] B | IsUnit (T.comp R)} ∈ nhds L :=
    ho.mem_nhds (by change IsUnit (L.comp R); rw [hLR]; exact isUnit_one)
  apply Filter.mem_of_superset hh
  intro T hT
  exact Surjective.of_comp (show Surjective (T ∘ R) from
    (ContinuousLinearMap.isUnit_iff_bijective.mp hT).2)


def perturbationDifferential (f : E → ℝ) (φ : Fin n → E → ℝ)
    (q : (Fin n → ℝ) × E) : E →L[ℝ] ℝ := fderiv ℝ (finitePerturbation f φ q.1) q.2


theorem perturbationDifferential_eq {f : E → ℝ} {φ : Fin n → E → ℝ} {q : (Fin n → ℝ) × E}
    (hf : DifferentiableAt ℝ f q.2) (hφ : ∀ i, DifferentiableAt ℝ (φ i) q.2) :
    perturbationDifferential f φ q = fderiv ℝ f q.2 + ∑ i, q.1 i • fderiv ℝ (φ i) q.2 := by
  simpa only [mfderiv_eq_fderiv, parameterDifferential_apply, perturbationDifferential] using
    mfderiv_finitePerturbation (I := 𝓘(ℝ, E)) hf.mdifferentiableAt
      (fun i => (hφ i).mdifferentiableAt) q.1


theorem contDiff_perturbationDifferential {f : E → ℝ} {φ : Fin n → E → ℝ}
    (hf : ContDiff ℝ ∞ f) (hφ : ∀ i, ContDiff ℝ ∞ (φ i)) :
    ContDiff ℝ ∞ (perturbationDifferential f φ) := by
  have heq : perturbationDifferential f φ = fun q : (Fin n → ℝ) × E =>
      fderiv ℝ f q.2 + ∑ i, q.1 i • fderiv ℝ (φ i) q.2 := by
    funext q
    exact perturbationDifferential_eq (hf.differentiable (by simp) q.2)
      (fun i => (hφ i).differentiable (by simp) q.2)
  rw [heq]
  apply ((contDiff_infty_iff_fderiv.mp hf).2.comp contDiff_snd).add
  apply ContDiff.sum
  intro i _
  exact ((contDiff_apply ℝ ℝ i).comp contDiff_fst).smul
    ((contDiff_infty_iff_fderiv.mp (hφ i)).2.comp contDiff_snd)


theorem hasFDerivAt_perturbationDifferential_parameter {f : E → ℝ} {φ : Fin n → E → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f x) (hφ : ∀ i, DifferentiableAt ℝ (φ i) x) (a : Fin n → ℝ) :
    HasFDerivAt (fun p => perturbationDifferential f φ (p,x))
      (parameterDifferential (I := 𝓘(ℝ, E)) φ x) a := by
  simpa only [mfderiv_eq_fderiv, perturbationDifferential] using
    hasFDerivAt_mfderiv_finitePerturbation (I := 𝓘(ℝ, E)) hf.mdifferentiableAt
      (fun i => (hφ i).mdifferentiableAt) a


theorem surjective_fderiv_perturbationDifferential {f : E → ℝ} {φ : Fin n → E → ℝ}
    (hf : ContDiff ℝ ∞ f) (hφ : ∀ i, ContDiff ℝ ∞ (φ i)) (q : (Fin n → ℝ) × E)
    (hreg : Surjective (parameterDifferential (I := 𝓘(ℝ, E)) φ q.2)) :
    Surjective (fderiv ℝ (perturbationDifferential f φ) q) := by
  have hd := ((contDiff_perturbationDifferential hf hφ).differentiable (by simp) q).hasFDerivAt
  have hh := hd.comp q.1 (hasFDerivAt_prodMk_left (𝕜 := ℝ) q.1 q.2)
  have heq := hh.unique (hasFDerivAt_perturbationDifferential_parameter
    (hf.differentiable (by simp) q.2) (fun i => (hφ i).differentiable (by simp) q.2) q.1)
  rw [← heq] at hreg
  exact Surjective.of_comp (show Surjective ((fderiv ℝ (perturbationDifferential f φ) q) ∘
    (ContinuousLinearMap.inl ℝ (Fin n → ℝ) E)) from hreg)


theorem continuous_parameterDifferential {φ : Fin n → E → ℝ}
    (hφ : ∀ i, ContDiff ℝ ∞ (φ i)) :
    Continuous (parameterDifferential (I := 𝓘(ℝ, E)) φ) := by
  apply continuous_clm_apply.mpr
  intro a
  simp only [parameterDifferential_apply, mfderiv_eq_fderiv]
  exact continuous_finsetSum _ fun i _ => ((hφ i).continuous_fderiv (by simp)).const_smul (a i)


theorem isOpen_regularPerturbationBase [FiniteDimensional ℝ E] {φ : Fin n → E → ℝ}
    (hφ : ∀ i, ContDiff ℝ ∞ (φ i)) :
    IsOpen {x : E | Surjective (parameterDifferential (I := 𝓘(ℝ, E)) φ x)} :=
  isOpen_surjective_clm.preimage (continuous_parameterDifferential hφ)

section FiniteDimension
variable [FiniteDimensional ℝ E]


theorem perturbationZero_finrank :
    Module.finrank ℝ ((Fin n → ℝ) × E) - Module.finrank ℝ (E →L[ℝ] ℝ) = n := by
  rw [← (LinearMap.toContinuousLinearMap : (E →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (E →L[ℝ] ℝ)).finrank_eq]
  simp [Module.finrank_prod, Subspace.dual_finrank_eq]


def regularPerturbationDomain (φ : Fin n → E → ℝ) : Set ((Fin n → ℝ) × E) :=
  univ ×ˢ {x : E | Surjective (parameterDifferential (I := 𝓘(ℝ, E)) φ x)}


theorem isOpen_regularPerturbationDomain {φ : Fin n → E → ℝ}
    (hφ : ∀ i, ContDiff ℝ ∞ (φ i)) : IsOpen (regularPerturbationDomain φ) :=
  isOpen_univ.prod (isOpen_regularPerturbationBase hφ)


theorem exists_supported_regularPerturbationDomain {K U : Set E}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ (n : ℕ) (φ : Fin n → E → ℝ),
      (∀ i, ContDiff ℝ ∞ (φ i) ∧ HasCompactSupport (φ i) ∧ tsupport (φ i) ⊆ U) ∧
      IsOpen (regularPerturbationDomain φ) ∧
      (univ ×ˢ K : Set ((Fin n → ℝ) × E)) ⊆ regularPerturbationDomain φ := by
  obtain ⟨n, φ, hφ,hspan⟩ := exists_supported_differentials_span_of_isCompact
    (I := 𝓘(ℝ, E)) hK hU hKU
  have hφ' : ∀ i, ContDiff ℝ ∞ (φ i) := fun i => contMDiff_iff_contDiff.mp (hφ i).1
  refine ⟨n, φ, fun i => ⟨hφ' i, (hφ i).2⟩,isOpen_regularPerturbationDomain hφ',?_⟩
  intro q hq
  exact ⟨mem_univ _,surjective_parameterDifferential (hspan q.2 hq.2)⟩

end FiniteDimension
end Poincare.Morse
