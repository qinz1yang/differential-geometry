import DifferentialGeometry.Topology.Morse.RelativePerturbation

set_option autoImplicit false
noncomputable section
open Bundle Set Filter Function Module
open scoped Manifold ContDiff Topology BigOperators
namespace DifferentialGeometry.Morse
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H M : Type*} [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H} {n : ℕ}


def finitePerturbation (f : M → ℝ) (φ : Fin n → M → ℝ) (a : Fin n → ℝ) (x : M) : ℝ :=
  f x + ∑ i, a i * φ i x

omit [TopologicalSpace M] in
theorem finitePerturbation_zero (f : M → ℝ) (φ : Fin n → M → ℝ) :
    finitePerturbation f φ 0 = f := by
  ext x
  simp [finitePerturbation]


theorem contMDiff_finitePerturbation {f : M → ℝ} {φ : Fin n → M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hφ : ∀ i, ContMDiff I 𝓘(ℝ, ℝ) ∞ (φ i))
    (a : Fin n → ℝ) : ContMDiff I 𝓘(ℝ, ℝ) ∞ (finitePerturbation f φ a) := by
  apply hf.add
  exact contMDiff_finsetSum fun i _ => contMDiff_const.mul (hφ i)


theorem exists_open_finitePerturbation_eq {f : M → ℝ} {φ : Fin n → M → ℝ} {U : Set M}
    (hφ : ∀ i, tsupport (φ i) ⊆ U) :
    ∃ N : Set M, IsOpen N ∧ Uᶜ ⊆ N ∧ ∀ a, EqOn (finitePerturbation f φ a) f N := by
  refine ⟨(⋃ i, tsupport (φ i))ᶜ, (isClosed_iUnion_of_finite fun i => isClosed_tsupport _).isOpen_compl,
    compl_subset_compl.mpr (iUnion_subset hφ), ?_⟩
  intro a x hx
  have hz : ∀ i, φ i x = 0 := fun i => image_eq_zero_of_notMem_tsupport
    (fun hi => hx (mem_iUnion.mpr ⟨i, hi⟩))
  simp [finitePerturbation, hz]


def parameterDifferential (φ : Fin n → M → ℝ) (x : M) :
    (Fin n → ℝ) →L[ℝ] (E →L[ℝ] ℝ) :=
  (Fintype.linearCombination ℝ (fun i : Fin n =>
    (show E →L[ℝ] ℝ from mfderiv I 𝓘(ℝ, ℝ) (φ i) x))).toContinuousLinearMap


theorem parameterDifferential_apply (φ : Fin n → M → ℝ) (x : M) (a : Fin n → ℝ) :
    parameterDifferential (I := I) φ x a = ∑ i, a i •
      (show E →L[ℝ] ℝ from mfderiv I 𝓘(ℝ, ℝ) (φ i) x) := rfl


theorem mfderiv_finitePerturbation {f : M → ℝ} {φ : Fin n → M → ℝ} {x : M}
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x)
    (hφ : ∀ i, MDifferentiableAt I 𝓘(ℝ, ℝ) (φ i) x) (a : Fin n → ℝ) :
    (show E →L[ℝ] ℝ from mfderiv I 𝓘(ℝ, ℝ) (finitePerturbation f φ a) x) =
      (show E →L[ℝ] ℝ from mfderiv I 𝓘(ℝ, ℝ) f x) + parameterDifferential (I := I) φ x a := by
  have hh := hf.hasMFDerivAt.add (HasMFDerivAt.sum (t := Finset.univ)
    (fun i _ => (hφ i).hasMFDerivAt.const_smul (a i)))
  have hfun : finitePerturbation f φ a = f + ∑ i, a i • φ i := by
    ext y
    simp [finitePerturbation]
  rw [parameterDifferential_apply, hfun]
  exact hh.mfderiv


theorem hasFDerivAt_mfderiv_finitePerturbation {f : M → ℝ} {φ : Fin n → M → ℝ} {x : M}
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x)
    (hφ : ∀ i, MDifferentiableAt I 𝓘(ℝ, ℝ) (φ i) x) (a : Fin n → ℝ) :
    HasFDerivAt (fun p : Fin n → ℝ =>
      (show E →L[ℝ] ℝ from mfderiv I 𝓘(ℝ, ℝ) (finitePerturbation f φ p) x))
      (parameterDifferential (I := I) φ x) a := by
  have hh := ((parameterDifferential (I := I) φ x).hasFDerivAt (x := a)).const_add
    (show E →L[ℝ] ℝ from mfderiv I 𝓘(ℝ, ℝ) f x)
  apply hh.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun p => mfderiv_finitePerturbation hf hφ p


theorem surjective_parameterDifferential {φ : Fin n → M → ℝ} {x : M}
    (hspan : Submodule.span ℝ (range (fun i : Fin n =>
      (show TangentSpace I x →L[ℝ] ℝ from mfderiv I 𝓘(ℝ, ℝ) (φ i) x))) = ⊤) :
    Surjective (parameterDifferential (I := I) φ x) := by
  apply LinearMap.range_eq_top.mp
  change (Fintype.linearCombination ℝ (fun i : Fin n =>
    (show E →L[ℝ] ℝ from mfderiv I 𝓘(ℝ, ℝ) (φ i) x))).range = ⊤
  rw [Fintype.range_linearCombination]
  exact hspan


theorem contMDiff_joint_finitePerturbation {f : M → ℝ} {φ : Fin n → M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hφ : ∀ i, ContMDiff I 𝓘(ℝ, ℝ) ∞ (φ i)) :
    ContMDiff (𝓘(ℝ, Fin n → ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun q : (Fin n → ℝ) × M => finitePerturbation f φ q.1 q.2) := by
  apply (hf.comp contMDiff_snd).add
  apply contMDiff_finsetSum
  intro i _
  exact ((ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ).contDiff.contMDiff.comp
    contMDiff_fst).mul ((hφ i).comp contMDiff_snd)


theorem exists_relative_perturbation_parameter_submersion
    [FiniteDimensional ℝ E] [T2Space M] [IsManifold I ∞ M]
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    {K U : Set M} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ (n : ℕ) (φ : Fin n → M → ℝ) (N : Set M),
      (∀ i, ContMDiff I 𝓘(ℝ, ℝ) ∞ (φ i) ∧ HasCompactSupport (φ i) ∧ tsupport (φ i) ⊆ U) ∧
      IsOpen N ∧ Uᶜ ⊆ N ∧
      (∀ a, ContMDiff I 𝓘(ℝ, ℝ) ∞ (finitePerturbation f φ a) ∧
        EqOn (finitePerturbation f φ a) f N) ∧
      ∀ x ∈ K, ∀ a : Fin n → ℝ,
        Surjective (fderiv ℝ (fun p : Fin n → ℝ =>
          (show E →L[ℝ] ℝ from mfderiv I 𝓘(ℝ, ℝ) (finitePerturbation f φ p) x)) a) := by
  obtain ⟨n, φ, hφ, hspan⟩ := exists_supported_differentials_span_of_isCompact (I := I) hK hU hKU
  obtain ⟨N, hN, hUN, heq⟩ := exists_open_finitePerturbation_eq (f := f) (fun i => (hφ i).2.2)
  refine ⟨n, φ, N, hφ, hN, hUN, fun a =>
    ⟨contMDiff_finitePerturbation hf (fun i => (hφ i).1) a, heq a⟩, ?_⟩
  intro x hx a
  rw [(hasFDerivAt_mfderiv_finitePerturbation (hf.mdifferentiableAt (by simp))
    (fun i => (hφ i).1.mdifferentiableAt (by simp)) a).fderiv]
  exact surjective_parameterDifferential (hspan x hx)

end DifferentialGeometry.Morse
