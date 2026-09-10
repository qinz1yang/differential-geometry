import DifferentialGeometry.Bundle.ParameterFamily
import DifferentialGeometry.Topology.VectorField.Transport
import DifferentialGeometry.Topology.VectorField.Pushforward

set_option autoImplicit false
noncomputable section
open Set Bundle Filter
open scoped Manifold ContDiff Topology
namespace Poincare.VectorField
variable {E H M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H} [IsManifold I 1 M]
  (c : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞)
  (V : ∀ x : M, TangentSpace I x) (A : ι → ∀ x : M, TangentSpace I x)


def parameterFamilyInCoordinates (q : (ι → ℝ) × E) : E :=
  _root_.VectorField.mpullback 𝓘(ℝ, E) I c.symm
    (Poincare.VectorBundle.parameterFamily V A q.1) q.2

omit [IsManifold I 1 M] in
theorem parameterFamilyInCoordinates_apply (p : ι → ℝ) (y : E) :
    parameterFamilyInCoordinates c V A (p, y) =
      _root_.VectorField.mpullback 𝓘(ℝ, E) I c.symm V y +
        ∑ i, p i • _root_.VectorField.mpullback 𝓘(ℝ, E) I c.symm (A i) y := by
  simp only [parameterFamilyInCoordinates, _root_.VectorField.mpullback,
    Poincare.VectorBundle.parameterFamily, map_add, map_sum, map_smul]
  rfl

omit [IsManifold I 1 M] in
theorem hasFDerivAt_parameterFamilyInCoordinates (p : ι → ℝ) (y : E) :
    HasFDerivAt (fun b => parameterFamilyInCoordinates c V A (b, y))
      ((mfderiv 𝓘(ℝ, E) I c.symm y).inverse ∘L
        Poincare.VectorBundle.parameterDerivative A (c.symm y)) p := by
  let L : TangentSpace I (c.symm y) →L[ℝ] E := (mfderiv 𝓘(ℝ, E) I c.symm y).inverse
  let D : (ι → ℝ) →L[ℝ] E := L ∘L Poincare.VectorBundle.parameterDerivative A (c.symm y)
  have he : (fun b => parameterFamilyInCoordinates c V A (b, y)) =
      (fun b => L (V (c.symm y)) + D b) := by
    funext b
    change L (V (c.symm y) + ∑ i, b i • A i (c.symm y)) =
      L (V (c.symm y)) + (L ∘L Poincare.VectorBundle.parameterDerivative A (c.symm y)) b
    rw [ContinuousLinearMap.comp_apply, Poincare.VectorBundle.parameterDerivative_apply, map_add, map_sum]
  rw [he]
  exact D.hasFDerivAt.const_add _

omit [IsManifold I 1 M] in
theorem surjective_parameterDerivative_in_coordinates {y : E} (hy : y ∈ c.target)
    (hspan : Submodule.span ℝ (range (fun i => A i (c.symm y))) = ⊤) :
    Function.Surjective ((mfderiv 𝓘(ℝ, E) I c.symm y).inverse ∘L
      Poincare.VectorBundle.parameterDerivative A (c.symm y)) :=
  (isInvertible_mfderiv_partialDiffeomorph c.symm (by simp) hy).inverse.surjective.comp
    (Poincare.VectorBundle.surjective_parameterDerivative A (c.symm y) hspan)

variable
  (hV : ContMDiff I I.tangent ∞ (fun x => (⟨x, V x⟩ : TangentBundle I M)))
  (hA : ∀ i, ContMDiff I I.tangent ∞ (fun x => (⟨x, A i x⟩ : TangentBundle I M)))

include hV hA

theorem contDiffOn_parameterFamilyInCoordinates :
    ContDiffOn ℝ ∞ (parameterFamilyInCoordinates c V A) (univ ×ˢ c.target) := by
  have hv : ContDiffOn ℝ ∞ (_root_.VectorField.mpullback 𝓘(ℝ, E) I c.symm V) c.target :=
    contMDiffOn_vectorSpace_iff_contDiffOn.mp
      (contMDiffOn_mpullback_partialDiffeomorph c.symm (by simp) hV.contMDiffOn)
  have ha (i : ι) : ContDiffOn ℝ ∞ (_root_.VectorField.mpullback 𝓘(ℝ, E) I c.symm (A i)) c.target :=
    contMDiffOn_vectorSpace_iff_contDiffOn.mp
      (contMDiffOn_mpullback_partialDiffeomorph c.symm (by simp) (hA i).contMDiffOn)
  have hs : ContDiffOn ℝ ∞ (fun q : (ι → ℝ) × E =>
      _root_.VectorField.mpullback 𝓘(ℝ, E) I c.symm V q.2 +
        ∑ i, q.1 i • _root_.VectorField.mpullback 𝓘(ℝ, E) I c.symm (A i) q.2)
      (univ ×ˢ c.target) := by
    apply (hv.comp contDiff_snd.contDiffOn (fun _ h => h.2)).add
    apply ContDiffOn.sum
    intro i _
    exact (((ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ).contDiff.comp
      contDiff_fst).contDiffOn).smul ((ha i).comp contDiff_snd.contDiffOn (fun _ h => h.2))
  exact hs.congr (fun q _ => parameterFamilyInCoordinates_apply c V A q.1 q.2)

theorem fderiv_parameterFamilyInCoordinates_comp_inl (p : ι → ℝ) {y : E}
    (hy : y ∈ c.target) :
    fderiv ℝ (parameterFamilyInCoordinates c V A) (p, y) ∘L
        ContinuousLinearMap.inl ℝ (ι → ℝ) E =
      (mfderiv 𝓘(ℝ, E) I c.symm y).inverse ∘L
        Poincare.VectorBundle.parameterDerivative A (c.symm y) := by
  have hd : DifferentiableAt ℝ (parameterFamilyInCoordinates c V A) (p, y) :=
    ((contDiffOn_parameterFamilyInCoordinates c V A hV hA).contDiffAt
      ((isOpen_univ.prod c.open_target).mem_nhds ⟨mem_univ _, hy⟩)).differentiableAt (by simp)
  have hin : HasFDerivAt (fun b : ι → ℝ => (b, y))
      (ContinuousLinearMap.inl ℝ (ι → ℝ) E) p :=
    (hasFDerivAt_id p).prodMk (hasFDerivAt_const y p)
  have hh : HasFDerivAt (fun b => parameterFamilyInCoordinates c V A (b, y))
      (fderiv ℝ (parameterFamilyInCoordinates c V A) (p, y) ∘L
        ContinuousLinearMap.inl ℝ (ι → ℝ) E) p := by
    simpa only [Function.comp_apply] using! hd.hasFDerivAt.comp p hin
  exact hh.unique (hasFDerivAt_parameterFamilyInCoordinates c V A p y)

theorem surjective_fderiv_parameterFamilyInCoordinates (p : ι → ℝ) {y : E}
    (hy : y ∈ c.target)
    (hspan : Submodule.span ℝ (range (fun i => A i (c.symm y))) = ⊤) :
    Function.Surjective (fderiv ℝ (parameterFamilyInCoordinates c V A) (p, y)) := by
  have hh := surjective_parameterDerivative_in_coordinates c A hy hspan
  rw [← fderiv_parameterFamilyInCoordinates_comp_inl c V A hV hA p hy] at hh
  exact Function.Surjective.of_comp hh

end Poincare.VectorField
