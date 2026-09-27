import DifferentialGeometry.Geometry.Metric.Construction.BumpExtension
import DifferentialGeometry.Tensor.Multilinear.Bundle.Evaluation
import DifferentialGeometry.Tensor.Multilinear.Bundle.Basis


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Manifold Filter Set
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Tensor.Multilinear
open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance tensorBumpC1 : IsManifold I 1 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)


theorem exists_tensor_bump_extension (U : TopologicalSpace.Opens M) (r : ℕ)
    (A : Tensor0SField (I := I) (M := U) (n := ∞) r)
    (χ : M → ℝ) (hχ : ContMDiff I 𝓘(ℝ) ∞ χ) (hsupp : tsupport χ ⊆ (U : Set M)) :
    ∃ B : Tensor0SField (I := I) (M := M) (n := ∞) r,
      (∀ x : M, ∀ hx : x ∈ U, ∀ v : Fin r → TangentSpace I x,
        B x v = χ x * A ⟨x, hx⟩ v) ∧
      ∀ x : M, x ∉ U → B x = 0 := by
  classical
  let raw : (x : M) → Tensor0SSpace r I x := fun x => if hx : x ∈ U then A ⟨x, hx⟩ else 0
  have hraw (x : M) (hx : x ∈ U) : raw x = A ⟨x, hx⟩ := dif_pos hx
  have hrawOut (x : M) (hx : x ∉ U) : raw x = 0 := dif_neg hx
  let T : (x : M) → Tensor0SSpace r I x := fun x => χ x • raw x
  let := tensor0SBundleTopology (𝕜 := ℝ) (I := I) (M := M) r
  refine ⟨⟨T, ?_⟩, ?_, ?_⟩
  · let b := Module.finBasis ℝ E
    refine (contMDiff_multilinearSection_iff_coord (TangentSpace I) ∞ b T).mpr ?_
    intro slots x₀
    let e := trivializationAt E (TangentSpace I : M → Type _) x₀
    have hx₀ : x₀ ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x₀
    have hscalar : ContMDiffAt I 𝓘(ℝ) ∞
        (fun x => T x (fun k => Geometry.frameVec (I := I) x₀ (slots k) x)) x₀ := by
      by_cases hxU : x₀ ∈ U
      · rw [← contMDiffAt_subtype_iff (I := I) (I' := 𝓘(ℝ)) (U := U) (x := ⟨x₀, hxU⟩)]
        have hframe := fun k => Geometry.frameVec_sub_cmdiffAt (I := I) U x₀ (slots k) hx₀ hxU
        have hvalue := TensorMultilinear.contMDiffAt_section_apply (I := I) (M := U)
          (T := fun z => A z) (A.contMDiff ⟨x₀, hxU⟩)
          (v := fun k z => Geometry.frameVec (I := I) x₀ (slots k) (z : M)) hframe
        have hχU := (hχ.comp (contMDiff_subtype_val (I := I) (U := U))).contMDiffAt
          (x := (⟨x₀, hxU⟩ : U))
        apply (hχU.mul hvalue).congr_of_eventuallyEq
        exact Filter.Eventually.of_forall fun z => by
          change (χ (z : M) • raw (z : M)) (fun k => Geometry.frameVec (I := I) x₀ (slots k) (z : M)) = _
          rw [hraw (z : M) z.property]
          rfl
      · have hxSupp : x₀ ∉ tsupport χ := fun h => hxU (hsupp h)
        apply (contMDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
        filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hxSupp] with x hx
        have hzero : χ x = 0 := image_eq_zero_of_notMem_tsupport hx
        simp only [T, hzero, zero_smul, Tensor0SSpace.zero_apply]
    refine hscalar.congr_of_eventuallyEq ?_
    filter_upwards [e.open_baseSet.mem_nhds hx₀] with x _hx
    rw [continuousMultilinearMap_basis_repr]
    change (tensor0SSpaceFiberContinuousLinearEquiv (I := I) (M := M) r x (T x)).compContinuousLinearMap
      (fun _ : Fin r => e.symmL ℝ x) (fun k => b (slots k)) = _
    rw [ContinuousMultilinearMap.compContinuousLinearMap_apply,
      tensor0SSpaceFiberContinuousLinearEquiv_apply_apply]
    rfl
  · intro x hx v
    change (χ x • raw x) v = _
    rw [hraw x hx]
    rfl
  · intro x hx
    change χ x • raw x = 0
    rw [hrawOut x hx, smul_zero]

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
