import DifferentialGeometry.Geometry.Connection.Realization.Embedding
import DifferentialGeometry.Bundle.Section
import DifferentialGeometry.Bundle.Dual
import DifferentialGeometry.Bundle.Equiv
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-!
# Smooth sections of the dual tangent bundle

This file provides smoothness lemmas about sections of the dual tangent bundle
`Bundle.dual ℝ (TangentSpace I)`, needed for realizing the dual covariant derivative
on 1-forms.

## Main results

* `contMDiff_dual_apply_section` : for smooth α ∈ Γ(T*M) and Y ∈ Γ(TM), the scalar
  function `y ↦ α(y)(Y(y))` is smooth.
* `contMDiff_extDerivFun_section` : for smooth `h : C^∞⟮I, M; ℝ⟯`, the exterior
  derivative `extDerivFun h` is a smooth section of the cotangent bundle.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Topology
open Bundle

section SmoothSections

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H)
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-! ### Claim A: smoothness of α applied to Y -/

/-- For a smooth section α of T*M (viewed as the hom bundle `Hom(TM, ℝ)`) and a smooth
vector field Y, the scalar function `y ↦ α(y)(Y(y))` is smooth.

The proof uses `ContMDiff.clm_bundle_apply` (from `Mathlib/Geometry/Manifold/VectorBundle/Hom.lean`)
applied to the two smooth total-space maps corresponding to α and Y, with codomain the
trivial ℝ-bundle. The trivial-bundle total-space smoothness then unwraps to ordinary
function smoothness via `Bundle.contMDiff_trivial`. -/
theorem contMDiff_dual_apply_section
    (α : Cₛ^∞⟮I; E →L[ℝ] ℝ, (Bundle.dual ℝ (TangentSpace I : M → Type _))⟯)
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun y => α y (Y y)) := by
  have hα : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ)
        (E := fun x : M => (TangentSpace I x →L[ℝ] (Bundle.Trivial M ℝ) x))
        y (α y)) := α.contMDiff
  have hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y (Y y)) := Y.contMDiff
  have hap : ContMDiff I (I.prod 𝓘(ℝ, ℝ)) ∞
      (fun y => TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) y (α y (Y y))) :=
    ContMDiff.clm_bundle_apply (b := id) hα hY

  intro y
  exact (contMDiffAt_section (F := ℝ) (E := Bundle.Trivial M ℝ) y).mp (hap y)

/-! ### Helper: pointwise-to-operator smoothness for CLM-valued maps

The Mathlib-side lemma `contMDiffAt_clm_of_pointwise` (in `VectorBundle/Equiv.lean`)
is now public and used directly below. -/

/-! ### Claim B: smoothness of the exterior derivative as a section of T*M -/

/-- For a smooth function `h : C^∞⟮I, M; ℝ⟯`, the exterior derivative `extDerivFun h`
is a smooth section of the dual tangent bundle `Bundle.dual ℝ (TangentSpace I)`.

Proof strategy: using `contMDiffAt_section`, reduce to smoothness of the trivialized
fiber component; using `contMDiffAt_clm_of_pointwise_local`, reduce to per-vector
smoothness; for each fixed `v : E`, the scalar `extDerivFun h x v` equals
`vectorFieldActionSmooth I M X h x` for a smooth section `X` with `X x₀ = v`, which
agrees with `v` on a neighborhood (after the coordinate change is handled). -/
theorem contMDiff_extDerivFun_section (h : C^∞⟮I, M; ℝ⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] ℝ)
        (E := fun x : M => (TangentSpace I x →L[ℝ] (Bundle.Trivial M ℝ) x))
        x (extDerivFun h x)) := by
  intro x₀

  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, ?_⟩

  apply contMDiffAt_clm_of_pointwise (IB := I) (X := M)
  intro v

  have hh : ContMDiff I 𝓘(ℝ, ℝ) ∞ (h : M → ℝ) := h.contMDiff
  have hmfderiv : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] ℝ) ∞
      (inTangentCoordinates I 𝓘(ℝ, ℝ) id (h : M → ℝ) (mfderiv I 𝓘(ℝ, ℝ) (h : M → ℝ)) x₀) x₀ :=
    hh.contMDiffAt.mfderiv_const (le_refl _)
  have hmfderiv_v : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun x => inTangentCoordinates I 𝓘(ℝ, ℝ) id (h : M → ℝ)
        (mfderiv I 𝓘(ℝ, ℝ) (h : M → ℝ)) x₀ x v) x₀ :=
    ((ContinuousLinearMap.apply ℝ ℝ v).contMDiff.contMDiffAt).comp x₀ hmfderiv

  convert hmfderiv_v using 1
  ext x

  simp only [inTangentCoordinates, ContinuousLinearMap.inCoordinates,
    Bundle.Trivial.fiberBundle_trivializationAt',
    Bundle.Trivial.continuousLinearMapAt_trivialization,
    TangentBundle.continuousLinearMapAt_model_space,
    extDerivFun, ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.coe_id', id_eq]

  rfl

/-! ### Bridge: pointwise smoothness of CLM-bundle-valued sections

Given `φ : ∀ x : M, V₁ x →L[ℝ] V₂ x` such that for every smooth section `Y` of `V₁` the
section `x ↦ ⟨x, φ x (Y x)⟩` of `V₂` is smooth, conclude that `φ` itself is a smooth
section of the Hom-bundle `Hom(V₁, V₂)`.

This is the missing adjoint of `ContMDiff.clm_bundle_apply`: it lifts pointwise
smoothness of a CLM-bundle-valued section to total-space smoothness of the
corresponding Hom-bundle section, when the source bundle is finite-dimensional. -/
theorem contMDiff_clm_section_of_pointwise
    {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [FiniteDimensional ℝ F₁]
    {V₁ : M → Type*} [∀ x, AddCommGroup (V₁ x)] [∀ x, Module ℝ (V₁ x)]
    [TopologicalSpace (TotalSpace F₁ V₁)] [∀ x, TopologicalSpace (V₁ x)]
    [FiberBundle F₁ V₁] [VectorBundle ℝ F₁ V₁]
    [ContMDiffVectorBundle ∞ F₁ V₁ I]
    {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] [FiniteDimensional ℝ F₂]
    {V₂ : M → Type*} [∀ x, AddCommGroup (V₂ x)] [∀ x, Module ℝ (V₂ x)]
    [TopologicalSpace (TotalSpace F₂ V₂)] [∀ x, TopologicalSpace (V₂ x)]
    [FiberBundle F₂ V₂] [VectorBundle ℝ F₂ V₂]
    [ContMDiffVectorBundle ∞ F₂ V₂ I]
    [∀ x, IsTopologicalAddGroup (V₂ x)] [∀ x, ContinuousSMul ℝ (V₂ x)]
    (φ : ∀ x : M, V₁ x →L[ℝ] V₂ x)
    (h : ∀ (Y : Cₛ^∞⟮I; F₁, V₁⟯),
      ContMDiff I (I.prod 𝓘(ℝ, F₂)) ∞
        (fun x => TotalSpace.mk' F₂ (E := V₂) x (φ x (Y x)))) :
    ContMDiff I (I.prod 𝓘(ℝ, F₁ →L[ℝ] F₂)) ∞
      (fun x => TotalSpace.mk' (F₁ →L[ℝ] F₂)
        (E := fun x : M => V₁ x →L[ℝ] V₂ x) x (φ x)) := by
  intro x₀

  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, ?_⟩

  apply contMDiffAt_clm_of_pointwise (IB := I) (X := M)
  intro v

  let e₁ := trivializationAt F₁ V₁ x₀
  let e₂ := trivializationAt F₂ V₂ x₀
  let b := Module.finBasis ℝ F₁
  have he₁ : x₀ ∈ e₁.baseSet := mem_baseSet_trivializationAt F₁ V₁ x₀
  have he₂ : x₀ ∈ e₂.baseSet := mem_baseSet_trivializationAt F₂ V₂ x₀

  have hframe := e₁.isLocalFrameOn_localFrame_baseSet I (⊤ : ℕ∞) b
  obtain ⟨Y, hY⟩ := hframe.exists_contMDiffSection_eqOn_nhd e₁.open_baseSet he₁

  have hφY : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, F₂)) ∞
      (fun x => TotalSpace.mk' F₂ (E := V₂) x (φ x (Y i x))) := fun i => h (Y i)

  have hφY_fiber : ∀ i, ContMDiffAt I 𝓘(ℝ, F₂) ∞
      (fun x => (e₂ ⟨x, φ x (Y i x)⟩).2) x₀ := fun i => by
    have hi := (contMDiffAt_section (F := F₂) (E := V₂) x₀).mp ((hφY i) x₀)
    simpa [e₂, trivializationAt] using hi

  have hsum : ContMDiffAt I 𝓘(ℝ, F₂) ∞
      (fun x => ∑ i, b.repr v i • (e₂ ⟨x, φ x (Y i x)⟩).2) x₀ := by
    apply ContMDiffAt.sum
    intro i _
    exact (contMDiffAt_const (c := (b.repr v i : ℝ))).smul (hφY_fiber i)

  refine hsum.congr_of_eventuallyEq ?_

  have h_base₁ : ∀ᶠ x in 𝓝 x₀, x ∈ e₁.baseSet :=
    e₁.open_baseSet.mem_nhds he₁
  have h_base₂ : ∀ᶠ x in 𝓝 x₀, x ∈ e₂.baseSet :=
    e₂.open_baseSet.mem_nhds he₂
  filter_upwards [h_base₁, h_base₂, hY] with x hx₁ hx₂ hYx

  have hv_decomp : v = ∑ i, b.repr v i • b i := (b.sum_repr v).symm
  have h_inCoord : (ContinuousLinearMap.inCoordinates F₁ V₁ F₂ V₂ x₀ x x₀ x (φ x)) v =
      e₂.continuousLinearMapAt ℝ x ((φ x) (e₁.symmL ℝ x v)) := rfl
  rw [h_inCoord]

  have h₁ : e₁.symmL ℝ x v = ∑ i, (b.repr v) i • e₁.symmL ℝ x (b i) := by
    conv_lhs => rw [hv_decomp]
    rw [map_sum]; congr 1; ext i; rw [map_smul]
  have h₂ : (φ x) (∑ i, (b.repr v) i • e₁.symmL ℝ x (b i)) =
      ∑ i, (b.repr v) i • (φ x) (e₁.symmL ℝ x (b i)) := by
    rw [map_sum]; congr 1; ext i; rw [map_smul]
  have h₃ : e₂.continuousLinearMapAt ℝ x (∑ i, (b.repr v) i • (φ x) (e₁.symmL ℝ x (b i))) =
      ∑ i, (b.repr v) i • e₂.continuousLinearMapAt ℝ x ((φ x) (e₁.symmL ℝ x (b i))) := by
    rw [map_sum]; congr 1; ext i; rw [map_smul]
  rw [h₁, h₂, h₃]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  congr 1

  have h_lf : e₁.symmL ℝ x (b i) = (Y i) x := by
    rw [hYx i]
    rw [Trivialization.localFrame_apply_of_mem_baseSet (hx := hx₁)]
    simp [Trivialization.basisAt]
  rw [h_lf]

  change (Trivialization.continuousLinearMapAt ℝ e₂ x) ((φ x) ((Y i) x)) = _
  rw [show ⇑(e₂.continuousLinearMapAt ℝ x) = ⇑(e₂.linearMapAt ℝ x) from rfl,
    e₂.coe_linearMapAt_of_mem hx₂]

end SmoothSections

end
