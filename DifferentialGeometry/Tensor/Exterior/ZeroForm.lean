import DifferentialGeometry.Tensor.Exterior.Basic
import Mathlib.Geometry.Manifold.ContMDiffMap
import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions

noncomputable section

open Bundle Set ContinuousAlternatingMap Function Filter
open scoped Topology Manifold ContDiff Bundle

namespace DifferentialGeometry
namespace DifferentialForm

attribute [local instance] seminormedAddCommGroupTangentSpace
attribute [local instance] normedAddCommGroupTangentSpace
attribute [local instance] normedSpaceTangentSpace

variable {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
  {HM : Type*} [TopologicalSpace HM]
  {IM : ModelWithCorners ℝ EM HM}
  {M : Type*} [TopologicalSpace M] [ChartedSpace HM M] [IsManifold IM ⊤ M]

noncomputable def ofFunction (f : M → ℝ) (hf : ContMDiff IM 𝓘(ℝ, ℝ) ⊤ f) :
    DifferentialForm IM M 0 :=
  ⟨fun x => constOfIsEmpty ℝ (TangentSpace IM x) (Fin 0) (f x), by
    intro x₀
    let e := trivializationAt (EM [⋀^Fin 0]→L[ℝ] ℝ)
      (Bundle.continuousAlternatingMap ℝ (Fin 0) EM (TangentSpace IM) ℝ
        (Bundle.Trivial M ℝ)) x₀
    rw [Bundle.Trivialization.contMDiffAt_section_iff e
      (mem_baseSet_trivializationAt (EM [⋀^Fin 0]→L[ℝ] ℝ)
        (Bundle.continuousAlternatingMap ℝ (Fin 0) EM (TangentSpace IM) ℝ
          (Bundle.Trivial M ℝ)) x₀)]
    let hclm : ℝ →L[ℝ] (EM [⋀^Fin 0]→L[ℝ] ℝ) :=
      (ContinuousAlternatingMap.constOfIsEmptyLIE ℝ EM ℝ
        (Fin 0)).toContinuousLinearEquiv.toContinuousLinearMap
    have hc : ContMDiffAt IM 𝓘(ℝ, EM [⋀^Fin 0]→L[ℝ] ℝ) ⊤
        (fun x : M => hclm (f x)) x₀ := by
      exact (ContinuousLinearMap.contMDiff hclm).contMDiffAt.comp x₀ hf.contMDiffAt
    have hc' : ContMDiffAt IM 𝓘(ℝ, EM [⋀^Fin 0]→L[ℝ] ℝ) ⊤
        (fun x : M => constOfIsEmpty ℝ EM (Fin 0) (f x)) x₀ := by
      refine hc.congr_of_eventuallyEq ?_
      exact eventually_of_mem (Filter.univ_mem : (univ : Set M) ∈ 𝓝 x₀) (fun x hx => by
        change hclm (f x) = constOfIsEmpty ℝ EM (Fin 0) (f x)
        rfl)
    refine hc'.congr_of_eventuallyEq ?_
    exact eventually_of_mem (e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt
      (EM [⋀^Fin 0]→L[ℝ] ℝ)
      (Bundle.continuousAlternatingMap ℝ (Fin 0) EM (TangentSpace IM) ℝ
        (Bundle.Trivial M ℝ)) x₀)) (fun x hx => by
      change (trivializationAt (EM [⋀^Fin 0]→L[ℝ] ℝ)
        (Bundle.continuousAlternatingMap ℝ (Fin 0) EM (TangentSpace IM) ℝ
          (Bundle.Trivial M ℝ)) x₀
        ⟨x, constOfIsEmpty ℝ (TangentSpace IM x) (Fin 0) (f x)⟩).2 =
        constOfIsEmpty ℝ EM (Fin 0) (f x)
      rw [continuousAlternatingMap_trivializationAt_apply (m := 0) (IM := IM) (M := M)
        (x₀ := x₀) (x := x)
        (L := constOfIsEmpty ℝ (TangentSpace IM x) (Fin 0) (f x))]
      exact (DifferentialGeometry.DifferentialForm.constOfIsEmpty_compContinuousLinearMap
        (E := TangentSpace IM x) (E' := EM) (y := f x)
        (A := (trivializationAt EM (TangentSpace IM) x₀).symmL ℝ x)))
    ⟩

noncomputable def ofFunctionMap (f : C^⊤⟮IM, M; ℝ⟯) : DifferentialForm IM M 0 :=
  ofFunction f.1 f.2

@[simp] theorem ofFunctionMap_apply (f : C^⊤⟮IM, M; ℝ⟯) (x : M) :
    (ofFunctionMap f) x = ofFunction f.1 f.2 x := rfl

noncomputable def toFunction (α : DifferentialForm IM M 0) : M → ℝ :=
  fun x => (α x).toFun (0 : Fin 0 → TangentSpace IM x)

@[simp]
theorem toFunction_ofFunction (f : M → ℝ) (hf : ContMDiff IM 𝓘(ℝ, ℝ) ⊤ f) :
    toFunction (ofFunction f hf) = f := by
  funext x
  dsimp [toFunction, ofFunction]

theorem contMDiff_toFunction (α : DifferentialForm IM M 0) :
    ContMDiff IM 𝓘(ℝ, ℝ) ⊤ (toFunction α) := by
  intro x₀
  let e := trivializationAt (EM [⋀^Fin 0]→L[ℝ] ℝ)
    (Bundle.continuousAlternatingMap ℝ (Fin 0) EM (TangentSpace IM) ℝ
      (Bundle.Trivial M ℝ)) x₀
  have hrep : ContMDiffAt IM 𝓘(ℝ, EM [⋀^Fin 0]→L[ℝ] ℝ) ⊤
      (fun x : M => (e ⟨x, α x⟩).2) x₀ := by
    exact (Bundle.Trivialization.contMDiffAt_section_iff e
      (mem_baseSet_trivializationAt (EM [⋀^Fin 0]→L[ℝ] ℝ)
        (Bundle.continuousAlternatingMap ℝ (Fin 0) EM (TangentSpace IM) ℝ
          (Bundle.Trivial M ℝ)) x₀)).mp (α.contMDiff_toFun x₀)
  let L : (EM [⋀^Fin 0]→L[ℝ] ℝ) →L[ℝ] ℝ :=
    (ContinuousAlternatingMap.constOfIsEmptyLIE ℝ EM ℝ
      (Fin 0)).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hL : ContMDiffAt IM 𝓘(ℝ, ℝ) ⊤ (fun x : M => L ((e ⟨x, α x⟩).2)) x₀ := by
    exact (ContinuousLinearMap.contMDiff L).contMDiffAt.comp x₀ hrep
  refine hL.congr_of_eventuallyEq ?_
  exact eventually_of_mem (e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt
    (EM [⋀^Fin 0]→L[ℝ] ℝ)
    (Bundle.continuousAlternatingMap ℝ (Fin 0) EM (TangentSpace IM) ℝ
      (Bundle.Trivial M ℝ)) x₀)) (fun x hx => by
    dsimp [toFunction, L]
    change (α x).toFun (0 : Fin 0 → TangentSpace IM x) =
      (trivializationAt (EM [⋀^Fin 0]→L[ℝ] ℝ)
        (Bundle.continuousAlternatingMap ℝ (Fin 0) EM (TangentSpace IM) ℝ
          (Bundle.Trivial M ℝ)) x₀ ⟨x, α x⟩).2 (0 : Fin 0 → EM)
    rw [continuousAlternatingMap_trivializationAt_apply (m := 0) (IM := IM) (M := M) (x₀ := x₀)
      (x := x) (L := α x)]
    change (α x).toFun (0 : Fin 0 → TangentSpace IM x) =
      (α x).toFun (((trivializationAt EM (TangentSpace IM) x₀).symmL ℝ x) ∘ (0 : Fin 0 → EM))
    apply congrArg (α x).toFun
    funext i
    exact Fin.elim0 i)

theorem ofFunction_toFunction (α : DifferentialForm IM M 0) :
    ofFunction (toFunction α) (contMDiff_toFunction α) = α := by
  ext x
  dsimp [ofFunction, toFunction]
  exact (ContinuousAlternatingMap.constOfIsEmptyLIE ℝ (TangentSpace IM x) ℝ (Fin 0)).right_inv (α x)

noncomputable def toFunctionMap (α : DifferentialForm IM M 0) : C^⊤⟮IM, M; ℝ⟯ :=
  ⟨toFunction α, contMDiff_toFunction α⟩

@[simp]
theorem toFunctionMap_apply (α : DifferentialForm IM M 0) (x : M) :
    (toFunctionMap α) x = toFunction α x := rfl

theorem toFunctionMap_ofFunctionMap (f : C^⊤⟮IM, M; ℝ⟯) :
    toFunctionMap (ofFunctionMap f) = f := by
  ext x
  simp [toFunctionMap, ofFunctionMap]

theorem ofFunctionMap_toFunctionMap (α : DifferentialForm IM M 0) :
    ofFunctionMap (toFunctionMap α) = α := by
  ext x
  simp [toFunctionMap, ofFunctionMap, ofFunction_toFunction]

theorem toFunction_add (α β : DifferentialForm IM M 0) :
    toFunction (α + β) = toFunction α + toFunction β := by
  funext x
  change (α x + β x).toFun (0 : Fin 0 → TangentSpace IM x) =
    (α x).toFun (0 : Fin 0 → TangentSpace IM x) + (β x).toFun (0 : Fin 0 → TangentSpace IM x)
  rfl

theorem toFunction_smul (c : ℝ) (α : DifferentialForm IM M 0) :
    toFunction (c • α) = c • toFunction α := by
  funext x
  change (c • α x).toFun (0 : Fin 0 → TangentSpace IM x) =
    c • (α x).toFun (0 : Fin 0 → TangentSpace IM x)
  rfl

noncomputable def zeroFormLinearEquiv : DifferentialForm IM M 0 ≃ₗ[ℝ] C^⊤⟮IM, M; ℝ⟯ where
  toFun := toFunctionMap
  invFun := ofFunctionMap
  left_inv := ofFunctionMap_toFunctionMap
  right_inv := toFunctionMap_ofFunctionMap
  map_add' := by
    intro α β
    ext x
    simp [toFunctionMap, toFunction_add]
  map_smul' := by
    intro c α
    ext x
    simp [toFunctionMap, toFunction_smul]

private theorem exteriorDerivativeAt_ofFunction_apply [BoundarylessManifold IM M]
    (f : M → ℝ) (hf : ContMDiff IM 𝓘(ℝ, ℝ) ⊤ f) (x : M) (v : TangentSpace IM x) :
    (exteriorDerivativeAt (ofFunction f hf) x).toFun (fun _ : Fin 1 => v) =
      mfderiv IM 𝓘(ℝ, ℝ) f x v := by
  let e₀ := trivializationAt (EM [⋀^Fin 0]→L[ℝ] ℝ)
    (Bundle.continuousAlternatingMap ℝ (Fin 0) EM (TangentSpace IM) ℝ (Bundle.Trivial M ℝ)) x
  let e₁' := trivializationAt (EM [⋀^Fin 1]→L[ℝ] ℝ)
    (Bundle.continuousAlternatingMap ℝ (Fin 1) EM (TangentSpace IM) ℝ (Bundle.Trivial M ℝ)) x
  let e₁ := trivializationAt EM (TangentSpace IM) x
  have hrep : (fun y : EM => (e₀ ⟨(extChartAt IM x).symm y,
      ofFunction f hf ((extChartAt IM x).symm y)⟩).2) =
      fun y : EM => constOfIsEmpty ℝ EM (Fin 0) (f ((extChartAt IM x).symm y)) := by
    funext y
    change (trivializationAt (EM [⋀^Fin 0]→L[ℝ] ℝ)
      (Bundle.continuousAlternatingMap ℝ (Fin 0) EM (TangentSpace IM) ℝ
        (Bundle.Trivial M ℝ)) x ⟨(extChartAt IM x).symm y,
        constOfIsEmpty ℝ (TangentSpace IM ((extChartAt IM x).symm y)) (Fin 0)
          (f ((extChartAt IM x).symm y))⟩).2 =
      constOfIsEmpty ℝ EM (Fin 0) (f ((extChartAt IM x).symm y))
    rw [continuousAlternatingMap_trivializationAt_apply (m := 0) (IM := IM) (M := M) (x₀ := x)
      (x := (extChartAt IM x).symm y)
      (L := constOfIsEmpty ℝ (TangentSpace IM ((extChartAt IM x).symm y)) (Fin 0)
        (f ((extChartAt IM x).symm y)))]
    exact DifferentialForm.constOfIsEmpty_compContinuousLinearMap
      (E := TangentSpace IM ((extChartAt IM x).symm y)) (E' := EM)
      (y := f ((extChartAt IM x).symm y))
      (A := (trivializationAt EM (TangentSpace IM) x).symmL ℝ ((extChartAt IM x).symm y))
  have hext : extDeriv (fun y : EM => (e₀ ⟨(extChartAt IM x).symm y,
      ofFunction f hf ((extChartAt IM x).symm y)⟩).2) ((extChartAt IM x) x) =
      ofSubsingleton ℝ EM ℝ (0 : Fin 1)
        (fderiv ℝ (fun y : EM => f ((extChartAt IM x).symm y)) ((extChartAt IM x) x)) := by
    rw [hrep]
    exact extDeriv_constOfIsEmpty (f := fun y : EM => f ((extChartAt IM x).symm y))
      ((extChartAt IM x) x)
  have hloc : (e₁' ⟨x, exteriorDerivativeAt (ofFunction f hf) x⟩).2 =
      ofSubsingleton ℝ EM ℝ (0 : Fin 1)
        (fderiv ℝ (fun y : EM => f ((extChartAt IM x).symm y)) ((extChartAt IM x) x)) := by
    exact (exteriorDerivative_localRepresentation (IM := IM) (M := M) (α := ofFunction f hf)
      (x₀ := x) (x := x) (by simp)
      (BoundarylessManifold.isInteriorPoint (I := IM) (M := M) (x := x))).trans hext
  have hstep : (exteriorDerivativeAt (ofFunction f hf) x).toFun (fun _ : Fin 1 => v) =
      ((exteriorDerivativeAt (ofFunction f hf) x).compContinuousLinearMap (e₁.symmL ℝ x)).toFun
        (fun _ : Fin 1 => e₁.continuousLinearMapAt ℝ x v) := by
    change (exteriorDerivativeAt (ofFunction f hf) x).toFun (fun _ : Fin 1 => v) =
      (exteriorDerivativeAt (ofFunction f hf) x).toFun
        ((e₁.symmL ℝ x) ∘ (fun _ : Fin 1 => e₁.continuousLinearMapAt ℝ x v))
    apply congrArg (exteriorDerivativeAt (ofFunction f hf) x).toFun
    funext i
    exact (Trivialization.symmL_continuousLinearMapAt (R := ℝ) e₁
      (mem_baseSet_trivializationAt EM (TangentSpace IM) x) v).symm
  have hfwd : (e₁' ⟨x, exteriorDerivativeAt (ofFunction f hf) x⟩).2 =
      (exteriorDerivativeAt (ofFunction f hf) x).compContinuousLinearMap (e₁.symmL ℝ x) := by
    exact continuousAlternatingMap_trivializationAt_apply (m := 1) (IM := IM) (M := M) (x₀ := x)
      (x := x)
      (L := exteriorDerivativeAt (ofFunction f hf) x)
  have hmain : (exteriorDerivativeAt (ofFunction f hf) x).toFun (fun _ : Fin 1 => v) =
      fderiv ℝ (fun y : EM => f ((extChartAt IM x).symm y)) ((extChartAt IM x) x)
        (e₁.continuousLinearMapAt ℝ x v) := by
    rw [hstep, ← hfwd, hloc]
    simp
  rw [hmain]
  have heq₁ : e₁.continuousLinearMapAt ℝ x = ContinuousLinearMap.id ℝ EM := by
    rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core (𝕜 := ℝ) (I := IM) (M := M)
      (by simp)]
    apply ContinuousLinearMap.ext
    intro w
    exact tangentCoordChange_self (I := IM) (x := x) (z := x)
      (by simp)
  rw [heq₁]
  have hmem : (extChartAt IM x) x ∈ interior ((extChartAt IM x).target) :=
    (ModelWithCorners.isInteriorPoint_iff (I := IM)).1
      (BoundarylessManifold.isInteriorPoint (I := IM) (M := M) (x := x))
  have hdiff : DifferentiableAt ℝ (fun y : EM => f ((extChartAt IM x).symm y))
      ((extChartAt IM x) x) := by
    have hs : ContMDiffAt 𝓘(ℝ, EM) IM ⊤ (extChartAt IM x).symm ((extChartAt IM x) x) := by
      exact (contMDiffOn_extChartAt_symm x).contMDiffAt (mem_interior_iff_mem_nhds.mp hmem)
    have hcomp : ContMDiffAt 𝓘(ℝ, EM) 𝓘(ℝ, ℝ) ⊤
        (fun y : EM => f ((extChartAt IM x).symm y)) ((extChartAt IM x) x) :=
      ContMDiffAt.comp ((extChartAt IM x) x) (hf.contMDiffAt) hs
    exact (contMDiffAt_iff_contDiffAt.mp hcomp).differentiableAt (by simp)
  have hmfd : mfderiv IM 𝓘(ℝ, ℝ) f x =
      fderivWithin ℝ (fun y : EM => f ((extChartAt IM x).symm y)) (range IM)
        ((extChartAt IM x) x) := by
    have hmd : MDifferentiableAt IM 𝓘(ℝ, ℝ) f x := hf.mdifferentiableAt (by simp)
    rw [mfderiv, if_pos hmd]
    ext y
    rfl
  have hfder : fderivWithin ℝ (fun y : EM => f ((extChartAt IM x).symm y)) (range IM)
        ((extChartAt IM x) x) =
      fderiv ℝ (fun y : EM => f ((extChartAt IM x).symm y)) ((extChartAt IM x) x) := by
    exact fderivWithin_eq_fderiv
      (IM.uniqueDiffOn ((extChartAt IM x) x)
        (interior_subset (interior_mono (extChartAt_target_subset_range (x := x)) hmem)))
      hdiff
  rw [hmfd, hfder]
  rfl

theorem exteriorDerivative_ofFunction_apply [BoundarylessManifold IM M] (f : M → ℝ)
    (hf : ContMDiff IM 𝓘(ℝ, ℝ) ⊤ f) (x : M) (v : TangentSpace IM x) :
    (exteriorDerivative (ofFunction f hf) x).toFun (fun _ : Fin 1 => v) =
      mfderiv IM 𝓘(ℝ, ℝ) f x v := by
  rw [exteriorDerivative_apply]
  exact exteriorDerivativeAt_ofFunction_apply f hf x v

end DifferentialForm
end DifferentialGeometry

end
