import DifferentialGeometry.Geometry.Coordinates.ModelBasis
import DifferentialGeometry.Bundle.TangentSpace
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

noncomputable section

open Bundle Manifold Set
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.Tensor.Coordinates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def centeredChartTangentEquiv (x : M) : TangentSpace I x ≃L[ℝ] E :=
  (trivializationAt E (TangentSpace I) x).continuousLinearEquivAt ℝ x
    (FiberBundle.mem_baseSet_trivializationAt' x)

def centeredChartTangentBasis (x : M) :
    Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x) :=
  (chartModelBasis E).map
    (centeredChartTangentEquiv (I := I) x).symm.toLinearEquiv

omit [Module.Finite ℝ E] in
@[simp] lemma centeredChartTangentEquiv_apply (x : M) (v : TangentSpace I x) :
    centeredChartTangentEquiv (I := I) x v =
      tangentSpaceModelContinuousLinearEquiv (I := I) x v := by
  rw [tangentSpaceModelContinuousLinearEquiv_apply]
  rw [centeredChartTangentEquiv]
  rw [Trivialization.coe_continuousLinearEquivAt_eq]
  rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core
    (b₀ := x) (b := x) (mem_chart_source H x)]
  exact (tangentBundleCore I M).coordChange_self (achart H x) x
    (by rw [tangentBundleCore_baseSet, coe_achart]; exact mem_chart_source H x) v

omit [Module.Finite ℝ E] in
@[simp] lemma centeredChartTangentEquiv_symm_apply (x : M) (v : E) :
    (centeredChartTangentEquiv (I := I) x).symm v = v := by
  let vT : TangentSpace I x := v
  change (centeredChartTangentEquiv (I := I) x).symm v = vT
  apply (centeredChartTangentEquiv (I := I) x).injective
  rw [ContinuousLinearEquiv.apply_symm_apply]
  have hv : centeredChartTangentEquiv (I := I) x vT = v := by
    rw [centeredChartTangentEquiv_apply,
      tangentSpaceModelContinuousLinearEquiv_apply]
  exact hv.symm

@[simp] lemma centeredChartTangentBasis_apply (x : M)
    (i : Fin (Module.finrank ℝ E)) :
    centeredChartTangentBasis (I := I) x i =
      (centeredChartTangentEquiv (I := I) x).symm (chartModelBasis E i) := by
  rfl

lemma tangent_model_equiv_centered_chart_basis (x : M)
    (i : Fin (Module.finrank ℝ E)) :
    tangentSpaceModelContinuousLinearEquiv (I := I) x
        (centeredChartTangentBasis (I := I) x i) =
      chartModelBasis E i := by
  calc
    tangentSpaceModelContinuousLinearEquiv (I := I) x
        (centeredChartTangentBasis (I := I) x i) =
      centeredChartTangentEquiv (I := I) x
        (centeredChartTangentBasis (I := I) x i) := by
          exact (centeredChartTangentEquiv_apply (I := I) x _).symm
    _ = chartModelBasis E i := by
      rw [centeredChartTangentBasis_apply, ContinuousLinearEquiv.apply_symm_apply]

lemma tangent_model_equiv_symm_chart_basis (x : M)
    (i : Fin (Module.finrank ℝ E)) :
    (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm
        (chartModelBasis E i) =
      centeredChartTangentBasis (I := I) x i := by
  apply (tangentSpaceModelContinuousLinearEquiv (I := I) x).injective
  rw [ContinuousLinearEquiv.apply_symm_apply,
    tangent_model_equiv_centered_chart_basis]

@[simp] lemma centeredChartTangentBasis_repr (x : M) (v : TangentSpace I x) :
    (centeredChartTangentBasis (I := I) x).repr v =
      (chartModelBasis E).repr (centeredChartTangentEquiv (I := I) x v) := by
  simp only [centeredChartTangentBasis, Module.Basis.map_repr,
    LinearEquiv.trans_apply, ContinuousLinearEquiv.coe_symm_toLinearEquiv,
    ContinuousLinearEquiv.symm_symm]

def chartBasisVecFiber (x₀ : M) (i : Fin (Module.finrank ℝ E)) (x : M) :
    TangentSpace I x :=
  (trivializationAt E (TangentSpace I) x₀).symmL ℝ x ((chartModelBasis E) i)

def chartBasisVec (x₀ : M) (i : Fin (Module.finrank ℝ E)) :
    M → TotalSpace E (TangentSpace I : M → Type _) :=
  fun x => TotalSpace.mk' E x (chartBasisVecFiber (I := I) x₀ i x)

@[simp] lemma chartBasisVec_proj (x₀ : M) (i : Fin (Module.finrank ℝ E)) (x : M) :
    (chartBasisVec (I := I) x₀ i x).proj = x := rfl

@[simp] lemma chartBasisVec_snd (x₀ : M) (i : Fin (Module.finrank ℝ E)) (x : M) :
    (chartBasisVec (I := I) x₀ i x).2 = chartBasisVecFiber (I := I) x₀ i x := rfl

lemma trivializationAt_chartBasisVec_snd
    (x₀ : M) (i : Fin (Module.finrank ℝ E)) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    (trivializationAt E (TangentSpace I) x₀
        ⟨x, chartBasisVecFiber (I := I) x₀ i x⟩).2
      = (chartModelBasis E) i := by
  have h := (trivializationAt E (TangentSpace I) x₀).apply_mk_symm hx
    ((chartModelBasis E) i)
  rw [chartBasisVecFiber, Trivialization.symmL_apply _ hx]
  exact congrArg Prod.snd h

lemma chartBasisVec_contMDiffOn
    (x₀ : M) (i : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞ (chartBasisVec (I := I) x₀ i)
      (trivializationAt E (TangentSpace I) x₀).baseSet := by
  have hiff :=
    ((trivializationAt E (TangentSpace I) x₀)).contMDiffOn_section_baseSet_iff
      (IB := I) (n := ∞) (s := fun x => chartBasisVecFiber (I := I) x₀ i x)
  refine hiff.mpr ?_
  have hconst : ContMDiffOn I 𝓘(ℝ, E) ∞
      (fun _ : M => (chartModelBasis E) i)
      (trivializationAt E (TangentSpace I) x₀).baseSet :=
    contMDiffOn_const
  refine hconst.congr ?_
  intro x hx
  exact (trivializationAt_chartBasisVec_snd (I := I) x₀ i hx)

lemma chartAlphaFrame_section_contMDiffOn
    (α : M) (i : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I I.tangent ∞
      (fun b : M => TotalSpace.mk' E b
        ((trivializationAt E (TangentSpace I) α).symmL ℝ b
          (chartModelBasis E i)))
      (chartAt H α).source := by
  have h_baseSet :
      (trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source :=
    TangentBundle.trivializationAt_baseSet (I := I) α
  rw [← h_baseSet]
  refine (chartBasisVec_contMDiffOn (I := I) α i).congr ?_
  intro b hb
  simp only [chartBasisVec, chartBasisVecFiber,
    Trivialization.symmL_apply _ hb]

def chartBasisFamily (x₀ : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x) :=
  (chartModelBasis E).map
    (ContinuousLinearEquiv.toLinearEquiv
      ((trivializationAt E (TangentSpace I) x₀).continuousLinearEquivAt ℝ x hx).symm)

lemma chartBasisFamily_apply (x₀ : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    (i : Fin (Module.finrank ℝ E)) :
    chartBasisFamily (I := I) x₀ hx i =
      chartBasisVecFiber (I := I) x₀ i x := by
  unfold chartBasisFamily chartBasisVecFiber
  rw [Module.Basis.map_apply]
  exact congrFun ((trivializationAt E (TangentSpace I) x₀).symm_continuousLinearEquivAt_eq hx)
    ((chartModelBasis E) i)

lemma chartBasisFamily_linearIndependent (x₀ : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    LinearIndependent ℝ
      (fun i : Fin (Module.finrank ℝ E) =>
        chartBasisVecFiber (I := I) x₀ i x) := by
  have h := (chartBasisFamily (I := I) x₀ hx).linearIndependent
  have hcongr : (chartBasisFamily (I := I) x₀ hx : Fin (Module.finrank ℝ E) → TangentSpace I x)
      = fun i => chartBasisVecFiber (I := I) x₀ i x := by
    funext i
    exact chartBasisFamily_apply (I := I) x₀ hx i
  rw [← hcongr]
  exact h

end DifferentialGeometry.Tensor.Coordinates
