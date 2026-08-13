import DifferentialGeometry.Tensor.Alternating.Wedge
import DifferentialGeometry.Tensor.Exterior.Basic
import DifferentialGeometry.Tensor.Exterior.Cochain
import DifferentialGeometry.Tensor.Auxiliary.Shuffle.Placement

open Equiv.Perm ContinuousAlternatingMap DifferentialGeometry DifferentialGeometry.DifferentialForm
open scoped Manifold ContDiff
open Lean Elab Command

section wedge

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {M : Type*} [NormedAddCommGroup M] [NormedSpace 𝕜 M]
variable {m n p : ℕ}

example :
    (∀ (g : M [⋀^Fin m]→L[𝕜] 𝕜) (h : M [⋀^Fin n]→L[𝕜] 𝕜) (l : M [⋀^Fin p]→L[𝕜] 𝕜),
      ContinuousAlternatingMap.domDomCongr Fin.finAssoc.symm (g ∧[𝕜] (h ∧[𝕜] l)) =
        ((g ∧[𝕜] h) ∧[𝕜] l)) :=
  @ContinuousAlternatingMap.wedge_mul_assoc 𝕜 _ M _ _ m n p

example :
    (∀ (g : M [⋀^Fin m]→L[𝕜] 𝕜) (h : M [⋀^Fin n]→L[𝕜] 𝕜),
      (g ∧[𝕜] h) = ((-1 : 𝕜)^(m*n) • (h ∧[𝕜] g)).domDomCongr Fin.finAddCongr) :=
  @ContinuousAlternatingMap.wedge_antisymm 𝕜 _ M _ _ m n

example :
    (∀ (g : M [⋀^Fin m]→L[𝕜] 𝕜),
      ContinuousAlternatingMap.domDomCongr finAddFlip (g∧[𝕜]g) = (g∧[𝕜]g)) :=
  @ContinuousAlternatingMap.domDomCongr_finAddFlip_wedge_self m 𝕜 _ M _ _

example :
    (∀ (g : M [⋀^Fin m]→L[𝕜] 𝕜) (_m_odd : Odd m) (_h2 : (2 : 𝕜) ≠ 0),
      (g ∧[𝕜] g) = 0) :=
  @ContinuousAlternatingMap.wedge_self_odd_zero m 𝕜 _ M _ _

end wedge

section alternatization

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {M N N' N'' : Type*} [NormedAddCommGroup M] [NormedSpace 𝕜 M]
  [NormedAddCommGroup N] [NormedSpace 𝕜 N] [NormedAddCommGroup N'] [NormedSpace 𝕜 N']
  [NormedAddCommGroup N''] [NormedSpace 𝕜 N'']
variable {m n : ℕ}

example :
    (∀ (g : M [⋀^Fin m]→L[𝕜] N) (h : M [⋀^Fin n]→L[𝕜] N')
      (f : N →L[𝕜] N' →L[𝕜] N'') (v : Fin (m + n) → M),
      (m.factorial * n.factorial) • (g ∧[f] h) v =
        MultilinearMap.alternatization (tensorProductMap g h f).toMultilinearMap v) :=
  factorial_nsmul_wedge_product_eq_alternatization

end alternatization

section exterior

variable {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
  {HM : Type*} [TopologicalSpace HM]
  {IM : ModelWithCorners ℝ EM HM}
  {M : Type*} [TopologicalSpace M] [ChartedSpace HM M] [IsManifold IM ⊤ M]
  {k : ℕ}

noncomputable example :
    (∀ (_α : DifferentialForm IM M k) (x : M)
      (_hxi : ModelWithCorners.IsInteriorPoint IM x),
      Bundle.continuousAlternatingMap ℝ (Fin (k + 1)) EM (TangentSpace IM) ℝ
        (Bundle.Trivial M ℝ) x) :=
  exteriorDerivativeAtInterior

noncomputable example :
    (∀ [BoundarylessManifold IM M] (_α : DifferentialForm IM M k) (x : M),
      Bundle.continuousAlternatingMap ℝ (Fin (k + 1)) EM (TangentSpace IM) ℝ
        (Bundle.Trivial M ℝ) x) :=
  exteriorDerivativeAt

example :
    (∀ (_α : DifferentialForm IM M k) {x₀ x : M}
      (_hx : x ∈ (extChartAt IM x₀).source)
      (hxi : ModelWithCorners.IsInteriorPoint IM x),
      (trivializationAt (EM [⋀^Fin (k + 1)]→L[ℝ] ℝ)
        (Bundle.continuousAlternatingMap ℝ (Fin (k + 1)) EM (TangentSpace IM) ℝ
          (Bundle.Trivial M ℝ)) x₀ ⟨x, exteriorDerivativeAtInterior _α x hxi⟩).2 =
        extDeriv (fun y : EM => (trivializationAt (EM [⋀^Fin k]→L[ℝ] ℝ)
          (Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ
            (Bundle.Trivial M ℝ)) x₀
            ⟨(extChartAt IM x₀).symm y, _α ((extChartAt IM x₀).symm y)⟩).2)
          ((extChartAt IM x₀) x)) :=
  exteriorDerivative_localRepresentation

end exterior

section cochain

example :
    (∀ {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
      {HM : Type*} [TopologicalSpace HM] {IM : ModelWithCorners ℝ EM HM}
      {M : Type*} [TopologicalSpace M] [ChartedSpace HM M] [IsManifold IM ⊤ M]
      [BoundarylessManifold IM M],
      pullbackCochainMap (id : M → M) (contMDiff_id (I := IM) (M := M)) =
        CategoryTheory.CategoryStruct.id (deRhamCochainComplex (IM := IM) (M := M))) :=
  @DifferentialGeometry.DifferentialForm.pullbackCochainMap_id

example :
    (∀ {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
      {HM : Type*} [TopologicalSpace HM] {IM : ModelWithCorners ℝ EM HM}
      {M : Type*} [TopologicalSpace M] [ChartedSpace HM M] [IsManifold IM ⊤ M]
      [BoundarylessManifold IM M] (k : ℕ),
      pullbackCohomologyMap (id : M → M) (contMDiff_id (I := IM) (M := M)) k =
        CategoryTheory.CategoryStruct.id (deRhamCohomology (IM := IM) (M := M) k)) :=
  @DifferentialGeometry.DifferentialForm.pullbackCohomologyMap_id

run_cmd do
  let env ← getEnv
  let names := ["DifferentialGeometry.DifferentialForm.pullbackCochainMap_comp",
    "DifferentialGeometry.DifferentialForm.pullbackMapCochainMap_id",
    "DifferentialGeometry.DifferentialForm.pullbackMapCochainMap_comp",
    "DifferentialGeometry.DifferentialForm.pullbackCohomologyMap_comp",
    "DifferentialGeometry.DifferentialForm.pullbackMapCohomologyMap_id",
    "DifferentialGeometry.DifferentialForm.pullbackMapCohomologyMap_comp"]
  for n in names do
    let parts := n.splitOn "."
    let nm := parts.foldl (fun acc p => Name.str acc p) Name.anonymous
    if !env.contains nm then
      throwError m!"missing declaration {n}"

end cochain

section finite

noncomputable example : Fintype (Equiv.Perm.ThreeShuffle 2 3 4) := inferInstance
example : Finite (Equiv.Perm.ThreeShuffle 2 3 4) := inferInstance

end finite
