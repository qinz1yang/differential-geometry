import DifferentialGeometry.Tensor.Exterior.Basic
import DifferentialGeometry.Tensor.Exterior.Pullback
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Abelian

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

noncomputable def deRhamCochainComplex [BoundarylessManifold IM M] :
    CochainComplex (ModuleCat ℝ) ℕ :=
  CochainComplex.of
    (fun n : ℕ => ModuleCat.of ℝ (DifferentialForm IM M n))
    (fun n : ℕ => ModuleCat.ofHom (exteriorDerivativeLinearMap (IM := IM) (M := M) n))
    (fun n : ℕ => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      simp [ModuleCat.ofHom, exteriorDerivativeLinearMap]
      simpa using (exteriorDerivative_sq x))

@[simp] theorem deRhamCochainComplex_X [BoundarylessManifold IM M] (n : ℕ) :
    (deRhamCochainComplex (IM := IM) (M := M)).X n = ModuleCat.of ℝ (DifferentialForm IM M n) := by
  change (CochainComplex.of (fun n : ℕ => ModuleCat.of ℝ (DifferentialForm IM M n))
    (fun n : ℕ => ModuleCat.ofHom (exteriorDerivativeLinearMap (IM := IM) (M := M) n))
    (fun n : ℕ => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      simp [ModuleCat.ofHom, exteriorDerivativeLinearMap]
      simpa using (exteriorDerivative_sq x))).X n = ModuleCat.of ℝ (DifferentialForm IM M n)
  exact CochainComplex.of_x (X := fun n : ℕ => ModuleCat.of ℝ (DifferentialForm IM M n))
    (d := fun n : ℕ => ModuleCat.ofHom (exteriorDerivativeLinearMap (IM := IM) (M := M) n))
    (sq := fun n : ℕ => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      simp [ModuleCat.ofHom, exteriorDerivativeLinearMap]
      simpa using (exteriorDerivative_sq x)) n

@[simp] theorem deRhamCochainComplex_d [BoundarylessManifold IM M] (n : ℕ) :
    (deRhamCochainComplex (IM := IM) (M := M)).d n (n + 1) =
      ModuleCat.ofHom (exteriorDerivativeLinearMap (IM := IM) (M := M) n) := by
  change (CochainComplex.of (fun n : ℕ => ModuleCat.of ℝ (DifferentialForm IM M n))
    (fun n : ℕ => ModuleCat.ofHom (exteriorDerivativeLinearMap (IM := IM) (M := M) n))
    (fun n : ℕ => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      simp [ModuleCat.ofHom, exteriorDerivativeLinearMap]
      simpa using (exteriorDerivative_sq x))).d n (n + 1) =
      ModuleCat.ofHom (exteriorDerivativeLinearMap (IM := IM) (M := M) n)
  exact CochainComplex.of_d (X := fun n : ℕ => ModuleCat.of ℝ (DifferentialForm IM M n))
    (d := fun n : ℕ => ModuleCat.ofHom (exteriorDerivativeLinearMap (IM := IM) (M := M) n))
    (sq := fun n : ℕ => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      simp [ModuleCat.ofHom, exteriorDerivativeLinearMap]
      simpa using (exteriorDerivative_sq x)) n

noncomputable def deRhamCohomology [BoundarylessManifold IM M] (k : ℕ) : ModuleCat ℝ :=
  (deRhamCochainComplex (IM := IM) (M := M)).homology k

universe u v w

variable {EM : Type u} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
  {HM : Type v} [TopologicalSpace HM]
  {IM : ModelWithCorners ℝ EM HM}
  {M : Type w} [TopologicalSpace M] [ChartedSpace HM M] [IsManifold IM ⊤ M]
  {EN : Type u} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
  {HN : Type v} [TopologicalSpace HN]
  {IN : ModelWithCorners ℝ EN HN}
  {N : Type w} [TopologicalSpace N] [ChartedSpace HN N] [IsManifold IN ⊤ N]
  {EP : Type u} [NormedAddCommGroup EP] [NormedSpace ℝ EP]
  {HP : Type v} [TopologicalSpace HP]
  {IP : ModelWithCorners ℝ EP HP}
  {P : Type w} [TopologicalSpace P] [ChartedSpace HP P] [IsManifold IP ⊤ P]

noncomputable def pullbackCochainMap [BoundarylessManifold IM M] [BoundarylessManifold IN N]
    (f : M → N) (hf : ContMDiff IM IN ⊤ f) :
    deRhamCochainComplex (IM := IN) (M := N) ⟶ deRhamCochainComplex (IM := IM) (M := M) where
  f i := ModuleCat.ofHom (pullbackLinearMap f hf i)
  comm' := by
    intro i j hij
    have hj : i + 1 = j := by simpa using hij
    subst j
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro η
    simp only [deRhamCochainComplex_d, ModuleCat.hom_comp, LinearMap.coe_comp, comp_apply]
    exact (exteriorDerivative_pullback f hf η).symm

theorem pullbackCochainMap_id [BoundarylessManifold IM M] :
    pullbackCochainMap (id : M → M) (contMDiff_id (I := IM) (M := M)) =
      CategoryTheory.CategoryStruct.id (deRhamCochainComplex (IM := IM) (M := M)) := by
  apply HomologicalComplex.hom_ext
  intro i
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro α
  simp only [pullbackCochainMap, pullbackLinearMap]
  exact pullback_id α

theorem pullbackCochainMap_comp [BoundarylessManifold IM M] [BoundarylessManifold IN N]
    [BoundarylessManifold IP P] (f : M → N) (hf : ContMDiff IM IN ⊤ f) (g : N → P)
    (hg : ContMDiff IN IP ⊤ g) :
    pullbackCochainMap (g ∘ f) (hg.comp hf) =
      CategoryTheory.CategoryStruct.comp (pullbackCochainMap g hg) (pullbackCochainMap f hf) := by
  apply HomologicalComplex.hom_ext
  intro i
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro α
  simp only [pullbackCochainMap, pullbackLinearMap, HomologicalComplex.comp_f,
    ModuleCat.hom_comp, LinearMap.coe_comp, comp_apply]
  exact pullback_comp f hf g hg α

noncomputable def pullbackMapCochainMap [BoundarylessManifold IM M] [BoundarylessManifold IN N]
    (f : C^⊤⟮IM, M; IN, N⟯) :
    deRhamCochainComplex (IM := IN) (M := N) ⟶ deRhamCochainComplex (IM := IM) (M := M) :=
  pullbackCochainMap f.1 f.2

theorem pullbackMapCochainMap_id [BoundarylessManifold IM M] :
    pullbackMapCochainMap (ContMDiffMap.id (I := IM) (M := M) : C^⊤⟮IM, M; IM, M⟯) =
      CategoryTheory.CategoryStruct.id (deRhamCochainComplex (IM := IM) (M := M)) := by
  simpa [pullbackMapCochainMap] using pullbackCochainMap_id

theorem pullbackMapCochainMap_comp [BoundarylessManifold IM M] [BoundarylessManifold IN N]
    [BoundarylessManifold IP P] (f : C^⊤⟮IM, M; IN, N⟯) (g : C^⊤⟮IN, N; IP, P⟯) :
    pullbackMapCochainMap (ContMDiffMap.comp g f) =
      CategoryTheory.CategoryStruct.comp (pullbackMapCochainMap g) (pullbackMapCochainMap f) := by
  simpa [pullbackMapCochainMap] using pullbackCochainMap_comp f.1 f.2 g.1 g.2

noncomputable def pullbackCohomologyMap [BoundarylessManifold IM M] [BoundarylessManifold IN N]
    (f : M → N) (hf : ContMDiff IM IN ⊤ f) (k : ℕ) :
    deRhamCohomology (IM := IN) (M := N) k ⟶ deRhamCohomology (IM := IM) (M := M) k :=
  HomologicalComplex.homologyMap (pullbackCochainMap f hf) k

theorem pullbackCohomologyMap_id [BoundarylessManifold IM M] (k : ℕ) :
    pullbackCohomologyMap (id : M → M) (contMDiff_id (I := IM) (M := M)) k =
      CategoryTheory.CategoryStruct.id (deRhamCohomology (IM := IM) (M := M) k) := by
  rw [pullbackCohomologyMap, pullbackCochainMap_id]
  exact HomologicalComplex.homologyMap_id
    (K := deRhamCochainComplex (IM := IM) (M := M)) (i := k)

theorem pullbackCohomologyMap_comp [BoundarylessManifold IM M] [BoundarylessManifold IN N]
    [BoundarylessManifold IP P] (f : M → N) (hf : ContMDiff IM IN ⊤ f) (g : N → P)
    (hg : ContMDiff IN IP ⊤ g) (k : ℕ) :
    pullbackCohomologyMap (g ∘ f) (hg.comp hf) k =
      CategoryTheory.CategoryStruct.comp (pullbackCohomologyMap g hg k)
        (pullbackCohomologyMap f hf k) := by
  have hc : pullbackCochainMap (g ∘ f) (hg.comp hf) =
      CategoryTheory.CategoryStruct.comp (pullbackCochainMap g hg) (pullbackCochainMap f hf) :=
    pullbackCochainMap_comp f hf g hg
  rw [pullbackCohomologyMap, pullbackCohomologyMap, pullbackCohomologyMap, hc]
  change HomologicalComplex.homologyMap
      (CategoryTheory.CategoryStruct.comp (pullbackCochainMap g hg) (pullbackCochainMap f hf)) k =
    CategoryTheory.CategoryStruct.comp
      (HomologicalComplex.homologyMap (pullbackCochainMap g hg) k)
      (HomologicalComplex.homologyMap (pullbackCochainMap f hf) k)
  exact HomologicalComplex.homologyMap_comp (C := ModuleCat.{max u w} ℝ) (c := ComplexShape.up ℕ)
    (K := deRhamCochainComplex (IM := IP) (M := P))
    (L := deRhamCochainComplex (IM := IN) (M := N))
    (M := deRhamCochainComplex (IM := IM) (M := M))
    (φ := pullbackCochainMap g hg) (ψ := pullbackCochainMap f hf) (i := k)

noncomputable def pullbackMapCohomologyMap [BoundarylessManifold IM M] [BoundarylessManifold IN N]
    (f : C^⊤⟮IM, M; IN, N⟯) (k : ℕ) :
    deRhamCohomology (IM := IN) (M := N) k ⟶ deRhamCohomology (IM := IM) (M := M) k :=
  pullbackCohomologyMap f.1 f.2 k

theorem pullbackMapCohomologyMap_id [BoundarylessManifold IM M] (k : ℕ) :
    pullbackMapCohomologyMap (ContMDiffMap.id (I := IM) (M := M) : C^⊤⟮IM, M; IM, M⟯) k =
      CategoryTheory.CategoryStruct.id (deRhamCohomology (IM := IM) (M := M) k) := by
  simpa [pullbackMapCohomologyMap] using pullbackCohomologyMap_id (k := k)

theorem pullbackMapCohomologyMap_comp [BoundarylessManifold IM M] [BoundarylessManifold IN N]
    [BoundarylessManifold IP P] (f : C^⊤⟮IM, M; IN, N⟯) (g : C^⊤⟮IN, N; IP, P⟯) (k : ℕ) :
    pullbackMapCohomologyMap (ContMDiffMap.comp g f) k =
      CategoryTheory.CategoryStruct.comp (pullbackMapCohomologyMap g k)
        (pullbackMapCohomologyMap f k) := by
  simpa [pullbackMapCohomologyMap] using pullbackCohomologyMap_comp f.1 f.2 g.1 g.2 (k := k)

end DifferentialForm
end DifferentialGeometry

end
