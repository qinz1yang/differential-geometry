import DifferentialGeometry.Tensor.Alternating.BundleMaps
import DifferentialGeometry.Tensor.Multilinear.Field

noncomputable section

open Bundle Set
open scoped Manifold Topology Bundle ContDiff

namespace DifferentialGeometry

abbrev AlternatingSection
    (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
    {HB : Type*} [TopologicalSpace HB] (IB : ModelWithCorners 𝕜 EB HB)
    {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
    (E : B → Type*) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace 𝕜 (E x)]
    [TopologicalSpace (TotalSpace F E)]
    [FiberBundle F E] [VectorBundle 𝕜 F E]
    (n : WithTop ℕ∞) [hSmooth : ContMDiffVectorBundle n F E IB] (s : ℕ) :=
  let _ := hSmooth
  ContMDiffSection IB (F [⋀^Fin s]→L[𝕜] 𝕜) n
    (Bundle.continuousAlternatingMap 𝕜 (Fin s) F E 𝕜 (Bundle.Trivial B 𝕜))

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
variable {HB : Type*} [TopologicalSpace HB]
variable {IB : ModelWithCorners 𝕜 EB HB}
variable {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
variable {E : B → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace 𝕜 (E x)]
variable [TopologicalSpace (TotalSpace F E)]
variable [FiberBundle F E] [VectorBundle 𝕜 F E]
variable {n : WithTop ℕ∞} [ContMDiffVectorBundle n F E IB]

namespace AlternatingSection

noncomputable def toMultilinearSection {s : ℕ}
    (α : AlternatingSection 𝕜 F IB E n s) :
    MultilinearSection 𝕜 F IB E n s :=
  ⟨fun x => (α x).toContinuousMultilinearMap,
    α.contMDiff_toFun.alternating_bundle_toMultilinear⟩

@[simp] theorem toMultilinearSection_apply {s : ℕ}
    (α : AlternatingSection 𝕜 F IB E n s) (x : B) :
    α.toMultilinearSection x = (α x).toContinuousMultilinearMap :=
  rfl

end AlternatingSection

namespace MultilinearSection

noncomputable def alternatization {s : ℕ}
    (α : MultilinearSection 𝕜 F IB E n s) :
    AlternatingSection 𝕜 F IB E n s :=
  ⟨fun x => ContinuousMultilinearMap.alternatizationCLM (α x),
    α.contMDiff_toFun.multilinear_bundle_alternatization⟩

@[simp] theorem alternatization_apply {s : ℕ}
    (α : MultilinearSection 𝕜 F IB E n s) (x : B) :
    α.alternatization x = ContinuousMultilinearMap.alternatizationCLM (α x) :=
  rfl

@[simp] theorem alternatization_toMultilinearSection [CharZero 𝕜] {s : ℕ}
    (α : AlternatingSection 𝕜 F IB E n s) :
    α.toMultilinearSection.alternatization = α := by
  apply ContMDiffSection.ext
  intro x
  exact ContinuousMultilinearMap.alternatizationCLM_apply_toContinuousMultilinearMap (α x)

end MultilinearSection

end DifferentialGeometry
