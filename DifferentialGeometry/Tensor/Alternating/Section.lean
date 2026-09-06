import DifferentialGeometry.Tensor.Alternating.Bundle
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

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CharZero 𝕜] [CompleteSpace 𝕜]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable [FiniteDimensional 𝕜 F]
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
  ⟨fun x => (α x).toContinuousMultilinearMap, by
    intro x₀
    let ea := trivializationAt (F [⋀^Fin s]→L[𝕜] 𝕜)
      (Bundle.continuousAlternatingMap 𝕜 (Fin s) F E 𝕜
        (Bundle.Trivial B 𝕜)) x₀
    let em := trivializationAt (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
      (Bundle.continuousMultilinearMap 𝕜 s F E) x₀
    rw [Bundle.Trivialization.contMDiffAt_section_iff em
      (mem_baseSet_trivializationAt _ _ x₀)]
    have hα : ContMDiffAt IB 𝓘(𝕜, F [⋀^Fin s]→L[𝕜] 𝕜) n
        (fun x => (ea ⟨x, α x⟩).2) x₀ := by
      exact (Bundle.Trivialization.contMDiffAt_section_iff ea
        (mem_baseSet_trivializationAt _ _ x₀)).mp (α.contMDiff_toFun x₀)
    have hconv : ContMDiffAt IB
        𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜) n
        (fun x => ContinuousAlternatingMap.toContinuousMultilinearMapCLM 𝕜
          ((ea ⟨x, α x⟩).2)) x₀ :=
      (ContinuousAlternatingMap.toContinuousMultilinearMapCLM 𝕜).contMDiff.contMDiffAt.comp
        x₀ hα
    refine hconv.congr_of_eventuallyEq ?_
    filter_upwards with x
    change (em ⟨x, (α x).toContinuousMultilinearMap⟩).2 =
      ContinuousAlternatingMap.toContinuousMultilinearMapCLM 𝕜 ((ea ⟨x, α x⟩).2)
    have hem :
        (em ⟨x, (α x).toContinuousMultilinearMap⟩).2 =
          (α x).toContinuousMultilinearMap.compContinuousLinearMap
            (fun _ => (trivializationAt F E x₀).symmL 𝕜 x) := by
      rfl
    have hea :
        (ea ⟨x, α x⟩).2 =
          (α x).compContinuousLinearMap
            ((trivializationAt F E x₀).symmL 𝕜 x) := by
      rw [FiberBundle.trivializationAt_continuousAlternatingMap_apply]
      ext v
      simp [ContinuousAlternatingMap.inCoordinates]
    rw [hem, hea]
    ext v
    rfl⟩

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F] in
@[simp] theorem toMultilinearSection_apply {s : ℕ}
    (α : AlternatingSection 𝕜 F IB E n s) (x : B) :
    α.toMultilinearSection x = (α x).toContinuousMultilinearMap :=
  rfl

end AlternatingSection

namespace MultilinearSection

noncomputable def alternatization {s : ℕ}
    (α : MultilinearSection 𝕜 F IB E n s) :
    AlternatingSection 𝕜 F IB E n s :=
  ⟨fun x => ContinuousMultilinearMap.alternatizationCLM (α x), by
    intro x₀
    let ea := trivializationAt (F [⋀^Fin s]→L[𝕜] 𝕜)
      (Bundle.continuousAlternatingMap 𝕜 (Fin s) F E 𝕜
        (Bundle.Trivial B 𝕜)) x₀
    let em := trivializationAt (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
      (Bundle.continuousMultilinearMap 𝕜 s F E) x₀
    rw [Bundle.Trivialization.contMDiffAt_section_iff ea
      (mem_baseSet_trivializationAt _ _ x₀)]
    have hα : ContMDiffAt IB
        𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜) n
        (fun x => (em ⟨x, α x⟩).2) x₀ := by
      exact (Bundle.Trivialization.contMDiffAt_section_iff em
        (mem_baseSet_trivializationAt _ _ x₀)).mp (α.contMDiff_toFun x₀)
    have hconv : ContMDiffAt IB 𝓘(𝕜, F [⋀^Fin s]→L[𝕜] 𝕜) n
        (fun x => ContinuousMultilinearMap.alternatizationCLM
          ((em ⟨x, α x⟩).2)) x₀ :=
      ContinuousMultilinearMap.alternatizationCLM.contMDiff.contMDiffAt.comp x₀ hα
    refine hconv.congr_of_eventuallyEq ?_
    filter_upwards with x
    change (ea ⟨x, ContinuousMultilinearMap.alternatizationCLM (α x)⟩).2 =
      ContinuousMultilinearMap.alternatizationCLM ((em ⟨x, α x⟩).2)
    have hem :
        (em ⟨x, α x⟩).2 =
          (α x).compContinuousLinearMap
            (fun _ => (trivializationAt F E x₀).symmL 𝕜 x) := by
      rfl
    have hea :
        (ea ⟨x, ContinuousMultilinearMap.alternatizationCLM (α x)⟩).2 =
          (ContinuousMultilinearMap.alternatizationCLM (α x)).compContinuousLinearMap
            ((trivializationAt F E x₀).symmL 𝕜 x) := by
      rw [FiberBundle.trivializationAt_continuousAlternatingMap_apply]
      ext v
      simp [ContinuousAlternatingMap.inCoordinates]
    rw [hem, hea]
    exact
      (ContinuousMultilinearMap.alternatizationCLM_compContinuousLinearMap
        (α x) ((trivializationAt F E x₀).symmL 𝕜 x)).symm⟩

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F] in
@[simp] theorem alternatization_apply {s : ℕ}
    (α : MultilinearSection 𝕜 F IB E n s) (x : B) :
    α.alternatization x = ContinuousMultilinearMap.alternatizationCLM (α x) :=
  rfl

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F] in
@[simp] theorem alternatization_toMultilinearSection {s : ℕ}
    (α : AlternatingSection 𝕜 F IB E n s) :
    α.toMultilinearSection.alternatization = α := by
  apply ContMDiffSection.ext
  intro x
  exact ContinuousMultilinearMap.alternatizationCLM_apply_toContinuousMultilinearMap (α x)

end MultilinearSection

end DifferentialGeometry
