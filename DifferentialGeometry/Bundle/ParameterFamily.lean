import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

set_option autoImplicit false
noncomputable section
open Set Bundle Filter
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.VectorBundle
variable {B ι : Type*} [Fintype ι] {F : B → Type*}
  [∀ x, AddCommGroup (F x)] [∀ x, Module ℝ (F x)]
  (V : ∀ x, F x) (A : ι → ∀ x, F x)


def parameterFamily (p : ι → ℝ) (x : B) : F x := V x + ∑ i, p i • A i x


@[simp]
theorem parameterFamily_zero (x : B) : parameterFamily V A 0 x = V x := by
  simp [parameterFamily]


theorem parameterFamily_eq_self (p : ι → ℝ) (x : B) (hA : ∀ i, A i x = 0) :
    parameterFamily V A p x = V x := by
  simp [parameterFamily, hA]

variable [∀ x, TopologicalSpace (F x)] [∀ x, IsTopologicalAddGroup (F x)]
  [∀ x, ContinuousSMul ℝ (F x)]


def parameterDerivative (x : B) : (ι → ℝ) →L[ℝ] F x :=
  ∑ i, (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ).smulRight (A i x)


@[simp]
theorem parameterDerivative_apply (x : B) (b : ι → ℝ) :
    parameterDerivative A x b = ∑ i, b i • A i x := by
  simp [parameterDerivative]

theorem hasFDerivAt_parameterFamily (x : B) (p : ι → ℝ) :
    HasFDerivAt (fun b => parameterFamily V A b x) (parameterDerivative A x) p := by
  apply HasFDerivAt.of_isLittleOTVS
  exact (Asymptotics.IsLittleOTVS.zero (fun b : ι → ℝ => b - p) (𝓝 p)).congr_left (fun b => by
    simp only [Pi.zero_apply, parameterFamily, ← parameterDerivative_apply A x, map_sub]
    abel)

theorem surjective_parameterDerivative (x : B)
    (hspan : Submodule.span ℝ (range (fun i => A i x)) = ⊤) :
    Function.Surjective (parameterDerivative A x) := by
  intro w
  obtain ⟨b, hb⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp
    (hspan ▸ (show w ∈ (⊤ : Submodule ℝ (F x)) from trivial))
  exact ⟨b, (parameterDerivative_apply A x b).trans hb⟩

section Smooth
variable {EB HB E : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  [TopologicalSpace HB] [TopologicalSpace B] [ChartedSpace HB B]
  (I : ModelWithCorners ℝ EB HB) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace (TotalSpace E F)] [FiberBundle E F] [VectorBundle ℝ E F]
  {n : ℕ∞ω}

omit [∀ x, IsTopologicalAddGroup (F x)] [∀ x, ContinuousSMul ℝ (F x)] in
theorem contMDiff_parameterFamily
    (hV : ContMDiff I (I.prod 𝓘(ℝ, E)) n (fun x => TotalSpace.mk' E x (V x)))
    (hA : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) n (fun x => TotalSpace.mk' E x (A i x))) :
    ContMDiff ((𝓘(ℝ, ι → ℝ)).prod I) (I.prod 𝓘(ℝ, E)) n
      (fun q : (ι → ℝ) × B => TotalSpace.mk' E q.2 (parameterFamily V A q.1 q.2)) := by
  intro q
  rw [contMDiffAt_totalSpace]
  refine ⟨contMDiffAt_snd, ?_⟩
  let e := trivializationAt E F q.2
  have hv : ContMDiffAt I 𝓘(ℝ, E) n (fun x => (e ⟨x, V x⟩).2) q.2 :=
    (contMDiffAt_section q.2).mp (hV q.2)
  have ha (i : ι) : ContMDiffAt I 𝓘(ℝ, E) n (fun x => (e ⟨x, A i x⟩).2) q.2 :=
    (contMDiffAt_section q.2).mp (hA i q.2)
  have hs : ContMDiffAt ((𝓘(ℝ, ι → ℝ)).prod I) 𝓘(ℝ, E) n
      (fun z : (ι → ℝ) × B => (e ⟨z.2, V z.2⟩).2 + ∑ i, z.1 i • (e ⟨z.2, A i z.2⟩).2) q := by
    apply (hv.comp q contMDiffAt_snd).add
    apply ContMDiffAt.sum
    intro i _
    exact (((ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ).contDiff.contMDiff.contMDiffAt).comp q
      contMDiffAt_fst).smul ((ha i).comp q contMDiffAt_snd)
  apply hs.congr_of_eventuallyEq
  have he : ∀ᶠ z : (ι → ℝ) × B in 𝓝 q, z.2 ∈ e.baseSet :=
    continuous_snd.continuousAt.preimage_mem_nhds
      (e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt E F q.2))
  filter_upwards [he] with z hz
  change (e ⟨z.2, parameterFamily V A z.1 z.2⟩).2 = _
  rw [e.apply_eq_prod_continuousLinearEquivAt ℝ z.2 hz]
  simp only [parameterFamily, map_add, map_sum, map_smul]
  congr 1
end Smooth
end DifferentialGeometry.VectorBundle
