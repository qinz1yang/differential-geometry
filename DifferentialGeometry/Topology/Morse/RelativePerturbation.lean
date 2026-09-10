import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Dual.Lemmas

set_option autoImplicit false
noncomputable section
open Bundle Set Filter Function Module
open scoped Manifold ContDiff Topology
universe uE uH uM
namespace Poincare.Morse
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {M : Type uM} [TopologicalSpace M]
  [ChartedSpace H M] (I : ModelWithCorners ℝ E H) [IsManifold I ∞ M] [T2Space M]

omit [IsManifold I ∞ M] in
theorem exists_finite_smoothBumpCovering {K U : Set M}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ (ι : Type uM) (_ : Fintype ι) (b : SmoothBumpCovering ι I M K),
      b.IsSubordinate (fun _ => U) := by
  classical
  have hb : ∀ x : K, ∃ b : SmoothBumpFunction I x.val, tsupport b ⊆ U := by
    intro x
    obtain ⟨b, _, hb⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := I) x.val).mem_iff.mp
      (hU.mem_nhds (hKU x.property))
    exact ⟨b, hb⟩
  choose b hb using hb
  let O : K → Set M := fun x => interior {y | b x y = 1}
  have hO : ∀ x, IsOpen (O x) := fun _ => isOpen_interior
  have hcover : K ⊆ ⋃ x : K, O x := by
    intro x hx
    refine mem_iUnion.mpr ⟨⟨x, hx⟩, ?_⟩
    exact mem_interior_iff_mem_nhds.mpr (b ⟨x,hx⟩).eventuallyEq_one
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover O hO hcover
  refine ⟨↥s, inferInstance, ⟨fun i => i.val.val, fun i => b i.val,
    fun i => i.val.property, locallyFinite_of_finite _, ?_⟩, fun i => hb i.val⟩
  intro x hx
  obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (hs hx)
  refine ⟨⟨i,hi⟩, ?_⟩
  exact mem_of_superset ((hO i).mem_nhds hxi) interior_subset

variable {I}
section LocalizedCharts
variable {ι : Type*} [Fintype ι] {K : Set M}


def localizedChartMap (b : SmoothBumpCovering ι I M K) (x : M) : ι → E :=
  fun i => b i x • extChartAt I (b.c i) x


theorem contMDiff_localizedChartMap (b : SmoothBumpCovering ι I M K) :
    ContMDiff I 𝓘(ℝ, ι → E) ∞ (localizedChartMap b) :=
  contMDiff_pi_space.mpr fun i => (b i).contMDiff_smul contMDiffOn_extChartAt


theorem proj_mfderiv_localizedChartMap (b : SmoothBumpCovering ι I M K)
    {x : M} (hx : x ∈ K) :
    (ContinuousLinearMap.proj (b.ind x hx) : (ι → E) →L[ℝ] E) ∘L
        mfderiv I 𝓘(ℝ, ι → E) (localizedChartMap b) x =
      mfderiv I I (chartAt H (b.c (b.ind x hx))) x := by
  let L : (ι → E) →L[ℝ] E := ContinuousLinearMap.proj (b.ind x hx)
  have hh := L.hasMFDerivAt.comp x
    ((contMDiff_localizedChartMap b).mdifferentiableAt (by simp)).hasMFDerivAt
  apply hasMFDerivAt_unique hh
  apply (hasMFDerivAt_extChartAt (b.mem_chartAt_ind_source x hx)).congr_of_eventuallyEq
  filter_upwards [b.eventuallyEq_one x hx] with y hy
  change b (b.ind x hx) y • extChartAt I (b.c (b.ind x hx)) y = extChartAt I (b.c (b.ind x hx)) y
  rw [hy, Pi.one_apply, one_smul]


theorem injective_mfderiv_localizedChartMap (b : SmoothBumpCovering ι I M K)
    {x : M} (hx : x ∈ K) :
    Injective (mfderiv I 𝓘(ℝ, ι → E) (localizedChartMap b) x) := by
  have hh : Injective (mfderiv I I (chartAt H (b.c (b.ind x hx))) x) :=
    LinearMap.ker_eq_bot.mp ((mdifferentiable_chart (b.c (b.ind x hx))).ker_mfderiv_eq_bot
      (b.mem_chartAt_ind_source x hx))
  rw [← proj_mfderiv_localizedChartMap b hx] at hh
  intro v w hvw
  apply hh
  exact congrArg (fun z : ι → E => z (b.ind x hx)) hvw

omit [Fintype ι] [IsManifold I ∞ M] [T2Space M] in
theorem tsupport_localizedChartMap_subset [Finite ι] (b : SmoothBumpCovering ι I M K) :
    tsupport (localizedChartMap b) ⊆ ⋃ i, tsupport (b i) := by
  apply closure_minimal _ (isClosed_iUnion_of_finite fun i => isClosed_tsupport (b i))
  intro x hx
  by_contra hn
  have hb : ∀ i, b i x = 0 := by
    intro i
    apply image_eq_zero_of_notMem_tsupport
    exact fun hi => hn (mem_iUnion.mpr ⟨i, hi⟩)
  apply hx
  funext i
  simp [localizedChartMap, hb]

omit [Fintype ι] [IsManifold I ∞ M] in
theorem hasCompactSupport_localizedChartMap [Finite ι] (b : SmoothBumpCovering ι I M K) :
    HasCompactSupport (localizedChartMap b) :=
  (isCompact_iUnion fun i => (b i).hasCompactSupport).of_isClosed_subset
    (isClosed_tsupport _) (tsupport_localizedChartMap_subset b)

end LocalizedCharts

omit [T2Space M] [IsManifold I ∞ M] [FiniteDimensional ℝ E] in
theorem mfderiv_component {n : ℕ} {F : M → Fin n → ℝ} {x : M}
    (hF : MDifferentiableAt I 𝓘(ℝ, Fin n → ℝ) F x) (i : Fin n) :
    mfderiv I 𝓘(ℝ, ℝ) (fun y => F y i) x =
      (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ) ∘L
        mfderiv I 𝓘(ℝ, Fin n → ℝ) F x := by
  exact ((ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ).hasMFDerivAt.comp x
    hF.hasMFDerivAt).mfderiv

omit [T2Space M] [IsManifold I ∞ M] in
theorem span_mfderiv_components_of_injective {n : ℕ} {F : M → Fin n → ℝ} {x : M}
    (hF : MDifferentiableAt I 𝓘(ℝ, Fin n → ℝ) F x)
    (hinj : Injective (mfderiv I 𝓘(ℝ, Fin n → ℝ) F x)) :
    Submodule.span ℝ (range (fun i : Fin n => (show TangentSpace I x →L[ℝ] ℝ from mfderiv I 𝓘(ℝ, ℝ) (fun y => F y i) x))) = ⊤ := by
  change Submodule.span ℝ (range (fun i : Fin n =>
    (show E →L[ℝ] ℝ from mfderiv I 𝓘(ℝ, ℝ) (fun y => F y i) x))) = ⊤
  rw [← Submodule.map_eq_top_iff
    (e := (LinearMap.toContinuousLinearMap :
      (E →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (E →L[ℝ] ℝ)).symm),
    Submodule.map_span, ← Set.range_comp]
  apply Submodule.span_eq_top_of_ne_zero
  intro v hv
  have hn : mfderiv I 𝓘(ℝ, Fin n → ℝ) F x v ≠ 0 := by
    intro hh
    apply hv
    apply hinj
    exact hh.trans (map_zero _).symm
  obtain ⟨i, hi⟩ : ∃ i, mfderiv I 𝓘(ℝ, Fin n → ℝ) F x v i ≠ 0 := by
    by_contra! hh
    exact hn (funext hh)
  refine ⟨_, mem_range_self i, ?_⟩
  change mfderiv I 𝓘(ℝ, ℝ) (fun y => F y i) x v ≠ 0
  rw [mfderiv_component hF]
  exact hi


theorem exists_supported_map_injective_mfderiv_on_compact {K U : Set M}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ (n : ℕ) (F : M → Fin n → ℝ),
      ContMDiff I 𝓘(ℝ, Fin n → ℝ) ∞ F ∧ HasCompactSupport F ∧ tsupport F ⊆ U ∧
      ∀ x ∈ K, Injective (mfderiv I 𝓘(ℝ, Fin n → ℝ) F x) := by
  classical
  obtain ⟨ι, inst, b, hb⟩ := exists_finite_smoothBumpCovering I hK hU hKU
  let e := (Module.finBasis ℝ (ι → E)).equivFunL
  refine ⟨_, e ∘ localizedChartMap b,
    e.contDiff.contMDiff.comp (contMDiff_localizedChartMap b),
    (hasCompactSupport_localizedChartMap b).comp_left (map_zero e), ?_, ?_⟩
  · exact (tsupport_comp_subset (map_zero e) _).trans
      ((tsupport_localizedChartMap_subset b).trans (iUnion_subset hb))
  · intro x hx
    rw [mfderiv_comp x e.differentiableAt.mdifferentiableAt
      ((contMDiff_localizedChartMap b).mdifferentiableAt (by simp)), e.mfderiv_eq]
    exact e.injective.comp (injective_mfderiv_localizedChartMap b hx)


theorem exists_supported_differentials_span_of_isCompact {K U : Set M}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ (n : ℕ) (φ : Fin n → M → ℝ),
      (∀ i, ContMDiff I 𝓘(ℝ, ℝ) ∞ (φ i) ∧ HasCompactSupport (φ i) ∧ tsupport (φ i) ⊆ U) ∧
      ∀ x ∈ K, Submodule.span ℝ (range (fun i : Fin n =>
        (show TangentSpace I x →L[ℝ] ℝ from mfderiv I 𝓘(ℝ, ℝ) (φ i) x))) = ⊤ := by
  obtain ⟨n, F, hF, hFc, hFU, hFinj⟩ := exists_supported_map_injective_mfderiv_on_compact (I := I) hK hU hKU
  refine ⟨n, fun i y => F y i, fun i => ?_, fun x hx => ?_⟩
  · let L : (Fin n → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj i
    exact ⟨L.contDiff.contMDiff.comp hF,
      hFc.comp_left (map_zero L), (tsupport_comp_subset (map_zero L) F).trans hFU⟩
  · exact span_mfderiv_components_of_injective (hF.mdifferentiableAt (by simp)) (hFinj x hx)

end Poincare.Morse
