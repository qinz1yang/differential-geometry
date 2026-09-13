import DifferentialGeometry.Topology.Morse.Defs
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Topology.DiscreteSubset

open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.Topology.Morse

noncomputable section

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem exists_nhds_fderiv_injOn [FiniteDimensional ℝ E]
    {g : E → ℝ} {a : E} (hg : ContDiffAt ℝ 2 g a)
    (hnd : (QuadraticMap.associated (R := ℝ) (chartHessianAt g a)).SeparatingLeft) :
    ∃ s ∈ nhds a, Set.InjOn (fderiv ℝ g) s := by
  have hsymm : ∀ u v, chartHessianBilinAt g a u v = chartHessianBilinAt g a v u := by
    intro u v
    exact (hg.isSymmSndFDerivAt (by norm_num [minSmoothness])).eq u v
  have hB : QuadraticMap.associated (R := ℝ) (chartHessianAt g a) =
      chartHessianBilinAt g a :=
    QuadraticMap.associated_left_inverse ℝ hsymm
  have hinj : Function.Injective (fderiv ℝ (fderiv ℝ g) a) := by
    apply (injective_iff_map_eq_zero (fderiv ℝ (fderiv ℝ g) a)).2
    intro u hu
    apply hnd u
    intro v
    rw [hB]
    change fderiv ℝ (fderiv ℝ g) a u v = 0
    rw [hu]
    rfl
  have hdim : Module.finrank ℝ E = Module.finrank ℝ (E →L[ℝ] ℝ) := by
    calc
      Module.finrank ℝ E = Module.finrank ℝ (Module.Dual ℝ E) := (Subspace.dual_finrank_eq).symm
      _ = Module.finrank ℝ (E →L[ℝ] ℝ) :=
        (LinearMap.toContinuousLinearMap : (E →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (E →L[ℝ] ℝ)).finrank_eq
  let L : E ≃L[ℝ] (E →L[ℝ] ℝ) :=
    ((fderiv ℝ (fderiv ℝ g) a).toLinearMap.linearEquivOfInjective hinj hdim).toContinuousLinearEquiv
  have hstrict : HasStrictFDerivAt (fderiv ℝ g) (L : E →L[ℝ] (E →L[ℝ] ℝ)) a := by
    exact (hg.fderiv_right (m := 1) (by norm_num)).hasStrictFDerivAt (by norm_num)
  let e := hstrict.toOpenPartialHomeomorph (fderiv ℝ g)
  exact ⟨e.source, e.open_source.mem_nhds hstrict.mem_toOpenPartialHomeomorph_source, e.injOn⟩

variable {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
variable (I : ModelWithCorners ℝ E H) [I.Boundaryless]

private theorem contDiffAt_chart {n : WithTop ℕ∞} [IsManifold I n M]
    {f : M → ℝ} {p : M} (hf : ContMDiffAt I 𝓘(ℝ, ℝ) n f p) :
    ContDiffAt ℝ n (fun y => f ((extChartAt I p).symm y)) (extChartAt I p p) := by
  have hs : ContMDiffAt 𝓘(ℝ, E) I n (extChartAt I p).symm (extChartAt I p p) :=
    (contMDiffOn_extChartAt_symm p).contMDiffAt
      ((isOpen_extChartAt_target p).mem_nhds
        ((extChartAt I p).map_source (mem_extChartAt_source p)))
  have hfep : ContMDiffAt I 𝓘(ℝ, ℝ) n f ((extChartAt I p).symm (extChartAt I p p)) := by
    simpa only [extChartAt_to_inv] using hf
  exact contMDiffAt_iff_contDiffAt.mp (hfep.comp (extChartAt I p p) hs)

private theorem mfderiv_eq_chart_fderiv
    {f : M → ℝ} {p : M} (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f p) :
    mfderiv I 𝓘(ℝ, ℝ) f p =
      fderiv ℝ (fun y => f ((extChartAt I p).symm y)) (extChartAt I p p) := by
  classical
  change (if MDifferentiableAt I 𝓘(ℝ, ℝ) f p then
    fderivWithin ℝ (writtenInExtChartAt I 𝓘(ℝ, ℝ) p f) (Set.range I) (extChartAt I p p)
    else (0 : E →L[ℝ] ℝ)) = _
  rw [if_pos hf, I.range_eq_univ, fderivWithin_univ]
  rfl

private theorem chart_fderiv_eq_zero_of_critical [IsManifold I 1 M]
    {f : M → ℝ} (p q : M) (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f q)
    (hq : q ∈ (extChartAt I p).source) (hcrit : IsCriticalPointAt I f q) :
    fderiv ℝ (fun y => f ((extChartAt I p).symm y)) (extChartAt I p q) = 0 := by
  have hinv : (extChartAt I p).symm (extChartAt I p q) = q := (extChartAt I p).left_inv hq
  have hs : MDifferentiableAt 𝓘(ℝ, E) I (extChartAt I p).symm (extChartAt I p q) :=
    ((contMDiffOn_extChartAt_symm p).contMDiffAt
      ((isOpen_extChartAt_target p).mem_nhds ((extChartAt I p).map_source hq))).mdifferentiableAt
      (n := 1) one_ne_zero
  have hfq : MDifferentiableAt I 𝓘(ℝ, ℝ) f
      ((extChartAt I p).symm (extChartAt I p q)) :=
    hinv.symm ▸ hf
  have hc := mfderiv_comp (extChartAt I p q) hfq hs
  rw [hinv, hcrit] at hc
  simp only [mfderiv_eq_fderiv] at hc
  change fderiv ℝ (f ∘ (extChartAt I p).symm) (extChartAt I p q) =
    (0 : E →L[ℝ] ℝ).comp
      (mfderiv 𝓘(ℝ, E) I (extChartAt I p).symm (extChartAt I p q)) at hc
  exact hc.trans (by ext v; rfl)

private theorem eventually_not_isCriticalPointAt [IsManifold I 1 M]
    {f : M → ℝ} {p : M} (hf : ContMDiffAt I 𝓘(ℝ, ℝ) 1 f p)
    (hp : ¬ IsCriticalPointAt I f p) :
    ∀ᶠ q in nhds p, ¬ IsCriticalPointAt I f q := by
  have hne : fderiv ℝ (fun y => f ((extChartAt I p).symm y)) (extChartAt I p p) ≠ 0 := by
    intro hz
    apply hp
    exact (mfderiv_eq_chart_fderiv I (hf.mdifferentiableAt one_ne_zero)).trans hz
  have hc := ((contDiffAt_chart I hf).fderiv_right (m := 0) (by norm_num)).continuousAt
  have hc' := hc.comp (continuousAt_extChartAt (I := I) p)
  have hev := hc'.eventually (isOpen_compl_singleton.mem_nhds hne)
  have hnear : ∀ᶠ q in nhds p, ContMDiffAt I 𝓘(ℝ, ℝ) 1 f q :=
    (contMDiffAt_iff_contMDiffAt_nhds (by norm_num)).mp hf
  filter_upwards [hev, extChartAt_source_mem_nhds (I := I) p, hnear] with q hq hsrc hfq
  intro hcrit
  exact hq (chart_fderiv_eq_zero_of_critical I p q (hfq.mdifferentiableAt one_ne_zero) hsrc hcrit)

theorem isClosed_setOf_isCriticalPointAt [IsManifold I 1 M]
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 1 f) :
    IsClosed {p | IsCriticalPointAt I f p} := by
  rw [← isOpen_compl_iff]
  exact isOpen_iff_mem_nhds.mpr fun p hp => eventually_not_isCriticalPointAt I (hf p) hp

theorem IsNondegenerateCriticalPointAt.isolated [FiniteDimensional ℝ E] [IsManifold I 2 M]
    {f : M → ℝ} {p : M} (hf : ContMDiffAt I 𝓘(ℝ, ℝ) 2 f p)
    (hnd : IsNondegenerateCriticalPointAt I f p) :
    ∀ᶠ q in nhds p, IsCriticalPointAt I f q → q = p := by
  obtain ⟨s, hs, hinj⟩ := exists_nhds_fderiv_injOn (contDiffAt_chart I hf) hnd.2
  have hs' := (continuousAt_extChartAt (I := I) p).preimage_mem_nhds hs
  have hp : extChartAt I p p ∈ s := mem_of_mem_nhds hs
  have hf1 : ContMDiffAt I 𝓘(ℝ, ℝ) 1 f p := hf.of_le (by norm_num)
  have hnear : ∀ᶠ q in nhds p, ContMDiffAt I 𝓘(ℝ, ℝ) 1 f q :=
    (contMDiffAt_iff_contMDiffAt_nhds (by norm_num)).mp hf1
  filter_upwards [hs', extChartAt_source_mem_nhds (I := I) p, hnear] with q hq hsrc hfq
  intro hcrit
  apply (extChartAt I p).injOn hsrc (mem_extChartAt_source p)
  apply hinj hq hp
  rw [chart_fderiv_eq_zero_of_critical I p q (hfq.mdifferentiableAt one_ne_zero) hsrc hcrit,
    chart_fderiv_eq_zero_of_critical I p p (hf1.mdifferentiableAt one_ne_zero)
      (mem_extChartAt_source p) hnd.1]

theorem finite_critical_points_of_isCompact [FiniteDimensional ℝ E] [IsManifold I 2 M]
    {f : M → ℝ} {K : Set M} (hK : IsCompact K)
    (hf : ∀ p ∈ K, ContMDiffAt I 𝓘(ℝ, ℝ) 2 f p)
    (hnd : ∀ p ∈ K, IsCriticalPointAt I f p → IsNondegenerateCriticalPointAt I f p) :
    {p ∈ K | IsCriticalPointAt I f p}.Finite := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hc : IsClosed {p : K | IsCriticalPointAt I f p} := by
    rw [← isOpen_compl_iff]
    apply isOpen_iff_mem_nhds.mpr
    intro p hp
    exact continuous_subtype_val.continuousAt.eventually
      (eventually_not_isCriticalPointAt I ((hf p p.property).of_le (by norm_num)) hp)
  have hcompact : IsCompact {p ∈ K | IsCriticalPointAt I f p} := by
    convert hc.isCompact.image continuous_subtype_val using 1
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_image, Subtype.exists, exists_and_right,
      exists_eq_right]
    tauto
  apply hcompact.finite
  apply IsDiscrete.of_nhdsWithin
  intro p hp
  rw [Filter.le_pure_iff]
  filter_upwards [((hnd p hp.1 hp.2).isolated I (hf p hp.1)).filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with q hq hcrit
  exact hq hcrit.2

theorem finite_critical_points [FiniteDimensional ℝ E] [IsManifold I 2 M] [CompactSpace M]
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f)
    (hnd : ∀ p, IsCriticalPointAt I f p → IsNondegenerateCriticalPointAt I f p) :
    {p | IsCriticalPointAt I f p}.Finite := by
  simpa only [Set.mem_univ, true_and] using finite_critical_points_of_isCompact I
    isCompact_univ (fun p _ => hf p) (fun p _ => hnd p)

end
end DifferentialGeometry.Topology.Morse
