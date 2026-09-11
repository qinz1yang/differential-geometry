import DifferentialGeometry.Geometry.Boundary.ModelInverse
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

noncomputable section
open Set Filter Topology Manifold
open scoped ContDiff

namespace DifferentialGeometry.Geometry.Boundary

open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary

variable {E H M F G N E' H' P : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H} [HasSmoothBoundary E H I] [IsManifold I ∞ M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace G] [TopologicalSpace N] [ChartedSpace G N]
  {J : ModelWithCorners ℝ F G} [IsManifold J ∞ N]
  [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [TopologicalSpace H'] [TopologicalSpace P] [ChartedSpace H' P]
  {K : ModelWithCorners ℝ E' H'}

set_option backward.isDefEq.respectTransparency false in
private theorem factorization_euclidean
    {f : M → F} {S : Set M} {g : P → M} {z : P}
    (hS : IsOpen S) (hz : g z ∈ S) (hf : ContMDiffOn I 𝓘(ℝ, F) ∞ f S)
    (hinj : Function.Injective (mfderiv I 𝓘(ℝ, F) f (g z)))
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F)
    (hg : ContinuousAt g z) (hfg : ContMDiffAt K 𝓘(ℝ, F) ∞ (f ∘ g) z) :
    ContMDiffAt K I ∞ g z := by
  let x := g z
  let p := extChartAt I x
  let D := p.target ∩ p.symm ⁻¹' S
  have hpx : p x ∈ p.target := mem_extChartAt_target x
  have hDx : D ∈ 𝓝[range I] p x := by
    apply inter_mem (extChartAt_target_mem_nhdsWithin x)
    apply mem_nhdsWithin_of_mem_nhds
    have hh := (continuousAt_extChartAt_symm (I := I) x).preimage_mem_nhds
      (hS.mem_nhds (by simpa only [extChartAt_to_inv] using hz))
    simpa only [p, extChartAt_to_inv] using hh
  obtain ⟨U, hU, hxU, hUD⟩ := mem_nhdsWithin.mp hDx
  have hcoords : ContDiffOn ℝ ∞ (f ∘ p.symm) (U ∩ range I) := by
    apply ContMDiffOn.contDiffOn
    apply hf.comp ((contMDiffOn_extChartAt_symm x).mono (fun y hy ↦ (hUD hy).1))
    exact fun y hy ↦ (hUD hy).2
  have hdf := (hf.contMDiffAt (hS.mem_nhds hz)).mdifferentiableAt (by simp)
  have hinj' : Function.Injective (fderivWithin ℝ (f ∘ p.symm) (range I) (p x)) := by
    rw [hdf.mfderiv] at hinj
    simp only [writtenInExtChartAt, extChartAt_model_space_eq_id, PartialEquiv.refl_coe,
      Function.id_comp] at hinj
    intro v w hvw
    exact hinj hvw
  obtain ⟨e, hxe, _, _, hi, heq⟩ := exists_localInverse_of_model I hU hxU
    (extChartAt_target_subset_range x hpx) hcoords hinj' hdim
  have hefx : e (p x) = f x := by
    rw [heq ⟨hxe, extChartAt_target_subset_range x hpx⟩]
    simp only [Function.comp_apply, p, extChartAt_to_inv]
  have hfe : f x ∈ e.target := hefx ▸ e.map_source hxe
  have hcoord : ContMDiffAt K 𝓘(ℝ, E) ∞ (e.symm ∘ (f ∘ g)) z :=
    (hi.contDiffAt (e.open_target.mem_nhds hfe)).contMDiffAt.comp z hfg
  have hevent : e.symm ∘ (f ∘ g) =ᶠ[𝓝 z] p ∘ g := by
    have hpg : ContinuousAt (p ∘ g) z := (continuousAt_extChartAt x).comp hg
    filter_upwards [hpg.preimage_mem_nhds (e.open_source.mem_nhds hxe),
      hg.preimage_mem_nhds (extChartAt_source_mem_nhds (I := I) x)] with w hwe hwp
    have hwI := extChartAt_target_subset_range x (p.map_source hwp)
    have hh := heq ⟨hwe, hwI⟩
    simp only [Function.comp_apply, p.left_inv hwp] at hh
    change e.symm (f (g w)) = p (g w)
    rw [← hh]
    exact e.left_inv hwe
  exact contMDiffAt_iff_target.mpr ⟨hg, hcoord.congr_of_eventuallyEq hevent.symm⟩

set_option backward.isDefEq.respectTransparency false in
theorem contMDiffAt_iff_comp_of_injective_mfderiv
    {f : M → N} (hf : ContMDiff I J ∞ f) {g : P → M} {z : P}
    (hinj : Function.Injective (mfderiv I J f (g z)))
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F) :
    ContMDiffAt K I ∞ g z ↔ ContinuousAt g z ∧ ContMDiffAt K J ∞ (f ∘ g) z := by
  constructor
  · exact fun hg ↦ ⟨hg.continuousAt, hf.contMDiffAt.comp z hg⟩
  · rintro ⟨hg, hfg⟩
    let q := extChartAt J (f (g z))
    let S := f ⁻¹' q.source
    have hS : IsOpen S := (isOpen_extChartAt_source _).preimage hf.continuous
    have hz : g z ∈ S := mem_extChartAt_source _
    have hq : ContMDiffOn J 𝓘(ℝ, F) ∞ q q.source := by
      simpa only [q, extChartAt_source] using contMDiffOn_extChartAt (I := J) (x := f (g z))
    have hqf : ContMDiffOn I 𝓘(ℝ, F) ∞ (q ∘ f) S :=
      hq.comp hf.contMDiffOn (fun _ hx ↦ hx)
    have hqi : Function.Injective (mfderiv J 𝓘(ℝ, F) q (f (g z))) :=
      (isInvertible_mfderiv_extChartAt (mem_extChartAt_source (f (g z)))).bijective.1
    have hqfi : Function.Injective (mfderiv I 𝓘(ℝ, F) (q ∘ f) (g z)) := by
      rw [mfderiv_comp (g z) ((contMDiffAt_extChartAt (n := ∞)).mdifferentiableAt (by simp))
        (hf.mdifferentiableAt (by simp))]
      exact hqi.comp hinj
    exact factorization_euclidean hS hz hqf hqfi hdim hg
      (contMDiffAt_extChartAt.comp z hfg)

theorem contMDiff_iff_comp_of_fullRank_embedding
    {f : M → N} (hf : ContMDiff I J ∞ f) (hemb : IsEmbedding f)
    (hinj : ∀ x, Function.Injective (mfderiv I J f x))
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F) (g : P → M) :
    ContMDiff K I ∞ g ↔ ContMDiff K J ∞ (f ∘ g) := by
  constructor
  · exact hf.comp
  · intro hfg z
    exact (contMDiffAt_iff_comp_of_injective_mfderiv hf (hinj (g z)) hdim).mpr
      ⟨(hemb.continuous_iff.mpr hfg.continuous).continuousAt, hfg z⟩

end DifferentialGeometry.Geometry.Boundary
