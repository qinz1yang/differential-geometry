import DifferentialGeometry.Topology.Manifold.InverseFunctionTheorem.Basic
import DifferentialGeometry.Analysis.Calculus.Inverse.LocalInverse
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

noncomputable section
open scoped ContDiff Manifold Topology

namespace Poincare.Topology.Manifold

variable {E F H H' M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] [TopologicalSpace H']
  [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace H' N]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
  [I.Boundaryless] [J.Boundaryless] [IsManifold I ∞ M] [IsManifold J ∞ N]

private def extendedChart (I : ModelWithCorners ℝ E H) [I.Boundaryless] (x : M) :
    OpenPartialHomeomorph M E where
  toPartialEquiv := extChartAt I x
  open_source := isOpen_extChartAt_source x
  open_target := isOpen_extChartAt_target x
  continuousOn_toFun := continuousOn_extChartAt x
  continuousOn_invFun := continuousOn_extChartAt_symm x

theorem isLocalDiffeomorphAt_of_hasMFDerivAt_equiv
    (f : M → N) (hf : ContMDiff I J ∞ f) (x₀ : M)
    (A : E ≃L[ℝ] F) (hdf : HasMFDerivAt I J f x₀ (A : E →L[ℝ] F)) :
    IsLocalDiffeomorphAt I J ∞ f x₀ := by
  let cM := extendedChart I x₀
  let cN := extendedChart J (f x₀)
  let g : E → F := cN ∘ f ∘ cM.symm
  let U := cM.target ∩ cM.symm ⁻¹' (f ⁻¹' cN.source)
  have hU : IsOpen U := cM.isOpen_inter_preimage_symm
    (cN.open_source.preimage hf.continuous)
  have hxM : x₀ ∈ cM.source := mem_extChartAt_source x₀
  have hxN : f x₀ ∈ cN.source := mem_extChartAt_source (f x₀)
  have hxU : cM x₀ ∈ U := by
    refine ⟨cM.map_source hxM, ?_⟩
    change f (cM.symm (cM x₀)) ∈ cN.source
    rw [cM.left_inv hxM]
    exact hxN
  have hg : ContDiffOn ℝ ∞ g U := by
    rw [← contMDiffOn_iff_contDiffOn]
    exact (contMDiffOn_extChartAt (I := J) (x := f x₀)).comp
      (hf.comp_contMDiffOn ((contMDiffOn_extChartAt_symm x₀).mono Set.inter_subset_left))
      (fun z hz ↦ by
        have hm : f (cM.symm z) ∈ (extChartAt J (f x₀)).source := hz.2
        change f (cM.symm z) ∈ (chartAt H' (f x₀)).source
        simpa only [extChartAt_source] using hm)
  have hd : HasFDerivAt g (A : E →L[ℝ] F) (cM x₀) := by
    have hw : HasFDerivWithinAt g (A : E →L[ℝ] F) (Set.range I) (cM x₀) := hdf.2
    exact hw.hasFDerivAt (by rw [I.range_eq_univ]; exact Filter.univ_mem)
  obtain ⟨e, hxe, heU, he, heinv, heq⟩ :=
    Poincare.Analysis.exists_localInverse_of_hasFDerivAt_equiv hg hU hxU hd
  let φ := (cM.trans e).trans cN.symm
  have hφ : ContMDiffOn I J ∞ φ φ.source := by
    apply (contMDiffOn_extChartAt_symm (I := J) (f x₀)).comp
    · exact he.contMDiffOn.comp
        ((contMDiffOn_extChartAt (I := I) (x := x₀)).mono
          (fun z hz ↦ by
            have hm : z ∈ (extChartAt I x₀).source := hz.1.1
            simpa only [extChartAt_source] using hm)) (fun z hz ↦ hz.1.2)
    · exact fun z hz ↦ hz.2
  have hφinv : ContMDiffOn J I ∞ φ.symm φ.target := by
    apply (contMDiffOn_extChartAt_symm (I := I) x₀).comp
    · exact heinv.contMDiffOn.comp
        ((contMDiffOn_extChartAt (I := J) (x := f x₀)).mono
          (fun z hz ↦ by
            have hm : z ∈ (extChartAt J (f x₀)).source := hz.1
            simpa only [extChartAt_source] using hm)) (fun z hz ↦ hz.2.1)
    · exact fun z hz ↦ hz.2.2
  let Φ : PartialDiffeomorph I J M N ∞ :=
    { toPartialEquiv := φ.toPartialEquiv
      open_source := φ.open_source
      open_target := φ.open_target
      contMDiffOn_toFun := hφ
      contMDiffOn_invFun := hφinv }
  refine ⟨Φ, ?_, ?_⟩
  · refine ⟨⟨hxM, hxe⟩, ?_⟩
    change e (cM x₀) ∈ cN.target
    rw [heq]
    change cN (f (cM.symm (cM x₀))) ∈ cN.target
    rw [cM.left_inv hxM]
    exact cN.map_source hxN
  · intro z hz
    change f z = cN.symm (e (cM z))
    rw [heq]
    change f z = cN.symm (cN (f (cM.symm (cM z))))
    rw [cM.left_inv hz.1.1]
    have hsource := (heU hz.1.2).2
    change f (cM.symm (cM z)) ∈ cN.source at hsource
    rw [cM.left_inv hz.1.1] at hsource
    exact (cN.left_inv hsource).symm

end Poincare.Topology.Manifold

open Manifold Set Topology

namespace Poincare.Topology

theorem isLocalDiffeomorphAt_of_contMDiffOn_of_isInvertible_mfderiv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G} [J.Boundaryless]
    {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]
    {f : M → N} {U : Set M} {x : M} (hU : IsOpen U) (hx : x ∈ U)
    (hf : ContMDiffOn I J ∞ f U) (hinv : (mfderiv I J f x).IsInvertible) :
    IsLocalDiffeomorphAt I J ∞ f x := by
  have hmd : MDifferentiableAt I J f x :=
    (hf.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp)
  have hcoord : (fderiv ℝ (writtenInExtChartAt I J x f) (extChartAt I x x)).IsInvertible := by
    rwa [hmd.mfderiv, I.range_eq_univ, fderivWithin_univ] at hinv
  obtain ⟨Φ, hxΦ, hΦU, heq⟩ :=
    DifferentialGeometry.Coordinates.exists_partialDiffeomorph_of_contMDiffOn
      (n := 1) le_rfl (by exact_mod_cast (WithTop.one_ne_top : (1 : ℕ∞) ≠ ⊤))
      hU hx (hf.of_le (by simp)) hcoord
  have hregular : ∀ y ∈ Φ.source,
      (fderiv ℝ (writtenInExtChartAt I J y f) (extChartAt I y y)).IsInvertible := by
    intro y hy
    have hd : IsLocalDiffeomorphAt I J 1 f y := ⟨Φ, hy, heq⟩
    have hinv' : (mfderiv I J f y).IsInvertible :=
      ⟨hd.mfderivToContinuousLinearEquiv one_ne_zero, rfl⟩
    rwa [(hd.mdifferentiableAt one_ne_zero).mfderiv, I.range_eq_univ,
      fderivWithin_univ] at hinv'
  obtain ⟨Ψ, hxΨ, _, hΨ⟩ :=
    DifferentialGeometry.Coordinates.exists_partialDiffeomorph_of_contMDiffOn_infty
      Φ.open_source hxΦ (hf.mono hΦU) hregular
  exact ⟨Ψ, hxΨ, hΨ⟩

end Poincare.Topology

namespace Poincare.Manifold

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem exists_partialDiffeomorph_of_contDiffAt {f : E → F} {p : E}
    (A : E ≃L[ℝ] F) (hf : ContDiffAt ℝ 1 f p)
    (hD : HasFDerivAt f A.toContinuousLinearMap p) :
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) E F 1,
      p ∈ Φ.source ∧ (Φ : E → F) = f := by
  let e := hf.toOpenPartialHomeomorph f hD (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
  have hp : p ∈ e.source := hf.mem_toOpenPartialHomeomorph_source hD (by norm_num)
  obtain ⟨U, hU, hcU⟩ := hf.contDiffOn (m := 1) le_rfl (by norm_num)
  have hi : ContDiffAt ℝ 1 e.symm (e p) := hf.to_localInverse hD (by norm_num)
  obtain ⟨V, hV, hcV⟩ := hi.contDiffOn (m := 1) le_rfl (by norm_num)
  let s : Set E := U ∩ e ⁻¹' V
  have hs : s ∈ 𝓝 p := Filter.inter_mem hU ((e.continuousAt hp).preimage_mem_nhds hV)
  let e' := e.restr s
  have hsub : e'.source ⊆ U := fun x hx ↦ (interior_subset hx.2).1
  have ht : e'.target ⊆ V := by
    intro y hy
    have hh := e'.map_target hy
    have hv : e (e'.symm y) ∈ V := (interior_subset hh.2).2
    exact (e'.right_inv hy) ▸ hv
  let Φ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) E F 1 := {
    toPartialEquiv := e'.toPartialEquiv
    open_source := e'.open_source
    open_target := e'.open_target
    contMDiffOn_toFun := (hcU.mono hsub).contMDiffOn
    contMDiffOn_invFun := (hcV.mono ht).contMDiffOn }
  refine ⟨Φ, ⟨hp, mem_interior_iff_mem_nhds.mpr hs⟩, rfl⟩

end Poincare.Manifold
