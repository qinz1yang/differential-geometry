import DifferentialGeometry.Analysis.Calculus.Inverse.LocalInverse
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

noncomputable section
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Topology.Manifold

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

theorem isLocalDiffeomorphAt_of_contMDiffOn_of_hasMFDerivAt_equiv
    (f : M → N) {U : Set M} (hf : ContMDiffOn I J ∞ f U) (hU : IsOpen U)
    (x₀ : M) (hx₀ : x₀ ∈ U)
    (A : E ≃L[ℝ] F) (hdf : HasMFDerivAt I J f x₀ (A : E →L[ℝ] F)) :
    IsLocalDiffeomorphAt I J ∞ f x₀ := by
  let cM := extendedChart I x₀
  let cN := extendedChart J (f x₀)
  let g : E → F := cN ∘ f ∘ cM.symm
  let D := U ∩ f ⁻¹' cN.source
  have hD : IsOpen D := hf.continuousOn.isOpen_inter_preimage hU cN.open_source
  let W := cM.target ∩ cM.symm ⁻¹' D
  have hW : IsOpen W := cM.isOpen_inter_preimage_symm hD
  have hxM : x₀ ∈ cM.source := mem_extChartAt_source x₀
  have hxN : f x₀ ∈ cN.source := mem_extChartAt_source (f x₀)
  have hxW : cM x₀ ∈ W := by
    refine ⟨cM.map_source hxM, ?_⟩
    change cM.symm (cM x₀) ∈ D
    rw [cM.left_inv hxM]
    exact ⟨hx₀, hxN⟩
  have hg : ContDiffOn ℝ ∞ g W := by
    rw [← contMDiffOn_iff_contDiffOn]
    exact (contMDiffOn_extChartAt (I := J) (x := f x₀)).comp
      (hf.comp ((contMDiffOn_extChartAt_symm x₀).mono Set.inter_subset_left)
        (fun z hz ↦ hz.2.1))
      (fun z hz ↦ by
        have hm : f (cM.symm z) ∈ (extChartAt J (f x₀)).source := hz.2.2
        change f (cM.symm z) ∈ (chartAt H' (f x₀)).source
        simpa only [extChartAt_source] using hm)
  have hd : HasFDerivAt g (A : E →L[ℝ] F) (cM x₀) := by
    have hw : HasFDerivWithinAt g (A : E →L[ℝ] F) (Set.range I) (cM x₀) := hdf.2
    exact hw.hasFDerivAt (by rw [I.range_eq_univ]; exact Filter.univ_mem)
  obtain ⟨e, hxe, heW, he, heinv, heq⟩ :=
    DifferentialGeometry.Analysis.exists_localInverse_of_hasFDerivAt_equiv hg hW hxW hd
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
    have hsource := (heW hz.1.2).2.2
    change f (cM.symm (cM z)) ∈ cN.source at hsource
    rw [cM.left_inv hz.1.1] at hsource
    exact (cN.left_inv hsource).symm

end DifferentialGeometry.Topology.Manifold
