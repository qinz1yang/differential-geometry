import DifferentialGeometry.Topology.Manifold.InverseFunctionTheorem.Basic

set_option autoImplicit false

noncomputable section

open Filter Manifold Set
open scoped Topology ContDiff Manifold

namespace DifferentialGeometry.Geometry.Topology

section Model

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace E]

private theorem eventually_isInvertible_fderiv {G : E → F} {V : Set E} {x : E}
    (hV : IsOpen V) (hx : x ∈ V) (hG : ContDiffOn ℝ ∞ G V)
    (hinv : (fderiv ℝ G x).IsInvertible) :
    ∀ᶠ y in 𝓝 x, (fderiv ℝ G y).IsInvertible := by
  obtain ⟨e, he⟩ := hinv
  have hinv_nhds : {L : E →L[ℝ] F | L.IsInvertible} ∈ 𝓝 (fderiv ℝ G x) := by
    rw [← he]
    exact e.nhds
  exact ((hG.contDiffAt (hV.mem_nhds hx)).continuousAt_fderiv (by simp)).preimage_mem_nhds
    hinv_nhds

end Model

section Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private def smoothExtChart (x : M) : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞ where
  toPartialEquiv := extChartAt I x
  open_source := isOpen_extChartAt_source x
  open_target := isOpen_extChartAt_target x
  contMDiffOn_toFun := by
    simpa only [extChartAt_source] using (contMDiffOn_extChartAt (I := I) (x := x))
  contMDiffOn_invFun := contMDiffOn_extChartAt_symm x

variable [CompleteSpace E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G} [J.Boundaryless]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]
  {f : M → N} {x : M}

theorem isLocalDiffeomorphAt_of_contMDiffOn_of_isInvertible {U : Set M}
    (hU : IsOpen U) (hx : x ∈ U) (hf : ContMDiffOn I J ∞ f U)
    (hinv : (fderiv ℝ (writtenInExtChartAt I J x f) (extChartAt I x x)).IsInvertible) :
    IsLocalDiffeomorphAt I J ∞ f x := by
  let c := smoothExtChart (I := I) x
  let d := smoothExtChart (I := J) (f x)
  let V : Set E := c.target ∩ (c.symm : E → M) ⁻¹' (U ∩ f ⁻¹' d.source)
  let K : E → F := fun z => d (f (c.symm z))
  have hV : IsOpen V :=
    c.symm.contMDiffOn_toFun.continuousOn.isOpen_inter_preimage c.open_target
      (hf.continuousOn.isOpen_inter_preimage hU d.open_source)
  have hxc : x ∈ c.source := mem_extChartAt_source x
  have hcxV : c x ∈ V := by
    refine ⟨c.toPartialEquiv.map_source hxc, ?_⟩
    change c.toPartialEquiv.symm (c.toPartialEquiv x) ∈ U ∩ f ⁻¹' d.source
    rw [c.toPartialEquiv.left_inv hxc]
    exact ⟨hx, mem_extChartAt_source (f x)⟩
  have hK : ContDiffOn ℝ ∞ K V := by
    exact (d.contMDiffOn_toFun.comp
      (hf.comp (c.contMDiffOn_invFun.mono inter_subset_left)
        (fun _ hz => hz.2.1)) (fun _ hz => hz.2.2)).contDiffOn
  have hinvK : (fderiv ℝ K (c x)).IsInvertible := hinv
  have hevent := eventually_isInvertible_fderiv hV hcxV hK hinvK
  have hgood : {z : E | (fderiv ℝ K z).IsInvertible} ∩ V ∈ 𝓝 (c x) :=
    inter_mem hevent (hV.mem_nhds hcxV)
  obtain ⟨W, hWsub, hW, hcxW⟩ := mem_nhds_iff.mp hgood
  apply DifferentialGeometry.Coordinates.isLocalDiffeomorphAt_of_coordinates
    c d hW hxc hcxW
  · intro z hz
    exact (hWsub hz).2.2.2
  · exact hK.mono (fun _ hz => (hWsub hz).2)
  · intro z hz
    exact (hWsub hz).1

theorem isLocalDiffeomorphAt_of_contMDiff_of_hasMFDerivAt
    (hf : ContMDiff I J ∞ f)
    (e : TangentSpace I x ≃L[ℝ] TangentSpace J (f x))
    (hdf : HasMFDerivAt I J f x
      (e : TangentSpace I x →L[ℝ] TangentSpace J (f x))) :
    IsLocalDiffeomorphAt I J ∞ f x := by
  let eModel : E ≃L[ℝ] F := e
  have hchart := hdf.2
  change HasFDerivWithinAt (writtenInExtChartAt I J x f) (eModel : E →L[ℝ] F)
    (range I) (extChartAt I x x) at hchart
  rw [ModelWithCorners.Boundaryless.range_eq_univ, hasFDerivWithinAt_univ] at hchart
  exact isLocalDiffeomorphAt_of_contMDiffOn_of_isInvertible
    isOpen_univ (mem_univ x) hf.contMDiffOn ⟨eModel, hchart.fderiv.symm⟩

end Manifold

end DifferentialGeometry.Geometry.Topology

end
