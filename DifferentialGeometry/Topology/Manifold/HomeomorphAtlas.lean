import DifferentialGeometry.Topology.Manifold.SmoothOpenCover

noncomputable section
open Set Topology Manifold
open scoped ContDiff

namespace DifferentialGeometry.Topology.Manifold

variable {E H M N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace M] [TopologicalSpace N] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless] [IsManifold I ∞ M]

set_option backward.isDefEq.respectTransparency false in
theorem exists_smoothAtlas_of_homeomorph (h : M ≃ₜ N) :
    ∃ C : ChartedSpace E N, let _ := C
      IsManifold 𝓘(ℝ, E) ∞ N ∧
      ∃ d : Diffeomorph I 𝓘(ℝ, E) M N ∞, (d : M → N) = h := by
  let e : Unit → OpenPartialHomeomorph M N := fun _ ↦ h.toOpenPartialHomeomorph
  have hc : ∀ q, ∃ i, q ∈ (e i).target := fun q ↦ ⟨Unit.unit, mem_univ q⟩
  have hi : ∀ i, (e i).source ⊆ I.interior M :=
    fun _ _ _ ↦ BoundarylessManifold.isInteriorPoint
  have htrans : ∀ i j, ContMDiffOn I I ∞ ((e i).trans (e j).symm)
      ((e i).trans (e j).symm).source := by
    intro i j
    exact contMDiffOn_id.congr (fun x _ ↦ h.symm_apply_apply x)
  obtain ⟨C, hm, hs⟩ := exists_smoothAtlas_of_openCover e hc hi
    (fun _ ↦ ContinuousLinearEquiv.refl ℝ E) htrans
  let := C
  have hfor : ContMDiff I 𝓘(ℝ, E) ∞ h := contMDiffOn_univ.mp (hs Unit.unit).1
  have hback : ContMDiff 𝓘(ℝ, E) I ∞ h.symm := contMDiffOn_univ.mp (hs Unit.unit).2
  exact ⟨C, hm, ⟨h.toEquiv, hfor, hback⟩, rfl⟩

end DifferentialGeometry.Topology.Manifold
