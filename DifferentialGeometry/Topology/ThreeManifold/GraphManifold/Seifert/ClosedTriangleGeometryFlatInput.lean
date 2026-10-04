import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CompactFoldSpec

/-!
# CF's fold datum on a flat triangle, read in the flat chart

Lane B3 (design `docs/geometrization/handoffs/20261004-design-b3-closed-triangle-assembly.md`,
§6, with review 27: the fold input is CF's `CompactShape.FoldData`, here for
`σ.toCompactShape` of a flat `EuclidShape σ`). The fields of a fold datum `D` are restated with the
explicit flat triangle, reflections, rotated disc coordinates and vertices of `σ`
(`D.triangle_diff_subset_U'`, `D.foldWall_diff_subset_V'`, `D.f_refl'`, `D.refl_mapsTo_V'`,
`D.bijOn_f'`, `D.f_apexOne'`, `D.f_apexTwo'`, `D.det_fderiv_pos'`): the apex germs hold on the
full Euclidean discs `‖z - vⱼ‖ < apexRadius`, the outer germ on the punctured disc about `0`.
-/

set_option autoImplicit false

noncomputable section
open Set Complex
open scoped ComplexConjugate ContDiff

namespace GC.Seifert

namespace ClosedTriangle

variable {σ : EuclidShape} (D : σ.toCompactShape.FoldData)

theorem toCompactShape_toEuclidShape (σ : EuclidShape) :
    σ.toCompactShape.toEuclidShape rfl = σ := rfl

theorem triangle_diff_subset_U' : σ.triangle \ {0} ⊆ D.U := by
  have h := D.triangle_diff_subset_U
  rwa [CompactShape.triangle_flat rfl] at h

theorem foldWall_diff_subset_V' (i : Fin 3) :
    {z | z ∈ σ.triangle ∧ σ.wallSide i z = 0} \ {0} ⊆ D.V i := by
  have h := D.foldWall_diff_subset_V i
  rwa [CompactShape.foldWall_flat rfl] at h

theorem f_refl' (i : Fin 3) {z : ℂ} (hz : z ∈ D.V i) : D.f (σ.refl i z) = conj (D.f z) := by
  have h := D.f_refl i z hz
  rwa [CompactShape.refl_flat rfl] at h

theorem refl_mapsTo_V' (i : Fin 3) : MapsTo (σ.refl i) (D.V i) (D.V i) := by
  intro z hz
  have h := D.refl_mapsTo_V i hz
  rwa [CompactShape.refl_flat rfl] at h

theorem bijOn_f' : BijOn D.f (σ.triangle \ {0}) basePlusSeven := by
  have h := D.bijOn_f
  rwa [CompactShape.triangle_flat rfl] at h

theorem det_fderiv_pos' {z : ℂ} (hz : z ∈ D.U) (h1 : z ≠ σ.vertexOne) (h2 : z ≠ σ.vertexTwo) :
    0 < (fderiv ℝ D.f z).det := by
  refine D.det_fderiv_pos z hz ?_ ?_
  · rwa [CompactShape.vertexOne_flat rfl]
  · rwa [CompactShape.vertexTwo_flat rfl]

theorem f_apexOne' {z : ℂ} (hz : ‖z - σ.vertexOne‖ < D.apexRadius 0) :
    z ∈ D.U ∧ D.f z = σ.apexOne z := by
  have hm : z ∈ σ.toCompactShape.apexDisc σ.toCompactShape.vertexOne (D.apexRadius 0) := by
    rw [CompactShape.apexDisc_flat rfl, CompactShape.vertexOne_flat rfl]
    exact hz
  obtain ⟨hU, hf⟩ := D.f_apexOne z hm
  refine ⟨hU, ?_⟩
  rw [hf, CompactShape.rotOne_flat rfl]
  rfl

theorem f_apexTwo' {z : ℂ} (hz : ‖z - σ.vertexTwo‖ < D.apexRadius 1) :
    z ∈ D.U ∧ D.f z = σ.apexTwo z := by
  have hm : z ∈ σ.toCompactShape.apexDisc σ.toCompactShape.vertexTwo (D.apexRadius 1) := by
    rw [CompactShape.apexDisc_flat rfl, CompactShape.vertexTwo_flat rfl]
    exact hz
  obtain ⟨hU, hf⟩ := D.f_apexTwo z hm
  refine ⟨hU, ?_⟩
  rw [hf, CompactShape.rotTwo_flat rfl]
  rfl

theorem f_outer' {z : ℂ} (h0 : 0 < ‖z‖) (hz : ‖z‖ < D.apexRadius 2) :
    z ∈ D.U ∧ D.f z = compactOuterGerm σ.p₃ z :=
  D.f_outer z h0 hz

theorem continuousAt_f {z : ℂ} (hz : z ∈ D.U) : ContinuousAt D.f z :=
  (D.contDiffOn_f.continuousOn.continuousAt (D.isOpen_U.mem_nhds hz))

end ClosedTriangle

end GC.Seifert
