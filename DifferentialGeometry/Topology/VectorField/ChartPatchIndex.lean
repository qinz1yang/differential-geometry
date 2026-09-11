import DifferentialGeometry.Topology.VectorField.ChartPatch
import DifferentialGeometry.Topology.VectorField.ContinuousIsolatedZeroGerm
import DifferentialGeometry.Topology.VectorField.InteriorIndexTransport

set_option autoImplicit false
noncomputable section
open Bundle Set Filter
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.VectorField
section General
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H M : Type*} [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H} [IsManifold I 1 M]
  (c : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞)
  (V : ∀ x : M, TangentSpace I x) (W : E → E)

theorem hasContinuousIsolatedZero_patchInCoordinates {x : M} (hx : x ∈ c.source)
    (hW : DifferentialGeometry.LocalDegree.isolatedZero W (c x)) :
    HasContinuousIsolatedZero I (patchInCoordinates c V W) x := by
  have hP := (hasContinuousIsolatedZero_modelSpace_iff.mpr hW).mpullback I 𝓘(ℝ, E)
    c (by simp) hx
  apply hP.congr
  filter_upwards [patchInCoordinates_eventuallyEq_pullback c V W hx] with y hy
  exact (TotalSpace.mk_injective y hy).symm

theorem hasContinuousIsolatedZero_patchInCoordinates_off [T2Space M] {C : Set E}
    (hC : IsCompact C) (hCt : C ⊆ c.target)
    (hagree : ∀ y ∈ c.target \ C,
      W y = _root_.VectorField.mpullback 𝓘(ℝ, E) I c.symm V y)
    {x : M} (hx : x ∉ c.symm '' C) (hV : HasContinuousIsolatedZero I V x) :
    HasContinuousIsolatedZero I (patchInCoordinates c V W) x := by
  apply hV.congr
  filter_upwards [patchInCoordinates_eventuallyEq_self c V W hC hCt hagree hx] with y hy
  exact (TotalSpace.mk_injective y hy).symm

private theorem mdifferentiableAt_model_section {x : E} (hW : DifferentiableAt ℝ W x) :
    MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E).tangent
      (fun y => (⟨y, W y⟩ : TangentBundle 𝓘(ℝ, E) E)) x := by
  erw [mdifferentiableAt_section]
  simpa only [trivializationAt_model_space_apply] using! hW.mdifferentiableAt

theorem mdifferentiableAt_patchInCoordinates {x : M} (hx : x ∈ c.source)
    (hW : DifferentiableAt ℝ W (c x)) :
    MDifferentiableAt I I.tangent
      (fun y => (⟨y, patchInCoordinates c V W y⟩ : TangentBundle I M)) x :=
  (mdifferentiableAt_mpullback_partialDiffeomorph c (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤)) hx
    (mdifferentiableAt_model_section W hW)).congr_of_eventuallyEq
      (patchInCoordinates_eventuallyEq_pullback c V W hx)

theorem det_linearizationAtZero_patchInCoordinates {x : M} (hx : x ∈ c.source)
    (hW : DifferentiableAt ℝ W (c x)) (hz : W (c x) = 0) :
    LinearMap.det (linearizationAtZero (mdifferentiableAt_patchInCoordinates c V W hx hW)
      ((patchInCoordinates_eq_zero_iff c V W hx).mpr hz)).toLinearMap =
        LinearMap.det (fderiv ℝ W (c x)).toLinearMap := by
  have hd := mdifferentiableAt_model_section W hW
  have hP := mdifferentiableAt_mpullback_partialDiffeomorph c (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤)) hx hd
  have hzP := (mpullback_partialDiffeomorph_eq_zero_iff c (by simp) W hx).mpr hz
  rw [linearizationAtZero_congr_of_eventuallyEq
    (mdifferentiableAt_patchInCoordinates c V W hx hW) hP
    ((patchInCoordinates_eq_zero_iff c V W hx).mpr hz) hzP
    (patchInCoordinates_eventuallyEq_pullback c V W hx)]
  rw [det_linearizationAtZero_mpullback_partialDiffeomorph c (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤)) hx hd hz,
    linearizationAtZero_modelSpace_eq_fderiv]
  rfl

end General

section Index
variable {d : ℕ} {H M : Type*} [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin (d + 1))) H) [IsManifold I 1 M]
  (c : PartialDiffeomorph I 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) M
    (EuclideanSpace ℝ (Fin (d + 1))) ∞)
  (V : ∀ x : M, TangentSpace I x)
  (W : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1)))

omit [IsManifold I 1 M] in
private theorem isInteriorPoint_of_mem_chart {x : M} (hx : x ∈ c.source) :
    I.IsInteriorPoint x := by
  have hh := DifferentialGeometry.Manifold.isInteriorPoint_of_model_partialDiffeomorph I ∞ c.symm
    (by simp) (c.map_source hx)
  erw [c.left_inv hx] at hh
  exact hh

theorem interiorIndex_patchInCoordinates {x : M} (hx : x ∈ c.source)
    (hW : DifferentialGeometry.LocalDegree.isolatedZero W (c x)) :
    interiorIndex I (patchInCoordinates c V W) x
      (hasContinuousIsolatedZero_patchInCoordinates c V W hx hW)
      (isInteriorPoint_of_mem_chart I c hx) =
        DifferentialGeometry.LocalDegree.euclideanLocalDegree W (c x) hW := by
  let c₁ : PartialDiffeomorph I 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) M
      (EuclideanSpace ℝ (Fin (d + 1))) 1 :=
    { c with
      contMDiffOn_toFun := c.contMDiffOn_toFun.of_le (by simp)
      contMDiffOn_invFun := c.contMDiffOn_invFun.of_le (by simp) }
  rw [interiorIndex_eq_in_coordinates I
    (hasContinuousIsolatedZero_patchInCoordinates c V W hx hW)
    (isInteriorPoint_of_mem_chart I c hx) c₁ hx]
  apply DifferentialGeometry.LocalDegree.euclideanLocalDegree_congr
  filter_upwards [c.open_target.mem_nhds (c.map_source hx)] with y hy
  exact mpullback_patchInCoordinates c V W hy

theorem interiorIndex_patchInCoordinates_off [T2Space M] {C : Set (EuclideanSpace ℝ (Fin (d + 1)))}
    (hC : IsCompact C) (hCt : C ⊆ c.target)
    (hagree : ∀ y ∈ c.target \ C,
      W y = _root_.VectorField.mpullback 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) I c.symm V y)
    {x : M} (hx : x ∉ c.symm '' C) (hV : HasContinuousIsolatedZero I V x)
    (hIx : I.IsInteriorPoint x) :
    interiorIndex I (patchInCoordinates c V W) x
      (hasContinuousIsolatedZero_patchInCoordinates_off c V W hC hCt hagree hx hV) hIx =
        interiorIndex I V x hV hIx := by
  apply interiorIndex_congr
  filter_upwards [patchInCoordinates_eventuallyEq_self c V W hC hCt hagree hx] with y hy
  exact TotalSpace.mk_injective y hy

end Index
end DifferentialGeometry.VectorField
