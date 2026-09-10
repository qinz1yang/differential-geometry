import DifferentialGeometry.Topology.VectorField.InteriorIndex
import DifferentialGeometry.Topology.VectorField.IndexTransport

set_option autoImplicit false
open Bundle Filter Set
open scoped Manifold ContDiff Topology
noncomputable section
namespace DifferentialGeometry.VectorField
variable {d : ℕ} {H G M N : Type*} [TopologicalSpace H] [TopologicalSpace G]
  [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace G N]
  (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin (d + 1))) H)
  (J : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin (d + 1))) G)
  [IsManifold I 1 M] [IsManifold J 1 N]

theorem interiorIndex_mpullback_partialDiffeomorph
    (f : PartialDiffeomorph I J M N 1) {x : M} (hx : x ∈ f.source)
    (hIx : I.IsInteriorPoint x) (hJx : J.IsInteriorPoint (f x))
    {V : ∀ y : N, TangentSpace J y} (hV : HasContinuousIsolatedZero J V (f x)) :
    interiorIndex I (_root_.VectorField.mpullback I J f V) x (hV.mpullback I J f le_rfl hx) hIx =
      interiorIndex J V (f x) hV hJx := by
  let c := DifferentialGeometry.Manifold.interiorChart I 1 x
  have hcx : x ∈ c.source := (DifferentialGeometry.Manifold.mem_interiorChart_source_iff I 1 x).mpr hIx
  let e := c.symm.trans f
  have hxe : c x ∈ e.source := by
    refine ⟨c.map_source hcx, ?_⟩
    change c.toPartialEquiv.symm (c x) ∈ f.source
    rw [c.left_inv hcx]
    exact hx
  have hecenter : e (c x) = f x := congrArg f (c.left_inv hcx)
  have hVE : HasContinuousIsolatedZero J V (e (c x)) := hecenter.symm ▸ hV
  have hP := hV.mpullback I J f le_rfl hx
  have hp := hP.in_coordinates I c le_rfl hcx
  have he := hVE.model_pullback J e le_rfl hxe
  have heq : _root_.VectorField.mpullback 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) I
      c.symm (_root_.VectorField.mpullback I J f V) =ᶠ[𝓝 (c x)]
      _root_.VectorField.mpullback 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) J e V := by
    filter_upwards [e.open_source.mem_nhds hxe] with y hy
    have hf := f.mdifferentiableAt one_ne_zero hy.2
    have hc := c.symm.mdifferentiableAt one_ne_zero hy.1
    have hi := isInvertible_mfderiv_partialDiffeomorph f one_ne_zero hy.2
    change _ = _root_.VectorField.mpullback 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) J
      (f ∘ c.symm) V y
    unfold _root_.VectorField.mpullback
    erw [mfderiv_comp y hf hc]
    exact hi.inverse_comp_apply_of_left.symm
  rw [interiorIndex_eq_in_coordinates I hP hIx c hcx]
  have hdegree := (DifferentialGeometry.LocalDegree.euclideanLocalDegree_congr hp he heq).trans
    (interiorIndex_eq_localDegree J e hxe hVE).symm
  simpa only [hecenter] using hdegree

omit J [IsManifold J 1 N] in
theorem interiorIndex_congr {V W : ∀ x : M, TangentSpace I x} {x : M}
    (hV : HasContinuousIsolatedZero I V x) (hW : HasContinuousIsolatedZero I W x)
    (hVW : V =ᶠ[𝓝 x] W) (hIx : I.IsInteriorPoint x) :
    interiorIndex I V x hV hIx = interiorIndex I W x hW hIx := by
  let c := DifferentialGeometry.Manifold.interiorChart I 1 x
  have hx : x ∈ c.source := (DifferentialGeometry.Manifold.mem_interiorChart_source_iff I 1 x).mpr hIx
  have heq : _root_.VectorField.mpullback 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) I c.symm V =ᶠ[𝓝 (c x)]
      _root_.VectorField.mpullback 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) I c.symm W := by
    have hvw : V =ᶠ[𝓝 (c.symm (c x))] W := (c.left_inv hx).symm ▸ hVW
    filter_upwards [(c.symm.toOpenPartialHomeomorph.continuousAt (c.map_source hx)).eventually hvw]
      with y hy
    unfold _root_.VectorField.mpullback
    erw [hy]
    rfl
  rw [interiorIndex_eq_in_coordinates I hV hIx c hx,
    interiorIndex_eq_in_coordinates I hW hIx c hx]
  exact DifferentialGeometry.LocalDegree.euclideanLocalDegree_congr _ _ heq

end DifferentialGeometry.VectorField
