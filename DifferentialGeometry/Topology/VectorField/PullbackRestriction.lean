import DifferentialGeometry.Topology.VectorField.OpenRestriction

set_option autoImplicit false
noncomputable section
open Set Bundle Manifold TopologicalSpace
open scoped ContDiff Topology
namespace DifferentialGeometry.VectorField

theorem mpullback_eq_of_restrict_opens
    {E H M F G N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace G] [TopologicalSpace N] [ChartedSpace G N]
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
    {S U : Opens M} {Y W : Opens N}
    (e : Diffeomorph I J S Y ∞) (d : Diffeomorph I J U W ∞)
    (hUS : U ≤ S) (hd : ∀ q : U, (d q).val = (e ⟨q.val, hUS q.property⟩).val)
    (V : ∀ x : N, TangentSpace J x) (q : U) :
    _root_.VectorField.mpullback I J d (fun y : W => V y.val) q =
      _root_.VectorField.mpullback I J e (fun y : Y => V y.val) ⟨q.val, hUS q.property⟩ := by
  let i : U → S := Opens.inclusion hUS
  have hc : (Subtype.val : W → N) ∘ d = (Subtype.val : Y → N) ∘ e ∘ i := funext hd
  have hdi := (contMDiff_inclusion (I := I) (n := ∞) hUS).mdifferentiable (by simp)
  have hdq := mfderiv_comp q
    ((contMDiff_subtype_val (I := J) (U := W) (n := ∞)).mdifferentiableAt (by simp))
    (d.contMDiff.mdifferentiableAt (by simp))
  have heq := mfderiv_comp q
    (((contMDiff_subtype_val (I := J) (U := Y) (n := ∞)).comp e.contMDiff).mdifferentiableAt (by simp))
    (hdi q)
  have heq' := mfderiv_comp (i q)
    ((contMDiff_subtype_val (I := J) (U := Y) (n := ∞)).mdifferentiableAt (by simp))
    (e.contMDiff.mdifferentiableAt (by simp))
  have hder : (mfderiv I J d q : E →L[ℝ] F) = mfderiv I J e (i q) := by
    rw [DifferentialGeometry.mfderiv_subtype_val] at hdq heq'
    change mfderiv I J ((Subtype.val : W → N) ∘ d) q =
      (ContinuousLinearMap.id ℝ F).comp (mfderiv I J d q) at hdq
    erw [ContinuousLinearMap.id_comp, hc] at hdq
    erw [heq, heq'] at hdq
    simpa only [i, DifferentialGeometry.mfderiv_opens_incl,
      ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id] using! hdq.symm
  change (mfderiv I J d q).inverse (V (d q).val) =
    (mfderiv I J e (i q)).inverse (V (e (i q)).val)
  rw [hder]
  exact congrArg (mfderiv I J e (i q)).inverse (congrArg (fun x => (V x : F)) (hd q))

end DifferentialGeometry.VectorField
