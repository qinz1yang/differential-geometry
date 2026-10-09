import DifferentialGeometry.Topology.Manifold.SmoothOrientation
import DifferentialGeometry.Topology.Manifold.OrientationLinearVariation

set_option autoImplicit false
noncomputable section
open Set Function Filter Manifold
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Topology.Manifold
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
variable [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem preferredChartTangentEquiv_eq_coordChange (p x : M)
    (hx : x ∈ (chartAt H p).source) :
    (preferredChartTangentEquiv I p x hx : E →L[ℝ] E) = tangentCoordChange I x p x := by
  have h₁ := TangentBundle.continuousLinearMapAt_trivializationAt (I := I) hx
  have h₂ := TangentBundle.continuousLinearMapAt_trivializationAt_eq_core (I := I) hx
  exact h₁.symm.trans h₂

def preferredChartTransitionEquiv (p q : M)
    (x : ↥((chartAt H p).source ∩ (chartAt H q).source)) : E ≃L[ℝ] E :=
  (preferredChartTangentEquiv I p x.val x.property.1).symm.trans
    (preferredChartTangentEquiv I q x.val x.property.2)

theorem preferredChartTransitionEquiv_apply (p q : M)
    (x : ↥((chartAt H p).source ∩ (chartAt H q).source)) (v : E) :
    preferredChartTransitionEquiv I p q x v = tangentCoordChange I p q x.val v := by
  let e := preferredChartTangentEquiv I p x.val x.property.1
  have hcomp := tangentCoordChange_comp (I := I) (w := x.val) (x := p) (y := q)
    (z := x.val) (v := e.symm v)
    (show x.val ∈ (extChartAt I x.val).source ∩ (extChartAt I p).source ∩
      (extChartAt I q).source from
      ⟨⟨by simp, by simpa only [extChartAt_source] using x.property.1⟩,
        by simpa only [extChartAt_source] using x.property.2⟩)
  have hp := congrArg (fun A : E →L[ℝ] E => A (e.symm v))
    (preferredChartTangentEquiv_eq_coordChange I p x.val x.property.1)
  have hq := congrArg (fun A : E →L[ℝ] E => A (e.symm v))
    (preferredChartTangentEquiv_eq_coordChange I q x.val x.property.2)
  have hp' : tangentCoordChange I x.val p x.val (e.symm v) = v :=
    hp.symm.trans (e.apply_symm_apply v)
  rw [hp'] at hcomp
  exact hq.trans hcomp.symm

theorem continuous_preferredChartTransition (p q : M) :
    Continuous (fun x : ↥((chartAt H p).source ∩ (chartAt H q).source) =>
      (preferredChartTransitionEquiv I p q x : E →L[ℝ] E)) := by
  have h : Continuous (fun x : ↥((chartAt H p).source ∩ (chartAt H q).source) =>
      tangentCoordChange I p q x.val) := by
    apply ContinuousOn.comp_continuous (continuousOn_tangentCoordChange (I := I) p q)
      continuous_subtype_val
    intro x
    simpa only [extChartAt_source] using x.property
  apply h.congr
  intro x
  apply ContinuousLinearMap.ext
  intro v
  exact (preferredChartTransitionEquiv_apply I p q x v).symm

theorem preferredChartTransition_orientation_locallyConstant (p q : M)
    (o : Orientation ℝ E (Fin (Module.finrank ℝ E))) :
    IsLocallyConstant (fun x : ↥((chartAt H p).source ∩ (chartAt H q).source) =>
      Orientation.map _ (preferredChartTransitionEquiv I p q x).toLinearEquiv o) :=
  orientation_map_isLocallyConstant _ (continuous_preferredChartTransition I p q) o

omit [FiniteDimensional ℝ E] in
theorem orientation_map_trans (e f : E ≃ₗ[ℝ] E)
    (o : Orientation ℝ E (Fin (Module.finrank ℝ E))) :
    Orientation.map _ (e.trans f) o = Orientation.map _ f (Orientation.map _ e o) := by
  induction o using Module.Ray.ind with
  | h o ho => rfl

theorem preferredChartTransition_orientation (p q : M)
    (x : ↥((chartAt H p).source ∩ (chartAt H q).source))
    (o : Orientation ℝ E (Fin (Module.finrank ℝ E))) :
    Orientation.map _ (preferredChartTransitionEquiv I p q x).toLinearEquiv
        (Orientation.map _
          (preferredChartTangentEquiv I p x.val x.property.1).toLinearEquiv o) =
      Orientation.map _ (preferredChartTangentEquiv I q x.val x.property.2).toLinearEquiv o := by
  change Orientation.map _
    ((preferredChartTangentEquiv I p x.val x.property.1).toLinearEquiv.symm.trans
      (preferredChartTangentEquiv I q x.val x.property.2).toLinearEquiv)
    (Orientation.map _ (preferredChartTangentEquiv I p x.val x.property.1).toLinearEquiv o) = _
  rw [orientation_map_trans]
  rw [← Orientation.map_symm, Equiv.symm_apply_apply]
end DifferentialGeometry.Topology.Manifold
