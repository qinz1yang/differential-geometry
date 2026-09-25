import DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.Compact
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SlabJointSmoothness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.IncomingSlabCapBall

noncomputable section

open Set
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

universe u

variable {P : OrientedThreeStage.{u}} {a s : ℝ}

private theorem hasDerivWithinAt_inner (G : P.IncomingSlab a s)
    {t : ℝ} (ht : t ∈ Ico a s) (x : P.Carrier) (v w : TangentSpace ThreeModel x) :
    HasDerivWithinAt (fun r => (G.flow.base.metric r).inner x v w)
      (-2 * ricciTensor (G.flow.base.metric t) x v w) (Ici a) t := by
  rcases eq_or_lt_of_le ht.1 with rfl | hat
  · simpa only [SolutionOn.ricciAt, SolutionFamily.ricciAt,
      metricRicciAt_apply_eq_ricciTensor] using G.hasDerivWithinAt_inner_at_start x v w
  · simpa only [SolutionOn.ricciAt, SolutionFamily.ricciAt,
      metricRicciAt_apply_eq_ricciTensor, SolutionOn.family_metric] using
      (metricDerivAt G.flow G.equation ⟨t, hat, ht.2⟩ x v w).hasDerivWithinAt (s := Ici a)

theorem metric_eq_on_Ico_of_initial {b : ℝ}
    (G : P.IncomingSlab a s) (F : P.IncomingSlab a b)
    (hinit : G.flow.base.metric a = F.flow.base.metric a) :
    ∀ t ∈ Ico a (min s b), G.flow.base.metric t = F.flow.base.metric t := by
  apply ricci_flow_forward_unique_of_joint_contMDiffOn
    G.flow.base.metric F.flow.base.metric (lt_min G.lt F.lt)
  · exact G.smoothUpTo.jointContMDiffOn.mono
      (prod_mono (fun _ ht => ⟨ht.1, ht.2.trans_le (min_le_left s b)⟩) subset_rfl)
  · exact F.smoothUpTo.jointContMDiffOn.mono
      (prod_mono (fun _ ht => ⟨ht.1, ht.2.trans_le (min_le_right s b)⟩) subset_rfl)
  · intro t ht x v w
    exact hasDerivWithinAt_inner G ⟨ht.1, ht.2.trans_le (min_le_left s b)⟩ x v w
  · intro t ht x v w
    exact hasDerivWithinAt_inner F ⟨ht.1, ht.2.trans_le (min_le_right s b)⟩ x v w
  · exact hinit

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab
