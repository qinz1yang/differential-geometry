import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ChildParent
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Solutions.OpenRestriction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Restriction
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Algebra.Order.Group.Pointwise.Interval

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology Pointwise

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness

universe u
variable {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s)

def componentTimeShift (c : ConnectedComponents P.Carrier) :
    SolutionOn (I := ThreeModel) (M := P.componentOpen c)
      (RealTimeInterval.closedOpen 0 (s - a) (sub_pos.mpr G.lt)) := by
  let : CompactSpace (P.componentOpen c) := P.component_compact c
  exact (solutionOnRestrictOpen (G.flow.timeShift a) (P.componentOpen c)).timeRestrict _

theorem componentTimeShift_metric (c : ConnectedComponents P.Carrier) (t : ℝ) :
    (G.componentTimeShift c).base.metric t =
      (G.flow.base.metric (t + a)).restrictOpen (P.componentOpen c) := rfl

theorem componentTimeShift_scalar (c : ConnectedComponents P.Carrier)
    (t : ℝ) (x : P.componentOpen c) :
    (G.componentTimeShift c).scalar t x = G.flow.scalar (t + a) x.val := by
  let : CompactSpace (P.componentOpen c) := P.component_compact c
  exact scalar_restrictOpen (G.flow.timeShift a) (P.componentOpen c) t x

theorem isSolutionOn_componentTimeShift (c : ConnectedComponents P.Carrier) :
    IsSolutionOn (G.componentTimeShift c) := by
  let : CompactSpace (P.componentOpen c) := P.component_compact c
  apply isSolutionOn_timeRestrict _
  · rw [RealTimeInterval.timeShift_closedOpen_carrier]
    exact Subset.rfl
  · rw [RealTimeInterval.timeShift_closedOpen_regular]
    exact Subset.rfl
  · exact isSolutionOn_restrictOpen _ (isSolutionOn_timeShift G.equation a) (P.componentOpen c)

theorem componentTimeShift_scalar_left_derivative (c : ConnectedComponents P.Carrier)
    (t : ℝ) (x : P.componentOpen c) :
    derivWithin (fun u => (G.componentTimeShift c).scalar u x) (Iic t) t =
      derivWithin (fun u => G.flow.scalar u x.val) (Iic (t + a)) (t + a) := by
  simp only [G.componentTimeShift_scalar]
  rw [derivWithin_comp_add_const (fun u => G.flow.scalar u x.val)]
  congr 1
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    change a + y ≤ t + a
    have hy' : y ≤ t := hy
    linarith
  · intro hz
    refine ⟨z - a, ?_, by simp⟩
    change z - a ≤ t
    change z ≤ t + a at hz
    linarith

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab
