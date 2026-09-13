import Mathlib.Topology.MetricSpace.Holder
import Mathlib.Topology.ExtendFrom
import Mathlib.Topology.UniformSpace.Cauchy

noncomputable section
open Set Filter
open scoped Topology NNReal

theorem HolderOnWith.closure
    {X Y : Type*} [PseudoEMetricSpace X] [PseudoEMetricSpace Y]
    {s : Set X} {f : X → Y} {K α : ℝ≥0}
    (hf : HolderOnWith K α f s) (hc : ContinuousOn f (_root_.closure s)) :
    HolderOnWith K α f (_root_.closure s) := by
  have := ENNReal.continuous_const_mul (ENNReal.coe_ne_top (r := K))
  have := @ENNReal.continuous_rpow_const (α : ℝ)
  refine fun x hx y hy => le_on_closure
    (fun y hy => le_on_closure (fun x hx => hf x hx y hy) ?_ ?_ hx) ?_ ?_ hy
  all_goals fun_prop

private theorem continuousOn_extendFrom_of_uniformContinuousOn
    {X Y : Type*} [UniformSpace X] [UniformSpace Y] [CompleteSpace Y]
    {s : Set X} {f : X → Y} (hf : UniformContinuousOn f s) :
    ContinuousOn (_root_.extendFrom s f) (_root_.closure s) := by
  apply continuousOn_extendFrom Subset.rfl
  intro x hx
  have hn : NeBot (𝓝[s] x) := mem_closure_iff_nhdsWithin_neBot.mp hx
  exact CompleteSpace.complete ((cauchy_nhds.mono' hn nhdsWithin_le_nhds).map_of_le hf
    inf_le_right)

theorem HolderOnWith.extendFrom
    {X Y : Type*} [PseudoEMetricSpace X] [EMetricSpace Y] [CompleteSpace Y]
    {s : Set X} {f : X → Y} {K α : ℝ≥0}
    (hf : HolderOnWith K α f s) (hα : 0 < α) :
    HolderOnWith K α (_root_.extendFrom s f) (_root_.closure s) ∧ EqOn (_root_.extendFrom s f) f s := by
  have he := extendFrom_extends (hf.continuousOn hα)
  refine ⟨?_, he⟩
  apply HolderOnWith.closure (hc :=
    continuousOn_extendFrom_of_uniformContinuousOn (hf.uniformContinuousOn hα))
  intro x hx y hy
  simpa only [he x hx, he y hy] using hf x hx y hy
