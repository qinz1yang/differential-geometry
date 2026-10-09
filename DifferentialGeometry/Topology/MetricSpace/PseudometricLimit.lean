import Mathlib.Topology.UniformSpace.Dini
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open Filter Set
open scoped Topology

namespace PseudoMetricSpace

variable {ι X : Type*} {l : Filter ι} [NeBot l]

@[instance_reducible]
noncomputable def ofPointwiseDistLimit (m : ι → PseudoMetricSpace X) (D : X → X → ℝ)
    (hlim : ∀ x y, Tendsto (fun i => @dist X (m i).toDist x y) l (𝓝 (D x y))) :
    PseudoMetricSpace X where
  dist := D
  dist_self x := tendsto_nhds_unique (hlim x x) (by simp only [dist_self]; exact tendsto_const_nhds)
  dist_comm x y := tendsto_nhds_unique (hlim x y) (by
    convert hlim y x using 1
    funext i
    exact @dist_comm X (m i) x y)
  dist_triangle x y z := le_of_tendsto_of_tendsto (hlim x z) ((hlim x y).add (hlim y z))
    (Eventually.of_forall (fun i => @dist_triangle X (m i) x y z))

@[simp] theorem ofPointwiseDistLimit_dist (m : ι → PseudoMetricSpace X) (D : X → X → ℝ)
    (hlim : ∀ x y, Tendsto (fun i => @dist X (m i).toDist x y) l (𝓝 (D x y))) (x y : X) :
    @dist X (ofPointwiseDistLimit m D hlim).toDist x y = D x y := rfl

end PseudoMetricSpace

namespace Metric

variable {ι X : Type*} [Preorder ι] [NeBot (atTop : Filter ι)] [PseudoMetricSpace X]

theorem tendstoUniformlyOn_dist_of_dominated_antitone
    (m : ι → PseudoMetricSpace X) (D : X → X → ℝ)
    (hbound : ∀ i x y, @dist X (m i).toDist x y ≤ dist x y)
    (hanti : ∀ x y, Antitone (fun i => @dist X (m i).toDist x y))
    (hlim : ∀ x y, Tendsto (fun i => @dist X (m i).toDist x y) atTop (𝓝 (D x y)))
    {s : Set X} (hs : IsCompact s) :
    TendstoUniformlyOn (fun i (xy : X × X) => @dist X (m i).toDist xy.1 xy.2)
      (fun xy => D xy.1 xy.2) atTop (s ×ˢ s) := by
  have hLip (i : ι) : LipschitzWith 2 (fun xy : X × X => @dist X (m i).toDist xy.1 xy.2) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have h := @dist_dist_dist_le X (m i) x.1 x.2 y.1 y.2
    have hx := hbound i x.1 y.1
    have hy := hbound i x.2 y.2
    have hmax1 : dist x.1 y.1 ≤ dist x y := le_max_left _ _
    have hmax2 : dist x.2 y.2 ≤ dist x y := le_max_right _ _
    norm_num only [NNReal.coe_ofNat]
    linarith
  have hDLip : LipschitzWith 2 (fun xy : X × X => D xy.1 xy.2) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    exact le_of_tendsto ((hlim x.1 x.2).dist (hlim y.1 y.2))
      (Eventually.of_forall (fun i => (hLip i).dist_le_mul x y))
  exact Antitone.tendstoUniformlyOn_of_forall_tendsto (hs.prod hs)
    (fun i => (hLip i).continuous.continuousOn)
    (fun xy _ => hanti xy.1 xy.2) hDLip.continuous.continuousOn
    (fun xy _ => hlim xy.1 xy.2)

end Metric
