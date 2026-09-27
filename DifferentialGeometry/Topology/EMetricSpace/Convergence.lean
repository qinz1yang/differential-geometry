import Mathlib.Topology.Instances.ENNReal.Lemmas

set_option autoImplicit false

namespace DifferentialGeometry.Topology

open Filter
open scoped ENNReal _root_.Topology

theorem tendsto_edist_of_tendsto_edist_zero
    {ι : Type*} {α : ι → Type*} [∀ i, PseudoEMetricSpace (α i)]
    {l : Filter ι} {a b c d : ∀ i, α i} {z : ℝ≥0∞}
    (ha : Tendsto (fun i => edist (a i) (b i)) l (𝓝 0))
    (hc : Tendsto (fun i => edist (c i) (d i)) l (𝓝 0))
    (hd : Tendsto (fun i => edist (a i) (c i)) l (𝓝 z)) :
    Tendsto (fun i => edist (b i) (d i)) l (𝓝 z) := by
  have he : Tendsto (fun i => edist (a i) (b i) + edist (c i) (d i)) l (𝓝 0) := by
    simpa only [add_zero] using ha.add hc
  have hlo := ENNReal.Tendsto.sub hd he (Or.inr ENNReal.zero_ne_top)
  have hhi := hd.add he
  simp only [tsub_zero, add_zero] at hlo hhi
  apply hlo.squeeze hhi
  · intro i
    apply tsub_le_iff_right.mpr
    simpa only [edist_comm (d i) (c i), add_comm, add_left_comm, add_assoc] using
      edist_triangle4 (a i) (b i) (d i) (c i)
  · intro i
    simpa only [edist_comm (b i) (a i), add_comm, add_left_comm, add_assoc] using
      edist_triangle4 (b i) (a i) (c i) (d i)

end DifferentialGeometry.Topology
