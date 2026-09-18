import Mathlib.Algebra.Field.Periodic
import Mathlib.Topology.MetricSpace.UniformConvergence

open Filter Set

namespace Function.Periodic

theorem tendstoUniformlyOn_comp_of_Icc
    {ι P T Y : Type*} [PseudoMetricSpace Y] {l : Filter ι}
    {f : ι → ℝ → T → Y} {fInf : ℝ → T → Y}
    {J : Set T} {K : Set P} {c : ℝ} (hc : 0 < c)
    (hper : ∀ᶠ i in l, ∀ t ∈ J, Function.Periodic (fun x => f i x t) c)
    (hperInf : ∀ t ∈ J, Function.Periodic (fun x => fInf x t) c)
    (hf : TendstoUniformlyOn (fun i (q : ℝ × T) => f i q.1 q.2)
      (fun q : ℝ × T => fInf q.1 q.2) l (Icc (0 : ℝ) c ×ˢ J))
    (x : P → T → ℝ) :
    TendstoUniformlyOn (fun i (q : P × T) => f i (x q.1 q.2) q.2)
      (fun q : P × T => fInf (x q.1 q.2) q.2) l (K ×ˢ J) := by
  rw [Metric.tendstoUniformlyOn_iff] at hf ⊢
  intro ε hε
  filter_upwards [hper, hf ε hε] with i hpi hi
  intro q hq
  have hpair : Function.Periodic (fun y => (fInf y q.2, f i y q.2)) c := by
    intro y
    exact Prod.ext (hperInf q.2 hq.2 y) (hpi q.2 hq.2 y)
  obtain ⟨y, hy, heq⟩ := hpair.exists_mem_Ico₀ hc (x q.1 q.2)
  rw [(Prod.mk.inj heq).1, (Prod.mk.inj heq).2]
  exact hi (y, q.2) ⟨⟨hy.1, hy.2.le⟩, hq.2⟩

end Function.Periodic
