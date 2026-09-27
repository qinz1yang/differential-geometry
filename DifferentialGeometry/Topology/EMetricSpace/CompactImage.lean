import Mathlib.Topology.EMetricSpace.Basic
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.ENNReal.Lemmas

section

set_option autoImplicit false

noncomputable section

open Set
open scoped ENNReal

namespace EMetric

variable {A X : Type*} [TopologicalSpace A] [PseudoEMetricSpace X]

theorem edist_lt_top_of_continuous_of_preconnected
    [PreconnectedSpace A] {f : A → X} (hf : Continuous f) (a b : A) :
    edist (f a) (f b) < ⊤ := by
  let S : Set A := f ⁻¹' Metric.eball (f b) ⊤
  have hcl : IsClopen S :=
    ⟨Metric.isClosed_eball_top.preimage hf, Metric.isOpen_eball.preimage hf⟩
  have hb : b ∈ S := by
    change edist (f b) (f b) < ⊤
    simp
  rcases isClopen_iff.mp hcl with hempty | huniv
  · simp only [hempty, mem_empty_iff_false] at hb
  · have ha : a ∈ S := huniv ▸ mem_univ a
    exact ha

theorem exists_uniform_edist_bound_of_compact_preconnected
    [CompactSpace A] [PreconnectedSpace A] {f : A → X}
    (hf : Continuous f) (a : A) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ b : A, edist (f b) (f a) ≤ ENNReal.ofReal R := by
  have hc : Continuous (fun b => edist (f b) (f a)) := hf.edist continuous_const
  obtain ⟨b, -, hmax⟩ := isCompact_univ.exists_isMaxOn ⟨a, mem_univ a⟩ hc.continuousOn
  refine ⟨(edist (f b) (f a)).toReal, ENNReal.toReal_nonneg, ?_⟩
  intro c
  rw [ENNReal.ofReal_toReal (edist_lt_top_of_continuous_of_preconnected hf b a).ne]
  exact hmax (mem_univ c)

end EMetric

end

end
