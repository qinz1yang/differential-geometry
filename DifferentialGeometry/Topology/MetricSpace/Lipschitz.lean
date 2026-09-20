import Mathlib.Topology.MetricSpace.Lipschitz

open Set Filter
open scoped Topology

section

variable {X Y Z : Type*} [PseudoEMetricSpace X] [PseudoEMetricSpace Y] [PseudoEMetricSpace Z]

theorem LocallyLipschitzOn.comp {f : Y → Z} {g : X → Y} {s : Set X} {t : Set Y}
    (hf : LocallyLipschitzOn t f) (hg : LocallyLipschitzOn s g) (hm : MapsTo g s t) :
    LocallyLipschitzOn s (f ∘ g) := by
  intro x hx
  obtain ⟨K, U, hU, hfU⟩ := hf (hm hx)
  obtain ⟨L, V, hV, hgV⟩ := hg hx
  refine ⟨K * L, V ∩ g ⁻¹' U, inter_mem hV ((hg.continuousOn x hx).tendsto_nhdsWithin hm hU), ?_⟩
  exact hfU.comp (hgV.mono inter_subset_left) (mapsTo_preimage g U |>.mono_left inter_subset_right)

theorem LocallyLipschitzOn.prodMk {f : X → Y} {g : X → Z} {s : Set X}
    (hf : LocallyLipschitzOn s f) (hg : LocallyLipschitzOn s g) :
    LocallyLipschitzOn s (fun x => (f x, g x)) :=
  locallyLipschitzOn_iff_restrict.mpr (hf.restrict.prodMk hg.restrict)

end

theorem locallyLipschitz_of_lipschitzOn_closedBall
    {X Y : Type*} [PseudoMetricSpace X] [PseudoEMetricSpace Y] {f : X → Y} (p : X)
    (hf : ∀ R : ℝ, 0 ≤ R → ∃ K, LipschitzOnWith K f (Metric.closedBall p R)) :
    LocallyLipschitz f := by
  intro x
  obtain ⟨K, hK⟩ := hf (dist x p + 1) (by positivity)
  exact ⟨K, Metric.closedBall p (dist x p + 1),
    Metric.closedBall_mem_nhds_of_mem (by linarith : dist x p < dist x p + 1), hK⟩
