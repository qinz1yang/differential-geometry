/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Order.Basic

open Set Filter Topology

namespace Metric

theorem tendsto_diam_smallSets {X : Type*} [PseudoMetricSpace X] (x : X) :
    Tendsto diam (𝓝 x).smallSets (𝓝 (0 : ℝ)) := by
  refine Metric.tendsto_nhds.mpr fun ε hε => ?_
  refine eventually_smallSets.mpr ⟨closedBall x (ε / 4), closedBall_mem_nhds _ (by positivity), ?_⟩
  intro s hs
  rw [Real.dist_eq, sub_zero, abs_of_nonneg Metric.diam_nonneg]
  exact (diam_le_of_subset_closedBall (by positivity) hs).trans_lt (by linarith)

end Metric

theorem ContinuousWithinAt.tendsto_diam_image_Icc
    {α X ι : Type*} [LinearOrder α] [TopologicalSpace α] [OrderTopology α]
    [PseudoMetricSpace X] {f : α → X} {K : Set α} {x : α}
    (hf : ContinuousWithinAt f K x) {l : Filter ι} {u v : ι → α}
    (hu : Tendsto u l (𝓝 x)) (hv : Tendsto v l (𝓝 x))
    (hK : ∀ᶠ i in l, Icc (u i) (v i) ⊆ K) :
    Tendsto (fun i => Metric.diam (f '' Icc (u i) (v i))) l (𝓝 0) := by
  have hsmall : Tendsto (fun i => Icc (u i) (v i)) l (𝓝[K] x).smallSets := by
    rw [nhdsWithin, smallSets_inf, smallSets_principal]
    exact tendsto_inf.mpr ⟨hu.Icc hv, tendsto_principal.mpr hK⟩
  exact (Metric.tendsto_diam_smallSets (f x)).comp (hf.image_smallSets.comp hsmall)
