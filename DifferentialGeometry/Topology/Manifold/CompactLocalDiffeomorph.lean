/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import DifferentialGeometry.Topology.Manifold.InjectiveLocalDiffeomorph
import Mathlib.Topology.Separation.Hausdorff

open Set Filter Function
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Topology.Manifold

variable {E F H G X Y : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] [TopologicalSpace G] [TopologicalSpace X] [TopologicalSpace Y]
  [ChartedSpace H X] [ChartedSpace G Y] [T2Space Y] [Nonempty X]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}

theorem exists_partialDiffeomorph_of_injOn_compact
    {f : X → Y} {K : Set X} {n : ℕ∞ω} (hK : IsCompact K) (hinj : InjOn f K)
    (hloc : ∀ x ∈ K, IsLocalDiffeomorphAt I J n f x)
    {O : Set Y} (hO : IsOpen O) (hKO : f '' K ⊆ O) :
    ∃ d : PartialDiffeomorph I J X Y n,
      K ⊆ d.source ∧ d.target ⊆ O ∧ (d : X → Y) = f := by
  obtain ⟨V, hV, hKV, hinjV⟩ := hinj.exists_isOpen_superset hK
    (fun x hx => (hloc x hx).contMDiffAt.continuousAt) (by
      intro x hx
      obtain ⟨d, hxd, heq⟩ := hloc x hx
      exact ⟨d.source, d.open_source.mem_nhds hxd, fun _ hy _ hz he =>
        d.injOn hy hz ((heq hy).symm.trans (he.trans (heq hz)))⟩)
  let U := {x | IsLocalDiffeomorphAt I J n f x ∧ f x ∈ O}
  have hU : IsOpen U := by
    apply isOpen_iff_mem_nhds.mpr
    intro x hx
    obtain ⟨d, hxd, heq⟩ := hx.1
    filter_upwards [d.open_source.mem_nhds hxd,
      hx.1.contMDiffAt.continuousAt.preimage_mem_nhds (hO.mem_nhds hx.2)] with y hy hyO
    exact ⟨⟨d, hy, heq⟩, hyO⟩
  have hKU : K ⊆ U := fun x hx => ⟨hloc x hx, hKO ⟨x, hx, rfl⟩⟩
  obtain ⟨d, hds, hdt, heq⟩ := exists_partialDiffeomorph_of_injOn
    (I := I) (J := J) (hV.inter hU)
    (fun x => x.2.2.1) (hinjV.mono inter_subset_left)
  refine ⟨d, ?_, ?_, heq⟩
  · rw [hds]
    exact subset_inter hKV hKU
  · rw [hdt]
    rintro y ⟨x, hx, rfl⟩
    exact hx.2.2

end DifferentialGeometry.Topology.Manifold
