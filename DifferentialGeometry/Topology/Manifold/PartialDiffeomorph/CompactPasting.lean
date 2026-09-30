/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import DifferentialGeometry.Topology.Manifold.CompactLocalDiffeomorph
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph

open Set Filter Topology
open scoped ContDiff Manifold

namespace PartialDiffeomorph

variable {E F H G M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] [TopologicalSpace G] [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace H M] [ChartedSpace G N] [T2Space M] [T2Space N] [Nonempty M]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}

theorem exists_pasting_of_compact
    (d e : PartialDiffeomorph I J M N ∞) {K L : Set M}
    (hK : IsCompact K) (hL : IsCompact L) (hKd : K ⊆ d.source) (hLe : L ⊆ e.source)
    {V : Set M} (hV : IsOpen V) (hKL : K ∩ L ⊆ V) (hmatch : EqOn d e V)
    (hcross : ∀ x ∈ K, ∀ y ∈ L, d x = e y → x = y)
    {U : Set M} (hU : IsOpen U) (hKU : K ∪ L ⊆ U) :
    ∃ c : PartialDiffeomorph I J M N ∞,
      K ∪ L ⊆ c.source ∧ c.source ⊆ U ∧
      (∀ x ∈ K, (c : M → N) =ᶠ[𝓝 x] d) ∧
      (∀ x ∈ L, (c : M → N) =ᶠ[𝓝 x] e) := by
  classical
  have hdis : Disjoint K (L \ V) := disjoint_left.mpr fun x hx hxL =>
    hxL.2 (hKL ⟨hx, hxL.1⟩)
  obtain ⟨A, B, hA, hB, hKA, hLB, hAB⟩ :=
    SeparatedNhds.of_isCompact_isCompact hK (hL.diff hV) hdis
  let f : M → N := A.piecewise d e
  have hfd (x : M) (hx : x ∈ K) : f =ᶠ[𝓝 x] d := by
    filter_upwards [hA.mem_nhds (hKA hx)] with y hy
    exact ite_eq_left hy
  have hfe (x : M) (hx : x ∈ L) : f =ᶠ[𝓝 x] e := by
    by_cases hxV : x ∈ V
    · filter_upwards [hV.mem_nhds hxV] with y hy
      by_cases hyA : y ∈ A
      · exact (ite_eq_left hyA).trans (hmatch hy)
      · exact ite_eq_right hyA
    · filter_upwards [hB.mem_nhds (hLB ⟨hx, hxV⟩)] with y hy
      exact ite_eq_right (fun hyA => disjoint_left.mp hAB hyA hy)
  have hinj : InjOn f (K ∪ L) := by
    rintro x (hx | hx) y (hy | hy) heq
    · exact d.injOn (hKd hx) (hKd hy)
        ((hfd x hx).eq_of_nhds.symm.trans (heq.trans (hfd y hy).eq_of_nhds))
    · exact hcross x hx y hy
        ((hfd x hx).eq_of_nhds.symm.trans (heq.trans (hfe y hy).eq_of_nhds))
    · exact (hcross y hy x hx
        ((hfd y hy).eq_of_nhds.symm.trans (heq.symm.trans (hfe x hx).eq_of_nhds))).symm
    · exact e.injOn (hLe hx) (hLe hy)
        ((hfe x hx).eq_of_nhds.symm.trans (heq.trans (hfe y hy).eq_of_nhds))
  have hlocal (x : M) (hx : x ∈ K ∪ L) : IsLocalDiffeomorphAt I J ∞ f x := by
    rcases hx with hx | hx
    · obtain ⟨W, hWf, hW, hxW⟩ := mem_nhds_iff.mp (hfd x hx)
      let a := DifferentialGeometry.Topology.PartialDiffeomorph.restrict d W hW
      exact ⟨a, ⟨hKd hx, hxW⟩, fun y hy => hWf hy.2⟩
    · obtain ⟨W, hWf, hW, hxW⟩ := mem_nhds_iff.mp (hfe x hx)
      let a := DifferentialGeometry.Topology.PartialDiffeomorph.restrict e W hW
      exact ⟨a, ⟨hLe hx, hxW⟩, fun y hy => hWf hy.2⟩
  obtain ⟨a, hKa, _, ha⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_partialDiffeomorph_of_injOn_compact
      (hK.union hL) hinj hlocal isOpen_univ (subset_univ _)
  let c := DifferentialGeometry.Topology.PartialDiffeomorph.restrict a U hU
  have hc : (c : M → N) = f := ha
  exact ⟨c, fun x hx => ⟨hKa hx, hKU hx⟩, fun _ hx => hx.2,
    fun x hx => hc ▸ hfd x hx, fun x hx => hc ▸ hfe x hx⟩

end PartialDiffeomorph
