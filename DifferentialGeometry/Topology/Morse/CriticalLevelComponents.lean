import DifferentialGeometry.Topology.Manifold.RegularLevel.Components
import DifferentialGeometry.Topology.Morse.CriticalExtrema
import DifferentialGeometry.Topology.Connected.ComponentIn
import DifferentialGeometry.Topology.Order.LocalExtrema

open Set
open scoped ContDiff Manifold

namespace DifferentialGeometry.Topology.Morse

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  (I : ModelWithCorners ℝ E H) [I.Boundaryless] [IsManifold I ∞ M]

theorem inter_closure_superlevel_components_eq_singleton
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {c : ℝ} {p q s : M}
    (hp : c < f p) (hq : c < f q)
    (hconn : IsPreconnected {x | c ≤ f x})
    (hmax : ¬ IsLocalMax f s)
    (hcover : {x | c < f x} = connectedComponentIn {x | c < f x} p ∪
      connectedComponentIn {x | c < f x} q)
    (hne : connectedComponentIn {x | c < f x} p ≠ connectedComponentIn {x | c < f x} q)
    (hcritical : ∀ x, f x = c → IsCriticalPointAt I f x → x = s) :
    closure (connectedComponentIn {x | c < f x} p) ∩
      closure (connectedComponentIn {x | c < f x} q) = {s} := by
  let C := connectedComponentIn {x | c < f x} p
  let D := connectedComponentIn {x | c < f x} q
  have hunion : closure C ∪ closure D = {x | c ≤ f x} := by
    rw [← closure_union, ← hcover]
    apply hf.continuous.closure_gt_eq_ge_of_not_isLocalMax
    intro x hx hxmax
    have hxs := hcritical x hx
      (isCriticalPointAt_of_isLocalMax (I := I) hxmax BoundarylessManifold.isInteriorPoint)
    exact hmax (hxs ▸ hxmax)
  have hinter : closure C ∩ closure D ⊆ {s} := by
    rintro x ⟨hxC, hxD⟩
    have hxlevel : c ≤ f x := hunion.subset (Or.inl hxC)
    have hxeq : f x = c := by
      apply le_antisymm _ hxlevel
      by_contra h
      have hxU : c < f x := lt_of_not_ge h
      have hxCp : x ∈ C := (closure_connectedComponentIn_inter {y | c < f y} p).subset ⟨hxC, hxU⟩
      have hxDq : x ∈ D := (closure_connectedComponentIn_inter {y | c < f y} q).subset ⟨hxD, hxU⟩
      exact hne ((connectedComponentIn_eq hxCp).trans (connectedComponentIn_eq hxDq).symm)
    have hxc : IsCriticalPointAt I f x := by
      by_contra hr
      exact hne (
        DifferentialGeometry.Manifold.RegularLevel.superlevel_connectedComponentIn_eq_of_mem_closure
          I hf hxeq hr hxC hxD)
    exact hcritical x hxeq hxc
  have hpC : p ∈ closure C := subset_closure (mem_connectedComponentIn hp)
  have hqD : q ∈ closure D := subset_closure (mem_connectedComponentIn hq)
  obtain ⟨x, _, hxC, hxD⟩ := isPreconnected_closed_iff.mp hconn
    (closure C) (closure D) isClosed_closure isClosed_closure hunion.symm.subset
    ⟨p, hp.le, hpC⟩ ⟨q, hq.le, hqD⟩
  apply Subset.antisymm hinter
  exact singleton_subset_iff.mpr (mem_singleton_iff.mp (hinter ⟨hxC, hxD⟩) ▸ ⟨hxC, hxD⟩)

end DifferentialGeometry.Topology.Morse
