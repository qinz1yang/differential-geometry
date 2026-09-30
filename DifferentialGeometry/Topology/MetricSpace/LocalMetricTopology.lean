import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open Set Metric

namespace PseudoMetricSpace

theorem toTopology_eq_of_locally_dist_eq {X : Type*} (m m' : PseudoMetricSpace X)
    (hdom : ∀ x y : X, m.dist x y ≤ m'.dist x y)
    (hlocal : ∀ x : X, ∃ r : ℝ, 0 < r ∧ ∀ y : X,
      m.dist y x < r → m'.dist y x = m.dist y x) :
    m.toUniformSpace.toTopologicalSpace = m'.toUniformSpace.toTopologicalSpace := by
  apply TopologicalSpace.ext_iff.mpr
  intro s
  rw [@Metric.isOpen_iff X m s, @Metric.isOpen_iff X m' s]
  constructor
  · intro hs x hx
    obtain ⟨r, hr, hsub⟩ := hs x hx
    refine ⟨r, hr, fun y hy => hsub ?_⟩
    exact (hdom y x).trans_lt hy
  · intro hs x hx
    obtain ⟨δ, hδ, hsub⟩ := hs x hx
    obtain ⟨r, hr, heq⟩ := hlocal x
    refine ⟨min δ r, lt_min hδ hr, fun y hy => hsub ?_⟩
    change m'.dist y x < δ
    have hy' : m.dist y x < min δ r := hy
    rw [heq y (hy'.trans_le (min_le_right _ _))]
    exact hy'.trans_le (min_le_left _ _)

end PseudoMetricSpace

