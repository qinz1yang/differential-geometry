import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ComparisonComposition

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {N M : Type*} [TopologicalSpace N] [ChartedSpace ThreeSpace N]
  [IsManifold I3 ∞ N] [T2Space N] [SigmaCompactSpace N]
  [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]

theorem nonempty_metricComparisonOn_congr_reference
    {h h' : ℝ → SmoothRiemannianMetric I3 N}
    {g : ℝ → SmoothRiemannianMetric I3 M} {F : N → M}
    {U : Set N} {times : Set ℝ} {order : ℕ} {eps : ℝ}
    (C : MetricComparisonOn h g F U times order eps)
    (heq : Set.EqOn h' h times) :
    Nonempty (MetricComparisonOn h' g F U times order eps) := by
  let jet : ℕ → ℝ → Tensor0SField (I := I3) (M := N) ∞ 2 := fun b s =>
    match b with
    | 0 => C.pullback s - metricTensorField (h' s)
    | b + 1 => C.jet (b + 1) s
  have hj : ∀ b s, s ∈ times → jet b s = C.jet b s := by
    intro b s hs
    cases b with
    | zero =>
      apply DFunLike.ext
      intro y
      apply DFunLike.ext
      intro v
      change C.pullback s y v - metricTensorField (h' s) y v = C.jet 0 s y v
      rw [metricTensorField_apply, heq hs, C.jet_zero]
    | succ b => rfl
  refine ⟨{ pullback := C.pullback
            pullback_eq := C.pullback_eq
            jet := jet
            jet_zero := ?_
            jet_succ := ?_
            equivalence := ?_
            close := ?_ }⟩
  · intro s y v
    change C.pullback s y v - metricTensorField (h' s) y v = _
    rw [metricTensorField_apply]
  · intro b s hs y hy v
    rw [hj (b + 1) s hs, C.jet_succ b s hs y hy v]
    exact derivWithin_congr (fun a ha => by rw [hj b a ha]) (by rw [hj b s hs])
  · intro s hs y hy v
    rw [heq hs]
    exact C.equivalence s hs y hy v
  · intro a b hab s hs y hy
    rw [hj b s hs, heq hs]
    exact C.close a b hab s hs y hy


end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
