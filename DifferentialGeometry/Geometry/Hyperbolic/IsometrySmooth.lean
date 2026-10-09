import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.CoveringIsometry
import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.IsometrySmooth
import Mathlib.Geometry.Manifold.LocalDiffeomorph

noncomputable section

open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Hyperbolic

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  {H H' : Type*} [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ V H} {J : ModelWithCorners ℝ W H'}
  {M N : Type*} [PseudoEMetricSpace M] [PseudoEMetricSpace N]
  [ChartedSpace H M] [ChartedSpace H' N]

theorem contMDiff_isometryEquiv_of_covering {n : ℕ∞ω}
    (q : Hyperboloid E → M) (p : Hyperboloid F → N)
    (hq : IsCoveringMap q) (hp : IsCoveringMap p)
    (hqs : Function.Surjective q) (hps : Function.Surjective p)
    (hqball : ∀ x r, 0 < r → q '' Metric.ball x r = Metric.eball (q x) (ENNReal.ofReal r))
    (hpball : ∀ x r, 0 < r → p '' Metric.ball x r = Metric.eball (p x) (ENNReal.ofReal r))
    (hqd : IsLocalDiffeomorph 𝓘(ℝ, E) I n q) (hpd : ContMDiff 𝓘(ℝ, F) J n p)
    (a : M ≃ᵢ N) : ContMDiff I J n a := by
  let _ : ContractibleSpace (Hyperboloid E) := Hyperboloid.spaceHomeomorph.contractibleSpace
  let _ : LocallyPathConnectedSpace (Hyperboloid E) :=
    (Hyperboloid.spaceHomeomorph (E := E)).symm.locallyPathConnectedSpace
  let u : C(Hyperboloid E, N) := (a : C(M, N)).comp ⟨q, hq.continuous⟩
  obtain ⟨y₀, hy₀⟩ := hps (u Hyperboloid.origin)
  obtain ⟨f, ⟨_, hproj⟩, _⟩ := hp.existsUnique_continuousMap_lifts u Hyperboloid.origin y₀ hy₀
  have hcomm (x : Hyperboloid E) : p (f x) = a (q x) := congrFun hproj x
  obtain ⟨e, he⟩ := Hyperboloid.exists_isometryEquiv_eq_lift q p hq hp hqball hpball a f hcomm
  have hecomm (x : Hyperboloid E) : p (e x) = a (q x) := by rw [he]; exact hcomm x
  have hpe : ContMDiff 𝓘(ℝ, E) J n (p ∘ e) := hpd.comp (Hyperboloid.contMDiff_isometryEquiv e)
  intro x
  obtain ⟨x₀, rfl⟩ := hqs x
  have hlocal := hqd x₀
  have hcomp := hpe.contMDiffAt.comp (q x₀) hlocal.contMDiffAt_localInverse
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [hlocal.localInverse_eventuallyEq_right] with y hy
  change a y = p (e (hlocal.localInverse y))
  rw [hecomm]
  exact congrArg a hy.symm

end DifferentialGeometry.Geometry.Hyperbolic
