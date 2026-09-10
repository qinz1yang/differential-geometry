import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Topology.Homotopy.Lifting
import DifferentialGeometry.Topology.Manifold.LocallyPathConnected

noncomputable section

open Set Filter Topology Manifold
open scoped Manifold ContDiff

namespace Poincare.Topology

theorem contMDiff_of_lift_through_localDiffeomorph
    {E F G H H' H'' W M N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace H'']
    [TopologicalSpace W] [ChartedSpace H W]
    [TopologicalSpace M] [ChartedSpace H' M]
    [TopologicalSpace N] [ChartedSpace H'' N]
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
    {L : ModelWithCorners ℝ G H''}
    {p : N → M} (hp : IsLocalDiffeomorph L J ∞ p)
    {f : W → M} (hf : ContMDiff I J ∞ f)
    (g : C(W, N)) (hpg : ∀ x, p (g x) = f x) : ContMDiff I L ∞ g := by
  intro x
  obtain ⟨φ, hx, hφ⟩ := hp (g x)
  have hfx : f x ∈ φ.target := by
    rw [← hpg x, hφ hx]
    exact φ.map_source hx
  have hs := (φ.contMDiffOn_invFun.contMDiffAt (φ.open_target.mem_nhds hfx)).comp x
    (hf x)
  apply hs.congr_of_eventuallyEq
  filter_upwards [g.continuous.continuousAt.preimage_mem_nhds (φ.open_source.mem_nhds hx)] with y hy
  change g y = φ.symm (f y)
  rw [← hpg y, hφ hy]
  exact (φ.left_inv hy).symm

theorem exists_smooth_lift_of_simplyConnected
    {E F G H H' H'' W M N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace H'']
    [TopologicalSpace W] [ChartedSpace H W] [SimplyConnectedSpace W]
    [TopologicalSpace M] [ChartedSpace H' M]
    [TopologicalSpace N] [ChartedSpace H'' N]
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
    {L : ModelWithCorners ℝ G H''}
    {p : N → M} (hp : IsCoveringMap p) (hps : IsLocalDiffeomorph L J ∞ p)
    (f : W → M) (hf : ContMDiff I J ∞ f) (w₀ : W) (n₀ : N) (hn₀ : p n₀ = f w₀) :
    ∃ g : C(W, N), g w₀ = n₀ ∧ (∀ x, p (g x) = f x) ∧ ContMDiff I L ∞ g := by
  have : LocallyPathConnectedSpace W :=
    Poincare.Topology.Manifold.locallyPathConnectedSpace_of_modelWithCorners I
  obtain ⟨g, ⟨hg₀, hpg⟩, _⟩ := hp.existsUnique_continuousMap_lifts
    ⟨f, hf.continuous⟩ w₀ n₀ hn₀
  have hpg' : ∀ x, p (g x) = f x := fun x ↦ congrFun hpg x
  exact ⟨g, hg₀, hpg', contMDiff_of_lift_through_localDiffeomorph hps hf g hpg'⟩

end Poincare.Topology
