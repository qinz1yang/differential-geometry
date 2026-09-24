import DifferentialGeometry.Topology.Covering.SmoothLift

noncomputable section

open Set Filter Topology Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology

theorem exists_contMDiff_lift_of_simplyConnected
    {E F G H H' H'' W M N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace H'']
    [TopologicalSpace W] [ChartedSpace H W] [SimplyConnectedSpace W]
    [TopologicalSpace M] [ChartedSpace H' M]
    [TopologicalSpace N] [ChartedSpace H'' N]
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
    {L : ModelWithCorners ℝ G H''} {n : ℕ∞ω}
    {p : N → M} (hp : IsCoveringMap p) (hps : IsLocalDiffeomorph L J n p)
    (f : W → M) (hf : ContMDiff I J n f) (w₀ : W) (n₀ : N) (hn₀ : p n₀ = f w₀) :
    ∃ g : C(W, N), g w₀ = n₀ ∧ (∀ x, p (g x) = f x) ∧ ContMDiff I L n g := by
  have : LocallyPathConnectedSpace W :=
    DifferentialGeometry.Topology.Manifold.locallyPathConnectedSpace_of_modelWithCorners I
  obtain ⟨g, ⟨hg₀, hpg⟩, _⟩ := hp.existsUnique_continuousMap_lifts
    ⟨f, hf.continuous⟩ w₀ n₀ hn₀
  have hpg' : ∀ x, p (g x) = f x := fun x => congrFun hpg x
  refine ⟨g, hg₀, hpg', ?_⟩
  intro x
  obtain ⟨φ, hx, hφ⟩ := hps (g x)
  have hfx : f x ∈ φ.target := by
    rw [← hpg' x, hφ hx]
    exact φ.map_source hx
  have hs := (φ.contMDiffOn_invFun.contMDiffAt (φ.open_target.mem_nhds hfx)).comp x (hf x)
  apply hs.congr_of_eventuallyEq
  filter_upwards [g.continuous.continuousAt.preimage_mem_nhds
    (φ.open_source.mem_nhds hx)] with y hy
  change g y = φ.symm (f y)
  rw [← hpg' y, hφ hy]
  exact (φ.left_inv hy).symm

end DifferentialGeometry.Topology
