import DifferentialGeometry.Topology.Covering.ImmersionLift

noncomputable section
open Set Topology Manifold
open scoped ContDiff

namespace DifferentialGeometry.Topology

theorem exists_continuousMap_factor_of_range_subset
    {W M S : Type*} [TopologicalSpace W] [TopologicalSpace M] [TopologicalSpace S]
    {ι : W → M} (hι : IsEmbedding ι) (e : C(S, M)) (hsub : range e ⊆ range ι) :
    ∃ η : C(S, W), ∀ x, ι (η x) = e x := by
  have hmem (x : S) : ∃ w, ι w = e x := hsub (mem_range_self x)
  choose η hη using hmem
  have heq : ι ∘ η = e := funext hη
  exact ⟨⟨η, hι.continuous_iff.mpr (heq ▸ e.continuous)⟩, hη⟩

theorem exists_embedded_smooth_lift_of_simplyConnected
    {E F H H' W M N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] [TopologicalSpace H']
    [TopologicalSpace W] [ChartedSpace H W] [SimplyConnectedSpace W]
    [TopologicalSpace M] [ChartedSpace H' M]
    [TopologicalSpace N] [ChartedSpace H' N]
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
    {p : N → M} (hp : IsCoveringMap p) (hps : IsLocalDiffeomorph J J ∞ p)
    (ι : W → M) (hι : ContMDiff I J ∞ ι) (hemb : IsEmbedding ι)
    (hinj : ∀ w, Function.Injective (mfderiv I J ι w))
    (w₀ : W) (n₀ : N) (hn₀ : p n₀ = ι w₀) :
    ∃ g : C(W, N), g w₀ = n₀ ∧ (∀ w, p (g w) = ι w) ∧
      ContMDiff I J ∞ g ∧ IsEmbedding g ∧
      ∀ w, Function.Injective (mfderiv I J g w) := by
  obtain ⟨g, hg₀, hpg, hgs⟩ := exists_smooth_lift_of_simplyConnected hp hps ι hι w₀ n₀ hn₀
  have heq : p ∘ g = ι := funext hpg
  exact ⟨g, hg₀, hpg, hgs,
    IsEmbedding.of_comp g.continuous hps.contMDiff.continuous (heq ▸ hemb),
    injective_mfderiv_of_smooth_lift hps.contMDiff hinj hgs hpg⟩

end DifferentialGeometry.Topology
