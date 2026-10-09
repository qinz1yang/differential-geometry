import DifferentialGeometry.Topology.MetricSpace.ApproximationBallCapture
import DifferentialGeometry.Topology.Manifold.ChartPatch.ProtectedGerms
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.Linarith

set_option autoImplicit false

noncomputable section

open Set Filter Metric
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Topology.Manifold

theorem exists_fixed_cutoff_chart_patch_of_metric_approximation
    {E F H G X : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] [TopologicalSpace G]
    [MetricSpace X] [ChartedSpace H X]
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
    {p : ℕ∞} [IsManifold I p X]
    {Y : ℕ → Type*} [∀ i, PseudoMetricSpace (Y i)] [∀ i, ChartedSpace G (Y i)]
    {A W T P : Set X}
    (hA : IsOpen A) (hW : IsOpen W) (hT : IsOpen T)
    (hcompact : IsCompact (closure W)) (hcover : closure W ⊆ A ∪ T)
    (hP : IsCompact P) (hPA : P ⊆ A) (hPW : P ⊆ W)
    (f : ∀ i, X → Y i) (b : ∀ i, Y i) (q : X → F)
    (hf : ∀ᶠ i in atTop, ContMDiffOn I J p (f i) A)
    (hq : ContMDiffOn I 𝓘(ℝ, F) p q (W ∩ T))
    (e : ∀ i, OpenPartialHomeomorph F (Y i))
    (he : ∀ i, ContMDiffOn 𝓘(ℝ, F) J p (e i) (e i).source)
    (heinv : ∀ i, ContMDiffOn J 𝓘(ℝ, F) p (e i).symm (e i).target)
    (c : X) {r R : ℝ} (hrR : r < R)
    (hDe : ∀ i, ball (0 : F) R ⊆ (e i).source)
    (hqD : MapsTo q (W ∩ T) (ball (0 : F) R))
    (heball : ∀ i, ball (b i) R ⊆ e i '' ball (0 : F) R)
    (hbound : ∀ x ∈ W ∩ T ∩ A, dist x c ≤ r)
    (a : ∀ i, Y i → X)
    (hconv : TendstoUniformlyOn (fun i x ↦ a i (f i x)) id atTop (W ∩ T ∩ A))
    (hcenter : Tendsto (fun i ↦ a i (b i)) atTop (𝓝 c))
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (hdist : ∀ᶠ i in atTop, ∀ x ∈ W ∩ T ∩ A,
      dist (f i x) (b i) ≤ dist (a i (f i x)) (a i (b i)) + ε i) :
    ∃ χ : X → ℝ, ∃ g : ∀ i, X → Y i,
      ContMDiff I 𝓘(ℝ, ℝ) p χ ∧ HasCompactSupport χ ∧
      (∀ x, χ x ∈ Icc (0 : ℝ) 1) ∧ tsupport χ ⊆ A ∧
      W ∩ tsupport (fun x ↦ 1 - χ x) ⊆ T ∧
      χ =ᶠ[𝓝ˢ P] 1 ∧ (∀ i, ContMDiffOn I J p (g i) W) ∧
      ∀ᶠ i in atTop,
        EqOn (g i) (f i) (W \ T) ∧
        (∀ x ∈ P, g i =ᶠ[𝓝 x] f i) ∧
        EqOn (g i) (f i) (W ∩ {x | χ x = 1}) ∧
        EqOn (g i) (e i ∘ q) (W ∩ {x | χ x = 0}) ∧
        MapsTo (g i) (W ∩ T) (e i).target ∧
        (∀ x ∈ W ∩ T,
          g i x = e i (q x + χ x • ((e i).symm (f i x) - q x))) ∧
        (∀ x ∈ W ∩ T,
          (e i).symm (g i x) = q x + χ x • ((e i).symm (f i x) - q x)) := by
  have hcapture := Metric.eventually_mapsTo_ball_of_approximation
    f a id c b hrR hbound hconv hcenter ε hε hdist
  have hfD : ∀ᶠ i in atTop, ∀ x ∈ W ∩ T ∩ A,
      f i x ∈ (e i).target ∧ (e i).symm (f i x) ∈ ball (0 : F) R := by
    filter_upwards [hcapture] with i hi x hx
    obtain ⟨v, hv, hfv⟩ := heball i (hi hx)
    have hvsource := hDe i hv
    have htarget : f i x ∈ (e i).target := hfv ▸ (e i).map_source hvsource
    have hinverse : (e i).symm (f i x) = v := by
      rw [← hfv]
      exact (e i).left_inv hvsource
    exact ⟨htarget, hinverse.symm ▸ hv⟩
  exact exists_fixed_cutoff_eventually_chart_patch_preserving_germs
    hA hW hT hcompact hcover hP hPA hPW f b q hf hq e he heinv
    (convex_ball (0 : F) R) hDe hqD hfD

end DifferentialGeometry.Topology.Manifold
