import DifferentialGeometry.Geometry.Metric.Comparison.CurveLength
import Mathlib.Geometry.Manifold.Riemannian.Basic

noncomputable section

open scoped Manifold ContDiff Bundle Topology

namespace DifferentialGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem riemannianEDistOf_ne_top_iff
    (g₀ g₁ : SmoothRiemannianMetric I M) (x y : M) :
    riemannianEDistOf g₀ x y ≠ ⊤ ↔ riemannianEDistOf g₁ x y ≠ ⊤ := by
  suffices h : ∀ g h : SmoothRiemannianMetric I M,
      riemannianEDistOf g x y ≠ ⊤ → riemannianEDistOf h x y ≠ ⊤ from
    ⟨h g₀ g₁, h g₁ g₀⟩
  intro g h hfin
  let : Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  have hlt : Manifold.riemannianEDist I x y < ⊤ := lt_top_iff_ne_top.mpr hfin
  obtain ⟨γ, hzero, hone, hγ, _⟩ :=
    Manifold.exists_lt_of_riemannianEDist_lt (I := I) hlt
  have hle := riemannianEDistOf_le_arcLength h (by norm_num : (0 : ℝ) ≤ 1) hγ
  simpa only [hzero, hone] using (hle.trans_lt ENNReal.ofReal_lt_top).ne

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem eventually_riemannianEDistOf_ne_top
    {P : Type*} [TopologicalSpace P] (g : P → SmoothRiemannianMetric I M)
    (g₀ : SmoothRiemannianMetric I M) {τ : P} {O x : M}
    (hfin : riemannianEDistOf g₀ O x ≠ ⊤) :
    ∀ᶠ p : P × M in 𝓝 (τ, x), riemannianEDistOf (g p.1) O p.2 ≠ ⊤ := by
  let : Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g₀.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
    ⟨g₀.inner, g₀.contMDiff.continuous, fun _ _ _ => rfl⟩
  have hlocal : ∀ᶠ y in 𝓝 x, riemannianEDistOf g₀ x y < 1 :=
    eventually_riemannianEDist_lt I x zero_lt_one
  filter_upwards [(continuous_snd.tendsto (τ, x)).eventually hlocal] with p hp
  apply (riemannianEDistOf_ne_top_iff g₀ (g p.1) O p.2).mp
  exact ((riemannianEDistOf_triangle g₀ O x p.2).trans_lt
    (ENNReal.add_lt_top.mpr ⟨lt_top_iff_ne_top.mpr hfin, lt_trans hp (by simp)⟩)).ne

end DifferentialGeometry
