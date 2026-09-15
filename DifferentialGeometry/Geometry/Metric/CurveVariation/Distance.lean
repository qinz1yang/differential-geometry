import DifferentialGeometry.Geometry.Metric.CurveVariation.Basic
import DifferentialGeometry.Topology.Connected.FiniteEDistance

noncomputable section

open Set Filter MeasureTheory Bundle Manifold
open scoped Manifold ContDiff NNReal ENNReal Topology

namespace DifferentialGeometry.Geometry

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {H G : Type*} [TopologicalSpace H] [TopologicalSpace G]
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
    {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace H M] [ChartedSpace G N] [IsManifold I ∞ M] [IsManifold J ∞ N]

theorem riemannianEDistOf_comp_le_of_local_riemannianCurveVariation_of_ne_top [RegularSpace M] [RegularSpace N]
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (f : M → N) (L : ℝ≥0)
    (hloc : ∀ x : M, ∃ U ∈ 𝓝 x, ∀ (a b : ℝ) (γ : ℝ → M),
      a ≤ b → ContinuousOn γ (Icc a b) → MapsTo γ (Icc a b) U →
      riemannianCurveVariation g γ a b ≠ ⊤ →
      riemannianCurveVariation h (f ∘ γ) a b ≤ L * riemannianCurveVariation g γ a b)
    {x y : M} (hgfin : riemannianEDistOf g x y ≠ ⊤) :
    riemannianEDistOf h (f x) (f y) ≤ L * riemannianEDistOf g x y := by
  let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  let : PseudoEMetricSpace M := .ofRiemannianMetric I M
  let : RiemannianBundle (TangentSpace J : N → Type _) := ⟨h.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle F (TangentSpace J : N → Type _) :=
    ⟨h.inner, h.contMDiff.continuous, fun _ _ _ => rfl⟩
  let : PseudoEMetricSpace N := .ofRiemannianMetric J N
  let Admissible : Type _ :=
    {γ : ℝ → M // γ 0 = x ∧ γ 1 = y ∧ ContinuousOn γ (Icc 0 1) ∧
      riemannianCurveVariation g γ 0 1 ≠ ⊤}
  have hne : Nonempty Admissible := by
    obtain ⟨r, hr1, hr2⟩ := exists_between (lt_top_iff_ne_top.mpr hgfin)
    obtain ⟨γ, hγ0, hγ1, hγsm, hγlen⟩ := Manifold.exists_lt_of_riemannianEDist_lt hr1
    exact ⟨⟨γ, hγ0, hγ1, hγsm.continuousOn,
      ne_top_of_lt ((riemannianCurveVariation_le_pathELength g hγsm).trans_lt hγlen)⟩⟩
  have hinner : riemannianEDistOf h (f x) (f y) ≤
      ⨅ (γ : Admissible), (L : ℝ≥0∞) * riemannianCurveVariation g γ.1 0 1 := by
    refine le_iInf fun γ => ?_
    have h1 : riemannianEDistOf h (f (γ.1 0)) (f (γ.1 1)) ≤
        riemannianCurveVariation h (f ∘ γ.1) 0 1 :=
      riemannianEDistOf_le_riemannianCurveVariation h (f ∘ γ.1) (by norm_num)
    rw [γ.2.1, γ.2.2.1] at h1
    exact h1.trans (riemannianCurveVariation_comp_le_of_local g h f L hloc γ.2.2.2.1 γ.2.2.2.2)
  have hstep : ⨅ (γ : Admissible), (L : ℝ≥0∞) * riemannianCurveVariation g γ.1 0 1 =
      (L : ℝ≥0∞) * ⨅ (γ : Admissible), riemannianCurveVariation g γ.1 0 1 := by
    rw [ENNReal.mul_iInf' (fun hL _ => absurd hL ENNReal.coe_ne_top) (fun _ => hne)]
  have hle : ⨅ (γ : Admissible), riemannianCurveVariation g γ.1 0 1 ≤
      riemannianEDistOf g x y := by
    refine le_of_forall_gt_imp_ge_of_dense fun r hr => ?_
    obtain ⟨r', hr1, hr2⟩ := exists_between hr
    obtain ⟨γ, hγ0, hγ1, hγsm, hγlen⟩ := Manifold.exists_lt_of_riemannianEDist_lt hr1
    have hfin : riemannianCurveVariation g γ 0 1 ≠ ⊤ :=
      ne_top_of_lt ((riemannianCurveVariation_le_pathELength g hγsm).trans_lt hγlen)
    refine (iInf_le (fun γ : Admissible => riemannianCurveVariation g γ.1 0 1)
      ⟨γ, hγ0, hγ1, hγsm.continuousOn, hfin⟩).trans ?_
    exact le_of_lt ((riemannianCurveVariation_le_pathELength g hγsm).trans_lt (hγlen.trans hr2))
  calc riemannianEDistOf h (f x) (f y)
      ≤ ⨅ (γ : Admissible), (L : ℝ≥0∞) * riemannianCurveVariation g γ.1 0 1 := hinner
    _ = (L : ℝ≥0∞) * ⨅ (γ : Admissible), riemannianCurveVariation g γ.1 0 1 := hstep
    _ ≤ (L : ℝ≥0∞) * riemannianEDistOf g x y := mul_le_mul_right hle _

theorem riemannianEDistOf_comp_le_of_local_riemannianCurveVariation [RegularSpace M] [RegularSpace N]
    [PreconnectedSpace M]
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (f : M → N) (L : ℝ≥0)
    (hloc : ∀ x : M, ∃ U ∈ 𝓝 x, ∀ (a b : ℝ) (γ : ℝ → M),
      a ≤ b → ContinuousOn γ (Icc a b) → MapsTo γ (Icc a b) U →
      riemannianCurveVariation g γ a b ≠ ⊤ →
      riemannianCurveVariation h (f ∘ γ) a b ≤ L * riemannianCurveVariation g γ a b) :
    ∀ x y, riemannianEDistOf h (f x) (f y) ≤ L * riemannianEDistOf g x y := by
  let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  let : PseudoEMetricSpace M := .ofRiemannianMetric I M
  intro x y
  exact riemannianEDistOf_comp_le_of_local_riemannianCurveVariation_of_ne_top g h f L hloc
    (DifferentialGeometry.Analysis.edist_ne_top_of_preconnected x y)

theorem riemannianEDistOf_comp_le_of_local_riemannianCurveVariation_of_ne_zero [RegularSpace M] [RegularSpace N]
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (f : M → N) (L : ℝ≥0) (hL : L ≠ 0)
    (hloc : ∀ x : M, ∃ U ∈ 𝓝 x, ∀ (a b : ℝ) (γ : ℝ → M),
      a ≤ b → ContinuousOn γ (Icc a b) → MapsTo γ (Icc a b) U →
      riemannianCurveVariation g γ a b ≠ ⊤ →
      riemannianCurveVariation h (f ∘ γ) a b ≤ L * riemannianCurveVariation g γ a b) :
    ∀ x y, riemannianEDistOf h (f x) (f y) ≤ L * riemannianEDistOf g x y := by
  intro x y
  by_cases hfin : riemannianEDistOf g x y = ⊤
  · rw [hfin, ENNReal.mul_top (by simpa using hL)]
    exact le_top
  · exact riemannianEDistOf_comp_le_of_local_riemannianCurveVariation_of_ne_top g h f L hloc hfin


end DifferentialGeometry.Geometry
