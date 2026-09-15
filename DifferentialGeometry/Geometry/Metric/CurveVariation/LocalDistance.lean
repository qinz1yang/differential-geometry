import DifferentialGeometry.Geometry.Metric.CurveVariation.Basic
import DifferentialGeometry.Geometry.Metric.LocalChartDistance

set_option autoImplicit false

noncomputable section

open Bundle Set Manifold Filter
open scoped Manifold ContDiff ENNReal NNReal Topology

namespace DifferentialGeometry.Geometry

variable {E F H H' M N A : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [RegularSpace M]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
  [TopologicalSpace A]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem local_riemannianEDistOf_le_of_riemannianCurveVariation_le
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (φ : A → M) (hφ : _root_.Topology.IsOpenEmbedding φ) (f : A → N)
    (hlen : ∀ (γ : ℝ → A) (a b : ℝ), a ≤ b → ContinuousOn γ (Icc a b) →
      riemannianCurveVariation g (φ ∘ γ) a b ≠ ⊤ →
      riemannianCurveVariation h (f ∘ γ) a b ≤ riemannianCurveVariation g (φ ∘ γ) a b)
    (p : A) :
    ∃ U ∈ 𝓝 p, ∀ y ∈ U, ∀ z ∈ U,
      riemannianEDistOf h (f y) (f z) ≤ riemannianEDistOf g (φ y) (φ z) := by
  let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  obtain ⟨c, hc, hball⟩ := setOfPred_riemannianEDist_lt_subset_nhds I
    (hφ.isOpen_range.mem_nhds (mem_range_self p))
  let V : Set M := {q | riemannianEDistOf g (φ p) q < (c / 3 : ℝ≥0)}
  have hV : V ∈ 𝓝 (φ p) := eventually_riemannianEDist_lt I (φ p) (by positivity)
  refine ⟨φ ⁻¹' V, hφ.continuous.continuousAt.preimage_mem_nhds hV, ?_⟩
  intro y hy z hz
  by_contra hnot
  have hd : riemannianEDistOf g (φ y) (φ z) < riemannianEDistOf h (f y) (f z) :=
    lt_of_not_ge hnot
  have hdsmall : riemannianEDistOf g (φ y) (φ z) <
      ((c / 3 : ℝ≥0) : ℝ≥0∞) + (c / 3 : ℝ≥0) := by
    have hy' : riemannianEDistOf g (φ y) (φ p) < (c / 3 : ℝ≥0) := by
      rw [riemannianEDistOf_comm]
      exact hy
    exact (riemannianEDistOf_triangle g (φ y) (φ p) (φ z)).trans_lt
      (ENNReal.add_lt_add hy' hz)
  obtain ⟨γ, hγ0, hγ1, hγ, hshort⟩ :=
    exists_lt_of_riemannianEDist_lt (lt_min hd hdsmall)
  have hsum : ((c / 3 : ℝ≥0) : ℝ≥0∞) +
      (((c / 3 : ℝ≥0) : ℝ≥0∞) + (c / 3 : ℝ≥0)) = (c : ℝ≥0∞) := by
    exact_mod_cast (show c / 3 + (c / 3 + c / 3) = c by ring)
  have hmaps : MapsTo γ (Icc 0 1) (range φ) := by
    apply DifferentialGeometry.Geometry.Metric.mapsTo_of_riemannianEDistOf_add_pathELength_lt
      g (φ p) (range φ) c hball γ hγ
    have hstart : riemannianEDistOf g (φ p) (γ 0) < (c / 3 : ℝ≥0) := by
      rwa [hγ0]
    simpa only [hsum] using
      ENNReal.add_lt_add hstart (hshort.trans_le (min_le_right _ _))
  let η : ℝ → A := fun t => if ht : t ∈ Icc (0 : ℝ) 1 then
      Classical.choose (hmaps ht) else y
  have hη : EqOn (φ ∘ η) γ (Icc 0 1) := by
    intro t ht
    simp only [Function.comp_apply, η, dif_pos ht]
    exact Classical.choose_spec (hmaps ht)
  have hηcont : ContinuousOn η (Icc 0 1) :=
    hφ.isEmbedding.continuousOn_iff.mpr (hγ.continuousOn.congr hη)
  have hη0 : η 0 = y := hφ.injective ((hη (by simp)).trans hγ0)
  have hη1 : η 1 = z := hφ.injective ((hη (by simp)).trans hγ1)
  have hηlength : riemannianCurveVariation g (φ ∘ η) 0 1 =
      riemannianCurveVariation g γ 0 1 := by
    unfold riemannianCurveVariation
    congr 1
    funext q
    apply Finset.sum_congr rfl
    intro n hn
    rw [hη (q.2.2.2 (n + 1)), hη (q.2.2.2 n)]
  have hfin : riemannianCurveVariation g (φ ∘ η) 0 1 ≠ ⊤ := by
    rw [hηlength]
    exact ne_top_of_lt ((riemannianCurveVariation_le_pathELength g hγ).trans_lt
      (hshort.trans_le (min_le_right _ _)))
  have hbound := (riemannianEDistOf_le_riemannianCurveVariation h (f ∘ η) zero_le_one).trans
    (hlen η 0 1 zero_le_one hηcont hfin)
  rw [Function.comp_apply, Function.comp_apply, hη0, hη1, hηlength] at hbound
  exact (not_lt_of_ge (hbound.trans (riemannianCurveVariation_le_pathELength g hγ)))
    (hshort.trans_le (min_le_left _ _))

end DifferentialGeometry.Geometry
