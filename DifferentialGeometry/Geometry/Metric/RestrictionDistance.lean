import DifferentialGeometry.Geometry.Metric.Completeness
import DifferentialGeometry.Geometry.Metric.LocalChartDistance
import DifferentialGeometry.Geometry.Metric.Distance.Ball

set_option autoImplicit false

noncomputable section

open Bundle Set Manifold MeasureTheory
open scoped Manifold ContDiff ENNReal NNReal Topology

namespace DifferentialGeometry.Geometry.Metric

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem riemannianEDistOf_restrictOpen_le_pathELength
    (g : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M) [T2Space U]
    {x y : U} {γ : ℝ → M} (hγ : ContMDiffOn 𝓘(ℝ) I 1 γ (Icc 0 1))
    (hmem : MapsTo γ (Icc 0 1) U) (hx : γ 0 = x) (hy : γ 1 = y) :
    letI : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
    riemannianEDistOf (g.restrictOpen U) x y ≤ pathELength I γ 0 1 := by
  let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : RiemannianBundle (TangentSpace I : U → Type _) :=
    ⟨(g.restrictOpen U).toRiemannianMetric⟩
  let f : unitInterval → U := fun t => ⟨γ t, hmem t.property⟩
  have hfM : ContMDiff (𝓡∂ 1) I 1 ((Subtype.val : U → M) ∘ f) := by
    rw [← contMDiffOn_comp_projIcc_iff]
    apply hγ.congr
    intro t ht
    simp only [Function.comp_apply, f, projIcc_of_mem, ht]
  have hf : ContMDiff (𝓡∂ 1) I 1 f := by
    intro t
    exact (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff
      (P := ContDiffWithinAtProp (𝓡∂ 1) I 1) f univ t).mp (hfM t)
  let δ : Path x y := ⟨⟨f, hf.continuous⟩, Subtype.ext hx, Subtype.ext hy⟩
  have hδ : CMDiff 1 δ := hf
  change riemannianEDist I x y ≤ _
  rw [riemannianEDist]
  refine (biInf_le _ hδ).trans_eq ?_
  have hint : (∫⁻ t, ‖mfderiv% δ t 1‖ₑ) =
      ∫⁻ t, ‖mfderiv% (δ.map continuous_subtype_val) t 1‖ₑ := by
    apply lintegral_congr
    intro t
    have hc := mfderiv_comp t
      (hasMFDerivAt_subtype_val (I := I) U (δ t)).mdifferentiableAt
      (hδ.mdifferentiableAt one_ne_zero)
    change mfderiv% (δ.map continuous_subtype_val) t = _ at hc
    rw [← ofReal_norm, ← ofReal_norm, norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner]
    change ENNReal.ofReal (Real.sqrt ((g.restrictOpen U).inner (δ t)
      (mfderiv% δ t 1) (mfderiv% δ t 1))) =
      ENNReal.ofReal (Real.sqrt (g.inner ((δ.map continuous_subtype_val) t)
        (mfderiv% (δ.map continuous_subtype_val) t 1)
        (mfderiv% (δ.map continuous_subtype_val) t 1)))
    rw [hc, mfderiv_subtype_val]
    rfl
  rw [hint, lintegral_norm_mfderiv_Icc_eq_pathELength_projIcc]
  apply pathELength_congr
  intro t ht
  simp only [Function.comp_apply, projIcc_of_mem, ht]
  rfl

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem riemannianEDistOf_restrictOpen_lt_of_riemannianBallOf_subset
    (g : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M) [T2Space U]
    (p q : U) {r : ℝ} (hball : riemannianBallOf g p.val r ⊆ U)
    (hq : riemannianEDistOf g p q < ENNReal.ofReal r) :
    riemannianEDistOf (g.restrictOpen U) p q < ENNReal.ofReal r := by
  let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  obtain ⟨γ, hγ0, hγ1, hγ, hlen⟩ := exists_lt_of_riemannianEDist_lt hq
  have hmaps : MapsTo γ (Icc 0 1) U :=
    mapsTo_of_riemannianEDistOf_add_pathELength_lt g p U (ENNReal.ofReal r) hball γ hγ
      (by rw [hγ0, riemannianEDistOf_self, zero_add]; exact hlen)
  exact (riemannianEDistOf_restrictOpen_le_pathELength g U hγ hmaps hγ0 hγ1).trans_lt
    hlen

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem riemannianEDistOf_restrictOpen_eq_of_ball_subset
    (g : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M) [T2Space U]
    (p : M) (c : ℝ≥0)
    (hball : {q | riemannianEDistOf g p q < c} ⊆ U)
    (x y : U) (hx : riemannianEDistOf g p x < (c / 3 : ℝ≥0))
    (hy : riemannianEDistOf g p y < (c / 3 : ℝ≥0)) :
    riemannianEDistOf (g.restrictOpen U) x y = riemannianEDistOf g x y := by
  apply le_antisymm
  · let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
    by_contra hnot
    have hd : riemannianEDistOf g x y < riemannianEDistOf (g.restrictOpen U) x y :=
      lt_of_not_ge hnot
    have hdsmall : riemannianEDistOf g x y <
        ((c / 3 : ℝ≥0) : ℝ≥0∞) + (c / 3 : ℝ≥0) := by
      have hx' : riemannianEDistOf g x p < (c / 3 : ℝ≥0) := by
        rwa [riemannianEDistOf_comm]
      exact (riemannianEDistOf_triangle g x p y).trans_lt (ENNReal.add_lt_add hx' hy)
    obtain ⟨γ, hγ0, hγ1, hγ, hlength⟩ :=
      exists_lt_of_riemannianEDist_lt (lt_min hd hdsmall)
    have hlen := lt_of_lt_of_le hlength (min_le_right _ _)
    have hstart : riemannianEDistOf g p (γ 0) < (c / 3 : ℝ≥0) := by rwa [hγ0]
    have hsum : ((c / 3 : ℝ≥0) : ℝ≥0∞) +
        (((c / 3 : ℝ≥0) : ℝ≥0∞) + (c / 3 : ℝ≥0)) = (c : ℝ≥0∞) := by
      exact_mod_cast (show c / 3 + (c / 3 + c / 3) = c by ring)
    have hmaps : MapsTo γ (Icc 0 1) U :=
      mapsTo_of_riemannianEDistOf_add_pathELength_lt g p U c hball γ hγ
        (by simpa only [hsum] using ENNReal.add_lt_add hstart hlen)
    have hbound := riemannianEDistOf_restrictOpen_le_pathELength g U hγ hmaps hγ0 hγ1
    exact (not_lt_of_ge hbound) (lt_of_lt_of_le hlength (min_le_left _ _))
  · exact riemannianEDistOf_le_restrictOpen g U x y

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_mem_nhds_riemannianEDistOf_restrictOpen_eq [RegularSpace M]
    (g : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M) [T2Space U]
    (p : U) :
    ∃ V ∈ 𝓝 (p : M), ∀ x y : U, (x : M) ∈ V → (y : M) ∈ V →
      riemannianEDistOf (g.restrictOpen U) x y = riemannianEDistOf g x y := by
  let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  obtain ⟨c, hc, hball⟩ :=
    setOfPred_riemannianEDist_lt_subset_nhds I (U.isOpen.mem_nhds p.property)
  refine ⟨{q | riemannianEDistOf g p q < (c / 3 : ℝ≥0)}, ?_, ?_⟩
  · exact eventually_riemannianEDist_lt I (p : M) (by positivity)
  · intro x y hx hy
    exact riemannianEDistOf_restrictOpen_eq_of_ball_subset g U p c hball x y hx hy

end DifferentialGeometry.Geometry.Metric
