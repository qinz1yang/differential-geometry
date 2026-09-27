import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Norm.Convergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalCovariantBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Metric.Endpoint.CovariantEvolution

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Filter Set DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold ContDiff _root_.Topology BigOperators
open Perelman.CanonicalNeighborhood.FiniteHorn
  (exists_local_curvature_derivative_bounds_before_terminal
    metric_covariant_bounds_of_local_curvature_bounds)

section Regular

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem solution_metricCovDerivNorm_continuousAt_regular
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {t : ℝ} (ht : t ∈ D.regular) (R : SmoothRiemannianMetric I M) (q : ℕ) (x : M) :
    ContinuousAt (fun s => metricCovDerivNorm q (S.base.metric s) R x) t := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let _ : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by decide)
  let _ : IsManifold I 2 M := IsManifold.of_le (n := ∞) (by decide)
  classical
  obtain ⟨basis, horth⟩ := exists_orthonormal_basis R x
  have hinv := metricInverseInBasis_of_orthonormal R basis horth
  have hnorm (g : SmoothRiemannianMetric I M) :
      metricCovDerivNorm q g R x = Real.sqrt
        (∑ slots : Fin (q + 2) → Fin (Module.finrank ℝ (TangentSpace I x)),
          (component0S basis (metricCovDeriv g R q x) slots) ^ 2) := by
    rw [metricCovDerivNorm, normSq0S_identity_eq_sum_sq R x (q + 2) basis hinv]
  simp only [hnorm]
  apply ContinuousAt.sqrt
  apply tendsto_finsetSum
  intro slots _
  have h := solutionTower_hasDerivAt R S hS q
    (solutionTowerSwap_regularity R S hS q (fun {_s} hs => D.regular_isOpen.mem_nhds hs))
    q le_rfl t ht x (fun i => basis (slots i))
  exact h.continuousAt.pow 2


end Regular

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [BoundarylessManifold I M]

theorem solution_metricCovDeriv_component_continuousWithinAt_terminal
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a b : ℝ} (hab : a < b) (hslab : Icc a b ⊆ D.carrier)
    (hregular : Ioo a b ⊆ D.regular)
    (R : SmoothRiemannianMetric I M) (q : ℕ) (x : M)
    (basis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x))
    (slots : Fin (q + 2) → Fin (Module.finrank ℝ E)) :
    ContinuousWithinAt
      (fun t => component0S basis (metricCovDeriv (S.base.metric t) R q x) slots) (Iic b) b := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let _ : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by decide)
  let _ : IsManifold I 2 M := IsManifold.of_le (n := ∞) (by decide)
  let _ : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional I
  obtain ⟨V, d, C₀, hV, hxV, hVc, had, hdb, hcurv⟩ :=
    exists_local_curvature_derivative_bounds_before_terminal
      S hS hab hslab hregular x
  obtain ⟨K, hK, hxK, hKV⟩ := exists_compact_between isCompact_singleton hV
    (singleton_subset_iff.mpr hxV)
  let U : TopologicalSpace.Opens M := ⟨interior K, isOpen_interior⟩
  let _ : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen I U.isOpen)
  let c := (d + b) / 2
  have hdc : d < c := by dsimp [c]; linarith
  have hcb : c < b := by dsimp [c]; linarith
  have hbounds := metric_covariant_bounds_of_local_curvature_bounds
    S hS (a := c) (b := b)
    (fun t ht => hslab ⟨had.le.trans (hdc.le.trans ht.1), ht.2⟩)
    (fun t ht => hregular ⟨had.trans (hdc.trans_le ht.1), ht.2⟩)
    hV hVc R C₀ (fun m t ht y hy => hcurv m t ⟨hdc.trans_le ht.1, ht.2⟩ y hy)
    hK hKV
  rw [continuousWithinAt_iff_continuousAt_domRestrict _ (s := Iic b) (x := b)
    (by change b ≤ b; exact le_rfl)]
  apply tendsto_iff_seq_tendsto.mpr
  intro tau htau
  have htauVal : Tendsto (fun k => (tau k).val) atTop (𝓝 b) :=
    continuous_subtype_val.continuousAt.tendsto.comp htau
  let G : ℕ → SmoothRiemannianMetric I U :=
    fun k => (S.base.metric (tau k).val).restrictOpen U
  have hbound : ∀ r : ℕ, ∀ L : Set U, IsCompact L → ∃ C : ℝ,
      ∀ k : ℕ, ∀ y ∈ L, metricCovDerivNorm r (G k) (R.restrictOpen U) y ≤ C := by
    intro r L hL
    apply cov_bdd_of_eventual hL r G (R.restrictOpen U)
    obtain ⟨C, _, hC⟩ := hbounds r
    obtain ⟨Cb, hCb⟩ := metricCovDerivNorm_bddOn hK r (S.base.metric b) R
    obtain ⟨N, hN⟩ := eventually_atTop.mp (htauVal.eventually_const_lt hcb)
    refine ⟨N, max C Cb, fun k hk y _ => ?_⟩
    dsimp only [G]
    rw [covNorm_restrictOpen]
    rcases (mem_Iic.mp (tau k).property).lt_or_eq with hlt | heq
    · exact (hC _ ⟨(hN k hk).le, hlt⟩ y (interior_subset y.property)).trans (le_max_left _ _)
    · rw [heq]
      exact (hCb y (interior_subset y.property)).trans (le_max_right _ _)
  have hinner (y : U) : Tendsto (fun k => (G k).inner y) atTop
      (𝓝 (((S.base.metric b).restrictOpen U).inner y)) := by
    have hc : ContinuousWithinAt (fun t => (S.base.metric t).inner (y : M)) D.carrier b := by
      apply continuousWithinAt_clm_apply.mpr
      intro v
      apply continuousWithinAt_clm_apply.mpr
      intro w
      exact hS.smoothMetric.coeff_cont (y : M) v w b (hslab ⟨hab.le, le_rfl⟩)
    apply hc.tendsto.comp
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨htauVal, ?_⟩
    filter_upwards [htauVal.eventually_const_lt hab] with k hk
    exact hslab ⟨hk.le, (tau k).property⟩
  have hn := metricCovDeriv_component_tendsto_of_uniform_bounds G
    ((S.base.metric b).restrictOpen U) (R.restrictOpen U) hbound hinner q
    ⟨x, hxK (mem_singleton x)⟩ basis slots
  change Tendsto
    (fun k => metricCovDeriv ((S.base.metric (tau k).val).restrictOpen U)
      (R.restrictOpen U) q ⟨x, hxK (mem_singleton x)⟩ (fun i => basis (slots i))) atTop
    (𝓝 (metricCovDeriv ((S.base.metric b).restrictOpen U) (R.restrictOpen U) q
      ⟨x, hxK (mem_singleton x)⟩ (fun i => basis (slots i)))) at hn
  have heq (g : SmoothRiemannianMetric I M) :
      metricCovDeriv (g.restrictOpen U) (R.restrictOpen U) q
        ⟨x, hxK (mem_singleton x)⟩ (fun i => basis (slots i)) =
      component0S basis (metricCovDeriv g R q x) slots := by
    exact metricCovDeriv_restrictOpen_apply (I := I) g R U q
      ⟨x, hxK (mem_singleton x)⟩ (fun i => basis (slots i))
  simp only [heq] at hn
  exact hn

theorem solution_metricCovDerivNorm_continuousWithinAt_terminal
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a b : ℝ} (hab : a < b) (hslab : Icc a b ⊆ D.carrier)
    (hregular : Ioo a b ⊆ D.regular)
    (R : SmoothRiemannianMetric I M) (q : ℕ) (x : M) :
    ContinuousWithinAt (fun t => metricCovDerivNorm q (S.base.metric t) R x) (Iic b) b := by
  classical
  obtain ⟨basis, horth⟩ := exists_orthonormal_basis R x
  have hinv := metricInverseInBasis_of_orthonormal R basis horth
  have hnorm (g : SmoothRiemannianMetric I M) :
      metricCovDerivNorm q g R x = Real.sqrt
        (∑ slots : Fin (q + 2) → Fin (Module.finrank ℝ (TangentSpace I x)),
          (component0S basis (metricCovDeriv g R q x) slots) ^ 2) := by
    rw [metricCovDerivNorm, normSq0S_identity_eq_sum_sq R x (q + 2) basis hinv]
  simp only [hnorm]
  apply ContinuousWithinAt.sqrt
  apply tendsto_finsetSum
  intro slots _
  exact (solution_metricCovDeriv_component_continuousWithinAt_terminal S hS hab hslab
    hregular R q x basis slots).pow 2


theorem solution_metricCovDerivNorm_continuousOn_closed_interval
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a b : ℝ} (hab : a < b) (hslab : Icc a b ⊆ D.carrier)
    (hregular : Ico a b ⊆ D.regular)
    (R : SmoothRiemannianMetric I M) (q : ℕ) (x : M) :
    ContinuousOn (fun t => metricCovDerivNorm q (S.base.metric t) R x) (Icc a b) := by
  intro t ht
  rcases ht.2.lt_or_eq with htb | htb
  · exact (solution_metricCovDerivNorm_continuousAt_regular S hS
      (hregular ⟨ht.1, htb⟩) R q x).continuousWithinAt
  · subst t
    exact (solution_metricCovDerivNorm_continuousWithinAt_terminal S hS hab hslab
      (Ioo_subset_Ico_self.trans hregular) R q x).mono Icc_subset_Iic_self

end DifferentialGeometry.PDE.RicciFlow
