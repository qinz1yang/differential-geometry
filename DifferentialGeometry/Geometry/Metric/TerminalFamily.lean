import DifferentialGeometry.Geometry.Metric.Convergence.Compactness.ComponentSubsequence
import DifferentialGeometry.Geometry.Metric.Convergence.Window.AllOrders
import DifferentialGeometry.Geometry.Metric.Convergence.DerivativeNorm.Arity
import DifferentialGeometry.Geometry.Metric.Completeness
import Mathlib.Topology.Order.IsLUB

set_option autoImplicit false
noncomputable section
open Set Bundle Manifold Filter DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff BigOperators Topology
namespace DifferentialGeometry.Geometry.Metric
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

theorem exists_terminal_metric_of_reference_bounds (hne : Nonempty M)
    (gRef : SmoothRiemannianMetric I M) (hRef : RiemannianMetricComplete gRef)
    (g : ℝ → SmoothRiemannianMetric I M) (T Λ : ℝ) (hT : 0 < T) (hΛ : 1 ≤ Λ)
    (C L : ℕ → ℝ) (hL : ∀ N, 0 ≤ L N)
    (he : ∀ t ∈ Ico 0 T, MetricUniformEquivalentOn univ gRef (g t) Λ)
    (hc : ∀ N : ℕ, ∀ t ∈ Ico 0 T, ∀ x : M, metricCovDerivNorm N (g t) gRef x ≤ C N)
    (hl : ∀ N : ℕ, ∀ s ∈ Ico 0 T, ∀ t ∈ Ico 0 T, ∀ x : M,
      metricDerivNorm N (g s) (g t) gRef x ≤ L N * |s - t|) :
    ∃ gT : SmoothRiemannianMetric I M,
      RiemannianMetricComplete gT ∧ MetricUniformEquivalentOn univ gRef gT Λ ∧
      (∀ N : ℕ, ∀ x : M, metricCovDerivNorm N gT gRef x ≤ C N) ∧
      (∃ u : ℕ → ℝ, StrictMono u ∧ (∀ n, u n ∈ Ioo 0 T) ∧ Tendsto u atTop (𝓝 T) ∧
        MetricCInfConvergenceOnCompacts (fun n => g (u n)) gT gRef) ∧
      ∀ N : ℕ, ∀ t ∈ Ico 0 T, ∀ x : M,
        metricDerivNorm N (g t) gT gRef x ≤ L N * (T - t) := by
  obtain ⟨u, hu, huI, huT⟩ := exists_seq_strictMono_tendsto' hT
  have huC (n : ℕ) : u n ∈ Ico 0 T := ⟨(huI n).1.le, (huI n).2⟩
  have hΛp : 0 < Λ := lt_of_lt_of_le zero_lt_one hΛ
  obtain ⟨φ, hφ, gT, hgT⟩ := metricPreconvInf (I := I) (M := M)
    hne gRef (fun n => g (u n))
    (fun q _ _ => ⟨C q, fun n x _ => hc q (u n) (huC n) x⟩)
    ⟨Λ⁻¹, inv_pos.mpr hΛp, fun n x v => (he (u n) (huC n)).2 x (mem_univ x) v |>.1⟩
  have heT : MetricUniformEquivalentOn univ gRef gT Λ := by
    refine ⟨hΛ, ?_⟩
    intro x _ v
    have hh := metricCInf_inner _ gT gRef hgT x v v
    exact ⟨le_of_tendsto_of_tendsto tendsto_const_nhds hh (Eventually.of_forall fun n =>
      (he (u (φ n)) (huC (φ n))).2 x (mem_univ x) v |>.1),
      le_of_tendsto_of_tendsto hh tendsto_const_nhds (Eventually.of_forall fun n =>
      (he (u (φ n)) (huC (φ n))).2 x (mem_univ x) v |>.2)⟩
  have hpoint (N : ℕ) (x : M) (ε : ℝ) (hε : 0 < ε) :
      ∀ᶠ n in atTop, metricDerivNorm N (g (u (φ n))) gT
        gRef x < ε := by
    obtain ⟨n₀, hn₀⟩ := hgT {x} isCompact_singleton N ε hε
    exact eventually_atTop.mpr ⟨n₀, fun n hn =>
      (derivNorm_le_sup isCompact_singleton le_rfl _ _ _ (mem_singleton x)).trans_lt (hn₀ n hn)⟩
  have hcT (N : ℕ) (x : M) :
      metricCovDerivNorm N gT gRef x ≤ C N := by
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨n, hn⟩ := (hpoint N x ε hε).exists
    have hh := covNorm_le_add N gT (g (u (φ n))) gRef x
    rw [metricDerivNorm_symm] at hh
    exact hh.trans (add_le_add (hc N _ (huC (φ n)) x) hn.le)
  refine ⟨gT, RiemannianMetricComplete.of_lower hRef
    (inv_pos.mpr hΛp) (fun x v => (heT.2 x (mem_univ x) v).1), heT, hcT,
    ⟨u ∘ φ, hu.comp hφ, fun n => huI (φ n), huT.comp hφ.tendsto_atTop, hgT⟩, ?_⟩
  intro N t ht x
  apply le_of_forall_pos_le_add
  intro ε hε
  have hafter : ∀ᶠ n in atTop, t < u (φ n) :=
    (huT.comp hφ.tendsto_atTop).eventually_const_lt ht.2
  obtain ⟨n, hn, hnt⟩ := ((hpoint N x ε hε).and hafter).exists
  have hh := metricDerivNorm_triangle N (g t) (g (u (φ n))) gT
    gRef x
  have htime := hl N t ht (u (φ n)) (huC (φ n)) x
  rw [abs_of_nonpos (sub_nonpos.mpr hnt.le), neg_sub] at htime
  have hscale := mul_le_mul_of_nonneg_left (sub_le_sub_right (huI (φ n)).2.le t) (hL N)
  exact hh.trans (add_le_add (htime.trans hscale) hn.le)

private theorem closed_gram_jets_of_time_bounds
    (gRef : SmoothRiemannianMetric I M) (τ : ℝ) (g : ℝ → SmoothRiemannianMetric I M)
    (hlip : ∀ K : Set M, IsCompact K → ∀ p : ℕ, ∃ Lp : ℝ, 0 ≤ Lp ∧
      ∀ s ∈ Icc 0 τ, ∀ t ∈ Icc 0 τ, ∀ a : ℕ, a ≤ p → ∀ x ∈ K,
        metricDerivNorm a (g s) (g t) gRef x ≤ Lp * |s - t|) :
    ∀ (r : ℕ) (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContinuousOn
        (fun p : ℝ × E => iteratedFDeriv ℝ r (chartGramOnE (g p.1) x₀ i j) p.2)
        (Icc 0 τ ×ˢ interior (extChartAt I x₀).target) := by
  intro r x₀ i j p₀ hp₀
  obtain ⟨C, hCc, hCint, hCsub⟩ := exists_compact_subset isOpen_interior hp₀.2
  have hCtgt : C ⊆ (extChartAt I x₀).target := hCsub.trans interior_subset
  let K : Set M := (extChartAt I x₀).symm '' C
  have hKc : IsCompact K :=
    hCc.image_of_continuousOn ((continuousOn_extChartAt_symm (I := I) x₀).mono hCtgt)
  have hKchart : K ⊆ (chartAt H x₀).source := by
    rintro y ⟨z, hz, rfl⟩
    rw [← extChartAt_source_eq_chartAt_source (I := I)]
    exact (extChartAt I x₀).map_target (hCtgt hz)
  obtain ⟨Cjet, hCjet, hjet⟩ := chartJet_sub_le gRef x₀ hKc hKchart r
  obtain ⟨Lp, hLp, hb⟩ := hlip K hKc r
  let A := Cjet * ((r + 1 : ℕ) : ℝ) * Lp
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hcOn : ContinuousOn
      (fun p : ℝ × E => iteratedFDeriv ℝ r (chartGramOnE (g p.1) x₀ i j) p.2)
      (Icc 0 τ ×ˢ C) := by
    apply continuousOn_prod_of_continuousOn_lipschitzOnWith _ ⟨A, hA⟩
    · intro t _ z hz
      have hh := (chartGramOnE_contDiffOn (I := I) (g t) x₀ i j).mono interior_subset
      exact ((hh.contDiffAt (isOpen_interior.mem_nhds (hCsub hz))).continuousAt_iteratedFDeriv
        (WithTop.coe_le_coe.2 (le_top : (r : ℕ∞) ≤ (⊤ : ℕ∞)))).continuousWithinAt
    · intro z hz
      apply LipschitzOnWith.of_dist_le_mul
      intro s hs t ht
      let y : M := (extChartAt I x₀).symm z
      have hyK : y ∈ K := ⟨z, hz, rfl⟩
      have hright : extChartAt I x₀ y = z := (extChartAt I x₀).right_inv (hCtgt hz)
      rw [dist_eq_norm, Real.dist_eq]
      change ‖iteratedFDeriv ℝ r (chartGramOnE (g s) x₀ i j) z -
        iteratedFDeriv ℝ r (chartGramOnE (g t) x₀ i j) z‖ ≤ A * |s - t|
      have hh := hjet (g s) (g t) y hyK i j
      rw [hright] at hh
      refine hh.trans ?_
      calc
        Cjet * ∑ q ∈ Finset.range (r + 1), metricDerivNorm q (g s) (g t) gRef y
            ≤ Cjet * ∑ _q ∈ Finset.range (r + 1), Lp * |s - t| := by
              apply mul_le_mul_of_nonneg_left _ hCjet
              exact Finset.sum_le_sum (fun q hq => hb s hs t ht q
                (Nat.lt_succ_iff.mp (Finset.mem_range.mp hq)) y hyK)
        _ = A * |s - t| := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          dsimp only [A]
          ring
  have hmem : Icc 0 τ ×ˢ C ∈ 𝓝[Icc 0 τ ×ˢ interior (extChartAt I x₀).target] p₀ := by
    have hnhds : (univ ×ˢ interior C : Set (ℝ × E)) ∈ 𝓝 p₀ :=
      prod_mem_nhds Filter.univ_mem (isOpen_interior.mem_nhds hCint)
    refine Filter.mem_of_superset (inter_mem_nhdsWithin _ hnhds) ?_
    rintro ⟨t, z⟩ ⟨⟨ht, _⟩, _, hzC⟩
    exact ⟨ht, interior_subset hzC⟩
  exact (hcOn.continuousWithinAt ⟨hp₀.1, interior_subset hCint⟩).mono_of_mem_nhdsWithin hmem

theorem exists_closed_terminal_family_of_reference_bounds (hne : Nonempty M)
    (gRef : SmoothRiemannianMetric I M) (hRef : RiemannianMetricComplete gRef)
    (g : ℝ → SmoothRiemannianMetric I M) (T Λ : ℝ) (hT : 0 < T) (hΛ : 1 ≤ Λ)
    (C L : ℕ → ℝ) (hL : ∀ N, 0 ≤ L N)
    (he : ∀ t ∈ Ico 0 T, MetricUniformEquivalentOn univ gRef (g t) Λ)
    (hc : ∀ N : ℕ, ∀ t ∈ Ico 0 T, ∀ x : M, metricCovDerivNorm N (g t) gRef x ≤ C N)
    (hl : ∀ N : ℕ, ∀ s ∈ Ico 0 T, ∀ t ∈ Ico 0 T, ∀ x : M,
      metricDerivNorm N (g s) (g t) gRef x ≤ L N * |s - t|) :
    ∃ G : ℝ → SmoothRiemannianMetric I M,
      (∀ t ∈ Ico 0 T, G t = g t) ∧
      (∀ t ∈ Icc 0 T, RiemannianMetricComplete (G t)) ∧
      (∀ t ∈ Icc 0 T, MetricUniformEquivalentOn univ gRef (G t) Λ) ∧
      (∀ N : ℕ, ∀ t ∈ Icc 0 T, ∀ x : M, metricCovDerivNorm N (G t) gRef x ≤ C N) ∧
      (∀ N : ℕ, ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T, ∀ x : M,
        metricDerivNorm N (G s) (G t) gRef x ≤ L N * |s - t|) ∧
      ∀ (r : ℕ) (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
        ContinuousOn
          (fun p : ℝ × E => iteratedFDeriv ℝ r (chartGramOnE (G p.1) x₀ i j) p.2)
          (Icc 0 T ×ˢ interior (extChartAt I x₀).target) := by
  classical
  obtain ⟨gT, _, heT, hcT, _, hrate⟩ :=
    exists_terminal_metric_of_reference_bounds hne gRef hRef g T Λ hT hΛ C L hL he hc hl
  let G := fun t => if t < T then g t else gT
  have heG (t : ℝ) (ht : t ∈ Icc 0 T) : MetricUniformEquivalentOn univ gRef (G t) Λ := by
    by_cases htT : t < T
    · simpa only [G, ite_eq_left htT] using he t ⟨ht.1, htT⟩
    · simpa only [G, ite_eq_right htT] using heT
  have hcG (N : ℕ) (t : ℝ) (ht : t ∈ Icc 0 T) (x : M) :
      metricCovDerivNorm N (G t) gRef x ≤ C N := by
    by_cases htT : t < T
    · simpa only [G, ite_eq_left htT] using hc N t ⟨ht.1, htT⟩ x
    · simpa only [G, ite_eq_right htT] using hcT N x
  have hlG (N : ℕ) (s : ℝ) (hs : s ∈ Icc 0 T) (t : ℝ) (ht : t ∈ Icc 0 T) (x : M) :
      metricDerivNorm N (G s) (G t) gRef x ≤ L N * |s - t| := by
    by_cases hsT : s < T
    · by_cases htT : t < T
      · simpa only [G, ite_eq_left hsT, ite_eq_left htT] using hl N s ⟨hs.1, hsT⟩ t ⟨ht.1, htT⟩ x
      · have htEq : t = T := le_antisymm ht.2 (le_of_not_gt htT)
        subst t
        simpa only [G, ite_eq_left hsT, lt_self_iff_false, ite_false,
          abs_of_nonpos (sub_nonpos.mpr hsT.le), neg_sub] using hrate N s ⟨hs.1, hsT⟩ x
    · have hsEq : s = T := le_antisymm hs.2 (le_of_not_gt hsT)
      subst s
      by_cases htT : t < T
      · simpa only [G, ite_eq_left htT, lt_self_iff_false, ite_false, metricDerivNorm_symm,
          abs_of_nonneg (sub_nonneg.mpr htT.le)] using hrate N t ⟨ht.1, htT⟩ x
      · simp only [G, lt_self_iff_false, ite_false, ite_eq_right htT, metricDerivNorm_self]
        exact mul_nonneg (hL N) (abs_nonneg _)
  refine ⟨G, fun t ht => ite_eq_left ht.2, ?_, heG, hcG, hlG, ?_⟩
  · intro t ht
    exact RiemannianMetricComplete.of_lower hRef
      (inv_pos.mpr (lt_of_lt_of_le zero_lt_one hΛ))
      (fun x v => ((heG t ht).2 x (mem_univ x) v).1)
  · apply closed_gram_jets_of_time_bounds gRef T G
    intro K _ p
    let A := ∑ a ∈ Finset.range (p + 1), L a
    refine ⟨A, Finset.sum_nonneg (fun a _ => hL a), ?_⟩
    intro s hs t ht a ha x _
    have haA : L a ≤ A := Finset.single_le_sum (s := Finset.range (p + 1)) (a := a)
      (f := L) (fun b _ => hL b) (Finset.mem_range.mpr (by omega))
    exact (hlG a s hs t ht x).trans (mul_le_mul_of_nonneg_right haA (abs_nonneg _))
end DifferentialGeometry.Geometry.Metric
