import DifferentialGeometry.Geometry.Comparison.FiniteMetric.FourPointApproximants
import DifferentialGeometry.Geometry.Metric.Approximation.FiniteMetric.SigmaCompact
import DifferentialGeometry.Geometry.Exponential.FiniteMetric.InteriorMinimizerUniqueness
import DifferentialGeometry.Geometry.Geodesic.Convergence.FiniteBundleReadings
import DifferentialGeometry.Geometry.Geodesic.Convergence.FiniteMetricMovingTime

/-!
# Initial directions of actual smooth minimizing arms

Uniform quadratic-form bounds give a compact vector subsequence. Actual distance and
moving-time finite geodesic convergence identify its endpoint, and interior uniqueness on
the longer minimizing ray identifies its initial direction without any angle-limit input.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold ContDiff ENNReal Topology

namespace DifferentialGeometry.Geometry.FiniteComparison

open DifferentialGeometry.Geometry.Comparison.Toponogov
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.MetricSmoothing

variable {E : Type*} [groupE : NormedAddCommGroup E] [innerE : InnerProductSpace ℝ E]
  [finiteE : FiniteDimensional ℝ E] [rankE : NeZero (Module.finrank ℝ E)]
  {H : Type*} [topologyH : TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [boundarylessI : I.Boundaryless] {M : Type*} [metricM : MetricSpace M]
  [chartsM : ChartedSpace H M] [manifoldM : IsManifold I ∞ M]
  [sigmaM : SigmaCompactSpace M] [bundleM : RiemannianBundle (fun x : M => TangentSpace I x)]
  [riemannianM : IsRiemannianManifold I M] [completeM : CompleteSpace M] {r : ℕ∞}

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

omit rankE sigmaM in
theorem exists_subsequence_minimizingArmDirections_tendsto
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 3 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (gSeq : ℕ → SmoothRiemannianMetric I M)
    (hbil : ∀ (k : ℕ) (x : M) (w : TangentSpace I x),
      (1 - 1 / ((k : ℝ) + 2)) ^ 2 * g.inner x w w ≤ (gSeq k).inner x w w ∧
        (gSeq k).inner x w w ≤ (1 + 1 / ((k : ℝ) + 2)) ^ 2 * g.inner x w w)
    (hconv : ∀ (q : M) (L : Set E), IsCompact L → L ⊆ (extChartAt I q).target →
      MapCPConvergenceOn L 2 (fun k => chartCoeff (gSeq k) q) (chartCoeff g q))
    (σ : ℕ → ℕ) (hσ : StrictMono σ) (vSeq : ℕ → E)
    {o : M} {u : E} {a s : ℝ} (hs : 0 < s) (hsa : s < a)
    (hu : g.inner o u u = 1)
    (hmin : dist o (g.expMap (⟨o, a • u⟩ : TangentBundle I M)) = a)
    (hv : ∀ k, (gSeq (σ k)).inner o (vSeq k) (vSeq k) = 1)
    (hreach : ∀ k,
      (gSeq (σ k)).expMap
        (⟨o, (riemannianEDistOf (I := I) (gSeq (σ k)) o
          (g.expMap (⟨o, s • u⟩ : TangentBundle I M))).toReal • vSeq k⟩ :
            TangentBundle I M) = g.expMap (⟨o, s • u⟩ : TangentBundle I M)) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ Tendsto (fun k => vSeq (ψ k)) atTop (𝓝 u) := by
  have hr1 : 1 ≤ r := (by norm_num : (1 : ℕ∞) ≤ 3).trans hr
  have hr2 : 2 ≤ r := (by norm_num : (2 : ℕ∞) ≤ 3).trans hr
  have hbound (k : ℕ) : g.inner o (vSeq k) (vSeq k) ≤ 4 := by
    have he := one_div_nat_add_two_mem (σ k)
    have hl := (hbil (σ k) o (vSeq k)).1
    rw [hv k] at hl
    have hsquare : (1 / 4 : ℝ) ≤ (1 - 1 / ((σ k : ℝ) + 2)) ^ 2 := by
      nlinarith [he.1, he.2]
    by_cases hn : 0 ≤ g.inner o (vSeq k) (vSeq k)
    · nlinarith [mul_le_mul_of_nonneg_right hsquare hn]
    · linarith
  obtain ⟨v, ψ, hψ, htangent⟩ :=
    exists_subseq_tendsto_tangentBundle_of_inner_le
      hr1 g tendsto_const_nhds vSeq hbound
  have hvector : Tendsto (fun k => vSeq (ψ k)) atTop (𝓝 v) := by
    have hread :=
      (tendsto_mfderiv_extChartAt_of_tendsto
        htangent).2
    rw [mfderiv_extChartAt_self] at hread
    exact hread
  have hmetric : Tendsto (fun k => g.inner o (vSeq (ψ k)) (vSeq (ψ k))) atTop
      (𝓝 (g.inner o v v)) := (g.inner o).continuous.clm_apply continuous_id |>.tendsto v |>.comp
        hvector
  have herr : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 2)) atTop (𝓝 (0 : ℝ)) := by
    refine (tendsto_one_div_add_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 1)).congr
      fun k => ?_
    simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]
    ring
  have hindex : StrictMono (fun k => σ (ψ k)) := hσ.comp hψ
  have herrSub := herr.comp hindex.tendsto_atTop
  have h1 : Tendsto (fun k : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have hlower := ((h1.sub herrSub).pow 2).mul hmetric
  have hupper := ((h1.add herrSub).pow 2).mul hmetric
  have hvunit : g.inner o v v = 1 := by
    apply le_antisymm
    · have hle := le_of_tendsto_of_tendsto' hlower
        (tendsto_const_nhds (x := (1 : ℝ))) (fun k => by
          simpa only [hv, Function.comp_apply] using (hbil (σ (ψ k)) o (vSeq (ψ k))).1)
      simpa using hle
    · have hle := le_of_tendsto_of_tendsto' (tendsto_const_nhds (x := (1 : ℝ))) hupper
        (fun k => by simpa only [hv, Function.comp_apply] using (hbil (σ (ψ k)) o (vSeq (ψ k))).2)
      simpa using hle
  let q := g.expMap (⟨o, s • u⟩ : TangentBundle I M)
  have hdistance : dist o q = s :=
    (g.dist_expMap_smul_eq_of_dist_eq hr1 hnorm hu hmin).1 s ⟨hs.le, hsa.le⟩
  let time : ℕ → ℝ := fun k =>
    (riemannianEDistOf (I := I) (gSeq (σ (ψ k))) o q).toReal
  have htime : Tendsto time atTop (𝓝 s) := by
    have ht := (tendsto_toReal_riemannianEDistOf_of_bilipschitz g hnorm gSeq hbil o q).comp
      hindex.tendsto_atTop
    change Tendsto time atTop (𝓝 (dist o q)) at ht
    rwa [hdistance] at ht
  have horder : (r : ℕ∞ω) + 1 ≤ (∞ : ℕ∞ω) := by
    exact_mod_cast (le_top : r + 1 ≤ (⊤ : ℕ∞))
  let h : ℕ → ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E
      (TangentSpace I : M → Type _) := fun k =>
    { gSeq (σ (ψ k)) with contMDiff := (gSeq (σ (ψ k))).contMDiff.of_le horder }
  have hdomain (k : ℕ) : (h k).geodesicFlowDomain = univ := by
    let gs := gSeq (σ (ψ k))
    have he := one_div_nat_add_two_mem (σ (ψ k))
    have hfin := riemannianEDistOf_ne_top_of_le g hnorm gs
      (by linarith [he.1] : 0 < 1 + 1 / ((σ (ψ k) : ℝ) + 2))
      (fun x w => (hbil (σ (ψ k)) x w).2)
    have hcomplete := completeSpace_inducedEMetricSpace_of_le g hnorm gs
      (by linarith [he.2] : 0 < 1 - 1 / ((σ (ψ k) : ℝ) + 2))
      (fun x w => (hbil (σ (ψ k)) x w).1)
    let approxMetric : MetricSpace M := @EMetricSpace.toMetricSpace M (inducedEMetricSpace gs)
      hfin
    let approxComplete : CompleteSpace M := hcomplete
    change gs.geodesicFlowDomain = univ
    exact geodesicFlowDomain_eq_univ_of_riemannianEDistOf gs (fun x y => edist_dist x y)
  have hdomainInf : g.geodesicFlowDomain = univ := g.geodesicFlowDomain_eq_univ hr2 hnorm
  have hflow :=
    finite_geodesicFlow_tendsto_at_moving_time
      hr1 h g (fun x L hL hLt => ((hconv x L hL hLt).mono_order (by norm_num)).comp_subseq
        hindex) (fun k => (⟨o, vSeq (ψ k)⟩ : TangentBundle I M)) ⟨o, v⟩
      (show s ∈ Ioo 0 (s + 1) from ⟨hs, by linarith⟩)
      (fun k t ht => by rw [hdomain k]; exact mem_univ _)
      (fun t ht => by rw [hdomainInf]; exact mem_univ _)
      (by simpa only [ContMDiffRiemannianMetric.geodesicFlow_zero _ hr1] using htangent)
      time htime
  have hproj := (FiberBundle.continuous_proj E (TangentSpace I)).tendsto
    (g.geodesicFlow (⟨o, v⟩ : TangentBundle I M) s) |>.comp hflow
  have hreachProj (k : ℕ) :
      ((h k).geodesicFlow (⟨o, vSeq (ψ k)⟩ : TangentBundle I M) (time k)).proj = q := by
    rw [← (h k).expMap_smul_eq_proj_geodesicFlow hr1 o (vSeq (ψ k)) (time k)
      (by rw [hdomain k]; exact mem_univ _)]
    exact hreach (ψ k)
  have heq : g.expMap (⟨o, s • v⟩ : TangentBundle I M) = q := by
    have hq := tendsto_nhds_unique hproj
      (show Tendsto (fun k =>
        ((h k).geodesicFlow (⟨o, vSeq (ψ k)⟩ : TangentBundle I M) (time k)).proj) atTop
        (𝓝 q) from by simpa only [hreachProj] using tendsto_const_nhds)
    exact (g.expMap_smul_eq_proj_geodesicFlow hr1 o v s
      (by rw [hdomainInf]; exact mem_univ _)).trans hq
  have hveq := g.eq_of_expMap_eq_on_interior_minimizing_ray hr2 hnorm hs hsa hu hvunit hmin heq
  exact ⟨ψ, hψ, hveq ▸ hvector⟩

end DifferentialGeometry.Geometry.FiniteComparison
