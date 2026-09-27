import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.MetricTruncationNorm
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.ReferenceCurvatureBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.CompactDoublePatchCurvature
import DifferentialGeometry.Geometry.Curvature.DerivativeIsometry
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.CompactUniformRegularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.MixedMetricBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.CompactCoreMaps
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.CompleteReferenceLimit
import DifferentialGeometry.Geometry.Curvature.RiemannRicciNorm
import DifferentialGeometry.Geometry.Metric.Coordinates.ChartGram
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.Convergence

set_option autoImplicit false
noncomputable section
open Set Bundle Manifold TopologicalSpace DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Integral.Measure DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.PDE.RicciFlow.StandardCap DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology ENNReal BigOperators
namespace DifferentialGeometry.PDE.RicciFlow
private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev E4 := EuclideanSpace ℝ (Fin 4)
private abbrev S3 := Metric.sphere (0 : E4) 1
private local instance : Fact (Module.finrank ℝ E4 = 3 + 1) := ⟨by simp⟩
private local instance (U : Opens E3) : SigmaCompactSpace U :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen (𝓡 3) U.isOpen)

private theorem intrinsic_bound_on_ambient (k : ℕ) (ell B A : ℝ)
    (hA : ∀ (U : Opens E3) (g : SmoothRiemannianMetric (𝓡 3) U) (q : U),
      (∀ v : TangentSpace (𝓡 3) q,
        ell * (DifferentialGeometry.PDE.RicciFlow.StandardCap.metric.restrictOpen U).inner q v v ≤ g.inner q v v) →
      (∀ j ≤ k + 2, metricDerivNorm j g
        (DifferentialGeometry.PDE.RicciFlow.StandardCap.metric.restrictOpen U)
        (DifferentialGeometry.PDE.RicciFlow.StandardCap.metric.restrictOpen U) q ≤ B) →
      Real.sqrt (normSq0S g q (4 + k) (iterCov g 4 (metricRm04 g) k q)) ≤ A)
    (g : SmoothRiemannianMetric (𝓡 3) E3)
    (hlow : ∀ (x : E3) (v : TangentSpace (𝓡 3) x),
      ell * DifferentialGeometry.PDE.RicciFlow.StandardCap.metric.inner x v v ≤ g.inner x v v)
    (hb : ∀ j ≤ k + 2, ∀ x : E3, metricDerivNorm j g
      DifferentialGeometry.PDE.RicciFlow.StandardCap.metric DifferentialGeometry.PDE.RicciFlow.StandardCap.metric x ≤ B)
    (x : E3) :
    Real.sqrt (normSq0S g x (4 + k) (iterCov g 4 (metricRm04 g) k x)) ≤ A := by
  let U : Opens E3 := ⊤
  let q : U := ⟨x, mem_univ x⟩
  have hh := hA U (g.restrictOpen U) q
    (fun v => hlow x v)
    (fun j hj => (metricDerivNorm_restrictOpen g DifferentialGeometry.PDE.RicciFlow.StandardCap.metric
      DifferentialGeometry.PDE.RicciFlow.StandardCap.metric U j q).le.trans (hb j hj x))
  have he := normSq_iterCov_metricRm04_of_metric_isometry_on_open
    (g.restrictOpen U) g (⊤ : Opens U) (Subtype.val : U → E3)
    (contMDiff_subtype_val.contMDiffOn)
    (fun y _ v w => by
      rw [mfderiv_subtype_val_apply, mfderiv_subtype_val_apply]
      exact SmoothRiemannianMetric.restrictOpen_inner g U y v w)
    k ⟨q, mem_univ q⟩
  exact (congrArg Real.sqrt he).symm.le.trans hh

theorem exists_uniform_compact_truncation_curvature_bounds
    (ell : ℝ) (hell : 0 < ell) (C : ℕ → ℝ) (hC : ∀ k, 0 ≤ C k) :
    ∃ A : ℕ → ℝ, (∀ k, 0 < A k) ∧
      ∀ g : SmoothRiemannianMetric (𝓡 3) E3,
      (∀ (x : E3) (v : TangentSpace (𝓡 3) x),
        ell * DifferentialGeometry.PDE.RicciFlow.StandardCap.metric.inner x v v ≤ g.inner x v v) →
      (∀ k : ℕ, ∀ x : E3, metricDerivNorm k g
        DifferentialGeometry.PDE.RicciFlow.StandardCap.metric DifferentialGeometry.PDE.RicciFlow.StandardCap.metric x ≤ C k) →
      ∀ (north : S3) (R : ℝ) (hR : max transitionEnd 2 + 2 ≤ R),
        transitionEnd + 4 ≤ R → ∀ k : ℕ, ∀ x : S3,
          Real.sqrt (normSq0S (compactDoubleTruncationMetric north R hR g) x (4 + k)
            (iterCov (compactDoubleTruncationMetric north R hR g) 4
              (metricRm04 (compactDoubleTruncationMetric north R hR g)) k x)) ≤ A k := by
  choose κ hκ hκbound using exists_uniform_metricTruncation_derivative_bound
  let Q : ℕ → ℝ := fun N => ∑ j ∈ Finset.range (N + 1), C j
  have hQ (N : ℕ) : 0 ≤ Q N := Finset.sum_nonneg (fun j _ => hC j)
  let D : ℕ → ℝ := fun N => κ N * Q N
  have hD (N : ℕ) : 0 ≤ D N := mul_nonneg (hκ N).le (hQ N)
  let ell' : ℝ := min ell 1
  have hell' : 0 < ell' := lt_min hell zero_lt_one
  choose A _hA hAbound using fun k =>
    exists_pos_bound_intrinsic_curvature_derivative_of_metric_jets_on_opens
      k ell' (D (k + 2)) hell' (hD (k + 2))
  obtain ⟨AC, hAC, hpatch⟩ := exists_uniform_bounds_iterCov_compactDoublePatchedMetric A
  refine ⟨AC, hAC, ?_⟩
  intro g hlower hjets north R hR hlarge
  have hRtwo : 2 < R := by linarith [le_max_right transitionEnd 2]
  have hinput (N j : ℕ) (hjN : j ≤ N) (x : E3) :
      metricDerivNorm j g DifferentialGeometry.PDE.RicciFlow.StandardCap.metric
        DifferentialGeometry.PDE.RicciFlow.StandardCap.metric x ≤ Q N := by
    exact (hjets j x).trans
      (Finset.single_le_sum (s := Finset.range (N + 1)) (a := j) (f := C)
        (fun i _ => hC i) (Finset.mem_range.mpr (by omega)))
  have htruncLower (x : E3) (v : TangentSpace (𝓡 3) x) :
      ell' * DifferentialGeometry.PDE.RicciFlow.StandardCap.metric.inner x v v ≤
        (metricTruncation g R hRtwo).inner x v v :=
    metricTruncation_lower g R hRtwo ell hlower x v
  have hb (N j : ℕ) (hjN : j ≤ N) (x : E3) :
      metricDerivNorm j (metricTruncation g R hRtwo)
        DifferentialGeometry.PDE.RicciFlow.StandardCap.metric DifferentialGeometry.PDE.RicciFlow.StandardCap.metric x ≤ D N :=
    hκbound N g R hRtwo hlarge (Q N) (hQ N) (hinput N) j hjN x
  have hcurv (k : ℕ) (x : E3) :
      Real.sqrt (normSq0S (metricTruncation g R hRtwo) x (4 + k)
        (iterCov (metricTruncation g R hRtwo) 4
          (metricRm04 (metricTruncation g R hRtwo)) k x)) ≤ A k :=
    intrinsic_bound_on_ambient k ell' (D (k + 2)) (A k) (hAbound k)
      (metricTruncation g R hRtwo) htruncLower (hb (k + 2)) x
  exact hpatch north R hR (metricTruncation g R hRtwo)
    (fun _ hx v w => metricTruncation_inner_end g R hRtwo hx v w) hcurv

private theorem ricci_bound_of_mixed_zero
    (τ : ℝ) (hτ : 0 < τ)
    (Z : SolutionOn (I := 𝓡 3) (M := S3) (RealTimeInterval.closed 0 τ hτ.le))
    (B : ℝ)
    (hRm : ∀ t ∈ Icc 0 τ, ∀ y : S3,
      Real.sqrt (normSq0S (Z.base.metric t) y 4 (nablaKRm04Field Z t 0 y)) ≤ B) :
    ∀ t ∈ Icc 0 τ, ∀ y : S3, ricciNorm Z t y ≤ 81 * B ^ 2 := by
  intro t ht y
  have hRsq := (Real.sqrt_le_iff.mp (hRm t ht y)).2
  have hh := ricTower_normSq_le Z t 0 y
  norm_num only [finrank_euclideanSpace, Fintype.card_fin, Nat.cast_ofNat,
    Nat.reduceAdd, pow_succ, pow_zero] at hh
  change ricciNorm Z t y ≤ 81 *
    normSq0S (Z.base.metric t) y 4 (nablaKRm04Field Z t 0 y) at hh
  nlinarith only [hRsq, hh]

theorem exists_uniform_complete_cap_reference_core_restarts
    (ell : ℝ) (hell : 0 < ell) (C : ℕ → ℝ) (hC : ∀ k, 0 ≤ C k) :
    ∃ τ : ℝ, ∃ hτ : 0 < τ, ∃ B : ℕ → ℝ, (∀ N, 0 ≤ B N) ∧
      ∃ ΛZ : ℝ, 1 ≤ ΛZ ∧ ∃ CZ LZ : ℕ → ℝ,
      (∀ N, 0 ≤ CZ N) ∧ (∀ N, 0 ≤ LZ N) ∧
      ∀ g : SmoothRiemannianMetric (𝓡 3) E3,
      (∀ (x : E3) (v : TangentSpace (𝓡 3) x),
        ell * DifferentialGeometry.PDE.RicciFlow.StandardCap.metric.inner x v v ≤ g.inner x v v) →
      (∀ k : ℕ, ∀ x : E3, metricDerivNorm k g
        DifferentialGeometry.PDE.RicciFlow.StandardCap.metric DifferentialGeometry.PDE.RicciFlow.StandardCap.metric x ≤ C k) →
      ∀ north : S3,
        ∃ Z : ℕ → SolutionOn (I := 𝓡 3) (M := S3) (RealTimeInterval.closed 0 τ hτ.le),
        ∃ hZ : ∀ j, IsSolutionOn (Z j),
          (∀ stage : ℕ,
            let R := compactCapApproximationRadius (stage + 2)
            let hR := compactCapApproximationRadius_large (stage + 2)
            (Z stage).base.metric 0 = compactDoubleTruncationMetric north R hR g ∧
            (∀ t ∈ Icc 0 τ, RiemannianMetricComplete ((Z stage).base.metric t)) ∧
            (∀ (x₀ : S3) (i j : Fin (Module.finrank ℝ E3)),
              ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) 𝓘(ℝ, ℝ) ∞
                (fun p : ℝ × S3 => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix ((Z stage).base.metric p.1) x₀ p.2 i j)
                (Icc 0 τ ×ˢ (trivializationAt E3 (TangentSpace (𝓡 3)) x₀).baseSet)) ∧
            (∀ t ∈ Icc 0 τ, ∀ (x : S3) (v w : TangentSpace (𝓡 3) x),
              HasDerivWithinAt (fun r => ((Z stage).base.metric r).inner x v w)
                (-2 * ricciTensor ((Z stage).base.metric t) x v w) (Ici 0) t) ∧
            (∀ N a b : ℕ, a + 2 * b ≤ N → ∀ t ∈ Icc 0 τ, ∀ x : S3,
              Real.sqrt (normSq0S ((Z stage).base.metric t) x (4 + a)
                (iteratedCovariantTimeDerivWithin (Z stage).base.metric
                  (fun r => nablaKRm04Field (Z stage) r a x) (Icc 0 τ) b t)) ≤ B N) ∧
            (∀ x ∈ Metric.ball (0 : E3) (R + 1), ∀ v w : E3,
              ((Z stage).base.metric 0).inner (compactDoubleCapMap north R x)
                (mfderiv (𝓡 3) (𝓡 3) (compactDoubleCapMap north R) x v)
                (mfderiv (𝓡 3) (𝓡 3) (compactDoubleCapMap north R) x w) =
                  (metricTruncation g R (by linarith [le_max_right transitionEnd 2])).inner x v w) ∧
            (∀ (x : E3), ‖x‖ ≤ R - 2 → ∀ v w : E3,
              ((Z stage).base.metric 0).inner (compactDoubleCapMap north R x)
                (mfderiv (𝓡 3) (𝓡 3) (compactDoubleCapMap north R) x v)
                (mfderiv (𝓡 3) (𝓡 3) (compactDoubleCapMap north R) x w) = g.inner x v w) ∧
            (∀ t ∈ Icc 0 τ, MetricUniformEquivalentOn univ
              ((Z stage).base.metric 0) ((Z stage).base.metric t) ΛZ) ∧
            (∀ N : ℕ, ∀ t ∈ Icc 0 τ, ∀ x : S3,
              metricCovDerivNorm N ((Z stage).base.metric t) ((Z stage).base.metric 0) x ≤ CZ N) ∧
            ∀ N : ℕ, ∀ s ∈ Icc 0 τ, ∀ t ∈ Icc 0 τ, ∀ x : S3,
              metricDerivNorm N ((Z stage).base.metric s) ((Z stage).base.metric t)
                ((Z stage).base.metric 0) x ≤ LZ N * |s - t|) ∧
          let Φ := compactCorePointedMaps g north Z hZ
          let hsrc := compactCorePointedMaps_sourceSigma g north Z hZ
          let htgt := compactCorePointedMaps_targetSigma g north Z hZ
          ∃ bf : BumpFamily Φ,
          ∃ co : FlowMetricConvergenceData Φ g bf hsrc htgt 0 τ,
            (∀ stage t, t ∈ Icc 0 τ →
              letI : TopologicalSpace (SourceDomain Φ stage) := sourceDomTop Φ stage
              letI : ChartedSpace E3 (SourceDomain Φ stage) := sourceDomCharted Φ stage
              letI : IsManifold (𝓡 3) ∞ (SourceDomain Φ stage) := sourceDomSmooth Φ stage
              ∀ (y : SourceDomain Φ stage) (v : TangentSpace (𝓡 3) y),
                ΛZ⁻¹ * g.inner y.val v v ≤ (sourceMetric Φ hsrc htgt stage t).inner y v v) ∧
            (∀ q : ℕ, ∃ Cq : ℝ, ∀ stage t, t ∈ Icc 0 τ → ∀ x ∈ bf.grow stage,
              metricCovDerivNorm q (gSeqExt Φ g bf hsrc htgt stage t) g x ≤ Cq) ∧
            co.gInf 0 = g ∧
            (∀ t ∈ Icc 0 τ, RiemannianMetricComplete (co.gInf t)) ∧
            (∀ (r : ℕ) (x₀ : E3) (i j : Fin (Module.finrank ℝ E3)),
              ContinuousOn
                (fun p : ℝ × E3 => iteratedFDeriv ℝ r (chartGramOnE (co.gInf p.1) x₀ i j) p.2)
                (Icc 0 τ ×ˢ interior (extChartAt (𝓡 3) x₀).target)) ∧
            (∀ (x₀ : E3) (i j : Fin (Module.finrank ℝ E3)),
              ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) 𝓘(ℝ, ℝ) ∞
                (fun p : ℝ × E3 => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (co.gInf p.1) x₀ p.2 i j)
                (Icc 0 τ ×ˢ (trivializationAt E3 (TangentSpace (𝓡 3)) x₀).baseSet)) ∧
            (∀ t ∈ Ioo 0 τ, ∀ (x : E3) (v w : TangentSpace (𝓡 3) x),
              HasDerivAt (fun r => (co.gInf r).inner x v w)
                (-2 * ricciTensor (co.gInf t) x v w) t) ∧
            (∀ K : Set E3, IsCompact K → ∀ p : ℕ, ∃ Lp : ℝ, 0 ≤ Lp ∧
              ∀ s ∈ Icc 0 τ, ∀ t ∈ Icc 0 τ, ∀ a : ℕ, a ≤ p → ∀ x ∈ K,
                metricDerivNorm a (co.gInf s) (co.gInf t) g x ≤ Lp * |s - t|) ∧
            ∀ t ∈ Icc 0 τ, ∀ x : E3,
              Real.sqrt (normSq0S (co.gInf t) x 4 (metricRm04 (co.gInf t) x)) ≤ 567 * B 0 := by
  obtain ⟨AC, _hAC, hcurv⟩ :=
    exists_uniform_compact_truncation_curvature_bounds ell hell C hC
  obtain ⟨τ, hτ, B, hB, hflow⟩ :=
    exists_uniform_compact_flows_of_curvature_derivative_bounds (I := 𝓡 3) (M := S3) (by simp) AC
  obtain ⟨ΛZ, hΛZ, CZ, LZ, hCZ, hLZ, henrich⟩ :=
    exists_uniform_metric_time_bounds_of_spatial_curvature_bounds
      (I := 𝓡 3) (M := S3) (by simp) τ hτ B hB
  refine ⟨τ, hτ, B, hB, ΛZ, hΛZ, CZ, LZ, hCZ, hLZ, ?_⟩
  intro g hlower hjets north
  have hcomplete : RiemannianMetricComplete g :=
    RiemannianMetricComplete.of_lower DifferentialGeometry.PDE.RicciFlow.StandardCap.metric_complete hell hlower
  choose Z hZ hz hcomp hg hp hm using fun j : ℕ =>
    hflow (compactDoubleTruncationMetric north (compactCapApproximationRadius (j + 2))
      (compactCapApproximationRadius_large (j + 2)) g)
      (hcurv g hlower hjets north (compactCapApproximationRadius (j + 2))
        (compactCapApproximationRadius_large (j + 2)) (compactCapCoreApproximationRadius_large j))
  have henrichZ (j : ℕ) := henrich (Z j) (hZ j) (hg j) (hp j)
    (fun k t ht x => hm j k k 0 (by omega) t ht x)
  have heZ := fun j => (henrichZ j).1
  have hcZ := fun j => (henrichZ j).2.1
  have hlZ := fun j => (henrichZ j).2.2
  refine ⟨Z, hZ, ?_, ?_⟩
  · intro stage
    refine ⟨hz stage, hcomp stage, hg stage, hp stage, hm stage, ?_, ?_,
      heZ stage, hcZ stage, hlZ stage⟩
    · intro x hx v w
      rw [hz stage]
      exact compactDoubleTruncationMetric_cap_pullback north
        (compactCapApproximationRadius (stage + 2))
        (compactCapApproximationRadius_large (stage + 2)) g x hx v w
    · intro x hx v w
      rw [hz stage]
      exact compactDoubleTruncationMetric_cap_pullback_core north
        (compactCapApproximationRadius (stage + 2))
        (compactCapApproximationRadius_large (stage + 2)) g x hx v w
  · let Φ := compactCorePointedMaps g north Z hZ
    let hsrc := compactCorePointedMaps_sourceSigma g north Z hZ
    let htgt := compactCorePointedMaps_targetSigma g north Z hZ
    have hi := compactCorePointedMaps_initial g north Z hZ hz
    obtain ⟨hesrc, hbounds⟩ :=
      compactCorePointedMaps_reference_bounds g north Z hZ hz τ ΛZ CZ LZ hCZ hLZ heZ hcZ hlZ
    obtain ⟨bf, co, hbound, hcovTail, hinit, hc, hjlim, hglim, hplim, hllim⟩ :=
      exists_complete_closed_reference_limit Φ τ hτ subset_rfl subset_rfl
        hcomplete.complete hsrc htgt ΛZ hΛZ hi hesrc hbounds
    refine ⟨bf, co, hbound, hcovTail, hinit, hc, hjlim, hglim, hplim, hllim, ?_⟩
    have hRicSeq := fun j => ricci_bound_of_mixed_zero τ hτ (Z j) (B 0)
      (hm j 0 0 0 (by norm_num))
    intro t ht x
    have hlow : 0 < ΛZ⁻¹ := inv_pos.mpr (zero_lt_one.trans_le hΛZ)
    have hconv := co.ricNorm_convergence_at Φ g bf hsrc htgt 0 τ ΛZ⁻¹ hlow hbound hcovTail ht x
    have hRic : normSq0S (co.gInf t) x 2 (metricRicci (co.gInf t) x) ≤ 81 * (B 0) ^ 2 := by
      apply le_of_tendsto hconv
      exact Filter.Eventually.of_forall (fun j => hRicSeq (co.φ j) t ht _)
    have hsqrt : Real.sqrt (normSq0S (co.gInf t) x 2 (metricRicci (co.gInf t) x)) ≤ 9 * B 0 := by
      apply Real.sqrt_le_iff.mpr
      exact ⟨mul_nonneg (by norm_num) (hB 0), by nlinarith only [hRic]⟩
    have hthree := sqrt_normSq_metricRm04_le_ricci_three (co.gInf t) x
      (by change Module.finrank ℝ E3 = 3; exact finrank_euclideanSpace_fin)
    nlinarith only [hsqrt, hthree]
end DifferentialGeometry.PDE.RicciFlow
