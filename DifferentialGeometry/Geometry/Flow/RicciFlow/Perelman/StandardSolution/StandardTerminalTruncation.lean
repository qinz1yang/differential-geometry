import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.MetricTruncationNorm
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardTerminalRegularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.ReferenceCurvatureBounds
import DifferentialGeometry.Geometry.Curvature.DerivativeIsometry
import DifferentialGeometry.Geometry.Metric.Coordinates.ChartGram

set_option autoImplicit false
noncomputable section
open Set Bundle Manifold TopologicalSpace DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Integral.Measure DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.StandardCap DifferentialGeometry.Geometry.Riemannian
open scoped Manifold ContDiff Topology ENNReal BigOperators
namespace DifferentialGeometry.PDE.RicciFlow
private abbrev E3 := EuclideanSpace ℝ (Fin 3)
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

theorem standard_uniform_terminal_truncation_jets :
    ∃ α : ℝ, 0 < α ∧ ∃ Λ : ℝ, 1 ≤ Λ ∧ ∃ C L D A : ℕ → ℝ,
      (∀ N, 0 ≤ C N) ∧ (∀ N, 0 ≤ L N) ∧ (∀ N, 0 ≤ D N) ∧ (∀ N, 0 < A N) ∧
      ∃ ell : ℝ, 0 < ell ∧
      ∀ S : PartialStandardSolution, ∀ T : ℝ, 0 < T → T ≤ α →
        ENNReal.ofReal T ≤ S.lifetime →
        ∃ G : ℝ → SmoothRiemannianMetric (𝓡 3) E3,
          (∀ t ∈ Ico 0 T, G t = S.metric t) ∧
          G 0 = DifferentialGeometry.PDE.RicciFlow.StandardCap.metric ∧
          (∀ t ∈ Icc 0 T, RiemannianMetricComplete (G t)) ∧
          (∀ t ∈ Icc 0 T, MetricUniformEquivalentOn univ DifferentialGeometry.PDE.RicciFlow.StandardCap.metric (G t) Λ) ∧
          (∀ N : ℕ, ∀ t ∈ Icc 0 T, ∀ x : E3,
            metricCovDerivNorm N (G t) DifferentialGeometry.PDE.RicciFlow.StandardCap.metric x ≤ C N) ∧
          (∀ N : ℕ, ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T, ∀ x : E3,
            metricDerivNorm N (G s) (G t) DifferentialGeometry.PDE.RicciFlow.StandardCap.metric x ≤ L N * |s - t|) ∧
          (∀ (r : ℕ) (x₀ : E3) (i j : Fin (Module.finrank ℝ E3)),
            ContinuousOn
              (fun p : ℝ × E3 => iteratedFDeriv ℝ r (chartGramOnE (G p.1) x₀ i j) p.2)
              (Icc 0 T ×ˢ interior (extChartAt (𝓡 3) x₀).target)) ∧
          (∀ t ∈ Ico 0 T, ∀ (x : E3) (v w : TangentSpace (𝓡 3) x),
            HasDerivWithinAt (fun s => (G s).inner x v w)
              (-2 * ricciTensor (G t) x v w) (Ici 0) t) ∧
          (∀ (x₀ : E3) (i j : Fin (Module.finrank ℝ E3)),
            ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) 𝓘(ℝ, ℝ) ∞
              (fun p : ℝ × E3 => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (G p.1) x₀ p.2 i j)
              (Icc 0 T ×ˢ (trivializationAt E3 (TangentSpace (𝓡 3)) x₀).baseSet)) ∧
          (∀ t ∈ Icc 0 T, ∀ (x : E3) (v w : TangentSpace (𝓡 3) x),
            HasDerivWithinAt (fun s => (G s).inner x v w)
              (-2 * ricciTensor (G t) x v w) (Icc 0 T) t) ∧
          (∀ (R : ℝ) (hR : 2 < R),
            RiemannianMetricComplete (metricTruncation (G T) R hR) ∧
            (∀ (x : E3) (v : TangentSpace (𝓡 3) x),
              ell * DifferentialGeometry.PDE.RicciFlow.StandardCap.metric.inner x v v ≤
                (metricTruncation (G T) R hR).inner x v v) ∧
            (∀ (x : E3), ‖x‖ ≤ R - 2 → ∀ (v w : TangentSpace (𝓡 3) x),
              (metricTruncation (G T) R hR).inner x v w = (G T).inner x v w) ∧
            (∀ (x : E3), R - 1 ≤ ‖x‖ → ∀ (v w : TangentSpace (𝓡 3) x),
              (metricTruncation (G T) R hR).inner x v w =
                DifferentialGeometry.PDE.RicciFlow.StandardCap.metric.inner x v w)) ∧
          ∀ (R : ℝ) (hR : 2 < R), transitionEnd + 4 ≤ R →
            (∀ N j : ℕ, j ≤ N → ∀ x : E3,
              metricDerivNorm j (metricTruncation (G T) R hR)
                DifferentialGeometry.PDE.RicciFlow.StandardCap.metric DifferentialGeometry.PDE.RicciFlow.StandardCap.metric x ≤ D N) ∧
            (∀ k : ℕ, ∀ x : E3,
              Real.sqrt (normSq0S (metricTruncation (G T) R hR) x (4 + k)
                (iterCov (metricTruncation (G T) R hR) 4
                  (metricRm04 (metricTruncation (G T) R hR)) k x)) ≤ A k) := by
  obtain ⟨α, hα, Λ, hΛ, C, L, hC, hL, hs⟩ := standard_uniform_smooth_terminal_families
  choose κ hκ hκbound using exists_uniform_metricTruncation_derivative_bound
  let Q : ℕ → ℝ := fun N => ∑ j ∈ Finset.range (N + 1), L j * α
  have hQ (N : ℕ) : 0 ≤ Q N := Finset.sum_nonneg (fun j _ => mul_nonneg (hL j) hα.le)
  let D : ℕ → ℝ := fun N => κ N * Q N
  have hD (N : ℕ) : 0 ≤ D N := mul_nonneg (hκ N).le (hQ N)
  let ell : ℝ := min Λ⁻¹ 1
  have hell : 0 < ell := lt_min (inv_pos.mpr (zero_lt_one.trans_le hΛ)) zero_lt_one
  choose A hA hAbound using fun k =>
    exists_pos_bound_intrinsic_curvature_derivative_of_metric_jets_on_opens
      k ell (D (k + 2)) hell (hD (k + 2))
  refine ⟨α, hα, Λ, hΛ, C, L, D, A, hC, hL, hD, hA, ell, hell, ?_⟩
  intro S T hT hTα hTS
  obtain ⟨G, hEq, hzero, hc, he, hCov, hLip, hj, hpde, hgram, hclosed⟩ := hs S T hT hTα hTS
  have hlower (x : E3) (v : TangentSpace (𝓡 3) x) :
      Λ⁻¹ * DifferentialGeometry.PDE.RicciFlow.StandardCap.metric.inner x v v ≤ (G T).inner x v v :=
    ((he T ⟨hT.le, le_rfl⟩).2 x (mem_univ x) v).1
  have htruncLower (R : ℝ) (hR : 2 < R) (x : E3) (v : TangentSpace (𝓡 3) x) :
      ell * DifferentialGeometry.PDE.RicciFlow.StandardCap.metric.inner x v v ≤
        (metricTruncation (G T) R hR).inner x v v :=
    metricTruncation_lower (G T) R hR Λ⁻¹ hlower x v
  have hinput (N j : ℕ) (hjN : j ≤ N) (x : E3) :
      metricDerivNorm j (G T) DifferentialGeometry.PDE.RicciFlow.StandardCap.metric
        DifferentialGeometry.PDE.RicciFlow.StandardCap.metric x ≤ Q N := by
    have hh := hLip j T ⟨hT.le, le_rfl⟩ 0 ⟨le_rfl, hT.le⟩ x
    rw [hzero, sub_zero, abs_of_nonneg hT.le] at hh
    exact hh.trans ((mul_le_mul_of_nonneg_left hTα (hL j)).trans
      (Finset.single_le_sum (s := Finset.range (N + 1)) (a := j) (f := fun i => L i * α)
        (fun i _ => mul_nonneg (hL i) hα.le) (Finset.mem_range.mpr (by omega))))
  refine ⟨G, hEq, hzero, hc, he, hCov, hLip, hj, hpde, hgram, hclosed, ?_, ?_⟩
  · intro R hR
    exact ⟨metricTruncation_complete (G T) R hR Λ⁻¹
        (inv_pos.mpr (zero_lt_one.trans_le hΛ)) hlower,
      htruncLower R hR,
      fun _ hx v w => metricTruncation_inner_core (G T) R hR hx v w,
      fun _ hx v w => metricTruncation_inner_end (G T) R hR hx v w⟩
  · intro R hR hlarge
    have hb (N j : ℕ) (hjN : j ≤ N) (x : E3) :
        metricDerivNorm j (metricTruncation (G T) R hR)
          DifferentialGeometry.PDE.RicciFlow.StandardCap.metric DifferentialGeometry.PDE.RicciFlow.StandardCap.metric x ≤ D N :=
      hκbound N (G T) R hR hlarge (Q N) (hQ N) (hinput N) j hjN x
    refine ⟨hb, ?_⟩
    intro k x
    exact intrinsic_bound_on_ambient k ell (D (k + 2)) (A k) (hAbound k)
      (metricTruncation (G T) R hR) (htruncLower R hR) (hb (k + 2)) x
end DifferentialGeometry.PDE.RicciFlow
