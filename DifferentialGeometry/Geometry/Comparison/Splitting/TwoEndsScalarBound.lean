import DifferentialGeometry.Geometry.Comparison.Splitting.TwoEndsMetricLine
import DifferentialGeometry.Geometry.Comparison.Busemann.Ray.BusemannSmooth
import DifferentialGeometry.Geometry.Comparison.Splitting.AffineFlowIsometry
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Pullback
import DifferentialGeometry.Topology.Ends.ProductLineEnds

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped Topology NNReal ContDiff Manifold
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.HopfRinow

namespace DifferentialGeometry.Geometry.Topology

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]

theorem exists_metricScalarAt_le_of_nonnegative_ricci_of_two_ends
    (g : SmoothRiemannianMetric I M)
    (hcomplete : RiemannianMetricComplete (I := I) g)
    (hRic : ∀ y : M, ∀ w : TangentSpace I y, 0 ≤ ricciTensor (I := I) g y w w)
    (hends : HasAtLeastEnds M 2) :
    ∃ C : ℝ, ∀ x : M, metricScalarAt (I := I) g x ≤ C := by
  classical
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  by_cases hz : Module.finrank ℝ E = 0
  · let : Subsingleton E := Module.finrank_zero_iff.mp hz
    let : Subsingleton H := I.injective.subsingleton
    let : DiscreteTopology H := inferInstance
    let : DiscreteTopology M := ChartedSpace.discreteTopology H M
    let : Subsingleton M := subsingleton_of_preconnected_totallyDisconnected
    exact (not_hasAtLeastEnds_of_compact (X := M) (by decide : 0 < 2) hends).elim
  · let : NeZero (Module.finrank ℝ E) := ⟨hz⟩
    let : IsManifold I 1 M := IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)
    let : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
    let : T3Space M := inferInstance
    let : RiemannianBundle (fun x : M => TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    let : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
    let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
    let : CompleteSpace M := hcomplete.complete
    have hEnorm : IsMetricNorm (I := I) (M := M) g := fun x v =>
      tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := I) g x v
    let : MetricSpace M := riemMetricSpace (I := I) (M := M)
    let : ProperSpace M := properSpace_riemMetric (I := I) hcomplete.complete g hEnorm
    obtain ⟨gamma, hgamma⟩ := exists_riemannian_metric_line_of_two_ends g hcomplete hends
    have hiso : Isometry gamma := by
      apply Isometry.of_dist_eq
      intro s t
      rw [riemMetric_dist_eq (I := I),
        ← riemannianEDistOf_eq_riemannianEDist (I := I) g hEnorm, hgamma,
        ENNReal.toReal_ofReal (abs_nonneg _), Real.dist_eq]
    let b := busemann (fun t : ℝ≥0 => gamma t)
    have hb : ContMDiff I 𝓘(ℝ, ℝ) ∞ b := busemann_contMDiff g hEnorm hRic hiso
    have hunit (p : M) :
        g.inner p (gradientFun (I := I) g b p) (gradientFun (I := I) g b p) = 1 :=
      (opposite_busemann_gradient_unit g hEnorm hRic hiso p).1
    have hH (p : M) : hessFun (I := I) g b p = 0 :=
      busemann_hessian_eq_zero g hEnorm hRic hiso p
    let N := {p : M // b p = 0}
    let : ConnectedSpace N := affineFunctionZeroLevel_connectedSpace g hEnorm hb hunit hH
    let e : (N × ℝ) ≃ₜ M := affineFunctionZeroLevelHomeomorph g hEnorm hb hunit hH
    by_cases hcompact : CompactSpace N
    · let : CompactSpace N := hcompact
      have hscalarInv (p : M) (t : ℝ) :
          metricScalarAt (I := I) g p =
            metricScalarAt (I := I) g (affineGradientFlow (I := I) g hEnorm b p t) := by
        let Φ := affineGradientFlowDiffeomorph (I := I) g hEnorm hb hunit hH t
        have hmetric : Diffeomorph.pullbackMetric (I := I) g Φ = g := by
          apply SmoothRiemannianMetric.ext_inner
          intro q v w
          rw [Diffeomorph.pullbackMetric_inner]
          exact affineGradientFlow_preserves_metric (I := I) g hEnorm hb hunit hH q v w t
        have hs := DifferentialGeometry.CheegerGromovCompactness.metricScalarAt_pullback
          (I := I) g Φ p
        rw [hmetric] at hs
        exact hs
      let f : N → ℝ := fun p => metricScalarAt (I := I) g p.1
      have hf : Continuous f :=
        (metricScalar_smooth (I := I) (M := M) g).continuous.comp continuous_subtype_val
      obtain ⟨A, hA⟩ := isCompact_univ.exists_bound_of_continuousOn hf.continuousOn
      refine ⟨A, ?_⟩
      intro x
      let p : N := ⟨affineGradientFlow (I := I) g hEnorm b x (-b x), by
        rw [affineFunction_flow_eq_add (I := I) g hEnorm hb hunit hH, add_neg_cancel]⟩
      have hscalar : metricScalarAt (I := I) g x = metricScalarAt (I := I) g p.1 :=
        hscalarInv x (-b x)
      calc
        metricScalarAt (I := I) g x = metricScalarAt (I := I) g p.1 := hscalar
        _ ≤ |metricScalarAt (I := I) g p.1| := le_abs_self _
        _ ≤ A := by
          simpa only [f, Real.norm_eq_abs] using hA p (mem_univ p)
    · have hone := hasExactlyEnds_prod_real_of_noncompact hcompact
      exact (hone.2 ((hasAtLeastEnds_homeomorph_iff e 2).mpr hends)).elim

end DifferentialGeometry.Geometry.Topology

end
