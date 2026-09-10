import DifferentialGeometry.Geometry.Comparison.Splitting.TwoEndsMetricLine
import DifferentialGeometry.Geometry.Comparison.Busemann.Ray.BusemannSmooth
import DifferentialGeometry.Geometry.Comparison.Splitting.AffineFlowRegularity
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

theorem hasAtMostTwoEnds_of_nonnegative_ricci (g : SmoothRiemannianMetric I M)
    (hcomplete : RiemannianMetricComplete (I := I) g)
    (hRic : ∀ y : M, ∀ w : TangentSpace I y, 0 ≤ ricciTensor (I := I) g y w w) :
    HasAtMostTwoEnds M := by
  classical
  by_cases hends : HasAtLeastEnds M 2
  · by_cases hz : Module.finrank ℝ E = 0
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
        exact (hasAtMostTwoEnds_homeomorph_iff e).mp
          (hasAtMostTwoEnds_prod_real_of_compact (X := N))
      · have hone := hasExactlyEnds_prod_real_of_noncompact hcompact
        exact (hone.2 ((hasAtLeastEnds_homeomorph_iff e 2).mpr hends)).elim
  · exact hasAtMostTwoEnds_of_not_hasAtLeastEnds_two hends

theorem hasExactlyTwoEnds_of_nonnegative_ricci (g : SmoothRiemannianMetric I M)
    (hcomplete : RiemannianMetricComplete (I := I) g)
    (hRic : ∀ y : M, ∀ w : TangentSpace I y, 0 ≤ ricciTensor (I := I) g y w w)
    (hends : HasAtLeastEnds M 2) : HasExactlyEnds M 2 :=
  ⟨hends, hasAtMostTwoEnds_of_nonnegative_ricci g hcomplete hRic⟩

end DifferentialGeometry.Geometry.Topology

end
