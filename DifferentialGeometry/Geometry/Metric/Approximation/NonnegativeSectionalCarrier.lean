import DifferentialGeometry.Geometry.Metric.Approximation.NonnegativeSectional
import DifferentialGeometry.Geometry.Metric.Pullback.FiniteRegularity
import DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.Sectional
import DifferentialGeometry.Topology.Manifold.InteriorAtlas
import DifferentialGeometry.Topology.ThreeManifold.Geometrization.Carrier

/-!
# LFR50 on manifolds whose model has corners but whose boundary is empty

A manifold `M` modelled on `I` (possibly with corners) with `BoundarylessManifold I M` carries the
identity rechart `interiorChartedSpace I ∞` to the boundaryless model `𝓘(ℝ, E)`
(`Topology/Manifold/InteriorAtlas.lean`). This file

* pulls a `C^n` metric `g` (`2 ≤ n`) back along the smooth identity diffeomorphism
  `(interiorAtlasDiffeomorph I ∞).symm` with the (now proved) finite-regularity pullback
  `finitePullbackMetric` (`Geometry/Metric/Pullback/FiniteRegularityProof.lean`);
* transports the finite-order sectional curvature
  (`sectionalCurvature_finitePullback_interiorAtlas`). `sectionalCurvature_eq_of_pullback`
  (`FiniteMetric.lean:401`) needs both models boundaryless, so the identity is proved directly:
  the extended charts of the two structures are the same maps, and the chart coefficients agree
  on the open interior of the chart target;
* runs LFR50 on the rechart and returns the smooth metric by `pullbackMetricCross` along
  `interiorAtlasDiffeomorph` (`exists_smooth_sectional_nonneg_of_finite_metric_of_boundarylessManifold`);
* states the carrier form `CompactCarrier.exists_smooth_sectional_nonneg_of_metric2_of_boundary_eq_empty`
  with `hclosed : W.model.boundary W.Carrier = ∅` (design §1), and a consumer.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter
open DifferentialGeometry DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.MetricSmoothing

open DifferentialGeometry.Analysis (coefficientSectional coefficientRm04 coefficientGram
  jet2_congr_of_eventuallyEq)

section Germ

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- The coefficient sectional curvature only depends on the germ of the coefficient field. -/
theorem coefficientSectional_congr_of_eventuallyEq {b c : E → E →L[ℝ] E →L[ℝ] ℝ} {y : E}
    (h : b =ᶠ[𝓝 y] c) (v w : E) :
    coefficientSectional b y v w = coefficientSectional c y v w := by
  have hG : coefficientGram b =ᶠ[𝓝 y] coefficientGram c :=
    h.mono fun z hz => by simp only [coefficientGram, hz]
  unfold coefficientSectional coefficientRm04
  rw [jet2_congr_of_eventuallyEq hG, h.eq_of_nhds]

end Germ

section Rechart

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M]

/-- **Finite curvature across the identity rechart.** If `g'` on the interior rechart is the
pullback of `g` along the identity, its finite-order sectional curvature is that of `g`. -/
theorem sectionalCurvature_finitePullback_interiorAtlas {n m : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) :
    letI := interiorChartedSpace I ∞ (M := M)
    letI := interiorIsManifold I ∞ (M := M)
    ∀ (g' : ContMDiffRiemannianMetric 𝓘(ℝ, E) m E (TangentSpace 𝓘(ℝ, E) : M → Type _)),
      (∀ (x : M) (v w : TangentSpace 𝓘(ℝ, E) x), g'.inner x v w =
        g.inner ((interiorAtlasDiffeomorph I ∞).symm x)
          (mfderiv 𝓘(ℝ, E) I (interiorAtlasDiffeomorph I ∞).symm x v)
          (mfderiv 𝓘(ℝ, E) I (interiorAtlasDiffeomorph I ∞).symm x w)) →
      ∀ (p : M) (v w : TangentSpace 𝓘(ℝ, E) p), g'.sectionalCurvature p v w =
        g.sectionalCurvature p (mfderiv 𝓘(ℝ, E) I (interiorAtlasDiffeomorph I ∞).symm p v)
          (mfderiv 𝓘(ℝ, E) I (interiorAtlasDiffeomorph I ∞).symm p w) := by
  let := interiorChartedSpace I ∞ (M := M)
  let := interiorIsManifold I ∞ (M := M)
  intro g' hg' p v w
  let Ψ := (interiorAtlasDiffeomorph I ∞ (M := M)).symm
  have hΨ : ∀ x : M, MDifferentiableAt 𝓘(ℝ, E) I Ψ x := fun x =>
    (Ψ.contMDiff.mdifferentiable (by simp)) x
  -- the target of the interior chart is an open neighbourhood of the base point
  have hO : (extChartAt 𝓘(ℝ, E) p).target ∈ 𝓝 (extChartAt 𝓘(ℝ, E) p p) :=
    (isOpen_extChartAt_target p).mem_nhds ((extChartAt 𝓘(ℝ, E) p).map_source
      (mem_extChartAt_source p))
  have hpt : ∀ y ∈ (extChartAt 𝓘(ℝ, E) p).target, ∀ a : E,
      mfderiv 𝓘(ℝ, E) I Ψ ((extChartAt 𝓘(ℝ, E) p).symm y)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) p).symm y a) =
      mfderiv 𝓘(ℝ, E) I (extChartAt I p).symm y a := by
    intro y hy a
    have hs := mdifferentiableAt_extChartAt_symm_of_mem (I := 𝓘(ℝ, E)) p hy
    have hc := mfderiv_comp y (hΨ ((extChartAt 𝓘(ℝ, E) p).symm y)) hs
    exact (congrArg (fun L => L a) hc).symm
  have hvec : ∀ u : TangentSpace 𝓘(ℝ, E) p,
      mfderiv I 𝓘(ℝ, E) (extChartAt I p) p (mfderiv 𝓘(ℝ, E) I Ψ p u) =
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) p) p u := by
    intro u
    have he : MDifferentiableAt I 𝓘(ℝ, E) (extChartAt I p) (Ψ p) :=
      mdifferentiableAt_extChartAt (mem_chart_source H p)
    have hc := mfderiv_comp p he (hΨ p)
    exact (congrArg (fun L => L u) hc).symm
  change coefficientSectional _ (extChartAt 𝓘(ℝ, E) p p)
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) p) p v)
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) p) p w) =
    coefficientSectional _ (extChartAt I p p)
      (mfderiv I 𝓘(ℝ, E) (extChartAt I p) p (mfderiv 𝓘(ℝ, E) I Ψ p v))
      (mfderiv I 𝓘(ℝ, E) (extChartAt I p) p (mfderiv 𝓘(ℝ, E) I Ψ p w))
  rw [hvec v, hvec w]
  apply coefficientSectional_congr_of_eventuallyEq
  filter_upwards [hO] with y hy
  ext a b
  change g'.inner ((extChartAt 𝓘(ℝ, E) p).symm y)
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) p).symm y a)
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) p).symm y b) =
    g.inner ((extChartAt I p).symm y) (mfderiv 𝓘(ℝ, E) I (extChartAt I p).symm y a)
      (mfderiv 𝓘(ℝ, E) I (extChartAt I p).symm y b)
  rw [hg', hpt y hy a, hpt y hy b]
  rfl

end Rechart

section Main

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [CompactSpace M] [BoundarylessManifold I M]

/-- **LFR50 for a model with corners and empty boundary.** On a compact connected `3`-manifold
`M` modelled on `I` (possibly with corners) whose boundary is empty, a `C^n` metric, `2 ≤ n`, with
nonnegative finite-order sectional curvature yields a smooth metric with `sec ≥ 0` on `M`.
The metric is pulled back to the identity rechart `interiorChartedSpace I ∞` (finite-regularity
pullback along a smooth diffeomorphism), LFR50 runs there, and the smooth result returns along
`interiorAtlasDiffeomorph`. -/
theorem exists_smooth_sectional_nonneg_of_finite_metric_of_boundarylessManifold
    [ConnectedSpace M] (hdim : Module.finrank ℝ E = 3) {n : ℕ∞ω} (hn : (2 : ℕ∞ω) ≤ n)
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _))
    (hsec : ∀ x (v w : TangentSpace I x), 0 ≤ g.sectionalCurvature x v w) :
    ∃ h : SmoothRiemannianMetric I M, SectionalBoundedBelow h 0 := by
  let := interiorChartedSpace I ∞ (M := M)
  let := interiorIsManifold I ∞ (M := M)
  let Ψ := (interiorAtlasDiffeomorph I ∞ (M := M)).symm
  let g' := DifferentialGeometry.Geometry.finitePullbackMetric (m := (2 : ℕ∞ω)) g Ψ hn
    (by simp)
  have hsec' : ∀ x (v w : TangentSpace 𝓘(ℝ, E) x), 0 ≤ g'.sectionalCurvature x v w := by
    intro x v w
    rw [sectionalCurvature_finitePullback_interiorAtlas g g'
      (fun y a b => DifferentialGeometry.Geometry.finitePullbackMetric_inner g Ψ hn _ y a b)
      x v w]
    exact hsec _ _ _
  obtain ⟨h', hh'⟩ := exists_smooth_sectional_nonneg_of_finite_metric (I := 𝓘(ℝ, E)) (M := M)
    hdim le_rfl g' hsec'
  exact exists_sectionalBoundedBelow_of_diffeomorph (interiorAtlasDiffeomorph I ∞ (M := M)) h' hh'

end Main

end DifferentialGeometry.Geometry.MetricSmoothing

namespace GC.Endpoint

open DifferentialGeometry.Geometry.MetricSmoothing

universe v

/-- **LFR50, carrier form (design §1).** On a compact connected carrier with empty boundary
(either model kind), a `C^n` metric, `2 ≤ n`, with nonnegative finite-order sectional curvature
yields a smooth metric with `sec ≥ 0` on the same carrier. No `Boundaryless` instance on the
carrier model is assumed. -/
theorem CompactCarrier.exists_smooth_sectional_nonneg_of_finite_metric_of_boundary_eq_empty
    (W : CompactCarrier.{v}) [ConnectedSpace W.Carrier]
    (hclosed : W.model.boundary W.Carrier = ∅) {n : ℕ∞ω} (hn : (2 : ℕ∞ω) ≤ n)
    (g : Bundle.ContMDiffRiemannianMetric W.model n (EuclideanSpace ℝ (Fin 3))
      (TangentSpace W.model : W.Carrier → Type _))
    (hsec : ∀ x (v w : TangentSpace W.model x), 0 ≤ g.sectionalCurvature x v w) :
    ∃ h : SmoothRiemannianMetric W.model W.Carrier, SectionalBoundedBelow h 0 := by
  let := ModelWithCorners.Boundaryless.of_boundary_eq_empty hclosed
  exact exists_smooth_sectional_nonneg_of_finite_metric_of_boundarylessManifold
    finrank_euclideanSpace_fin hn g hsec

/-- **Consumer (the design's `Metric2` carrier endpoint).** The `C²` case with
`hclosed : W.model.boundary W.Carrier = ∅`. -/
theorem CompactCarrier.exists_smooth_sectional_nonneg_of_metric2_of_boundary_eq_empty
    (W : CompactCarrier.{v}) [ConnectedSpace W.Carrier]
    (hclosed : W.model.boundary W.Carrier = ∅)
    (g : Bundle.ContMDiffRiemannianMetric W.model (2 : ℕ∞ω) (EuclideanSpace ℝ (Fin 3))
      (TangentSpace W.model : W.Carrier → Type _))
    (hsec : ∀ x (v w : TangentSpace W.model x), 0 ≤ g.sectionalCurvature x v w) :
    ∃ h : SmoothRiemannianMetric W.model W.Carrier, SectionalBoundedBelow h 0 :=
  W.exists_smooth_sectional_nonneg_of_finite_metric_of_boundary_eq_empty hclosed le_rfl g hsec

/-- **Consumer (interior points).** The same conclusion when every point of the carrier is an
interior point of its model. -/
theorem CompactCarrier.exists_smooth_sectional_nonneg_of_metric2_of_forall_isInteriorPoint
    (W : CompactCarrier.{v}) [ConnectedSpace W.Carrier]
    (hint : ∀ x : W.Carrier, W.model.IsInteriorPoint x)
    (g : Bundle.ContMDiffRiemannianMetric W.model (2 : ℕ∞ω) (EuclideanSpace ℝ (Fin 3))
      (TangentSpace W.model : W.Carrier → Type _))
    (hsec : ∀ x (v w : TangentSpace W.model x), 0 ≤ g.sectionalCurvature x v w) :
    ∃ h : SmoothRiemannianMetric W.model W.Carrier, SectionalBoundedBelow h 0 := by
  refine W.exists_smooth_sectional_nonneg_of_metric2_of_boundary_eq_empty ?_ g hsec
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  exact fun hx => (W.model.isInteriorPoint_iff_not_isBoundaryPoint x).mp (hint x) hx

end GC.Endpoint
