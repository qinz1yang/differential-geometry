import DifferentialGeometry.Geometry.Metric.Approximation.NonnegativeSectional
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.SurfaceCommonExistence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Preservation.SurfaceFlatOrPositiveApplications

/-!
# SF1: a `C²` metric with `K ≥ 0` on a closed surface yields a smooth one (2D LFR50)

`exists_smooth_curvature_nonneg_of_finite_metric_dim_two` (row SF1 of package SURF,
`design-finite-surface-foundations-20261004.md` §C2 step 1, §D2): on a compact connected
boundaryless surface, a `C^n` metric (`n ≥ 2`) whose finite-order sectional curvature is
nonnegative yields a SMOOTH metric with `K ≥ 0` on the same surface.

The proof is the LFR50 composite (`exists_smooth_sectional_nonneg_of_finite_metric`) with its only
three-dimensional step, parts B + C, replaced by the surface version
`exists_common_flows_sectional_lower_bound_of_finrank_eq_two`: part A (smooth approximants with
one `|Rm|` bound, `sec ≥ -εₖ → 0`, one bilipschitz reference), parts B + C on surfaces (common
Ricci flows keeping `sec ≥ -εₖ`), part D (positive-time slices satisfy the canonical compactness
hypotheses), parts E + F (limit on the same surface, `sec ≥ 0`).

Consumers: the smooth case, the round two-sphere regarded as a `C²` metric, and SF1 followed by
SF2 (`flat_or_exists_scalar_pos_of_sectional_nonneg_dim_two`): a `C²` metric with `K ≥ 0` on a
closed connected surface gives a smooth flat metric or a smooth metric with `R > 0`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure DifferentialGeometry.PDE.RicciFlow
open scoped Manifold ContDiff ENNReal Topology

namespace DifferentialGeometry.Geometry.MetricSmoothing

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [CompactSpace M] [BoundarylessManifold I M]

/-- **SF1 (2D LFR50).** On a compact connected boundaryless surface, a `C^n` Riemannian metric,
`2 ≤ n`, with nonnegative finite-order sectional curvature yields a smooth Riemannian metric with
nonnegative sectional curvature on the same surface. -/
theorem exists_smooth_curvature_nonneg_of_finite_metric_dim_two [ConnectedSpace M]
    (hdim : Module.finrank ℝ E = 2) {n : ℕ∞ω} (hn : (2 : ℕ∞ω) ≤ n)
    (g : Bundle.ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _))
    (hsec : ∀ x (v w : TangentSpace I x), 0 ≤ g.sectionalCurvature x v w) :
    ∃ h : SmoothRiemannianMetric I M, SectionalBoundedBelow h 0 := by
  have : NeZero (Module.finrank ℝ E) := ⟨by omega⟩
  obtain ⟨gSeq, B, ε, gRef, Λ, hRm, -, hεlim, hsecε, hΛ, hbil, -⟩ :=
    exists_smooth_approximants_of_sectional_nonneg g hn hsec
  obtain ⟨d₀, v₀, hv₀, huni⟩ := exists_uniform_diam_volume_of_bilipschitz (I := I) gRef hΛ
  have hdiam : ∀ k (x y : M), riemannianEDistOf (gSeq k) x y ≤ ENNReal.ofReal d₀ :=
    fun k => (huni (gSeq k) (hbil k)).1
  have p : M := Classical.arbitrary M
  obtain ⟨T, hT, hflow⟩ :=
    exists_common_flows_sectional_lower_bound_of_finrank_eq_two (I := I) hdim B gSeq ε hRm hsecε
  choose τ hτ F hF using hflow
  set Bs : ℝ := Real.sqrt (2 * B ^ 2 + 1) with hBs
  have hBpos : 0 < Bs := Real.sqrt_pos.mpr (by positivity)
  have hcurv : ∀ k t, t ∈ Icc 0 T → ∀ x : M,
      Real.sqrt (Tensor0SBundle.normSq0S ((F k).S.base.metric t) x 4
        (metricRm04 ((F k).S.base.metric t) x)) ≤ Bs := fun k t ht => (hF k t ht).1
  have hhalf : T / 2 ∈ Icc 0 T := ⟨by linarith, by linarith⟩
  obtain ⟨hcomplete, -, ⟨hgeom⟩, ⟨hinj⟩⟩ :=
    positiveTimeSlice_canonical_compactness_hypotheses_of_bilipschitz (I := I) gSeq T Bs hT hBpos
      τ hτ F hcurv gRef hΛ hbil p
  exact exists_sectional_nonneg_of_bounded_geometry_limit p
    (fun k => (F k).S.base.metric (T / 2)) hcomplete hgeom hinj
    (Real.exp ((Module.finrank ℝ E : ℝ) ^ 2 * Bs * (T / 2)) * (max d₀ 0 + 1))
    (fun k x y => riemannianEDistOf_le_of_flowTo (F k) (hτ k) hBpos (hcurv k) (hdiam k) hhalf
      x y)
    ε hεlim (fun k => (hF k (T / 2) hhalf).2)

/-- SF1 for the design's `Metric2 = ContMDiffRiemannianMetric I 2`. -/
theorem exists_smooth_curvature_nonneg_of_metric2_dim_two [ConnectedSpace M]
    (hdim : Module.finrank ℝ E = 2)
    (g : Bundle.ContMDiffRiemannianMetric I (2 : ℕ∞ω) E (TangentSpace I : M → Type _))
    (hsec : ∀ x (v w : TangentSpace I x), 0 ≤ g.sectionalCurvature x v w) :
    ∃ h : SmoothRiemannianMetric I M, SectionalBoundedBelow h 0 :=
  exists_smooth_curvature_nonneg_of_finite_metric_dim_two hdim le_rfl g hsec

/-- **Consumer (smooth case).** SF1 applies to a smooth metric with `K ≥ 0` on a closed surface. -/
theorem exists_smooth_curvature_nonneg_of_smooth_dim_two [ConnectedSpace M]
    (hdim : Module.finrank ℝ E = 2) (g : SmoothRiemannianMetric I M)
    (hg : SectionalBoundedBelow g 0) :
    ∃ h : SmoothRiemannianMetric I M, SectionalBoundedBelow h 0 :=
  exists_smooth_curvature_nonneg_of_finite_metric_dim_two hdim (by simp) g
    (sectionalCurvature_nonneg_of_sectionalBoundedBelow_zero g hg)

/-- **SF1 → SF2.** A `C^n` metric (`n ≥ 2`) with `K ≥ 0` on a closed connected surface gives a
smooth flat metric (vanishing curvature tensor) or a smooth metric with positive scalar
curvature everywhere. -/
theorem exists_smooth_flat_or_scalar_pos_of_finite_metric_dim_two [ConnectedSpace M]
    (hdim : Module.finrank ℝ E = 2) {n : ℕ∞ω} (hn : (2 : ℕ∞ω) ≤ n)
    (g : Bundle.ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _))
    (hsec : ∀ x (v w : TangentSpace I x), 0 ≤ g.sectionalCurvature x v w) :
    (∃ h : SmoothRiemannianMetric I M, ∀ x (v w z u : TangentSpace I x),
        metricRm04StandardAt (I := I) (M := M) h x v w z u = 0) ∨
      ∃ h : SmoothRiemannianMetric I M, ∀ x, 0 < metricScalarAt (I := I) h x := by
  obtain ⟨h, hh⟩ := exists_smooth_curvature_nonneg_of_finite_metric_dim_two hdim hn g hsec
  rcases flat_or_exists_scalar_pos_of_sectional_nonneg_dim_two hdim h hh with hflat | hpos
  · exact Or.inl ⟨h, hflat⟩
  · exact Or.inr hpos

end DifferentialGeometry.Geometry.MetricSmoothing

namespace DifferentialGeometry.PDE.RicciFlow

open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.MetricSmoothing

/-- **SF1 → SF2 on `𝓡 2` surfaces.** A `C²` metric with `K ≥ 0` on a closed connected surface
modelled on `ℝ²` gives a smooth flat metric or a smooth metric with `R > 0` everywhere. -/
theorem exists_smooth_flat_or_scalar_pos_of_metric2_euclidean_two
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (𝓡 2) ∞ M] [CompactSpace M] [T2Space M] [ConnectedSpace M]
    (g : Bundle.ContMDiffRiemannianMetric (𝓡 2) (2 : ℕ∞ω) (EuclideanSpace ℝ (Fin 2))
      (TangentSpace (𝓡 2) : M → Type _))
    (hsec : ∀ x (v w : TangentSpace (𝓡 2) x), 0 ≤ g.sectionalCurvature x v w) :
    (∃ h : SmoothRiemannianMetric (𝓡 2) M, ∀ x (v w z u : TangentSpace (𝓡 2) x),
        metricRm04StandardAt (I := 𝓡 2) (M := M) h x v w z u = 0) ∨
      ∃ h : SmoothRiemannianMetric (𝓡 2) M, ∀ x, 0 < metricScalarAt (I := 𝓡 2) h x :=
  exists_smooth_flat_or_scalar_pos_of_finite_metric_dim_two finrank_euclideanSpace_fin le_rfl g
    hsec

/-- **Consumer on an actual surface.** SF1 run on the round two-sphere, regarded as a `C²` metric
(`SmoothRiemannianMetric.toMetric2`), returns a smooth metric with `K ≥ 0` on `S²`. -/
theorem exists_smooth_curvature_nonneg_roundTwoSphere_via_metric2 :
    ∃ h : SmoothRiemannianMetric (𝓡 2) (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1),
      SectionalBoundedBelow h 0 :=
  have := connectedSpace_sphere_euclideanSpace_three
  exists_smooth_curvature_nonneg_of_metric2_dim_two finrank_euclideanSpace_fin
    (SmoothRiemannianMetric.toMetric2 roundTwoSphereShrinkerMetric) fun x v w =>
      (sectionalCurvature_toMetric2 roundTwoSphereShrinkerMetric x v w).symm ▸
        sectionalCurvature_nonneg_of_sectionalBoundedBelow_zero roundTwoSphereShrinkerMetric
          roundTwoSphereShrinkerMetric_sectionalBoundedBelow_zero x v w

end DifferentialGeometry.PDE.RicciFlow
