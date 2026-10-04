import DifferentialGeometry.Geometry.Flow.RicciFlow.Preservation.ScalarPositivity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Preservation.SurfaceSectionalLowerBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.CompactCommonExistence

/-!
# A nonnegatively curved closed surface is flat or carries a positively curved metric (SF2)

Let `g` be a smooth metric with `K ≥ 0` on a closed connected surface. In dimension two
`Rm = (R / 2) g ∧ g`, so either `R ≡ 0` and `g` is flat, or `R(g) ≥ 0` is positive somewhere. In
the second case run the Ricci flow for a short time (`flow_to_seed`): along the flow
`∂R = ΔR + 2|Ric|² ≥ ΔR`, and the strong maximum principle
(`scalar_curvature_positive_of_nonnegative_initial`) makes `R > 0` everywhere at every positive
time. The time slice is the required smooth metric of positive curvature.

This is row SF2 of package SURF (`design-finite-surface-foundations-20261004.md` §C2 step 2,
§D2). The positive branch has the input shape of the two-dimensional Hamilton theorem
(`∀ y, 0 < metricScalarAt h y`).
-/

set_option autoImplicit false

noncomputable section

open Set
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [CompactSpace M]
  [T2Space M] [BoundarylessManifold I M]

/-- The positive branch: a smooth metric with `K ≥ 0` on a closed connected surface whose scalar
curvature is positive at one point is followed by a smooth metric with `R > 0` everywhere. -/
theorem exists_scalar_pos_of_sectional_nonneg_of_scalar_pos_dim_two [ConnectedSpace M]
    (hdim : Module.finrank ℝ E = 2) (g : SmoothRiemannianMetric I M)
    (hg : SectionalBoundedBelow g 0) {x₀ : M} (hx₀ : 0 < metricScalarAt (I := I) g x₀) :
    ∃ h : SmoothRiemannianMetric I M, ∀ x, 0 < metricScalarAt (I := I) h x := by
  have : NeZero (Module.finrank ℝ E) := ⟨by omega⟩
  have hR : ∀ x, 0 ≤ metricScalarAt (I := I) g x := fun x => by
    have h := (sectionalBoundedBelow_iff_two_mul_le_scalar_of_finrank_eq_two hdim).1 hg x
    linarith
  obtain ⟨τ, ⟨F⟩⟩ := flow_to_seed (I := I) g
  have hτ : 0 < τ := F.time_pos
  have hstart : F.S.base.metric 0 = g := by
    simpa only [SolutionOn.family_metric] using F.start
  refine ⟨F.S.base.metric (τ / 2), fun y => ?_⟩
  have hinit : ∀ x : M, 0 ≤ F.S.scalar 0 x := fun x => by
    change 0 ≤ metricScalarAt (I := I) (F.S.base.metric 0) x
    rw [hstart]
    exact hR x
  have hpos0 : 0 < F.S.scalar 0 x₀ := by
    change 0 < metricScalarAt (I := I) (F.S.base.metric 0) x₀
    rw [hstart]
    exact hx₀
  exact scalar_curvature_positive_of_nonnegative_initial F.S F.isSmoothSolutionOn
    (half_pos hτ) (F.Icc_subset_carrier (half_lt_self hτ))
    (F.Ioc_subset_regular (half_lt_self hτ)) hinit hpos0 y

/-- **SF2.** A smooth metric with `K ≥ 0` on a closed connected surface is flat (its whole
curvature tensor vanishes), or the surface carries a smooth metric with positive scalar
curvature everywhere. -/
theorem flat_or_exists_scalar_pos_of_sectional_nonneg_dim_two [ConnectedSpace M]
    (hdim : Module.finrank ℝ E = 2) (g : SmoothRiemannianMetric I M)
    (hg : SectionalBoundedBelow g 0) :
    (∀ x (v w z u : TangentSpace I x), metricRm04StandardAt (I := I) (M := M) g x v w z u = 0) ∨
      ∃ h : SmoothRiemannianMetric I M, ∀ x, 0 < metricScalarAt (I := I) h x := by
  by_cases hflat : ∀ x, metricScalarAt (I := I) g x = 0
  · exact Or.inl fun x v w z u =>
      metricRm04StandardAt_eq_zero_of_scalar_eq_zero_of_finrank_eq_two g hdim (hflat x) v w z u
  · obtain ⟨x₀, hx₀⟩ := not_forall.mp hflat
    have hR := (sectionalBoundedBelow_iff_two_mul_le_scalar_of_finrank_eq_two hdim).1 hg x₀
    have hpos : 0 < metricScalarAt (I := I) g x₀ := lt_of_le_of_ne (by linarith) (Ne.symm hx₀)
    exact Or.inr (exists_scalar_pos_of_sectional_nonneg_of_scalar_pos_dim_two hdim g hg hpos)

omit [BoundarylessManifold I M] in
/-- On a closed surface, positive scalar curvature everywhere is a uniform positive lower bound
of the sectional curvature. -/
theorem exists_sectionalBoundedBelow_pos_of_scalar_pos_dim_two [Nonempty M]
    (hdim : Module.finrank ℝ E = 2) (h : SmoothRiemannianMetric I M)
    (hpos : ∀ x, 0 < metricScalarAt (I := I) h x) :
    ∃ κ : ℝ, 0 < κ ∧ SectionalBoundedBelow h κ := by
  obtain ⟨xm, -, hxm⟩ := isCompact_univ.exists_isMinOn univ_nonempty
    (metricScalar_smooth (I := I) h).continuous.continuousOn
  refine ⟨metricScalarAt (I := I) h xm / 2, half_pos (hpos xm), ?_⟩
  refine (sectionalBoundedBelow_iff_two_mul_le_scalar_of_finrank_eq_two hdim).2 fun x => ?_
  have hx : metricScalarAt (I := I) h xm ≤ metricScalarAt (I := I) h x := hxm (mem_univ x)
  linarith

/-- **SF2, sectional form.** A smooth metric with `K ≥ 0` on a closed connected surface is flat,
or the surface carries a smooth metric with `K ≥ κ` for some `κ > 0`. -/
theorem flat_or_exists_sectional_pos_of_sectional_nonneg_dim_two [ConnectedSpace M]
    (hdim : Module.finrank ℝ E = 2) (g : SmoothRiemannianMetric I M)
    (hg : SectionalBoundedBelow g 0) :
    (∀ x (v w z u : TangentSpace I x), metricRm04StandardAt (I := I) (M := M) g x v w z u = 0) ∨
      ∃ h : SmoothRiemannianMetric I M, ∃ κ : ℝ, 0 < κ ∧ SectionalBoundedBelow h κ := by
  rcases flat_or_exists_scalar_pos_of_sectional_nonneg_dim_two hdim g hg with hflat | ⟨h, hpos⟩
  · exact Or.inl hflat
  · have : Nonempty M := ConnectedSpace.toNonempty
    exact Or.inr ⟨h, exists_sectionalBoundedBelow_pos_of_scalar_pos_dim_two hdim h hpos⟩

end DifferentialGeometry.PDE.RicciFlow
