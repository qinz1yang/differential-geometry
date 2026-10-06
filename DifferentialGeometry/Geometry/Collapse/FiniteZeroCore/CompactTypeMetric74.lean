import DifferentialGeometry.Geometry.Collapse.FiniteZeroCore.CompactClassification
import DifferentialGeometry.Geometry.Collapse.Inhabitants.DihedralCurvature
import DifferentialGeometry.Geometry.Metric.Sphere.Quotient.SphericalMetric
import DifferentialGeometry.Geometry.Metric.Sphere.Quotient.SpaceFormCovering
import DifferentialGeometry.Geometry.Thurston.ConstantCurvatureAtlas
import DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.Sectional

/-!
# Draft 74, G32: a smooth metric of `sec ≥ 0` on every compact nonnegative type

Lane C14-REG-CHAIN (by S-REG-CHAIN3), G32. LPA05's compact-model branch (`CompactModelSublevel`)
records only the TYPE of the closed zero piece (`IsCompactNonnegativeType`: spherical space form,
`S² × S¹`, `ℝP³ # ℝP³`, compact flat), but the closed branch of the zero model
(`ClosedZeroPiece`, `SelectedSmoothCore74.closed`) carries a smooth metric with
`SectionalBoundedBelow g 0`. The converse of LFR53 for the four types:

* spherical space form: the descended round metric of `sphericalSpaceFormQuotientModel…`
  (`sphericalMetric`, `sec = 1`), pulled back by the oriented diffeomorphism;
* `S² × S¹`: the product of the round metrics (the product curvature splits, each factor has
  `Rm04 = Gram ≥ 0`), pulled back by the cross-model diffeomorphism;
* `ℝP³ # ℝP³`: the dihedral metric (`dihedralMetric_sectional_nonneg`), pulled back;
* compact flat: the metric of the Euclidean structure, `sec = 0`.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Curvature

universe u

/-- The Gram form is nonnegative (Cauchy–Schwarz), so a metric whose `Rm04` equals
`κ ·` Gram with `0 ≤ κ` has `sec ≥ 0`. -/
theorem sectionalBoundedBelow_zero_of_rm04_eq_mul_gram74
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (g : SmoothRiemannianMetric I M) {κ : ℝ} (hκ : 0 ≤ κ)
    (h : ∀ (x : M) (X Y : TangentSpace I x), metricRm04StandardAt g x X Y Y X =
      κ * (g.inner x X X * g.inner x Y Y - g.inner x X Y * g.inner x X Y)) :
    SectionalBoundedBelow g 0 := by
  intro x v w
  rw [zero_mul, h x v w]
  refine mul_nonneg hκ (sub_nonneg.mpr ?_)
  simpa only [pow_two] using SmoothRiemannianMetric.metric_inner_cauchy_schwarz_sq g x v w

/-- **Spherical space forms**: the descended round metric. -/
theorem exists_nonneg_metric_sphericalSpaceForm74 (G : SphericalSpaceFormGroup) :
    ∃ g : SmoothRiemannianMetric (𝓡 3) G.manifold.Carrier, SectionalBoundedBelow g 0 :=
  ⟨GC.Geometry.sphericalMetric (sphericalSpaceFormQuotientModelOfSphericalSpaceFormGroup G),
    sectionalBoundedBelow_zero_of_rm04_eq_mul_gram74 _ zero_le_one (fun x X Y =>
      (GC.Geometry.sphericalMetric_sectional_one _ x X Y).trans (one_mul _).symm)⟩

/-- **`ℝP³ # ℝP³`**: the unit dihedral metric. -/
theorem exists_nonneg_metric_dihedral74 :
    ∃ g : SmoothRiemannianMetric (𝓡 3)
      (connectedSum projectiveThreeSpaceLift.{0} projectiveThreeSpaceLift.{0}).Carrier,
      SectionalBoundedBelow g 0 :=
  ⟨dihedralMetric 1 1 one_pos one_pos,
    fun x => dihedralMetric_sectional_nonneg 1 1 one_pos one_pos x⟩

/-- **Compact flat manifolds**: the metric of the Euclidean structure has `sec = 0`. -/
theorem sectionalBoundedBelow_zero_of_euclidean74 {P : ConnectedClosedOrientedManifold.{u} 3}
    (G : GC.Geometry.GeometricStructure (𝓡 3) P.Carrier) (hG : G.model = .euclidean) :
    SectionalBoundedBelow G.metric 0 := by
  have hA : GC.Geometry.HasThurstonAtlas G.metric .euclidean := hG ▸ G.atlas
  have hc := (GC.Geometry.hasConstantSectionalCurvature_iff G.metric 0).mp
    (GC.Geometry.hasConstantSectionalCurvature_of_hasThurstonAtlas_euclidean hA)
  exact sectionalBoundedBelow_zero_of_rm04_eq_mul_gram74 G.metric le_rfl hc

section SphereTwoTimesCircle

local instance sphereTwoDim74 : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
  ⟨by simp⟩

local instance sphereOneDim74 : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 1 + 1) :=
  ⟨by simp⟩

/-- The product of the round metrics of `S²` and `S¹`. -/
def sphereTwoTimesCircleMetric74 :
    SmoothRiemannianMetric ((𝓡 2).prod (𝓡 1)) SphereTwoTimesCircle :=
  (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).prod
    (roundMetric (E := EuclideanSpace ℝ (Fin 2)) (n := 1))

/-- On a round sphere `Rm04` of a four-tuple `(v, w, w, v)` (in `vec4` slots) is nonnegative. -/
theorem metricRm04At_round_nonneg74 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {n : ℕ} [Fact (Module.finrank ℝ E = n + 1)]
    (x : Metric.sphere (0 : E) 1) (b : Fin 4 → TangentSpace (𝓡 n) x) (h03 : b 0 = b 3)
    (h12 : b 1 = b 2) : 0 ≤ metricRm04At (roundMetric (E := E) (n := n)) x b := by
  have hb : b = vec4 (b 0) (b 1) (b 2) (b 3) := by
    ext k
    fin_cases k <;> rfl
  rw [hb, ← metricRm04StandardAt_apply, ← h03, ← h12, roundMetric_sec_value]
  refine sub_nonneg.mpr ?_
  simpa only [pow_two] using
    SmoothRiemannianMetric.metric_inner_cauchy_schwarz_sq (roundMetric (E := E) (n := n)) x
      (b 0) (b 1)

/-- **`S² × S¹`**: the product of the round metrics has `sec ≥ 0` (the curvature of a product
splits, and each round factor has `Rm04 = Gram ≥ 0`). -/
theorem sphereTwoTimesCircleMetric74_nonneg :
    SectionalBoundedBelow sphereTwoTimesCircleMetric74 0 := by
  intro x v w
  rw [zero_mul, metricRm04StandardAt_apply, sphereTwoTimesCircleMetric74,
    metricRm04At_productMetric_apply]
  exact add_nonneg
    (metricRm04At_round_nonneg74 (E := EuclideanSpace ℝ (Fin 3)) (n := 2) x.1 _ rfl rfl)
    (metricRm04At_round_nonneg74 (E := EuclideanSpace ℝ (Fin 2)) (n := 1) x.2 _ rfl rfl)

end SphereTwoTimesCircle

/-- **LFR53, converse for the four types.** A closed connected oriented three-manifold of one of
LFR53's four smooth types (`IsCompactNonnegativeType`) carries a smooth metric with `sec ≥ 0`;
the metric is canonical for the type, transported by the diffeomorphism. -/
theorem exists_nonneg_metric_of_isCompactNonnegativeType74
    (P : ConnectedClosedOrientedManifold.{0} 3) (h : IsCompactNonnegativeType P) :
    ∃ g : SmoothRiemannianMetric (𝓡 3) P.Carrier, SectionalBoundedBelow g 0 := by
  rcases h with ⟨Γ, ⟨F⟩⟩ | ⟨⟨Φ⟩⟩ | ⟨⟨Φ⟩⟩ | ⟨⟨G, hG⟩, -⟩
  · obtain ⟨g, hg⟩ := exists_nonneg_metric_sphericalSpaceForm74 Γ
    exact exists_sectionalBoundedBelow_of_diffeomorph F.1 g hg
  · exact exists_sectionalBoundedBelow_of_diffeomorph Φ _ sphereTwoTimesCircleMetric74_nonneg
  · obtain ⟨g, hg⟩ := exists_nonneg_metric_dihedral74
    exact exists_sectionalBoundedBelow_of_diffeomorph Φ g hg
  · exact ⟨G.metric, sectionalBoundedBelow_zero_of_euclidean74 G hG⟩

end DifferentialGeometry.Geometry.Collapse
