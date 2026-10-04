import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryLocalization
import DifferentialGeometry.Geometry.Collapse.LocalExport.StaticInterface
import DifferentialGeometry.Geometry.Curvature.Metric.DerivativeNorm

/-!
# Consumers of the LC88 localisation and the LC90 closed interface

* `boundary_localization_of_hyperbolic_plane`: the LC88 localisation at a point carrying a plane of
  exact cusp curvature `-1/4` (the reference curvature of the depth-100 cusp collar): the selected
  zero radius is below `1/20` and the whole selected ball stays at distance greater than nine from
  the boundary.
* `eventual_bound_of_fixed_family`: for a FIXED finite family of compact carriers (constant in `j`)
  the eventual whole-ball derivative tests hold by compactness, with `N = 0`.
* `exists_threshold_fixed_closed_family_rawGraph`: hence LC90's closed interface applies to any
  finite list of connected closed carriers with no analytic input beyond the static theorem.
-/

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Riemannian GC.Endpoint GC.GraphManifold
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff ENNReal
namespace DifferentialGeometry.Geometry.Collapse
universe u

/-- LC88 localisation at a plane of exact cusp curvature `-1/4`. -/
theorem boundary_localization_of_hyperbolic_plane (W : CompactCarrier.{u})
    (g : SmoothRiemannianMetric W.model W.Carrier) {i x : W.Carrier} {r : ℝ} (hr : 0 < r)
    (v w : TangentSpace W.model x)
    (hplane : 0 < g.inner x v v * g.inner x w w - g.inner x v w ^ 2)
    (hlower : SectionalBoundedBelowAt g x (-(1 / (60 * r) ^ 2)))
    (hcusp : metricRm04StandardAt (I := W.model) (M := W.Carrier) g x v w w v =
      -(1 / 4) * (g.inner x v v * g.inner x w w - g.inner x v w ^ 2))
    (hi : ENNReal.ofReal boundaryBufferDistance < distanceToBoundary W g i) :
    r < 1 / 20 ∧ ∀ y ∈ riemannianBallOf g i r, ENNReal.ofReal 9 < distanceToBoundary W g y := by
  have hupper : metricRm04StandardAt (I := W.model) (M := W.Carrier) g x v w w v ≤
      -(1 / 8) * (g.inner x v v * g.inner x w w - g.inner x v w ^ 2) := by
    rw [hcusp]
    linarith
  obtain ⟨-, h2, h3⟩ := boundary_localization W g hr v w hplane hlower hupper hi
  exact ⟨h2, h3⟩

/-- For a fixed finite family of compact carriers, the eventual whole-ball derivative tests of
LC89/LC90 hold from the start (`N = 0`), by compactness. -/
theorem eventual_bound_of_fixed_family (K : ℕ) (ι : Type*) [Finite ι]
    (W : ι → CompactCarrier.{u}) (g : (i : ι) → SmoothRiemannianMetric (W i).model (W i).Carrier) :
    ∀ w : ℝ, 0 < w → w < euclideanThreeUnitBallVolume →
      ∃ N : ℕ, ∃ C : ℝ, 0 < C ∧
        ∀ j : ℕ, N ≤ j → ∀ (i : ι) (p : (W i).Carrier) (r : ℝ), 0 < r →
          ENNReal.ofReal r < curvatureRadius (g i) p →
          ENNReal.ofReal (w * r ^ 3) ≤ ballVolume (g i) p r →
          ∀ k : ℕ, k ≤ K → ∀ q ∈ riemannianBallOf (g i) p r,
            curvatureDerivativeNorm (g i) k q ≤ C * (r ^ (k + 2))⁻¹ := by
  classical
  intro w hw _
  have := Fintype.ofFinite ι
  choose B hB hbound using fun i => exists_bound_curvatureDerivativeNorm_of_compactSpace (g i) K
  choose R hR hradius using fun i => exists_radius_bound_of_volume_lower (W i) (g i) w hw
  let D : ι → ℝ := fun i => B i * (max 1 (R i)) ^ (K + 2)
  have hD : ∀ i, 0 ≤ D i := fun i =>
    mul_nonneg (hB i) (pow_nonneg ((zero_le_one).trans (le_max_left _ _)) _)
  refine ⟨0, 1 + ∑ i, D i, by
    have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => hD i); linarith, ?_⟩
  intro j _ i p r hr _ hv k hk q _
  have hrk : 0 < r ^ (k + 2) := pow_pos hr _
  rw [le_mul_inv_iff₀ hrk]
  have hr1 : r ≤ max 1 (R i) := (hradius i p r hr hv).trans (le_max_right _ _)
  have hpow : r ^ (k + 2) ≤ (max 1 (R i)) ^ (K + 2) :=
    (pow_le_pow_left₀ hr.le hr1 _).trans (pow_le_pow_right₀ (le_max_left _ _) (by omega))
  have hDi : B i * r ^ (k + 2) ≤ D i := mul_le_mul_of_nonneg_left hpow (hB i)
  have hsum : D i ≤ ∑ l, D l := Finset.single_le_sum (fun l _ => hD l) (Finset.mem_univ i)
  have hq := mul_le_mul_of_nonneg_right (hbound i k hk q) hrk.le
  linarith

/-- LC90's closed interface for a fixed finite list of connected carriers: given the closed static
theorem at order `K`, one threshold `w₀` serves the whole list, and each closed carrier volume
collapsed below `w₀` has a raw graph presentation. -/
theorem exists_threshold_fixed_closed_family_rawGraph (K : ℕ) (ι : Type*) [Finite ι]
    (W : ι → CompactCarrier.{u}) [∀ i, ConnectedSpace (W i).Carrier]
    (g : (i : ι) → SmoothRiemannianMetric (W i).model (W i).Carrier)
    (static : ∀ A : ℝ → ℝ, (∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w) →
      ∃ w₀ : ℝ, 0 < w₀ ∧ w₀ < euclideanThreeUnitBallVolume ∧
        ∀ (V : CompactCarrier.{u}) [ConnectedSpace V.Carrier]
          (h : SmoothRiemannianMetric V.model V.Carrier),
          closedCollapseHypotheses V h K A w₀ → Nonempty (RawGraphPresentation V)) :
    ∃ w₀ : ℝ, 0 < w₀ ∧ w₀ < euclideanThreeUnitBallVolume ∧
      ∀ i : ι, (W i).model.boundary (W i).Carrier = ∅ →
        (∀ p, volumeCollapsedAtCurvatureScale (g i) w₀ p) →
        Nonempty (RawGraphPresentation (W i)) := by
  obtain ⟨w₀, hw₀, hwc, h⟩ := exists_threshold_closed_components_rawGraph K (fun _ => ι)
    (fun _ i => W i) (fun _ i => g i) (eventual_bound_of_fixed_family K ι W g) static
  exact ⟨w₀, hw₀, hwc, fun i => h 0 i⟩

end DifferentialGeometry.Geometry.Collapse
