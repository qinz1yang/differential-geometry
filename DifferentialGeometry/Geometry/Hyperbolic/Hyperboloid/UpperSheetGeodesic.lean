import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.UpperSheet
import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.RiemannianGeodesic
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Geodesic.AsymptoticRays

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.Hyperboloid

open Hyperbolic (HUpper LorVec tc lorB)
open HyperbolicBoundary (BoundaryH)
open HyperbolicConvexity (dirVec geodFromTo)
open AsymptoticRays (dirTo rayTo)

variable {n : ℕ}

private theorem lorentzForm_coordinate_pair (v w : LorVec n) :
    lorentzForm (EuclideanSpace ℝ (Fin n))
      (tc v, WithLp.toLp 2 (fun i : Fin n => v (Sum.inl i)))
      (tc w, WithLp.toLp 2 (fun i : Fin n => w (Sum.inl i))) = lorB v w := by
  simp [lorentzForm_apply, PiLp.inner_apply, Hyperbolic.lorB, Hyperbolic.sdot, mul_comm]

private theorem lorentzForm_upper_coordinate_pair (x : HUpper n) (v : LorVec n) :
    lorentzForm (EuclideanSpace ℝ (Fin n))
      ((hUpperIsometryEquiv n x).time, (hUpperIsometryEquiv n x).space)
      (tc v, WithLp.toLp 2 (fun i : Fin n => v (Sum.inl i))) = lorB x.val v := by
  exact lorentzForm_coordinate_pair x.val v

private theorem dirVec_coordinate_unit {x y : HUpper n} (hxy : x ≠ y) :
    lorentzForm (EuclideanSpace ℝ (Fin n))
      (tc (dirVec x y), WithLp.toLp 2 (fun i : Fin n => dirVec x y (Sum.inl i)))
      (tc (dirVec x y), WithLp.toLp 2 (fun i : Fin n => dirVec x y (Sum.inl i))) = 1 := by
  rw [lorentzForm_coordinate_pair]
  exact HyperbolicConvexity.lorB_dirVec_self hxy

private theorem dirVec_coordinate_orthogonal (x y : HUpper n) :
    lorentzForm (EuclideanSpace ℝ (Fin n))
      ((hUpperIsometryEquiv n x).time, (hUpperIsometryEquiv n x).space)
      (tc (dirVec x y), WithLp.toLp 2 (fun i : Fin n => dirVec x y (Sum.inl i))) = 0 := by
  rw [lorentzForm_upper_coordinate_pair, Hyperbolic.lorB_comm]
  exact HyperbolicConvexity.lorB_dirVec_left x y

private theorem dirTo_coordinate_unit (x : HUpper n) (ξ : BoundaryH n) :
    lorentzForm (EuclideanSpace ℝ (Fin n))
      (tc (dirTo x ξ), WithLp.toLp 2 (fun i : Fin n => dirTo x ξ (Sum.inl i)))
      (tc (dirTo x ξ), WithLp.toLp 2 (fun i : Fin n => dirTo x ξ (Sum.inl i))) = 1 := by
  rw [lorentzForm_coordinate_pair]
  exact AsymptoticRays.lorB_dirTo_self x ξ

private theorem dirTo_coordinate_orthogonal (x : HUpper n) (ξ : BoundaryH n) :
    lorentzForm (EuclideanSpace ℝ (Fin n))
      ((hUpperIsometryEquiv n x).time, (hUpperIsometryEquiv n x).space)
      (tc (dirTo x ξ), WithLp.toLp 2 (fun i : Fin n => dirTo x ξ (Sum.inl i))) = 0 := by
  rw [lorentzForm_upper_coordinate_pair, Hyperbolic.lorB_comm]
  exact AsymptoticRays.lorB_dirTo_left x ξ

theorem hUpperIsometryEquiv_geodFromTo (x y : HUpper n) (hxy : x ≠ y) (t : ℝ) :
    hUpperIsometryEquiv n (geodFromTo x y hxy t) =
      geodesicLine (hUpperIsometryEquiv n x)
        (tc (dirVec x y), WithLp.toLp 2 (fun i : Fin n => dirVec x y (Sum.inl i)))
        (dirVec_coordinate_unit hxy) (dirVec_coordinate_orthogonal x y) t := by
  apply Hyperboloid.ext
  apply PiLp.ext
  intro i
  rw [hUpperIsometryEquiv_space_apply, geodesicLine_space]
  change Real.cosh t * x.val (Sum.inl i) + Real.sinh t * dirVec x y (Sum.inl i) = _
  rfl

theorem hUpperIsometryEquiv_rayTo (x : HUpper n) (ξ : BoundaryH n) (t : ℝ) :
    hUpperIsometryEquiv n (rayTo x ξ t) =
      geodesicLine (hUpperIsometryEquiv n x)
        (tc (dirTo x ξ), WithLp.toLp 2 (fun i : Fin n => dirTo x ξ (Sum.inl i)))
        (dirTo_coordinate_unit x ξ) (dirTo_coordinate_orthogonal x ξ) t := by
  apply Hyperboloid.ext
  apply PiLp.ext
  intro i
  rw [hUpperIsometryEquiv_space_apply, geodesicLine_space]
  change Real.cosh t * x.val (Sum.inl i) + Real.sinh t * dirTo x ξ (Sum.inl i) = _
  rfl

theorem isGeodesic_hUpperIsometryEquiv_geodFromTo (x y : HUpper n) (hxy : x ≠ y) :
    Geometry.Riemannian.Geodesic.IsGeodesic riemannianMetric
      (fun t => hUpperIsometryEquiv n (geodFromTo x y hxy t)) := by
  simp_rw [hUpperIsometryEquiv_geodFromTo]
  exact isGeodesic_geodesicLine _ _ _ _

theorem isGeodesic_hUpperIsometryEquiv_rayTo (x : HUpper n) (ξ : BoundaryH n) :
    Geometry.Riemannian.Geodesic.IsGeodesic riemannianMetric
      (fun t => hUpperIsometryEquiv n (rayTo x ξ t)) := by
  simp_rw [hUpperIsometryEquiv_rayTo]
  exact isGeodesic_geodesicLine _ _ _ _

theorem hUpperIsometryEquiv_geodFromTo_unit_speed (x y : HUpper n) (hxy : x ≠ y) (t : ℝ) :
    riemannianMetric.inner (hUpperIsometryEquiv n (geodFromTo x y hxy t))
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        (fun s => hUpperIsometryEquiv n (geodFromTo x y hxy s)) t
          ((NormedSpace.fromTangentSpace (𝕜 := ℝ) t).symm 1))
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        (fun s => hUpperIsometryEquiv n (geodFromTo x y hxy s)) t
          ((NormedSpace.fromTangentSpace (𝕜 := ℝ) t).symm 1)) = 1 := by
  exact geodesicLine_unit_speed (hUpperIsometryEquiv n x)
    (tc (dirVec x y), WithLp.toLp 2 (fun i : Fin n => dirVec x y (Sum.inl i)))
    (dirVec_coordinate_unit hxy) (dirVec_coordinate_orthogonal x y) t

theorem hUpperIsometryEquiv_rayTo_unit_speed (x : HUpper n) (ξ : BoundaryH n) (t : ℝ) :
    riemannianMetric.inner (hUpperIsometryEquiv n (rayTo x ξ t))
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        (fun s => hUpperIsometryEquiv n (rayTo x ξ s)) t
          ((NormedSpace.fromTangentSpace (𝕜 := ℝ) t).symm 1))
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        (fun s => hUpperIsometryEquiv n (rayTo x ξ s)) t
          ((NormedSpace.fromTangentSpace (𝕜 := ℝ) t).symm 1)) = 1 := by
  exact geodesicLine_unit_speed (hUpperIsometryEquiv n x)
    (tc (dirTo x ξ), WithLp.toLp 2 (fun i : Fin n => dirTo x ξ (Sum.inl i)))
    (dirTo_coordinate_unit x ξ) (dirTo_coordinate_orthogonal x ξ) t

end DifferentialGeometry.Hyperboloid
