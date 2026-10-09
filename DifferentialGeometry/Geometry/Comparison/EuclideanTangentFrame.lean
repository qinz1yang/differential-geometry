import DifferentialGeometry.Geometry.Metric.TangentCone
import DifferentialGeometry.Geometry.Metric.ConeAntipodalLine
import DifferentialGeometry.Geometry.Comparison.OrthogonalLineSplitting
import DifferentialGeometry.Geometry.Comparison.OriginalFactorGeometry

set_option autoImplicit false

open Set Metric Filter Topology
open scoped NNReal
open DifferentialGeometry.Geometry.Comparison.Toponogov

namespace Metric.EuclideanCone

theorem germComparisonAngle_twoRayPath {Y : Type*} [MetricSpace Y] (a b c d : Y) :
    germComparisonAngle 0 (twoRayPath a b) (twoRayPath c d) = min Real.pi (dist a c) := by
  have hpoint (s t : ℝ) (hs : 0 < s) (ht : 0 < t) :
      comparisonAngleNegCurvature 0 s t (dist (twoRayPath a b s) (twoRayPath c d t)) =
        min Real.pi (dist a c) := by
    rw [twoRayPath, ite_eq_left hs.le, twoRayPath, ite_eq_left ht.le, dist_mk,
      comparisonAngleNegCurvature_zero, comparisonAngle, comparisonCosine]
    have he := coneDistance_sq (x := (s, a)) (y := (t, c)) hs.le ht.le
    simp only [Real.coe_toNNReal s hs.le, Real.coe_toNNReal t ht.le]
    rw [he]
    have hquot : (s ^ 2 + t ^ 2 - (s ^ 2 + t ^ 2 -
        2 * s * t * Real.cos (min Real.pi (dist a c)))) / (2 * s * t) =
          Real.cos (min Real.pi (dist a c)) := by
      field_simp
      ring
    rw [hquot]
    exact Real.arccos_cos (le_min Real.pi_pos.le dist_nonneg) (min_le_left _ _)
  apply germComparisonAngle_eq_of_tendsto
  apply tendsto_const_nhds.congr'
  have hp : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  filter_upwards [hp.prod_inl _, hp.prod_inr _] with z hs ht
  exact (hpoint z.1 z.2 hs ht).symm

end Metric.EuclideanCone

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

theorem exists_pointed_euclidean_tangent_of_orthogonal_frame
    {X : Type*} [MetricSpace X] (q : X) [HasAnglesAt q] [ProperSpace (TangentCone q)]
    {m : ℕ} (hcomp : fourPointComparison 0 (univ : Set (TangentCone q)))
    (hsegments : ∀ x y : TangentCone q, ∃ f : unitInterval → TangentCone q,
      Continuous f ∧ f 0 = x ∧ f 1 = y ∧
      ∀ s t, dist (f s) (f t) = dist x y * dist s t)
    (hdim : dimH (univ : Set (TangentCone q)) ≤ m)
    (v : (Fin m × Bool) → SpaceOfDirections q)
    (hopposite : ∀ i, dist (v (i, true)) (v (i, false)) = Real.pi)
    (horthogonal : ∀ i j, i ≠ j → dist (v (i, true)) (v (j, true)) = Real.pi / 2) :
    ∃ e : TangentCone q ≃ᵢ EuclideanSpace ℝ (Fin m), e EuclideanCone.tip = 0 := by
  cases m with
  | zero =>
    let : Subsingleton (TangentCone q) := Metric.subsingleton_of_dimH_lt_one hsegments
      (hdim.trans_lt (by norm_num))
    refine ⟨{
      toFun := fun _ => 0
      invFun := fun _ => EuclideanCone.tip
      left_inv := fun _ => Subsingleton.elim _ _
      right_inv := fun _ => Subsingleton.elim _ _
      isometry_toFun := Isometry.of_dist_eq (fun x y => by rw [Subsingleton.elim x y]; simp) }, rfl⟩
  | succ k =>
    let γ : Fin (k + 1) → ℝ → TangentCone q :=
      fun i => EuclideanCone.twoRayPath (v (i, true)) (v (i, false))
    have hγ (i : Fin (k + 1)) : Isometry (γ i) :=
      EuclideanCone.isometry_twoRayPath_iff.mpr (hopposite i).ge
    have hγ0 (i : Fin (k + 1)) : γ i 0 = EuclideanCone.tip :=
      EuclideanCone.twoRayPath_zero _ _
    have hangle (i j : Fin (k + 1)) (hij : i ≠ j) :
        germComparisonAngle 0 (γ i) (γ j) = Real.pi / 2 := by
      rw [EuclideanCone.germComparisonAngle_twoRayPath, horthogonal i j hij,
        min_eq_right (by linarith [Real.pi_pos] : Real.pi / 2 ≤ Real.pi)]
    obtain ⟨Z, mZ, z, e, he, _, _, _, _, _⟩ := exists_oriented_euclidean_splitting
      EuclideanCone.tip hcomp hsegments γ hγ hγ0 hangle
    let := mZ
    exact IsometryEquiv.exists_pointed_euclidean_of_nonnegative_comparison
      (by omega : 1 ≤ k + 1) hsegments hcomp hdim e EuclideanCone.tip z he

end DifferentialGeometry.Geometry.Comparison.Toponogov
