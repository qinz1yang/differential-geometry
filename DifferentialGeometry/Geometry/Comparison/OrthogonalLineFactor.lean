import DifferentialGeometry.Geometry.Comparison.CrossingLineCoordinates
import DifferentialGeometry.Geometry.Comparison.LineSplitting
import DifferentialGeometry.Geometry.Comparison.MetricTransfer

set_option autoImplicit false
open Set Filter Topology

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

variable {X : Type*} [MetricSpace X] {γ β δ : ℝ → X}

def orthogonalLineInFactor
    (hs : fourPointComparison 0 (univ : Set X)) (hγ : Isometry γ) (hβ : Isometry β)
    (hbase : γ 0 = β 0) (hangle : germComparisonAngle 0 γ β = Real.pi / 2) :
    ℝ → {x : X // lineCoordinate γ x = 0} :=
  fun t => ⟨β t, lineCoordinate_crossing_isometry_eq_zero_of_right_angle hs hγ hβ hbase hangle t⟩

theorem isometry_orthogonalLineInFactor
    (hs : fourPointComparison 0 (univ : Set X)) (hγ : Isometry γ) (hβ : Isometry β)
    (hbase : γ 0 = β 0) (hangle : germComparisonAngle 0 γ β = Real.pi / 2) :
    Isometry (orthogonalLineInFactor hs hγ hβ hbase hangle) := by
  apply Isometry.of_dist_eq
  intro s t
  exact hβ.dist_eq s t

theorem orthogonalLineInFactor_zero
    (hs : fourPointComparison 0 (univ : Set X)) (hγ : Isometry γ) (hβ : Isometry β)
    (hbase : γ 0 = β 0) (hangle : germComparisonAngle 0 γ β = Real.pi / 2) :
    orthogonalLineInFactor hs hγ hβ hbase hangle 0 =
      ⟨γ 0, lineCoordinate_apply_isometry hγ 0⟩ := by
  exact Subtype.ext hbase.symm

theorem germComparisonAngle_orthogonalLineInFactor
    (hs : fourPointComparison 0 (univ : Set X)) (hγ : Isometry γ)
    (hβ : Isometry β) (hδ : Isometry δ)
    (hβbase : γ 0 = β 0) (hδbase : γ 0 = δ 0)
    (hβangle : germComparisonAngle 0 γ β = Real.pi / 2)
    (hδangle : germComparisonAngle 0 γ δ = Real.pi / 2) (κ : ℝ) :
    germComparisonAngle κ (orthogonalLineInFactor hs hγ hβ hβbase hβangle)
      (orthogonalLineInFactor hs hγ hδ hδbase hδangle) = germComparisonAngle κ β δ := by
  exact (germComparisonAngle_comp_of_eventually_dist_eq
    (f := (Subtype.val : {x : X // lineCoordinate γ x = 0} → X))
    (γ := orthogonalLineInFactor hs hγ hβ hβbase hβangle)
    (β := orthogonalLineInFactor hs hγ hδ hδbase hδangle)
    (Eventually.of_forall (fun _ => rfl))).symm

theorem lineSplitting_apply_of_lineCoordinate_eq_zero
    [ProperSpace X] (hs : fourPointComparison 0 (univ : Set X)) (hγ : Isometry γ)
    (hsegments : ∀ a b : X, ∃ f : Icc (0 : ℝ) 1 → X,
      Continuous f ∧ f ⟨0, by norm_num⟩ = a ∧ f ⟨1, by norm_num⟩ = b ∧
      ∀ s t, dist (f s) (f t) = dist a b * dist s t)
    (x : X) (hx : lineCoordinate γ x = 0) :
    lineSplitting hs hγ hsegments x = WithLp.toLp 2 (0, ⟨x, hx⟩) := by
  apply (WithLp.equiv 2 _).injective
  apply Prod.ext
  · exact hx
  · apply Subtype.ext
    change lineTranslation hs hγ hsegments (-lineCoordinate γ x) x = x
    rw [hx, neg_zero, lineTranslation_zero]

end DifferentialGeometry.Geometry.Comparison.Toponogov
