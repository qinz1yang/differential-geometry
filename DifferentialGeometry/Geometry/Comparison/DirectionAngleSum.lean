import DifferentialGeometry.Geometry.Comparison.GeodesicDirectionCurvature
import DifferentialGeometry.Geometry.Comparison.CanonicalLocalAngle

set_option autoImplicit false

open Set Filter Topology Metric
open UniformSpace (Completion)
open DifferentialGeometry.Geometry.Comparison.Toponogov

namespace Metric.SpaceOfDirections

variable {X : Type*} [MetricSpace X] {p : X} [HasAnglesAt p]

theorem dist_add_dist_add_dist_le_two_pi_of_local_fourPointComparison
    {κ : ℝ} (hκ : 0 ≤ κ) {Ω : Set X} (hΩ : IsOpen Ω)
    (hcomp : fourPointComparison κ Ω) (hp : p ∈ Ω)
    (a b c : SpaceOfDirections p) :
    dist a b + dist b c + dist c a ≤ 2 * Real.pi := by
  have heq (σ τ : GeodesicRepresentative p) :
      germComparisonAngle κ σ.path τ.path = dist σ.direction τ.direction := by
    exact tendsto_nhds_unique
      (tendsto_germComparisonAngle_of_local_fourPointComparison hκ
        σ.length_pos τ.length_pos hΩ hcomp hp
        (fun _ ht => σ.dist_base_path ⟨ht.1.le, ht.2⟩)
        (fun _ ht => τ.dist_base_path ⟨ht.1.le, ht.2⟩)
        (fun _ hs _ ht => σ.dist_path ⟨hs.1.le, hs.2⟩ ⟨ht.1.le, ht.2⟩)
        (fun _ hs _ ht => τ.dist_path ⟨hs.1.le, hs.2⟩ ⟨ht.1.le, ht.2⟩))
      (σ.tendsto_comparisonAngleNegCurvature_dist_direction τ hκ)
  change dist (show Completion (GeodesicDirections p) from a) b + dist b c +
    dist c a ≤ 2 * Real.pi
  refine Completion.induction_on₃
    (p := fun a b c : Completion (GeodesicDirections p) =>
      dist a b + dist b c + dist c a ≤ 2 * Real.pi) a b c ?_ ?_
  · exact isClosed_le
      (((continuous_fst.dist continuous_snd.fst).add
        (continuous_snd.fst.dist continuous_snd.snd)).add
        (continuous_snd.snd.dist continuous_fst)) continuous_const
  · intro a b c
    obtain ⟨σ, rfl⟩ := SeparationQuotient.surjective_mk a
    obtain ⟨τ, rfl⟩ := SeparationQuotient.surjective_mk b
    obtain ⟨υ, rfl⟩ := SeparationQuotient.surjective_mk c
    have h := germComparisonAngle_sum_le_two_pi_of_local_fourPointComparison
      (ι := GeodesicRepresentative p) hκ
      (L := fun σ => σ.length) (fun σ => σ.length_pos) hΩ hcomp hp
      (γ := fun σ => σ.path)
      (fun σ _ hs => σ.dist_base_path ⟨hs.1.le, hs.2⟩)
      (fun σ _ hs _ ht => σ.dist_path ⟨hs.1.le, hs.2⟩ ⟨ht.1.le, ht.2⟩) σ τ υ
    change dist σ.direction τ.direction + dist τ.direction υ.direction +
      dist υ.direction σ.direction ≤ 2 * Real.pi
    simpa only [heq] using h

end Metric.SpaceOfDirections
