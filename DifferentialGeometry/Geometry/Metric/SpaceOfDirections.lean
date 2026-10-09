import DifferentialGeometry.Geometry.Comparison.GeodesicAngle
import Mathlib.Topology.MetricSpace.Completion

set_option autoImplicit false

open Set Filter Topology Metric UniformSpace

namespace Metric

variable {X : Type*} [MetricSpace X]

def GeodesicDirections (p : X) [HasAnglesAt p] := SeparationQuotient (GeodesicRepresentative p)

noncomputable instance {p : X} [HasAnglesAt p] : MetricSpace (GeodesicDirections p) :=
  inferInstanceAs (MetricSpace (SeparationQuotient (GeodesicRepresentative p)))

def SpaceOfDirections (p : X) [HasAnglesAt p] := Completion (GeodesicDirections p)

noncomputable instance {p : X} [HasAnglesAt p] : MetricSpace (SpaceOfDirections p) :=
  inferInstanceAs (MetricSpace (Completion (GeodesicDirections p)))

instance {p : X} [HasAnglesAt p] : CompleteSpace (SpaceOfDirections p) :=
  inferInstanceAs (CompleteSpace (Completion (GeodesicDirections p)))

variable {p : X} [HasAnglesAt p]

noncomputable def GeodesicRepresentative.geodesicDirection (σ : GeodesicRepresentative p) :
    GeodesicDirections p := SeparationQuotient.mk σ

noncomputable def GeodesicDirections.toDirection (v : GeodesicDirections p) : SpaceOfDirections p :=
  (v : Completion (GeodesicDirections p))

noncomputable def GeodesicRepresentative.direction (σ : GeodesicRepresentative p) : SpaceOfDirections p :=
  σ.geodesicDirection.toDirection

theorem GeodesicRepresentative.dist_geodesicDirection (σ τ : GeodesicRepresentative p) :
    dist σ.geodesicDirection τ.geodesicDirection = σ.angle τ :=
  SeparationQuotient.dist_mk σ τ

theorem GeodesicRepresentative.geodesicDirection_eq_iff (σ τ : GeodesicRepresentative p) :
    σ.geodesicDirection = τ.geodesicDirection ↔ σ.angle τ = 0 := by
  exact SeparationQuotient.mk_eq_mk.trans Metric.inseparable_iff

theorem GeodesicDirections.isometry_toDirection :
    Isometry (toDirection : GeodesicDirections p → SpaceOfDirections p) :=
  Completion.coe_isometry

theorem GeodesicRepresentative.dist_direction (σ τ : GeodesicRepresentative p) :
    dist σ.direction τ.direction = σ.angle τ := by
  exact (GeodesicDirections.isometry_toDirection.dist_eq _ _).trans
    (σ.dist_geodesicDirection τ)

theorem GeodesicRepresentative.direction_eq_iff (σ τ : GeodesicRepresentative p) :
    σ.direction = τ.direction ↔ σ.angle τ = 0 := by
  rw [← dist_eq_zero, σ.dist_direction τ]

theorem GeodesicRepresentative.direction_shorten (σ : GeodesicRepresentative p) {r : ℝ}
    (hr : 0 < r) (hle : r ≤ σ.length) : (σ.shorten hr hle).direction = σ.direction := by
  rw [direction_eq_iff, σ.angle_shorten_left σ hr hle, σ.angle_self]

theorem SpaceOfDirections.exists_representative_dist_lt (v : SpaceOfDirections p)
    {ε : ℝ} (hε : 0 < ε) : ∃ σ : GeodesicRepresentative p, dist v σ.direction < ε := by
  obtain ⟨q, hq⟩ := Completion.denseRange_coe.exists_dist_lt
    (show Completion (GeodesicDirections p) from v) hε
  obtain ⟨σ, rfl⟩ := SeparationQuotient.surjective_mk q
  exact ⟨σ, hq⟩

theorem SpaceOfDirections.dist_le_pi (v w : SpaceOfDirections p) : dist v w ≤ Real.pi := by
  change dist (show Completion (GeodesicDirections p) from v) w ≤ Real.pi
  refine Completion.induction_on₂ (p := fun a b : Completion (GeodesicDirections p) =>
    dist a b ≤ Real.pi) v w ?_ ?_
  · exact isClosed_le continuous_dist continuous_const
  · intro a b
    obtain ⟨σ, rfl⟩ := SeparationQuotient.surjective_mk a
    obtain ⟨τ, rfl⟩ := SeparationQuotient.surjective_mk b
    exact (σ.dist_direction τ).le.trans (σ.angle_mem_Icc τ).2

theorem GeodesicRepresentative.tendsto_comparisonAngle_dist_direction
    (σ τ : GeodesicRepresentative p) :
    Tendsto (fun z : ℝ × ℝ =>
      DifferentialGeometry.Geometry.Comparison.Toponogov.comparisonAngleNegCurvature
        0 z.1 z.2 (dist (σ.path z.1) (τ.path z.2)))
      (𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ)) (𝓝 (dist σ.direction τ.direction)) := by
  rw [σ.dist_direction τ]
  exact HasAnglesAt.tendsto_angle σ τ

instance [IsEmpty (GeodesicRepresentative p)] : IsEmpty (GeodesicDirections p) := by
  refine ⟨fun v => ?_⟩
  obtain ⟨σ, _⟩ := SeparationQuotient.surjective_mk v
  exact isEmptyElim σ

instance [IsEmpty (GeodesicRepresentative p)] : IsEmpty (SpaceOfDirections p) := by
  refine ⟨fun v => ?_⟩
  obtain ⟨σ, _⟩ := v.exists_representative_dist_lt (show (0 : ℝ) < 1 by norm_num)
  exact isEmptyElim σ

end Metric
