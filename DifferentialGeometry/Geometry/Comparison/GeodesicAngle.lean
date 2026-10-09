import DifferentialGeometry.Geometry.Metric.GeodesicRepresentative
import DifferentialGeometry.Geometry.Comparison.GermAngleTriangle

set_option autoImplicit false

open Set Filter Topology Metric
open DifferentialGeometry.Geometry.Comparison.Toponogov

namespace Metric

variable {X : Type*} [MetricSpace X] {p : X}

noncomputable def GeodesicRepresentative.angle (σ τ : GeodesicRepresentative p) : ℝ :=
  germComparisonAngle 0 σ.path τ.path

class HasAnglesAt (p : X) : Prop where
  tendsto_angle : ∀ σ τ : GeodesicRepresentative p,
    Tendsto (fun z : ℝ × ℝ => comparisonAngleNegCurvature 0 z.1 z.2
      (dist (σ.path z.1) (τ.path z.2)))
      (𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ)) (𝓝 (σ.angle τ))

theorem hasAnglesAt_of_local_fourPointComparison_zero {Ω : Set X}
    (hΩ : IsOpen Ω) (hcomp : fourPointComparison 0 Ω) (hp : p ∈ Ω) : HasAnglesAt p := by
  refine ⟨fun σ τ => ?_⟩
  exact tendsto_germComparisonAngle_of_local_fourPointComparison (le_refl 0)
    σ.length_pos τ.length_pos hΩ hcomp hp
    (fun _ ht => σ.dist_base_path ⟨ht.1.le, ht.2⟩)
    (fun _ ht => τ.dist_base_path ⟨ht.1.le, ht.2⟩)
    (fun _ hs _ ht => σ.dist_path ⟨hs.1.le, hs.2⟩ ⟨ht.1.le, ht.2⟩)
    (fun _ hs _ ht => τ.dist_path ⟨hs.1.le, hs.2⟩ ⟨ht.1.le, ht.2⟩)

namespace GeodesicRepresentative

theorem angle_mem_Icc (σ τ : GeodesicRepresentative p) :
    σ.angle τ ∈ Icc (0 : ℝ) Real.pi := germComparisonAngle_mem_Icc _ _ _

theorem angle_comm (σ τ : GeodesicRepresentative p) : σ.angle τ = τ.angle σ :=
  germComparisonAngle_comm _ _ _

theorem angle_self (σ : GeodesicRepresentative p) : σ.angle σ = 0 :=
  germComparisonAngle_self (le_refl 0) σ.length_pos
    (fun _ hs _ ht => σ.dist_path ⟨hs.1.le, hs.2⟩ ⟨ht.1.le, ht.2⟩)

theorem angle_shorten_left (σ τ : GeodesicRepresentative p) {r : ℝ}
    (hr : 0 < r) (hle : r ≤ σ.length) : (σ.shorten hr hle).angle τ = σ.angle τ := by
  apply germComparisonAngle_congr_on hr τ.length_pos
  · intro t ht
    exact σ.shorten_path hr hle ⟨ht.1.le, ht.2⟩
  · exact fun _ _ => rfl

theorem angle_triangle [HasAnglesAt p] (σ τ υ : GeodesicRepresentative p) :
    σ.angle υ ≤ σ.angle τ + τ.angle υ :=
  angle_triangle_of_joint_comparisonAngle (le_refl 0) σ.length_pos τ.length_pos υ.length_pos
    p σ.path τ.path υ.path
    (fun _ ht => σ.dist_base_path ⟨ht.1.le, ht.2⟩)
    (fun _ ht => τ.dist_base_path ⟨ht.1.le, ht.2⟩)
    (fun _ ht => υ.dist_base_path ⟨ht.1.le, ht.2⟩)
    (HasAnglesAt.tendsto_angle σ τ) (HasAnglesAt.tendsto_angle τ υ)
    (HasAnglesAt.tendsto_angle σ υ)

noncomputable instance [HasAnglesAt p] : PseudoMetricSpace (GeodesicRepresentative p) where
  dist := angle
  dist_self := angle_self
  dist_comm := angle_comm
  dist_triangle := angle_triangle

end GeodesicRepresentative

end Metric
