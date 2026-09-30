import DifferentialGeometry.Geometry.Metric.TangentCone
import DifferentialGeometry.Geometry.Metric.EuclideanConeProper

set_option autoImplicit false

noncomputable section

open Set Metric
open scoped NNReal

namespace Metric.TangentCone

theorem dense_representative_vectors {X : Type*} [MetricSpace X] {q : X} [HasAnglesAt q] :
    Dense ({EuclideanCone.tip} ∪ Set.range
      (fun z : ℝ≥0 × GeodesicRepresentative q => z.2.tangentVector z.1) :
        Set (TangentCone q)) := by
  have hd : DenseRange (GeodesicRepresentative.direction :
      GeodesicRepresentative q → SpaceOfDirections q) :=
    Metric.denseRange_iff.mpr fun u _ hε => u.exists_representative_dist_lt hε
  intro x
  rcases EuclideanCone.eq_tip_or_eq_mk x with rfl | ⟨r, u, _, rfl⟩
  · exact subset_closure (Or.inl (mem_singleton _))
  · have hf : Continuous (fun v : SpaceOfDirections q => EuclideanCone.mk r v) :=
      EuclideanCone.continuous_mk.comp (continuous_const.prodMk continuous_id)
    have hc := hf.continuousWithinAt.mem_closure_image (hd u)
    apply closure_mono (s := (fun v : SpaceOfDirections q => EuclideanCone.mk r v) ''
      Set.range GeodesicRepresentative.direction) ?_ hc
    rintro _ ⟨_, ⟨σ, rfl⟩, rfl⟩
    exact Or.inr ⟨(r, σ), rfl⟩

end Metric.TangentCone
