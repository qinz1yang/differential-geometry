import DifferentialGeometry.Geometry.Comparison.Busemann.Ray.Busemann
import Mathlib.Topology.UniformSpace.Dini
import Mathlib.Tactic.Linarith

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology

namespace DifferentialGeometry.Geometry.Metric

variable {M : Type*} [PseudoMetricSpace M] {gamma : ℝ → M}

theorem busemannFunction_tendstoUniformlyOn (hgamma : Isometry gamma)
    {K : Set M} (hK : IsCompact K) :
    TendstoUniformlyOn (fun t : ℝ ↦ fun x : M ↦ dist x (gamma t) - t)
      (busemannFunction gamma) atTop K := by
  apply Antitone.tendstoUniformlyOn_of_forall_tendsto hK
  · intro t
    exact ((continuous_id.dist continuous_const).sub continuous_const).continuousOn
  · intro x _ s t hst
    have htriangle := dist_triangle x (gamma s) (gamma t)
    rw [hgamma.dist_eq, Real.dist_eq,
      abs_of_nonpos (sub_nonpos.mpr hst)] at htriangle
    linarith
  · exact (busemannFunction_lipschitz hgamma).continuous.continuousOn
  · intro x _
    exact busemannFunction_tendsto hgamma x

end DifferentialGeometry.Geometry.Metric
end
