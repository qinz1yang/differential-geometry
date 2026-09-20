import Mathlib.Analysis.SpecialFunctions.PolarCoord

open MeasureTheory Set Filter

namespace DifferentialGeometry.Topology

theorem ae_mem_complex_slitPlane : ∀ᵐ z : ℂ ∂volume, z ∈ Complex.slitPlane := by
  have hslit :=
    Complex.volume_preserving_equiv_real_prod.quasiMeasurePreserving.preimage_ae_eq
      polarCoord_source_ae_eq_univ
  filter_upwards [hslit] with z hz
  have hm := hz.mpr (mem_univ z)
  change 0 < z.re ∨ z.im ≠ 0 at hm
  exact hm

end DifferentialGeometry.Topology
