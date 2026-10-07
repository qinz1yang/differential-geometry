import DifferentialGeometry.Geometry.Hyperbolic.TruncationVolume
import DifferentialGeometry.Geometry.Hyperbolic.TruncationEnds

/-!
# Consumer of the G1 intake (S-HG-INTAKE, suffix `_HGI`)

HG09 neighbour + end count: for a truncation `Tr` of a finite-volume hyperbolic model,
the end count equals `Tr.count` and the volume of the complement of the core is the sum of
the cusp-torus volumes.
-/

set_option autoImplicit false

open Set Manifold GC.Endpoint
open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic

universe u

theorem truncation_endCount_and_complement_volume_HGI
    {H : FiniteVolumeHyperbolicModel.{u}} (Tr : HyperbolicTruncation H) :
    DifferentialGeometry.Geometry.Topology.endCount H.Carrier = (Tr.count : ℕ∞) ∧
      Integral.Measure.riemannianVolumeMeasure (𝓡 3) H.Carrier H.metric (range Tr.inclusion)ᶜ =
        ∑ i, Integral.Measure.riemannianVolumeMeasure torusModel Torus
          (Tr.cusp i).torusMetric univ :=
  ⟨Tr.endCount_eq_count, Tr.volume_compl_range_inclusion⟩
