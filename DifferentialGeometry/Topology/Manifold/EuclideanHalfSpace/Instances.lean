import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Topology.Compactness.SigmaCompact

set_option autoImplicit false

namespace EuclideanHalfSpace

theorem t2Space (n : ℕ) [NeZero n] : T2Space (EuclideanHalfSpace n) := by
  unfold EuclideanHalfSpace
  infer_instance

theorem sigmaCompactSpace (n : ℕ) [NeZero n] : SigmaCompactSpace (EuclideanHalfSpace n) :=
  IsClosed.sigmaCompactSpace
    (isClosed_Ici.preimage (EuclideanSpace.proj (𝕜 := ℝ) 0).continuous)

theorem secondCountableTopology (n : ℕ) [NeZero n] :
    SecondCountableTopology (EuclideanHalfSpace n) := by
  unfold EuclideanHalfSpace
  infer_instance

attribute [instance] t2Space sigmaCompactSpace secondCountableTopology

end EuclideanHalfSpace
