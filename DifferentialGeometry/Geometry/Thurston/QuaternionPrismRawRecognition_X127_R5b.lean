import DifferentialGeometry.Geometry.Thurston.QuaternionPrismCircleBundleRaw_X127_R9b
import DifferentialGeometry.Geometry.Thurston.QuaternionPrismSpaceFormFaithful_X127_R4b

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Geometry GC.GraphManifold
universe u

namespace GC.Geometry.QuaternionPrismRawRecognitionX127

open GC.Geometry.QuaternionPrismX127R3
open GC.Geometry.QuaternionPrismCircleBundleRawX127
open GC.Geometry.QuaternionPrismSpaceFormFaithfulX127

theorem noncyclic_prismRaw_X127 (n : ℕ) [NeZero n] (hn : 2 ≤ n) :
    Nat.card (spaceForm_X127 n).group = 4 * n ∧
      (∃ a b : (spaceForm_X127 n).group, a * b ≠ b * a) ∧
      Nonempty (RawGraphPresentation (NoCuts.carrier
        ((spaceForm_X127 n).manifold.ulift.{0, u}))) := by
  exact ⟨prismSpaceFormGroup_card_X127 n,
    prismSpaceForm_noncommutative_X127 n hn,
    prismHopfRawPresentation_ulift_X127 n⟩

end GC.Geometry.QuaternionPrismRawRecognitionX127
