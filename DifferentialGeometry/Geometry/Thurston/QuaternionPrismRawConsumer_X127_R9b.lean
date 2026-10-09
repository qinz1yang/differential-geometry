import DifferentialGeometry.Geometry.Thurston.QuaternionPrismConjugateRaw_X127_R2b

/-!
Consumer of the generalized quaternion (prism) Raw package `_X127_R*b`: the first two noncyclic
members (`n = 2`: the quaternion group of order 8, `n = 3`: the dicyclic group of order 12) get
a concrete `RawGraphPresentation` with one component and no pairing, built from the actual
circle fibration over the real projective plane, and a conjugate copy is again Raw.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Geometry GC.GraphManifold
open GC.Geometry.QuaternionPrismX127R3
open GC.Geometry.QuaternionPrismCircleBundleRawX127
open GC.Geometry.QuaternionPrismRawRecognitionX127
open GC.Geometry.QuaternionPrismConjugateRawX127
open GC.Geometry.QuaternionPrismSpaceFormFaithfulX127
open scoped Manifold ContDiff

universe u

namespace GC.Geometry.QuaternionPrismRawConsumerX127

theorem order_eight_raw_X127 :
    Nat.card (spaceForm_X127 2).group = 8 ∧
      (∃ a b : (spaceForm_X127 2).group, a * b ≠ b * a) ∧
      Nonempty (RawGraphPresentation (NoCuts.carrier
        ((spaceForm_X127 2).manifold.ulift.{0, u}))) :=
  noncyclic_prismRaw_X127 2 le_rfl

theorem order_twelve_raw_X127 :
    Nat.card (spaceForm_X127 3).group = 12 ∧
      (∃ a b : (spaceForm_X127 3).group, a * b ≠ b * a) ∧
      Nonempty (RawGraphPresentation (NoCuts.carrier
        ((spaceForm_X127 3).manifold.ulift.{0, u}))) :=
  noncyclic_prismRaw_X127 3 (by norm_num)

theorem prismRaw_one_component_X127 (n : ℕ) [NeZero n] :
    (prismHopfRawPresentation_X127 n).components.count = 1 :=
  RawGraphPresentation.ofClosedCircleFibration_components_count
    (spaceForm_X127 n).manifold (prismHopfCircleFibration_X127 n)

theorem prismRaw_no_pairing_X127 (n : ℕ) [NeZero n] :
    (prismHopfRawPresentation_X127 n).pairing.count = 0 :=
  RawGraphPresentation.ofClosedCircleFibration_pairing_count
    (spaceForm_X127 n).manifold (prismHopfCircleFibration_X127 n)

theorem prismProjectedHopf_proper_submersion_X127 (n : ℕ) [NeZero n]
    (x : (spaceForm_X127 n).Orbit) :
    IsProperMap (prismProjectedHopf_X127 n) ∧
      Function.Surjective (mfderiv (𝓡 3) (𝓡 2) (prismProjectedHopf_X127 n) x) :=
  ⟨prismProjectedHopf_isProper_X127 n, prismProjectedHopf_mfderiv_surjective_X127 n x⟩

theorem prismRaw_identity_conjugate_X127 (n : ℕ) [NeZero n] :
    Nonempty (RawGraphPresentation (NoCuts.carrier
      (conjSphericalSpaceFormGroup (spaceForm_X127 n)
        (LinearIsometryEquiv.refl ℝ (EuclideanSpace ℝ (Fin 4)))).manifold.ulift.{0, u})) :=
  nonempty_rawGraphPresentation_conjugatePrism_X127 n _

end GC.Geometry.QuaternionPrismRawConsumerX127
