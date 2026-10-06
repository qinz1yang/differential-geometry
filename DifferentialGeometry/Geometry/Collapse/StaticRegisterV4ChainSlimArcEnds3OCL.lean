import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainSlimArcEnds2OCL

/-!
# Draft 74, S0 on the member: `ArcEnds74` with a property of every end (kind included)

Lane C14-REG-CHAIN (by S-REG-CHAIN6), G4 (kernel part, suffix `_OCL`). The strengthening of
`ArcEnds74.exists_of_ends2_OCL` (G1, untouched) in which the property `Q b k fn` is demanded and
delivered for EVERY end `b` together with its classification `k` and end function `fn` (so it can
speak about `kind`, e.g. `kind b = none ↔ the end value is not a slim face point`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0

open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open GC.GraphManifold.Assembly

variable {W : CompactCarrier.{0}} {n : ℕ} {E : BoundaryTori W n} {Z : ZeroDomains W}
  {Cu : CuspCores W E}

/-- **`ArcEnds74` from end-by-end data, with a property of the classification and the end
function of every end**: the produced record satisfies `Q b (ends.kind b) (ends.fn b)` for all
ends `b`. -/
theorem ArcEnds74.exists_of_ends3_OCL {pieceSet : Set W.Carrier}
    {slice : Bool → Set W.Carrier}
    (Q : Bool → Option (NeighbourFace Z Cu) → (W.Carrier → ℝ) → Prop)
    (h : ∀ b : Bool, ∃ (k : Option (NeighbourFace Z Cu)) (fn : W.Carrier → ℝ)
        (near : TopologicalSpace.Opens W.Carrier),
      (∀ F, k = some F → slice b = neighbourSet F) ∧
      (k = none → (near : Set W.Carrier) ⊆ W.interior) ∧
      (k = none → ContMDiffOn W.model 𝓘(ℝ, ℝ) ∞ fn near) ∧
      (k = none → ∀ x ∈ near, fn x = 0 → mfderiv W.model 𝓘(ℝ, ℝ) fn x ≠ 0) ∧
      (k = none → slice b = {x | x ∈ near ∧ fn x = 0}) ∧
      (k = none → pieceSet ∩ near = {x | x ∈ near ∧ fn x ≤ 0}) ∧
      Q b k fn) :
    ∃ ends : ArcEnds74 Z Cu pieceSet slice, ∀ b, Q b (ends.kind b) (ends.fn b) := by
  choose k fn near h1 h2 h3 h4 h5 h6 h7 using h
  exact ⟨{
    kind := k
    fn := fn
    near := near
    shared_eq := fun b F hk => h1 b F hk
    near_interior := fun b hk => h2 b hk
    fn_smooth := fun b hk => h3 b hk
    fn_regular := fun b hk => h4 b hk
    fn_level := fun b hk => h5 b hk
    fn_eq := fun b hk => h6 b hk }, fun b => h7 b⟩

end GC.GraphManifold.Assembly.FC39P0
