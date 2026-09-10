import DifferentialGeometry.Topology.Morse.Defs
import DifferentialGeometry.Topology.Attachment.Union
import DifferentialGeometry.Topology.Homotopy.EquivUnder

set_option autoImplicit false
noncomputable section
open Set
open DifferentialGeometry.Topology DifferentialGeometry.Topology.Morse
open DifferentialGeometry.Topology.Homotopy
namespace DifferentialGeometry.Morse
variable {M : Type} [TopologicalSpace M]


def sublevelRestrictionHomeomorph (s : Set M) (f : M → ℝ) (a : ℝ)
    (hs : sublevel f a ⊆ s) :
    SublevelSpace (fun x : s => f x) a ≃ₜ SublevelSpace f a where
  toFun x := ⟨x.1.1, x.2⟩
  invFun x := ⟨⟨x.1, hs x.2⟩, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _


@[simp]
theorem sublevelRestrictionHomeomorph_apply (s : Set M) (f : M → ℝ) (a : ℝ)
    (hs : sublevel f a ⊆ s) (x : SublevelSpace (fun x : s => f x) a) :
    (sublevelRestrictionHomeomorph s f a hs x : M) = (x.1 : M) := rfl


@[simp]
theorem sublevelRestrictionHomeomorph_symm_apply (s : Set M) (f : M → ℝ) (a : ℝ)
    (hs : sublevel f a ⊆ s) (x : SublevelSpace f a) :
    (((sublevelRestrictionHomeomorph s f a hs).symm x).1 : M) = x.1 := rfl


theorem sublevelRestrictionHomeomorph_inclusion (s : Set M) (f : M → ℝ) {a b : ℝ}
    (hab : a ≤ b) (ha : sublevel f a ⊆ s) (hb : sublevel f b ⊆ s)
    (x : SublevelSpace (fun x : s => f x) a) :
    sublevelRestrictionHomeomorph s f b hb (sublevelInclusion (fun x : s => f x) hab x) =
      sublevelInclusion f hab (sublevelRestrictionHomeomorph s f a ha x) := rfl


def cellAttachmentUnderSublevelRestriction (s : Set M) (f : M → ℝ) {a b : ℝ}
    (hab : a ≤ b) (ha : sublevel f a ⊆ s) (hb : sublevel f b ⊆ s) {k : ℕ}
    (φ : C(CellBoundary k, SublevelSpace (fun x : s => f x) a))
    (h : HomotopyEquivUnder (sublevelInclusion (fun x : s => f x) hab)
      (ContinuousMap.mk (adjunctionLower (i := cellBoundaryInclusion k) φ)
        (continuous_adjunctionLower (i := cellBoundaryInclusion k) φ))) :
    HomotopyEquivUnder (sublevelInclusion f hab)
      (ContinuousMap.mk
        (adjunctionLower (i := cellBoundaryInclusion k)
          ((sublevelRestrictionHomeomorph s f a ha) ∘ φ))
        (continuous_adjunctionLower (i := cellBoundaryInclusion k) _)) := by
  let ea := sublevelRestrictionHomeomorph s f a ha
  let eb := sublevelRestrictionHomeomorph s f b hb
  let ia : C(SublevelSpace f a, SublevelSpace (fun x : s => f x) a) :=
    ⟨ea.symm, ea.symm.continuous_toFun⟩
  let j := (sublevelInclusion (fun x : s => f x) hab).comp ia
  let lower : C(SublevelSpace (fun x : s => f x) a, CellAdjunctionSpace k φ) :=
    ⟨adjunctionLower (i := cellBoundaryInclusion k) φ, continuous_adjunctionLower _ _⟩
  let newLower : C(SublevelSpace f a, CellAdjunctionSpace k (ea ∘ φ)) :=
    ⟨adjunctionLower (i := cellBoundaryInclusion k) (ea ∘ φ), continuous_adjunctionLower _ _⟩
  let hup := HomotopyEquivUnder.ofHomeomorph (sublevelInclusion f hab) j eb.symm
    (by ext x; rfl)
  let hp := HomotopyEquivUnder.precomp h ia
  let eadj := (adjunctionHomeoOfLowerEquiv (cellBoundaryInclusion k) φ ea).symm
  have he : (⟨eadj, eadj.continuous_toFun⟩ : C(CellAdjunctionSpace k φ,
      CellAdjunctionSpace k (ea ∘ φ))).comp (lower.comp ia) = newLower := by
    ext x
    change adjunctionLower (i := cellBoundaryInclusion k) (ea ∘ φ) (ea (ea.symm x)) = _
    rw [ea.apply_symm_apply]
    rfl
  let hlow := HomotopyEquivUnder.ofHomeomorph (lower.comp ia) newLower eadj he
  exact (hup.trans hp rfl).trans hlow rfl
end DifferentialGeometry.Morse
