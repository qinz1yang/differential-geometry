import DifferentialGeometry.Geometry.Boundary.Manifold.CollaredGluing
import DifferentialGeometry.Topology.Double.Basic
import DifferentialGeometry.Topology.Double.SeamPatch
import Mathlib.Logic.Relation

open Set Function Topology Relation
open scoped Manifold ContDiff

noncomputable section
set_option autoImplicit false

namespace DifferentialGeometry.Topology

section

variable {X : Type*}

private def subtypeSelfRel (B : Set X) (u v : X ⊕ X) : Prop :=
  u = v ∨ (∃ b : B, u = Sum.inl (b : X) ∧ v = Sum.inr (b : X)) ∨
    (∃ b : B, v = Sum.inl (b : X) ∧ u = Sum.inr (b : X))

private theorem subtypeSelfRel_symm {B : Set X} {u v : X ⊕ X}
    (h : subtypeSelfRel B u v) : subtypeSelfRel B v u := by
  rcases h with h | ⟨b, h1, h2⟩ | ⟨b, h1, h2⟩
  · exact Or.inl h.symm
  · exact Or.inr (Or.inr ⟨b, h1, h2⟩)
  · exact Or.inr (Or.inl ⟨b, h1, h2⟩)

private theorem subtypeSelfRel_trans {B : Set X} {u v w : X ⊕ X}
    (h1 : subtypeSelfRel B u v) (h2 : subtypeSelfRel B v w) : subtypeSelfRel B u w := by
  rcases h1 with h | ⟨b, hbu, hvb⟩ | ⟨b, hbv, hub⟩
  · subst h; exact h2
  · rcases h2 with h | ⟨c, hvc, hwc⟩ | ⟨c, hwc, hvc⟩
    · exact Or.inr (Or.inl ⟨b, hbu, h ▸ hvb⟩)
    · exact absurd (hvb.symm.trans hvc) (by simp)
    · have hbc : (b : X) = (c : X) := Sum.inr.inj (hvb.symm.trans hvc)
      exact Or.inl (hbu.trans ((congrArg Sum.inl hbc).trans hwc.symm))
  · rcases h2 with h | ⟨c, hvc, hwc⟩ | ⟨c, hwc, hvc⟩
    · exact Or.inr (Or.inr ⟨b, h ▸ hbv, hub⟩)
    · have hbc : (b : X) = (c : X) := Sum.inl.inj (hbv.symm.trans hvc)
      exact Or.inl (hub.trans ((congrArg Sum.inr hbc).trans hwc.symm))
    · exact absurd (hbv.symm.trans hvc) (by simp)

private theorem subtypeSelfRel_of_adjunctionRel {B : Set X} {u v : X ⊕ X}
    (h : adjunctionRel (Subtype.val : B → X) (Subtype.val : B → X) u v) :
    subtypeSelfRel B u v := by
  obtain ⟨c, h | h⟩ := h
  · exact Or.inr (Or.inl ⟨c, h.1, h.2⟩)
  · exact Or.inr (Or.inr ⟨c, h.1, h.2⟩)

theorem eqvGen_adjunctionRel_subtypeVal_self_iff (B : Set X) (u v : X ⊕ X) :
    EqvGen (adjunctionRel (Subtype.val : B → X) (Subtype.val : B → X)) u v ↔
      (u = v ∨ (∃ b : B, u = Sum.inl (b : X) ∧ v = Sum.inr (b : X)) ∨
        (∃ b : B, v = Sum.inl (b : X) ∧ u = Sum.inr (b : X))) := by
  change EqvGen (adjunctionRel (Subtype.val : B → X) (Subtype.val : B → X)) u v ↔
    subtypeSelfRel B u v
  constructor
  · intro h
    induction h with
    | rel a b hab => exact subtypeSelfRel_of_adjunctionRel hab
    | refl a => exact Or.inl rfl
    | symm a b _ ih => exact subtypeSelfRel_symm ih
    | trans a b c _ _ ih1 ih2 => exact subtypeSelfRel_trans ih1 ih2
  · rintro (rfl | ⟨b, h1, h2⟩ | ⟨b, h1, h2⟩)
    · exact EqvGen.refl u
    · rw [h1, h2]
      exact EqvGen.rel _ _ ⟨b, Or.inl ⟨rfl, rfl⟩⟩
    · rw [h1, h2]
      exact EqvGen.symm _ _ (EqvGen.rel _ _ ⟨b, Or.inl ⟨rfl, rfl⟩⟩)

end

variable {X : Type*} [TopologicalSpace X]

theorem doublePositive_eq_doubleNegative_iff (B : Set X) (x y : X) :
    doublePositive B x = doubleNegative B y ↔ x = y ∧ x ∈ B := by
  have hfn : ∀ z : X, doublePositive B z = Quot.mk
      (adjunctionRel (Subtype.val : B → X) (Subtype.val : B → X)) (Sum.inl z) := fun _ => rfl
  have hfn' : ∀ z : X, doubleNegative B z = Quot.mk
      (adjunctionRel (Subtype.val : B → X) (Subtype.val : B → X)) (Sum.inr z) := fun _ => rfl
  rw [hfn x, hfn' y, Quot.eq, eqvGen_adjunctionRel_subtypeVal_self_iff]
  constructor
  · rintro (h | ⟨b, h1, h2⟩ | ⟨b, h1, h2⟩)
    · exact absurd h (by simp)
    · exact ⟨Sum.inl.inj h1 |>.trans (Sum.inr.inj h2).symm, (Sum.inl.inj h1) ▸ b.2⟩
    · exact absurd h1 (by simp)
  · rintro ⟨rfl, hx⟩
    exact Or.inr (Or.inl ⟨⟨x, hx⟩, rfl, rfl⟩)

theorem doublePositive_eq_doubleNegative_singleton_zero :
    doublePositive ({0} : Set ℝ) 0 = doubleNegative ({0} : Set ℝ) 0 :=
  (doublePositive_eq_doubleNegative_iff _ _ _).mpr ⟨rfl, rfl⟩

theorem doublePositive_ne_doubleNegative_singleton_one :
    doublePositive ({0} : Set ℝ) 0 ≠ doubleNegative ({0} : Set ℝ) 1 := by
  intro h
  have h01 : (0 : ℝ) = 1 := ((doublePositive_eq_doubleNegative_iff _ _ _).mp h).1
  norm_num at h01

section SeamPatch

variable [CompactSpace X] [T2Space X]
  (B : Set X) (r : C(X, ℝ)) (hr : ∀ b : B, r b.val = 0)
  (hz : ∀ x, r x = 0 → x ∈ B) (hn : ∀ x, 0 ≤ r x)
  {a : ℝ} (c : C(B × Icc (0 : ℝ) a, X))
  (hheight : ∀ q, r (c q) = q.2.val)
  (hsmall : ∀ x, r x ≤ a → x ∈ range c) (hc : IsEmbedding c)

theorem doubleSeamPatch_apply_eq (ha : 0 < a) (b b' : B) {q : B × ℝ}
    (hq : |q.2| < a) :
    doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b q =
      doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b' q := by
  rw [doubleSeamPatch_apply B r hr hz hn c hheight hsmall hc ha b hq,
    doubleSeamPatch_apply B r hr hz hn c hheight hsmall hc ha b' hq]

end SeamPatch

end DifferentialGeometry.Topology

namespace DifferentialGeometry.Geometry.Boundary

universe u v

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {X : Type u} [TopologicalSpace X] [ChartedSpace H X]
variable {ι : Type v} [Finite ι]

namespace CollaredGluing

theorem rel_collarRight_attaching [IsManifold I 1 X] (G : CollaredGluing I X ι) (i : ι)
    (z : ↥(G.left i).carrier) :
    (G.toBoundaryGluing).rel
      (G.collarRight i (G.attaching i z, ⟨0, le_rfl, (G.ε_pos i).le⟩))
      (G.collarLeft i (z, ⟨0, le_rfl, (G.ε_pos i).le⟩)) := by
  rw [G.collarRight_zero i (G.attaching i z), G.collarLeft_zero i z]
  exact Topology.BoundaryGluing.rel_of_attaching G.toBoundaryGluing i z

end CollaredGluing

section UnitInterval

theorem unitIntervalCollaredGluing_exists_rel_collarRight_attaching (i : Fin 1) :
    ∃ z : ↥(unitIntervalCollaredGluing.left i).carrier,
      (unitIntervalCollaredGluing.toBoundaryGluing).rel
        (unitIntervalCollaredGluing.collarRight i
          (unitIntervalCollaredGluing.attaching i z,
            ⟨0, le_rfl, (unitIntervalCollaredGluing.ε_pos i).le⟩))
        (unitIntervalCollaredGluing.collarLeft i
          (z, ⟨0, le_rfl, (unitIntervalCollaredGluing.ε_pos i).le⟩)) := by
  obtain ⟨z, hz⟩ := BoundaryComponent.carrier_nonempty (unitIntervalCollaredGluing.left i)
  exact ⟨⟨z, hz⟩, CollaredGluing.rel_collarRight_attaching unitIntervalCollaredGluing i _⟩

end UnitInterval

end DifferentialGeometry.Geometry.Boundary
