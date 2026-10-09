import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.CompactPatchEvent

set_option autoImplicit false

/-!
# CP1-D6 (2): transport of backward survivor domains between two histories related by a
value-preserving index embedding (`SamePresentation` casts and `restrict` embeddings).
-/

noncomputable section
open Set Manifold DifferentialGeometry DifferentialGeometry.Topology GC.Topology
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.Surgery GC.LongTime
open scoped Manifold ContDiff

namespace GC.LongTime.CuspP1

universe u

/-- The index embedding `j ↦ j` of `Fin (H.eventCount + 1)` into `Fin (K.eventCount + 1)`. -/
def embIdx_CPD6 {H K : ObservedHistory.{u}} (hHK : H.eventCount ≤ K.eventCount)
    (j : Fin (H.eventCount + 1)) : Fin (K.eventCount + 1) :=
  Fin.castLE (Nat.succ_le_succ hHK) j

theorem embIdx_le_CPD6 {H K : ObservedHistory.{u}} (hHK : H.eventCount ≤ K.eventCount)
    {a b : Fin (H.eventCount + 1)} (h : a ≤ b) : embIdx_CPD6 hHK a ≤ embIdx_CPD6 hHK b := by
  rw [Fin.le_iff_val_le_val] at h ⊢
  exact h

/-- Data: `H` embeds into `K` along equal stages and transported regular crossings. -/
structure HistEmb_CPD6 (H K : ObservedHistory.{u}) : Type _ where
  le : H.eventCount ≤ K.eventCount
  stage_eq : ∀ j : Fin (H.eventCount + 1), H.stage j = K.stage (embIdx_CPD6 le j)
  crossing : ∀ (i : Fin H.eventCount) (p : (H.stage i.castSucc).Carrier)
    (q : (H.stage i.succ).Carrier), (H.event i).RegularCrossing p q →
    (K.event (Fin.castLE le i)).RegularCrossing
      (carrierHomeo_CPD2 (stage_eq i.castSucc) p) (carrierHomeo_CPD2 (stage_eq i.succ) q)
  time_eq : ∀ j : Fin (H.eventCount + 1), H.time j = K.time (embIdx_CPD6 le j)
  horizon_le : H.horizon ≤ K.horizon
  beyond : ∀ k : Fin (K.eventCount + 1), H.eventCount < k.val → H.horizon < K.time k

namespace HistEmb_CPD6

variable {H K : ObservedHistory.{u}} (E : HistEmb_CPD6 H K)

/-- carrier identification at stage `j` -/
def cst (j : Fin (H.eventCount + 1)) :
    (H.stage j).Carrier ≃ₜ (K.stage (embIdx_CPD6 E.le j)).Carrier :=
  carrierHomeo_CPD2 (E.stage_eq j)

/-- preimage index of `j'` below the image of `last` -/
def preIdx {last : Fin (H.eventCount + 1)} (j' : Fin (K.eventCount + 1))
    (hl : j' ≤ embIdx_CPD6 E.le last) : Fin (H.eventCount + 1) :=
  ⟨j'.val, lt_of_le_of_lt (Fin.le_iff_val_le_val.mp hl) last.isLt⟩

/-- the transported backward trace -/
def traceMap {first last : Fin (H.eventCount + 1)} {hle : first ≤ last}
    {x : (H.stage last).Carrier} (A : BackwardPointTrace H first last hle x) :
    BackwardPointTrace K (embIdx_CPD6 E.le first) (embIdx_CPD6 E.le last)
      (embIdx_le_CPD6 E.le hle) (E.cst last x) where
  point j' hf hl :=
    E.cst (E.preIdx j' hl)
      (A.point (E.preIdx j' hl) (by
        have := Fin.le_iff_val_le_val.mp hf
        exact Fin.le_iff_val_le_val.mpr this) (by
        exact Fin.le_iff_val_le_val.mpr (Fin.le_iff_val_le_val.mp hl)))
  endpoint_eq := by
    exact congrArg (E.cst last) A.endpoint_eq
  crossing i' hf hl := by
    exact E.crossing ⟨i'.val, by
        have := Fin.le_iff_val_le_val.mp hl
        have h2 := last.isLt
        simp only [Fin.val_succ, embIdx_CPD6, Fin.val_castLE] at this
        omega⟩ _ _ (A.crossing _ _ _)

/-- the induced continuous map of survivor domains -/
def domMap (first last : Fin (H.eventCount + 1)) (hle : first ≤ last) :
    C(H.backwardSurvivorDomain first last hle,
      K.backwardSurvivorDomain (embIdx_CPD6 E.le first) (embIdx_CPD6 E.le last)
        (embIdx_le_CPD6 E.le hle)) :=
  ⟨fun z => ⟨E.cst last z.val, ⟨E.traceMap (Classical.choice z.property)⟩⟩,
    Continuous.subtype_mk ((E.cst last).continuous.comp continuous_subtype_val) _⟩

theorem domMap_val (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    (z : H.backwardSurvivorDomain first last hle) :
    (E.domMap first last hle z).val = E.cst last z.val := rfl

/-- survivor maps commute with the transport -/
theorem survivorMap_domMap (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    (j : Fin (H.eventCount + 1)) (hj : first ≤ j) (hl : j ≤ last)
    (z : H.backwardSurvivorDomain first last hle) :
    K.backwardSurvivorMap (embIdx_CPD6 E.le first) (embIdx_CPD6 E.le last)
      (embIdx_le_CPD6 E.le hle) (embIdx_CPD6 E.le j) (embIdx_le_CPD6 E.le hj)
      (embIdx_le_CPD6 E.le hl) (E.domMap first last hle z) =
    E.cst j (H.backwardSurvivorMap first last hle j hj hl z) := by
  rw [K.backwardSurvivorMap_eq_point _ _ _ _ _ _ _ (E.traceMap (Classical.choice z.property)),
    H.backwardSurvivorMap_eq_point _ _ _ _ _ _ _ (Classical.choice z.property)]
  rfl

end HistEmb_CPD6

end GC.LongTime.CuspP1
