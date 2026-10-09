import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.CompactPatchHistory

set_option autoImplicit false

/-!
# CP1-D6 (3): the embeddings `history n ↪ history N` of an observation tower
-/

noncomputable section
open Set Manifold DifferentialGeometry DifferentialGeometry.Topology GC.Topology
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.Surgery GC.LongTime
open scoped Manifold ContDiff

namespace GC.LongTime.CuspP1

universe u

theorem carrierHomeo_trans_CPD6 {A B C : OrientedThreeStage.{u}} (h1 : A = B) (h2 : B = C)
    (a : A.Carrier) :
    carrierHomeo_CPD2 (h1.trans h2) a = carrierHomeo_CPD2 h2 (carrierHomeo_CPD2 h1 a) := by
  subst h1; subst h2; rfl

namespace HistEmb_CPD6

/-- composition of embeddings -/
def trans {H K L : ObservedHistory.{u}} (E1 : HistEmb_CPD6 H K) (E2 : HistEmb_CPD6 K L) :
    HistEmb_CPD6 H L where
  le := E1.le.trans E2.le
  stage_eq j := (E1.stage_eq j).trans (E2.stage_eq (embIdx_CPD6 E1.le j))
  crossing i p q h := by
    have h2 := E2.crossing (Fin.castLE E1.le i) _ _ (E1.crossing i p q h)
    have e1 := carrierHomeo_trans_CPD6 (E1.stage_eq i.castSucc)
      (E2.stage_eq (embIdx_CPD6 E1.le i.castSucc)) p
    have e2 := carrierHomeo_trans_CPD6 (E1.stage_eq i.succ)
      (E2.stage_eq (embIdx_CPD6 E1.le i.succ)) q
    exact Eq.mpr (congrArg₂ (fun a b => (L.event (Fin.castLE (E1.le.trans E2.le) i)).RegularCrossing
      a b) e1 e2) h2
  time_eq j := (E1.time_eq j).trans (E2.time_eq (embIdx_CPD6 E1.le j))
  horizon_le := E1.horizon_le.trans E2.horizon_le
  beyond k hk := by
    by_cases hkk : k.val ≤ K.eventCount
    · have := E1.beyond ⟨k.val, Nat.lt_succ_of_le hkk⟩ hk
      rw [E2.time_eq] at this
      exact this
    · exact E1.horizon_le.trans_lt (E2.beyond k (by omega))

end HistEmb_CPD6

/-- `SamePresentation` gives an embedding -/
def histEmbOfSame_CPD6 {H K : ObservedHistory.{u}} (R : H.SamePresentation K) :
    HistEmb_CPD6 H K where
  le := R.count_eq.le
  stage_eq j := R.stage_eq j
  crossing i p q h := regularCrossing_samePresentation_CPD6 (R.event_eq i) h
  time_eq j := R.time_eq j
  horizon_le := R.horizon_eq.le
  beyond k hk := by
    have := k.isLt
    have h2 := R.count_eq
    omega

/-- the restriction embeds -/
def histEmbRestrict_CPD6 (K : ObservedHistory.{u}) (a : Icc (0 : ℝ) K.horizon) :
    HistEmb_CPD6 (K.restrict a) K where
  le := Nat.le_of_lt_succ (K.activeStage a).isLt
  stage_eq _ := rfl
  crossing _ _ _ h := h
  time_eq _ := rfl
  horizon_le := a.2.2
  beyond k hk := by
    by_contra hcon
    have h1 : K.time k ≤ a.1 := not_lt.mp hcon
    have h2 := K.le_activeStage a k h1
    have h3 : (K.restrict a).eventCount = (K.activeStage a).val := rfl
    rw [Fin.le_iff_val_le_val] at h2
    omega

variable {P : OrientedThreeStage.{u}} {g : P.Metric}

/-- the embedding of the `n`-th history into the `N`-th one -/
def towerEmb_CPD6 (T : ObservationTower P g) (n N : ℕ) (hnN : n ≤ N) :
    HistEmb_CPD6 (T.history n) (T.history N) :=
  (histEmbOfSame_CPD6 (T.integer_restrict n N hnN).symm).trans
    (histEmbRestrict_CPD6 (T.history N) ⟨(n : ℝ), Nat.cast_nonneg n, by
      rw [T.horizon_eq]; exact_mod_cast hnN⟩)

/-- embeddings respect the active stage -/
theorem HistEmb_CPD6.activeStage_CPD6 {H K : ObservedHistory.{u}} (E : HistEmb_CPD6 H K)
    (t : Icc (0 : ℝ) H.horizon) :
    embIdx_CPD6 E.le (H.activeStage t) =
      K.activeStage ⟨t.1, t.2.1, t.2.2.trans E.horizon_le⟩ := by
  symm
  apply K.activeStage_eq_of_maximal
  · rw [← E.time_eq]; exact H.activeStage_time_le t
  · intro k hk
    by_cases hkk : H.eventCount < k.val
    · have := E.beyond k hkk
      exact absurd (this.trans_le hk) (not_lt.mpr t.2.2)
    · let k0 : Fin (H.eventCount + 1) := ⟨k.val, Nat.lt_succ_of_le (not_lt.mp hkk)⟩
      have hk0 : embIdx_CPD6 E.le k0 = k := Fin.ext rfl
      have : H.time k0 ≤ t.1 := by rw [E.time_eq k0, hk0]; exact hk
      have := H.le_activeStage t k0 this
      rw [← hk0]
      exact embIdx_le_CPD6 E.le this

end GC.LongTime.CuspP1
