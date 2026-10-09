import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventCapCapture

/-!
# CH12-S74 G2 (b1'), pure-logic part: building a backward point trace under a one-event step

`exists_backwardTrace_of_step_S74`: if a predicate `Good j q` on the points of the stages holds at
the endpoint `y` and every event `i` of the window `first ≤ i.castSucc`, `i.succ ≤ last` can be
inverted (`Good i.succ q → ∃ p, RegularCrossing p q ∧ Good i.castSucc p`), then the backward trace of
`y` down to `first` exists and `Good` holds at every point of it.  (The step is where the cap
exclusion and the backward barrier of the S63 constants table enter.)
-/

set_option autoImplicit false

noncomputable section

open Set DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace GC.LongTime.Ch12

universe u

theorem exists_backwardTrace_of_step_S74 (H : ObservedHistory.{u})
    (Good : ∀ j : Fin (H.eventCount + 1), (H.stage j).Carrier → Prop)
    {first last : Fin (H.eventCount + 1)} (hle : first ≤ last) {y : (H.stage last).Carrier}
    (hy : Good last y)
    (hstep : ∀ i : Fin H.eventCount, first ≤ i.castSucc → i.succ ≤ last →
      ∀ q : (H.stage i.succ).Carrier, Good i.succ q →
        ∃ p : (H.stage i.castSucc).Carrier, (H.event i).RegularCrossing p q ∧
          Good i.castSucc p) :
    ∃ X : BackwardPointTrace H first last hle y,
      ∀ (j : Fin (H.eventCount + 1)) (hf : first ≤ j) (hl : j ≤ last), Good j (X.point j hf hl) := by
  have key : ∀ m : Fin (H.eventCount + 1), first ≤ m → ∀ hml : m ≤ last,
      ∃ A : BackwardPointTrace H m last hml y,
        ∀ (j : Fin (H.eventCount + 1)) (hf : m ≤ j) (hl : j ≤ last), Good j (A.point j hf hl) := by
    intro m
    induction m using Fin.reverseInduction with
    | last =>
      intro _ hml
      have he : last = Fin.last H.eventCount := le_antisymm (Fin.le_last _) hml
      subst last
      refine ⟨BackwardPointTrace.singleton H _ y, fun j hf hl => ?_⟩
      obtain rfl : j = Fin.last H.eventCount := le_antisymm hl hf
      exact (BackwardPointTrace.singleton H _ y).endpoint_eq ▸ hy
    | cast i ih =>
      intro hfi hml
      by_cases he : i.castSucc = last
      · subst last
        refine ⟨BackwardPointTrace.singleton H _ y, fun j hf hl => ?_⟩
        obtain rfl : j = i.castSucc := le_antisymm hl hf
        exact (BackwardPointTrace.singleton H _ y).endpoint_eq ▸ hy
      · have hs : i.succ ≤ last := by
          apply Fin.le_iff_val_le_val.mpr
          have hlt : i.castSucc < last := lt_of_le_of_ne hml he
          exact Nat.succ_le_iff.mpr hlt
        obtain ⟨A, hA⟩ := ih (hfi.trans (Fin.castSucc_lt_succ (i := i)).le) hs
        obtain ⟨p, hcross, hp⟩ := hstep i hfi hs _ (hA i.succ le_rfl hs)
        refine ⟨A.prepend p hcross, fun j hf hl => ?_⟩
        by_cases hji : j = i.castSucc
        · subst hji
          rw [BackwardPointTrace.prepend_point_first]
          exact hp
        · have hsucc : i.succ ≤ j := by
            apply Fin.le_iff_val_le_val.mpr
            have hlt : i.castSucc < j := lt_of_le_of_ne hf (Ne.symm hji)
            exact Nat.succ_le_iff.mpr hlt
          have hh : (A.prepend p hcross).point j hf hl = A.point j hsucc hl := by
            simp [BackwardPointTrace.prepend, hji]
          rw [hh]
          exact hA j hsucc hl
  exact key first le_rfl hle

end GC.LongTime.Ch12
