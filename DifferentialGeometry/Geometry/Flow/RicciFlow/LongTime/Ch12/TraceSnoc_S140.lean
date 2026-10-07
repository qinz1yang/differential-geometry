import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.Backward

/-!
# CH12-S140, group 1b: forward construction of `BackwardPointTrace`s

`snoc_S140` extends a trace ending at stage `i.castSucc` by one regular crossing of event `i`;
`forward_trace_exists_S140` is the forward induction principle: a predicate `Φ` on points of the stages that
propagates through every later event by a regular crossing yields a trace from stage `j` to the last stage
through the given point (the survival induction of `hsurv` (B) is an instance of it).
-/

set_option autoImplicit false

noncomputable section

open Set Manifold DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace GC.LongTime.Ch12

universe u

/-- Extend a trace ending at stage `i.castSucc` by one regular crossing of event `i`. -/
def snoc_S140 {H : ObservedHistory.{u}} {first : Fin (H.eventCount + 1)} (i : Fin H.eventCount)
    (hfi : first ≤ i.castSucc) {y : (H.stage i.castSucc).Carrier}
    (A : BackwardPointTrace H first i.castSucc hfi y) {y' : (H.stage i.succ).Carrier}
    (hc : (H.event i).RegularCrossing y y') :
    BackwardPointTrace H first i.succ (hfi.trans (Fin.castSucc_lt_succ (i := i)).le) y' where
  point j hf hl :=
    if h : j ≤ i.castSucc then A.point j hf h
    else (le_antisymm hl (Fin.castSucc_lt_iff_succ_le.mp (not_le.mp h)) ▸ y')
  endpoint_eq := by
    simp only [Fin.succ_le_castSucc_iff, lt_self_iff_false, dite_false]
  crossing i' hf hl := by
    by_cases h : i'.succ ≤ i.castSucc
    · have h' : i'.castSucc ≤ i.castSucc := (Fin.castSucc_lt_succ (i := i')).le.trans h
      simp only [h, h', dite_true]
      exact A.crossing i' hf h
    · have hlt : i.castSucc < i'.succ := not_le.mp h
      have hii : i' = i := by
        apply Fin.ext
        have h1 := Fin.le_iff_val_le_val.mp hl
        have h2 := Fin.lt_def.mp hlt
        simp only [Fin.val_succ, Fin.val_castSucc] at h1 h2
        omega
      subst hii
      have h' : i'.castSucc ≤ i'.castSucc := le_rfl
      simp only [h, h', dite_true, dite_false]
      have hy : A.point i'.castSucc hf le_rfl = y := A.endpoint_eq
      rw [hy]
      exact hc

/-- Forward induction principle: a predicate `Φ` propagating through every event after stage `j` by a regular
crossing gives a trace from stage `j` to the last stage through the given point `y₀`, ending in `Φ`. -/
theorem forward_trace_exists_S140 (H : ObservedHistory.{u}) (j : Fin (H.eventCount + 1))
    (Φ : ∀ m : Fin (H.eventCount + 1), (H.stage m).Carrier → Prop)
    {y₀ : (H.stage j).Carrier} (h0 : Φ j y₀)
    (hstep : ∀ i : Fin H.eventCount, j ≤ i.castSucc → ∀ y : (H.stage i.castSucc).Carrier,
      Φ i.castSucc y → ∃ y' : (H.stage i.succ).Carrier, (H.event i).RegularCrossing y y' ∧ Φ i.succ y') :
    ∃ (yf : (H.stage (Fin.last H.eventCount)).Carrier)
      (A : BackwardPointTrace H j (Fin.last H.eventCount) (Fin.le_last _) yf),
      A.point j le_rfl (Fin.le_last _) = y₀ ∧ Φ (Fin.last H.eventCount) yf := by
  have key : ∀ m : Fin (H.eventCount + 1), ∀ hjm : j ≤ m, ∃ (ym : (H.stage m).Carrier)
      (A : BackwardPointTrace H j m hjm ym), A.point j le_rfl hjm = y₀ ∧ Φ m ym := by
    intro m
    induction m using Fin.induction with
    | zero =>
      intro hjm
      obtain rfl : j = 0 := Fin.le_zero_iff.mp hjm
      exact ⟨y₀, BackwardPointTrace.singleton H _ y₀, rfl, h0⟩
    | succ i ih =>
      intro hjm
      by_cases hji : j ≤ i.castSucc
      · obtain ⟨y, A, hA, hΦ⟩ := ih hji
        obtain ⟨y', hc, hΦ'⟩ := hstep i hji y hΦ
        refine ⟨y', snoc_S140 i hji A hc, ?_, hΦ'⟩
        simp only [snoc_S140, hji, dite_true]
        exact hA
      · have hje : j = i.succ := le_antisymm hjm (Fin.castSucc_lt_iff_succ_le.mp (not_le.mp hji))
        subst hje
        exact ⟨y₀, BackwardPointTrace.singleton H _ y₀, rfl, h0⟩
  obtain ⟨ym, A, hA, hΦ⟩ := key (Fin.last H.eventCount) (Fin.le_last _)
  exact ⟨ym, A, hA, hΦ⟩

end GC.LongTime.Ch12
