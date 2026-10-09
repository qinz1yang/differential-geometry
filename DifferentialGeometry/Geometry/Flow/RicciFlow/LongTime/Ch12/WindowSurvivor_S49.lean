import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySurvivorDomain
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BackwardTraceLocalChart
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.TimeSmoothingTheta_CX5

set_option autoImplicit false

/-! # CH12-S49 G1: survivor-range restriction, junction identification, dyadic window bookkeeping

Pure pieces of the history bookkeeping behind `PersistentModelPatch` (CX5):
* `survivorRestrict_S49`: a survivor point of the range `[f₁, l₁]` is a survivor point of every
  sub-range `[f, l]` (used to bring two lifts to one common stage range of one history);
* `survivor_join_S49`: `hjoin` from the exact endpoint identity, by injectivity of the survivor map;
* `exists_windows_S49`: for `t₀ > T`, a time interval `(a, b)` around `t₀` meeting at most the dyadic
  windows `j`, `j+1`, with a junction only when `t₀ = t_{j+1}`. -/

noncomputable section
open Set Filter DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff

namespace GC.LongTime.Ch12
universe u

section Survivor
variable (K : ObservedHistory.{u}) {f₁ l₁ f l : Fin (K.eventCount + 1)}

/-- A survivor point of the range `[f₁, l₁]`, seen as a survivor point of `[f, l] ⊆ [f₁, l₁]`
(its image at stage `l`). -/
def survivorRestrict_S49 (h₁ : f₁ ≤ l₁) (h : f ≤ l) (hf : f₁ ≤ f) (hl : l ≤ l₁)
    (x : K.backwardSurvivorDomain f₁ l₁ h₁) : K.backwardSurvivorDomain f l h :=
  ⟨K.backwardSurvivorMap f₁ l₁ h₁ l (hf.trans h) hl x,
   ⟨((Classical.choice x.property).restrictLast (hf.trans h) hl).restrictFirst hf h⟩⟩

theorem backwardSurvivorMap_survivorRestrict_S49 (h₁ : f₁ ≤ l₁) (h : f ≤ l) (hf : f₁ ≤ f)
    (hl : l ≤ l₁) (j : Fin (K.eventCount + 1)) (hj : f ≤ j) (hjl : j ≤ l)
    (x : K.backwardSurvivorDomain f₁ l₁ h₁) :
    K.backwardSurvivorMap f l h j hj hjl (survivorRestrict_S49 K h₁ h hf hl x) =
      K.backwardSurvivorMap f₁ l₁ h₁ j (hf.trans hj) (hjl.trans hl) x :=
  (K.backwardSurvivorMap_eq_point f l h j hj hjl _
    (((Classical.choice x.property).restrictLast (hf.trans h) hl).restrictFirst hf h)).trans rfl

theorem contMDiff_survivorRestrict_S49 (h₁ : f₁ ≤ l₁) (h : f ≤ l) (hf : f₁ ≤ f)
    (hl : l ≤ l₁) : ContMDiff (𝓡 3) (𝓡 3) ∞ (survivorRestrict_S49 K h₁ h hf hl) :=
  (ContMDiff.subtypeVal_comp_iff (K.backwardSurvivorDomain f l h) (survivorRestrict_S49 K h₁ h hf hl)).mp
    (K.backwardSurvivorMap_isLocalDiffeomorph f₁ l₁ h₁ l (hf.trans h) hl).contMDiff

/-- `hjoin` from the exact endpoint identification: two survivor points whose images at one stage
are heterogeneously equal to the same actual-flow point coincide. -/
theorem survivor_join_S49 (h : f ≤ l) (j : Fin (K.eventCount + 1)) (hj : f ≤ j) (hjl : j ≤ l)
    {Q : Type u} (x y : K.backwardSurvivorDomain f l h) (u v : Q)
    (hx : HEq (K.backwardSurvivorMap f l h j hj hjl x) u)
    (hy : HEq (K.backwardSurvivorMap f l h j hj hjl y) v) (huv : u = v) : x = y := by
  subst huv
  exact K.backwardSurvivorMap_injective f l h j hj hjl (eq_of_heq (hx.trans hy.symm))

end Survivor

section Windows

/-- Dyadic window bookkeeping: around `t₀ > T` there is a time interval `(a, b)` (inside any given
`(a₀, b₀)`, with `T < a`) meeting only the windows `j`, `j + 1`; the junction `t_{j+1}` lies inside
`(a, b)` only when `t₀ = t_{j+1}`. -/
theorem exists_windows_S49 {T t₀ : ℝ} (hT : 0 < T) (ht₀ : T < t₀) {a₀ b₀ : ℝ}
    (ha₀ : a₀ < t₀) (hb₀ : t₀ < b₀) :
    ∃ (j : ℕ) (a b : ℝ), T < a ∧ a₀ ≤ a ∧ a < t₀ ∧ t₀ < b ∧ b ≤ b₀ ∧
      dyadicTime_CX5 T j < t₀ ∧ t₀ ≤ dyadicTime_CX5 T (j + 1) ∧
      ((t₀ < dyadicTime_CX5 T (j + 1) ∧
        (∀ k : ℕ, dyadicTime_CX5 T k < b → a < dyadicTime_CX5 T (k + 1) → k = j) ∧
        (∀ k : ℕ, a < dyadicTime_CX5 T (k + 1) → dyadicTime_CX5 T (k + 1) < b → False)) ∨
       (t₀ = dyadicTime_CX5 T (j + 1) ∧
        (∀ k : ℕ, dyadicTime_CX5 T k < b → a < dyadicTime_CX5 T (k + 1) → k = j ∨ k = j + 1) ∧
        (∀ k : ℕ, a < dyadicTime_CX5 T (k + 1) → dyadicTime_CX5 T (k + 1) < b → k = j))) := by
  classical
  have hmono := dyadicTime_strictMono_CX5 hT
  have hex : ∃ m : ℕ, t₀ ≤ dyadicTime_CX5 T m := by
    have htend : Tendsto (dyadicTime_CX5 T) atTop atTop :=
      (tendsto_pow_atTop_atTop_of_one_lt one_lt_two).atTop_mul_const hT
    exact (htend.eventually (eventually_ge_atTop t₀)).exists
  have hm0 : ¬ t₀ ≤ dyadicTime_CX5 T 0 := by
    rw [dyadicTime_zero_CX5]; exact not_le.2 ht₀
  have hfind := Nat.find_spec hex
  have hne : Nat.find hex ≠ 0 := fun h0 => hm0 (h0 ▸ hfind)
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hne
  have hup : t₀ ≤ dyadicTime_CX5 T (j + 1) := by
    have h := hfind
    rw [hj] at h
    exact h
  have hlow : dyadicTime_CX5 T j < t₀ := by
    have := Nat.find_min hex (show j < Nat.find hex by omega)
    exact not_le.1 this
  have hTj : T ≤ dyadicTime_CX5 T j := by
    have := hmono.monotone (Nat.zero_le j)
    simpa using this
  have hj1 : dyadicTime_CX5 T (j + 1) < dyadicTime_CX5 T (j + 2) := hmono (by omega)
  rcases hup.lt_or_eq with hlt | heq
  · refine ⟨j, max a₀ ((dyadicTime_CX5 T j + t₀) / 2), min b₀ ((t₀ + dyadicTime_CX5 T (j + 1)) / 2),
      ?_, le_max_left _ _, ?_, ?_, min_le_left _ _, hlow, hup, Or.inl ⟨hlt, ?_, ?_⟩⟩
    · exact lt_of_lt_of_le (by linarith) (le_max_right _ _)
    · exact max_lt ha₀ (by linarith)
    · exact lt_min hb₀ (by linarith)
    · intro k hkb hka
      have h1 : dyadicTime_CX5 T k < dyadicTime_CX5 T (j + 1) :=
        hkb.trans_le ((min_le_right _ _).trans (by linarith))
      have h2 : dyadicTime_CX5 T j < dyadicTime_CX5 T (k + 1) :=
        lt_of_lt_of_le (by linarith [le_max_right a₀ ((dyadicTime_CX5 T j + t₀) / 2)]) hka.le
      have := hmono.lt_iff_lt.1 h1
      have := hmono.lt_iff_lt.1 h2
      omega
    · intro k hka hkb
      have h1 : dyadicTime_CX5 T (k + 1) < dyadicTime_CX5 T (j + 1) :=
        hkb.trans_le ((min_le_right _ _).trans (by linarith))
      have h2 : dyadicTime_CX5 T j < dyadicTime_CX5 T (k + 1) :=
        lt_of_lt_of_le (by linarith [le_max_right a₀ ((dyadicTime_CX5 T j + t₀) / 2)]) hka.le
      have := hmono.lt_iff_lt.1 h1
      have := hmono.lt_iff_lt.1 h2
      omega
  · have hlt2 : t₀ < dyadicTime_CX5 T (j + 2) := heq ▸ hj1
    refine ⟨j, max a₀ ((dyadicTime_CX5 T j + t₀) / 2), min b₀ ((t₀ + dyadicTime_CX5 T (j + 2)) / 2),
      ?_, le_max_left _ _, ?_, ?_, min_le_left _ _, hlow, hup, Or.inr ⟨heq, ?_, ?_⟩⟩
    · exact lt_of_lt_of_le (by linarith) (le_max_right _ _)
    · exact max_lt ha₀ (by linarith)
    · exact lt_min hb₀ (by linarith)
    · intro k hkb hka
      have h1 : dyadicTime_CX5 T k < dyadicTime_CX5 T (j + 2) :=
        hkb.trans_le ((min_le_right _ _).trans (by linarith))
      have h2 : dyadicTime_CX5 T j < dyadicTime_CX5 T (k + 1) :=
        lt_of_lt_of_le (by linarith [le_max_right a₀ ((dyadicTime_CX5 T j + t₀) / 2)]) hka.le
      have := hmono.lt_iff_lt.1 h1
      have := hmono.lt_iff_lt.1 h2
      omega
    · intro k hka hkb
      have h1 : dyadicTime_CX5 T (k + 1) < dyadicTime_CX5 T (j + 2) :=
        hkb.trans_le ((min_le_right _ _).trans (by linarith))
      have h2 : dyadicTime_CX5 T j < dyadicTime_CX5 T (k + 1) :=
        lt_of_lt_of_le (by linarith [le_max_right a₀ ((dyadicTime_CX5 T j + t₀) / 2)]) hka.le
      have := hmono.lt_iff_lt.1 h1
      have := hmono.lt_iff_lt.1 h2
      omega

end Windows

end GC.LongTime.Ch12
