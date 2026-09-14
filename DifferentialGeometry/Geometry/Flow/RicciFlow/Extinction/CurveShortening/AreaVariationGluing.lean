import Mathlib.Topology.Order.LeftRightNhds
import Mathlib.Tactic

open Filter Set
open scoped Topology

namespace DifferentialGeometry

theorem forall_pos_of_eventually_nhdsGT_of_add {P : ℝ → Prop}
    (hsmall : ∀ᶠ h in 𝓝[>] (0 : ℝ), P h)
    (hadd : ∀ s t : ℝ, 0 < s → 0 < t → P s → P t → P (s + t)) :
    ∀ h : ℝ, 0 < h → P h := by
  intro h hhpos
  obtain ⟨δ, hδpos, hδ⟩ := (nhdsGT_basis (0 : ℝ)).mem_iff.mp hsmall
  obtain ⟨n, hn⟩ := exists_nat_gt (h / δ)
  have hlt : h < ((n : ℝ) + 1) * δ := by
    rw [div_lt_iff₀ hδpos] at hn
    nlinarith [hn, hδpos]
  set m : ℕ := n + 1 with hm
  have hmreal : (0 : ℝ) < (m : ℝ) := by positivity
  have hmδ : h < (m : ℝ) * δ := by simpa only [hm, Nat.cast_add, Nat.cast_one] using hlt
  set u : ℝ := h / (m : ℝ) with hu
  have hupos : 0 < u := by rw [hu]; positivity
  have hult : u < δ := by
    rw [hu, div_lt_iff₀ hmreal]
    linarith [hmδ, mul_comm (m : ℝ) δ]
  have hPu : P u := hδ ⟨hupos, hult⟩
  have hmain : ∀ k : ℕ, 1 ≤ k → P ((k : ℝ) * u) := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => simpa using hPu
    | succ j hj ih =>
        have hjpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj
        have hjupos : 0 < (j : ℝ) * u := mul_pos hjpos hupos
        have hstep := hadd ((j : ℝ) * u) u hjupos hupos ih hPu
        rwa [show (j : ℝ) * u + u = ((j + 1 : ℕ) : ℝ) * u by push_cast; ring] at hstep
  have hmul : (m : ℝ) * u = h := by
    rw [hu]
    field_simp
  have hfin := hmain m (Nat.succ_le_of_lt (Nat.succ_pos n))
  rwa [hmul] at hfin

theorem forall_add_le_of_eventually_nhdsGT_of_cocycle {P : ℝ → ℝ → Prop} {a b : ℝ}
    (hsmall : ∀ᶠ h in 𝓝[>] (0 : ℝ), ∀ t ∈ Ico a b, t + h ≤ b → P t h)
    (hcomp : ∀ t s t' : ℝ, P t s → P (t + s) t' → P t (s + t')) :
    ∀ t ∈ Ico a b, ∀ h : ℝ, 0 < h → t + h ≤ b → P t h := by
  intro t ht h hhpos hb
  obtain ⟨δ, hδpos, hδ⟩ := (nhdsGT_basis (0 : ℝ)).mem_iff.mp hsmall
  obtain ⟨n, hn⟩ := exists_nat_gt (h / δ)
  have hlt : h < ((n : ℝ) + 1) * δ := by
    rw [div_lt_iff₀ hδpos] at hn
    nlinarith [hn, hδpos]
  set m : ℕ := n + 1 with hm
  have hmreal : (0 : ℝ) < (m : ℝ) := by positivity
  have hmδ : h < (m : ℝ) * δ := by simpa only [hm, Nat.cast_add, Nat.cast_one] using hlt
  set u : ℝ := h / (m : ℝ) with hu
  have hupos : 0 < u := by rw [hu]; positivity
  have hult : u < δ := by
    rw [hu, div_lt_iff₀ hmreal]
    linarith [hmδ, mul_comm (m : ℝ) δ]
  have hmul : (m : ℝ) * u = h := by
    rw [hu]
    field_simp
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast Nat.succ_le_of_lt (Nat.succ_pos n)
  have hu_le_h : u ≤ h := by
    have hle := mul_le_mul_of_nonneg_right hm1 hupos.le
    rwa [one_mul, hmul] at hle
  have hstep : ∀ s : ℝ, a ≤ s → s + u ≤ b → P s u := fun s hs1 hs2 =>
    hδ ⟨hupos, hult⟩ s ⟨hs1, by linarith [hs2, hupos]⟩ hs2
  have hmain : ∀ k : ℕ, 1 ≤ k → k ≤ m → P t ((k : ℝ) * u) := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => intro _; simpa using hstep t ht.1 (by linarith [hb, hu_le_h])
    | succ j hj ih =>
        intro hjm
        have hprev : P t ((j : ℝ) * u) := ih (Nat.le_of_succ_le hjm)
        have hju : ((j : ℝ) + 1) * u ≤ (m : ℝ) * u :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hjm) hupos.le
        have hguard : t + (j : ℝ) * u + u ≤ b := by
          have h1 : t + ((j : ℝ) + 1) * u ≤ t + h := by
            rw [hmul] at hju
            linarith
          have h2 : t + (j : ℝ) * u + u = t + ((j : ℝ) + 1) * u := by ring
          linarith
        have hsau : a ≤ t + (j : ℝ) * u := by
          have h0 : 0 ≤ (j : ℝ) * u := mul_nonneg (Nat.cast_nonneg j) hupos.le
          linarith [ht.1]
        have hnext := hcomp t ((j : ℝ) * u) u hprev (hstep _ hsau hguard)
        rwa [show (j : ℝ) * u + u = ((j + 1 : ℕ) : ℝ) * u by push_cast; ring] at hnext
  have hfin := hmain m (Nat.succ_le_of_lt (Nat.succ_pos n)) le_rfl
  rwa [hmul] at hfin

end DifferentialGeometry
