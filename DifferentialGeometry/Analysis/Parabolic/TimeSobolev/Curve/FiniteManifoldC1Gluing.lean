import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.Curve.ManifoldC1Gluing
import Mathlib.Order.Interval.Set.Monotone

set_option autoImplicit false

noncomputable section

open Filter Function Set
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TimeSobolev

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M]

theorem curve_c1_fin {gamma : Real → M} {t : Nat → Real} {m : Nat}
    (hm : 0 < m)
    (ht : ∀ k, k < m → t k < t (k + 1))
    (hpiece : ∀ k, k < m →
      ContMDiffOn 𝓘(Real, Real) I 1 gamma (Icc (t k) (t (k + 1))))
    (hnode : ∀ k, 0 < k → k < m →
      derivWithin ((extChartAt I (gamma (t k))) ∘ gamma)
          (Icc (t (k - 1)) (t k)) (t k) =
        derivWithin ((extChartAt I (gamma (t k))) ∘ gamma)
          (Icc (t k) (t (k + 1))) (t k)) :
    ContMDiffOn 𝓘(Real, Real) I 1 gamma (Icc (t 0) (t m)) := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
      cases m with
      | zero => exact (Nat.lt_asymm hm hm).elim
      | succ n =>
          by_cases hn : n = 0
          · subst n
            simpa only [Nat.zero_add, Nat.reduceAdd] using hpiece 0 (by omega)
          · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
            have hleft : ContMDiffOn 𝓘(Real, Real) I 1 gamma (Icc (t 0) (t n)) :=
              ih n (Nat.lt_succ_self n) hnpos
                (fun k hk ↦ ht k (hk.trans (Nat.lt_succ_self n)))
                (fun k hk ↦ hpiece k (hk.trans (Nat.lt_succ_self n)))
                (fun k hk0 hk ↦ hnode k hk0 (hk.trans (Nat.lt_succ_self n)))
            have hright : ContMDiffOn 𝓘(Real, Real) I 1 gamma
                (Icc (t n) (t (n + 1))) :=
              hpiece n (Nat.lt_succ_self n)
            have hmono : StrictMonoOn t (Iic (n + 1)) :=
              strictMonoOn_Iic_of_lt_succ fun k hk ↦ ht k hk
            have h0n : t 0 < t n :=
              hmono (by simp) (by simp) hnpos
            have hnnext : t n < t (n + 1) :=
              ht n (Nat.lt_succ_self n)
            have hprev : t (n - 1) < t n := by
              have h := ht (n - 1) (by omega)
              rw [Nat.sub_add_cancel (Nat.succ_le_iff.mpr hnpos)] at h
              exact h
            have hsets : Icc (t 0) (t n) =ᶠ[nhds (t n)] Icc (t (n - 1)) (t n) := by
              have h0prev : t 0 ≤ t (n - 1) := by
                exact hmono.monotoneOn (by simp) (by simp; omega) (Nat.zero_le _)
              filter_upwards [Ioi_mem_nhds hprev] with x hx
              apply propext
              constructor
              · intro h
                exact ⟨hx.le, h.2⟩
              · intro h
                exact ⟨h0prev.trans h.1, h.2⟩
            have hder :
                derivWithin ((extChartAt I (gamma (t n))) ∘ gamma)
                    (Icc (t 0) (t n)) (t n) =
                  derivWithin ((extChartAt I (gamma (t n))) ∘ gamma)
                    (Icc (t n) (t (n + 1))) (t n) := by
              rw [derivWithin_congr_set hsets]
              exact hnode n hnpos (Nat.lt_succ_self n)
            exact curve_c1_join h0n hnnext hleft hright hder

end TimeSobolev
end Parabolic
end Analysis
end DifferentialGeometry

end
