import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Dynamics.FixedPoints.Topology
import Mathlib.Order.Iterate
import Mathlib.Topology.ContinuousMap.Algebra

set_option autoImplicit false
open Set Filter Function
open scoped Topology

namespace DifferentialGeometry.Topology

variable {α : Type*} [ConditionallyCompleteLinearOrder α] [TopologicalSpace α]
  [OrderTopology α] {a b : α} {f : α → α}

theorem tendsto_iterate_of_lt_on_Ico (hab : a < b)
    (hcont : ContinuousOn f (Ico a b))
    (hincr : ∀ x ∈ Ico a b, x < f x)
    (hbound : ∀ x ∈ Ico a b, f x < b) :
    Tendsto (fun n : ℕ => f^[n] a) atTop (𝓝 b) := by
  have hmem (n : ℕ) : f^[n] a ∈ Ico a b := by
    induction n with
    | zero => exact ⟨le_rfl, hab⟩
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact ⟨ih.1.trans (hincr _ ih).le, hbound _ ih⟩
  have hmono : StrictMono (fun n : ℕ => f^[n] a) := by
    apply strictMono_nat_of_lt_succ
    intro n
    rw [Function.iterate_succ_apply']
    exact hincr _ (hmem n)
  have hbdd : BddAbove (range fun n : ℕ => f^[n] a) :=
    ⟨b, fun _ ⟨n, hn⟩ => hn ▸ (hmem n).2.le⟩
  let c := ⨆ n : ℕ, f^[n] a
  have hc : Tendsto (fun n : ℕ => f^[n] a) atTop (𝓝 c) :=
    tendsto_atTop_ciSup hmono.monotone hbdd
  have hcb : c ≤ b := ciSup_le (fun n => (hmem n).2.le)
  have hac : a < c := by
    have hh := (hincr a ⟨le_rfl, hab⟩).trans_le (le_ciSup hbdd 1)
    simpa using hh
  have heq : c = b := by
    by_contra hne
    have hlt : c < b := lt_of_le_of_ne hcb hne
    have hfixed := isFixedPt_of_tendsto_iterate hc
      ((hcont c ⟨hac.le, hlt⟩).continuousAt (Ico_mem_nhds hac hlt))
    exact (ne_of_lt (hincr c ⟨hac.le, hlt⟩)) hfixed.symm
  rwa [heq] at hc

variable [AddCommGroup α] [IsOrderedAddMonoid α] [ContinuousAdd α]

theorem exists_strictMono_sequence_of_pos_continuous_step
    (hab : a < b) (d : C(Ico a b, α))
    (hd : ∀ t, 0 < d t) (hfit : ∀ t : Ico a b, (t : α) + d t < b) :
    ∃ s : ℕ → Ico a b,
      (s 0 : α) = a ∧ StrictMono (fun n => (s n : α)) ∧
      Tendsto (fun n => (s n : α)) atTop (𝓝 b) ∧
      ∀ n, (s (n + 1) : α) = (s n : α) + d (s n) := by
  classical
  let f : α → α := fun x => if hx : x ∈ Ico a b then x + d ⟨x, hx⟩ else x
  have hf (x : Ico a b) : f x = (x : α) + d x := by simp only [f, dif_pos x.property]
  have hcont : ContinuousOn f (Ico a b) := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact (continuous_subtype_val.add d.continuous).congr (fun x => (hf x).symm)
  have hinc (x : α) (hx : x ∈ Ico a b) : x < f x := by
    rw [hf ⟨x, hx⟩]
    exact lt_add_of_pos_right x (hd ⟨x, hx⟩)
  have hb (x : α) (hx : x ∈ Ico a b) : f x < b := by
    rw [hf ⟨x, hx⟩]
    exact hfit ⟨x, hx⟩
  have hmap : MapsTo f (Ico a b) (Ico a b) :=
    fun x hx => ⟨hx.1.trans (hinc x hx).le, hb x hx⟩
  let s : ℕ → Ico a b := fun n => ⟨f^[n] a, hmap.iterate n ⟨le_rfl, hab⟩⟩
  refine ⟨s, rfl, ?_, tendsto_iterate_of_lt_on_Ico hab hcont hinc hb, ?_⟩
  · apply strictMono_nat_of_lt_succ
    intro n
    exact (hinc _ (s n).property).trans_eq (Function.iterate_succ_apply' f n a).symm
  · intro n
    exact (Function.iterate_succ_apply' f n a).trans (hf (s n))

end DifferentialGeometry.Topology
