import DifferentialGeometry.Topology.Ehresmann.IntervalCompletionSpace
import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Tactic.Linarith

noncomputable section
open Set Topology

namespace Poincare.Topology.Ehresmann

variable {B M : Type*} [TopologicalSpace B] [TopologicalSpace M]

set_option backward.isDefEq.respectTransparency false in
theorem exists_lower_signed_collar
    {u : M → ℝ} {a b ε : ℝ} {K : Set B} {i : B → M}
    (hε : 0 < ε) (hgap : a + ε < b)
    (c : OpenPartialHomeomorph (B × Ici (0 : ℝ)) M)
    (hsource : c.source = K ×ˢ {t : Ici (0 : ℝ) | t.1 < ε})
    (hzero : ∀ x ∈ K, c (x, ⟨0, show (0 : ℝ) ≤ 0 from le_rfl⟩) = i x)
    (hheight : ∀ z ∈ c.source, u (c z) = a + z.2.1) :
    ∃ d : (K × Iio ε) ≃ₜ {q : IntervalCompletionSpace u a b // q.1.1 ∈ c.target},
      (∀ z, (d z).1.1 =
        (c (z.1.1, ⟨max 0 z.2.1, le_max_left 0 z.2.1⟩), a + z.2.1)) ∧
      ∀ q, (d.symm q).1.1 = (c.symm q.1.1.1).1 ∧
        (d.symm q).2.1 = q.1.1.2 - a := by
  let Q := {q : IntervalCompletionSpace u a b // q.1.1 ∈ c.target}
  let clamp : ℝ → Ici (0 : ℝ) := fun t ↦ ⟨max 0 t, le_max_left 0 t⟩
  have hcparam : ∀ z : K × Iio ε, (z.1.1, clamp z.2.1) ∈ c.source := by
    intro z
    rw [hsource]
    exact ⟨z.1.2, max_lt hε z.2.2⟩
  have hinitial : ∀ x ∈ K, u (i x) = a := by
    intro x hx
    have hh := hheight (x, ⟨0, show (0 : ℝ) ≤ 0 from le_rfl⟩) (by rw [hsource]; exact ⟨hx, hε⟩)
    simpa only [hzero x hx, add_zero] using hh
  have hmem : ∀ z : K × Iio ε,
      a + z.2.1 = u (c (z.1.1, clamp z.2.1)) ∨
      (u (c (z.1.1, clamp z.2.1)) = a ∧ a + z.2.1 ≤ a) ∨
      (u (c (z.1.1, clamp z.2.1)) = b ∧ b ≤ a + z.2.1) := by
    intro z
    by_cases ht : 0 ≤ z.2.1
    · exact Or.inl (by
        rw [hheight _ (hcparam z)]
        simp only [clamp, max_eq_right ht])
    · have hclamp : clamp z.2.1 = ⟨0, show (0 : ℝ) ≤ 0 from le_rfl⟩ :=
        Subtype.ext (max_eq_left (le_of_not_ge ht))
      rw [hclamp, hzero z.1.1 z.1.2, hinitial z.1.1 z.1.2]
      exact Or.inr (Or.inl ⟨rfl, by linarith⟩)
  let f : K × Iio ε → Q := fun z ↦
    ⟨⟨(c (z.1.1, clamp z.2.1), a + z.2.1), hmem z⟩, c.map_source (hcparam z)⟩
  have hcinv : ∀ q : Q, (c.symm q.1.1.1).1 ∈ K ∧ (c.symm q.1.1.1).2.1 < ε := by
    intro q
    have hh := c.map_target q.2
    rwa [hsource] at hh
  have hcoord : ∀ q : Q, u q.1.1.1 = a + (c.symm q.1.1.1).2.1 := by
    intro q
    have hh := hheight (c.symm q.1.1.1) (c.map_target q.2)
    rwa [c.right_inv q.2] at hh
  have hlt : ∀ q : Q, u q.1.1.1 < b := by
    intro q
    have hh := hcoord q
    have ht := (hcinv q).2
    linarith
  have htime : ∀ q : Q, q.1.1.2 - a < ε := by
    intro q
    rcases q.1.2 with h | ⟨_, ht⟩ | ⟨hb, _⟩
    · rw [h, hcoord q]
      simpa only [add_sub_cancel_left] using (hcinv q).2
    · linarith
    · exact (ne_of_lt (hlt q) hb).elim
  let g : Q → K × Iio ε := fun q ↦
    (⟨(c.symm q.1.1.1).1, (hcinv q).1⟩, ⟨q.1.1.2 - a, htime q⟩)
  have hclamp : ∀ q : Q, clamp (q.1.1.2 - a) = (c.symm q.1.1.1).2 := by
    intro q
    apply Subtype.ext
    change max 0 (q.1.1.2 - a) = (c.symm q.1.1.1).2.1
    have hn := (c.symm q.1.1.1).2.2
    rcases q.1.2 with h | ⟨ha, ht⟩ | ⟨hb, _⟩
    · rw [h, hcoord q, add_sub_cancel_left, max_eq_right hn]
    · rw [max_eq_left (sub_nonpos.mpr ht)]
      have hh := hcoord q
      linarith
    · exact (ne_of_lt (hlt q) hb).elim
  have hleft : Function.LeftInverse g f := by
    intro z
    apply Prod.ext
    · apply Subtype.ext
      change (c.symm (c (z.1.1, clamp z.2.1))).1 = z.1.1
      rw [c.left_inv (hcparam z)]
    · apply Subtype.ext
      change a + z.2.1 - a = z.2.1
      exact add_sub_cancel_left _ _
  have hright : Function.RightInverse g f := by
    intro q
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · change c ((c.symm q.1.1.1).1, clamp (q.1.1.2 - a)) = q.1.1.1
      rw [hclamp q]
      exact c.right_inv q.2
    · change a + (q.1.1.2 - a) = q.1.1.2
      linarith
  have hclampc : Continuous clamp := (continuous_const.max continuous_id).subtype_mk _
  have hf : Continuous f := by
    have hc : Continuous (fun z : K × Iio ε ↦ c (z.1.1, clamp z.2.1)) :=
      c.continuousOn.comp_continuous
        ((continuous_subtype_val.comp continuous_fst).prodMk
          (hclampc.comp (continuous_subtype_val.comp continuous_snd))) hcparam
    exact ((hc.prodMk (continuous_const.add (continuous_subtype_val.comp continuous_snd))).subtype_mk _).subtype_mk _
  have hg : Continuous g := by
    have hq : Continuous (fun q : Q ↦ q.1.1.1) :=
      continuous_fst.comp (continuous_subtype_val.comp continuous_subtype_val)
    have hi : Continuous (fun q : Q ↦ c.symm q.1.1.1) :=
      c.continuousOn_symm.comp_continuous hq (fun q ↦ q.2)
    exact (hi.fst.subtype_mk _).prodMk
      (((continuous_snd.comp (continuous_subtype_val.comp continuous_subtype_val)).sub
        continuous_const).subtype_mk _)
  exact ⟨{ toFun := f, invFun := g, left_inv := hleft, right_inv := hright,
           continuous_toFun := hf, continuous_invFun := hg }, (fun _ ↦ rfl), (fun _ ↦ ⟨rfl, rfl⟩)⟩

set_option backward.isDefEq.respectTransparency false in
theorem exists_upper_signed_collar
    {u : M → ℝ} {a b ε : ℝ} {K : Set B} {i : B → M}
    (hε : 0 < ε) (hgap : a + ε < b)
    (c : OpenPartialHomeomorph (B × Ici (0 : ℝ)) M)
    (hsource : c.source = K ×ˢ {t : Ici (0 : ℝ) | t.1 < ε})
    (hzero : ∀ x ∈ K, c (x, ⟨0, show (0 : ℝ) ≤ 0 from le_rfl⟩) = i x)
    (hheight : ∀ z ∈ c.source, u (c z) = b - z.2.1) :
    ∃ d : (K × Ioi (-ε)) ≃ₜ {q : IntervalCompletionSpace u a b // q.1.1 ∈ c.target},
      (∀ z, (d z).1.1 =
        (c (z.1.1, ⟨max 0 (-z.2.1), le_max_left 0 (-z.2.1)⟩), b + z.2.1)) ∧
      ∀ q, (d.symm q).1.1 = (c.symm q.1.1.1).1 ∧
        (d.symm q).2.1 = q.1.1.2 - b := by
  have hh : ∀ z ∈ c.source, (fun x ↦ -u x) (c z) = -b + z.2.1 := by
    intro z hz
    change -u (c z) = -b + z.2.1
    rw [hheight z hz]
    linarith
  have hgap' : -b + ε < -a := by linarith
  obtain ⟨e, he, hei⟩ := exists_lower_signed_collar (u := fun x ↦ -u x)
    hε hgap' c hsource hzero hh
  let R : Ioi (-ε) ≃ₜ Iio ε :=
    { toFun := fun t ↦ ⟨-t.1, by have ht := t.2; change -ε < t.1 at ht; change -t.1 < ε; linarith⟩
      invFun := fun t ↦ ⟨-t.1, by have ht := t.2; change t.1 < ε at ht; change -ε < -t.1; linarith⟩
      left_inv := fun t ↦ Subtype.ext (neg_neg t.1)
      right_inv := fun t ↦ Subtype.ext (neg_neg t.1)
      continuous_toFun := continuous_subtype_val.neg.subtype_mk
        (fun t ↦ by have ht := t.2; change -ε < t.1 at ht; change -t.1 < ε; linarith)
      continuous_invFun := continuous_subtype_val.neg.subtype_mk
        (fun t ↦ by have ht := t.2; change t.1 < ε at ht; change -ε < -t.1; linarith) }
  let H : {q : IntervalCompletionSpace (fun x ↦ -u x) (-b) (-a) // q.1.1 ∈ c.target} ≃ₜ
      {q : IntervalCompletionSpace u a b // q.1.1 ∈ c.target} :=
    (intervalCompletionReflect u a b).symm.subtype (fun _ ↦ Iff.rfl)
  let d := ((Homeomorph.refl K).prodCongr R).trans (e.trans H)
  refine ⟨d, ?_, ?_⟩
  · intro z
    have hp := he (z.1, R z.2)
    apply Prod.ext
    · change (e (z.1, R z.2)).1.1.1 =
        c (z.1.1, ⟨max 0 (-z.2.1), le_max_left 0 (-z.2.1)⟩)
      exact congrArg (fun p : M × ℝ ↦ p.1) hp
    · have ht := congrArg Prod.snd hp
      change (e (z.1, R z.2)).1.1.2 = -b + (-z.2.1) at ht
      change -(e (z.1, R z.2)).1.1.2 = b + z.2.1
      linarith
  · intro q
    have hp := hei (H.symm q)
    refine ⟨hp.1, ?_⟩
    have ht := hp.2
    change (e.symm (H.symm q)).2.1 = -q.1.1.2 - (-b) at ht
    change -(e.symm (H.symm q)).2.1 = q.1.1.2 - b
    linarith

end Poincare.Topology.Ehresmann
