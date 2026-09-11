import DifferentialGeometry.Topology.Ehresmann.SignedCollar
import DifferentialGeometry.Topology.Ehresmann.IntervalCompletionInterior

noncomputable section
open Set Topology

namespace DifferentialGeometry.Topology.Ehresmann

private theorem exists_openPartialHomeomorph_of_subtype
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {S : Set X} {T : Set Y} (hS : IsOpen S) (hT : IsOpen T) (hSne : S.Nonempty)
    (h : S ≃ₜ T) :
    ∃ d : OpenPartialHomeomorph X Y, d.source = S ∧ d.target = T ∧
      (∀ x (hx : x ∈ S), d x = (h ⟨x, hx⟩).1) ∧
      ∀ y (hy : y ∈ T), d.symm y = (h.symm ⟨y, hy⟩).1 := by
  classical
  let x₀ : S := ⟨hSne.choose, hSne.choose_spec⟩
  let f : X → Y := fun x ↦ if hx : x ∈ S then (h ⟨x, hx⟩).1 else (h x₀).1
  let g : Y → X := fun y ↦ if hy : y ∈ T then (h.symm ⟨y, hy⟩).1 else x₀.1
  have hf (x : X) (hx : x ∈ S) : f x = (h ⟨x, hx⟩).1 := dif_pos hx
  have hg (y : Y) (hy : y ∈ T) : g y = (h.symm ⟨y, hy⟩).1 := dif_pos hy
  have hfc : ContinuousOn f S := by
    rw [continuousOn_iff_continuous_domRestrict]
    have heq : S.domRestrict f = fun x : S ↦ (h x).1 := funext (fun x ↦ hf x.1 x.2)
    rw [heq]
    exact continuous_subtype_val.comp h.continuous
  have hgc : ContinuousOn g T := by
    rw [continuousOn_iff_continuous_domRestrict]
    have heq : T.domRestrict g = fun y : T ↦ (h.symm y).1 := funext (fun y ↦ hg y.1 y.2)
    rw [heq]
    exact continuous_subtype_val.comp h.symm.continuous
  refine ⟨{
      toFun := f
      invFun := g
      source := S
      target := T
      map_source' := ?_
      map_target' := ?_
      left_inv' := ?_
      right_inv' := ?_
      open_source := hS
      open_target := hT
      continuousOn_toFun := hfc
      continuousOn_invFun := hgc }, rfl, rfl, hf, hg⟩
  · intro x hx
    rw [hf x hx]
    exact (h ⟨x, hx⟩).2
  · intro y hy
    rw [hg y hy]
    exact (h.symm ⟨y, hy⟩).2
  · intro x hx
    rw [hf x hx, hg _ (h ⟨x, hx⟩).2]
    exact congrArg Subtype.val (h.symm_apply_apply ⟨x, hx⟩)
  · intro y hy
    rw [hg y hy, hf _ (h.symm ⟨y, hy⟩).2]
    exact congrArg Subtype.val (h.apply_symm_apply ⟨y, hy⟩)

variable {B M : Type*} [TopologicalSpace B] [TopologicalSpace M]

set_option backward.isDefEq.respectTransparency false in
theorem exists_lower_completionChart
    {u : M → ℝ} {a b ε : ℝ} {K : Set B} {i : B → M}
    (hK : IsOpen K) (hKne : K.Nonempty) (hε : 0 < ε) (hgap : a + ε < b)
    (c : OpenPartialHomeomorph (B × Ici (0 : ℝ)) M)
    (hsource : c.source = K ×ˢ {t : Ici (0 : ℝ) | t.1 < ε})
    (hzero : ∀ x ∈ K, c (x, ⟨0, show (0 : ℝ) ≤ 0 from le_rfl⟩) = i x)
    (hheight : ∀ z ∈ c.source, u (c z) = a + z.2.1) :
    ∃ d : OpenPartialHomeomorph (B × ℝ) (IntervalCompletionSpace u a b),
      d.source = K ×ˢ Iio ε ∧ d.target = {q | q.1.1 ∈ c.target} ∧
      (∀ z ∈ d.source, (d z).1 =
        (c (z.1, ⟨max 0 z.2, le_max_left 0 z.2⟩), a + z.2)) ∧
      ∀ q ∈ d.target, d.symm q = ((c.symm q.1.1).1, q.1.2 - a) := by
  obtain ⟨e, he, hei⟩ := exists_lower_signed_collar hε hgap c hsource hzero hheight
  let H := (Homeomorph.Set.prod K (Iio ε)).trans e
  have htarget : IsOpen {q : IntervalCompletionSpace u a b | q.1.1 ∈ c.target} :=
    c.open_target.preimage (continuous_fst.comp continuous_subtype_val)
  have hSne : (K ×ˢ Iio ε).Nonempty :=
    ⟨(hKne.choose, 0), hKne.choose_spec, hε⟩
  obtain ⟨d, hdS, hdT, hdf, hdi⟩ := exists_openPartialHomeomorph_of_subtype
    (hK.prod isOpen_Iio) htarget hSne H
  refine ⟨d, hdS, hdT, ?_, ?_⟩
  · intro z hz
    have hz' : z ∈ K ×ˢ Iio ε := hdS ▸ hz
    rw [hdf z hz']
    exact he (⟨z.1, hz'.1⟩, ⟨z.2, hz'.2⟩)
  · intro q hq
    have hq' : q ∈ {q : IntervalCompletionSpace u a b | q.1.1 ∈ c.target} := hdT ▸ hq
    rw [hdi q hq']
    exact Prod.ext (hei ⟨q, hq'⟩).1 (hei ⟨q, hq'⟩).2

set_option backward.isDefEq.respectTransparency false in
theorem exists_upper_completionChart
    {u : M → ℝ} {a b ε : ℝ} {K : Set B} {i : B → M}
    (hK : IsOpen K) (hKne : K.Nonempty) (hε : 0 < ε) (hgap : a + ε < b)
    (c : OpenPartialHomeomorph (B × Ici (0 : ℝ)) M)
    (hsource : c.source = K ×ˢ {t : Ici (0 : ℝ) | t.1 < ε})
    (hzero : ∀ x ∈ K, c (x, ⟨0, show (0 : ℝ) ≤ 0 from le_rfl⟩) = i x)
    (hheight : ∀ z ∈ c.source, u (c z) = b - z.2.1) :
    ∃ d : OpenPartialHomeomorph (B × ℝ) (IntervalCompletionSpace u a b),
      d.source = K ×ˢ Ioi (-ε) ∧ d.target = {q | q.1.1 ∈ c.target} ∧
      (∀ z ∈ d.source, (d z).1 =
        (c (z.1, ⟨max 0 (-z.2), le_max_left 0 (-z.2)⟩), b + z.2)) ∧
      ∀ q ∈ d.target, d.symm q = ((c.symm q.1.1).1, q.1.2 - b) := by
  obtain ⟨e, he, hei⟩ := exists_upper_signed_collar hε hgap c hsource hzero hheight
  let H := (Homeomorph.Set.prod K (Ioi (-ε))).trans e
  have htarget : IsOpen {q : IntervalCompletionSpace u a b | q.1.1 ∈ c.target} :=
    c.open_target.preimage (continuous_fst.comp continuous_subtype_val)
  have hzeroTime : (0 : ℝ) ∈ Ioi (-ε) := neg_neg_of_pos hε
  obtain ⟨d, hdS, hdT, hdf, hdi⟩ := exists_openPartialHomeomorph_of_subtype
    (hK.prod isOpen_Ioi) htarget ⟨(hKne.choose, 0), hKne.choose_spec, hzeroTime⟩ H
  refine ⟨d, hdS, hdT, ?_, ?_⟩
  · intro z hz
    have hz' : z ∈ K ×ˢ Ioi (-ε) := hdS ▸ hz
    rw [hdf z hz']
    exact he (⟨z.1, hz'.1⟩, ⟨z.2, hz'.2⟩)
  · intro q hq
    have hq' : q ∈ {q : IntervalCompletionSpace u a b | q.1.1 ∈ c.target} := hdT ▸ hq
    rw [hdi q hq']
    exact Prod.ext (hei ⟨q, hq'⟩).1 (hei ⟨q, hq'⟩).2

end DifferentialGeometry.Topology.Ehresmann
