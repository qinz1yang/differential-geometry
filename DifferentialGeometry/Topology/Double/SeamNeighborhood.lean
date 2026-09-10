import DifferentialGeometry.Topology.Double.Seam

set_option autoImplicit false
noncomputable section
open Set Function Topology
namespace Poincare.Topology
variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  (B : Set X) (r : C(X, ℝ)) (hr : ∀ b : B, r b.val = 0)
  (hz : ∀ x, r x = 0 → x ∈ B) (hn : ∀ x, 0 ≤ r x)
  {ε : ℝ} (c : C(B × Icc (0 : ℝ) ε, X))
  (hheight : ∀ q, r (c q) = q.2.val)
  (hsmall : ∀ x, r x ≤ ε → x ∈ range c)

include hn hsmall in
theorem range_doubleSeam :
    range (doubleSeam B r hr hz c hheight) = {z | |doubleHeight B r hr z| ≤ ε} := by
  ext z
  constructor
  · rintro ⟨q, rfl⟩
    have hh := congrArg Prod.snd (doubleRealization_doubleSeam B r hr hz c hheight q)
    change doubleHeight B r hr (doubleSeam B r hr hz c hheight q) = q.2.val at hh
    change |doubleHeight B r hr (doubleSeam B r hr hz c hheight q)| ≤ ε
    rw [hh]
    exact abs_le.mpr q.2.property
  · intro hzband
    change |doubleHeight B r hr z| ≤ ε at hzband
    have hsmallz : r (doubleFold B z) ≤ ε := (abs_doubleHeight B r hr hn z) ▸ hzband
    obtain ⟨p, hp⟩ := hsmall (doubleFold B z) hsmallz
    let t : Icc (-ε) ε := ⟨doubleHeight B r hr z, abs_le.mp hzband⟩
    refine ⟨(p.1, t), (injective_doubleRealization B r hr hz) ?_⟩
    rw [doubleRealization_doubleSeam]
    refine Prod.ext ?_ rfl
    have ht : (⟨|t.val|, abs_nonneg _, abs_le.mpr t.property⟩ : Icc (0 : ℝ) ε) = p.2 := by
      apply Subtype.ext
      change |doubleHeight B r hr z| = p.2.val
      rw [abs_doubleHeight B r hr hn, ← hp, hheight]
    change c (p.1, _) = doubleFold B z
    rw [ht]
    exact hp


def doubleOpenSeam : C(B × Ioo (-ε) ε, Double B) :=
  (doubleSeam B r hr hz c hheight).comp
    ⟨fun q => (q.1, ⟨q.2.val, q.2.property.1.le, q.2.property.2.le⟩), by fun_prop⟩

include hn hsmall in
theorem range_doubleOpenSeam :
    range (doubleOpenSeam B r hr hz c hheight) = {z | |doubleHeight B r hr z| < ε} := by
  ext z
  constructor
  · rintro ⟨q, rfl⟩
    have hh := congrArg Prod.snd (doubleRealization_doubleSeam B r hr hz c hheight
      (q.1, ⟨q.2.val, q.2.property.1.le, q.2.property.2.le⟩))
    change doubleHeight B r hr (doubleOpenSeam B r hr hz c hheight q) = q.2.val at hh
    change |doubleHeight B r hr (doubleOpenSeam B r hr hz c hheight q)| < ε
    rw [hh]
    exact abs_lt.mpr q.2.property
  · intro hband
    change |doubleHeight B r hr z| < ε at hband
    obtain ⟨q, hq⟩ := (Set.ext_iff.mp (range_doubleSeam B r hr hz hn c hheight hsmall) z).mpr hband.le
    have hh := congrArg Prod.snd (doubleRealization_doubleSeam B r hr hz c hheight q)
    change doubleHeight B r hr (doubleSeam B r hr hz c hheight q) = q.2.val at hh
    rw [hq] at hh
    have ht : q.2.val ∈ Ioo (-ε) ε := abs_lt.mp (hh ▸ hband)
    refine ⟨(q.1, ⟨q.2.val, ht⟩), ?_⟩
    exact hq

include hn hsmall in
theorem isOpenEmbedding_doubleOpenSeam (hc : IsEmbedding c) :
    IsOpenEmbedding (doubleOpenSeam B r hr hz c hheight) := by
  have hi : IsEmbedding (fun q : Ioo (-ε) ε =>
      (⟨q.val, q.property.1.le, q.property.2.le⟩ : Icc (-ε) ε)) := by
    apply IsEmbedding.of_comp (by fun_prop) continuous_subtype_val
    exact IsEmbedding.subtypeVal
  refine ⟨(isEmbedding_doubleSeam B r hr hz c hheight hc).comp (IsEmbedding.id.prodMap hi), ?_⟩
  rw [range_doubleOpenSeam B r hr hz hn c hheight hsmall]
  exact isOpen_lt (doubleHeight B r hr).continuous.abs continuous_const


def doubleSeamHomeomorph (hc : IsEmbedding c) :
    B × Ioo (-ε) ε ≃ₜ {z : Double B | |doubleHeight B r hr z| < ε} :=
  (isOpenEmbedding_doubleOpenSeam B r hr hz hn c hheight hsmall hc).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (range_doubleOpenSeam B r hr hz hn c hheight hsmall))


theorem doubleSeamHomeomorph_apply (hc : IsEmbedding c) (q : B × Ioo (-ε) ε) :
    (doubleSeamHomeomorph B r hr hz hn c hheight hsmall hc q).val =
      doubleOpenSeam B r hr hz c hheight q := rfl


theorem doubleHeight_seamHomeomorph (hc : IsEmbedding c) (q : B × Ioo (-ε) ε) :
    doubleHeight B r hr (doubleSeamHomeomorph B r hr hz hn c hheight hsmall hc q).val = q.2.val :=
  congrArg Prod.snd (doubleRealization_doubleSeam B r hr hz c hheight
    (q.1, ⟨q.2.val, q.2.property.1.le, q.2.property.2.le⟩))


theorem doubleSeamHomeomorph_symm_height (hc : IsEmbedding c)
    (z : {z : Double B | |doubleHeight B r hr z| < ε}) :
    (doubleSeamHomeomorph B r hr hz hn c hheight hsmall hc).symm z |>.2.val =
      doubleHeight B r hr z.val := by
  have hh := doubleHeight_seamHomeomorph B r hr hz hn c hheight hsmall hc
    ((doubleSeamHomeomorph B r hr hz hn c hheight hsmall hc).symm z)
  rw [Homeomorph.apply_symm_apply] at hh
  exact hh.symm

end Poincare.Topology
