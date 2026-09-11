import DifferentialGeometry.Topology.Double.SeamNeighborhood
import Mathlib.Topology.OpenPartialHomeomorph.Composition

set_option autoImplicit false
noncomputable section
open Set Function Topology TopologicalSpace
namespace DifferentialGeometry.Topology
variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  (B : Set X) (r : C(X, ℝ)) (hr : ∀ b : B, r b.val = 0)
  (hz : ∀ x, r x = 0 → x ∈ B) (hn : ∀ x, 0 ≤ r x)
  {a : ℝ} (c : C(B × Icc (0 : ℝ) a, X))
  (hheight : ∀ q, r (c q) = q.2.val)
  (hsmall : ∀ x, r x ≤ a → x ∈ range c) (hc : IsEmbedding c)


def doubleRealSeamHomeomorph :
    {q : B × ℝ | |q.2| < a} ≃ₜ {z : Double B | |doubleHeight B r hr z| < a} :=
  (show {q : B × ℝ | |q.2| < a} ≃ₜ B × Ioo (-a) a from
    { toFun := fun q => (q.val.1, ⟨q.val.2, abs_lt.mp q.property⟩)
      invFun := fun q => ⟨(q.1, q.2.val), abs_lt.mpr q.2.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }).trans
    (doubleSeamHomeomorph B r hr hz hn c hheight hsmall hc)


theorem doubleHeight_realSeamHomeomorph (q : {q : B × ℝ | |q.2| < a}) :
    doubleHeight B r hr (doubleRealSeamHomeomorph B r hr hz hn c hheight hsmall hc q).val =
      q.val.2 :=
  doubleHeight_seamHomeomorph B r hr hz hn c hheight hsmall hc _


def doubleSeamPatch (ha : 0 < a) (b : B) : OpenPartialHomeomorph (B × ℝ) (Double B) :=
  let P : Opens (B × ℝ) := ⟨{q | |q.2| < a}, isOpen_lt continuous_snd.abs continuous_const⟩
  let W : Opens (Double B) :=
    ⟨{z | |doubleHeight B r hr z| < a},
      isOpen_lt (doubleHeight B r hr).continuous.abs continuous_const⟩
  let p : P := ⟨(b, 0), by change |(0 : ℝ)| < a; simpa using ha⟩
  let s := doubleRealSeamHomeomorph B r hr hz hn c hheight hsmall hc
  (P.openPartialHomeomorphSubtypeCoe ⟨p⟩).symm.trans
    (s.toOpenPartialHomeomorph.trans (W.openPartialHomeomorphSubtypeCoe ⟨s p⟩))


theorem doubleSeamPatch_source (ha : 0 < a) (b : B) :
    (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b).source = {q | |q.2| < a} := by
  simp [doubleSeamPatch]


theorem doubleSeamPatch_target (ha : 0 < a) (b : B) :
    (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b).target =
      {z | |doubleHeight B r hr z| < a} := by
  simp [doubleSeamPatch]


theorem doubleSeamPatch_apply (ha : 0 < a) (b : B) {q : B × ℝ} (hq : |q.2| < a) :
    doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b q =
      (doubleRealSeamHomeomorph B r hr hz hn c hheight hsmall hc ⟨q, hq⟩).val := by
  let P : Opens (B × ℝ) := ⟨{q | |q.2| < a}, isOpen_lt continuous_snd.abs continuous_const⟩
  let p : P := ⟨(b, 0), by change |(0 : ℝ)| < a; simpa using ha⟩
  have hh : (P.openPartialHomeomorphSubtypeCoe ⟨p⟩).symm q = ⟨q, hq⟩ :=
    (P.openPartialHomeomorphSubtypeCoe ⟨p⟩).left_inv (x := ⟨q, hq⟩) trivial
  change (doubleRealSeamHomeomorph B r hr hz hn c hheight hsmall hc
    ((P.openPartialHomeomorphSubtypeCoe ⟨p⟩).symm q)).val = _
  rw [hh]


theorem doubleHeight_seamPatch (ha : 0 < a) (b : B) {q : B × ℝ} (hq : |q.2| < a) :
    doubleHeight B r hr (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b q) = q.2 := by
  rw [doubleSeamPatch_apply B r hr hz hn c hheight hsmall hc ha b hq]
  exact doubleHeight_realSeamHomeomorph B r hr hz hn c hheight hsmall hc _


theorem doubleSeamPatch_symm_height (ha : 0 < a) (b : B) {z : Double B}
    (hz' : |doubleHeight B r hr z| < a) :
    ((doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b).symm z).2 =
      doubleHeight B r hr z := by
  let e := doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b
  have hzt : z ∈ e.target := by rw [doubleSeamPatch_target]; exact hz'
  have hq : |(e.symm z).2| < a := by
    have hh := e.map_target hzt
    rwa [doubleSeamPatch_source] at hh
  have hh := doubleHeight_realSeamHomeomorph B r hr hz hn c hheight hsmall hc ⟨e.symm z, hq⟩
  rw [← doubleSeamPatch_apply B r hr hz hn c hheight hsmall hc ha b hq] at hh
  change doubleHeight B r hr (e (e.symm z)) = _ at hh
  rw [e.right_inv hzt] at hh
  exact hh.symm

theorem doubleSeamPatch_of_nonneg (ha : 0 < a) (b : B) {q : B × ℝ}
    (hq : |q.2| < a) (ht : 0 ≤ q.2) :
    doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b q =
      doublePositive B (c (q.1, ⟨q.2, ht, (le_abs_self q.2).trans hq.le⟩)) := by
  classical
  rw [doubleSeamPatch_apply B r hr hz hn c hheight hsmall hc ha b hq]
  change (if 0 ≤ q.2 then doublePositive B (c _) else doubleNegative B (c _)) = _
  rw [if_pos ht]
  apply congrArg (fun p => doublePositive B (c p))
  exact Prod.ext rfl (Subtype.ext (abs_of_nonneg ht))

theorem doubleSeamPatch_of_neg (ha : 0 < a) (b : B) {q : B × ℝ}
    (hq : |q.2| < a) (ht : q.2 < 0) :
    doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b q =
      doubleNegative B (c (q.1, ⟨-q.2, (neg_pos.mpr ht).le,
        (neg_le_abs q.2).trans hq.le⟩)) := by
  classical
  rw [doubleSeamPatch_apply B r hr hz hn c hheight hsmall hc ha b hq]
  change (if 0 ≤ q.2 then doublePositive B (c _) else doubleNegative B (c _)) = _
  rw [if_neg (not_le.mpr ht)]
  apply congrArg (fun p => doubleNegative B (c p))
  exact Prod.ext rfl (Subtype.ext (abs_of_neg ht))

theorem doubleSeamPatch_of_nonpos (ha : 0 < a) (b : B) {q : B × ℝ}
    (hq : |q.2| < a) (ht : q.2 ≤ 0) :
    doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b q =
      doubleNegative B (c (q.1, ⟨-q.2, neg_nonneg.mpr ht,
        (neg_le_abs q.2).trans hq.le⟩)) := by
  rcases lt_or_eq_of_le ht with ht | ht
  · exact doubleSeamPatch_of_neg B r hr hz hn c hheight hsmall hc ha b hq ht
  · have htp : 0 ≤ q.2 := ht ▸ le_rfl
    rw [doubleSeamPatch_of_nonneg B r hr hz hn c hheight hsmall hc ha b hq htp]
    have hp : (q.1, (⟨-q.2, neg_nonneg.mpr ht.le, (neg_le_abs q.2).trans hq.le⟩ : Icc (0 : ℝ) a)) =
        (q.1, ⟨q.2, htp, (le_abs_self q.2).trans hq.le⟩) := by
      have heq : -q.2 = q.2 := by rw [ht, neg_zero]
      exact Prod.ext rfl (Subtype.ext heq)
    rw [hp]
    exact double_seam B ⟨_, hz _ ((hheight _).trans ht)⟩


theorem doubleSeamPatch_transition_apply (ha : 0 < a) (b b' : B) {q : B × ℝ}
    (hq : q ∈ ((doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b).trans
      (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b').symm).source) :
    ((doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b).trans
      (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b').symm) q = q := by
  have hqa : |q.2| < a := by
    have hh := hq.1
    change q ∈ (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b).source at hh
    rwa [doubleSeamPatch_source] at hh
  have heq : doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b q =
      doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b' q := by
    rw [doubleSeamPatch_apply B r hr hz hn c hheight hsmall hc ha b hqa,
      doubleSeamPatch_apply B r hr hz hn c hheight hsmall hc ha b' hqa]
  change (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b').symm
    (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b q) = q
  rw [heq]
  apply OpenPartialHomeomorph.left_inv
  rw [doubleSeamPatch_source]
  exact hqa

end DifferentialGeometry.Topology
