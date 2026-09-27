import DifferentialGeometry.Topology.Double.ClosedCover
import Mathlib.Topology.Homotopy.Equiv
import Mathlib.Topology.Piecewise

set_option autoImplicit false
noncomputable section
open Set Function Topology
namespace DifferentialGeometry.Topology

theorem exists_doublePositive_neighborhood_homotopyEquiv
    {X : Type} [TopologicalSpace X]
    (B : Set X) (r : C(X, ℝ)) (hr : ∀ b : B, r b.val = 0)
    (hn : ∀ x, 0 ≤ r x) (hz : ∀ x, r x = 0 → x ∈ B)
    {ε a : ℝ} (ha : 0 < a) (haε : a < ε)
    (s : B × Ioo (-ε) ε ≃ₜ {z : Double B | |doubleHeight B r hr z| < ε})
    (hs : ∀ q, doubleHeight B r hr (s q).val = q.2.val) :
    Nonempty (ContinuousMap.HomotopyEquiv {z : Double B | -a < doubleHeight B r hr z} X) := by
  classical
  let h := doubleHeight B r hr
  let U := {z : Double B | -a < h z}
  let E := {q : unitInterval × U | h q.2.val ≤ 0}
  have hε : 0 < ε := ha.trans haε
  let v : E → {z : Double B | |h z| < ε} := fun q =>
    ⟨q.val.2.val, abs_lt.mpr ⟨(neg_lt_neg haε).trans q.val.2.property, q.property.trans_lt hε⟩⟩
  have hv : Continuous v := by fun_prop
  let w : E → B × Ioo (-ε) ε := s.symm ∘ v
  have hw : Continuous w := s.symm.continuous.comp hv
  have hwt (q : E) : (w q).2.val = h q.val.2.val := by
    have hh := hs (w q)
    change h (s (s.symm (v q))).val = (w q).2.val at hh
    rw [s.apply_symm_apply] at hh
    exact hh.symm
  let t : E → ℝ := fun q => (1 - q.val.1.val) * (w q).2.val
  have ht (q : E) : h q.val.2.val ≤ t q ∧ t q ≤ 0 := by
    dsimp only [t]
    rw [hwt]
    have hq : h q.val.2.val ≤ 0 := q.property
    constructor
    · nlinarith [mul_nonpos_of_nonneg_of_nonpos q.val.1.property.1 hq]
    · exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr q.val.1.property.2) hq
  let k : E → B × Ioo (-ε) ε := fun q =>
    ((w q).1, ⟨t q, (neg_lt_neg haε).trans (q.val.2.property.trans_le (ht q).1), (ht q).2.trans_lt hε⟩)
  have hk : Continuous k := by
    have htt : Continuous t := (continuous_const.sub
      (continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val))).mul
      (continuous_subtype_val.comp (continuous_snd.comp hw))
    exact (continuous_fst.comp hw).prodMk (htt.subtype_mk _)
  have hgU (q : E) : (s (k q)).val ∈ U := by
    change -a < h (s (k q)).val
    rw [hs]
    exact q.val.2.property.trans_le (ht q).1
  let g : C(E, U) := ⟨fun q => ⟨(s (k q)).val, hgU q⟩,
    (continuous_subtype_val.comp (s.continuous.comp hk)).subtype_mk hgU⟩
  have hgheight (q : E) : h (g q).val = t q := hs (k q)
  have hgeq (q : E) (heq : t q = (w q).2.val) : g q = q.val.2 := by
    have hkw : k q = w q := Prod.ext rfl (Subtype.ext heq)
    apply Subtype.ext
    change (s (k q)).val = q.val.2.val
    rw [hkw]
    exact congrArg Subtype.val (s.apply_symm_apply (v q))
  have hgfix (q : E) (hq : h q.val.2.val = 0) : g q = q.val.2 := by
    apply hgeq
    change (1 - q.val.1.val) * (w q).2.val = (w q).2.val
    rw [hwt, hq, mul_zero]
  let G : unitInterval × U → U := fun q => if hq : h q.2.val ≤ 0 then g ⟨q, hq⟩ else q.2
  have hGneg : ContinuousOn G E := by
    rw [continuousOn_iff_continuous_domRestrict]
    apply g.continuous.congr
    intro q
    change g q = G q.val
    dsimp only [G]
    rw [dif_pos (show h q.val.2.val ≤ 0 from q.property)]
  have hGfix (q : unitInterval × U) (hq : 0 ≤ h q.2.val) : G q = q.2 := by
    dsimp only [G]
    split_ifs with hneg
    · exact hgfix ⟨q, hneg⟩ (le_antisymm hneg hq)
    · rfl
  have hGpos : ContinuousOn G {q : unitInterval × U | 0 ≤ h q.2.val} :=
    continuous_snd.continuousOn.congr (fun q hq => hGfix q hq)
  have hcover : E ∪ {q : unitInterval × U | 0 ≤ h q.2.val} = univ :=
    eq_univ_of_forall (fun q => le_total (h q.2.val) 0)
  have hGc : Continuous G := by
    rw [← continuousOn_univ, ← hcover]
    exact hGneg.union_of_isClosed hGpos
      (isClosed_le (h.continuous.comp (continuous_subtype_val.comp continuous_snd)) continuous_const)
      (isClosed_le continuous_const (h.continuous.comp (continuous_subtype_val.comp continuous_snd)))
  have hGzero (q : U) : G (0, q) = q := by
    dsimp only [G]
    split_ifs with hq
    · apply hgeq
      change (1 - (0 : ℝ)) * (w ⟨(0, q), hq⟩).2.val = (w ⟨(0, q), hq⟩).2.val
      ring
    · rfl
  have hGone (q : U) : 0 ≤ h (G (1, q)).val := by
    dsimp only [G]
    split_ifs with hq
    · rw [hgheight]
      change 0 ≤ (1 - (1 : ℝ)) * _
      simp
    · exact le_of_lt (lt_of_not_ge hq)
  let j : C(X, U) := ⟨fun x => ⟨doublePositive B x, (neg_lt_zero.mpr ha).trans_le (hn x)⟩,
    (doublePositive B).continuous.subtype_mk _⟩
  let R : C(U, X) := ⟨fun q => doubleFold B (G (1, q)).val,
    (doubleFold B).continuous.comp (continuous_subtype_val.comp (hGc.comp (continuous_const.prodMk continuous_id)))⟩
  have hposval (q : U) : j (R q) = G (1, q) := by
    obtain ⟨x, hx⟩ := (Set.ext_iff.mp (range_doublePositive B r hr hn hz) (G (1, q)).val).mpr (hGone q)
    apply Subtype.ext
    change doublePositive B (doubleFold B (G (1, q)).val) = (G (1, q)).val
    rw [← hx, doubleFold_positive]
  let H : (ContinuousMap.id U).Homotopy (j.comp R) :=
    ⟨⟨G, hGc⟩, hGzero, fun q => (hposval q).symm⟩
  refine ⟨⟨R, j, ⟨H.symm⟩, ?_⟩⟩
  have hRj : R.comp j = ContinuousMap.id X := by
    ext x
    change doubleFold B (G (1, j x)).val = x
    rw [hGfix (1, j x) (hn x)]
    rfl
  simpa only [hRj] using ContinuousMap.Homotopic.refl (ContinuousMap.id X)

end DifferentialGeometry.Topology
