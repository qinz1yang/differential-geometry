import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.FunProp

set_option autoImplicit false
noncomputable section
open Set Function Topology
namespace Poincare.Topology


def heightBandHomeomorph
    {B X : Type*} [TopologicalSpace B] [TopologicalSpace X]
    (h : C(X, ℝ)) {a ε : ℝ} (haε : a ≤ ε)
    (s : B × Ioo (-ε) ε ≃ₜ {x : X | |h x| < ε})
    (hs : ∀ q, h (s q).val = q.2.val) :
    B × Ioo (-a) a ≃ₜ {x : X | |h x| < a} := by
  let i : B × Ioo (-a) a → B × Ioo (-ε) ε := fun q =>
    (q.1, ⟨q.2.val, (neg_le_neg haε).trans_lt q.2.property.1, q.2.property.2.trans_le haε⟩)
  let v : {x : X | |h x| < a} → {x : X | |h x| < ε} := fun x =>
    ⟨x.val, x.property.trans_le haε⟩
  have hcoord (x : {x : X | |h x| < a}) : (s.symm (v x)).2.val = h x.val := by
    have hh := hs (s.symm (v x))
    rw [s.apply_symm_apply] at hh
    exact hh.symm
  let f : B × Ioo (-a) a → {x : X | |h x| < a} := fun q =>
    ⟨(s (i q)).val, by change |h (s (i q)).val| < a; rw [hs]; exact abs_lt.mpr q.2.property⟩
  let g : {x : X | |h x| < a} → B × Ioo (-a) a := fun x =>
    ((s.symm (v x)).1, ⟨(s.symm (v x)).2.val, abs_lt.mp ((hcoord x).symm ▸ x.property)⟩)
  have hfi (q : B × Ioo (-a) a) : v (f q) = s (i q) := rfl
  have hgi (x : {x : X | |h x| < a}) : i (g x) = s.symm (v x) := rfl
  have hgf (q : B × Ioo (-a) a) : g (f q) = q := by
    have hh : i (g (f q)) = i q := by rw [hgi, hfi, s.symm_apply_apply]
    have hb : (g (f q)).1 = q.1 := congrArg (fun z : B × Ioo (-ε) ε => z.1) hh
    have ht : (g (f q)).2.val = q.2.val := congrArg (fun z : B × Ioo (-ε) ε => z.2.val) hh
    exact Prod.ext hb (Subtype.ext ht)
  have hfg (x : {x : X | |h x| < a}) : f (g x) = x := by
    apply Subtype.ext
    change (s (i (g x))).val = x.val
    rw [hgi, s.apply_symm_apply]
  have hf : Continuous f := by
    have hi : Continuous i := by fun_prop
    exact (continuous_subtype_val.comp (s.continuous.comp hi)).subtype_mk _
  have hg : Continuous g := by
    have hv : Continuous v := by fun_prop
    have hw := s.symm.continuous.comp hv
    exact (continuous_fst.comp hw).prodMk
      ((continuous_subtype_val.comp (continuous_snd.comp hw)).subtype_mk _)
  exact ⟨⟨f, g, hgf, hfg⟩, hf, hg⟩

end Poincare.Topology
