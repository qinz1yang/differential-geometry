import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.UrysohnsLemma
import Mathlib.Topology.Connected.Clopen

section

set_option autoImplicit false
noncomputable section

open Set Filter Topology
open scoped Topology

namespace DifferentialGeometry.Topology

private theorem eq_const_of_continuousAt_of_mem_closure
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
    {f : X → Y} {S : Set X} {x : X} {c : Y} (hf : ContinuousAt f x)
    (hx : x ∈ closure S) (hconst : ∀ y ∈ S, f y = c) : f x = c := by
  have hmem : f x ∈ closure (f '' S) := hf.continuousWithinAt.mem_closure_image hx
  have hsub : f '' S ⊆ {c} := by rintro _ ⟨y, hy, rfl⟩; exact hconst y hy
  have h := closure_mono hsub hmem
  simpa only [closure_singleton, mem_singleton_iff] using h

theorem not_disconnected_zero_level_of_continuous_logarithms
    {X : Type*} [TopologicalSpace X] {f g : X → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hp : IsPreconnected {x | 0 < f x}) (hn : IsPreconnected {x | f x < 0})
    {a b : X} (hfa : f a = 0) (hfb : f b = 0) (hga : g a = 0) (hgb : g b = 1)
    (haP : a ∈ closure {x | 0 < f x}) (hbP : b ∈ closure {x | 0 < f x})
    (haN : a ∈ closure {x | f x < 0}) (hbN : b ∈ closure {x | f x < 0})
    (hlog : ∃ L : C(X, ℂ), ∀ x, Complex.exp (L x) =
      (⟨f x, 2 * g x - 1⟩ : ℂ)) : False := by
  obtain ⟨L, hL⟩ := hlog
  let h : X → ℂ := fun x => ⟨f x, 2 * g x - 1⟩
  have hc : Continuous h := by
    have h' : Continuous (fun x => (f x : ℂ) + ((2 * g x - 1 : ℝ) : ℂ) * Complex.I) :=
      (Complex.continuous_ofReal.comp hf).add
        ((Complex.continuous_ofReal.comp ((continuous_const.mul hg).sub continuous_const)).mul
          continuous_const)
    convert h' using 1
    funext x
    exact (Complex.re_add_im (h x)).symm
  have ha : h a = -Complex.I := by apply Complex.ext <;> simp [h, hfa, hga]
  have hb : h b = Complex.I := by apply Complex.ext <;> norm_num [h, hfb, hgb]
  let dp : X → ℂ := fun x => L x - Complex.log (h x)
  let dn : X → ℂ := fun x => L x - (Complex.log (-h x) + (Real.pi : ℂ) * Complex.I)
  have hpslit (x) (hx : 0 < f x) : h x ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_iff.mpr (Or.inl hx)
  have hnslit (x) (hx : f x < 0) : -h x ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_iff.mpr (Or.inl (by change 0 < -(f x); linarith))
  have hdp : ContinuousOn dp {x | 0 < f x} :=
    L.continuous.continuousOn.sub (hc.continuousOn.clog hpslit)
  have hdn : ContinuousOn dn {x | f x < 0} :=
    L.continuous.continuousOn.sub ((hc.neg.continuousOn.clog hnslit).add continuousOn_const)
  have hexpP (x) (hx : 0 < f x) : Complex.exp (dp x) = 1 := by
    change Complex.exp (L x - Complex.log (h x)) = 1
    rw [Complex.exp_sub, hL, Complex.exp_log (Complex.slitPlane_ne_zero (hpslit x hx))]
    exact div_self (Complex.slitPlane_ne_zero (hpslit x hx))
  have hexpN (x) (hx : f x < 0) : Complex.exp (dn x) = 1 := by
    have hh : Complex.exp (Complex.log (-h x) + (Real.pi : ℂ) * Complex.I) = h x := by
      rw [Complex.exp_add, Complex.exp_log (Complex.slitPlane_ne_zero (hnslit x hx)),
        Complex.exp_pi_mul_I, neg_mul_neg, mul_one]
    change Complex.exp (L x - (Complex.log (-h x) + (Real.pi : ℂ) * Complex.I)) = 1
    rw [Complex.exp_sub, hh, hL]
    have hn0 : h x ≠ 0 := fun hz => Complex.slitPlane_ne_zero (hnslit x hx) (by rw [hz, neg_zero])
    exact div_self hn0
  obtain ⟨xP, hxP⟩ : ({x | 0 < f x} : Set X).Nonempty := by
    by_contra hnone
    rw [not_nonempty_iff_eq_empty.mp hnone, closure_empty] at haP
    exact haP
  obtain ⟨xN, hxN⟩ : ({x | f x < 0} : Set X).Nonempty := by
    by_contra hnone
    rw [not_nonempty_iff_eq_empty.mp hnone, closure_empty] at haN
    exact haN
  have hdpconst : ∀ x ∈ {x | 0 < f x}, dp x = dp xP := by
    intro x hx
    exact Complex.isCoveringMap_exp.constOn_of_comp hp hdp
      (fun y hy z hz => Subtype.ext ((hexpP y hy).trans (hexpP z hz).symm)) hx hxP
  have hdnconst : ∀ x ∈ {x | f x < 0}, dn x = dn xN := by
    intro x hx
    exact Complex.isCoveringMap_exp.constOn_of_comp hn hdn
      (fun y hy z hz => Subtype.ext ((hexpN y hy).trans (hexpN z hz).symm)) hx hxN
  have hIa : h a ∈ Complex.slitPlane := by rw [ha]; simp [Complex.mem_slitPlane_iff]
  have hIb : h b ∈ Complex.slitPlane := by rw [hb]; simp [Complex.mem_slitPlane_iff]
  have hnIa : -h a ∈ Complex.slitPlane := by rw [ha, neg_neg]; simp [Complex.mem_slitPlane_iff]
  have hnIb : -h b ∈ Complex.slitPlane := by rw [hb]; simp [Complex.mem_slitPlane_iff]
  have hpa : dp a = dp xP := eq_const_of_continuousAt_of_mem_closure
    (L.continuous.continuousAt.sub (hc.continuousAt.clog hIa)) haP hdpconst
  have hpb : dp b = dp xP := eq_const_of_continuousAt_of_mem_closure
    (L.continuous.continuousAt.sub (hc.continuousAt.clog hIb)) hbP hdpconst
  have hna : dn a = dn xN := eq_const_of_continuousAt_of_mem_closure
    (L.continuous.continuousAt.sub ((hc.neg.continuousAt.clog hnIa).add continuousAt_const))
    haN hdnconst
  have hnb : dn b = dn xN := eq_const_of_continuousAt_of_mem_closure
    (L.continuous.continuousAt.sub ((hc.neg.continuousAt.clog hnIb).add continuousAt_const))
    hbN hdnconst
  have hpab := hpa.trans hpb.symm
  have hnab := hna.trans hnb.symm
  have heq : Complex.log (h a) - (Complex.log (-h a) + (Real.pi : ℂ) * Complex.I) =
      Complex.log (h b) - (Complex.log (-h b) + (Real.pi : ℂ) * Complex.I) := by
    dsimp only [dp, dn] at hpab hnab
    linear_combination hnab - hpab
  rw [ha, hb, neg_neg, Complex.log_neg_I, Complex.log_I] at heq
  have him := congrArg Complex.im heq
  simp only [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero,
    Complex.neg_im, Complex.div_im, Complex.div_re] at him
  norm_num at him
  linarith [Real.pi_pos]

end DifferentialGeometry.Topology

end

end

section

set_option autoImplicit false
noncomputable section

open Set Filter Topology
open scoped Topology

namespace DifferentialGeometry.Topology

theorem Continuous.isPreconnected_zero_level_of_sign_connectedness
    {X : Type*} [TopologicalSpace X] [NormalSpace X] [SimplyConnectedSpace X]
    [LocallyPathConnectedSpace X] {f : X → ℝ} (hf : Continuous f)
    (hp : IsPreconnected {x | 0 < f x}) (hn : IsPreconnected {x | f x < 0})
    (hclosure : {x | f x = 0} ⊆ closure {x | 0 < f x} ∩ closure {x | f x < 0}) :
    IsPreconnected {x | f x = 0} := by
  have hZ : IsClosed {x | f x = 0} := isClosed_eq hf continuous_const
  apply (isPreconnected_iff_subset_of_fully_disjoint_closed hZ).mpr
  intro A B hA hB hcover hdisj
  by_contra hnot
  have hnot' := not_or.mp hnot
  obtain ⟨a, hfa, haA⟩ := Set.not_subset.mp hnot'.1
  obtain ⟨b, hfb, hbB⟩ := Set.not_subset.mp hnot'.2
  have haB : a ∈ B := (hcover hfa).resolve_left haA
  have hbA : b ∈ A := (hcover hfb).resolve_right hbB
  obtain ⟨g, hgA, hgB, _⟩ := exists_continuous_zero_one_of_isClosed hA hB hdisj
  let h : X → ℂ := fun x => ⟨f x, 2 * g x - 1⟩
  have hh : Continuous h := by
    have h' : Continuous
        (fun x => (f x : ℂ) + ((2 * g x - 1 : ℝ) : ℂ) * Complex.I) :=
      (Complex.continuous_ofReal.comp hf).add
        ((Complex.continuous_ofReal.comp
          ((continuous_const.mul g.continuous).sub continuous_const)).mul
          continuous_const)
    convert h' using 1
    funext x
    exact (Complex.re_add_im (h x)).symm
  have hne (x : X) : h x ≠ 0 := by
    intro hx
    have hfx : f x = 0 := congrArg Complex.re hx
    have hgx : 2 * g x - 1 = 0 := congrArg Complex.im hx
    rcases hcover hfx with hxA | hxB
    · have hg0 : g x = 0 := hgA hxA
      rw [hg0] at hgx
      norm_num at hgx
    · have hg1 : g x = 1 := hgB hxB
      rw [hg1] at hgx
      norm_num at hgx
  let H : C(X, {z : ℂ // z ≠ 0}) := ⟨fun x => ⟨h x, hne x⟩, hh.subtype_mk _⟩
  obtain ⟨L, ⟨_, hL⟩, _⟩ := Complex.isCoveringMap_exp.existsUnique_continuousMap_lifts
    H a (Complex.log (h a)) (Subtype.ext (Complex.exp_log (hne a)))
  have hlog : ∃ L : C(X, ℂ), ∀ x, Complex.exp (L x) = (⟨f x, 2 * g x - 1⟩ : ℂ) := by
    refine ⟨L, ?_⟩
    intro x
    exact congrArg Subtype.val (congrFun hL x)
  have hcA := hclosure hfb
  have hcB := hclosure hfa
  exact not_disconnected_zero_level_of_continuous_logarithms hf g.continuous hp hn hfb hfa
    (hgA hbA) (hgB haB) hcA.1 hcB.1 hcA.2 hcB.2 hlog

theorem Continuous.isPreconnected_level_of_sign_connectedness
    {X : Type*} [TopologicalSpace X] [NormalSpace X] [SimplyConnectedSpace X]
    [LocallyPathConnectedSpace X] {f : X → ℝ} (hf : Continuous f) (c : ℝ)
    (hp : IsPreconnected {x | c < f x}) (hn : IsPreconnected {x | f x < c})
    (hclosure : {x | f x = c} ⊆ closure {x | c < f x} ∩ closure {x | f x < c}) :
    IsPreconnected {x | f x = c} := by
  have h := Continuous.isPreconnected_zero_level_of_sign_connectedness
    (hf.sub (continuous_const (y := c)))
    (by simpa only [Pi.sub_apply, sub_pos] using hp)
    (by simpa only [Pi.sub_apply, sub_neg] using hn)
    (by simpa only [Pi.sub_apply, sub_eq_zero, sub_pos, sub_neg] using hclosure)
  simpa only [Pi.sub_apply, sub_eq_zero] using h

end DifferentialGeometry.Topology

end

end
