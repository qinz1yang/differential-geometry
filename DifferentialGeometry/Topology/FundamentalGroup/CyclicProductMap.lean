/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.FundamentalGroup.Nullhomotopy
import DifferentialGeometry.Topology.FundamentalGroup.Product
import Mathlib.Algebra.Group.Equiv.TypeTags

namespace DifferentialGeometry.Topology

private theorem injective_cyclic_hom_of_surjective
    {G H : Type*} [Group G] [Group H]
    (eG : G ≃* Multiplicative ℤ) (eH : H ≃* Multiplicative ℤ)
    (f : G →* H) (hf : Function.Surjective f) : Function.Injective f := by
  let F := eH.toMonoidHom.comp (f.comp eG.symm.toMonoidHom)
  let a : ℤ →+ ℤ := MonoidHom.toAdditiveRight F
  have ha : Function.Surjective a := eH.surjective.comp (hf.comp eG.symm.surjective)
  have hlin (n : ℤ) : a n = n * a 1 := by
    conv_lhs => rw [show n = n • (1 : ℤ) by simp]
    rw [map_zsmul]
    simp
  obtain ⟨n, hn⟩ := ha 1
  have hne : a 1 ≠ 0 := by
    intro h
    rw [hlin, h, mul_zero] at hn
    exact zero_ne_one hn
  have hi : Function.Injective a := by
    intro u v huv
    rw [hlin u, hlin v] at huv
    exact mul_right_cancel₀ hne huv
  intro u v huv
  apply eG.injective
  apply Multiplicative.toAdd.injective
  apply hi
  change (eH (f (eG.symm (eG u)))).toAdd = (eH (f (eG.symm (eG v)))).toAdd
  rw [eG.symm_apply_apply, eG.symm_apply_apply, huv]

theorem surjective_fundamentalGroup_snd_of_nullhomotopic_fiber
    {X M Q T : Type*} [TopologicalSpace X] [TopologicalSpace M]
    [TopologicalSpace Q] [TopologicalSpace T]
    (f : C(M × Q, T)) (g : C(X, M × Q)) (x : X)
    (eQ : FundamentalGroup Q (g x).2 ≃* Multiplicative ℤ)
    (eT : FundamentalGroup T (f (g x)) ≃* Multiplicative ℤ)
    (hnull : (f.comp (ContinuousMap.prodMk (ContinuousMap.id M)
      (ContinuousMap.const M (g x).2))).Nullhomotopic)
    (honto : Function.Surjective (FundamentalGroup.map (f.comp g) x)) :
    Function.Surjective (FundamentalGroup.map (ContinuousMap.snd.comp g) x) := by
  let p := g x
  let e := fundamentalGroupProdEquiv p.1 p.2
  let l : C(M, M × Q) := ContinuousMap.prodMk (ContinuousMap.id M)
    (ContinuousMap.const M p.2)
  let F := FundamentalGroup.map f p
  let L : FundamentalGroup Q p.2 →* FundamentalGroup T (f p) :=
    F.comp (e.symm.toMonoidHom.comp
      (MonoidHom.inr (FundamentalGroup M p.1) (FundamentalGroup Q p.2)))
  have hleft (a : FundamentalGroup M p.1) :
      e.symm (a, 1) = FundamentalGroup.map l p.1 a := by
    rw [fundamentalGroupProdEquiv_symm_apply]
    induction a using Path.Homotopic.Quotient.ind with
    | mk a =>
      change Path.Homotopic.Quotient.mk (a.prod (Path.refl p.2)) =
        Path.Homotopic.Quotient.mk (a.map l.continuous)
      congr 1
  have hkill (a : FundamentalGroup M p.1) : F (e.symm (a, 1)) = 1 := by
    rw [hleft]
    exact (Path.Homotopic.Quotient.map_comp).symm.trans
      (fundamentalGroup_map_eq_one_of_nullhomotopic (f.comp l) hnull p.1 a)
  have hfactor (a : FundamentalGroup (M × Q) p) :
      F a = L (FundamentalGroup.map ContinuousMap.snd p a) := by
    have hsplit : a = e.symm ((e a).1, 1) * e.symm (1, (e a).2) := by
      apply e.injective
      simp only [map_mul, MulEquiv.apply_symm_apply, Prod.mk_mul_mk, mul_one, one_mul,
        Prod.mk.eta]
    calc
      F a = F (e.symm ((e a).1, 1) * e.symm (1, (e a).2)) := congrArg F hsplit
      _ = F (e.symm (1, (e a).2)) := by rw [map_mul, hkill, one_mul]
      _ = L (FundamentalGroup.map ContinuousMap.snd p a) := rfl
  have hcomp (a : FundamentalGroup X x) :
      FundamentalGroup.map (f.comp g) x a =
        L (FundamentalGroup.map (ContinuousMap.snd.comp g) x a) := by
    exact Path.Homotopic.Quotient.map_comp.trans
      ((hfactor (FundamentalGroup.map g x a)).trans
        (congrArg L Path.Homotopic.Quotient.map_comp.symm))
  have hL : Function.Surjective L := by
    intro a
    obtain ⟨b, hb⟩ := honto a
    exact ⟨FundamentalGroup.map (ContinuousMap.snd.comp g) x b, (hcomp b).symm.trans hb⟩
  have hLi := injective_cyclic_hom_of_surjective eQ eT L hL
  intro a
  obtain ⟨b, hb⟩ := honto (L a)
  exact ⟨b, hLi ((hcomp b).symm.trans hb)⟩

end DifferentialGeometry.Topology
