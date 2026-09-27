/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.GeneralPosition
import DifferentialGeometry.Topology.InvarianceOfDomainManifold

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

private theorem exists_homeomorph_sub_first {a : ℝ × ℝ → ℝ}
    (ha : IsPiecewiseAffineOn a univ) :
    ∃ e : (ℝ × ℝ × ℝ) ≃ₜ (ℝ × ℝ × ℝ),
      (∀ p, e p = (p.1 - a (p.2.1, p.2.2), p.2.1, p.2.2)) ∧
        IsPLHomeomorphOn e univ univ := by
  let F : ℝ × ℝ × ℝ → ℝ × ℝ × ℝ :=
    fun p => (p.1 - a (p.2.1, p.2.2), p.2.1, p.2.2)
  let G : ℝ × ℝ × ℝ → ℝ × ℝ × ℝ :=
    fun p => (p.1 + a (p.2.1, p.2.2), p.2.1, p.2.2)
  have hFG : Function.LeftInverse G F := by
    rintro ⟨u, v, t⟩
    dsimp [F, G]
    apply Prod.ext
    · ring_nf
    · apply Prod.ext <;> rfl
  have hGF : Function.RightInverse G F := by
    rintro ⟨u, v, t⟩
    dsimp [F, G]
    apply Prod.ext
    · ring_nf
    · apply Prod.ext <;> rfl
  have hacont : Continuous a :=
    continuous_iff_continuousAt.2 fun q => ha.continuousAt isOpen_univ (mem_univ q)
  have hFcont : Continuous F := by
    have hcoord : Continuous (fun p : ℝ × ℝ × ℝ => (p.2.1, p.2.2)) :=
      continuous_snd.fst.prodMk continuous_snd.snd
    have hfirst : Continuous (fun p : ℝ × ℝ × ℝ => p.1 - a (p.2.1, p.2.2)) :=
      continuous_fst.sub (hacont.comp hcoord)
    exact hfirst.prodMk (continuous_snd.fst.prodMk continuous_snd.snd)
  have hGcont : Continuous G := by
    have hcoord : Continuous (fun p : ℝ × ℝ × ℝ => (p.2.1, p.2.2)) :=
      continuous_snd.fst.prodMk continuous_snd.snd
    have hfirst : Continuous (fun p : ℝ × ℝ × ℝ => p.1 + a (p.2.1, p.2.2)) :=
      continuous_fst.add (hacont.comp hcoord)
    exact hfirst.prodMk (continuous_snd.fst.prodMk continuous_snd.snd)
  let e : (ℝ × ℝ × ℝ) ≃ₜ (ℝ × ℝ × ℝ) :=
    { toFun := F
      invFun := G
      left_inv := hFG
      right_inv := hGF
      continuous_toFun := hFcont
      continuous_invFun := hGcont }
  have hfst : IsPiecewiseAffineOn (fun p : ℝ × ℝ × ℝ => p.1) univ :=
    isPiecewiseAffineOn_of_affine (LinearMap.fst ℝ ℝ (ℝ × ℝ)).toAffineMap isOpen_univ
  have hmid : IsPiecewiseAffineOn (fun p : ℝ × ℝ × ℝ => p.2.1) univ :=
    isPiecewiseAffineOn_of_affine
      ((LinearMap.fst ℝ ℝ ℝ).comp (LinearMap.snd ℝ ℝ (ℝ × ℝ))).toAffineMap isOpen_univ
  have hlast : IsPiecewiseAffineOn (fun p : ℝ × ℝ × ℝ => p.2.2) univ :=
    isPiecewiseAffineOn_of_affine
      ((LinearMap.snd ℝ ℝ ℝ).comp (LinearMap.snd ℝ ℝ (ℝ × ℝ))).toAffineMap isOpen_univ
  have hcoord : IsPiecewiseAffineOn (fun p : ℝ × ℝ × ℝ => (p.2.1, p.2.2)) univ :=
    hmid.prod_mk hlast
  have ha' : IsPiecewiseAffineOn (fun p : ℝ × ℝ × ℝ => a (p.2.1, p.2.2)) univ := by
    have h := ha.comp hcoord
    rw [preimage_univ, inter_univ] at h
    exact h.congr fun _ _ => rfl
  have hfirstF : IsPiecewiseAffineOn (fun p : ℝ × ℝ × ℝ =>
      p.1 - a (p.2.1, p.2.2)) univ := by
    have hneg := ha'.affine_comp (-AffineMap.id ℝ ℝ)
    have hneg' : IsPiecewiseAffineOn (fun p : ℝ × ℝ × ℝ =>
        -a (p.2.1, p.2.2)) univ :=
      hneg.congr fun _ _ => rfl
    exact (hfst.add hneg').congr fun _ _ => by simp only [sub_eq_add_neg]
  have hfirstG : IsPiecewiseAffineOn (fun p : ℝ × ℝ × ℝ =>
      p.1 + a (p.2.1, p.2.2)) univ :=
    hfst.add ha'
  have hFpl : IsPiecewiseAffineOn F univ :=
    (hfirstF.prod_mk (hmid.prod_mk hlast)).congr fun _ _ => rfl
  have hGpl : IsPiecewiseAffineOn G univ :=
    (hfirstG.prod_mk (hmid.prod_mk hlast)).congr fun _ _ => rfl
  have hbij : Function.Bijective F := ⟨hFG.injective, hGF.surjective⟩
  have hplinv : IsPiecewiseAffineOn e.symm univ := by
    have heq : EqOn e.symm G univ := fun _ _ => rfl
    exact hGpl.congr heq.symm
  refine ⟨e, fun p => rfl, ?_⟩
  refine ⟨hbij.bijOn_univ, hFpl, ?_⟩
  apply hplinv.congr
  intro y hy
  apply e.injective
  change F (Function.invFunOn F univ y) = F (e.symm y)
  exact (hbij.bijOn_univ.invOn_invFunOn.2 hy).trans (e.apply_symm_apply y).symm

private theorem exists_homeomorph_sub_middle_contracting {c : ℝ × ℝ × ℝ → ℝ} {q : ℝ}
    (hc : IsPiecewiseAffineOn c univ) (hq : 0 ≤ q) (hq_lt : q < 1)
    (hvert : ∀ u v v' t : ℝ, |c (u, v, t) - c (u, v', t)| ≤ q * |v - v'|) :
    ∃ e : (ℝ × ℝ × ℝ) ≃ₜ (ℝ × ℝ × ℝ),
      (∀ p, e p = (p.1, p.2.1 - c p, p.2.2)) ∧
        IsPLHomeomorphOn e univ univ := by
  let k : NNReal := ⟨q, hq⟩
  have hcon : ∀ u s t : ℝ, ContractingWith k (fun v : ℝ => s + c (u, v, t)) := by
    intro u s t
    refine ⟨hq_lt, LipschitzWith.of_dist_le_mul fun v v' => ?_⟩
    calc
      dist (s + c (u, v, t)) (s + c (u, v', t)) = |c (u, v, t) - c (u, v', t)| := by
        rw [Real.dist_eq]
        congr 1
        ring_nf
      _ ≤ q * |v - v'| := hvert u v v' t
      _ = (k : ℝ) * dist v v' := by rfl
  let F : ℝ × ℝ × ℝ → ℝ × ℝ × ℝ :=
    fun p => (p.1, p.2.1 - c p, p.2.2)
  have hbij : Function.Bijective F := by
    constructor
    · rintro ⟨u, v, t⟩ ⟨u', v', t'⟩ hpp'
      change (u, v - c (u, v, t), t) = (u', v' - c (u', v', t'), t') at hpp'
      have hfst : u = u' := congrArg Prod.fst hpp'
      have hmid : v - c (u, v, t) = v' - c (u', v', t') :=
        congrArg (fun z : ℝ × ℝ × ℝ => z.2.1) hpp'
      have hlast : t = t' := congrArg (fun z : ℝ × ℝ × ℝ => z.2.2) hpp'
      subst u'
      subst t'
      apply Prod.ext
      · rfl
      · apply Prod.ext
        · apply (hcon u (v - c (u, v, t)) t).fixedPoint_unique'
          · change v - c (u, v, t) + c (u, v, t) = v
            ring_nf
          · change v - c (u, v, t) + c (u, v', t) = v'
            linarith
        · rfl
    · rintro ⟨u, s, t⟩
      let v := ContractingWith.fixedPoint (fun z : ℝ => s + c (u, z, t)) (hcon u s t)
      refine ⟨(u, v, t), ?_⟩
      change (u, v - c (u, v, t), t) = (u, s, t)
      apply Prod.ext
      · rfl
      · apply Prod.ext
        · have hv : s + c (u, v, t) = v := (hcon u s t).fixedPoint_isFixedPt
          change v - c (u, v, t) = s
          linarith
        · rfl
  have hccont : Continuous c :=
    continuous_iff_continuousAt.2 fun p => hc.continuousAt isOpen_univ (mem_univ p)
  have hFcont : Continuous F := by
    have hmid : Continuous (fun p : ℝ × ℝ × ℝ => p.2.1 - c p) :=
      continuous_snd.fst.sub hccont
    exact continuous_fst.prodMk (hmid.prodMk continuous_snd.snd)
  have hopen : IsOpenMap F := by
    intro U hU
    exact DifferentialGeometry.Topology.invariance_of_domain_isOpen_image_of_finrank_eq rfl hU
      hFcont.continuousOn hbij.1.injOn
  let e : (ℝ × ℝ × ℝ) ≃ₜ (ℝ × ℝ × ℝ) :=
    (Equiv.ofBijective F hbij).toHomeomorphOfContinuousOpen hFcont hopen
  have hfst : IsPiecewiseAffineOn (fun p : ℝ × ℝ × ℝ => p.1) univ :=
    isPiecewiseAffineOn_of_affine (LinearMap.fst ℝ ℝ (ℝ × ℝ)).toAffineMap isOpen_univ
  have hmidBase : IsPiecewiseAffineOn (fun p : ℝ × ℝ × ℝ => p.2.1) univ :=
    isPiecewiseAffineOn_of_affine
      ((LinearMap.fst ℝ ℝ ℝ).comp (LinearMap.snd ℝ ℝ (ℝ × ℝ))).toAffineMap isOpen_univ
  have hlast : IsPiecewiseAffineOn (fun p : ℝ × ℝ × ℝ => p.2.2) univ :=
    isPiecewiseAffineOn_of_affine
      ((LinearMap.snd ℝ ℝ ℝ).comp (LinearMap.snd ℝ ℝ (ℝ × ℝ))).toAffineMap isOpen_univ
  have hmid : IsPiecewiseAffineOn (fun p : ℝ × ℝ × ℝ => p.2.1 - c p) univ := by
    have hneg := hc.affine_comp (-AffineMap.id ℝ ℝ)
    have hneg' : IsPiecewiseAffineOn (fun p : ℝ × ℝ × ℝ => -c p) univ :=
      hneg.congr fun _ _ => rfl
    exact (hmidBase.add hneg').congr fun _ _ => by simp only [sub_eq_add_neg]
  have hpl : IsPiecewiseAffineOn F univ :=
    (hfst.prod_mk (hmid.prod_mk hlast)).congr fun _ _ => rfl
  have hplinv : IsPiecewiseAffineOn e.symm univ := by
    have h := IsPiecewiseAffineOn.symm (e := e.toOpenPartialHomeomorph) hpl
    have heq : EqOn e.symm e.toOpenPartialHomeomorph.symm univ := by
      intro y _
      apply e.injective
      exact (e.apply_symm_apply y).trans
        (e.toOpenPartialHomeomorph.right_inv (by simp)).symm
    have h' := h.congr heq
    simpa only [Homeomorph.toOpenPartialHomeomorph_source,
      Homeomorph.toOpenPartialHomeomorph_target] using h'
  have hbijSet : BijOn F univ univ := hbij.bijOn_univ
  refine ⟨e, fun p => rfl, ?_⟩
  refine ⟨hbijSet, hpl, hplinv.congr fun y hy => ?_⟩
  apply e.injective
  change F (Function.invFunOn F univ y) = F (e.symm y)
  exact (hbijSet.invOn_invFunOn.2 hy).trans (e.apply_symm_apply y).symm

theorem exists_pl_homeomorph_two_graphs_to_coordinate_planes_of_lipschitz {a b : ℝ × ℝ → ℝ}
    {La Lb η : ℝ} (ha : IsPiecewiseAffineOn a univ)
    (hb : IsPiecewiseAffineOn b univ) (hη : 0 < η) (hLa : 0 ≤ La) (hLb : 0 ≤ Lb)
    (hmargin : La * Lb ≤ 1 - η)
    (hA : ∀ v v' t : ℝ, |a (v, t) - a (v', t)| ≤ La * |v - v'|)
    (hB : ∀ u u' t : ℝ, |b (u, t) - b (u', t)| ≤ Lb * |u - u'|) :
    ∃ H : (ℝ × ℝ × ℝ) ≃ₜ (ℝ × ℝ × ℝ), IsPLHomeomorphOn H univ univ ∧
      (∀ p, (H p).2.2 = p.2.2) ∧
      H '' Set.range (fun q : ℝ × ℝ => (a q, q.1, q.2)) = {p | p.1 = 0} ∧
      H '' Set.range (fun q : ℝ × ℝ => (q.1, b q, q.2)) = {p | p.2.1 = 0} := by
  obtain ⟨e₁, he₁, hpl₁⟩ := exists_homeomorph_sub_first ha
  let c : ℝ × ℝ × ℝ → ℝ := fun p => b (p.1 + a (p.2.1, p.2.2), p.2.2)
  have hfst : IsPiecewiseAffineOn (fun p : ℝ × ℝ × ℝ => p.1) univ :=
    isPiecewiseAffineOn_of_affine (LinearMap.fst ℝ ℝ (ℝ × ℝ)).toAffineMap isOpen_univ
  have hmid : IsPiecewiseAffineOn (fun p : ℝ × ℝ × ℝ => p.2.1) univ :=
    isPiecewiseAffineOn_of_affine
      ((LinearMap.fst ℝ ℝ ℝ).comp (LinearMap.snd ℝ ℝ (ℝ × ℝ))).toAffineMap isOpen_univ
  have hlast : IsPiecewiseAffineOn (fun p : ℝ × ℝ × ℝ => p.2.2) univ :=
    isPiecewiseAffineOn_of_affine
      ((LinearMap.snd ℝ ℝ ℝ).comp (LinearMap.snd ℝ ℝ (ℝ × ℝ))).toAffineMap isOpen_univ
  have hvt : IsPiecewiseAffineOn (fun p : ℝ × ℝ × ℝ => (p.2.1, p.2.2)) univ :=
    hmid.prod_mk hlast
  have ha' : IsPiecewiseAffineOn (fun p : ℝ × ℝ × ℝ => a (p.2.1, p.2.2)) univ := by
    have h := ha.comp hvt
    rw [preimage_univ, inter_univ] at h
    exact h.congr fun _ _ => rfl
  have hfirst : IsPiecewiseAffineOn (fun p : ℝ × ℝ × ℝ => p.1 + a (p.2.1, p.2.2)) univ :=
    hfst.add ha'
  have hbt : IsPiecewiseAffineOn (fun p : ℝ × ℝ × ℝ =>
      (p.1 + a (p.2.1, p.2.2), p.2.2)) univ :=
    hfirst.prod_mk hlast
  have hc : IsPiecewiseAffineOn c univ := by
    have h := hb.comp hbt
    rw [preimage_univ, inter_univ] at h
    exact h.congr fun _ _ => rfl
  have hq : 0 ≤ La * Lb := mul_nonneg hLa hLb
  have hq_lt : La * Lb < 1 := by linarith
  have hcvert : ∀ u v v' t : ℝ,
      |c (u, v, t) - c (u, v', t)| ≤ (La * Lb) * |v - v'| := by
    intro u v v' t
    calc
      |c (u, v, t) - c (u, v', t)| =
          |b (u + a (v, t), t) - b (u + a (v', t), t)| := by rfl
      _ ≤ Lb * |(u + a (v, t)) - (u + a (v', t))| := hB _ _ t
      _ = Lb * |a (v, t) - a (v', t)| := by
        congr 1
        ring_nf
      _ ≤ Lb * (La * |v - v'|) := mul_le_mul_of_nonneg_left (hA v v' t) hLb
      _ = (La * Lb) * |v - v'| := by ring_nf
  obtain ⟨e₂, he₂, hpl₂⟩ :=
    exists_homeomorph_sub_middle_contracting hc hq hq_lt hcvert
  refine ⟨e₁.trans e₂, hpl₁.trans hpl₂, ?_, ?_, ?_⟩
  · intro p
    rw [Homeomorph.trans_apply, he₂, he₁]
  · apply Set.Subset.antisymm
    · rintro z ⟨w, ⟨q, rfl⟩, rfl⟩
      rw [Homeomorph.trans_apply, he₂, he₁]
      exact sub_self _
    · intro z hz
      change z.1 = 0 at hz
      let x := (e₁.trans e₂).symm z
      have hHx : (e₁.trans e₂) x = z := by
        dsimp [x]
        exact (e₁.trans e₂).apply_symm_apply z
      have hxzero : (e₁ x).1 = 0 := by
        have hzfirst : ((e₁.trans e₂) x).1 = 0 := by
          rw [hHx]
          exact hz
        rw [Homeomorph.trans_apply, he₂] at hzfirst
        exact hzfirst
      have hgraph : x.1 = a (x.2.1, x.2.2) := by
        rw [he₁] at hxzero
        exact sub_eq_zero.mp hxzero
      refine ⟨x, ⟨(x.2.1, x.2.2), ?_⟩, hHx⟩
      apply Prod.ext
      · exact hgraph.symm
      · apply Prod.ext <;> rfl
  · apply Set.Subset.antisymm
    · rintro z ⟨w, ⟨q, rfl⟩, rfl⟩
      rw [Homeomorph.trans_apply, he₂, he₁]
      change b q - b (q.1 - a (b q, q.2) + a (b q, q.2), q.2) = 0
      rw [sub_add_cancel]
      exact sub_self _
    · intro z hz
      change z.2.1 = 0 at hz
      let x := (e₁.trans e₂).symm z
      have hHx : (e₁.trans e₂) x = z := by
        dsimp [x]
        exact (e₁.trans e₂).apply_symm_apply z
      have hxzero : (e₁ x).2.1 - c (e₁ x) = 0 := by
        have hzmiddle : ((e₁.trans e₂) x).2.1 = 0 := by
          rw [hHx]
          exact hz
        rw [Homeomorph.trans_apply, he₂] at hzmiddle
        exact hzmiddle
      have hgraph : x.2.1 = b (x.1, x.2.2) := by
        rw [he₁] at hxzero
        dsimp [c] at hxzero
        have hcancel : x.1 - a (x.2.1, x.2.2) + a (x.2.1, x.2.2) = x.1 :=
          sub_add_cancel _ _
        rw [hcancel] at hxzero
        exact sub_eq_zero.mp hxzero
      refine ⟨x, ⟨(x.1, x.2.2), ?_⟩, hHx⟩
      apply Prod.ext
      · rfl
      · apply Prod.ext
        · exact hgraph.symm
        · rfl

end DifferentialGeometry.Topology.PiecewiseLinear
