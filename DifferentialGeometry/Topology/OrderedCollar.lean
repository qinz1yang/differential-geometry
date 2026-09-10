import DifferentialGeometry.Topology.FiberwiseHomeomorph
import Mathlib.Topology.UniformSpace.Real
import Mathlib.Topology.Order.Compact

noncomputable section
open Set

namespace Poincare.Topology

theorem exists_ordered_graph_band_of_fiberwise_bijective
    {N P L : Type*} [TopologicalSpace N] [CompactSpace N]
    [TopologicalSpace P] [T2Space P]
    [LinearOrder L] [TopologicalSpace L] [OrderClosedTopology L]
    (a b : ℝ) (hab : a ≤ b) (e : N × Icc a b → P × L)
    (he : Continuous e) (hinj : Function.Injective e)
    (hbij : ∀ t, Function.Bijective (fun p ↦ (e (p, t)).1))
    (horder : ∀ p q, (e (p, ⟨a, le_rfl, hab⟩)).1 = (e (q, ⟨b, hab, le_rfl⟩)).1 →
      (e (p, ⟨a, le_rfl, hab⟩)).2 ≤ (e (q, ⟨b, hab, le_rfl⟩)).2) :
    ∃ h : C(P × Icc a b, L),
      (∀ x, e x = ((e x).1, h ((e x).1, x.2))) ∧
      (∀ p, StrictMono (fun t ↦ h (p, t))) ∧
      range e = {x | h (x.1, ⟨a, le_rfl, hab⟩) ≤ x.2 ∧
        x.2 ≤ h (x.1, ⟨b, hab, le_rfl⟩)} ∧
      ∀ s t : Icc a b, e '' ((univ : Set N) ×ˢ Icc s t) =
        {y | h (y.1, s) ≤ y.2 ∧ y.2 ≤ h (y.1, t)} := by
  let : Fact (a ≤ b) := ⟨hab⟩
  let Φ := fiberwiseHomeomorph (fun x ↦ (e x).1) he.fst hbij
  let h : C(P × Icc a b, L) := ⟨fun x ↦ (e (Φ.symm x)).2, he.snd.comp Φ.symm.continuous⟩
  have hparam (x : P × Icc a b) : (Φ.symm x).2 = x.2 :=
    fiberwiseHomeomorph_symm_snd _ _ _ x
  have hfirst (x : P × Icc a b) : (e (Φ.symm x)).1 = x.1 :=
    congrArg Prod.fst (Φ.apply_symm_apply x)
  have hgraph (x : P × Icc a b) : e (Φ.symm x) = (x.1, h x) :=
    Prod.ext (hfirst x) rfl
  have heq (x : N × Icc a b) : e x = ((e x).1, h ((e x).1, x.2)) := by
    have hx : Φ.symm ((e x).1, x.2) = x := Φ.symm_apply_apply x
    exact (congrArg e hx).symm.trans (hgraph ((e x).1, x.2))
  have hmono (p : P) : StrictMono (fun t ↦ h (p, t)) := by
    have hc : Continuous (fun t ↦ h (p, t)) :=
      h.continuous.comp (continuous_const.prodMk continuous_id)
    have hi : Function.Injective (fun t ↦ h (p, t)) := by
      intro t s hts
      change h (p, t) = h (p, s) at hts
      have he : e (Φ.symm (p, t)) = e (Φ.symm (p, s)) := by
        rw [hgraph, hgraph, hts]
      have heq := congrArg Φ (hinj he)
      rw [Φ.apply_symm_apply, Φ.apply_symm_apply] at heq
      exact congrArg Prod.snd heq
    apply hc.strictMono_of_inj_boundedOrder _ hi
    have h₀ : ((Φ.symm (p, ⊥)).1, (⊥ : Icc a b)) = Φ.symm (p, ⊥) :=
      Prod.ext rfl (hparam (p, ⊥)).symm
    have h₁ : ((Φ.symm (p, ⊤)).1, (⊤ : Icc a b)) = Φ.symm (p, ⊤) :=
      Prod.ext rfl (hparam (p, ⊤)).symm
    have ho := horder (Φ.symm (p, ⊥)).1 (Φ.symm (p, ⊤)).1
    change (e ((Φ.symm (p, ⊥)).1, (⊥ : Icc a b))).1 =
      (e ((Φ.symm (p, ⊤)).1, (⊤ : Icc a b))).1 →
      (e ((Φ.symm (p, ⊥)).1, (⊥ : Icc a b))).2 ≤
      (e ((Φ.symm (p, ⊤)).1, (⊤ : Icc a b))).2 at ho
    rw [h₀, h₁] at ho
    exact ho ((hfirst (p, ⊥)).trans (hfirst (p, ⊤)).symm)
  have hsub (s t : Icc a b) : e '' ((univ : Set N) ×ˢ Icc s t) =
      {y | h (y.1, s) ≤ y.2 ∧ y.2 ≤ h (y.1, t)} := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hy := congrArg Prod.snd (heq x)
      change h ((e x).1, s) ≤ (e x).2 ∧ (e x).2 ≤ h ((e x).1, t)
      rw [hy]
      exact ⟨(hmono (e x).1).monotone hx.2.1, (hmono (e x).1).monotone hx.2.2⟩
    · intro hy
      have hc : Continuous (fun u ↦ h (y.1, u)) :=
        h.continuous.comp (continuous_const.prodMk continuous_id)
      have hmem : y.2 ∈ (fun u ↦ h (y.1, u)) '' Icc s t := by
        rw [hc.image_Icc_of_strictMono (hmono y.1)]
        exact hy
      obtain ⟨u, hu, hz⟩ := hmem
      refine ⟨Φ.symm (y.1, u), ⟨mem_univ _, ?_⟩, ?_⟩
      · change s ≤ (Φ.symm (y.1, u)).2 ∧ (Φ.symm (y.1, u)).2 ≤ t
        rw [hparam]
        exact hu
      · exact (hgraph (y.1, u)).trans (Prod.ext rfl hz)
  refine ⟨h, heq, hmono, ?_, hsub⟩
  change range e = {x | h (x.1, (⊥ : Icc a b)) ≤ x.2 ∧ x.2 ≤ h (x.1, (⊤ : Icc a b))}
  simpa only [Icc_bot_top, univ_prod_univ, image_univ] using hsub ⊥ ⊤

end Poincare.Topology
