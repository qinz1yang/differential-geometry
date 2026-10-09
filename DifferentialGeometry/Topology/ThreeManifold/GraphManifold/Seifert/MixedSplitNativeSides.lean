import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MixedSplitNative

/-!
# Sides and seam charts of the native mixed split system

Lane MS, tier MS4 (design `handoffs/20261004-design-ms-mixed-split.md` §3.3), continuing
`MixedSplitNative`. The surviving seams are the seams `c ≠ j` of the fixed presentation. A side of
such a seam is a port of a passive piece, read in the cut system `capCut`, unless it is a port of
the host, in which case it is the unique port of the capped solid torus `D.solidOf` of that host
circle (`capSide`, lane N2c's `cappedSide`). `recover` reads a port back as a side of the old
presentation; it is injective and inverts `capSide` (`recover_capSide`), so `capSide` is a
bijection onto all ports (`capSide_bijective`). The seam chart of `c` is the fixed seam read
through the core (`capSeam`); on a passive side it reads the passive collar (Lane BA's seam
formulas of `capCut`), on a host port the collar of the capped solid torus
(`solid_collar_eq_fixed`), which gives `capSeam_neg` and `capSeam_pos` with the fixed matching.
-/

set_option autoImplicit false

noncomputable section
open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert.RelativeNormalization.MixedStage

variable {Q : ConnectedClosedOrientedManifold.{u} 3} {σ : MixedStage Q}
  {j : Fin σ.toTorus.pairing.count} {b : Bool} {h : σ.IsSplitSeam j b} {S : σ.SplitData h}
  {T : SphericalTubeSystem Q.toClosedOrientedManifold} {N : ClosedOrientedManifold.{u} 3}
  {K : SphericalCapping Q.toClosedOrientedManifold N T} {a : T.Index} {δ₂ : ℝ}
  (D : σ.SideData S K a δ₂) (hC : σ.CappedConditions S a δ₂)

theorem capCut_side_fst (c : Fin σ.toTorus.pairing.count) (β : Bool) :
    ((capCut D hC).side c β).1 = σ.seamPiece c β := by
  cases β <;> rfl

include h in
theorem seamPiece_ne_seamPiece_of_ne {c : Fin σ.toTorus.pairing.count} (hc : c ≠ j) (β : Bool) :
    σ.seamPiece c β ≠ σ.seamPiece j b := fun he =>
  hc (σ.eq_of_seamPiece_eq_of_isSplitSeam h he).1

theorem seamPiece_eq_or (c : Fin σ.toTorus.pairing.count) (β : Bool) :
    σ.seamPiece c β = σ.seamPiece c b ∨ σ.seamPiece c β = σ.hostPiece c b := by
  cases β <;> cases b <;> simp [hostPiece]

open Classical in
def capSide (c : CapSeam σ j) (β : Bool) : Σ i : CapPiece σ j b, Fin (capTorusCount D hC i) :=
  if hH : σ.seamPiece c.1 β = σ.hostPiece j b then
    ⟨.inr (D.solidOf (σ.hostPortOf h hH)), ⟨0, Nat.one_pos⟩⟩
  else
    ⟨.inl ⟨((capCut D hC).side c.1 β).1, by
      rw [capCut_side_fst]
      exact ⟨seamPiece_ne_seamPiece_of_ne (h := h) c.2 β, hH⟩⟩, ((capCut D hC).side c.1 β).2⟩

theorem capSide_of_host (c : CapSeam σ j) {β : Bool} (hH : σ.seamPiece c.1 β = σ.hostPiece j b) :
    capSide D hC c β = ⟨.inr (D.solidOf (σ.hostPortOf h hH)), ⟨0, Nat.one_pos⟩⟩ := by
  classical
  unfold capSide
  rw [dite_eq_left hH]

theorem capSide_of_not_host (c : CapSeam σ j) {β : Bool}
    (hH : ¬ σ.seamPiece c.1 β = σ.hostPiece j b) :
    capSide D hC c β = ⟨.inl ⟨((capCut D hC).side c.1 β).1, by
      rw [capCut_side_fst]
      exact ⟨seamPiece_ne_seamPiece_of_ne (h := h) c.2 β, hH⟩⟩, ((capCut D hC).side c.1 β).2⟩ := by
  classical
  unfold capSide
  rw [dite_eq_right hH]

def recover : (Σ i : CapPiece σ j b, Fin (capTorusCount D hC i)) → σ.toTorus.Side
  | ⟨.inl k, l⟩ => (capTorus D hC).sideEquiv.symm ⟨k.1, l⟩
  | ⟨.inr t, _⟩ =>
    (σ.standardPort (σ.hostPiece j b) (σ.hostPiece_not_frozen h) h.2.2.1 (D.port t)).val

theorem sidePiece_sideEquiv_symm (x : Σ k : Fin σ.toTorus.components.count,
    Fin ((capCut D hC).torusCount k)) :
    σ.toTorus.sidePiece ((capTorus D hC).sideEquiv.symm x) = x.1 := by
  have h1 := congrArg Sigma.fst ((capTorus D hC).sideEquiv.apply_symm_apply x)
  rw [TorusPresentation.sideEquiv_apply] at h1
  rcases hs : (capTorus D hC).sideEquiv.symm x with c | c | i
  all_goals rw [hs] at h1; exact h1

theorem recover_capSide (c : CapSeam σ j) (β : Bool) :
    recover D hC (capSide D hC c β) = σ.seamSide c.1 β := by
  by_cases hH : σ.seamPiece c.1 β = σ.hostPiece j b
  · rw [capSide_of_host D hC c hH]
    change (σ.standardPort (σ.hostPiece j b) (σ.hostPiece_not_frozen h) h.2.2.1
      (D.port (D.solidOf (σ.hostPortOf h hH)))).val = _
    rw [D.port_solidOf (σ.hostPortOf_ne_hostSide c.2 hH), standardPort_hostPortOf]
  · rw [capSide_of_not_host D hC c hH]
    change (capTorus D hC).sideEquiv.symm ((capCut D hC).side c.1 β) = _
    change (capTorus D hC).sideEquiv.symm ((capTorus D hC).sideEquiv
      ((capTorus D hC).sideSum (.inl (c.1, β)))) = _
    rw [Equiv.symm_apply_apply]
    cases β <;> rfl

theorem standardPort_port_ne_seamSide (t β : Bool) :
    (σ.standardPort (σ.hostPiece j b) (σ.hostPiece_not_frozen h) h.2.2.1 (D.port t)).val ≠
      σ.seamSide j β := by
  intro hcβ
  have hH : σ.seamPiece j β = σ.hostPiece j b := by
    rw [← σ.sidePiece_seamSide, ← hcβ]
    exact (σ.standardPort (σ.hostPiece j b) (σ.hostPiece_not_frozen h) h.2.2.1 (D.port t)).2
  have hβ : β = !b := by
    by_contra hβ
    have hb' : β = b := by cases β <;> cases b <;> simp_all
    rw [hb'] at hH
    exact σ.seamPiece_ne_hostPiece h hH
  rw [hβ] at hcβ
  have := (σ.standardPort (σ.hostPiece j b) (σ.hostPiece_not_frozen h) h.2.2.1).injective
    (Subtype.ext (hcβ.trans (congrArg Subtype.val (σ.standardPort_hostSide h)).symm))
  exact D.port_ne t this

theorem recover_injective : Injective (recover D hC) := by
  rintro ⟨i, l⟩ ⟨i', l'⟩ he
  rcases i with k | t <;> rcases i' with k' | t'
  · change (capTorus D hC).sideEquiv.symm ⟨k.1, l⟩ =
      (capTorus D hC).sideEquiv.symm ⟨k'.1, l'⟩ at he
    have h1 := (capTorus D hC).sideEquiv.symm.injective he
    have h2 := Sigma.mk.inj_iff.mp h1
    obtain ⟨k, hk⟩ := k
    obtain ⟨k', hk'⟩ := k'
    obtain rfl : k = k' := h2.1
    rw [eq_of_heq h2.2]
  · have h1 : σ.toTorus.sidePiece (recover D hC ⟨.inl k, l⟩) = k.1 :=
      sidePiece_sideEquiv_symm D hC ⟨k.1, l⟩
    have h2 : σ.toTorus.sidePiece (recover D hC ⟨.inr t', l'⟩) = σ.hostPiece j b :=
      (σ.standardPort (σ.hostPiece j b) (σ.hostPiece_not_frozen h) h.2.2.1 (D.port t')).2
    exact absurd (h1.symm.trans ((congrArg σ.toTorus.sidePiece he).trans h2)) k.2.2
  · have h1 : σ.toTorus.sidePiece (recover D hC ⟨.inl k', l'⟩) = k'.1 :=
      sidePiece_sideEquiv_symm D hC ⟨k'.1, l'⟩
    have h2 : σ.toTorus.sidePiece (recover D hC ⟨.inr t, l⟩) = σ.hostPiece j b :=
      (σ.standardPort (σ.hostPiece j b) (σ.hostPiece_not_frozen h) h.2.2.1 (D.port t)).2
    exact absurd (h1.symm.trans ((congrArg σ.toTorus.sidePiece he).symm.trans h2)) k'.2.2
  · change (σ.standardPort (σ.hostPiece j b) (σ.hostPiece_not_frozen h) h.2.2.1
      (D.port t)).val = (σ.standardPort (σ.hostPiece j b) (σ.hostPiece_not_frozen h) h.2.2.1
      (D.port t')).val at he
    have ht := (σ.standardPort (σ.hostPiece j b) (σ.hostPiece_not_frozen h) h.2.2.1).injective
      (Subtype.ext he)
    have htt : t = t' := by rw [← D.solidOf_port t, ht, D.solidOf_port]
    subst htt
    have hl : l = l' := Subsingleton.elim (α := Fin 1) _ _
    rw [hl]

theorem capSide_bijective : Bijective (uncurry (capSide D hC)) := by
  refine ⟨fun x y hxy => ?_, fun z => ?_⟩
  · obtain ⟨c, β⟩ := x
    obtain ⟨c', β'⟩ := y
    have he : σ.seamSide c.1 β = σ.seamSide c'.1 β' := by
      rw [← recover_capSide D hC, ← recover_capSide D hC]
      exact congrArg (recover D hC) hxy
    obtain ⟨h1, h2⟩ := σ.seamSide_eq_seamSide_iff.mp he
    exact Prod.ext (Subtype.ext h1) h2
  · obtain ⟨c, β, hcβ⟩ := σ.exists_seamSide_eq (recover D hC z)
    have hc : c ≠ j := by
      intro hcj
      rw [hcj] at hcβ
      obtain ⟨i, l⟩ := z
      rcases i with k | t
      · have hk := sidePiece_sideEquiv_symm D hC ⟨k.1, l⟩
        change σ.toTorus.sidePiece (recover D hC ⟨.inl k, l⟩) = k.1 at hk
        rw [← hcβ, σ.sidePiece_seamSide] at hk
        rcases seamPiece_eq_or (σ := σ) (b := b) j β with e | e
        · exact k.2.1 (hk.symm.trans e)
        · exact k.2.2 (hk.symm.trans e)
      · exact standardPort_port_ne_seamSide D t β hcβ.symm
    refine ⟨(⟨c, hc⟩, β), recover_injective D hC ?_⟩
    change recover D hC (capSide D hC ⟨c, hc⟩ β) = _
    rw [recover_capSide, hcβ]

end GC.Seifert.RelativeNormalization.MixedStage
