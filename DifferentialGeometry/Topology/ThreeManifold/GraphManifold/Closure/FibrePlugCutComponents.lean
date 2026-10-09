import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.SphereCutComponents
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.SphereCapComponents
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FibrePlugOpenSides
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FibrePlugCapShell

/-!
The fixed bounded fibre plug produces actual cut and capped components on its same zero sphere.
Ordinary side geometry discharges the cut hypotheses and assigns exactly one old port to each side.
-/

set_option autoImplicit false

noncomputable section

open Set Function Topology TopologicalSpace
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open GC.GraphManifold.MixedBoundaryCertificate
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert.ElementaryPresentation

variable {W : CompactCarrier.{u}} (E : ElementaryPresentation W)
  {j : Fin E.toTorus.pairing.count} {b : Bool} (h : E.IsSplitSeam j b)
  (hlin : E.IsLinearSeam j) (hc : E.toTorus.components.count = 2)
  (hn : E.toTorus.pairing.count = 1)
  (d : PartialDiffeomorph sphereSignedCollarModel W.model
    (ClosureSphere.{u} × ℝ) W.Carrier ∞) (hs : d.source = sphereSignedCollarSource)
  (heq : ∀ z s, d (z, s) = E.boundedSplitTubeMap h hlin (z.down, s))

private def fibrePlugCutSides (a : Bool) : Set W.Carrier := E.fibrePlugSide h hlin (!a)

include heq in
private theorem fibrePlugCut_zero_image : sphereCutAmbientZero (boundedPlugCutCollars d) =
    range (fun z : SphereTwo => E.boundedSplitTubeMap h hlin (z, 0)) := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, z, hz⟩ := mem_iUnion.mp hx
    refine ⟨z.down, ?_⟩
    exact (heq z 0).symm.trans hz
  · rintro ⟨z, rfl⟩
    exact mem_iUnion.mpr ⟨0, ULift.up z, heq (ULift.up z) 0⟩

include hn hc heq in
private theorem fibrePlugCut_cover : (sphereCutAmbientZero (boundedPlugCutCollars d))ᶜ =
    fibrePlugCutSides E h hlin false ∪ fibrePlugCutSides E h hlin true := by
  rw [E.fibrePlugCut_zero_image h hlin d heq,
    E.fibrePlug_sphere_complement h hlin hn hc]
  exact union_comm _ _

include heq in
private theorem fibrePlugCut_germ :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 / 4 ∧ ∀ a z s, 0 < s → s < η →
      boundedPlugCutCollars d 0 (z, sphereCutSign a s) ∈ fibrePlugCutSides E h hlin a := by
  refine ⟨1 / 4, by norm_num, le_rfl, ?_⟩
  intro a z s hs0 hs1
  change d (z, sphereCutSign a s) ∈ E.fibrePlugSide h hlin (!a)
  rw [heq]
  apply E.fibrePlug_tube_side h hlin (!a) z.down (sphereCutSign a s)
  · cases a <;> simp only [sphereCutSign, Bool.false_eq_true, ite_false, ite_true, abs_neg]
    all_goals rw [abs_of_pos hs0]; linarith
  · cases a <;> simp [sphereCutSign, SplitTube.sgnR, hs0]

def fibrePlugCutComponents : (boundedPlugCutCarrier d hs).Components :=
  sphereCutComponents (boundedPlugCutCollars d) (boundedPlugCutCollars_source d hs)
    (boundedPlugCutCollars_disjoint d) (fibrePlugCutSides E h hlin)
    (fun a => E.fibrePlugSide_connected h hlin (!a))
    (fun a => E.fibrePlugSide_isOpen h hlin hn hc (!a))
    (E.fibrePlugSide_disjoint h hlin hn).symm
    (E.fibrePlugCut_cover h hlin hc hn d heq) (E.fibrePlugCut_germ h hlin d heq)

theorem fibrePlugCutComponents_count :
    (E.fibrePlugCutComponents h hlin hc hn d hs heq).count = 2 := rfl

set_option backward.isDefEq.respectTransparency false in
theorem fibrePlugCutComponents_piece (i : Fin 2) :
    ((E.fibrePlugCutComponents h hlin hc hn d hs heq).piece i :
      Set (boundedPlugCutCarrier d hs).Carrier) =
        sphereCutFold (boundedPlugCutCollars d) ⁻¹'
          E.fibrePlugSide h hlin (!sphereCutBoundarySide i) ∪
            range (sphereCutZero (boundedPlugCutCollars d) 0 (sphereCutBoundarySide i)) := rfl

set_option backward.isDefEq.respectTransparency false in
theorem fibrePlugCutComponents_zero_mem (i : Fin 2) (a : Bool) (z : ClosureSphere.{u}) :
    sphereCutZero (boundedPlugCutCollars d) 0 a z ∈
      (E.fibrePlugCutComponents h hlin hc hn d hs heq).piece i ↔ a = sphereCutBoundarySide i :=
  sphereCutComponents_zero_mem (boundedPlugCutCollars d) (boundedPlugCutCollars_source d hs)
    (boundedPlugCutCollars_disjoint d) (fibrePlugCutSides E h hlin)
    (fun a => E.fibrePlugSide_connected h hlin (!a))
    (fun a => E.fibrePlugSide_isOpen h hlin hn hc (!a))
    (E.fibrePlugSide_disjoint h hlin hn).symm
    (E.fibrePlugCut_cover h hlin hc hn d heq) (E.fibrePlugCut_germ h hlin d heq) i a z

set_option backward.isDefEq.respectTransparency false in
theorem fibrePlugCutComponents_fullSphere_owned (i : Fin 2) :
    (sphereCutFullCollar (boundedPlugCutCollars d) (boundedPlugCutCollars_source d hs)
      (boundedPlugCutCollars_disjoint d) 0 (sphereCutBoundarySide i)).target ⊆
        (E.fibrePlugCutComponents h hlin hc hn d hs heq).piece i :=
  sphereCutComponents_fullCollar_owned (boundedPlugCutCollars d)
    (boundedPlugCutCollars_source d hs) (boundedPlugCutCollars_disjoint d)
    (fibrePlugCutSides E h hlin) (fun a => E.fibrePlugSide_connected h hlin (!a))
    (fun a => E.fibrePlugSide_isOpen h hlin hn hc (!a))
    (E.fibrePlugSide_disjoint h hlin hn).symm
    (E.fibrePlugCut_cover h hlin hc hn d heq) (E.fibrePlugCut_germ h hlin d heq) i

def fibrePlugCutSideEquiv : Fin 2 ≃ Bool where
  toFun i := !sphereCutBoundarySide i
  invFun t := if t then 0 else 1
  left_inv i := by fin_cases i <;> rfl
  right_inv t := by cases t <;> rfl

def fibrePlugCutPortEquiv : Fin 2 ≃ Fin E.toTorus.externalCount :=
  fibrePlugCutSideEquiv.trans (E.fibrePlugSideExternalEquiv h hc hn)

theorem fibrePlugCutPortEquiv_apply (i : Fin 2) :
    E.fibrePlugCutPortEquiv h hc hn i =
      E.fibrePlugSideExternalEquiv h hc hn (!sphereCutBoundarySide i) := rfl

variable {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
  (hI : d.target ⊆ W.interior)
  (hav : ∀ r, Disjoint ((E.toTorus.external.shrink hρ hρ1).collar r).target d.target)

abbrev fibrePlugCutBoundary : MixedBoundaryCertificate (boundedPlugCutCarrier d hs) :=
  boundedPlugCutBoundary d hs hI (E.toTorus.external.shrink hρ hρ1)
    (E.toTorus.external_exhausted.trans
      (E.toTorus.external.shrink_image hρ hρ1).symm) hav

set_option backward.isDefEq.respectTransparency false in
theorem fibrePlugCutComponents_fullTorus_owned (i : Fin 2) :
    ((E.fibrePlugCutBoundary d hs hρ hρ1 hI hav).tori.collar
      (E.fibrePlugCutPortEquiv h hc hn i)).target ⊆
        (E.fibrePlugCutComponents h hlin hc hn d hs heq).piece i := by
  apply sphereCutComponents_retained_full_owned (boundedPlugCutCollars d)
    (boundedPlugCutCollars_source d hs) (boundedPlugCutCollars_disjoint d)
    (fibrePlugCutSides E h hlin) (fun a => E.fibrePlugSide_connected h hlin (!a))
    (fun a => E.fibrePlugSide_isOpen h hlin hn hc (!a))
    (E.fibrePlugSide_disjoint h hlin hn).symm
    (E.fibrePlugCut_cover h hlin hc hn d heq) (E.fibrePlugCut_germ h hlin d heq)
    (E.toTorus.external.shrink hρ hρ1) (fun r => Function.const (Fin 1) (hav r))
    (E.fibrePlugCutPortEquiv h hc hn i) i
  intro t
  rw [BoundaryTori.shrink_torusMap]
  exact E.fibrePlug_external_mem_side h hc hn hlin (!sphereCutBoundarySide i) t

set_option backward.isDefEq.respectTransparency false in
theorem fibrePlugCutComponents_torus_owned (i : Fin 2) (t : Torus) :
    (E.fibrePlugCutBoundary d hs hρ hρ1 hI hav).tori.torusMap
      (E.fibrePlugCutPortEquiv h hc hn i) t ∈
        (E.fibrePlugCutComponents h hlin hc hn d hs heq).piece i :=
  E.fibrePlugCutComponents_fullTorus_owned h hlin hc hn d hs heq hρ hρ1 hI hav i
    (((E.fibrePlugCutBoundary d hs hρ hρ1 hI hav).tori.collar _).map_source
      (((E.fibrePlugCutBoundary d hs hρ hρ1 hI hav).tori.source_eq _).symm.subset
        (zero_mem_halfCollarSource t)))


set_option backward.isDefEq.respectTransparency false in
theorem fibrePlugCutComponents_torus_mem_iff (r : Fin E.toTorus.externalCount) (i : Fin 2)
    (t : Torus) :
    (E.fibrePlugCutBoundary d hs hρ hρ1 hI hav).tori.torusMap r t ∈
      (E.fibrePlugCutComponents h hlin hc hn d hs heq).piece i ↔
        r = E.fibrePlugCutPortEquiv h hc hn i := by
  let P := E.fibrePlugCutPortEquiv h hc hn
  let D := E.fibrePlugCutComponents h hlin hc hn d hs heq
  constructor
  · intro hmem
    have hk := E.fibrePlugCutComponents_torus_owned h hlin hc hn d hs heq
      hρ hρ1 hI hav (P.symm r) t
    rw [P.apply_symm_apply] at hk
    have he : P.symm r = i := by
      by_contra hne
      exact disjoint_left.mp (D.disjoint hne) hk hmem
    exact (P.apply_symm_apply r).symm.trans (congrArg P he)
  · rintro rfl
    exact E.fibrePlugCutComponents_torus_owned h hlin hc hn d hs heq hρ hρ1 hI hav i t

set_option backward.isDefEq.respectTransparency false in
theorem fibrePlugCutComponents_torus_range_iff (r : Fin E.toTorus.externalCount) (i : Fin 2) :
    range ((E.fibrePlugCutBoundary d hs hρ hρ1 hI hav).tori.torusMap r) ⊆
      (E.fibrePlugCutComponents h hlin hc hn d hs heq).piece i ↔
        r = E.fibrePlugCutPortEquiv h hc hn i := by
  constructor
  · intro hmem
    exact (E.fibrePlugCutComponents_torus_mem_iff h hlin hc hn d hs heq hρ hρ1 hI hav
      r i (1, 1)).mp (hmem (mem_range_self (1, 1)))
  · intro hr
    rintro x ⟨t, rfl⟩
    exact (E.fibrePlugCutComponents_torus_mem_iff h hlin hc hn d hs heq hρ hρ1 hI hav
      r i t).mpr hr

set_option backward.isDefEq.respectTransparency false in
theorem fibrePlugCutComponents_one_port (i : Fin 2) :
    Nat.card {r : Fin E.toTorus.externalCount |
      range ((E.fibrePlugCutBoundary d hs hρ hρ1 hI hav).tori.torusMap r) ⊆
        (E.fibrePlugCutComponents h hlin hc hn d hs heq).piece i} = 1 := by
  classical
  have he : {r : Fin E.toTorus.externalCount |
      range ((E.fibrePlugCutBoundary d hs hρ hρ1 hI hav).tori.torusMap r) ⊆
        (E.fibrePlugCutComponents h hlin hc hn d hs heq).piece i} =
      {r | r = E.fibrePlugCutPortEquiv h hc hn i} := by
    ext r
    exact E.fibrePlugCutComponents_torus_range_iff h hlin hc hn d hs heq hρ hρ1 hI hav r i
  rw [he]
  let : Unique {r : Fin E.toTorus.externalCount | r = E.fibrePlugCutPortEquiv h hc hn i} :=
    { default := ⟨E.fibrePlugCutPortEquiv h hc hn i, rfl⟩
      uniq r := Subtype.ext r.property }
  exact Nat.card_unique

def fibrePlugCapComponents :
    (E.fibrePlugCutBoundary d hs hρ hρ1 hI hav).sphereCapCarrier.Components :=
  (E.fibrePlugCutBoundary d hs hρ hρ1 hI hav).sphereCapComponents
    (E.fibrePlugCutComponents h hlin hc hn d hs heq)

theorem fibrePlugCapComponents_count :
    (E.fibrePlugCapComponents h hlin hc hn d hs heq hρ hρ1 hI hav).count = 2 := rfl

set_option backward.isDefEq.respectTransparency false in
theorem fibrePlugCapComponents_core_mem (i : Fin 2) (x : (boundedPlugCutCarrier d hs).Carrier) :
    (E.fibrePlugCutBoundary d hs hρ hρ1 hI hav).sphereCapCore x ∈
      (E.fibrePlugCapComponents h hlin hc hn d hs heq hρ hρ1 hI hav).piece i ↔
        x ∈ (E.fibrePlugCutComponents h hlin hc hn d hs heq).piece i :=
  (E.fibrePlugCutBoundary d hs hρ hρ1 hI hav).sphereCapComponents_core_mem
    (E.fibrePlugCutComponents h hlin hc hn d hs heq) i x

set_option backward.isDefEq.respectTransparency false in
theorem fibrePlugCutBoundary_sphere_owner (i : Fin 2) :
    (E.fibrePlugCutBoundary d hs hρ hρ1 hI hav).sphereCapComponentOwner
      (E.fibrePlugCutComponents h hlin hc hn d hs heq) i = i := by
  let B := E.fibrePlugCutBoundary d hs hρ hρ1 hI hav
  let D := E.fibrePlugCutComponents h hlin hc hn d hs heq
  let z : ClosureSphere.{u} := Classical.choice inferInstance
  have ho := B.sphereCapComponentOwner_mem D i z
  have hi : B.sphereMap i z ∈ D.piece i :=
    E.fibrePlugCutComponents_fullSphere_owned h hlin hc hn d hs heq i
      ((B.sphere i).map_source ((B.sphere_source i).symm.subset (by
        change (0 : ℝ) < 1
        norm_num)))
  by_contra hne
  exact disjoint_left.mp (D.disjoint hne) ho hi

set_option backward.isDefEq.respectTransparency false in
theorem fibrePlugCapComponents_cap_owned (i : Fin 2) (x : ClosedCell 3) :
    (E.fibrePlugCutBoundary d hs hρ hρ1 hI hav).sphereCapReparameterizedCap i x ∈
      (E.fibrePlugCapComponents h hlin hc hn d hs heq hρ hρ1 hI hav).piece i := by
  let B := E.fibrePlugCutBoundary d hs hρ hρ1 hI hav
  have hm := B.sphereCapComponents_cap_mem (E.fibrePlugCutComponents h hlin hc hn d hs heq) i x
  rwa [E.fibrePlugCutBoundary_sphere_owner h hlin hc hn d hs heq hρ hρ1 hI hav] at hm

set_option backward.isDefEq.respectTransparency false in
theorem fibrePlugCapComponents_fullTorus_owned (i : Fin 2) :
    ((E.fibrePlugCutBoundary d hs hρ hρ1 hI hav).sphereCapRetained.collar
      (E.fibrePlugCutPortEquiv h hc hn i)).target ⊆
        (E.fibrePlugCapComponents h hlin hc hn d hs heq hρ hρ1 hI hav).piece i := by
  let B := E.fibrePlugCutBoundary d hs hρ hρ1 hI hav
  let e := B.sphereCapRetained.collar (E.fibrePlugCutPortEquiv h hc hn i)
  intro x hx
  let p := e.symm x
  have hp : p ∈ halfCollarSource :=
    (B.sphereCapRetained.source_eq _).subset (e.map_target hx)
  have he : x = B.sphereCapCore (B.tori.collar (E.fibrePlugCutPortEquiv h hc hn i) p) := by
    rw [← e.right_inv hx]
    exact B.sphereCapRetained_collar _ hp
  rw [he]
  apply (E.fibrePlugCapComponents_core_mem h hlin hc hn d hs heq hρ hρ1 hI hav i
    (B.tori.collar (E.fibrePlugCutPortEquiv h hc hn i) p)).mpr
  exact E.fibrePlugCutComponents_fullTorus_owned h hlin hc hn d hs heq hρ hρ1 hI hav i
    ((B.tori.collar _).map_source ((B.tori.source_eq _).symm.subset hp))

set_option backward.isDefEq.respectTransparency false in
theorem fibrePlugCapComponents_torus_mem_iff (r : Fin E.toTorus.externalCount) (i : Fin 2)
    (t : Torus) :
    (E.fibrePlugCutBoundary d hs hρ hρ1 hI hav).sphereCapRetained.torusMap r t ∈
      (E.fibrePlugCapComponents h hlin hc hn d hs heq hρ hρ1 hI hav).piece i ↔
        r = E.fibrePlugCutPortEquiv h hc hn i := by
  let B := E.fibrePlugCutBoundary d hs hρ hρ1 hI hav
  change B.sphereCapRetained.collar r (t, halfZero) ∈ _ ↔ _
  rw [B.sphereCapRetained_collar r (zero_mem_halfCollarSource t),
    E.fibrePlugCapComponents_core_mem h hlin hc hn d hs heq hρ hρ1 hI hav]
  exact E.fibrePlugCutComponents_torus_mem_iff h hlin hc hn d hs heq hρ hρ1 hI hav r i t


theorem fibrePlugCutSideEquiv_symm (t : Bool) :
    fibrePlugCutSideEquiv.symm t = if t then 0 else 1 := rfl

theorem fibrePlugCutSideEquiv_sign (t : Bool) :
    sphereCutBoundarySide (fibrePlugCutSideEquiv.symm t) = !t := by
  cases t <;> rfl

theorem fibrePlugCutPortEquiv_side (t : Bool) :
    E.fibrePlugCutPortEquiv h hc hn (fibrePlugCutSideEquiv.symm t) =
      E.fibrePlugSideExternalEquiv h hc hn t :=
  congrArg (E.fibrePlugSideExternalEquiv h hc hn) (fibrePlugCutSideEquiv.apply_symm_apply t)

set_option backward.isDefEq.respectTransparency false in
theorem fibrePlugCutComponents_external_side (t : Bool) (τ : Torus) :
    (E.fibrePlugCutBoundary d hs hρ hρ1 hI hav).tori.torusMap
      (E.fibrePlugSideExternalEquiv h hc hn t) τ ∈
        (E.fibrePlugCutComponents h hlin hc hn d hs heq).piece
          (fibrePlugCutSideEquiv.symm t) := by
  rw [← E.fibrePlugCutPortEquiv_side h hc hn t]
  exact E.fibrePlugCutComponents_torus_owned h hlin hc hn d hs heq hρ hρ1 hI hav _ τ

set_option backward.isDefEq.respectTransparency false in
theorem fibrePlugCapComponents_external_side (t : Bool) (τ : Torus) :
    (E.fibrePlugCutBoundary d hs hρ hρ1 hI hav).sphereCapRetained.torusMap
      (E.fibrePlugSideExternalEquiv h hc hn t) τ ∈
        (E.fibrePlugCapComponents h hlin hc hn d hs heq hρ hρ1 hI hav).piece
          (fibrePlugCutSideEquiv.symm t) :=
  (E.fibrePlugCapComponents_torus_mem_iff h hlin hc hn d hs heq hρ hρ1 hI hav
    (E.fibrePlugSideExternalEquiv h hc hn t) (fibrePlugCutSideEquiv.symm t) τ).mpr
      (E.fibrePlugCutPortEquiv_side h hc hn t).symm

set_option backward.isDefEq.respectTransparency false in
theorem fibrePlugCapComponents_one_port (i : Fin 2) :
    Nat.card {r : Fin E.toTorus.externalCount |
      range ((E.fibrePlugCutBoundary d hs hρ hρ1 hI hav).sphereCapRetained.torusMap r) ⊆
        (E.fibrePlugCapComponents h hlin hc hn d hs heq hρ hρ1 hI hav).piece i} = 1 := by
  classical
  have hm (r : Fin E.toTorus.externalCount) :
      range ((E.fibrePlugCutBoundary d hs hρ hρ1 hI hav).sphereCapRetained.torusMap r) ⊆
        (E.fibrePlugCapComponents h hlin hc hn d hs heq hρ hρ1 hI hav).piece i ↔
          r = E.fibrePlugCutPortEquiv h hc hn i := by
    constructor
    · intro hx
      exact (E.fibrePlugCapComponents_torus_mem_iff h hlin hc hn d hs heq hρ hρ1 hI hav
        r i (1, 1)).mp (hx (mem_range_self (1, 1)))
    · intro hr
      rintro x ⟨t, rfl⟩
      exact (E.fibrePlugCapComponents_torus_mem_iff h hlin hc hn d hs heq hρ hρ1 hI hav
        r i t).mpr hr
  have he : {r : Fin E.toTorus.externalCount |
      range ((E.fibrePlugCutBoundary d hs hρ hρ1 hI hav).sphereCapRetained.torusMap r) ⊆
        (E.fibrePlugCapComponents h hlin hc hn d hs heq hρ hρ1 hI hav).piece i} =
      {r | r = E.fibrePlugCutPortEquiv h hc hn i} := by
    ext r
    exact hm r
  rw [he]
  let : Unique {r : Fin E.toTorus.externalCount | r = E.fibrePlugCutPortEquiv h hc hn i} :=
    { default := ⟨E.fibrePlugCutPortEquiv h hc hn i, rfl⟩
      uniq r := Subtype.ext r.property }
  exact Nat.card_unique


set_option backward.isDefEq.respectTransparency false in
theorem fibrePlugCutComponents_offZero_mem (i : Fin 2)
    (x : (boundedPlugCutCarrier d hs).Carrier)
    (hx : x ∈ sphereCutOffZero (boundedPlugCutCollars d)) :
    x ∈ (E.fibrePlugCutComponents h hlin hc hn d hs heq).piece i ↔
      sphereCutFold (boundedPlugCutCollars d) x ∈
        E.fibrePlugSide h hlin (!sphereCutBoundarySide i) :=
  sphereCutSideSet_offZero (boundedPlugCutCollars d) (fibrePlugCutSides E h hlin)
    (sphereCutBoundarySide i) x hx

include h hc hn in
theorem fibrePlugCutPorts_count : E.toTorus.externalCount = 2 := by
  have he := Fintype.card_congr (E.fibrePlugCutPortEquiv h hc hn)
  simpa only [Fintype.card_fin] using he.symm

set_option backward.isDefEq.respectTransparency false in
theorem fibrePlugCapComponents_ball_owned (i : Fin 2) (x : ClosedCell 3) :
    (E.fibrePlugCutBoundary d hs hρ hρ1 hI hav).sphereCapBall i x ∈
      (E.fibrePlugCapComponents h hlin hc hn d hs heq hρ hρ1 hI hav).piece i := by
  let B := E.fibrePlugCutBoundary d hs hρ hρ1 hI hav
  change B.sphereCapBall i x ∈ B.sphereCapComponentSet
    (E.fibrePlugCutComponents h hlin hc hn d hs heq) i
  apply (B.sphereCapComponentSet_ball_mem (E.fibrePlugCutComponents h hlin hc hn d hs heq)
    i i x).mpr
  exact E.fibrePlugCutBoundary_sphere_owner h hlin hc hn d hs heq hρ hρ1 hI hav i

set_option backward.isDefEq.respectTransparency false in
theorem fibrePlugCapComponents_wholeCap_owned (i : Fin 2) (x : ClosedCell 3) :
    (E.fibrePlugCutBoundary d hs hρ hρ1 hI hav).boundedPlugWholeCap i x ∈
      (E.fibrePlugCapComponents h hlin hc hn d hs heq hρ hρ1 hI hav).piece i := by
  rw [MixedBoundaryCertificate.boundedPlugWholeCap_eq]
  exact E.fibrePlugCapComponents_ball_owned h hlin hc hn d hs heq hρ hρ1 hI hav i _

end GC.Seifert.ElementaryPresentation
