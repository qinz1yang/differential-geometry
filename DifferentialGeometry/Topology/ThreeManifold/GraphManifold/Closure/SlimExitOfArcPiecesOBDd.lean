import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.SlimPiecesOfExits74
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.RowsLinkOfStageSrc74
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.SlimArcPiecesComponentsOBDd

/-!
# `SlimExit74` from one slim piece exit per arc piece of `D₃`, in the source form (S-BD2d2, `_OBDd`)

Lane O-BD1 (by S-BD2d2), group G10d, `SlimCutPieces74`. The boundary twin of
`exists_slimExit74_of_exits` (closed route; it uses a carrier identification `ψ : X ≃ W` and
`StageIdent_LND74`): here the slim stage is identified with the decomposition's final map `q`
through its source (`StageIdentSrc_LND74`, so the whole `f₃`-preimage of a base set `S` is
`src ∩ q⁻¹(ι S)`), and the components of `D₃` are the finitely many compact connected pieces
`pc i` of a union (no loops: every component of the slim base domain is a sub-arc).

`exists_slimExit74_of_arcPieces_OBDd`: given the component equivalence `comp` onto the actual
components of the union `Dtot = ⋃ pc` with `ι`-compatible images and, for every piece `pc i`, a slim
piece exit of image `src ∩ q⁻¹(pc i)` satisfying a predicate `Pp i`, there is `Xe : SlimExit74 A D`
whose exit at the component of `pc i` satisfies `Pp i`, and every exit of `Xe` is at some `pc i`.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open GC.GraphManifold.Assembly

namespace GC.GraphManifold.Assembly.FC39P0

variable {W : CompactCarrier.{0}} {n : ℕ} {E : BoundaryTori W n}
  {A : SmoothStageGeometry74 W E} {D : StageCutChoice74 A} {Bs : Type*} [TopologicalSpace Bs]
  [T2Space Bs] {q : W.Carrier → Bs} {ι : A.slim.Base → Bs} {src : Set W.Carrier} {N : ℕ}
  {pc : Fin N → Set Bs}

/-- **`SlimExit74` from one exit per arc piece** (source form, no loops). -/
theorem exists_slimExit74_of_arcPieces_OBDd
    (hid : StageIdentSrc_LND74 A.slim.toStageProj74 q ι src)
    (hcpt : ∀ i, IsCompact (pc i)) (hpre : ∀ i, IsPreconnected (pc i))
    (hne : ∀ i, (pc i).Nonempty) (hdisj : Pairwise fun i j => Disjoint (pc i) (pc j))
    {Dtot : Set Bs} (hU : (⋃ j, pc j) = Dtot)
    (comp : ActualComponent D.D₃ ≃ ActualComponent Dtot)
    (hcomp : ∀ c, ι '' c.1 = (comp c).1)
    (Pp : Fin N → SlimPieceExit74 A.zero A.cusp → Prop)
    (arcX : ∀ i, ∃ x : SlimPieceExit74 A.zero A.cusp,
      range x.piece.map = src ∩ q ⁻¹' pc i ∧ Pp i x) :
    ∃ Xe : SlimExit74 A D, (∀ i, ∃ jx : Fin Xe.count,
      (comp (Xe.componentEquiv jx)).1 = pc i ∧ Pp i (Xe.exit jx)) ∧
      ∀ jx : Fin Xe.count, ∃ i, (comp (Xe.componentEquiv jx)).1 = pc i := by
  subst hU
  choose xa ha hpa using arcX
  let ce := arcPieceComponentEquiv_OBDd hcpt hpre hne hdisj
  let Xe : SlimExit74 A D := {
    count := N
    exit := xa
    componentEquiv := ce.trans comp.symm
    piece_range := fun j => by
      change range (xa j).piece.map = {x | ∃ h : x ∈ A.slim.parent,
        A.slim.proj ⟨x, h⟩ ∈ (comp.symm (ce j)).1}
      rw [ha j, stageSetSrc_LND74 hid, hcomp, comp.apply_symm_apply]
      rfl }
  refine ⟨Xe, fun i => ⟨i, ?_, hpa i⟩, fun jx => ⟨jx, ?_⟩⟩
  · change (comp (comp.symm (ce i))).1 = pc i
    rw [comp.apply_symm_apply]
    rfl
  · change (comp (comp.symm (ce jx))).1 = pc jx
    rw [comp.apply_symm_apply]
    rfl

end GC.GraphManifold.Assembly.FC39P0
