import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0HandleFaceResidual
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0CornersV2
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GArcTraceManifold

/-!
# FC39 GROUP G arcs (A1): partitioned faces are residual faces; the trace of a defining function

Lane FC39-G-ARC (external draft 58 §四 A1, disposition D58-5). For a seam–face link `sf`:

* `FaceLayer.eq_of_partitioned_meet_GARC` — a partitioned face meeting any face of the catalogue is
  that face (`face_disjoint`, the seam conditions are vacuous for a partitioned face);
* `SeamFacesLink.face_nonempty_GARC` — every face of the catalogue is non-empty (an actual
  component);
* `SeamFacesLink.exists_residual_of_partitioned_GARC` — **every partitioned face is the residual
  face of some residual label** (`faceEquiv`, `face_image`, `vertex_piece`; a shared zero / cusp
  internal face or a shared slim end is a whole seam face, an external cusp face is a port face:
  both are excluded by `face_disjoint`; `modelFace_cases`, `endFace_exhausted`).

For a restriction link `Lk` and a global face link `Gk` of the final circle region:

* `GlobalFaceLinkV2.mem_cornerBase_iff_GARC` — `c ∈ C₁(circ) ↔ ι c ∈ C₁(rows)`;
* `CircleRestrictionLink.fibre_eq_GARC` — the row fibre over `ι c` is the circle fibre over `c`;
* `GlobalFaceLinkV2.mem_traceSet_iff_GARC` — **the trace of the defining function `l` is the set of
  points of `C₁(circ)` whose whole fibre lies in the actual face of `l`** (`face_eq`).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly.FC39P0

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n}

/-! ## The face catalogue -/

/-- A partitioned face meeting a face of the catalogue is that face. -/
theorem FaceLayer.eq_of_partitioned_meet_GARC {V : VertexLayer W} {circ : CircleRegion W}
    {S : SeamLayer W V circ} {O : PortLayer W E V} (F : FaceLayer W E V S O)
    {f f' : Fin F.faceCount} (hf : F.faceKind f = .partitioned)
    (h : (F.face f ∩ F.face f').Nonempty) : f = f' := by
  by_contra hne
  have hd := F.face_disjoint f f' hne
    (fun c b hcb => by rw [hf] at hcb; cases hcb.1)
    (fun c b hcb => by rw [hf] at hcb; cases hcb.1)
  rw [Set.disjoint_iff_inter_eq_empty] at hd
  rw [hd] at h
  exact Set.not_nonempty_empty h

/-- The image of a model boundary face is non-empty. -/
theorem ModelBoundaryFace.image_nonempty_GARC {P : PieceEmbedding W} (m : ModelBoundaryFace P) :
    (P.map '' m.1).Nonempty := by
  obtain ⟨x, hx, hm⟩ := m.2
  exact ⟨P.map x, x, by rw [hm]; exact mem_connectedComponentIn hx, rfl⟩

/-- Transport of a model boundary face along an equality of pieces. -/
theorem ModelBoundaryFace.exists_transport_GARC {P Q : PieceEmbedding W} (h : P = Q)
    (m : ModelBoundaryFace P) : ∃ m' : ModelBoundaryFace Q, P.map '' m.1 = Q.map '' m'.1 := by
  subst h
  exact ⟨m, rfl⟩

section Catalogue

variable {Rw : FC39RowsV2 W E} {V : VertexLayer W} {VL : VertexModelLink Rw V}
  {O : PortLayer W E V} {circ : CircleRegion W} {S : SeamLayer W V circ}
  {F : FaceLayer W E V S O} {N : Rw.SharedFace → TopologicalSpace.Opens W.Carrier}

/-- Every face of the catalogue is non-empty. -/
theorem SeamFacesLink.face_nonempty_GARC (sf : SeamFacesLink Rw V VL O S F N)
    (f : Fin F.faceCount) : (F.face f).Nonempty := by
  obtain ⟨m, hm⟩ := sf.exists_face_eq_image f
  rw [hm]
  exact m.image_nonempty_GARC

/-- A partitioned face is not a whole shared slim end (those are seam faces). -/
theorem SeamFacesLink.false_of_partitioned_eq_endSet_GARC (sf : SeamFacesLink Rw V VL O S F N)
    {f : Fin F.faceCount} (hf : F.faceKind f = .partitioned) (e : Rw.slim.End)
    (he : (Rw.slim.endKind e).isSome) (hface : F.face f = Rw.slim.endSet e) : False := by
  let σ : Rw.SharedFace := ⟨e, he⟩
  have hσ : Rw.sharedSet σ = Rw.slim.endSet e := rfl
  cases hs : Rw.sharedShape σ with
  | sphere =>
    let c := sf.sphereEquiv.symm ⟨σ, hs⟩
    have hc : (sf.sphereEquiv c).1 = σ := by
      change (sf.sphereEquiv (sf.sphereEquiv.symm ⟨σ, hs⟩)).1 = σ
      rw [Equiv.apply_symm_apply]
    obtain ⟨f', -, hf'k⟩ := F.sphereSeam_face c true
    have hface' : F.face f' = Rw.slim.endSet e := by
      rw [(F.face_sphereSeam f' c true hf'k).1, sf.sphere_slim c, hc, hσ]
    have hff := F.eq_of_partitioned_meet_GARC hf (f' := f')
      (by rw [hface, ← hface', inter_self]; exact sf.face_nonempty_GARC f')
    rw [hff, hf'k] at hf
    cases hf
  | torus =>
    let c := sf.torusEquiv.symm ⟨σ, hs⟩
    have hc : (sf.torusEquiv c).1 = σ := by
      change (sf.torusEquiv (sf.torusEquiv.symm ⟨σ, hs⟩)).1 = σ
      rw [Equiv.apply_symm_apply]
    obtain ⟨f', -, hf'k⟩ := F.torusSeam_face c true _ (sf.torusSide_eq c true)
    have hface' : F.face f' = Rw.slim.endSet e := by
      rw [(F.face_torusSeam f' c true hf'k).1, sf.torus_slim c, hc, hσ]
    have hff := F.eq_of_partitioned_meet_GARC hf (f' := f')
      (by rw [hface, ← hface', inter_self]; exact sf.face_nonempty_GARC f')
    rw [hff, hf'k] at hf
    cases hf

/-- **A1: every partitioned face is the residual face of some residual label.** -/
theorem SeamFacesLink.exists_residual_of_partitioned_GARC (sf : SeamFacesLink Rw V VL O S F N)
    {f : Fin F.faceCount} (hf : F.faceKind f = .partitioned) :
    ∃ G : Rw.slim.ResidualFace, F.face f = Rw.slim.residualSet G := by
  classical
  obtain ⟨m, hm⟩ := sf.exists_face_eq_image f
  obtain ⟨m', hm'⟩ := ModelBoundaryFace.exists_transport_GARC (VL.vertex_piece (F.faceOwner f)) m
  rw [hm'] at hm
  clear hm' m
  generalize VL.index (F.faceOwner f) = a at m' hm
  rcases a with i | b | j
  · -- a zero domain
    let F0 : NeighbourFace Rw.zero Rw.cusp := .inl ⟨i, m'⟩
    by_cases hsh : ∃ e, Rw.slim.endKind e = some F0
    · obtain ⟨e, he⟩ := hsh
      exfalso
      refine sf.false_of_partitioned_eq_endSet_GARC hf e (by rw [he]; rfl) ?_
      rw [Rw.junctions.shared_eq e F0 he]
      exact hm
    · simp only [not_exists] at hsh
      exact ⟨.inl ⟨F0, hsh⟩, hm⟩
  · -- a cusp core
    rcases Rw.cusp.modelFace_cases b m' with hb | hb
    · let F0 : NeighbourFace Rw.zero Rw.cusp := .inr ⟨b, m', hb⟩
      by_cases hsh : ∃ e, Rw.slim.endKind e = some F0
      · obtain ⟨e, he⟩ := hsh
        exfalso
        refine sf.false_of_partitioned_eq_endSet_GARC hf e (by rw [he]; rfl) ?_
        rw [Rw.junctions.shared_eq e F0 he]
        exact hm
      · simp only [not_exists] at hsh
        exact ⟨.inl ⟨F0, hsh⟩, hm⟩
    · exfalso
      have hface : F.face f = range (E.torusMap b) := by
        rw [hm, hb]
        change (Rw.cusp.piece b).map '' (Rw.cusp.externalModelFace b).1 = _
        rw [Rw.cusp.externalModelFace_eq, ← range_comp]
        exact congrArg range (funext fun t => Rw.cusp.external_end b t)
      obtain ⟨f', hf'k⟩ := F.external_face b
      have hface' : F.face f' = range (E.torusMap b) := (F.face_external f' b hf'k).1
      have hff := F.eq_of_partitioned_meet_GARC hf (f' := f')
        (by rw [hface, ← hface', inter_self]; exact sf.face_nonempty_GARC f')
      rw [hff, hf'k] at hf
      cases hf
  · -- a slim piece
    obtain ⟨bb, hint, he⟩ := Rw.slim.endFace_exhausted j m'
    let e : Rw.slim.End := ⟨(j, bb), hint⟩
    have hface : F.face f = Rw.slim.endSet e := by
      rw [hm, ← he]
      change (Rw.slim.piece j).map '' (Rw.slim.endFace e).1 = _
      rw [Rw.slim.endFace_eq]
      rfl
    cases hk : Rw.slim.endKind e with
    | none => exact ⟨.inr ⟨e, hk⟩, hface⟩
    | some F0 =>
      exfalso
      exact sf.false_of_partitioned_eq_endSet_GARC hf e (by rw [hk]; rfl) hface

end Catalogue

/-! ## The trace of a defining function of the final circle region -/

section Trace

variable {Rw : FC39RowsV2 W E} {circ : CircleRegion W}

/-- The circle fibre of the final circle region over `c` (in `W`). -/
def _root_.GC.GraphManifold.Assembly.CircleRegion.fibre_GARC (R : CircleRegion W) (c : R.Base) : Set W.Carrier :=
  Subtype.val '' (R.proj ⁻¹' {c})

theorem _root_.GC.GraphManifold.Assembly.CircleRegion.fibre_nonempty_GARC (R : CircleRegion W) (c : R.Base) :
    (R.fibre_GARC c).Nonempty := by
  let y := (R.trivialization c).symm (⟨c, R.mem_neighborhood c⟩, 1)
  refine ⟨y.1.1, y.1, ?_, rfl⟩
  have h := R.projection_trivialization c y
  rw [(R.trivialization c).apply_symm_apply] at h
  exact h.symm

/-- The row fibre over `ι c` is the circle fibre over `c`. -/
theorem CircleRestrictionLink.fibre_eq_GARC (Lk : CircleRestrictionLink Rw.circle circ)
    (c : circ.Base) : Rw.circle.fibre (Lk.ι c) = circ.fibre_GARC c := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hyd : (y : W.Carrier) ∈ (circ.domain : Set W.Carrier) := by
      rw [Lk.domain_eq]
      exact ⟨y, ⟨c, hy.symm⟩, rfl⟩
    obtain ⟨hx, hpx⟩ := Lk.proj_eq ⟨y, hyd⟩
    refine ⟨⟨y, hyd⟩, ?_, rfl⟩
    have h1 : Rw.circle.proj ⟨y, hx⟩ = Rw.circle.proj y := rfl
    exact Lk.ι_isOpenEmbedding.injective (hpx.symm.trans (h1.trans hy))
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨hx, hpx⟩ := Lk.proj_eq z
    refine ⟨⟨z, hx⟩, ?_, rfl⟩
    change Rw.circle.proj ⟨z, hx⟩ = Lk.ι c
    rw [hpx, show circ.proj z = c from hz]

variable {GF : GlobalFaceFunctionsV2 Rw} {Lk : CircleRestrictionLink Rw.circle circ}

theorem GlobalFaceLinkV2.defining_eq_fn_GARC (Gk : GlobalFaceLinkV2 GF circ Lk) (f : GF.Face)
    (c : circ.Base) : circ.defining (Gk.faceIndex.symm f) c = GF.fn f (Lk.ι c) := by
  rw [Gk.defining_eq, Equiv.apply_symm_apply]

/-- `c ∈ C₁(circ) ↔ ι c ∈ C₁(rows)`. -/
theorem GlobalFaceLinkV2.mem_cornerBase_iff_GARC (Gk : GlobalFaceLinkV2 GF circ Lk)
    {c : circ.Base} :
    c ∈ circ.cornerBase ↔ Lk.ι c ∈ Rw.circle.cbase := by
  rw [circ.cornerBase_eq, GF.base_eq]
  constructor
  · intro h
    refine ⟨Gk.range_subset ⟨c, rfl⟩, fun f => ?_⟩
    rw [← Gk.defining_eq_fn_GARC]
    exact h _
  · intro h l
    rw [Gk.defining_eq]
    exact h.2 _

/-- **The trace of the defining function `l`**: the points of `C₁(circ)` whose whole circle fibre
lies in the actual face of `l`. -/
theorem GlobalFaceLinkV2.mem_traceSet_iff_GARC (Gk : GlobalFaceLinkV2 GF circ Lk)
    {l : Fin circ.definingCount} {c : circ.Base} :
    c ∈ circ.traceSet_GARC l ↔ c ∈ circ.cornerBase ∧
      circ.fibre_GARC c ⊆ circleFaceSet Rw.slim Rw.edge (Gk.faceOfDefining l) := by
  have hface := GF.face_eq (Gk.faceIndex l)
  have hmem : Lk.ι c ∈ {c' | c' ∈ Rw.circle.cbase ∧ GF.fn (Gk.faceIndex l) c' = 0} ↔
      Lk.ι c ∈ Rw.baseTrace (GF.actualFace (Gk.faceIndex l)) := by
    rw [hface]
  change (c ∈ circ.cornerBase ∧ circ.defining l c = 0) ↔ _
  rw [Gk.defining_eq, Gk.mem_cornerBase_iff_GARC, ← Lk.fibre_eq_GARC]
  exact hmem

end Trace

end GC.GraphManifold.Assembly.FC39P0
