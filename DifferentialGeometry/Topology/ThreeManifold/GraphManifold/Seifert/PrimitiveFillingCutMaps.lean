import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.PrimitiveFillingData

/-!
# Actual maps on the disjoint cut components

Diffeomorphisms of the actual compact cut pieces combine to a diffeomorphism of the entire cut
carrier. The formulas preserve the supplied piece maps, rather than choosing an unrelated carrier
identification. Smoothness follows on each open component of the finite disjoint partition.
-/

set_option autoImplicit false
noncomputable section
open Set
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology
universe u

namespace GC.Seifert.PrimitiveFillingComponents

variable {C C' : CompactCarrier.{u}}

private theorem exists_piece (D : C.Components) (x : C.Carrier) :
    ∃ i, x ∈ D.piece i := by
  have hx : x ∈ ⋃ i, (D.piece i : Set C.Carrier) := by rw [D.covers]; exact mem_univ x
  exact mem_iUnion.mp hx

def index (D : C.Components) (x : C.Carrier) : Fin D.count :=
  Classical.choose (exists_piece D x)

theorem index_mem (D : C.Components) (x : C.Carrier) : x ∈ D.piece (index D x) :=
  Classical.choose_spec (exists_piece D x)

theorem index_eq (D : C.Components) {i : Fin D.count} {x : C.Carrier}
    (hx : x ∈ D.piece i) : index D x = i := by
  by_contra h
  exact disjoint_left.mp (D.disjoint h) (index_mem D x) hx

private theorem piece_point_eq {I : Type*}
    (S : I → TopologicalSpace.Opens C.Carrier) (x : C.Carrier) (i j : I)
    (hij : i = j) (hi : x ∈ S i) (hj : x ∈ S j) :
    (⟨i, ⟨x, hi⟩⟩ : (a : I) × S a) = ⟨j, ⟨x, hj⟩⟩ := by
  subst j
  rfl

variable (D : C.Components) (D' : C'.Components) (e : Fin D.count ≃ Fin D'.count)
  (f : (i : Fin D.count) → D.piece i ≃ₘ⟮C.model, C'.model⟯ D'.piece (e i))

def map (x : C.Carrier) : C'.Carrier :=
  (f (index D x) ⟨x, index_mem D x⟩).val

def inverse (y : C'.Carrier) : C.Carrier :=
  ((f (e.symm (index D' y))).symm
    ⟨y, by rw [Equiv.apply_symm_apply]; exact index_mem D' y⟩).val

theorem map_piece (i : Fin D.count) (x : D.piece i) :
    map D D' e f x.val = (f i x).val := by
  have he := piece_point_eq D.piece x.val (index D x.val) i (index_eq D x.property)
    (index_mem D x.val) x.property
  exact congrArg (fun z : (a : Fin D.count) × D.piece a => (f z.1 z.2).val) he

theorem inverse_piece (i : Fin D.count) (y : D'.piece (e i)) :
    inverse D D' e f y.val = ((f i).symm y).val := by
  have hi : e.symm (index D' y.val) = i :=
    (congrArg e.symm (index_eq D' y.property)).trans (e.symm_apply_apply i)
  have hm : y.val ∈ D'.piece (e (e.symm (index D' y.val))) := by
    rw [Equiv.apply_symm_apply]
    exact index_mem D' y.val
  have he := piece_point_eq (fun a => D'.piece (e a)) y.val
    (e.symm (index D' y.val)) i hi hm y.property
  exact congrArg (fun z : (a : Fin D.count) × D'.piece (e a) => ((f z.1).symm z.2).val) he

theorem map_contMDiff : ContMDiff C.model C'.model ∞ (map D D' e f) := by
  intro x
  let i := index D x
  let z : D.piece i := ⟨x, index_mem D x⟩
  apply (contMDiffAt_subtype_iff (x := z)).mp
  have hfun : (fun a : D.piece i => map D D' e f a.val) =
      fun a => (f i a).val := by
    funext a
    exact map_piece D D' e f i a
  rw [hfun]
  exact (contMDiff_subtype_val.comp (f i).contMDiff).contMDiffAt

theorem inverse_contMDiff : ContMDiff C'.model C.model ∞ (inverse D D' e f) := by
  intro y
  let i := e.symm (index D' y)
  let z : D'.piece (e i) := ⟨y, by rw [Equiv.apply_symm_apply]; exact index_mem D' y⟩
  apply (contMDiffAt_subtype_iff (x := z)).mp
  have hfun : (fun a : D'.piece (e i) => inverse D D' e f a.val) =
      fun a => ((f i).symm a).val := by
    funext a
    exact inverse_piece D D' e f i a
  rw [hfun]
  exact (contMDiff_subtype_val.comp (f i).symm.contMDiff).contMDiffAt

def diffeomorph : C.Carrier ≃ₘ⟮C.model, C'.model⟯ C'.Carrier where
  toFun := map D D' e f
  invFun := inverse D D' e f
  left_inv x := by
    let i := index D x
    let z : D.piece i := ⟨x, index_mem D x⟩
    rw [map_piece D D' e f i z, inverse_piece D D' e f i (f i z)]
    exact congrArg Subtype.val ((f i).symm_apply_apply z)
  right_inv y := by
    let i := e.symm (index D' y)
    let z : D'.piece (e i) := ⟨y, by rw [Equiv.apply_symm_apply]; exact index_mem D' y⟩
    rw [inverse_piece D D' e f i z, map_piece D D' e f i ((f i).symm z)]
    exact congrArg Subtype.val ((f i).apply_symm_apply z)
  contMDiff_toFun := map_contMDiff D D' e f
  contMDiff_invFun := inverse_contMDiff D D' e f

theorem diffeomorph_piece (i : Fin D.count) (x : D.piece i) :
    diffeomorph D D' e f x.val = (f i x).val :=
  map_piece D D' e f i x

theorem diffeomorph_image_piece (i : Fin D.count) :
    diffeomorph D D' e f '' (D.piece i : Set C.Carrier) = (D'.piece (e i) : Set C'.Carrier) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [diffeomorph_piece D D' e f i ⟨x, hx⟩]
    exact Subtype.property _
  · intro hy
    refine ⟨((f i).symm ⟨y, hy⟩).val, Subtype.property _, ?_⟩
    rw [diffeomorph_piece D D' e f i ((f i).symm ⟨y, hy⟩)]
    exact congrArg Subtype.val ((f i).apply_symm_apply ⟨y, hy⟩)

end GC.Seifert.PrimitiveFillingComponents
