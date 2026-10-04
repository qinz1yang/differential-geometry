import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.EmbeddedPieces
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MobiusBlockAssembly

/-!
# Splicing piece systems into a torus presentation

Lane MD6 of `20261003-survey-p1-morse-decomposition.md`, the assembly over `W` (route G).

A `TorusPresentation.Refinement T k` is a cut system of every component carrier of `T`, all with
pieces modelled on `k`, together with a bijection from its external tori to the ports owned by
the component such that the external half collars of the system are the port collars of `T` on
the whole collar. `Refinement.splice` builds the cut system of `W` whose pieces are all the pieces
of all the systems, mapped by the reconstruction of `T`; its seams are the seams of the systems,
carried into `W` by the reconstruction (`newSeam`, a partial diffeomorphism by the inverse
function theorem at interior points), followed by the seams of `T`; its external tori are those
of `T`. The sides are numbered by one equivalence `sideEquiv`, so `sides_bijective` is the
bijectivity of an equivalence. The spliced presentation has the external collars of `T`
(`splice_external_collar`). The trivial refinement (`trivialRefinement`, every component by
itself) splices back to `T`; for `mobiusPresentation` (two-piece seams, Möbius base) this is
checked in `mobiusPresentation_splice_external_collar` and `mobiusPresentation_splice_seam`.

A `ProductRefinement T` adds product certificates to every system; it gives an elementary
presentation of `W` (`ProductRefinement.toElementaryPresentation`). Hence `ElementarizeOnSubCollar`
holds as soon as every raw presentation has a torus presentation with the same external tori at
`s = 0` up to `ψ` which admits a product refinement
(`elementarizeOnSubCollar_of_productRefinement`).
For route G the torus presentation is `(G.reparam ψ).shrink δ` of `SF/CollarGermAdapter.lean`
(`elementarizeOnSubCollar_of_reparam_shrink`): the old seams are the old seams reparametrised and
rescaled, and what is left is a product refinement of each old piece, the per-piece output of
MD1, MD3, MD4 and MD5. Two convenient forms of that input are a `PieceRefinement` (a product
`EmbeddedPieceSystem` of every component carrier) and an `ElementaryRefinement` (an elementary
presentation of every component carrier, for instance a Möbius region presented by
`mobiusPresentation`), each with external collars equal to the port collars on the whole collar
(`elementarizeOnSubCollar_of_pieceRefinement`, `elementarizeOnSubCollar_of_elementaryRefinement`).
-/

set_option autoImplicit false

noncomputable section
open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert

namespace TorusPresentation

variable {W : CompactCarrier.{u}} (T : TorusPresentation W)

abbrev Component (i : Fin T.components.count) : CompactCarrier.{u} :=
  GC.Topology.componentCarrier T.cutCarrier T.components i

structure Refinement (k : CarrierModel) where
  system : ∀ i, EmbeddedCutSystem (T.Component i) k
  port : ∀ i, Fin (system i).externalCount ≃ T.OwnedSide i
  port_collar : ∀ i l p, p ∈ halfCollarSource →
    Subtype.val ((system i).fold ((system i).sideCollar ((system i).externalSide l) p)) =
      T.sideCollar (port i l).val p

theorem cutMap_injOn_interior {x y : T.cutCarrier.Carrier}
    (hx : T.cutCarrier.model.IsInteriorPoint x) (h : T.cutMap x = T.cutMap y) : x = y := by
  have hq : T.pairing.quotientMap x = T.pairing.quotientMap y := T.reconstruction.injective h
  rcases (Quotient.exact hq : T.pairing.gluing.rel x y) with he | ⟨d, hd, -⟩
  · exact he
  · have hb : x ∈ T.cutCarrier.model.boundary T.cutCarrier.Carrier := by
      rw [T.cut_boundary_exhausted]
      exact Or.inl (mem_iUnion.2 ⟨d, hd⟩)
    exact absurd hx ((ModelWithCorners.isBoundaryPoint_iff_not_isInteriorPoint _).mp hb)

theorem cutMap_eq_seam_of_mem_block {x : T.cutCarrier.Carrier} {d : Fin T.pairing.count}
    (hd : x ∈ T.pairing.gluing.block d) : ∃ t, T.cutMap x = T.seam d (t, 0) := by
  rcases hd with hl | hr
  · refine ⟨(T.pairing.leftParam d).symm ⟨x, hl⟩, ?_⟩
    rw [T.seam_zero, Homeomorph.apply_symm_apply]
    rfl
  · refine ⟨(T.pairing.matching d).symm ((T.pairing.rightParam d).symm ⟨x, hr⟩), ?_⟩
    rw [T.seam_zero]
    change T.reconstruction (T.pairing.quotientMap x) = _
    rw [T.quotientMap_leftParam_eq_rightParam_matching, Diffeomorph.apply_symm_apply,
      Homeomorph.apply_symm_apply]

namespace Refinement

variable {T} {k : CarrierModel} (R : T.Refinement k)

abbrev count : ℕ := ∑ i, (R.system i).count

abbrev pieceIndex : Fin R.count ≃ Σ i, Fin (R.system i).count := finSigmaFinEquiv.symm

abbrev Piece (J : Fin R.count) : Type u :=
  (R.system (R.pieceIndex J).1).Piece (R.pieceIndex J).2

def map (J : Fin R.count) (q : R.Piece J) : W.Carrier :=
  T.cutMap ((R.system (R.pieceIndex J).1).map (R.pieceIndex J).2 q).val

abbrev torusCount (J : Fin R.count) : ℕ :=
  (R.system (R.pieceIndex J).1).torusCount (R.pieceIndex J).2

def collar (J : Fin R.count) (l : Fin (R.torusCount J)) :
    PartialDiffeomorph halfCollarModel k.model (Torus × EuclideanHalfSpace 1) (R.Piece J) ∞ :=
  (R.system (R.pieceIndex J).1).collar (R.pieceIndex J).2 l

def reindex : (Σ J, Fin (R.torusCount J)) ≃ Σ i, (R.system i).Side :=
  (Equiv.sigmaCongrLeft R.pieceIndex).trans
    (Equiv.sigmaAssoc fun i j => Fin ((R.system i).torusCount j))

def foldAt (w : Σ i, (R.system i).Side) (p : Torus × EuclideanHalfSpace 1) : W.Carrier :=
  T.cutMap ((R.system w.1).map w.2.1 ((R.system w.1).collar w.2.1 w.2.2 p)).val

theorem map_collar (τ : Σ J, Fin (R.torusCount J)) (p : Torus × EuclideanHalfSpace 1) :
    R.map τ.1 (R.collar τ.1 τ.2 p) = R.foldAt (R.reindex τ) p :=
  rfl

theorem map_collar_symm (w : Σ i, (R.system i).Side) (p : Torus × EuclideanHalfSpace 1) :
    R.map (R.reindex.symm w).1 (R.collar (R.reindex.symm w).1 (R.reindex.symm w).2 p) =
      R.foldAt w p := by
  rw [map_collar, Equiv.apply_symm_apply]

abbrev newSeamCount : ℕ := ∑ i, (R.system i).seamCount

def sideEquiv :
    (Fin (R.newSeamCount + T.pairing.count) × Bool ⊕ Fin T.externalCount) ≃
      Σ J, Fin (R.torusCount J) :=
  (((finSumFinEquiv.symm.prodCongr (Equiv.refl Bool)).trans
      (Equiv.sumProdDistrib _ _ _)).sumCongr (Equiv.refl _)).trans <|
    (Equiv.sumAssoc _ _ _).trans <|
    ((Equiv.refl _).sumCongr (Equiv.ofBijective T.sideSum T.bijective_sideSum)).trans <|
    ((finSigmaFinEquiv.symm.prodCongr (Equiv.refl Bool)).sumCongr
      (Equiv.sigmaFiberEquiv T.sidePiece).symm).trans <|
    ((Equiv.sigmaProdDistrib _ _).sumCongr
      (Equiv.sigmaCongrRight fun i => (R.port i).symm)).trans <|
    (Equiv.sigmaSumDistrib _ _).symm.trans <|
    (Equiv.sigmaCongrRight fun i =>
      Equiv.ofBijective _ (R.system i).sides_bijective).trans R.reindex.symm

theorem sideEquiv_new (i : Fin T.components.count) (c : Fin (R.system i).seamCount) (b : Bool) :
    R.sideEquiv (.inl (finSumFinEquiv (.inl (finSigmaFinEquiv ⟨i, c⟩)), b)) =
      R.reindex.symm ⟨i, (R.system i).side c b⟩ := by
  simp only [sideEquiv, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl,
    Equiv.prodCongr_apply, Prod.map_apply, Equiv.symm_apply_apply, Equiv.refl_apply,
    Equiv.sumProdDistrib_apply_left, Equiv.sumAssoc_apply_inl_inl]
  rfl

theorem sideEquiv_old (d : Fin T.pairing.count) (b : Bool) :
    R.sideEquiv (.inl (finSumFinEquiv (.inr d), b)) =
      R.reindex.symm ⟨T.sidePiece (T.sideSum (.inl (d, b))),
        (R.system _).externalSide ((R.port _).symm ⟨T.sideSum (.inl (d, b)), rfl⟩)⟩ := by
  simp only [sideEquiv, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr,
    Equiv.prodCongr_apply, Prod.map_apply, Equiv.symm_apply_apply, Equiv.refl_apply,
    Equiv.sumProdDistrib_apply_right, Equiv.sumAssoc_apply_inl_inr]
  rfl

theorem sideEquiv_external (m : Fin T.externalCount) :
    R.sideEquiv (.inr m) =
      R.reindex.symm ⟨T.externalPiece m,
        (R.system _).externalSide ((R.port _).symm ⟨.inr (.inr m), rfl⟩)⟩ :=
  rfl

theorem exists_newSeam (z : Σ i, Fin (R.system i).seamCount) :
    ∃ Φ : PartialDiffeomorph signedCollarModel W.model (Torus × ℝ) W.Carrier ∞,
      Φ.toPartialEquiv.source = signedCollarSource ∧
        Φ.toPartialEquiv.target =
          (fun y => T.cutMap ((R.system z.1).seam z.2 y).val) '' signedCollarSource ∧
          Φ.toFun = fun y => T.cutMap ((R.system z.1).seam z.2 y).val := by
  have hint : ∀ y ∈ signedCollarSource,
      T.cutCarrier.model.IsInteriorPoint ((R.system z.1).seam z.2 y).val := by
    intro y hy
    have h := (R.system z.1).seam_interior z.2
      ((R.system z.1).seam z.2 |>.map_source ((R.system z.1).seam_source z.2 ▸ hy))
    exact (ModelWithCorners.isInteriorPoint_iff_isInteriorPoint_val
      (I := T.cutCarrier.model) (u := T.components.piece z.1)).mp h
  refine IsLocalDiffeomorphOn.exists_partialDiffeomorph_of_injOn ?_ isOpen_signedCollarSource'
    ⟨((1 : Torus), 0), by norm_num, by norm_num⟩ ?_
  · rintro ⟨y, hy⟩
    have hs := ((R.system z.1).seam z.2).isLocalDiffeomorphAt signedCollarModel
      (T.Component z.1).model ∞ ((R.system z.1).seam_source z.2 ▸ hy)
    have hv := DifferentialGeometry.isLocalDiffeomorph_subtype_val (I := T.cutCarrier.model)
      (T.components.piece z.1) ((R.system z.1).seam z.2 y)
    exact hs.comp W.model W.Carrier (hv.comp W.model W.Carrier
      (T.isLocalDiffeomorphAt_cutMap (hint y hy)))
  · intro y hy y' hy' h
    have h1 := T.cutMap_injOn_interior (hint y hy) h
    exact ((R.system z.1).seam z.2).toOpenPartialHomeomorph.injOn
      ((R.system z.1).seam_source z.2 ▸ hy) ((R.system z.1).seam_source z.2 ▸ hy')
      (Subtype.ext h1)

def newSeam (z : Σ i, Fin (R.system i).seamCount) :
    PartialDiffeomorph signedCollarModel W.model (Torus × ℝ) W.Carrier ∞ :=
  Classical.choose (R.exists_newSeam z)

theorem newSeam_source (z : Σ i, Fin (R.system i).seamCount) :
    (R.newSeam z).source = signedCollarSource :=
  (Classical.choose_spec (R.exists_newSeam z)).1

theorem newSeam_target (z : Σ i, Fin (R.system i).seamCount) :
    (R.newSeam z).target =
      (fun y => T.cutMap ((R.system z.1).seam z.2 y).val) '' signedCollarSource :=
  (Classical.choose_spec (R.exists_newSeam z)).2.1

theorem newSeam_apply (z : Σ i, Fin (R.system i).seamCount) (y : Torus × ℝ) :
    R.newSeam z y = T.cutMap ((R.system z.1).seam z.2 y).val :=
  congrFun (Classical.choose_spec (R.exists_newSeam z)).2.2 y

def seam (c : Fin (R.newSeamCount + T.pairing.count)) :
    PartialDiffeomorph signedCollarModel W.model (Torus × ℝ) W.Carrier ∞ :=
  Sum.elim (fun c' => R.newSeam (finSigmaFinEquiv.symm c')) T.seam (finSumFinEquiv.symm c)

theorem seam_new (i : Fin T.components.count) (c : Fin (R.system i).seamCount) :
    R.seam (finSumFinEquiv (.inl (finSigmaFinEquiv ⟨i, c⟩))) = R.newSeam ⟨i, c⟩ := by
  simp only [seam, Equiv.symm_apply_apply, Sum.elim_inl]

theorem seam_old (d : Fin T.pairing.count) : R.seam (finSumFinEquiv (.inr d)) = T.seam d := by
  simp only [seam, Equiv.symm_apply_apply, Sum.elim_inr]

theorem seam_source (c : Fin (R.newSeamCount + T.pairing.count)) :
    (R.seam c).source = signedCollarSource := by
  obtain ⟨c', rfl⟩ := finSumFinEquiv.surjective c
  rcases c' with c' | d
  · obtain ⟨⟨i, c⟩, rfl⟩ := finSigmaFinEquiv.surjective c'
    rw [seam_new, newSeam_source]
  · rw [seam_old, T.seam_source]

theorem foldAt_externalSide (i : Fin T.components.count) (l : Fin (R.system i).externalCount)
    {p : Torus × EuclideanHalfSpace 1} (hp : p ∈ halfCollarSource) :
    R.foldAt ⟨i, (R.system i).externalSide l⟩ p = T.cutMap (T.sideCollar (R.port i l).val p) := by
  rw [← R.port_collar i l p hp, EmbeddedCutSystem.fold_sideCollar]
  rfl

theorem foldAt_port (s : T.Side) {p : Torus × EuclideanHalfSpace 1} (hp : p ∈ halfCollarSource) :
    R.foldAt ⟨T.sidePiece s, (R.system _).externalSide ((R.port _).symm ⟨s, rfl⟩)⟩ p =
      T.cutMap (T.sideCollar s p) := by
  rw [R.foldAt_externalSide _ _ hp, Equiv.apply_symm_apply]

theorem seam_neg (c : Fin (R.newSeamCount + T.pairing.count)) (t : Torus) (s : ℝ) (hs : s ≤ 0)
    (h1 : -1 < s) :
    R.seam c (t, s) = R.map (R.sideEquiv (.inl (c, true))).1
      (R.collar _ (R.sideEquiv (.inl (c, true))).2 (t, halfPoint (-s) (neg_nonneg.2 hs))) := by
  have hp : ((t, halfPoint (-s) (neg_nonneg.2 hs)) : Torus × EuclideanHalfSpace 1) ∈
      halfCollarSource := show -s < 1 by linarith
  obtain ⟨c', rfl⟩ := finSumFinEquiv.surjective c
  rcases c' with c' | d
  · obtain ⟨⟨i, c⟩, rfl⟩ := finSigmaFinEquiv.surjective c'
    rw [seam_new, newSeam_apply, sideEquiv_new, map_collar_symm, (R.system i).seam_neg c t s hs h1]
    rfl
  · rw [seam_old, sideEquiv_old, map_collar_symm, R.foldAt_port _ hp, T.seam_negative d t s hs h1]
    rfl

def matching (c : Fin (R.newSeamCount + T.pairing.count)) :
    Torus ≃ₘ⟮torusModel, torusModel⟯ Torus :=
  Sum.elim (fun c' => (R.system (finSigmaFinEquiv.symm c').1).matching
    (finSigmaFinEquiv.symm c').2) T.pairing.matching (finSumFinEquiv.symm c)

theorem matching_new (i : Fin T.components.count) (c : Fin (R.system i).seamCount) :
    R.matching (finSumFinEquiv (.inl (finSigmaFinEquiv ⟨i, c⟩))) = (R.system i).matching c := by
  simp only [matching, Equiv.symm_apply_apply, Sum.elim_inl]
  exact congrArg (fun z : Σ i, Fin (R.system i).seamCount => (R.system z.1).matching z.2)
    (finSigmaFinEquiv.symm_apply_apply ⟨i, c⟩)

theorem matching_old (d : Fin T.pairing.count) :
    R.matching (finSumFinEquiv (.inr d)) = T.pairing.matching d := by
  simp only [matching, Equiv.symm_apply_apply, Sum.elim_inr]

theorem seam_pos (c : Fin (R.newSeamCount + T.pairing.count)) (t : Torus) (s : ℝ) (hs : 0 ≤ s)
    (h1 : s < 1) :
    R.seam c (t, s) = R.map (R.sideEquiv (.inl (c, false))).1
      (R.collar _ (R.sideEquiv (.inl (c, false))).2 (R.matching c t, halfPoint s hs)) := by
  obtain ⟨c', rfl⟩ := finSumFinEquiv.surjective c
  rcases c' with c' | d
  · obtain ⟨⟨i, c⟩, rfl⟩ := finSigmaFinEquiv.surjective c'
    rw [seam_new, newSeam_apply, sideEquiv_new, map_collar_symm, matching_new,
      (R.system i).seam_pos c t s hs h1]
    rfl
  · have hp : ((T.pairing.matching d t, halfPoint s hs) : Torus × EuclideanHalfSpace 1) ∈
        halfCollarSource := h1
    rw [seam_old, sideEquiv_old, map_collar_symm, matching_old, R.foldAt_port _ hp,
      T.seam_positive d t s hs h1]
    rfl

theorem newSeam_isInteriorPoint (z : Σ i, Fin (R.system i).seamCount) {y : Torus × ℝ}
    (hy : y ∈ signedCollarSource) :
    T.cutCarrier.model.IsInteriorPoint ((R.system z.1).seam z.2 y).val := by
  have h := (R.system z.1).seam_interior z.2
    ((R.system z.1).seam z.2 |>.map_source ((R.system z.1).seam_source z.2 ▸ hy))
  exact (ModelWithCorners.isInteriorPoint_iff_isInteriorPoint_val
    (I := T.cutCarrier.model) (u := T.components.piece z.1)).mp h

theorem seam_interior (c : Fin (R.newSeamCount + T.pairing.count)) :
    (R.seam c).target ⊆ W.interior := by
  obtain ⟨c', rfl⟩ := finSumFinEquiv.surjective c
  rcases c' with c' | d
  · obtain ⟨⟨i, c⟩, rfl⟩ := finSigmaFinEquiv.surjective c'
    rw [seam_new, newSeam_target]
    rintro _ ⟨y, hy, rfl⟩
    have hx := R.newSeam_isInteriorPoint ⟨i, c⟩ hy
    exact ((T.isLocalDiffeomorphAt_cutMap hx).isInteriorPoint_iff (by simp)).mp hx
  · rw [seam_old]
    exact T.seam_interior d

theorem smooth_map (J : Fin R.count) : ContMDiff k.model W.model ∞ (R.map J) :=
  T.quotient_smooth.comp (contMDiff_subtype_val.comp ((R.system _).smooth _))

theorem bijective_mfderiv_map_aux (i : Fin T.components.count) (j : Fin (R.system i).count)
    (q : (R.system i).Piece j) :
    Bijective (mfderiv k.model W.model (fun q => T.cutMap ((R.system i).map j q).val) q) := by
  let g : (T.Component i).Carrier → W.Carrier := fun x => T.cutMap x.val
  have hg : ContMDiff (T.Component i).model W.model ∞ g :=
    (T.quotient_smooth.comp contMDiff_subtype_val : ContMDiff T.cutCarrier.model W.model ∞
      (fun x : T.components.piece i => T.cutMap x.val))
  have hgb : Bijective (mfderiv (T.Component i).model W.model g ((R.system i).map j q)) :=
    T.bijective_mfderiv_cutMap_val i ((R.system i).map j q)
  have hm := ((R.system i).smooth j).mdifferentiableAt (x := q) (by simp)
  change Bijective (mfderiv k.model W.model (g ∘ (R.system i).map j) q)
  rw [mfderiv_comp q (hg.mdifferentiableAt (by simp)) hm, ContinuousLinearMap.coe_comp]
  exact hgb.comp ((R.system i).mfderiv_bijective j q)

theorem bijective_mfderiv_map (J : Fin R.count) (q : R.Piece J) :
    Bijective (mfderiv k.model W.model (R.map J) q) :=
  R.bijective_mfderiv_map_aux _ _ q

theorem mem_range_map (z : Σ i, Fin (R.system i).count) (q : (R.system z.1).Piece z.2) :
    T.cutMap ((R.system z.1).map z.2 q).val ∈ ⋃ J, range (R.map J) := by
  obtain ⟨J, rfl⟩ := R.pieceIndex.surjective z
  exact mem_iUnion.2 ⟨J, q, rfl⟩

theorem covers : ⋃ J, range (R.map J) = univ := by
  refine eq_univ_of_forall fun w => ?_
  obtain ⟨q, rfl⟩ := T.reconstruction.surjective w
  induction q using Quotient.inductionOn with
  | h x =>
    have hx : x ∈ ⋃ i, (T.components.piece i : Set T.cutCarrier.Carrier) :=
      T.components.covers ▸ mem_univ x
    obtain ⟨i, hi⟩ := mem_iUnion.1 hx
    have hx' : (⟨x, hi⟩ : (T.Component i).Carrier) ∈ ⋃ j, range ((R.system i).map j) :=
      (R.system i).covers ▸ mem_univ _
    obtain ⟨j, q, hq⟩ := mem_iUnion.1 hx'
    have h := R.mem_range_map ⟨i, j⟩ q
    rw [show ((R.system i).map j q).val = x from congrArg Subtype.val hq] at h
    exact h

theorem external_local (m : Fin T.externalCount) (t : Torus) :
    IsLocalDiffeomorphAt k.model W.model ∞ (R.map (R.sideEquiv (.inr m)).1)
      (R.collar _ (R.sideEquiv (.inr m)).2 (t, halfZero)) := by
  have key : ∀ w : Σ i, (R.system i).Side, w = ⟨T.externalPiece m,
      (R.system _).externalSide ((R.port _).symm ⟨.inr (.inr m), rfl⟩)⟩ →
      IsLocalDiffeomorphAt k.model W.model ∞ (fun q => T.cutMap ((R.system w.1).map w.2.1 q).val)
        ((R.system w.1).collar w.2.1 w.2.2 (t, halfZero)) := by
    rintro w rfl
    have hm := (R.system (T.externalPiece m)).external_local
      ((R.port _).symm ⟨.inr (.inr m), rfl⟩) t
    have e : ((R.system (T.externalPiece m)).map
        ((R.system (T.externalPiece m)).externalSide ((R.port _).symm ⟨.inr (.inr m), rfl⟩)).1
        ((R.system (T.externalPiece m)).collar
          ((R.system (T.externalPiece m)).externalSide ((R.port _).symm ⟨.inr (.inr m), rfl⟩)).1
          ((R.system (T.externalPiece m)).externalSide ((R.port _).symm ⟨.inr (.inr m), rfl⟩)).2
          (t, halfZero))).val = T.cutExternal.collar m (t, halfZero) := by
      rw [← EmbeddedCutSystem.fold_sideCollar,
        R.port_collar _ _ _ (zero_mem_halfCollarSource t), Equiv.apply_symm_apply]
      rfl
    have hv := DifferentialGeometry.isLocalDiffeomorph_subtype_val (I := T.cutCarrier.model)
      (T.components.piece (T.externalPiece m))
      ((R.system (T.externalPiece m)).map
        ((R.system (T.externalPiece m)).externalSide ((R.port _).symm ⟨.inr (.inr m), rfl⟩)).1
        ((R.system (T.externalPiece m)).collar
          ((R.system (T.externalPiece m)).externalSide ((R.port _).symm ⟨.inr (.inr m), rfl⟩)).1
          ((R.system (T.externalPiece m)).externalSide ((R.port _).symm ⟨.inr (.inr m), rfl⟩)).2
          (t, halfZero)))
    have hc := T.isLocalDiffeomorphAt_cutMap_external m t
    rw [← e] at hc
    exact hm.comp W.model W.Carrier (hv.comp W.model W.Carrier hc)
  exact key (R.reindex (R.sideEquiv (.inr m))) (by rw [sideEquiv_external, Equiv.apply_symm_apply])

theorem overlap_aux (z z' : Σ i, Fin (R.system i).count) (q : (R.system z.1).Piece z.2)
    (q' : (R.system z'.1).Piece z'.2)
    (h : T.cutMap ((R.system z.1).map z.2 q).val = T.cutMap ((R.system z'.1).map z'.2 q').val) :
    (⟨z, q⟩ : Σ z : (Σ i, Fin (R.system i).count), (R.system z.1).Piece z.2) = ⟨z', q'⟩ ∨
      (∃ c t, T.cutMap ((R.system z.1).map z.2 q).val = R.newSeam c (t, 0)) ∨
        ∃ d t, T.cutMap ((R.system z.1).map z.2 q).val = T.seam d (t, 0) := by
  obtain ⟨i, j⟩ := z
  obtain ⟨i', j'⟩ := z'
  have hq : T.pairing.quotientMap ((R.system i).map j q).val =
      T.pairing.quotientMap ((R.system i').map j' q').val := T.reconstruction.injective h
  rcases (Quotient.exact hq : T.pairing.gluing.rel _ _) with he | ⟨d, hd, -⟩
  · have hii : i = i' := by
      by_contra hne
      exact (T.components.disjoint hne).le_bot
        ⟨((R.system i).map j q).property, he ▸ ((R.system i').map j' q').property⟩
    subst hii
    rcases (R.system i).overlap j j' q q' (Subtype.ext he) with hs | ⟨c, t, hc⟩
    · left
      obtain ⟨rfl, hqq⟩ := Sigma.mk.inj_iff.mp hs
      rw [eq_of_heq hqq]
    · exact Or.inr (Or.inl ⟨⟨i, c⟩, t, by rw [newSeam_apply, ← hc]⟩)
  · obtain ⟨t, ht⟩ := T.cutMap_eq_seam_of_mem_block hd
    exact Or.inr (Or.inr ⟨d, t, ht⟩)

theorem overlap (J J' : Fin R.count) (q : R.Piece J) (q' : R.Piece J')
    (h : R.map J q = R.map J' q') :
    (⟨J, q⟩ : Σ J, R.Piece J) = ⟨J', q'⟩ ∨ ∃ c t, R.map J q = R.seam c (t, 0) := by
  rcases R.overlap_aux (R.pieceIndex J) (R.pieceIndex J') q q' h with he | ⟨⟨i, c⟩, t, ht⟩ |
      ⟨d, t, ht⟩
  · exact Or.inl ((Equiv.sigmaCongrLeft R.pieceIndex
      (β := fun z : Σ i, Fin (R.system i).count => (R.system z.1).Piece z.2)).injective he)
  · exact Or.inr ⟨_, t, (R.seam_new i c).symm ▸ ht⟩
  · exact Or.inr ⟨_, t, (R.seam_old d).symm ▸ ht⟩

theorem sides_bijective : Bijective (Sum.elim
    (Function.uncurry fun c b => R.sideEquiv (.inl (c, b))) fun m => R.sideEquiv (.inr m)) := by
  have h : Sum.elim (Function.uncurry fun c b => R.sideEquiv (.inl (c, b)))
      (fun m => R.sideEquiv (.inr m)) = R.sideEquiv := by
    funext a
    rcases a with ⟨c, b⟩ | m <;> rfl
  rw [h]
  exact R.sideEquiv.bijective

def splice : EmbeddedCutSystem W k where
  count := R.count
  count_pos := Finset.sum_pos (fun i _ => (R.system i).count_pos)
    (Finset.univ_nonempty_iff.mpr ⟨⟨0, T.components.count_pos⟩⟩)
  Piece := R.Piece
  map := R.map
  smooth := R.smooth_map
  mfderiv_bijective := R.bijective_mfderiv_map
  covers := R.covers
  torusCount := R.torusCount
  collar := R.collar
  collar_source _ := (R.system _).collar_source _
  collar_disjoint _ := (R.system _).collar_disjoint _
  boundary_exhausted _ := (R.system _).boundary_exhausted _
  seamCount := R.newSeamCount + T.pairing.count
  side c b := R.sideEquiv (.inl (c, b))
  externalCount := T.externalCount
  externalSide m := R.sideEquiv (.inr m)
  sides_bijective := R.sides_bijective
  matching := R.matching
  seam := R.seam
  seam_source := R.seam_source
  seam_neg := R.seam_neg
  seam_pos := R.seam_pos
  seam_interior := R.seam_interior
  external_local := R.external_local
  overlap := R.overlap

theorem splice_external_collar (m : Fin T.externalCount) {p : Torus × EuclideanHalfSpace 1}
    (hp : p ∈ halfCollarSource) :
    R.splice.toTorusPresentation.external.collar m p = T.external.collar m p := by
  refine ((R.splice.toTorusPresentation_external_collar m p).trans
    (R.splice.fold_sideCollar _ _)).trans ?_
  change R.foldAt (R.reindex (R.sideEquiv (.inr m))) p = _
  rw [sideEquiv_external, Equiv.apply_symm_apply]
  exact (R.foldAt_port (.inr (.inr m)) hp).trans (T.marked_collar m p hp)

theorem splice_externalCount : R.splice.toTorusPresentation.externalCount = T.externalCount :=
  rfl

theorem splice_seam_old (d : Fin T.pairing.count) :
    R.splice.toTorusPresentation.seam (finSumFinEquiv (.inr d)) = T.seam d :=
  R.seam_old d

theorem splice_matching_old (d : Fin T.pairing.count) :
    R.splice.toTorusPresentation.pairing.matching (finSumFinEquiv (.inr d)) =
      T.pairing.matching d :=
  R.matching_old d

end Refinement

structure ProductRefinement extends T.Refinement .withBoundary where
  certificate : ∀ i, (system i).ProductCertificate

namespace ProductRefinement

variable {T} (R : T.ProductRefinement)

def spliceCertificate : R.splice.ProductCertificate where
  kind_mem _ := (R.certificate _).kind_mem _
  base _ := (R.certificate _).base _
  trivialization _ := (R.certificate _).trivialization _
  collar_eq _ := (R.certificate _).collar_eq _

def toElementaryPresentation : ElementaryPresentation W :=
  R.splice.toElementaryPresentation R.spliceCertificate

theorem toElementaryPresentation_externalCount :
    R.toElementaryPresentation.toTorus.externalCount = T.externalCount :=
  rfl

theorem toElementaryPresentation_external_collar (m : Fin T.externalCount)
    {p : Torus × EuclideanHalfSpace 1} (hp : p ∈ halfCollarSource) :
    R.toElementaryPresentation.toTorus.external.collar m p = T.external.collar m p :=
  R.toRefinement.splice_external_collar m hp

end ProductRefinement

structure PieceRefinement where
  system : ∀ i, EmbeddedPieceSystem (T.Component i)
  port : ∀ i, Fin (system i).externalCount ≃ T.OwnedSide i
  port_collar : ∀ i l p, p ∈ halfCollarSource →
    Subtype.val ((system i).map ((system i).externalSide l).1
      (((system i).base _).collar ((system i).externalSide l).2 (p.1.1, p.2), p.1.2)) =
      T.sideCollar (port i l).val p

def PieceRefinement.toProductRefinement (R : T.PieceRefinement) : T.ProductRefinement where
  system i := (R.system i).toCutSystem
  port := R.port
  port_collar i l p hp := (congrArg Subtype.val
    (((R.system i).toCutSystem.fold_sideCollar ((R.system i).externalSide l) p).trans
      ((R.system i).toCutSystem_map_collar _ _ p))).trans (R.port_collar i l p hp)
  certificate i := (R.system i).certificate

structure ElementaryRefinement where
  presentation : ∀ i, ElementaryPresentation (T.Component i)
  port : ∀ i, Fin (presentation i).toTorus.externalCount ≃ T.OwnedSide i
  port_collar : ∀ i l p, p ∈ halfCollarSource →
    Subtype.val ((presentation i).toTorus.external.collar l p) = T.sideCollar (port i l).val p

def ElementaryRefinement.toPieceRefinement (R : T.ElementaryRefinement) : T.PieceRefinement where
  system i := (R.presentation i).toPieceSystem
  port := R.port
  port_collar i l p hp := (congrArg Subtype.val
    (((R.presentation i).toPieceSystem.toElementaryPresentation_external_collar l p).symm.trans
      ((R.presentation i).toPieceSystem_external_collar l hp))).trans (R.port_collar i l p hp)

end TorusPresentation

namespace TorusPresentation

variable {W : CompactCarrier.{u}} (T : TorusPresentation W)

def trivialRefinement : T.Refinement T.cutCarrier.kind where
  system i := (T.ofPiece i).cutSystem
  port i := (Fintype.equivFin (T.OwnedSide i)).symm
  port_collar i l p hp := by
    have h := (T.ofPiece i).cutSystem_toTorusPresentation_external_collar l hp
    rw [EmbeddedCutSystem.toTorusPresentation_external_collar] at h
    exact (congrArg Subtype.val h).trans (T.pieceCollar_apply i _ hp)

theorem trivialRefinement_splice_external_collar (m : Fin T.externalCount)
    {p : Torus × EuclideanHalfSpace 1} (hp : p ∈ halfCollarSource) :
    T.trivialRefinement.splice.toTorusPresentation.external.collar m p = T.external.collar m p :=
  T.trivialRefinement.splice_external_collar m hp

theorem trivialRefinement_splice_seam_old (d : Fin T.pairing.count) :
    T.trivialRefinement.splice.toTorusPresentation.seam (finSumFinEquiv (.inr d)) = T.seam d :=
  T.trivialRefinement.splice_seam_old d

end TorusPresentation

theorem mobiusPresentation_cutSystem_external_collar (i : Fin 1)
    {p : Torus × EuclideanHalfSpace 1} (hp : p ∈ halfCollarSource) :
    mobiusPresentation.{u}.cutSystem.toTorusPresentation.external.collar i p =
      mobiusPresentation.{u}.external.collar i p :=
  mobiusPresentation.cutSystem_toTorusPresentation_external_collar i hp

theorem mobiusPresentation_cutSystem_seam_two_pieces (c : Fin 2) :
    mobiusPresentation.{u}.cutSystem.toTorusPresentation.leftPiece c ≠
      mobiusPresentation.{u}.cutSystem.toTorusPresentation.rightPiece c :=
  Fin.succ_ne_zero c

theorem mobiusPresentation_splice_external_collar (i : Fin 1)
    {p : Torus × EuclideanHalfSpace 1} (hp : p ∈ halfCollarSource) :
    mobiusPresentation.{u}.trivialRefinement.splice.toTorusPresentation.external.collar i p =
      mobiusPresentation.{u}.external.collar i p :=
  mobiusPresentation.trivialRefinement_splice_external_collar i hp

theorem mobiusPresentation_splice_seam (c : Fin 2) :
    mobiusPresentation.{u}.trivialRefinement.splice.toTorusPresentation.seam
      (finSumFinEquiv (.inr c)) = mobiusPresentation.{u}.seam c :=
  mobiusPresentation.trivialRefinement_splice_seam_old c

theorem elementarizeOnSubCollar_of_productRefinement
    (h : ∀ (W : CompactCarrier.{u}) (G : RawGraphPresentation W),
      ∃ (T : TorusPresentation W) (hT : T.externalCount = G.externalCount)
        (ψ : Fin G.externalCount → (Torus ≃ₘ⟮torusModel, torusModel⟯ Torus)),
        (∀ i t, T.external.collar (Fin.cast hT.symm i) (t, halfZero) =
          G.external.collar i (ψ i t, halfZero)) ∧ Nonempty T.ProductRefinement) :
    ElementarizeOnSubCollar.{u} := by
  refine elementarizeOnSubCollar_of_torus_eq fun W G => ?_
  obtain ⟨T, hT, ψ, h0, ⟨R⟩⟩ := h W G
  exact ⟨R.toElementaryPresentation, hT, ψ, fun i t =>
    (R.toElementaryPresentation_external_collar _ (zero_mem_halfCollarSource t)).trans (h0 i t)⟩

theorem elementarizeOnSubCollar_of_reparam_shrink
    (h : ∀ (W : CompactCarrier.{u}) (G : RawGraphPresentation W),
      ∃ (ψ : G.toTorusPresentation.Side → (Torus ≃ₘ⟮torusModel, torusModel⟯ Torus))
        (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1),
        Nonempty ((G.toTorusPresentation.reparam ψ).shrink hδ hδ1).ProductRefinement) :
    ElementarizeOnSubCollar.{u} := by
  refine elementarizeOnSubCollar_of_productRefinement fun W G => ?_
  obtain ⟨ψ, δ, hδ, hδ1, hR⟩ := h W G
  refine ⟨(G.toTorusPresentation.reparam ψ).shrink hδ hδ1, rfl, fun i => ψ (.inr (.inr i)),
    fun i t => ?_, hR⟩
  exact (congrFun (BoundaryTori.shrink_torusMap (G.toTorusPresentation.reparam ψ).external
    hδ hδ1 i) t).trans rfl


theorem elementarizeOnSubCollar_of_pieceRefinement
    (h : ∀ (W : CompactCarrier.{u}) (G : RawGraphPresentation W),
      ∃ (ψ : G.toTorusPresentation.Side → (Torus ≃ₘ⟮torusModel, torusModel⟯ Torus))
        (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1),
        Nonempty ((G.toTorusPresentation.reparam ψ).shrink hδ hδ1).PieceRefinement) :
    ElementarizeOnSubCollar.{u} :=
  elementarizeOnSubCollar_of_reparam_shrink fun W G => by
    obtain ⟨ψ, δ, hδ, hδ1, ⟨R⟩⟩ := h W G
    exact ⟨ψ, δ, hδ, hδ1, ⟨R.toProductRefinement⟩⟩

theorem elementarizeOnSubCollar_of_elementaryRefinement
    (h : ∀ (W : CompactCarrier.{u}) (G : RawGraphPresentation W),
      ∃ (ψ : G.toTorusPresentation.Side → (Torus ≃ₘ⟮torusModel, torusModel⟯ Torus))
        (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1),
        Nonempty ((G.toTorusPresentation.reparam ψ).shrink hδ hδ1).ElementaryRefinement) :
    ElementarizeOnSubCollar.{u} :=
  elementarizeOnSubCollar_of_pieceRefinement fun W G => by
    obtain ⟨ψ, δ, hδ, hδ1, ⟨R⟩⟩ := h W G
    exact ⟨ψ, δ, hδ, hδ1, ⟨R.toPieceRefinement⟩⟩

end GC.Seifert
