import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.Gluing
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.Peripheral
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Sphere
import DifferentialGeometry.Topology.ThreeManifold.Geometrization.StandardPrimes

/-!
# Two solid tori

Chapter 5, skeleton item C5 (= A3). Algebra: if every edge map `φ i : H →* G i` of a
`Monoid.PushoutI` is surjective, the base map is surjective (`pushoutI_base_surjective`), so is
every factor map (`pushoutI_of_surjective`), and the pushout is commutative when `H` is
(`pushoutI_commutative_of_surjective`).

Topology, for a torus presentation with one pairing torus whose sides lie in different pieces.
The images of the two pieces under the cut map meet only in the seam torus, so the seam separates
(`isSeparating_of_count_eq_one`). Without external tori a piece minus its seam torus is its
interior, which is path-connected, so the image of the piece lies in its region. Shrinking the
collar coordinate to `0` on the other half of the collar (`collarShrink`) is a homotopy from the
identity of the region to a retraction onto the image of the piece, and the cut map is a closed
embedding on the piece, so the region is homotopy equivalent to the piece by a map restricting to
the port on the seam torus (`exists_regionRetraction`, `regionEquivPiece`). A solid-torus piece
(base `PlanarBase 1`, homeomorphic to a closed disc, hence simply connected) has a π₁-surjective
port (`ProductFibredPiece.surjective_map_portMap`) and cyclic π₁. So the seam torus is
π₁-surjective onto both regions of K09's `seamVanKampen`, the amalgam is a quotient of
`π₁(T²)`: π₁ is commutative (`mul_comm_of_twoSolidTori`) and, as a quotient of π₁ of one solid
torus, cyclic (`isCyclic_of_twoSolidTori`). A closed manifold with such a presentation is prime
(`isPrime_of_twoSolidTori`). The Clifford presentation of the three-sphere has one pairing torus,
two pieces and a separating seam (`cliffordTorusPresentation_isSeparating`); its pieces are not
given `SolidTorusPiece` structures here, which needs a `PlanarBase 1` on the unit disc.
-/

set_option autoImplicit false

noncomputable section
open Set
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open DifferentialGeometry.Topology.VanKampen
open scoped Manifold ContDiff Topology unitInterval

universe u

namespace GC.Seifert

section Algebra
variable {ι : Type*} {G : ι → Type*} {H : Type*} [∀ i, Monoid (G i)] [Monoid H]
  {φ : ∀ i, H →* G i}

theorem pushoutI_base_surjective (hφ : ∀ i, Function.Surjective (φ i)) :
    Function.Surjective (Monoid.PushoutI.base φ) := by
  intro x
  induction x using Monoid.PushoutI.induction_on with
  | of i g =>
    obtain ⟨h, rfl⟩ := hφ i g
    exact ⟨h, (Monoid.PushoutI.of_apply_eq_base φ i h).symm⟩
  | base h => exact ⟨h, rfl⟩
  | mul x y hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a * b, map_mul _ a b⟩

theorem mul_comm_of_surjective_monoidHom {A B : Type*} [Monoid A] [Monoid B] (f : A →* B)
    (hf : Function.Surjective f) (hA : ∀ x y : A, x * y = y * x) (x y : B) :
    x * y = y * x := by
  obtain ⟨x, rfl⟩ := hf x
  obtain ⟨y, rfl⟩ := hf y
  rw [← map_mul, hA, map_mul]

theorem pushoutI_commutative_of_surjective (hH : ∀ x y : H, x * y = y * x)
    (hφ : ∀ i, Function.Surjective (φ i)) (a b : Monoid.PushoutI φ) : a * b = b * a := by
  obtain ⟨x, rfl⟩ := pushoutI_base_surjective hφ a
  obtain ⟨y, rfl⟩ := pushoutI_base_surjective hφ b
  rw [← map_mul, hH, map_mul]

theorem pushoutI_of_surjective (hφ : ∀ i, Function.Surjective (φ i)) (i : ι) :
    Function.Surjective (Monoid.PushoutI.of (φ := φ) i) := by
  intro x
  obtain ⟨h, rfl⟩ := pushoutI_base_surjective hφ x
  exact ⟨φ i h, Monoid.PushoutI.of_apply_eq_base φ i h⟩

end Algebra

section FundamentalGroup
variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

private theorem mapOfEq_rfl (f : C(X, Y)) (x : X) :
    FundamentalGroup.mapOfEq f (rfl : f x = f x) = FundamentalGroup.map f x := by
  ext p
  rw [FundamentalGroup.mapOfEq_apply]
  exact Path.Homotopic.Quotient.cast_rfl_rfl _

theorem surjective_fundamentalGroup_map_of_comp (f : C(X, Y)) (g : C(Y, Z)) (x : X)
    (h : Function.Surjective (FundamentalGroup.map (g.comp f) x)) :
    Function.Surjective (FundamentalGroup.map g (f x)) := by
  rw [GC.Topology.fundamentalGroup_map_comp] at h
  exact Function.Surjective.of_comp h

theorem surjective_fundamentalGroup_map_comp (f : C(X, Y)) (g : C(Y, Z)) (x : X)
    (hf : Function.Surjective (FundamentalGroup.map f x))
    (hg : Function.Surjective (FundamentalGroup.map g (f x))) :
    Function.Surjective (FundamentalGroup.map (g.comp f) x) := by
  rw [GC.Topology.fundamentalGroup_map_comp]
  exact hg.comp hf

theorem surjective_fundamentalGroup_map_of_comp_eq (s : C(X, Y)) (f : C(Y, Z)) (p : C(X, Z))
    (h : f.comp s = p) (x : X) (hf : Function.Injective (FundamentalGroup.map f (s x)))
    (hp : Function.Surjective (FundamentalGroup.map p x)) :
    Function.Surjective (FundamentalGroup.map s x) := by
  subst h
  intro a
  obtain ⟨b, hb⟩ := hp (FundamentalGroup.map f (s x) a)
  refine ⟨b, hf ?_⟩
  rw [← hb, GC.Topology.fundamentalGroup_map_comp]
  rfl

theorem surjective_fundamentalGroup_map_homeomorph (e : X ≃ₜ Y) (x : X) :
    Function.Surjective (FundamentalGroup.map (e : C(X, Y)) x) :=
  (bijective_fundamentalGroup_map_of_homotopyEquiv_leftInverse e.symm.toHomotopyEquiv
    (e : C(X, Y)) (fun y => e.symm_apply_apply y) x).2

end FundamentalGroup

theorem PlanarBase.simplyConnectedSpace_one (B : PlanarBase.{u} 1) :
    SimplyConnectedSpace B.surface.Carrier := by
  have he : B.surface.Carrier ≃ₜ Metric.closedBall (0 : ℂ) 3 :=
    B.isSmoothEmbedding.isEmbedding.toHomeomorph.trans
      (Homeomorph.setCongr (B.range_embedding.trans planarModel_one))
  have : ContractibleSpace (Metric.closedBall (0 : ℂ) 3) :=
    (convex_closedBall 0 3).contractibleSpace (Metric.nonempty_closedBall.2 (by norm_num))
  have : ContractibleSpace B.surface.Carrier := he.toHomotopyEquiv.contractibleSpace
  infer_instance

theorem isCyclic_fundamentalGroup_circle (u : Circle) : IsCyclic (FundamentalGroup Circle u) :=
  isCyclic_of_surjective ((fundamentalGroupMulEquivOfHomotopyEquiv
    (Homeomorph.mulLeft u).toHomotopyEquiv 1 u (mul_one u)).symm.trans
      fundamentalGroupCircleEquivInt).symm (MulEquiv.surjective _)

namespace ProductFibredPiece
variable {W : CompactCarrier.{u}} {T : TorusPresentation.{u} W} {i : Fin T.components.count}

theorem isCyclic_fundamentalGroup (P : SolidTorusPiece T i) (y : T.components.piece i) :
    IsCyclic (FundamentalGroup (T.components.piece i) y) := by
  have := P.base.simplyConnectedSpace_one
  obtain ⟨⟨b, u⟩, rfl⟩ : ∃ q, P.trivialization q = y :=
    ⟨P.trivialization.symm y, P.trivialization.apply_symm_apply y⟩
  have := isCyclic_fundamentalGroup_circle u
  let e := P.fundamentalGroupEquiv b u
  refine isCyclic_of_surjective (e.symm.toMonoidHom.comp (MonoidHom.inr _ _))
    fun a => ⟨(e a).2, ?_⟩
  apply e.injective
  simp only [MonoidHom.comp_apply, MonoidHom.inr_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.apply_symm_apply]
  exact Prod.ext (Subsingleton.elim _ _) rfl

theorem surjective_map_portMap (P : SolidTorusPiece T i) (x : Torus) :
    Function.Surjective (FundamentalGroup.map (P.portMap 0) x) := by
  have := P.base.simplyConnectedSpace_one
  intro a
  refine ⟨(fundamentalGroupProdEquiv x.1 x.2).symm
    (1, (P.fundamentalGroupEquiv (P.base.boundaryCircle 0 x.1) x.2 a).2), ?_⟩
  apply (P.fundamentalGroupEquiv (P.base.boundaryCircle 0 x.1) x.2).injective
  rw [P.fundamentalGroupEquiv_map_portMap, MulEquiv.apply_symm_apply]
  exact Prod.ext (Subsingleton.elim _ _) rfl

theorem subsingleton_ownedSide (P : SolidTorusPiece T i) : Subsingleton (T.OwnedSide i) :=
  P.port.symm.subsingleton

end ProductFibredPiece

namespace TorusPresentation
variable {W : CompactCarrier.{u}} (G : TorusPresentation W) (j : Fin G.pairing.count)

def leftPortTorus : C(Torus, G.components.piece (G.leftPiece j)) :=
  (G.pieceBoundaryTori (G.leftPiece j)).boundaryMap (Fintype.equivFin _ ⟨.inl j, rfl⟩)

def rightPortTorus : C(Torus, G.components.piece (G.rightPiece j)) :=
  (G.pieceBoundaryTori (G.rightPiece j)).boundaryMap (Fintype.equivFin _ ⟨.inr (.inl j), rfl⟩)

def matchingMap : C(Torus, Torus) :=
  ((G.pairing.matching j).toHomeomorph : C(Torus, Torus))

def RegionEquivPiece : Prop :=
  (∃ f : C(G.leftRegion j, G.components.piece (G.leftPiece j)),
      (∀ y, Function.Bijective (FundamentalGroup.map f y)) ∧
        f.comp (G.seamTorusToLeft j) = G.leftPortTorus j) ∧
    ∃ f : C(G.rightRegion j, G.components.piece (G.rightPiece j)),
      (∀ y, Function.Bijective (FundamentalGroup.map f y)) ∧
        f.comp (G.seamTorusToRight j) = (G.rightPortTorus j).comp (G.matchingMap j)

theorem leftPortTorus_eq (P : SolidTorusPiece G (G.leftPiece j)) :
    G.leftPortTorus j = P.portMap 0 := by
  have := P.subsingleton_ownedSide
  rw [← P.pieceBoundaryTori_boundaryMap 0, leftPortTorus, Subsingleton.elim (P.port 0)]

theorem rightPortTorus_eq (P : SolidTorusPiece G (G.rightPiece j)) :
    G.rightPortTorus j = P.portMap 0 := by
  have := P.subsingleton_ownedSide
  rw [← P.pieceBoundaryTori_boundaryMap 0, rightPortTorus, Subsingleton.elim (P.port 0)]

theorem leftPiece_ne_rightPiece (P : SolidTorusPiece G (G.leftPiece j)) :
    G.leftPiece j ≠ G.rightPiece j := by
  intro h
  have := P.subsingleton_ownedSide
  have hs := Subsingleton.elim (α := G.OwnedSide (G.leftPiece j)) ⟨.inl j, rfl⟩
    ⟨.inr (.inl j), h.symm⟩
  exact Sum.inl_ne_inr (congrArg Subtype.val hs)

theorem leftPortTorus_apply (t : Torus) :
    (G.leftPortTorus j t : G.cutCarrier.Carrier) = G.pairing.leftParam j t := by
  change (G.pieceCollar (G.leftPiece j) ((Fintype.equivFin _).symm
    (Fintype.equivFin _ ⟨.inl j, rfl⟩)) (t, halfZero) : G.cutCarrier.Carrier) = _
  rw [Equiv.symm_apply_apply, G.pieceCollar_apply _ _ (zero_mem_halfCollarSource t)]
  exact G.pairing.left_zero j t

theorem rightPortTorus_apply (t : Torus) :
    (G.rightPortTorus j t : G.cutCarrier.Carrier) = G.pairing.rightParam j t := by
  change (G.pieceCollar (G.rightPiece j) ((Fintype.equivFin _).symm
    (Fintype.equivFin _ ⟨.inr (.inl j), rfl⟩)) (t, halfZero) : G.cutCarrier.Carrier) = _
  rw [Equiv.symm_apply_apply, G.pieceCollar_apply _ _ (zero_mem_halfCollarSource t)]
  exact G.pairing.right_zero j t

section Separation

theorem continuous_cutMap : Continuous G.cutMap :=
  G.reconstruction.continuous.comp G.pairing.quotientMap.continuous

theorem surjective_cutMap : Function.Surjective G.cutMap := by
  intro w
  obtain ⟨x, hx⟩ := Quotient.mk''_surjective (G.reconstruction.symm w)
  refine ⟨x, ?_⟩
  change G.reconstruction (Quotient.mk'' x) = w
  rw [hx, Homeomorph.apply_symm_apply]

theorem cutMap_mem_seamSurface_of_mem_block (hc : G.pairing.count = 1)
    {x : G.cutCarrier.Carrier} {i : Fin G.pairing.count} (hx : x ∈ G.pairing.gluing.block i) :
    G.cutMap x ∈ G.seamSurface j := by
  have hi := i.isLt
  have hj := j.isLt
  obtain rfl : i = j := Fin.ext (by omega)
  rcases hx with hx | hx
  · refine ⟨(G.pairing.leftParam i).symm ⟨x, hx⟩, ?_⟩
    rw [seamTorus_eq_cutMap, Homeomorph.apply_symm_apply]
  · refine ⟨(G.pairing.matching i).symm ((G.pairing.rightParam i).symm ⟨x, hx⟩), ?_⟩
    rw [seamTorus_eq_cutMap_right, Diffeomorph.apply_symm_apply, Homeomorph.apply_symm_apply]

theorem cutMap_mem_seamSurface_of_eq (hc : G.pairing.count = 1) {x y : G.cutCarrier.Carrier}
    (hxy : G.cutMap x = G.cutMap y) (hne : x ≠ y) : G.cutMap x ∈ G.seamSurface j := by
  rcases Quotient.exact (G.reconstruction.injective hxy) with h | ⟨i, hx, -⟩
  · exact (hne h).elim
  · exact G.cutMap_mem_seamSurface_of_mem_block j hc hx

def pieceImage (i : Fin G.components.count) : Set W.Carrier :=
  G.cutMap '' (G.components.piece i : Set G.cutCarrier.Carrier)

def pieceComplImage (i : Fin G.components.count) : Set W.Carrier :=
  G.cutMap '' (G.components.piece i : Set G.cutCarrier.Carrier)ᶜ

theorem isClosed_pieceImage (i : Fin G.components.count) : IsClosed (G.pieceImage i) :=
  ((G.components.piece_compact i).image G.continuous_cutMap).isClosed

theorem isClosed_pieceComplImage (i : Fin G.components.count) :
    IsClosed (G.pieceComplImage i) :=
  ((G.components.piece i).isOpen.isClosed_compl.isCompact.image G.continuous_cutMap).isClosed

theorem pieceImage_subset_pieceComplImage {i i' : Fin G.components.count} (h : i ≠ i') :
    G.pieceImage i' ⊆ G.pieceComplImage i :=
  image_mono fun _ hx hx' => Set.disjoint_left.mp (G.components.disjoint h) hx' hx

theorem pieceImage_inter_pieceComplImage_subset (hc : G.pairing.count = 1)
    (i : Fin G.components.count) :
    G.pieceImage i ∩ G.pieceComplImage i ⊆ G.seamSurface j := by
  rintro w ⟨⟨x, hx, rfl⟩, ⟨y, hy, hxy⟩⟩
  exact G.cutMap_mem_seamSurface_of_eq j hc hxy.symm fun h => hy (h ▸ hx)

theorem leftPoint_mem_pieceImage : G.leftPoint j ∈ G.pieceImage (G.leftPiece j) := by
  have hp : ((1, 1), halfPoint 2⁻¹ (by norm_num)) ∈ halfCollarSource := by
    change (2 : ℝ)⁻¹ < 1
    norm_num
  refine ⟨G.pairing.leftCollar j ((1, 1), halfPoint 2⁻¹ (by norm_num)),
    G.sideCollar_target_subset (.inl j)
      ((G.pairing.leftCollar j).map_source (by rw [G.pairing.left_source]; exact hp)), ?_⟩
  rw [G.cutMap_leftCollar j hp]
  rfl

theorem rightPoint_mem_pieceImage : G.rightPoint j ∈ G.pieceImage (G.rightPiece j) := by
  have hp : (G.pairing.matching j (1, 1), halfPoint 2⁻¹ (by norm_num)) ∈ halfCollarSource := by
    change (2 : ℝ)⁻¹ < 1
    norm_num
  refine ⟨G.pairing.rightCollar j (G.pairing.matching j (1, 1), halfPoint 2⁻¹ (by norm_num)),
    G.sideCollar_target_subset (.inr (.inl j))
      ((G.pairing.rightCollar j).map_source (by rw [G.pairing.right_source]; exact hp)), ?_⟩
  rw [G.cutMap_rightCollar j hp, Diffeomorph.symm_apply_apply]
  rfl

theorem pathComponentIn_subset_pieceImage (hc : G.pairing.count = 1)
    (i : Fin G.components.count) {p : W.Carrier} (hp : p ∈ G.pieceImage i)
    (hpS : p ∉ G.seamSurface j) :
    pathComponentIn (G.seamSurface j)ᶜ p ⊆ G.pieceImage i := by
  have hS := G.pieceImage_inter_pieceComplImage_subset j hc i
  have hcover : pathComponentIn (G.seamSurface j)ᶜ p ⊆ G.pieceImage i ∪ G.pieceComplImage i := by
    intro w _
    obtain ⟨x, rfl⟩ := G.surjective_cutMap w
    by_cases hx : x ∈ G.components.piece i
    · exact Or.inl ⟨x, hx, rfl⟩
    · exact Or.inr ⟨x, hx, rfl⟩
  have hempty : pathComponentIn (G.seamSurface j)ᶜ p ∩
      (G.pieceImage i ∩ G.pieceComplImage i) = ∅ :=
    eq_empty_iff_forall_notMem.2 fun w hw => pathComponentIn_subset hw.1 (hS hw.2)
  rcases isPreconnected_iff_subset_of_disjoint_closed.1
    (isPathConnected_pathComponentIn hpS).isConnected.isPreconnected _ _
    (G.isClosed_pieceImage _) (G.isClosed_pieceComplImage _) hcover hempty with h | h
  · exact h
  · exact (hpS (hS ⟨hp, h (mem_pathComponentIn_self hpS)⟩)).elim

theorem leftSide_subset_pieceImage (hc : G.pairing.count = 1) :
    G.leftSide j ⊆ G.pieceImage (G.leftPiece j) :=
  G.pathComponentIn_subset_pieceImage j hc _ (G.leftPoint_mem_pieceImage j)
    (G.leftPoint_mem_compl j)

theorem rightSide_subset_pieceImage (hc : G.pairing.count = 1) :
    G.rightSide j ⊆ G.pieceImage (G.rightPiece j) :=
  G.pathComponentIn_subset_pieceImage j hc _ (G.rightPoint_mem_pieceImage j)
    (G.rightPoint_mem_compl j)

theorem isSeparating_of_count_eq_one (hc : G.pairing.count = 1)
    (hLR : G.leftPiece j ≠ G.rightPiece j) : G.IsSeparating j := by
  rw [isSeparating_iff]
  intro h
  exact G.rightPoint_mem_compl j (G.pieceImage_inter_pieceComplImage_subset j hc _
    ⟨G.leftSide_subset_pieceImage j hc h,
      G.pieceImage_subset_pieceComplImage hLR (G.rightPoint_mem_pieceImage j)⟩)

end Separation

section Collar

private theorem shrink_mem_signedCollarSource (τ : I) {p : Torus × ℝ}
    (hp : p ∈ signedCollarSource) : (p.1, (1 - (τ : ℝ)) * p.2) ∈ signedCollarSource := by
  obtain ⟨h1, h2⟩ := hp
  have h0 := τ.2.1
  have h1' := τ.2.2
  rcases le_or_gt 0 p.2 with hs | hs
  · constructor <;> nlinarith
  · constructor <;> nlinarith

private theorem symm_mem_signedCollarSource {w : W.Carrier} (hw : w ∈ G.seamCollar j) :
    (G.seam j).symm w ∈ signedCollarSource :=
  G.seam_source j ▸ (G.seam j).map_target' hw

def collarShrink (p : I × W.Carrier) : W.Carrier :=
  G.seam j (((G.seam j).symm p.2).1, (1 - (p.1 : ℝ)) * ((G.seam j).symm p.2).2)

theorem continuousOn_collarShrink :
    ContinuousOn (G.collarShrink j) (univ ×ˢ G.seamCollar j) := by
  have hs : ContinuousOn (fun p : I × W.Carrier => (G.seam j).symm p.2)
      (univ ×ˢ G.seamCollar j) :=
    (G.seam j).contMDiffOn_invFun.continuousOn.comp continuous_snd.continuousOn fun p hp => hp.2
  refine (G.continuousOn_seam j).comp
    ((continuous_fst.comp_continuousOn hs).prodMk
      (((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).continuousOn).mul
        (continuous_snd.comp_continuousOn hs))) fun p hp => ?_
  exact G.mem_seam_source j
    (shrink_mem_signedCollarSource p.1 (G.symm_mem_signedCollarSource j hp.2))

theorem collarShrink_mem_seamCollar (τ : I) {w : W.Carrier} (hw : w ∈ G.seamCollar j) :
    G.collarShrink j (τ, w) ∈ G.seamCollar j :=
  (G.seam j).map_source' (G.mem_seam_source j
    (shrink_mem_signedCollarSource τ (G.symm_mem_signedCollarSource j hw)))

theorem collarShrink_zero {w : W.Carrier} (hw : w ∈ G.seamCollar j) :
    G.collarShrink j (0, w) = w := by
  simp only [collarShrink, Set.Icc.coe_zero, sub_zero, one_mul, Prod.mk.eta]
  exact (G.seam j).right_inv' hw

theorem collarShrink_one_mem_seamSurface (w : W.Carrier) :
    G.collarShrink j (1, w) ∈ G.seamSurface j := by
  refine ⟨((G.seam j).symm w).1, ?_⟩
  simp only [collarShrink, Set.Icc.coe_one, sub_self, zero_mul]
  rfl

theorem collarShrink_of_mem_seamSurface (τ : I) {w : W.Carrier} (hw : w ∈ G.seamSurface j) :
    G.collarShrink j (τ, w) = w := by
  obtain ⟨t, rfl⟩ := hw
  have h : (G.seam j).symm (G.seamTorus j t) = (t, 0) :=
    (G.seam j).left_inv' (G.mem_seam_source j ⟨by norm_num, by norm_num⟩)
  simp only [collarShrink, h, mul_zero]
  rfl

end Collar

section Pieces

theorem eq_of_mem_piece {x : G.cutCarrier.Carrier} {a b : Fin G.components.count}
    (ha : x ∈ G.components.piece a) (hb : x ∈ G.components.piece b) : a = b := by
  by_contra h
  exact Set.disjoint_left.mp (G.components.disjoint h) ha hb

theorem flip_notMem_piece (hLR : G.leftPiece j ≠ G.rightPiece j) {x : G.cutCarrier.Carrier}
    (hx : x ∈ G.pairing.gluing.block j) {i : Fin G.components.count}
    (hxi : x ∈ G.components.piece i) : G.pairing.gluing.flip j x ∉ G.components.piece i := by
  intro hfi
  rcases hx with hx | hx
  · have hf : G.pairing.gluing.flip j x ∈ G.components.piece (G.rightPiece j) := by
      rw [G.pairing.gluing.flip_of_mem_left hx]
      exact G.right_owned j (G.pairing.gluing.attaching j ⟨x, hx⟩).2
    exact hLR ((G.eq_of_mem_piece (G.left_owned j hx) hxi).trans (G.eq_of_mem_piece hfi hf))
  · have hf : G.pairing.gluing.flip j x ∈ G.components.piece (G.leftPiece j) := by
      rw [G.pairing.gluing.flip_of_mem_right hx]
      exact G.left_owned j ((G.pairing.gluing.attaching j).symm ⟨x, hx⟩).2
    exact hLR ((G.eq_of_mem_piece hf hfi).trans (G.eq_of_mem_piece hxi (G.right_owned j hx)))

theorem injOn_cutMap (hc : G.pairing.count = 1) (hLR : G.leftPiece j ≠ G.rightPiece j)
    (i : Fin G.components.count) :
    InjOn G.cutMap (G.components.piece i : Set G.cutCarrier.Carrier) := by
  intro x hx y hy hxy
  rcases Quotient.exact (G.reconstruction.injective hxy) with h | ⟨k, hk, rfl⟩
  · exact h
  · have hk' := k.isLt
    have hj := j.isLt
    obtain rfl : k = j := Fin.ext (by omega)
    exact (G.flip_notMem_piece k hLR hk hx hy).elim

theorem mem_block_of_cutMap_mem_seamSurface {x : G.cutCarrier.Carrier}
    (h : G.cutMap x ∈ G.seamSurface j) : ∃ k, x ∈ G.pairing.gluing.block k := by
  obtain ⟨t, ht⟩ := h
  rw [seamTorus_eq_cutMap] at ht
  rcases Quotient.exact (G.reconstruction.injective ht) with h | ⟨k, hk, rfl⟩
  · exact ⟨j, Or.inl (h ▸ (G.pairing.leftParam j t).2)⟩
  · exact ⟨k, G.pairing.gluing.flip_mem_block hk⟩

theorem not_isInteriorPoint_of_mem_block {x : G.cutCarrier.Carrier} {k : Fin G.pairing.count}
    (hx : x ∈ G.pairing.gluing.block k) : ¬ G.cutCarrier.model.IsInteriorPoint x := by
  rw [ModelWithCorners.isInteriorPoint_iff_not_isBoundaryPoint, not_not]
  have hb : x ∈ G.cutCarrier.model.boundary G.cutCarrier.Carrier := by
    rw [G.cut_boundary_exhausted]
    exact Or.inl (mem_iUnion.mpr ⟨k, hx⟩)
  exact hb

theorem isInteriorPoint_of_forall_notMem_block (hext : G.externalCount = 0)
    {x : G.cutCarrier.Carrier}
    (hx : ∀ k, x ∉ G.pairing.gluing.block k) : G.cutCarrier.model.IsInteriorPoint x := by
  rw [ModelWithCorners.isInteriorPoint_iff_not_isBoundaryPoint]
  intro hb
  have hb' : x ∈ G.cutCarrier.model.boundary G.cutCarrier.Carrier := hb
  rw [G.cut_boundary_exhausted] at hb'
  rcases hb' with hb' | hb'
  · obtain ⟨k, hk⟩ := mem_iUnion.mp hb'
    exact hx k hk
  · obtain ⟨k, -⟩ := mem_iUnion.mp hb'
    have := k.isLt
    omega

theorem cutMap_notMem_seamSurface_of_mem_pieceInterior {i : Fin G.components.count}
    {x : G.cutCarrier.Carrier} (hx : x ∈ G.cutCarrier.pieceInterior (G.components.piece i)) :
    G.cutMap x ∉ G.seamSurface j := by
  intro h
  obtain ⟨k, hk⟩ := G.mem_block_of_cutMap_mem_seamSurface j h
  exact G.not_isInteriorPoint_of_mem_block hk hx.2

theorem mem_pieceInterior_of_cutMap_notMem (hext : G.externalCount = 0)
    (hc : G.pairing.count = 1) {i : Fin G.components.count} {x : G.cutCarrier.Carrier}
    (hx : x ∈ G.components.piece i) (hS : G.cutMap x ∉ G.seamSurface j) :
    x ∈ G.cutCarrier.pieceInterior (G.components.piece i) :=
  ⟨hx, G.isInteriorPoint_of_forall_notMem_block hext fun _ hk =>
    hS (G.cutMap_mem_seamSurface_of_mem_block j hc hk)⟩

theorem isPathConnected_pieceInterior (i : Fin G.components.count) :
    IsPathConnected
      (G.cutCarrier.pieceInterior (G.components.piece i) : Set G.cutCarrier.Carrier) := by
  have := Manifold.locallyPathConnectedSpace_of_modelWithCorners (M := G.cutCarrier.Carrier)
    G.cutCarrier.model
  have := G.components.interior_connected i
  exact (G.cutCarrier.pieceInterior
    (G.components.piece i)).isOpen.isConnected_iff_isPathConnected.mp
      (isConnected_iff_connectedSpace.mpr inferInstance)

theorem pieceImage_subset_pathComponentIn (hext : G.externalCount = 0)
    (hc : G.pairing.count = 1) (i : Fin G.components.count) {p : W.Carrier}
    (hp : p ∈ G.pieceImage i) (hpS : p ∉ G.seamSurface j) :
    G.pieceImage i ⊆ pathComponentIn (G.seamSurface j)ᶜ p ∪ G.seamSurface j := by
  have hQ : G.cutMap '' (G.cutCarrier.pieceInterior (G.components.piece i) : Set _) ⊆
      pathComponentIn (G.seamSurface j)ᶜ p := by
    obtain ⟨y, hy, rfl⟩ := hp
    exact ((G.isPathConnected_pieceInterior i).image G.continuous_cutMap).subset_pathComponentIn
      ⟨y, G.mem_pieceInterior_of_cutMap_notMem j hext hc hy hpS, rfl⟩
      (by rintro _ ⟨x, hx, rfl⟩; exact G.cutMap_notMem_seamSurface_of_mem_pieceInterior j hx)
  rintro _ ⟨x, hx, rfl⟩
  by_cases hS : G.cutMap x ∈ G.seamSurface j
  · exact Or.inr hS
  · exact Or.inl (hQ ⟨x, G.mem_pieceInterior_of_cutMap_notMem j hext hc hx hS, rfl⟩)

end Pieces

section Region

theorem exists_regionRetraction (hc : G.pairing.count = 1) (i : Fin G.components.count)
    (U : Set W.Carrier) (hinj : InjOn G.cutMap (G.components.piece i : Set G.cutCarrier.Carrier))
    (hS : G.seamSurface j ⊆ G.pieceImage i) (hKU : G.pieceImage i ⊆ U)
    (hCU : G.seamCollar j ⊆ U) (hUC : U ∩ G.pieceComplImage i ⊆ G.seamCollar j) :
    ∃ f : C(U, G.components.piece i), (∀ y, Function.Bijective (FundamentalGroup.map f y)) ∧
      ∀ (x : G.components.piece i) (hx : G.cutMap x ∈ U), f ⟨G.cutMap x, hx⟩ = x := by
  classical
  have : CompactSpace (G.components.piece i) :=
    isCompact_iff_compactSpace.mp (G.components.piece_compact i)
  let c : C(G.components.piece i, W.Carrier) :=
    ⟨fun x => G.cutMap x, G.continuous_cutMap.comp continuous_subtype_val⟩
  have hcinj : Function.Injective c := fun x y h => Subtype.ext (hinj x.2 y.2 h)
  have hemb : Topology.IsEmbedding c := (c.continuous.isClosedEmbedding hcinj).isEmbedding
  have hrange : range c = G.pieceImage i := by
    ext w
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, x.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  have hcover : ∀ w, w ∈ G.pieceImage i ∨ w ∈ G.pieceComplImage i := by
    intro w
    obtain ⟨x, rfl⟩ := G.surjective_cutMap w
    by_cases hx : x ∈ G.components.piece i
    · exact Or.inl ⟨x, hx, rfl⟩
    · exact Or.inr ⟨x, hx, rfl⟩
  have hKK := G.pieceImage_inter_pieceComplImage_subset j hc i
  let R : I × U → W.Carrier := fun p =>
    if p.2.1 ∈ G.pieceImage i then p.2.1 else G.collarShrink j (p.1, p.2.1)
  have hRK' : ∀ p : I × U, p.2.1 ∈ G.pieceComplImage i →
      R p = G.collarShrink j (p.1, p.2.1) := by
    intro p hp
    by_cases hK : p.2.1 ∈ G.pieceImage i
    · simp only [R, ite_eq_left hK]
      exact (G.collarShrink_of_mem_seamSurface j p.1 (hKK ⟨hK, hp⟩)).symm
    · simp only [R, ite_eq_right hK]
  have hR : Continuous R := by
    have hA : IsClosed {p : I × U | p.2.1 ∈ G.pieceImage i} :=
      (G.isClosed_pieceImage i).preimage (continuous_subtype_val.comp continuous_snd)
    have hB : IsClosed {p : I × U | p.2.1 ∈ G.pieceComplImage i} :=
      (G.isClosed_pieceComplImage i).preimage (continuous_subtype_val.comp continuous_snd)
    have hAB : {p : I × U | p.2.1 ∈ G.pieceImage i} ∪
        {p : I × U | p.2.1 ∈ G.pieceComplImage i} = univ :=
      eq_univ_of_forall fun p => hcover p.2.1
    rw [← continuousOn_univ, ← hAB]
    refine ContinuousOn.union_of_isClosed ?_ ?_ hA hB
    · refine (continuous_subtype_val.comp continuous_snd).continuousOn.congr fun p hp => ?_
      simp only [R, ite_eq_left (show p.2.1 ∈ G.pieceImage i from hp), Function.comp_apply]
    · exact ((G.continuousOn_collarShrink j).comp
        (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)).continuousOn
        fun p hp => ⟨trivial, hUC ⟨p.2.2, hp⟩⟩).congr fun p hp => hRK' p hp
  have hRU : ∀ p, R p ∈ U := by
    intro p
    by_cases hK : p.2.1 ∈ G.pieceImage i
    · simp only [R, ite_eq_left hK]
      exact p.2.2
    · simp only [R, ite_eq_right hK]
      exact hCU (G.collarShrink_mem_seamCollar j p.1
        (hUC ⟨p.2.2, (hcover p.2.1).resolve_left hK⟩))
  have hR0 : ∀ u : U, R (0, u) = u := by
    intro u
    by_cases hK : u.1 ∈ G.pieceImage i
    · simp only [R, ite_eq_left hK]
    · simp only [R, ite_eq_right hK]
      exact G.collarShrink_zero j (hUC ⟨u.2, (hcover u.1).resolve_left hK⟩)
  have hR1 : ∀ u : U, R (1, u) ∈ range c := by
    intro u
    rw [hrange]
    by_cases hK : u.1 ∈ G.pieceImage i
    · simp only [R, ite_eq_left hK]
      exact hK
    · simp only [R, ite_eq_right hK]
      exact hS (G.collarShrink_one_mem_seamSurface j _)
  let e := hemb.toHomeomorph
  have key : ∀ (w : W.Carrier) (hw : w ∈ range c) (x : G.components.piece i), w = c x →
      e.symm ⟨w, hw⟩ = x := by
    rintro w hw x rfl
    exact hemb.toHomeomorph_symm_apply x
  let f : C(U, G.components.piece i) :=
    ⟨fun u => e.symm ⟨R (1, u), hR1 u⟩, e.symm.continuous.comp
      ((hR.comp (continuous_const.prodMk continuous_id)).subtype_mk _)⟩
  let g : C(G.components.piece i, U) :=
    ⟨fun x => ⟨c x, hKU ⟨x, x.2, rfl⟩⟩, c.continuous.subtype_mk _⟩
  have hfg : ∀ x, f (g x) = x := fun x =>
    key _ _ x (ite_eq_left (show c x ∈ G.pieceImage i from ⟨x, x.2, rfl⟩))
  have hgf : ∀ u, (g (f u)).1 = R (1, u) := fun u =>
    congrArg Subtype.val (e.apply_symm_apply ⟨R (1, u), hR1 u⟩)
  let H : ContinuousMap.Homotopy (ContinuousMap.id U) (g.comp f) :=
    { toFun := fun p => ⟨R p, hRU p⟩
      continuous_toFun := hR.subtype_mk _
      map_zero_left := fun u => Subtype.ext (hR0 u)
      map_one_left := fun u => Subtype.ext (hgf u).symm }
  let E : ContinuousMap.HomotopyEquiv U (G.components.piece i) :=
    { toFun := f
      invFun := g
      left_inv := ⟨H.symm⟩
      right_inv := by
        rw [show f.comp g = ContinuousMap.id _ from ContinuousMap.ext hfg] }
  refine ⟨f, fun y => ?_, fun x _ => hfg x⟩
  have h : Function.Bijective (FundamentalGroup.mapOfEq f (rfl : f y = f y)) :=
    fundamentalGroup_mapOfEq_bijective_of_homotopyEquiv E y (f y) rfl
  rwa [mapOfEq_rfl] at h

theorem regionEquivPiece (hext : G.externalCount = 0) (hc : G.pairing.count = 1)
    (hLR : G.leftPiece j ≠ G.rightPiece j) : G.RegionEquivPiece j := by
  have hKK := G.pieceImage_inter_pieceComplImage_subset j hc
  have hSC := G.seamSurface_subset_seamCollar j
  have hSL : G.seamSurface j ⊆ G.pieceImage (G.leftPiece j) := by
    rintro _ ⟨t, rfl⟩
    exact ⟨_, G.left_owned j (G.pairing.leftParam j t).2, (G.seamTorus_eq_cutMap j t).symm⟩
  have hSR : G.seamSurface j ⊆ G.pieceImage (G.rightPiece j) := by
    rintro _ ⟨t, rfl⟩
    exact ⟨_, G.right_owned j (G.pairing.rightParam j _).2,
      (G.seamTorus_eq_cutMap_right j t).symm⟩
  have hlK := G.leftSide_subset_pieceImage j hc
  have hrK := G.rightSide_subset_pieceImage j hc
  obtain ⟨f, hf, hfx⟩ := G.exists_regionRetraction j hc (G.leftPiece j) (G.leftRegion j)
    (G.injOn_cutMap j hc hLR _) hSL
    (fun w hw => (G.pieceImage_subset_pathComponentIn j hext hc _ (G.leftPoint_mem_pieceImage j)
      (G.leftPoint_mem_compl j) hw).imp id fun h => hSC h)
    subset_union_right
    (fun w hw => hw.1.elim (fun h => hSC (hKK _ ⟨hlK h, hw.2⟩)) id)
  obtain ⟨g, hg, hgx⟩ := G.exists_regionRetraction j hc (G.rightPiece j) (G.rightRegion j)
    (G.injOn_cutMap j hc hLR _) hSR
    (fun w hw => (G.pieceImage_subset_pathComponentIn j hext hc _ (G.rightPoint_mem_pieceImage j)
      (G.rightPoint_mem_compl j) hw).imp id fun h => hSC h)
    subset_union_right
    (fun w hw => hw.1.elim (fun h => hSC (hKK _ ⟨hrK h, hw.2⟩)) id)
  refine ⟨⟨f, hf, ContinuousMap.ext fun t => ?_⟩, ⟨g, hg, ContinuousMap.ext fun t => ?_⟩⟩
  · let x : G.components.piece (G.leftPiece j) :=
      ⟨G.pairing.leftParam j t, G.left_owned j (G.pairing.leftParam j t).2⟩
    have hx : G.seamTorusToLeft j t = ⟨G.cutMap x, (G.seamTorus_eq_cutMap j t) ▸
        (G.seamTorusToLeft j t).2⟩ :=
      Subtype.ext (G.seamTorus_eq_cutMap j t)
    rw [ContinuousMap.comp_apply, hx, hfx]
    exact Subtype.ext (G.leftPortTorus_apply j t).symm
  · let x : G.components.piece (G.rightPiece j) :=
      ⟨G.pairing.rightParam j (G.pairing.matching j t),
        G.right_owned j (G.pairing.rightParam j _).2⟩
    have hx : G.seamTorusToRight j t = ⟨G.cutMap x, (G.seamTorus_eq_cutMap_right j t) ▸
        (G.seamTorusToRight j t).2⟩ :=
      Subtype.ext (G.seamTorus_eq_cutMap_right j t)
    rw [ContinuousMap.comp_apply, hx, hgx]
    exact Subtype.ext (G.rightPortTorus_apply j _).symm

end Region

theorem surjective_seamAmalgamation (h : G.IsSeparating j)
    (hl : Function.Surjective (FundamentalGroup.map (G.seamTorusToLeft j) torusBase))
    (hr : Function.Surjective (FundamentalGroup.map (G.seamTorusToRight j) torusBase)) :
    ∀ i, Function.Surjective (fundamentalGroupAmalgamation (G.leftRegion j)
      (G.rightRegion j) (G.seamTorus j torusBase) (G.seamTorus_mem_inter j torusBase) i) := by
  have hinter := G.leftRegion_inter_rightRegion j h
  intro i
  cases i with
  | false =>
    change Function.Surjective (FundamentalGroup.mapOfEq (interToLeft _ _)
      (rfl : interToLeft _ _ (G.seamTorusIn j _ hinter.ge torusBase) = _))
    rw [mapOfEq_rfl]
    exact surjective_fundamentalGroup_map_of_comp _ _ _ hl
  | true =>
    change Function.Surjective (FundamentalGroup.mapOfEq (interToRight _ _)
      (rfl : interToRight _ _ (G.seamTorusIn j _ hinter.ge torusBase) = _))
    rw [mapOfEq_rfl]
    exact surjective_fundamentalGroup_map_of_comp _ _ _ hr

theorem mul_comm_of_surjective_seamTorus [ConnectedSpace W.Carrier] (h : G.IsSeparating j)
    (hl : Function.Surjective (FundamentalGroup.map (G.seamTorusToLeft j) torusBase))
    (hr : Function.Surjective (FundamentalGroup.map (G.seamTorusToRight j) torusBase))
    (a b : FundamentalGroup W.Carrier (G.seamTorus j torusBase)) : a * b = b * a := by
  have hinter := G.leftRegion_inter_rightRegion j h
  have hbij := G.bijective_seamTorusIn j _ hinter torusBase
  have hH : ∀ x y : FundamentalGroup (↑(G.leftRegion j ∩ G.rightRegion j))
      (overlapBasepoint _ _ _ (G.seamTorus_mem_inter j torusBase)), x * y = y * x :=
    mul_comm_of_surjective_monoidHom _ hbij.2 torus_mul_comm
  let e := G.seamVanKampen j h torusBase
  obtain ⟨a, rfl⟩ := e.surjective a
  obtain ⟨b, rfl⟩ := e.surjective b
  rw [← map_mul, pushoutI_commutative_of_surjective hH (G.surjective_seamAmalgamation j h hl hr),
    map_mul]

theorem surjective_seamTorus_of_twoSolidTori (hext : G.externalCount = 0)
    (hc : G.pairing.count = 1) (PL : SolidTorusPiece G (G.leftPiece j))
    (PR : SolidTorusPiece G (G.rightPiece j)) :
    Function.Surjective (FundamentalGroup.map (G.seamTorusToLeft j) torusBase) ∧
      Function.Surjective (FundamentalGroup.map (G.seamTorusToRight j) torusBase) := by
  obtain ⟨⟨f, hf, hfc⟩, ⟨g, hg, hgc⟩⟩ :=
    G.regionEquivPiece j hext hc (G.leftPiece_ne_rightPiece j PL)
  refine ⟨surjective_fundamentalGroup_map_of_comp_eq _ f _ hfc torusBase (hf _).1 ?_,
    surjective_fundamentalGroup_map_of_comp_eq _ g _ hgc torusBase (hg _).1 ?_⟩
  · rw [G.leftPortTorus_eq j PL]
    exact PL.surjective_map_portMap torusBase
  · rw [G.rightPortTorus_eq j PR]
    exact surjective_fundamentalGroup_map_comp _ _ _
      (surjective_fundamentalGroup_map_homeomorph _ torusBase) (PR.surjective_map_portMap _)

theorem mul_comm_of_twoSolidTori [ConnectedSpace W.Carrier] (hext : G.externalCount = 0)
    (hc : G.pairing.count = 1) (PL : SolidTorusPiece G (G.leftPiece j))
    (PR : SolidTorusPiece G (G.rightPiece j))
    (a b : FundamentalGroup W.Carrier (G.seamTorus j torusBase)) : a * b = b * a :=
  G.mul_comm_of_surjective_seamTorus j
    (G.isSeparating_of_count_eq_one j hc (G.leftPiece_ne_rightPiece j PL))
    (G.surjective_seamTorus_of_twoSolidTori j hext hc PL PR).1
    (G.surjective_seamTorus_of_twoSolidTori j hext hc PL PR).2 a b

theorem isCyclic_of_twoSolidTori [ConnectedSpace W.Carrier] (hext : G.externalCount = 0)
    (hc : G.pairing.count = 1) (PL : SolidTorusPiece G (G.leftPiece j))
    (PR : SolidTorusPiece G (G.rightPiece j)) :
    IsCyclic (FundamentalGroup W.Carrier (G.seamTorus j torusBase)) := by
  have hLR := G.leftPiece_ne_rightPiece j PL
  have h := G.isSeparating_of_count_eq_one j hc hLR
  obtain ⟨hl, hr⟩ := G.surjective_seamTorus_of_twoSolidTori j hext hc PL PR
  obtain ⟨⟨f, hf, -⟩, -⟩ := G.regionEquivPiece j hext hc hLR
  let y : G.leftRegion j := ⟨G.seamTorus j torusBase, (G.seamTorus_mem_inter j torusBase).1⟩
  have : IsCyclic (FundamentalGroup (G.leftRegion j) y) := by
    have := PL.isCyclic_fundamentalGroup (f y)
    exact isCyclic_of_surjective (MulEquiv.ofBijective _ (hf y)).symm (MulEquiv.surjective _)
  exact isCyclic_of_surjective ((G.seamVanKampen j h torusBase).toMonoidHom.comp
    (Monoid.PushoutI.of false)) ((G.seamVanKampen j h torusBase).surjective.comp
      (pushoutI_of_surjective (G.surjective_seamAmalgamation j h hl hr) false))

end TorusPresentation

theorem isPrime_of_twoSolidTori {P : ConnectedClosedOrientedManifold.{u} 3}
    (G : TorusPresentation (NoCuts.carrier P)) (hc : G.pairing.count = 1)
    (S : ∀ i, SolidTorusPiece G i) : IsPrime P :=
  isPrime_of_commutative_fundamentalGroup P (G.seamTorus ⟨0, by omega⟩ torusBase)
    (G.mul_comm_of_twoSolidTori _ G.externalCount_eq_zero hc (S _) (S _))

theorem isCyclic_fundamentalGroup_of_twoSolidTori {P : ConnectedClosedOrientedManifold.{u} 3}
    (G : TorusPresentation (NoCuts.carrier P)) (hc : G.pairing.count = 1)
    (S : ∀ i, SolidTorusPiece G i) :
    IsCyclic (FundamentalGroup P.Carrier (G.seamTorus ⟨0, by omega⟩ torusBase)) :=
  G.isCyclic_of_twoSolidTori _ G.externalCount_eq_zero hc (S _) (S _)

theorem cliffordTorusPresentation_pairing_count :
    standardThreeSphereLiftRawGraphPresentation.{u}.toTorusPresentation.pairing.count = 1 :=
  rfl

theorem cliffordTorusPresentation_components_count :
    standardThreeSphereLiftRawGraphPresentation.{u}.toTorusPresentation.components.count = 2 :=
  rfl

theorem cliffordTorusPresentation_isSeparating :
    standardThreeSphereLiftRawGraphPresentation.{u}.toTorusPresentation.IsSeparating
      ⟨0, Nat.zero_lt_one⟩ :=
  TorusPresentation.isSeparating_of_count_eq_one _ _ rfl (by decide)

end GC.Seifert
