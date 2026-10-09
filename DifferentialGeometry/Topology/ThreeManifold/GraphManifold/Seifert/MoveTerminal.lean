import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MoveMerge
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.TwoFillingDetection

/-!
# The terminal move M4 of the (S⁺) normalization

Lane P2b: `moveTerminal : MoveTerminal` (`Seifert/Normalize.lean`), the partial assembly P2. A
move-free elementary presentation of a closed `Q` is grouped into Seifert blocks and `Q` is shown
to be a union of good blocks (`GoodBlockUnion`).

Transfers. A `PieceTransfer` moves a piece with its owned sides and collars to another
presentation; product pieces and `PieceBlock`s (a Seifert block on one piece with its ports) are
carried along it, a block through an orientation preserving map. The transfers used are the
restriction to a set of pieces (`restrictTransfer`) and the pieces off a contracted set
(`contractTransfer`, oriented through the fold maps by `preservesOrientation_of_comp`); the merged
piece of `contract` is the restricted carrier (`restrictContractDiffeomorph`).

Star groups. A `StarGroup T d` is a product piece over `P_{d.k}` (the centre, no self-seam) with
`d.fillingCount` solid tori on the left of seams into it, the meridians going to the filling
slopes of `d`. The restriction of `T` to the group is a `SeifertBlock` with data `d`
(`restrictBlock`), hence a `PieceBlock` of the contraction on its merged piece
(`contractBlock`); a group disjoint from the contracted set survives the contraction
(`StarGroup.transfer`, through `contractSeam`). A `Grouping T n` is `n` disjoint star groups whose
data are good for every block (`GoodData`) and good blocks on the other pieces. Contracting the
groups one at a time (`Grouping.nextGrouping`) ends in `BlockedPresentation.ofPieceBlocks`:
`Grouping.exists_isGood`.

Move-free presentations. Seams are flipped (`TorusPresentation.flipSeams`,
`ElementaryPresentation.flip`) so that every solid torus whose partner is not a solid torus lies
on the left (`solidFlip`); then each solid torus hangs on a pants at distance `≥ 2`. Every pants
with `m ≥ 1` such arms is a centre with `m` cones (`coneData`, cones from the host coordinates of
the meridians by `exists_cone_of_two_le_delta`); the other pieces are unfilled product blocks
over `P₂` or `P₃`. Goodness: one cone by K10c, two cones by K10e's `filledBlockGoodness`, three
cones and unfilled blocks directly (`seifertFactor_of_isMoveFree_of_normal`). A seam between two
solid tori makes them the whole of `Q` (`TorusPresentation.mem_of_not_isCrossing`), a single
block over `P₁` with no port and one filling when the distance is `≥ 1` on one side
(`seifertFactor_of_solidSeam`, after a flip in `seifertFactor_of_solidSeam_flip`).

Two configurations are local `sorry`s: two solid tori at distance `0` on both sides (the
three-sphere; a Dehn twist must re-trivialise one solid torus, `seifertFactor_of_solidSeam_zero`)
and a centre with a self-seam (`seifertFactor_of_centre_selfSeam`; `contract` glues every
internal seam, so the self-seam cannot remain a seam of the block presentation).
-/

set_option autoImplicit false

noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open GC.Topology (componentCarrier)
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert

section Orient

theorem orientation_map_trans_fin_three {A B C : Type*} [AddCommGroup A] [Module ℝ A]
    [AddCommGroup B] [Module ℝ B] [AddCommGroup C] [Module ℝ C]
    (e : A ≃ₗ[ℝ] B) (f : B ≃ₗ[ℝ] C) (o : Orientation ℝ A (Fin 3)) :
    Orientation.map (Fin 3) (e.trans f) o =
      Orientation.map (Fin 3) f (Orientation.map (Fin 3) e o) := by
  induction o using Module.Ray.ind with | h v hv => rfl

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M N : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold I' ∞ N]
  {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {X : Type*} [TopologicalSpace X] [ChartedSpace G X] [IsManifold J ∞ X]

theorem preservesOrientation_of_comp (f : M ≃ₘ⟮I, I'⟯ N) (FM : M → X) (FN : N → X)
    (hFN : ∀ y, MDifferentiableAt I' J FN y) (hcomp : ∀ x, FN (f x) = FM x)
    (oM : ManifoldOrientation I M 3) (oN : ManifoldOrientation I' N 3)
    (O : ManifoldOrientation J X 3)
    (hM : ∀ x, ∃ L : TangentSpace I x ≃ₗ[ℝ] TangentSpace J (FM x),
      (∀ v, L v = mfderiv I J FM x v) ∧
        Orientation.map (Fin 3) L (oM.orientation x) = O.orientation (FM x))
    (hN : ∀ y, ∃ L : TangentSpace I' y ≃ₗ[ℝ] TangentSpace J (FN y),
      (∀ v, L v = mfderiv I' J FN y v) ∧
        Orientation.map (Fin 3) L (oN.orientation y) = O.orientation (FN y)) :
    f.preservesOrientation oM oN := by
  intro x
  obtain ⟨LM, hLM, hoM⟩ := hM x
  obtain ⟨LN, hLN, hoN⟩ := hN (f x)
  let D := (f.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv
  have hFM : FM = FN ∘ f := funext fun x => (hcomp x).symm
  have key : ∀ v, LN (D v) = LM v := by
    intro v
    rw [hLM, hLN]
    have hc := mfderiv_comp x (hFN (f x)) (f.mdifferentiable (by simp) x)
    rw [← hFM] at hc
    rw [hc]
    rfl
  have hDL : D.trans LN = LM := LinearEquiv.ext key
  apply (Orientation.map (Fin 3) LN).injective
  have h1 := orientation_map_trans_fin_three D LN (oM.orientation x)
  have e3 : O.orientation (FN (f x)) = O.orientation (FM x) := by rw [hcomp x]
  exact h1.symm.trans ((congrArg (fun L => Orientation.map (Fin 3) L (oM.orientation x))
    hDL).trans (hoM.trans (e3.symm.trans hoN.symm)))

end Orient

section OrientedFold

variable {W C : CompactCarrier.{u}}

def IsOrientedFold (F : C.Carrier → W.Carrier) : Prop :=
  ∀ x, ∃ L : TangentSpace C.model x ≃ₗ[ℝ] TangentSpace W.model (F x),
    (∀ v, L v = mfderiv C.model W.model F x v) ∧
      Orientation.map (Fin 3) L (C.orientation.orientation x) = W.orientation.orientation (F x)

theorem IsOrientedFold.restrict {F : C.Carrier → W.Carrier} (hF : IsOrientedFold F)
    (hs : ContMDiff C.model W.model ∞ F) (U : TopologicalSpace.Opens C.Carrier) :
    ∀ x : U, ∃ L : TangentSpace C.model x ≃ₗ[ℝ] TangentSpace W.model (F x.val),
      (∀ v, L v = mfderiv C.model W.model (F ∘ Subtype.val) x v) ∧
        Orientation.map (Fin 3) L ((C.orientation.restrictOpen U).orientation x) =
          W.orientation.orientation (F x.val) := by
  intro x
  obtain ⟨L, hL, ho⟩ := hF x.val
  refine ⟨L, fun v => ?_, ho⟩
  rw [DifferentialGeometry.Topology.Manifold.mfderiv_restrict_open C.model W.model U F hs x]
  exact hL v

end OrientedFold

structure PieceTransfer {W W' : CompactCarrier.{u}} (T : TorusPresentation.{u} W)
    (i : Fin T.components.count) (T' : TorusPresentation.{u} W')
    (i' : Fin T'.components.count) where
  map : T.components.piece i ≃ₘ⟮T.cutCarrier.model, T'.cutCarrier.model⟯ T'.components.piece i'
  side : T.OwnedSide i ≃ T'.OwnedSide i'
  collar_eq : ∀ s p, p ∈ halfCollarSource →
    T'.pieceCollar i' (side s) p = map (T.pieceCollar i s p)

namespace ProductFibredPiece

variable {W W' : CompactCarrier.{u}} {T : TorusPresentation.{u} W}
  {i : Fin T.components.count} {T' : TorusPresentation.{u} W'} {i' : Fin T'.components.count}
  {k : ℕ}

def transfer (P : ProductFibredPiece T i k) (τ : PieceTransfer T i T' i') :
    ProductFibredPiece T' i' k where
  base := P.base
  port := P.port.trans τ.side
  trivialization := P.trivialization.trans τ.map
  collar_eq j p hp := by
    rw [Equiv.trans_apply, τ.collar_eq _ p hp, P.collar_eq j p hp]
    rfl

theorem transfer_port (P : ProductFibredPiece T i k) (τ : PieceTransfer T i T' i') (j : Fin k) :
    (P.transfer τ).port j = τ.side (P.port j) := rfl

end ProductFibredPiece

structure PieceBlock {W : CompactCarrier.{u}} (T : TorusPresentation.{u} W)
    (i : Fin T.components.count) where
  data : SeifertData
  block : SeifertBlock (componentCarrier T.cutCarrier T.components i) data
  port : Fin block.presentation.externalCount ≃ T.OwnedSide i
  collar_eq : ∀ r p, p ∈ halfCollarSource →
    block.presentation.external.collar r p = T.pieceCollar i (port r) p

namespace PieceBlock

variable {W W' : CompactCarrier.{u}} {T : TorusPresentation.{u} W}
  {i : Fin T.components.count} {T' : TorusPresentation.{u} W'} {i' : Fin T'.components.count}

def transfer (B : PieceBlock T i) (τ : PieceTransfer T i T' i')
    (hτ : τ.map.preservesOrientation (componentCarrier T.cutCarrier T.components i).orientation
      (componentCarrier T'.cutCarrier T'.components i').orientation) : PieceBlock T' i' where
  data := B.data
  block := B.block.transport τ.map hτ
  port := B.port.trans τ.side
  collar_eq r p hp := by
    change τ.map (B.block.presentation.external.collar r p) =
      T'.pieceCollar i' (τ.side (B.port r)) p
    rw [τ.collar_eq _ p hp, B.collar_eq r p hp]

theorem transfer_data (B : PieceBlock T i) (τ : PieceTransfer T i T' i')
    (hτ : τ.map.preservesOrientation (componentCarrier T.cutCarrier T.components i).orientation
      (componentCarrier T'.cutCarrier T'.components i').orientation) :
    (B.transfer τ hτ).data = B.data := rfl

end PieceBlock

def productData (k : ℕ) (hk1 : 1 ≤ k) (hk3 : k ≤ 3) : SeifertData where
  k := k
  ports := k
  cones := []
  normals := []
  one_le_k := hk1
  k_le_three := hk3
  two_le_of_mem_cones := by simp
  gcd_eq_one_of_mem_cones := by simp
  ports_add_length_add_length := rfl

def productPortEquiv (k : ℕ) (hk1 : 1 ≤ k) (hk3 : k ≤ 3) :
    Fin (productData k hk1 hk3).ports ⊕ Fin (productData k hk1 hk3).fillingCount ≃
      Fin (productData k hk1 hk3).k where
  toFun := Sum.elim id fun m => m.elim0
  invFun := Sum.inl
  left_inv o := by
    rcases o with r | m
    · rfl
    · exact m.elim0
  right_inv _ := rfl

def optionFinZeroEquiv : Option (Fin 0) ≃ Fin 1 where
  toFun _ := ⟨0, Nat.one_pos⟩
  invFun _ := none
  left_inv o := by
    rcases o with _ | m
    · rfl
    · exact m.elim0
  right_inv _ := Subsingleton.elim _ _

namespace ProductFibredPiece

variable {W : CompactCarrier.{u}} {T : TorusPresentation.{u} W} {i : Fin T.components.count}
  {k : ℕ}

def productBlock (P : ProductFibredPiece T i k) (hk1 : 1 ≤ k) (hk3 : k ≤ 3) :
    SeifertBlock (componentCarrier T.cutCarrier T.components i) (productData k hk1 hk3) where
  presentation := T.ofPiece i
  piece := optionFinZeroEquiv
  product := P.ofPiece
  solid m := m.elim0
  port := productPortEquiv k hk1 hk3
  seam := Equiv.refl _
  free := P.port.trans (Fintype.equivFin _)
  free_port _ := rfl
  filled_port m := m.elim0
  solid_port m := m.elim0
  slope m := m.elim0

def pieceBlock (P : ProductFibredPiece T i k) (hk1 : 1 ≤ k) (hk3 : k ≤ 3) : PieceBlock T i where
  data := productData k hk1 hk3
  block := P.productBlock hk1 hk3
  port := (Fintype.equivFin (T.OwnedSide i)).symm
  collar_eq _ _ _ := rfl

theorem pieceBlock_isGoodBlock (P : ProductFibredPiece T i k) (hk1 : 1 ≤ k) (hk2 : 2 ≤ k)
    (hk3 : k ≤ 3) : (P.pieceBlock hk1 hk3).block.IsGoodBlock :=
  SeifertBlock.isGoodBlock_of_fillingCount_eq_zero _ (by exact hk2) rfl

end ProductFibredPiece

namespace BlockedPresentation

variable {W : CompactCarrier.{u}}

def ofPieceBlocks (T : TorusPresentation.{u} W) (B : ∀ i, PieceBlock T i) :
    BlockedPresentation W where
  base := T
  data i := (B i).data
  block i := (B i).block
  port i := (B i).port
  collar_eq i := (B i).collar_eq

theorem isGood_ofPieceBlocks (T : TorusPresentation.{u} W) (B : ∀ i, PieceBlock T i)
    (h : ∀ i, (B i).block.IsGoodBlock) : (ofPieceBlocks T B).IsGood := h

end BlockedPresentation

namespace TorusPresentation

variable {W : CompactCarrier.{u}} (T : TorusPresentation.{u} W)

theorem isOrientedFold_cutMap : IsOrientedFold (W := W) (C := T.cutCarrier) T.cutMap :=
  T.quotient_oriented

variable (S : Finset (Fin T.components.count)) (hext : ∀ i, T.externalPiece i ∉ S)
  (hk : T.cutCarrier.kind = .withBoundary)
  (hconn : IsConnected (Set.range (T.restrictMap S) \ T.crossingSurface S))

theorem isOrientedFold_contractFold :
    IsOrientedFold (W := W) (C := T.contractCut S hext hk) (T.contractFold S hext hk) := by
  intro x
  exact ⟨(Manifold.differentialEquivOfBijective T.cutCarrier.model W.model
      (T.contractFold S hext hk) (T.mfderiv_contractFold_bijective S hext hk) x).toLinearEquiv,
    fun v => rfl, T.contractCut_orientation_map S hext hk x⟩

def contractTransfer {i : Fin T.components.count} (hi : i ∉ S) :
    PieceTransfer T i (T.contract S hext hk hconn) (T.contractIndex S hext hk hconn hi) where
  map := T.contractPieceDiffeomorph S hext hk hconn hi
  side := (T.contractOwnedSideEquiv S hext hk hconn hi).symm
  collar_eq s p hp := by
    apply Subtype.ext
    rw [TorusPresentation.pieceCollar_apply _ _ _ hp,
      T.contract_sideCollar_apply S hext hk hconn _ hp,
      T.contractLiftSide_contractOwnedSideEquiv_symm S hext hk hconn hi]
    have hmem : T.sideCollar s.val p ∈ T.subPiece Sᶜ :=
      T.piece_subset_subPiece Sᶜ (Finset.mem_compl.mpr hi)
        (T.sideCollar_target_subset_of_owned i s
          ((T.sideCollar s.val).map_source' ((T.sideCollar_source _).symm ▸ hp)))
    rw [T.contractMap_of_mem S hext hk hmem, T.contractPieceDiffeomorph_apply S hext hk hconn hi]
    congr 2
    rw [T.pieceCollar_apply i _ hp]

theorem contractTransfer_preservesOrientation {i : Fin T.components.count} (hi : i ∉ S) :
    (T.contractTransfer S hext hk hconn hi).map.preservesOrientation
      (componentCarrier T.cutCarrier T.components i).orientation
      (componentCarrier (T.contract S hext hk hconn).cutCarrier
        (T.contract S hext hk hconn).components (T.contractIndex S hext hk hconn hi)).orientation :=
  preservesOrientation_of_comp _ (T.cutMap ∘ Subtype.val)
    (T.contractFold S hext hk ∘ Subtype.val)
    (fun _ => ((T.contMDiff_contractFold S hext hk).comp contMDiff_subtype_val).mdifferentiableAt
      (by simp))
    (fun _ => rfl) _ _ W.orientation
    (T.isOrientedFold_cutMap.restrict T.quotient_smooth _)
    ((T.isOrientedFold_contractFold S hext hk).restrict (T.contMDiff_contractFold S hext hk) _)

section StarRegion

variable {m : ℕ} (c : Fin T.components.count) (f : Fin m → Fin T.pairing.count)

theorem seamCollar_subset_region_of_internal {k : Fin T.pairing.count}
    (hl : T.leftPiece k ∈ S) (hr : T.rightPiece k ∈ S) :
    T.seamCollar k ⊆ Set.range (T.restrictMap S) \ T.crossingSurface S := by
  intro y hy
  have hq : (T.seam k).symm y ∈ signedCollarSource := T.seam_source k ▸ (T.seam k).map_target' hy
  have hyq : T.seam k ((T.seam k).symm y) = y := (T.seam k).right_inv' hy
  refine ⟨?_, fun hc => ?_⟩
  · rw [← hyq]
    rcases le_total ((T.seam k).symm y).2 0 with h | h
    · exact T.seam_mem_range_of_nonpos _ k hl hq h
    · exact T.seam_mem_range_of_nonneg _ k hr hq h
  · obtain ⟨k', hk', hs⟩ := Set.mem_iUnion₂.mp hc
    have hkk : k' ≠ k := by
      rintro rfl
      rcases hk' with ⟨-, h⟩ | ⟨-, h⟩
      · exact h hr
      · exact h hl
    exact (T.seam_disjoint hkk).le_bot ⟨T.seamSurface_subset_seamCollar k' hs, hy⟩

def pieceImage' (i : Fin T.components.count) : Set W.Carrier :=
  T.cutMap '' (T.cutCarrier.pieceInterior (T.components.piece i) : Set T.cutCarrier.Carrier)

def starArm (l : Fin m) : Set W.Carrier :=
  T.pieceImage' c ∪ T.seamCollar (f l) ∪ T.pieceImage' (T.leftPiece (f l))

include hext in
theorem region_subset_star
    (hint : ∀ k, T.leftPiece k ∈ S → T.rightPiece k ∈ S → ∃ l, k = f l)
    (hmem : ∀ i ∈ S, i = c ∨ ∃ l, i = T.leftPiece (f l)) :
    Set.range (T.restrictMap S) \ T.crossingSurface S ⊆
      T.pieceImage' c ∪ ⋃ l, T.starArm c f l := by
  rintro y ⟨hy, hyc⟩
  rw [range_restrictMap] at hy
  obtain ⟨x, hxS, rfl⟩ := hy
  obtain ⟨i, hi, hxi⟩ := (T.mem_subPiece _).mp hxS
  by_cases hx : T.cutCarrier.model.IsInteriorPoint x
  · rcases hmem i hi with rfl | ⟨l, rfl⟩
    · exact Or.inl ⟨x, ⟨hxi, hx⟩, rfl⟩
    · exact Or.inr (Set.mem_iUnion.mpr ⟨l, Or.inr ⟨x, ⟨hxi, hx⟩, rfl⟩⟩)
  have hb : x ∈ T.cutCarrier.model.boundary T.cutCarrier.Carrier := by
    by_contra hb
    exact hx ((T.cutCarrier.model.isInteriorPoint_iff_not_isBoundaryPoint x).mpr hb)
  rw [T.cut_boundary_exhausted] at hb
  rcases hb with hb | hb
  · obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hb
    have hsk := T.cutMap_mem_seamSurface_block hk
    have hside : T.leftPiece k ∈ S ∨ T.rightPiece k ∈ S := by
      rcases hk with hk | hk
      · exact Or.inl (T.mem_of_mem_subPiece _ hxS (T.left_owned k hk))
      · exact Or.inr (T.mem_of_mem_subPiece _ hxS (T.right_owned k hk))
    by_cases hboth : T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S
    · obtain ⟨l, rfl⟩ := hint k hboth.1 hboth.2
      exact Or.inr (Set.mem_iUnion.mpr ⟨l, Or.inl (Or.inr
        (T.seamSurface_subset_seamCollar _ hsk))⟩)
    · refine (hyc (Set.mem_iUnion₂.mpr ⟨k, ?_, hsk⟩)).elim
      rcases hside with hl | hr
      · exact Or.inl ⟨hl, fun hr => hboth ⟨hl, hr⟩⟩
      · exact Or.inr ⟨hr, fun hl => hboth ⟨hl, hr⟩⟩
  · obtain ⟨e, t, ht⟩ : ∃ e t, T.cutExternal.torusMap e t = x := by
      obtain ⟨e, he⟩ := Set.mem_iUnion.mp hb
      obtain ⟨t, ht⟩ := he
      exact ⟨e, t, ht⟩
    exact (hext e (T.mem_of_mem_subPiece _ hxS (T.external_owned e ⟨t, ht⟩))).elim

theorem isConnected_pieceImage' (i : Fin T.components.count) : IsConnected (T.pieceImage' i) :=
  (isConnected_iff_connectedSpace.mpr (T.components.interior_connected i)).image _
    (T.reconstruction.continuous.comp T.pairing.quotientMap.continuous).continuousOn

theorem pieceImage'_inter_seamCollar (k : Fin T.pairing.count) (b : Bool) :
    (T.pieceImage' (T.sidePiece (T.pairSide k b)) ∩ T.seamCollar k).Nonempty := by
  have hp : ((1 : Torus), halfPoint (1 / 2) (by norm_num)) ∈ halfCollarSource := by
    change (1 / 2 : ℝ) < 1
    norm_num
  have hmem := (T.sideCollar (T.pairSide k b)).map_source' ((T.sideCollar_source _).symm ▸ hp)
  refine ⟨_, ⟨_, ⟨T.sideCollar_target_subset _ hmem,
    T.isInteriorPoint_sideCollar_pairSide k b hp (by change (0 : ℝ) < 1 / 2; norm_num)⟩,
    rfl⟩, ?_⟩
  have h := T.cutMap_mem_sideRegion (T.pairSide k b) hmem
  cases b <;> exact h

theorem isConnected_starArm (hfr : ∀ l, T.rightPiece (f l) = c) (l : Fin m) :
    IsConnected (T.starArm c f l) := by
  have hK : IsConnected (T.seamCollar (f l)) := (T.isPathConnected_seamCollar _).isConnected
  have h1 := T.pieceImage'_inter_seamCollar (f l) false
  have h2 := T.pieceImage'_inter_seamCollar (f l) true
  change (T.pieceImage' (T.rightPiece (f l)) ∩ _).Nonempty at h1
  change (T.pieceImage' (T.leftPiece (f l)) ∩ _).Nonempty at h2
  rw [hfr] at h1
  obtain ⟨y, hy1, hy2⟩ := h2
  exact ((T.isConnected_pieceImage' c).union h1 hK).union ⟨y, Or.inr hy2, hy1⟩
    (T.isConnected_pieceImage' _)

include hext in
theorem isConnected_region_star (hc : c ∈ S) (hfr : ∀ l, T.rightPiece (f l) = c)
    (hfl : ∀ l, T.leftPiece (f l) ∈ S)
    (hint : ∀ k, T.leftPiece k ∈ S → T.rightPiece k ∈ S → ∃ l, k = f l)
    (hmem : ∀ i ∈ S, i = c ∨ ∃ l, i = T.leftPiece (f l)) :
    IsConnected (Set.range (T.restrictMap S) \ T.crossingSurface S) := by
  have hsup : T.pieceImage' c ∪ ⋃ l, T.starArm c f l ⊆
      Set.range (T.restrictMap S) \ T.crossingSurface S := by
    refine Set.union_subset (T.cutMap_pieceInterior_subset_region S hc)
      (Set.iUnion_subset fun l => Set.union_subset (Set.union_subset
        (T.cutMap_pieceInterior_subset_region S hc) ?_)
        (T.cutMap_pieceInterior_subset_region S (hfl l)))
    exact T.seamCollar_subset_region_of_internal S (hfl l) ((hfr l).symm ▸ hc)
  rw [Set.Subset.antisymm (T.region_subset_star S hext c f hint hmem) hsup]
  have hne := (T.isConnected_pieceImage' c).nonempty
  obtain ⟨y, hy⟩ := hne
  have hU : T.pieceImage' c ∪ ⋃ l, T.starArm c f l =
      ⋃ o : Option (Fin m), Option.elim o (T.pieceImage' c) (T.starArm c f) := by
    ext z
    simp only [Set.mem_union, Set.mem_iUnion]
    constructor
    · rintro (hz | ⟨l, hz⟩)
      · exact ⟨none, hz⟩
      · exact ⟨some l, hz⟩
    · rintro ⟨o, hz⟩
      cases o with
      | none => exact Or.inl hz
      | some l => exact Or.inr ⟨l, hz⟩
  rw [hU]
  refine ⟨⟨y, Set.mem_iUnion.mpr ⟨none, hy⟩⟩, isPreconnected_iUnion ⟨y, ?_⟩ fun o => ?_⟩
  · refine Set.mem_iInter.mpr fun o => ?_
    cases o with
    | none => exact hy
    | some l => exact Or.inl (Or.inl hy)
  · cases o with
    | none => exact (T.isConnected_pieceImage' c).isPreconnected
    | some l => exact (T.isConnected_starArm c f hfr l).isPreconnected

end StarRegion

section RestrictTransfer

variable (hS : S.Nonempty)

def restrictLiftSide : (T.restrict S hS hext).Side → T.Side
  | .inl j => .inl (T.keptSeam S j).val
  | .inr (.inl j) => .inr (.inl (T.keptSeam S j).val)
  | .inr (.inr a) => (T.restrictSide S a).val

theorem restrictLiftSide_mem (s : (T.restrict S hS hext).Side) :
    T.sidePiece (T.restrictLiftSide S hext hS s) ∈ S := by
  rcases s with j | j | a
  · exact (T.keptSeam S j).property.1
  · exact (T.keptSeam S j).property.2
  · exact (T.restrictSide S a).property.1

theorem restrict_sidePiece (s : (T.restrict S hS hext).Side) :
    (T.restrict S hS hext).sidePiece s = T.subIndexOf S (T.restrictLiftSide_mem S hext hS s) := by
  rcases s with j | j | a <;> rfl

theorem restrictLiftSide_injective : Function.Injective (T.restrictLiftSide S hext hS) := by
  rintro (j | j | a) (j' | j' | a') h
  · have h' : (T.keptSeam S j).val = (T.keptSeam S j').val := Sum.inl_injective h
    exact congrArg Sum.inl ((Fintype.equivFin _).symm.injective (Subtype.ext h'))
  · exact absurd h (by simp [restrictLiftSide])
  · have ha := (T.restrictSide S a').property.2
    change Sum.inl (T.keptSeam S j).val = (T.restrictSide S a').val at h
    rw [← h] at ha
    exact (ha (T.keptSeam S j).property).elim
  · exact absurd h (by simp [restrictLiftSide])
  · have h' : (T.keptSeam S j).val = (T.keptSeam S j').val :=
      Sum.inl_injective (Sum.inr_injective h)
    exact congrArg (fun x => Sum.inr (Sum.inl x))
      ((Fintype.equivFin _).symm.injective (Subtype.ext h'))
  · have ha := (T.restrictSide S a').property.2
    change Sum.inr (Sum.inl (T.keptSeam S j).val) = (T.restrictSide S a').val at h
    rw [← h] at ha
    exact (ha (T.keptSeam S j).property).elim
  · have ha := (T.restrictSide S a).property.2
    change (T.restrictSide S a).val = Sum.inl (T.keptSeam S j').val at h
    rw [h] at ha
    exact (ha (T.keptSeam S j').property).elim
  · have ha := (T.restrictSide S a).property.2
    change (T.restrictSide S a).val = Sum.inr (Sum.inl (T.keptSeam S j').val) at h
    rw [h] at ha
    exact (ha (T.keptSeam S j').property).elim
  · have h' : T.restrictSide S a = T.restrictSide S a' := Subtype.ext h
    exact congrArg (fun x => Sum.inr (Sum.inr x)) ((Fintype.equivFin _).symm.injective h')

theorem exists_restrictLiftSide_eq (s : T.Side) (hs : T.sidePiece s ∈ S) :
    ∃ s', T.restrictLiftSide S hext hS s' = s := by
  by_cases hk : T.IsKeptSide S s
  · rcases s with k | k | e
    · refine ⟨.inl (Fintype.equivFin (T.KeptSeam S) ⟨k, hk⟩), ?_⟩
      change Sum.inl (T.keptSeam S (Fintype.equivFin _ ⟨k, hk⟩)).val = _
      rw [keptSeam_equivFin]
    · refine ⟨.inr (.inl (Fintype.equivFin (T.KeptSeam S) ⟨k, hk⟩)), ?_⟩
      change Sum.inr (Sum.inl (T.keptSeam S (Fintype.equivFin _ ⟨k, hk⟩)).val) = _
      rw [keptSeam_equivFin]
    · exact hk.elim
  · refine ⟨.inr (.inr (Fintype.equivFin (T.RestrictSide S) ⟨s, hs, hk⟩)), ?_⟩
    change (T.restrictSide S (Fintype.equivFin _ ⟨s, hs, hk⟩)).val = _
    rw [restrictSide_equivFin]

theorem restrict_sideCollar_val (s : (T.restrict S hS hext).Side)
    {p : Torus × EuclideanHalfSpace 1} (hp : p ∈ halfCollarSource) :
    ((T.restrict S hS hext).sideCollar s p).val =
      T.sideCollar (T.restrictLiftSide S hext hS s) p := by
  rcases s with j | j | a
  · exact T.subCollar_apply S (.inl (T.keptSeam S j).val) (T.keptSeam S j).property.1 hp
  · exact T.subCollar_apply S (.inr (.inl (T.keptSeam S j).val)) (T.keptSeam S j).property.2 hp
  · exact T.subCollar_apply S _ (T.restrictSide S a).property.1 hp

variable {i : Fin T.components.count} (hi : i ∈ S)

def restrictOwnedSideMap (s : (T.restrict S hS hext).OwnedSide (T.subIndexOf S hi)) :
    T.OwnedSide i :=
  ⟨T.restrictLiftSide S hext hS s.val, by
    have h := s.property
    rw [restrict_sidePiece] at h
    exact (T.subIndexOf_eq_iff _ hi).mp h⟩

theorem restrictOwnedSideMap_bijective :
    Function.Bijective (T.restrictOwnedSideMap S hext hS hi) := by
  refine ⟨fun a b h => Subtype.ext (T.restrictLiftSide_injective S hext hS
    (congrArg Subtype.val h)), fun s => ?_⟩
  have hsS : T.sidePiece s.val ∈ S := by rw [s.property]; exact hi
  obtain ⟨s', hs'⟩ := T.exists_restrictLiftSide_eq S hext hS s.val hsS
  refine ⟨⟨s', ?_⟩, Subtype.ext hs'⟩
  rw [restrict_sidePiece]
  refine (T.subIndexOf_eq_iff _ hi).mpr ?_
  rw [hs']
  exact s.property

def restrictOwnedSideEquiv :
    (T.restrict S hS hext).OwnedSide (T.subIndexOf S hi) ≃ T.OwnedSide i :=
  Equiv.ofBijective _ (T.restrictOwnedSideMap_bijective S hext hS hi)

theorem restrictLiftSide_restrictOwnedSideEquiv_symm (s : T.OwnedSide i) :
    T.restrictLiftSide S hext hS ((T.restrictOwnedSideEquiv S hext hS hi).symm s).val = s.val :=
  congrArg Subtype.val ((T.restrictOwnedSideEquiv S hext hS hi).apply_symm_apply s)

theorem mem_restrictPiece_iff (x : (T.subCarrier S).Carrier) :
    x ∈ (T.restrict S hS hext).components.piece (T.subIndexOf S hi) ↔
      x.val ∈ T.components.piece i := by
  change x.val ∈ T.components.piece (T.subIndex S (T.subIndexOf S hi)) ↔ _
  rw [subIndex_subIndexOf]

def restrictPieceDiffeomorph :
    T.components.piece i ≃ₘ⟮T.cutCarrier.model, (T.restrict S hS hext).cutCarrier.model⟯
      (T.restrict S hS hext).components.piece (T.subIndexOf S hi) where
  toFun x := ⟨⟨x.val, T.piece_subset_subPiece S hi x.property⟩,
    (T.mem_restrictPiece_iff S hext hS hi _).mpr x.property⟩
  invFun y := ⟨y.val.val, (T.mem_restrictPiece_iff S hext hS hi _).mp y.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  contMDiff_toFun := by
    refine (ContMDiff.subtypeVal_comp_iff _ _).mp ?_
    exact (ContMDiff.subtypeVal_comp_iff (I := T.cutCarrier.model) (I' := T.cutCarrier.model)
      (T.subPiece S) _).mp contMDiff_subtype_val
  contMDiff_invFun := by
    refine (ContMDiff.subtypeVal_comp_iff _ _).mp ?_
    exact (contMDiff_subtype_val (I := T.cutCarrier.model) (U := T.subPiece S)).comp
      (contMDiff_subtype_val (I := (T.restrict S hS hext).cutCarrier.model)
        (U := (T.restrict S hS hext).components.piece (T.subIndexOf S hi)))

theorem restrictPieceDiffeomorph_val (x : T.components.piece i) :
    (T.restrictPieceDiffeomorph S hext hS hi x).val.val = x.val := rfl

def restrictTransfer :
    PieceTransfer T i (T.restrict S hS hext) (T.subIndexOf S hi) where
  map := T.restrictPieceDiffeomorph S hext hS hi
  side := (T.restrictOwnedSideEquiv S hext hS hi).symm
  collar_eq s p hp := by
    apply Subtype.ext
    apply Subtype.ext
    rw [restrictPieceDiffeomorph_val, T.pieceCollar_apply i _ hp]
    have h1 := TorusPresentation.pieceCollar_apply (T.restrict S hS hext) (T.subIndexOf S hi)
      ((T.restrictOwnedSideEquiv S hext hS hi).symm s) hp
    rw [h1, restrict_sideCollar_val _ _ _ _ _ hp, restrictLiftSide_restrictOwnedSideEquiv_symm]

end RestrictTransfer

section LastPiece

theorem isOrientedFold_restrictCarrier_val :
    IsOrientedFold (W := W) (C := T.restrictCarrier S hext)
      (fun r : (T.restrictCarrier S hext).Carrier => r.val) := by
  intro x
  let C := T.restrictAtlas S hext
  exact ⟨(C.inclusionDifferentialEquiv x).toLinearEquiv, fun v => rfl,
    C.orientation_map_inclusion W.orientation x⟩

theorem mem_contractLast_iff (y : (T.contractCut S hext hk).Carrier) :
    y ∈ (T.contract S hext hk hconn).components.piece (T.contractLast S hext hk hconn) ↔
      y ∈ Set.range Sum.inr := by
  change y ∈ (T.contractPiece S hext hk (Fin.last _) : Set (T.ContractCut S hext hk)) ↔ _
  rw [contractPiece_last]

variable (r0 : (T.restrictCarrier S hext).Carrier)

def restrictContractDiffeomorph : (T.restrictCarrier S hext).Carrier ≃ₘ⟮
    (T.restrictCarrier S hext).model, (T.contract S hext hk hconn).cutCarrier.model⟯
    (T.contract S hext hk hconn).components.piece (T.contractLast S hext hk hconn) where
  toFun r := ⟨Sum.inr r, (T.mem_contractLast_iff S hext hk hconn _).mpr ⟨r, rfl⟩⟩
  invFun y := Sum.elim (fun _ => r0) (fun r => r) y.val
  left_inv _ := rfl
  right_inv := by
    rintro ⟨y, hy⟩
    obtain ⟨r, rfl⟩ := (T.mem_contractLast_iff S hext hk hconn _).mp hy
    rfl
  contMDiff_toFun := by
    refine (ContMDiff.subtypeVal_comp_iff _ _).mp ?_
    have h1 : ContMDiff (T.restrictCarrier S hext).model (T.contractRegion S hext hk).model ∞
        (fun r : (T.restrictCarrier S hext).Carrier =>
          @id (T.contractRegion S hext hk).Carrier r) :=
      (recast_contMDiff_iff_right (T.restrictCarrier S hext) T.cutCarrier.kind hk.symm
        (fun r : (T.restrictCarrier S hext).Carrier =>
          @id (T.contractRegion S hext hk).Carrier r)).mpr contMDiff_id
    exact (ContMDiff.inr (I := T.cutCarrier.model) (M := (T.subCarrier Sᶜ).Carrier)
      (M' := (T.contractRegion S hext hk).Carrier)).comp h1
  contMDiff_invFun := by
    have h1 : ContMDiff (T.contractRegion S hext hk).model (T.restrictCarrier S hext).model ∞
        (fun r : (T.contractRegion S hext hk).Carrier =>
          @id (T.restrictCarrier S hext).Carrier r) :=
      (recast_contMDiff_iff_left (T.restrictCarrier S hext) T.cutCarrier.kind hk.symm
        (fun r : (T.contractRegion S hext hk).Carrier =>
          @id (T.restrictCarrier S hext).Carrier r)).mpr contMDiff_id
    have h2 : ContMDiff T.cutCarrier.model (T.restrictCarrier S hext).model ∞
        (Sum.elim (fun _ : (T.subCarrier Sᶜ).Carrier => r0)
          (fun r : (T.contractRegion S hext hk).Carrier =>
            @id (T.restrictCarrier S hext).Carrier r)) :=
      ContMDiff.sumElim contMDiff_const h1
    exact h2.comp (contMDiff_subtype_val (I := (T.contract S hext hk hconn).cutCarrier.model)
      (U := (T.contract S hext hk hconn).components.piece (T.contractLast S hext hk hconn)))

theorem restrictContractDiffeomorph_val (r : (T.restrictCarrier S hext).Carrier) :
    (T.restrictContractDiffeomorph S hext hk hconn r0 r).val = Sum.inr r := rfl

theorem restrictContractDiffeomorph_preservesOrientation :
    (T.restrictContractDiffeomorph S hext hk hconn r0).preservesOrientation
      (T.restrictCarrier S hext).orientation
      (componentCarrier (T.contract S hext hk hconn).cutCarrier
        (T.contract S hext hk hconn).components (T.contractLast S hext hk hconn)).orientation :=
  preservesOrientation_of_comp _ (fun r : (T.restrictCarrier S hext).Carrier => r.val)
    (T.contractFold S hext hk ∘ Subtype.val)
    (fun _ => ((T.contMDiff_contractFold S hext hk).comp contMDiff_subtype_val).mdifferentiableAt
      (by simp))
    (fun _ => rfl) _ _ W.orientation (T.isOrientedFold_restrictCarrier_val S hext)
    ((T.isOrientedFold_contractFold S hext hk).restrict (T.contMDiff_contractFold S hext hk) _)

end LastPiece

section LastSides

theorem restrictOwnedSideEquiv_symm_val {i : Fin T.components.count} (hS : S.Nonempty)
    (hi : i ∈ S) (x : T.OwnedSide i) (s' : (T.restrict S hS hext).Side)
    (h : T.restrictLiftSide S hext hS s' = x.val) :
    ((T.restrictOwnedSideEquiv S hext hS hi).symm x).val = s' :=
  T.restrictLiftSide_injective S hext hS
    ((T.restrictLiftSide_restrictOwnedSideEquiv_symm S hext hS hi x).trans h.symm)

theorem not_isKeptSide_contractLiftSide (s : (T.contract S hext hk hconn).Side) :
    ¬ T.IsKeptSide S (T.contractLiftSide S hext hk hconn s) := by
  intro h
  rcases hs : T.contractLiftSide S hext hk hconn s with k | k | e
  · rw [hs] at h
    exact T.contractLiftSide_ne_pairSide S hext hk hconn h s true hs
  · rw [hs] at h
    exact T.contractLiftSide_ne_pairSide S hext hk hconn h s false hs
  · rw [hs] at h
    exact h

def contractLastSideMap
    (s : (T.contract S hext hk hconn).OwnedSide (T.contractLast S hext hk hconn)) :
    T.RestrictSide S :=
  ⟨T.contractLiftSide S hext hk hconn s.val,
    (T.contract_sidePiece_eq_last_iff S hext hk hconn s.val).mp s.property,
    T.not_isKeptSide_contractLiftSide S hext hk hconn s.val⟩

theorem contractLastSideMap_bijective :
    Function.Bijective (T.contractLastSideMap S hext hk hconn) := by
  refine ⟨fun a b h => Subtype.ext (T.contractLiftSide_injective S hext hk hconn
    (congrArg Subtype.val h)), fun a => ?_⟩
  have hs : ∀ k c, T.leftPiece k ∈ S → T.rightPiece k ∈ S → a.val ≠ T.pairSide k c := by
    intro k c hl hr he
    apply a.property.2
    rw [he]
    cases c
    · exact ⟨hl, hr⟩
    · exact ⟨hl, hr⟩
  obtain ⟨s', hs'⟩ := T.exists_contractLiftSide_eq S hext hk hconn a.val hs
  refine ⟨⟨s', (T.contract_sidePiece_eq_last_iff S hext hk hconn s').mpr
    (by rw [hs']; exact a.property.1)⟩, Subtype.ext hs'⟩

def contractLastSideEquiv :
    (T.contract S hext hk hconn).OwnedSide (T.contractLast S hext hk hconn) ≃ T.RestrictSide S :=
  Equiv.ofBijective _ (T.contractLastSideMap_bijective S hext hk hconn)

theorem contractLiftSide_contractLastSideEquiv_symm (a : T.RestrictSide S) :
    T.contractLiftSide S hext hk hconn ((T.contractLastSideEquiv S hext hk hconn).symm a).val =
      a.val :=
  congrArg Subtype.val ((T.contractLastSideEquiv S hext hk hconn).apply_symm_apply a)

end LastSides

end TorusPresentation

end GC.Seifert

namespace GC.Seifert

structure StarGroup {W : CompactCarrier.{u}} (T : TorusPresentation.{u} W) (d : SeifertData) where
  center : Fin T.components.count
  product : ProductFibredPiece T center d.k
  arm : Fin d.fillingCount → Fin T.pairing.count
  solid : ∀ l, SolidTorusPiece T (T.leftPiece (arm l))
  arm_right : ∀ l, T.rightPiece (arm l) = center
  arm_injective : Function.Injective arm
  no_self : ∀ k, T.leftPiece k = center → T.rightPiece k ≠ center
  slope : ∀ l, torusUnit (T.pairing.matching (arm l)) • meridianSlope =
    PrimitiveSlope.mk (d.fillingSlope l) (d.isPrimitive_fillingSlope l)

namespace StarGroup

variable {W : CompactCarrier.{u}} {T : TorusPresentation.{u} W} {d : SeifertData}
  (G : StarGroup T d)

def set : Finset (Fin T.components.count) :=
  insert G.center (Finset.univ.image fun l => T.leftPiece (G.arm l))

theorem center_mem : G.center ∈ G.set := Finset.mem_insert_self _ _

theorem solid_mem (l : Fin d.fillingCount) : T.leftPiece (G.arm l) ∈ G.set :=
  Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ l))

theorem mem_set {i : Fin T.components.count} (hi : i ∈ G.set) :
    i = G.center ∨ ∃ l, i = T.leftPiece (G.arm l) := by
  rcases Finset.mem_insert.mp hi with h | h
  · exact Or.inl h
  · obtain ⟨l, -, hl⟩ := Finset.mem_image.mp h
    exact Or.inr ⟨l, hl.symm⟩

theorem side_eq_of_solid (l : Fin d.fillingCount) (s : T.Side)
    (hs : T.sidePiece s = T.leftPiece (G.arm l)) : s = .inl (G.arm l) := by
  have hsub := (G.solid l).card_ownedSide
  have h1 : Subsingleton (T.OwnedSide (T.leftPiece (G.arm l))) :=
    Fintype.card_le_one_iff_subsingleton.mp hsub.le
  exact congrArg Subtype.val (Subsingleton.elim (⟨s, hs⟩ : T.OwnedSide _) ⟨.inl (G.arm l), rfl⟩)

theorem solid_ne_center (l : Fin d.fillingCount) : T.leftPiece (G.arm l) ≠ G.center :=
  fun h => G.no_self (G.arm l) h (G.arm_right l)

theorem leftPiece_arm_injective : Function.Injective fun l => T.leftPiece (G.arm l) := by
  intro l l' h
  have h1 := G.side_eq_of_solid l' (.inl (G.arm l)) h
  exact G.arm_injective (Sum.inl_injective h1)

theorem internal (k : Fin T.pairing.count) (hl : T.leftPiece k ∈ G.set)
    (hr : T.rightPiece k ∈ G.set) : ∃ l, k = G.arm l := by
  rcases G.mem_set hl with hl' | ⟨l, hl'⟩
  · rcases G.mem_set hr with hr' | ⟨l', hr'⟩
    · exact (G.no_self k hl' hr').elim
    · exact absurd (G.side_eq_of_solid l' (.inr (.inl k)) hr') (by simp)
  · exact ⟨l, Sum.inl_injective (G.side_eq_of_solid l (.inl k) hl')⟩

theorem set_nonempty : G.set.Nonempty := ⟨_, G.center_mem⟩

theorem isConnected_region (hext : ∀ i, T.externalPiece i ∉ G.set) :
    IsConnected (Set.range (T.restrictMap G.set) \ T.crossingSurface G.set) :=
  T.isConnected_region_star G.set hext G.center G.arm G.center_mem G.arm_right G.solid_mem
    G.internal fun _ hi => G.mem_set hi

def starIndex : Option (Fin d.fillingCount) → Fin G.set.card
  | none => T.subIndexOf G.set G.center_mem
  | some l => T.subIndexOf G.set (G.solid_mem l)

theorem starIndex_bijective : Function.Bijective G.starIndex := by
  constructor
  · rintro (_ | l) (_ | l') h <;> simp only [starIndex] at h
    · rfl
    · exact absurd ((T.subIndexOf_eq_iff _ _).mp h) (G.solid_ne_center l').symm
    · exact absurd ((T.subIndexOf_eq_iff _ _).mp h) (G.solid_ne_center l)
    · exact congrArg some (G.leftPiece_arm_injective ((T.subIndexOf_eq_iff _ _).mp h))
  · intro j
    rcases G.mem_set (T.subIndex_mem G.set j) with h | ⟨l, h⟩
    · refine ⟨none, ?_⟩
      change T.subIndexOf G.set G.center_mem = j
      rw [← T.subIndexOf_subIndex G.set j]
      exact (T.subIndexOf_eq_iff _ _).mpr h.symm
    · refine ⟨some l, ?_⟩
      change T.subIndexOf G.set (G.solid_mem l) = j
      rw [← T.subIndexOf_subIndex G.set j]
      exact (T.subIndexOf_eq_iff _ _).mpr h.symm

def keptArm (l : Fin d.fillingCount) : T.KeptSeam G.set :=
  ⟨G.arm l, G.solid_mem l, (G.arm_right l).symm ▸ G.center_mem⟩

theorem keptArm_bijective : Function.Bijective G.keptArm := by
  refine ⟨fun l l' h => G.arm_injective (congrArg Subtype.val h), fun k => ?_⟩
  obtain ⟨l, hl⟩ := G.internal k.val k.property.1 k.property.2
  exact ⟨l, Subtype.ext hl.symm⟩

def armSeam : Fin d.fillingCount ≃ Fin (Fintype.card (T.KeptSeam G.set)) :=
  (Equiv.ofBijective _ G.keptArm_bijective).trans (Fintype.equivFin _)

theorem keptSeam_armSeam (l : Fin d.fillingCount) :
    (T.keptSeam G.set (G.armSeam l)).val = G.arm l := by
  change (T.keptSeam G.set (Fintype.equivFin _ (G.keptArm l))).val = _
  rw [TorusPresentation.keptSeam_equivFin]
  rfl

theorem restrictSide_owned (a : T.RestrictSide G.set) : T.sidePiece a.val = G.center := by
  rcases G.mem_set a.property.1 with h | ⟨l, h⟩
  · exact h
  · have he := G.side_eq_of_solid l a.val h
    exact (a.property.2 (by
      rw [he]
      exact ⟨G.solid_mem l, (G.arm_right l).symm ▸ G.center_mem⟩)).elim

def centerSideMap : Fin d.fillingCount ⊕ T.RestrictSide G.set → T.OwnedSide G.center
  | .inl l => ⟨.inr (.inl (G.arm l)), G.arm_right l⟩
  | .inr a => ⟨a.val, G.restrictSide_owned a⟩

theorem centerSideMap_bijective : Function.Bijective G.centerSideMap := by
  constructor
  · rintro (l | a) (l' | a') h <;> have h' := congrArg Subtype.val h <;>
      simp only [centerSideMap] at h'
    · exact congrArg Sum.inl (G.arm_injective (Sum.inl_injective (Sum.inr_injective h')))
    · have hk : T.IsKeptSide G.set a'.val := by
        rw [← h']
        exact ⟨G.solid_mem l, (G.arm_right l).symm ▸ G.center_mem⟩
      exact (a'.property.2 hk).elim
    · have hk : T.IsKeptSide G.set a.val := by
        rw [h']
        exact ⟨G.solid_mem l', (G.arm_right l').symm ▸ G.center_mem⟩
      exact (a.property.2 hk).elim
    · exact congrArg Sum.inr (Subtype.ext h')
  · rintro ⟨s, hs⟩
    by_cases hk : T.IsKeptSide G.set s
    · rcases s with k | k | e
      · obtain ⟨l, rfl⟩ := G.internal k hk.1 hk.2
        exact absurd hs (G.solid_ne_center l)
      · obtain ⟨l, rfl⟩ := G.internal k hk.1 hk.2
        exact ⟨.inl l, rfl⟩
      · exact hk.elim
    · exact ⟨.inr ⟨s, hs ▸ G.center_mem, hk⟩, rfl⟩

def centerSideEquiv : Fin d.fillingCount ⊕ T.RestrictSide G.set ≃ T.OwnedSide G.center :=
  Equiv.ofBijective _ G.centerSideMap_bijective

theorem card_restrictSide : Fintype.card (T.RestrictSide G.set) = d.ports := by
  have h := Fintype.card_congr G.centerSideEquiv
  rw [Fintype.card_sum, Fintype.card_fin, G.product.card_ownedSide] at h
  have h2 := d.ports_add_fillingCount
  omega

def extSide : Fin d.ports ≃ T.RestrictSide G.set :=
  (finCongr G.card_restrictSide.symm).trans (Fintype.equivFin _).symm

def portEquiv : Fin d.ports ⊕ Fin d.fillingCount ≃ Fin d.k :=
  (Equiv.sumComm _ _).trans ((Equiv.sumCongr (Equiv.refl _) G.extSide).trans
    (G.centerSideEquiv.trans G.product.port.symm))

variable (hext : ∀ i, T.externalPiece i ∉ G.set)

def restrictBlock : SeifertBlock (T.restrictCarrier G.set hext) d where
  presentation := T.restrict G.set G.set_nonempty hext
  piece := Equiv.ofBijective G.starIndex G.starIndex_bijective
  product := G.product.transfer (T.restrictTransfer G.set hext G.set_nonempty G.center_mem)
  solid l := (G.solid l).transfer (T.restrictTransfer G.set hext G.set_nonempty (G.solid_mem l))
  port := G.portEquiv
  seam := G.armSeam
  free := finCongr G.card_restrictSide.symm
  free_port r := by
    change ((T.restrictOwnedSideEquiv G.set hext G.set_nonempty G.center_mem).symm
      (G.product.port (G.product.port.symm (G.centerSideMap (.inr (G.extSide r)))))).val = _
    rw [Equiv.apply_symm_apply]
    refine T.restrictOwnedSideEquiv_symm_val G.set hext G.set_nonempty G.center_mem _ _ ?_
    rfl
  filled_port l := by
    change ((T.restrictOwnedSideEquiv G.set hext G.set_nonempty G.center_mem).symm
      (G.product.port (G.product.port.symm (G.centerSideMap (.inl l))))).val = _
    rw [Equiv.apply_symm_apply]
    refine T.restrictOwnedSideEquiv_symm_val G.set hext G.set_nonempty G.center_mem _ _ ?_
    change Sum.inr (Sum.inl (T.keptSeam G.set (G.armSeam l)).val) = _
    rw [G.keptSeam_armSeam]
    rfl
  solid_port l := by
    change ((T.restrictOwnedSideEquiv G.set hext G.set_nonempty (G.solid_mem l)).symm
      ((G.solid l).port 0)).val = _
    refine T.restrictOwnedSideEquiv_symm_val G.set hext G.set_nonempty (G.solid_mem l) _ _ ?_
    change Sum.inl (T.keptSeam G.set (G.armSeam l)).val = _
    rw [G.keptSeam_armSeam, G.side_eq_of_solid l _ ((G.solid l).port 0).property]
  slope l := by
    change torusUnit (T.pairing.matching (T.keptSeam G.set (G.armSeam l)).val) • meridianSlope = _
    rw [G.keptSeam_armSeam]
    exact G.slope l

end StarGroup

end GC.Seifert

namespace GC.Seifert

section FlipGluing

variable {X : Type*} [TopologicalSpace X] {n : ℕ} (G : BoundaryGluing X (Fin n))
  (σ : Fin n → Bool)

def flipGluing : BoundaryGluing X (Fin n) where
  left k := if σ k then G.right k else G.left k
  right k := if σ k then G.left k else G.right k
  attaching k := if h : σ k then
      (Homeomorph.setCongr (ite_eq_left h)).trans ((G.attaching k).symm.trans
        (Homeomorph.setCongr (ite_eq_left h).symm))
    else (Homeomorph.setCongr (ite_eq_right h)).trans ((G.attaching k).trans
        (Homeomorph.setCongr (ite_eq_right h).symm))
  isClosed_left k := by
    split_ifs
    exacts [G.isClosed_right k, G.isClosed_left k]
  isClosed_right k := by
    split_ifs
    exacts [G.isClosed_left k, G.isClosed_right k]
  disjoint_left_right k := by
    split_ifs
    exacts [(G.disjoint_left_right k).symm, G.disjoint_left_right k]
  disjoint_blocks i j hij := by
    have hb : ∀ k, (if σ k then G.right k else G.left k) ∪
        (if σ k then G.left k else G.right k) = G.left k ∪ G.right k := fun k => by
      split_ifs
      exacts [Set.union_comm _ _, rfl]
    rw [hb, hb]
    exact G.disjoint_blocks i j hij

theorem flipGluing_block (k : Fin n) : (flipGluing G σ).block k = G.block k := by
  change (if σ k then G.right k else G.left k) ∪ (if σ k then G.left k else G.right k) = _
  split_ifs
  exacts [Set.union_comm _ _, rfl]

variable {G σ}

theorem flipGluing_left_true {k : Fin n} (h : σ k = true) :
    (flipGluing G σ).left k = G.right k := ite_eq_left h

theorem flipGluing_right_true {k : Fin n} (h : σ k = true) :
    (flipGluing G σ).right k = G.left k := ite_eq_left h

theorem flipGluing_left_false {k : Fin n} (h : ¬ σ k = true) :
    (flipGluing G σ).left k = G.left k := ite_eq_right h

theorem flipGluing_right_false {k : Fin n} (h : ¬ σ k = true) :
    (flipGluing G σ).right k = G.right k := ite_eq_right h

theorem flipGluing_attaching_eq_true {k : Fin n} (h : σ k = true) :
    (flipGluing G σ).attaching k = (Homeomorph.setCongr (flipGluing_left_true (G := G) h)).trans
      ((G.attaching k).symm.trans (Homeomorph.setCongr (flipGluing_right_true (G := G) h).symm)) :=
  dite_eq_left h

theorem flipGluing_attaching_eq_false {k : Fin n} (h : ¬ σ k = true) :
    (flipGluing G σ).attaching k = (Homeomorph.setCongr (flipGluing_left_false (G := G) h)).trans
      ((G.attaching k).trans (Homeomorph.setCongr (flipGluing_right_false (G := G) h).symm)) :=
  dite_eq_right h

theorem flipGluing_attaching_true {k : Fin n} (h : σ k = true)
    (x : (flipGluing G σ).left k) :
    ((flipGluing G σ).attaching k x : X) =
      ((G.attaching k).symm ⟨x.val, flipGluing_left_true (G := G) h ▸ x.property⟩ : X) := by
  rw [flipGluing_attaching_eq_true h]
  rfl

theorem flipGluing_attaching_false {k : Fin n} (h : ¬ σ k = true)
    (x : (flipGluing G σ).left k) :
    ((flipGluing G σ).attaching k x : X) =
      (G.attaching k ⟨x.val, flipGluing_left_false (G := G) h ▸ x.property⟩ : X) := by
  rw [flipGluing_attaching_eq_false h]
  rfl

theorem flipGluing_attaching_symm_true {k : Fin n} (h : σ k = true)
    (y : (flipGluing G σ).right k) :
    (((flipGluing G σ).attaching k).symm y : X) =
      (G.attaching k ⟨y.val, flipGluing_right_true (G := G) h ▸ y.property⟩ : X) := by
  rw [flipGluing_attaching_eq_true h]
  rfl

theorem flipGluing_attaching_symm_false {k : Fin n} (h : ¬ σ k = true)
    (y : (flipGluing G σ).right k) :
    (((flipGluing G σ).attaching k).symm y : X) =
      ((G.attaching k).symm ⟨y.val, flipGluing_right_false (G := G) h ▸ y.property⟩ : X) := by
  rw [flipGluing_attaching_eq_false h]
  rfl

theorem flipGluing_attaching_true' {k : Fin n} (h : σ k = true)
    (x : (flipGluing G σ).left k) (y : G.right k) (hxy : (x : X) = y) :
    ((flipGluing G σ).attaching k x : X) = ((G.attaching k).symm y : X) := by
  rw [flipGluing_attaching_true h]
  congr 2
  exact Subtype.ext hxy

theorem flipGluing_attaching_false' {k : Fin n} (h : ¬ σ k = true)
    (x : (flipGluing G σ).left k) (y : G.left k) (hxy : (x : X) = y) :
    ((flipGluing G σ).attaching k x : X) = (G.attaching k y : X) := by
  rw [flipGluing_attaching_false h]
  congr 2
  exact Subtype.ext hxy

theorem flipGluing_flip (k : Fin n) (x : X) : (flipGluing G σ).flip k x = G.flip k x := by
  by_cases h : σ k = true
  · by_cases hl : x ∈ G.left k
    · have hx : x ∈ (flipGluing G σ).right k := (flipGluing_right_true (G := G) h).symm ▸ hl
      rw [BoundaryGluing.flip_of_mem_right _ hx, G.flip_of_mem_left hl,
        flipGluing_attaching_symm_true h]
    · by_cases hr : x ∈ G.right k
      · have hx : x ∈ (flipGluing G σ).left k := (flipGluing_left_true (G := G) h).symm ▸ hr
        rw [BoundaryGluing.flip_of_mem_left _ hx, G.flip_of_mem_right hr,
          flipGluing_attaching_true h]
      · have hx : x ∉ (flipGluing G σ).block k := by
          rw [flipGluing_block]
          exact fun hb => hb.elim hl hr
        rw [BoundaryGluing.flip_of_notMem _ hx, G.flip_of_notMem fun hb => hb.elim hl hr]
  · by_cases hl : x ∈ G.left k
    · have hx : x ∈ (flipGluing G σ).left k := (flipGluing_left_false (G := G) h).symm ▸ hl
      rw [BoundaryGluing.flip_of_mem_left _ hx, G.flip_of_mem_left hl,
        flipGluing_attaching_false h]
    · by_cases hr : x ∈ G.right k
      · have hx : x ∈ (flipGluing G σ).right k := (flipGluing_right_false (G := G) h).symm ▸ hr
        rw [BoundaryGluing.flip_of_mem_right _ hx, G.flip_of_mem_right hr,
          flipGluing_attaching_symm_false h]
      · have hx : x ∉ (flipGluing G σ).block k := by
          rw [flipGluing_block]
          exact fun hb => hb.elim hl hr
        rw [BoundaryGluing.flip_of_notMem _ hx, G.flip_of_notMem fun hb => hb.elim hl hr]

theorem flipGluing_rel (x y : X) : (flipGluing G σ).rel x y ↔ G.rel x y := by
  unfold BoundaryGluing.rel
  simp only [flipGluing_block, flipGluing_flip]

end FlipGluing

section Swap

theorem reversesBoundaryOrientation_swap {C : CompactCarrier.{u}}
    (l r : PartialDiffeomorph halfCollarModel C.model (Torus × EuclideanHalfSpace 1) C.Carrier ∞)
    (hl : l.source = halfCollarSource) (hr : r.source = halfCollarSource)
    (φ : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus)
    (h : ReversesBoundaryOrientation C l (fun p => r (φ p.1, p.2))) :
    ReversesBoundaryOrientation C r (fun p => l (φ.symm p.1, p.2)) := by
  intro t
  obtain ⟨L, R, hL, hR, ho⟩ := h (φ.symm t)
  let Φ : (Torus × EuclideanHalfSpace 1) ≃ₘ⟮halfCollarModel, halfCollarModel⟯
      (Torus × EuclideanHalfSpace 1) :=
    φ.prodCongr (Diffeomorph.refl (𝓡∂ 1) (EuclideanHalfSpace 1) ∞)
  let Ψ : (Torus × EuclideanHalfSpace 1) ≃ₘ⟮halfCollarModel, halfCollarModel⟯
      (Torus × EuclideanHalfSpace 1) :=
    φ.symm.prodCongr (Diffeomorph.refl (𝓡∂ 1) (EuclideanHalfSpace 1) ∞)
  have hΦ : Φ (φ.symm t, halfZero) = (t, halfZero) := Prod.ext (φ.apply_symm_apply t) rfl
  have hΨ : Ψ (t, halfZero) = (φ.symm t, halfZero) := rfl
  have hrd : MDifferentiableAt halfCollarModel C.model r (t, halfZero) :=
    r.mdifferentiableAt (by simp) (by rw [hr]; exact zero_mem_halfCollarSource t)
  have hld : MDifferentiableAt halfCollarModel C.model l (φ.symm t, halfZero) :=
    l.mdifferentiableAt (by simp) (by rw [hl]; exact zero_mem_halfCollarSource _)
  let A := (Φ.mfderivToContinuousLinearEquiv (by simp) (φ.symm t, halfZero)).toLinearEquiv
  let B := (Ψ.mfderivToContinuousLinearEquiv (by simp) (t, halfZero)).toLinearEquiv
  have hAB : ∀ v, A (B v) = v := by
    intro v
    have hc := mfderiv_comp (I := halfCollarModel) (I' := halfCollarModel)
      (I'' := halfCollarModel) (t, halfZero) (Φ.mdifferentiable (by simp) (Ψ (t, halfZero)))
      (Ψ.mdifferentiable (by simp) (t, halfZero))
    have hid : (Φ ∘ Ψ) = id := funext fun p => Prod.ext (φ.apply_symm_apply p.1) rfl
    rw [hid, mfderiv_id] at hc
    exact (congrArg (fun F => F v) hc).symm
  have hRv : ∀ w, R w = mfderiv halfCollarModel C.model r (t, halfZero) (A w) := by
    intro w
    rw [hR w]
    have hc := mfderiv_comp (I := halfCollarModel) (I' := halfCollarModel) (I'' := C.model)
      (φ.symm t, halfZero) (hΦ ▸ hrd) (Φ.mdifferentiable (by simp) (φ.symm t, halfZero))
    have he : (fun p : Torus × EuclideanHalfSpace 1 => r (φ p.1, p.2)) = r ∘ Φ := rfl
    rw [he, hc]
    change mfderiv halfCollarModel C.model r (Φ (φ.symm t, halfZero))
        (mfderiv halfCollarModel halfCollarModel Φ (φ.symm t, halfZero) w) = _
    rw [hΦ]
    rfl
  have hR'v : ∀ v, L (B v) = mfderiv halfCollarModel C.model
      (fun p : Torus × EuclideanHalfSpace 1 => l (φ.symm p.1, p.2)) (t, halfZero) v := by
    intro v
    have hc := mfderiv_comp (I := halfCollarModel) (I' := halfCollarModel) (I'' := C.model)
      (t, halfZero) hld (Ψ.mdifferentiable (by simp) (t, halfZero))
    have he : (fun p : Torus × EuclideanHalfSpace 1 => l (φ.symm p.1, p.2)) = l ∘ Ψ := rfl
    rw [he, hc]
    exact hL (B v)
  refine ⟨A.symm.trans R, B.trans L, fun v => ?_, fun v => hR'v v, ?_⟩
  · change R (A.symm v) = _
    rw [hRv]
    exact congrArg _ (A.apply_symm_apply v)
  · have hBA : ∀ v, B.symm v = A v := fun v => by
      have e := hAB (B.symm v)
      rw [LinearEquiv.apply_symm_apply] at e
      exact e.symm
    have e1 : (A.symm.trans R).symm = R.symm.trans A := LinearEquiv.ext fun _ => rfl
    have e2 : (B.trans L).symm = L.symm.trans A := LinearEquiv.ext fun v => hBA (L.symm v)
    have hp : r (φ (φ.symm t), halfZero) = r (t, halfZero) := by rw [φ.apply_symm_apply]
    have ho' := ho
    beta_reduce at ho'
    rw [hp] at ho'
    have k1 : Orientation.map (Fin 3) R.symm (C.orientation.orientation (r (t, halfZero))) =
        -Orientation.map (Fin 3) L.symm (C.orientation.orientation (l (φ.symm t, halfZero))) :=
      ((neg_neg _).symm.trans (congrArg Neg.neg ho').symm)
    have s1 := (congrArg (fun e => Orientation.map (Fin 3) e
      (C.orientation.orientation (r (t, halfZero)))) e1).trans
      (orientation_map_trans_fin_three R.symm A (C.orientation.orientation (r (t, halfZero))))
    have s3 := (congrArg (fun e => Orientation.map (Fin 3) e
      (C.orientation.orientation (l (φ.symm t, halfZero)))) e2).trans
      (orientation_map_trans_fin_three L.symm A
        (C.orientation.orientation (l (φ.symm t, halfZero))))
    exact s1.trans ((congrArg (Orientation.map (Fin 3) A) k1).trans
      ((Orientation.map_neg _ _).trans (congrArg Neg.neg s3.symm)))

end Swap

section FlipPairing

variable {C : CompactCarrier.{u}} (P : TorusPairing C) (σ : Fin P.count → Bool)

def flipPairing : TorusPairing C where
  count := P.count
  gluing := flipGluing P.gluing σ
  leftParam k := if h : σ k then
      (P.rightParam k).trans (Homeomorph.setCongr (flipGluing_left_true (G := P.gluing) h).symm)
    else (P.leftParam k).trans
      (Homeomorph.setCongr (flipGluing_left_false (G := P.gluing) h).symm)
  rightParam k := if h : σ k then
      (P.leftParam k).trans (Homeomorph.setCongr (flipGluing_right_true (G := P.gluing) h).symm)
    else (P.rightParam k).trans
      (Homeomorph.setCongr (flipGluing_right_false (G := P.gluing) h).symm)
  matching k := if σ k then (P.matching k).symm else P.matching k
  matching_eq k t := by
    apply Subtype.ext
    by_cases h : σ k = true
    · rw [flipGluing_attaching_true' h _ (P.rightParam k t) (by rw [dite_eq_left h]; rfl)]
      have e2 : P.rightParam k t = P.gluing.attaching k (P.leftParam k ((P.matching k).symm t)) :=
        by rw [P.matching_eq, Diffeomorph.apply_symm_apply]
      rw [e2, Homeomorph.symm_apply_apply, dite_eq_left h, ite_eq_left h]
      rfl
    · rw [flipGluing_attaching_false' h _ (P.leftParam k t) (by rw [dite_eq_right h]; rfl),
        P.matching_eq, dite_eq_right h, ite_eq_right h]
      rfl
  leftCollar k := if σ k then P.rightCollar k else P.leftCollar k
  rightCollar k := if σ k then P.leftCollar k else P.rightCollar k
  left_source k := by
    split_ifs
    exacts [P.right_source k, P.left_source k]
  right_source k := by
    split_ifs
    exacts [P.left_source k, P.right_source k]
  left_zero k t := by
    by_cases h : σ k = true
    · rw [ite_eq_left h, dite_eq_left h]
      exact P.right_zero k t
    · rw [ite_eq_right h, dite_eq_right h]
      exact P.left_zero k t
  right_zero k t := by
    by_cases h : σ k = true
    · rw [ite_eq_left h, dite_eq_left h]
      exact P.left_zero k t
    · rw [ite_eq_right h, dite_eq_right h]
      exact P.right_zero k t
  reversing k := by
    by_cases h : σ k = true
    · rw [ite_eq_left h, ite_eq_left h, ite_eq_left h]
      exact reversesBoundaryOrientation_swap _ _ (P.left_source k) (P.right_source k) _
        (P.reversing k)
    · rw [ite_eq_right h, ite_eq_right h, ite_eq_right h]
      exact P.reversing k

variable {P σ}

theorem flipPairing_leftParam_true {k : Fin P.count} (h : σ k = true) :
    (flipPairing P σ).leftParam k = (P.rightParam k).trans
      (Homeomorph.setCongr (flipGluing_left_true (G := P.gluing) h).symm) :=
  dite_eq_left h

theorem flipPairing_leftParam_false {k : Fin P.count} (h : ¬ σ k = true) :
    (flipPairing P σ).leftParam k = (P.leftParam k).trans
      (Homeomorph.setCongr (flipGluing_left_false (G := P.gluing) h).symm) :=
  dite_eq_right h

theorem flipPairing_leftParam_val (k : Fin P.count) (t : Torus) :
    ((flipPairing P σ).leftParam k t : C.Carrier) =
      if σ k then (P.rightParam k t : C.Carrier) else (P.leftParam k t : C.Carrier) := by
  by_cases h : σ k = true
  · rw [ite_eq_left h, flipPairing_leftParam_true h]
    rfl
  · rw [ite_eq_right h, flipPairing_leftParam_false h]
    rfl

theorem flipPairing_matching (k : Fin P.count) :
    (flipPairing P σ).matching k = if σ k then (P.matching k).symm else P.matching k := rfl

theorem flipPairing_leftCollar (k : Fin P.count) :
    (flipPairing P σ).leftCollar k = if σ k then P.rightCollar k else P.leftCollar k := rfl

theorem flipPairing_rightCollar (k : Fin P.count) :
    (flipPairing P σ).rightCollar k = if σ k then P.leftCollar k else P.rightCollar k := rfl

end FlipPairing

def negDiffeomorph : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓘(ℝ, ℝ)⟯ ℝ where
  toFun x := -x
  invFun x := -x
  left_inv x := neg_neg x
  right_inv x := neg_neg x
  contMDiff_toFun := contDiff_neg.contMDiff
  contMDiff_invFun := contDiff_neg.contMDiff

def seamFlipDiffeomorph (φ : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus) :
    (Torus × ℝ) ≃ₘ⟮signedCollarModel, signedCollarModel⟯ (Torus × ℝ) :=
  φ.symm.prodCongr negDiffeomorph

theorem seamFlipDiffeomorph_apply (φ : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus)
    (p : Torus × ℝ) : seamFlipDiffeomorph φ p = (φ.symm p.1, -p.2) := rfl

def seamFlipChart (φ : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus) {W : CompactCarrier.{u}}
    (c : PartialDiffeomorph signedCollarModel W.model (Torus × ℝ) W.Carrier ∞) :
    PartialDiffeomorph signedCollarModel W.model (Torus × ℝ) W.Carrier ∞ :=
  (seamFlipDiffeomorph φ).toPartialDiffeomorph.trans c

theorem seamFlipChart_apply (φ : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus) {W : CompactCarrier.{u}}
    (c : PartialDiffeomorph signedCollarModel W.model (Torus × ℝ) W.Carrier ∞)
    (p : Torus × ℝ) : seamFlipChart φ c p = c (φ.symm p.1, -p.2) := rfl

theorem seamFlipChart_source (φ : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus)
    {W : CompactCarrier.{u}}
    (c : PartialDiffeomorph signedCollarModel W.model (Torus × ℝ) W.Carrier ∞)
    (hc : c.source = signedCollarSource) : (seamFlipChart φ c).source = signedCollarSource := by
  ext p
  change p ∈ Set.univ ∩ seamFlipDiffeomorph φ ⁻¹' c.source ↔ _
  rw [hc]
  simp only [Set.mem_inter_iff, Set.mem_univ, true_and, Set.mem_preimage,
    seamFlipDiffeomorph_apply]
  change (-1 < -p.2 ∧ -p.2 < 1) ↔ (-1 < p.2 ∧ p.2 < 1)
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

theorem seamFlipChart_target_subset (φ : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus)
    {W : CompactCarrier.{u}}
    (c : PartialDiffeomorph signedCollarModel W.model (Torus × ℝ) W.Carrier ∞) :
    (seamFlipChart φ c).target ⊆ c.target :=
  fun _ hx => hx.1

namespace TorusPresentation

variable {W : CompactCarrier.{u}} (T : TorusPresentation W) (σ : Fin T.pairing.count → Bool)

def flipReconstruction : (flipPairing T.pairing σ).QuotientSpace ≃ₜ W.Carrier :=
  (Homeomorph.Quotient.congrRight (fun x y => flipGluing_rel x y)).trans T.reconstruction

theorem flipReconstruction_apply (x : T.cutCarrier.Carrier) :
    T.flipReconstruction σ ((flipPairing T.pairing σ).quotientMap x) =
      T.reconstruction (T.pairing.quotientMap x) := rfl

theorem quotientMap_leftParam_eq_rightParam (k : Fin T.pairing.count) (t : Torus) :
    T.pairing.quotientMap (T.pairing.leftParam k ((T.pairing.matching k).symm t)) =
      T.pairing.quotientMap (T.pairing.rightParam k t) := by
  have hx := (T.pairing.leftParam k ((T.pairing.matching k).symm t)).property
  apply Quotient.sound
  have e := T.pairing.gluing.rel_of_mem_left hx
  have e2 : (T.pairing.gluing.attaching k ⟨_, hx⟩ : T.cutCarrier.Carrier) =
      T.pairing.rightParam k t := by
    have := T.pairing.matching_eq k ((T.pairing.matching k).symm t)
    rw [Diffeomorph.apply_symm_apply] at this
    exact congrArg Subtype.val this
  rw [e2] at e
  exact e

theorem flip_block (k : Fin T.pairing.count) :
    (flipPairing T.pairing σ).gluing.block k = T.pairing.gluing.block k :=
  flipGluing_block _ _ k

def flipSeam (k : Fin T.pairing.count) :
    PartialDiffeomorph signedCollarModel W.model (Torus × ℝ) W.Carrier ∞ :=
  if σ k then seamFlipChart (T.pairing.matching k) (T.seam k) else T.seam k

theorem flipSeam_target_subset (k : Fin T.pairing.count) :
    (T.flipSeam σ k).target ⊆ (T.seam k).target := by
  unfold flipSeam
  split_ifs
  exacts [seamFlipChart_target_subset _ _, le_rfl]

theorem flip_iUnion_block :
    (⋃ i : Fin (flipPairing T.pairing σ).count, (flipPairing T.pairing σ).gluing.block i) =
      ⋃ i, T.pairing.gluing.block i :=
  Set.iUnion_congr (T.flip_block σ)

theorem flipSeam_zero (k : Fin T.pairing.count) (t : Torus) :
    T.flipSeam σ k (t, 0) = T.flipReconstruction σ ((flipPairing T.pairing σ).quotientMap
      ((flipPairing T.pairing σ).leftParam k t)) := by
  change _ = T.reconstruction (T.pairing.quotientMap _)
  rw [flipPairing_leftParam_val]
  unfold flipSeam
  by_cases h : σ k = true
  · rw [ite_eq_left h, ite_eq_left h, seamFlipChart_apply, neg_zero, T.seam_zero,
      T.quotientMap_leftParam_eq_rightParam]
    rfl
  · rw [ite_eq_right h, ite_eq_right h, T.seam_zero]
    rfl

theorem flipSeam_positive (k : Fin T.pairing.count) (t : Torus) (a : ℝ) (ha : 0 ≤ a)
    (h1 : a < 1) : T.flipSeam σ k (t, a) = T.flipReconstruction σ
      ((flipPairing T.pairing σ).quotientMap ((flipPairing T.pairing σ).rightCollar k
        ((flipPairing T.pairing σ).matching k t, halfPoint a ha))) := by
  change _ = T.reconstruction (T.pairing.quotientMap _)
  rw [flipPairing_rightCollar, flipPairing_matching]
  unfold flipSeam
  by_cases h : σ k = true
  · rw [ite_eq_left h, ite_eq_left h, ite_eq_left h, seamFlipChart_apply,
      T.seam_negative k _ (-a) (neg_nonpos.mpr ha) (by linarith)]
    simp only [neg_neg]
    rfl
  · rw [ite_eq_right h, ite_eq_right h, ite_eq_right h, T.seam_positive k t a ha h1]
    rfl

theorem flipSeam_negative (k : Fin T.pairing.count) (t : Torus) (a : ℝ) (ha : a ≤ 0)
    (h1 : -1 < a) : T.flipSeam σ k (t, a) = T.flipReconstruction σ
      ((flipPairing T.pairing σ).quotientMap ((flipPairing T.pairing σ).leftCollar k
        (t, halfPoint (-a) (neg_nonneg.mpr ha)))) := by
  change _ = T.reconstruction (T.pairing.quotientMap _)
  rw [flipPairing_leftCollar]
  unfold flipSeam
  by_cases h : σ k = true
  · rw [ite_eq_left h, ite_eq_left h, seamFlipChart_apply,
      T.seam_positive k _ (-a) (neg_nonneg.mpr ha) (by linarith), Diffeomorph.apply_symm_apply]
    rfl
  · rw [ite_eq_right h, ite_eq_right h, T.seam_negative k t a ha h1]
    rfl

theorem flipSeam_source (k : Fin T.pairing.count) :
    (T.flipSeam σ k).source = signedCollarSource := by
  unfold flipSeam
  split_ifs
  exacts [seamFlipChart_source _ _ (T.seam_source k), T.seam_source k]

def flipLeftPiece (k : Fin T.pairing.count) : Fin T.components.count :=
  if σ k then T.rightPiece k else T.leftPiece k

def flipRightPiece (k : Fin T.pairing.count) : Fin T.components.count :=
  if σ k then T.leftPiece k else T.rightPiece k

theorem flip_left_owned (k : Fin T.pairing.count) :
    (flipPairing T.pairing σ).gluing.left k ⊆ T.components.piece (T.flipLeftPiece σ k) := by
  unfold flipLeftPiece
  change (if σ k then T.pairing.gluing.right k else T.pairing.gluing.left k) ⊆ _
  by_cases h : σ k = true
  · rw [ite_eq_left h, ite_eq_left h]
    exact T.right_owned k
  · rw [ite_eq_right h, ite_eq_right h]
    exact T.left_owned k

theorem flip_right_owned (k : Fin T.pairing.count) :
    (flipPairing T.pairing σ).gluing.right k ⊆ T.components.piece (T.flipRightPiece σ k) := by
  unfold flipRightPiece
  change (if σ k then T.pairing.gluing.left k else T.pairing.gluing.right k) ⊆ _
  by_cases h : σ k = true
  · rw [ite_eq_left h, ite_eq_left h]
    exact T.left_owned k
  · rw [ite_eq_right h, ite_eq_right h]
    exact T.right_owned k

def flipSeams : TorusPresentation W where
  cutCarrier := T.cutCarrier
  components := T.components
  pairing := flipPairing T.pairing σ
  externalCount := T.externalCount
  external := T.external
  cutExternal := T.cutExternal
  external_exhausted := T.external_exhausted
  cut_boundary_exhausted := by
    rw [T.flip_iUnion_block σ]
    exact T.cut_boundary_exhausted
  external_disjoint := by
    rw [T.flip_iUnion_block σ]
    exact T.external_disjoint
  reconstruction := T.flipReconstruction σ
  quotient_smooth := T.quotient_smooth
  quotient_oriented := T.quotient_oriented
  interiorImage := T.interiorImage
  interiorDiffeomorph := T.interiorDiffeomorph
  interior_map := T.interior_map
  seam := T.flipSeam σ
  seam_source := T.flipSeam_source σ
  seam_zero := T.flipSeam_zero σ
  seam_positive := T.flipSeam_positive σ
  seam_negative := T.flipSeam_negative σ
  seam_interior k := (T.flipSeam_target_subset σ k).trans (T.seam_interior k)
  seam_disjoint i k hik := (T.seam_disjoint hik).mono (T.flipSeam_target_subset σ i)
    (T.flipSeam_target_subset σ k)
  marked_collar := T.marked_collar
  external_seam_disjoint i k := (T.external_seam_disjoint i k).mono_right
    (T.flipSeam_target_subset σ k)
  leftPiece := T.flipLeftPiece σ
  rightPiece := T.flipRightPiece σ
  left_owned := T.flip_left_owned σ
  right_owned := T.flip_right_owned σ
  externalPiece := T.externalPiece
  external_owned := T.external_owned

def flipSide : T.Side → (T.flipSeams σ).Side
  | .inl k => if σ k then .inr (.inl k) else .inl k
  | .inr (.inl k) => if σ k then .inl k else .inr (.inl k)
  | .inr (.inr e) => .inr (.inr e)

def unflipSide : (T.flipSeams σ).Side → T.Side
  | .inl k => if σ k then .inr (.inl k) else .inl k
  | .inr (.inl k) => if σ k then .inl k else .inr (.inl k)
  | .inr (.inr e) => .inr (.inr e)

def flipSideEquiv : T.Side ≃ (T.flipSeams σ).Side where
  toFun := T.flipSide σ
  invFun := T.unflipSide σ
  left_inv s := by
    rcases s with k | k | e
    · by_cases h : σ k = true <;> simp [flipSide, unflipSide, h]
    · by_cases h : σ k = true <;> simp [flipSide, unflipSide, h]
    · rfl
  right_inv s := by
    rcases s with k | k | e
    · by_cases h : σ k = true <;> simp [flipSide, unflipSide, h]
    · by_cases h : σ k = true <;> simp [flipSide, unflipSide, h]
    · rfl

theorem sidePiece_flipSide (s : T.Side) :
    (T.flipSeams σ).sidePiece (T.flipSide σ s) = T.sidePiece s := by
  rcases s with k | k | e
  · by_cases h : σ k = true <;>
      simp [flipSide, h, sidePiece, flipSeams, flipLeftPiece, flipRightPiece]
  · by_cases h : σ k = true <;>
      simp [flipSide, h, sidePiece, flipSeams, flipLeftPiece, flipRightPiece]
  · rfl

theorem sideCollar_flipSide (s : T.Side) :
    (T.flipSeams σ).sideCollar (T.flipSide σ s) = T.sideCollar s := by
  rcases s with k | k | e
  · by_cases h : σ k = true <;>
      simp [flipSide, h, sideCollar, flipSeams, flipPairing_leftCollar,
        flipPairing_rightCollar] <;> rfl
  · by_cases h : σ k = true <;>
      simp [flipSide, h, sideCollar, flipSeams, flipPairing_leftCollar,
        flipPairing_rightCollar] <;> rfl
  · rfl

def ownedSideFlip (i : Fin T.components.count) :
    T.OwnedSide i ≃ (T.flipSeams σ).OwnedSide i :=
  (T.flipSideEquiv σ).subtypeEquiv fun s => by
    change T.sidePiece s = i ↔ (T.flipSeams σ).sidePiece (T.flipSide σ s) = i
    rw [sidePiece_flipSide]
    exact Iff.rfl

theorem ownedSideFlip_val (i : Fin T.components.count) (s : T.OwnedSide i) :
    (T.ownedSideFlip σ i s).val = T.flipSide σ s.val := rfl

theorem pieceCollar_flip (i : Fin T.components.count) (s : T.OwnedSide i) :
    (T.flipSeams σ).pieceCollar i (T.ownedSideFlip σ i s) = T.pieceCollar i s := by
  unfold pieceCollar
  simp only [ownedSideFlip_val, sideCollar_flipSide]
  rfl

end TorusPresentation

namespace ProductFibredPiece

variable {W : CompactCarrier.{u}} {T : TorusPresentation.{u} W} {i : Fin T.components.count}
  {k : ℕ}

def flip (P : ProductFibredPiece T i k) (σ : Fin T.pairing.count → Bool) :
    ProductFibredPiece (T.flipSeams σ) i k where
  base := P.base
  port := P.port.trans (T.ownedSideFlip σ i)
  trivialization := P.trivialization
  collar_eq j p hp := by
    rw [Equiv.trans_apply, T.pieceCollar_flip]
    exact P.collar_eq j p hp

end ProductFibredPiece

namespace ElementaryPresentation

variable {W : CompactCarrier.{u}}

def flip (E : ElementaryPresentation W) (σ : Fin E.toTorus.pairing.count → Bool) :
    ElementaryPresentation W where
  toTorus := E.toTorus.flipSeams σ
  kind := E.kind
  kind_mem := E.kind_mem
  piece i := (E.piece i).flip σ

theorem torusUnit_symm (φ : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus) :
    torusUnit φ.symm = (torusUnit φ)⁻¹ :=
  Units.ext rfl

variable (E : ElementaryPresentation W) (σ : Fin E.toTorus.pairing.count → Bool)

theorem complexity_flip : (E.flip σ).complexity = E.complexity := rfl

theorem kind_flip (i : Fin E.toTorus.components.count) : (E.flip σ).kind i = E.kind i := rfl

theorem seamPiece_flip (j : Fin E.toTorus.pairing.count) (b : Bool) :
    (E.flip σ).seamPiece j b = E.seamPiece j (b ^^ σ j) := by
  cases b <;> by_cases h : σ j = true <;>
    simp [seamPiece, flip, TorusPresentation.flipSeams, TorusPresentation.flipLeftPiece,
      TorusPresentation.flipRightPiece, h]

theorem hostPiece_flip (j : Fin E.toTorus.pairing.count) (b : Bool) :
    (E.flip σ).hostPiece j b = E.hostPiece j (b ^^ σ j) := by
  unfold hostPiece
  rw [seamPiece_flip]
  cases b <;> cases σ j <;> rfl

theorem fillingDistance_flip (j : Fin E.toTorus.pairing.count) (b : Bool) :
    (E.flip σ).fillingDistance j b = E.fillingDistance j (b ^^ σ j) := by
  by_cases h : σ j = true
  · have hm : (E.flip σ).toTorus.pairing.matching j = (E.toTorus.pairing.matching j).symm :=
      ite_eq_left h
    cases b
    · simp only [h, Bool.false_xor]
      change PrimitiveSlope.delta (torusUnit ((E.flip σ).toTorus.pairing.matching j) •
        fiberSlope) meridianSlope = PrimitiveSlope.delta
          (torusUnit (E.toTorus.pairing.matching j) • meridianSlope) fiberSlope
      rw [hm, torusUnit_symm, PrimitiveSlope.delta_comm,
        ← PrimitiveSlope.delta_smul (torusUnit (E.toTorus.pairing.matching j)), smul_inv_smul]
    · simp only [h, Bool.true_xor, Bool.not_true]
      change PrimitiveSlope.delta (torusUnit ((E.flip σ).toTorus.pairing.matching j) •
        meridianSlope) fiberSlope = _
      rw [hm, torusUnit_symm, fillingDistance_false]
  · have hm : (E.flip σ).toTorus.pairing.matching j = E.toTorus.pairing.matching j :=
      ite_eq_right h
    rw [Bool.not_eq_true] at h
    simp only [h, Bool.xor_false]
    cases b
    · change PrimitiveSlope.delta (torusUnit ((E.flip σ).toTorus.pairing.matching j) •
        fiberSlope) meridianSlope = PrimitiveSlope.delta
          (torusUnit (E.toTorus.pairing.matching j) • fiberSlope) meridianSlope
      rw [hm]
    · change PrimitiveSlope.delta (torusUnit ((E.flip σ).toTorus.pairing.matching j) •
        meridianSlope) fiberSlope = PrimitiveSlope.delta
          (torusUnit (E.toTorus.pairing.matching j) • meridianSlope) fiberSlope
      rw [hm]

end ElementaryPresentation

end GC.Seifert

namespace GC.Seifert

namespace StarGroup

variable {W : CompactCarrier.{u}} {T : TorusPresentation.{u} W} {d : SeifertData}
  (G : StarGroup T d) (hext : ∀ i, T.externalPiece i ∉ G.set)
  (hk : T.cutCarrier.kind = .withBoundary) (r0 : (T.restrictCarrier G.set hext).Carrier)

def contractBlock :
    PieceBlock (T.contract G.set hext hk (G.isConnected_region hext))
      (T.contractLast G.set hext hk (G.isConnected_region hext)) where
  data := d
  block := (G.restrictBlock hext).transport
    (T.restrictContractDiffeomorph G.set hext hk (G.isConnected_region hext) r0)
    (T.restrictContractDiffeomorph_preservesOrientation G.set hext hk
      (G.isConnected_region hext) r0)
  port := (Fintype.equivFin _).symm.trans
    (T.contractLastSideEquiv G.set hext hk (G.isConnected_region hext)).symm
  collar_eq r p hp := by
    apply Subtype.ext
    rw [TorusPresentation.pieceCollar_apply _ _ _ hp,
      T.contract_sideCollar_apply G.set hext hk (G.isConnected_region hext) _ hp]
    change Sum.inr ((T.restrict G.set G.set_nonempty hext).external.collar r p) = _
    change _ = T.contractMap G.set hext hk (T.sideCollar (T.contractLiftSide G.set hext hk
      (G.isConnected_region hext) ((T.contractLastSideEquiv G.set hext hk
        (G.isConnected_region hext)).symm (T.restrictSide G.set r)).val) p)
    rw [T.contractLiftSide_contractLastSideEquiv_symm,
      T.contractMap_sideCollar_of_mem G.set hext hk _ hp (T.restrictSide G.set r).property.1]
    exact congrArg Sum.inr (Subtype.ext (T.restrict_external_collar_val G.set
      G.set_nonempty hext r hp))

theorem contractBlock_data : (G.contractBlock hext hk r0).data = d := rfl

end StarGroup

end GC.Seifert

namespace GC.Seifert

namespace ProductFibredPiece

variable {W : CompactCarrier.{u}} {T : TorusPresentation.{u} W} {k : ℕ}

def congrIndex {i i' : Fin T.components.count} (P : ProductFibredPiece T i k) (h : i = i') :
    ProductFibredPiece T i' k :=
  h ▸ P

end ProductFibredPiece

namespace TorusPresentation

variable {W : CompactCarrier.{u}} (T : TorusPresentation.{u} W)
  (S : Finset (Fin T.components.count)) (hext : ∀ i, T.externalPiece i ∉ S)
  (hk : T.cutCarrier.kind = .withBoundary)
  (hconn : IsConnected (Set.range (T.restrictMap S) \ T.crossingSurface S))

def contractSeam {k : Fin T.pairing.count} (hk' : ¬(T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S)) :
    Fin (T.contract S hext hk hconn).pairing.count :=
  Fintype.equivFin (T.NonInternal S) ⟨k, hk'⟩

theorem nonInternal_contractSeam {k : Fin T.pairing.count}
    (hk' : ¬(T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S)) :
    (T.nonInternal S (T.contractSeam S hext hk hconn hk')).val = k := by
  unfold contractSeam
  rw [nonInternal_equivFin]

theorem contract_matching_contractSeam {k : Fin T.pairing.count}
    (hk' : ¬(T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S)) :
    (T.contract S hext hk hconn).pairing.matching (T.contractSeam S hext hk hconn hk') =
      T.pairing.matching k := by
  change T.pairing.matching (T.nonInternal S (T.contractSeam S hext hk hconn hk')).val = _
  rw [nonInternal_contractSeam]

theorem contract_leftPiece_contractSeam {k : Fin T.pairing.count}
    (hk' : ¬(T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S)) (hl : T.leftPiece k ∉ S) :
    (T.contract S hext hk hconn).leftPiece (T.contractSeam S hext hk hconn hk') =
      T.contractIndex S hext hk hconn hl := by
  refine (T.contract_sidePiece_eq_contractIndex_iff S hext hk hconn hl
    (.inl (T.contractSeam S hext hk hconn hk'))).mpr ?_
  change T.leftPiece (T.nonInternal S (T.contractSeam S hext hk hconn hk')).val = _
  rw [nonInternal_contractSeam]

theorem contract_rightPiece_contractSeam {k : Fin T.pairing.count}
    (hk' : ¬(T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S)) (hr : T.rightPiece k ∉ S) :
    (T.contract S hext hk hconn).rightPiece (T.contractSeam S hext hk hconn hk') =
      T.contractIndex S hext hk hconn hr := by
  refine (T.contract_sidePiece_eq_contractIndex_iff S hext hk hconn hr
    (.inr (.inl (T.contractSeam S hext hk hconn hk')))).mpr ?_
  change T.rightPiece (T.nonInternal S (T.contractSeam S hext hk hconn hk')).val = _
  rw [nonInternal_contractSeam]

theorem contractIndex_injective {i i' : Fin T.components.count} (hi : i ∉ S) (hi' : i' ∉ S)
    (h : T.contractIndex S hext hk hconn hi = T.contractIndex S hext hk hconn hi') : i = i' :=
  (T.subIndexOf_eq_iff _ _).mp (Fin.castSucc_injective _ h)

end TorusPresentation

namespace StarGroup

variable {W : CompactCarrier.{u}} {T : TorusPresentation.{u} W} {d : SeifertData}
  (G : StarGroup T d) {S : Finset (Fin T.components.count)}
  (hext : ∀ i, T.externalPiece i ∉ S) (hk : T.cutCarrier.kind = .withBoundary)
  (hconn : IsConnected (Set.range (T.restrictMap S) \ T.crossingSurface S))
  (hdisj : Disjoint G.set S)

include hdisj in
theorem center_not_mem : G.center ∉ S :=
  Finset.disjoint_left.mp hdisj G.center_mem

include hdisj in
theorem solid_not_mem (l : Fin d.fillingCount) : T.leftPiece (G.arm l) ∉ S :=
  Finset.disjoint_left.mp hdisj (G.solid_mem l)

include hdisj in
theorem arm_nonInternal (l : Fin d.fillingCount) :
    ¬(T.leftPiece (G.arm l) ∈ S ∧ T.rightPiece (G.arm l) ∈ S) :=
  fun h => G.solid_not_mem hdisj l h.1

def transfer : StarGroup (T.contract S hext hk hconn) d where
  center := T.contractIndex S hext hk hconn (G.center_not_mem hdisj)
  product := G.product.transfer (T.contractTransfer S hext hk hconn (G.center_not_mem hdisj))
  arm l := T.contractSeam S hext hk hconn (G.arm_nonInternal hdisj l)
  solid l := ((G.solid l).transfer (T.contractTransfer S hext hk hconn
    (G.solid_not_mem hdisj l))).congrIndex
    (T.contract_leftPiece_contractSeam S hext hk hconn _ (G.solid_not_mem hdisj l)).symm
  arm_right l := by
    rw [T.contract_rightPiece_contractSeam S hext hk hconn _
      ((G.arm_right l).symm ▸ G.center_not_mem hdisj)]
    congr 1
    exact G.arm_right l
  arm_injective l l' h := by
    have h' := congrArg (fun j => (T.nonInternal S j).val) h
    simp only [TorusPresentation.nonInternal_contractSeam] at h'
    exact G.arm_injective h'
  no_self k hl hr := by
    have hl' := (T.contract_sidePiece_eq_contractIndex_iff S hext hk hconn
      (G.center_not_mem hdisj) (.inl k)).mp hl
    have hr' := (T.contract_sidePiece_eq_contractIndex_iff S hext hk hconn
      (G.center_not_mem hdisj) (.inr (.inl k))).mp hr
    exact G.no_self _ hl' hr'
  slope l := by
    rw [T.contract_matching_contractSeam]
    exact G.slope l

end StarGroup

end GC.Seifert

namespace GC.Seifert

def GoodData (d : SeifertData) : Prop :=
  ∀ (V : CompactCarrier.{u}) (B : SeifertBlock V d), B.IsGoodBlock

namespace PieceBlock

variable {W : CompactCarrier.{u}} {T : TorusPresentation.{u} W}

def congrIndex {i i' : Fin T.components.count} (B : PieceBlock T i) (h : i = i') :
    PieceBlock T i' :=
  h ▸ B

theorem congrIndex_data {i i' : Fin T.components.count} (B : PieceBlock T i) (h : i = i') :
    (B.congrIndex h).data = B.data := by
  subst h
  rfl

end PieceBlock

namespace StarGroup

variable {W : CompactCarrier.{u}} {T : TorusPresentation.{u} W} {d : SeifertData}
  (G : StarGroup T d) {S : Finset (Fin T.components.count)}
  (hext : ∀ i, T.externalPiece i ∉ S) (hk : T.cutCarrier.kind = .withBoundary)
  (hconn : IsConnected (Set.range (T.restrictMap S) \ T.crossingSurface S))
  (hdisj : Disjoint G.set S)

theorem mem_transfer_set {j : Fin (T.contract S hext hk hconn).components.count}
    (hj : j ∈ (G.transfer hext hk hconn hdisj).set) :
    ∃ i, ∃ hi : i ∉ S, i ∈ G.set ∧ j = T.contractIndex S hext hk hconn hi := by
  rcases (G.transfer hext hk hconn hdisj).mem_set hj with h | ⟨l, h⟩
  · exact ⟨_, G.center_not_mem hdisj, G.center_mem, h⟩
  · refine ⟨_, G.solid_not_mem hdisj l, G.solid_mem l, h.trans ?_⟩
    exact T.contract_leftPiece_contractSeam S hext hk hconn _ (G.solid_not_mem hdisj l)

theorem contractIndex_mem_transfer_set {i : Fin T.components.count} (hi : i ∉ S)
    (h : i ∈ G.set) :
    T.contractIndex S hext hk hconn hi ∈ (G.transfer hext hk hconn hdisj).set := by
  rcases G.mem_set h with rfl | ⟨l, rfl⟩
  · exact (G.transfer hext hk hconn hdisj).center_mem
  · have h1 := (G.transfer hext hk hconn hdisj).solid_mem l
    change (T.contract S hext hk hconn).leftPiece
      (T.contractSeam S hext hk hconn (G.arm_nonInternal hdisj l)) ∈ _ at h1
    rwa [T.contract_leftPiece_contractSeam S hext hk hconn _ hi] at h1

end StarGroup

structure Grouping {W : CompactCarrier.{u}} (T : TorusPresentation.{u} W) (n : ℕ) where
  data : Fin n → SeifertData
  group : (a : Fin n) → StarGroup T (data a)
  arm_pos : ∀ a, 0 < (data a).fillingCount
  good : ∀ a, GoodData.{u} (data a)
  disjoint : ∀ a b, a ≠ b → Disjoint (group a).set (group b).set
  rest : ∀ i, (∀ a, i ∉ (group a).set) → {B : PieceBlock T i // GoodData.{u} B.data}

namespace Grouping

variable {W : CompactCarrier.{u}} {T : TorusPresentation.{u} W}

theorem hext_of_externalCount (hW : T.externalCount = 0) (S : Finset (Fin T.components.count)) :
    ∀ i, T.externalPiece i ∉ S :=
  fun i => Fin.elim0 (i.cast hW)

theorem exists_isGood_zero (Γ : Grouping T 0) : ∃ B : BlockedPresentation W, B.IsGood :=
  ⟨BlockedPresentation.ofPieceBlocks T fun i => (Γ.rest i fun a => a.elim0).val,
    fun i => (Γ.rest i fun a => a.elim0).property _ _⟩

end Grouping

end GC.Seifert

namespace GC.Seifert

namespace Grouping

variable {W : CompactCarrier.{u}} {T : TorusPresentation.{u} W} {n : ℕ}
  (Γ : Grouping T (n + 1)) (hW : T.externalCount = 0)

def firstSet : Finset (Fin T.components.count) := (Γ.group 0).set

include hW in
theorem hext_first : ∀ i, T.externalPiece i ∉ Γ.firstSet :=
  hext_of_externalCount hW _

include Γ in
theorem kind_first : T.cutCarrier.kind = .withBoundary :=
  T.cutCarrier_kind_of_pos (Fin.pos ((Γ.group 0).arm ⟨0, Γ.arm_pos 0⟩))

include hW in
theorem isConnected_first :
    IsConnected (Set.range (T.restrictMap Γ.firstSet) \ T.crossingSurface Γ.firstSet) :=
  (Γ.group 0).isConnected_region (Γ.hext_first hW)

def next : TorusPresentation.{u} W :=
  T.contract Γ.firstSet (Γ.hext_first hW) Γ.kind_first (Γ.isConnected_first hW)

omit hW in
theorem disjoint_first (a : Fin n) : Disjoint (Γ.group a.succ).set Γ.firstSet :=
  Γ.disjoint _ _ (Fin.succ_ne_zero a)

def nextGroup (a : Fin n) : StarGroup (Γ.next hW) (Γ.data a.succ) :=
  (Γ.group a.succ).transfer (Γ.hext_first hW) Γ.kind_first (Γ.isConnected_first hW)
    (Γ.disjoint_first a)

def firstPoint : (T.restrictCarrier Γ.firstSet (Γ.hext_first hW)).Carrier :=
  ⟨(Γ.isConnected_first hW).nonempty.some, (Γ.isConnected_first hW).nonempty.some_mem.1⟩

theorem not_mem_first_of_castPred (j : Fin (Γ.next hW).components.count)
    (h : j ≠ Fin.last _) :
    T.subIndex Γ.firstSetᶜ (j.castPred h) ∉ Γ.firstSet :=
  Finset.mem_compl.mp (T.subIndex_mem _ _)

theorem contractIndex_castPred (j : Fin (Γ.next hW).components.count) (h : j ≠ Fin.last _) :
    T.contractIndex Γ.firstSet (Γ.hext_first hW) Γ.kind_first (Γ.isConnected_first hW)
      (Γ.not_mem_first_of_castPred hW j h) = j := by
  unfold TorusPresentation.contractIndex
  rw [TorusPresentation.subIndexOf_subIndex]
  exact Fin.castSucc_castPred j h

theorem rest_cond (j : Fin (Γ.next hW).components.count) (h : j ≠ Fin.last _)
    (hj : ∀ a, j ∉ (Γ.nextGroup hW a).set) :
    ∀ a, T.subIndex Γ.firstSetᶜ (j.castPred h) ∉ (Γ.group a).set := by
  intro a
  induction a using Fin.cases with
  | zero => exact Γ.not_mem_first_of_castPred hW j h
  | succ b =>
    intro hb
    apply hj b
    rw [← Γ.contractIndex_castPred hW j h]
    exact (Γ.group b.succ).contractIndex_mem_transfer_set _ _ _ (Γ.disjoint_first b) _ hb

open Classical in
def nextRest (j : Fin (Γ.next hW).components.count) (hj : ∀ a, j ∉ (Γ.nextGroup hW a).set) :
    {B : PieceBlock (Γ.next hW) j // GoodData.{u} B.data} :=
  if h : j = Fin.last _ then
    ⟨((Γ.group 0).contractBlock (Γ.hext_first hW) Γ.kind_first (Γ.firstPoint hW)).congrIndex
      h.symm, (congrArg GoodData.{u} (PieceBlock.congrIndex_data _ _)).mpr (Γ.good 0)⟩
  else
    ⟨(((Γ.rest _ (Γ.rest_cond hW j h hj)).val.transfer
      (T.contractTransfer Γ.firstSet (Γ.hext_first hW) Γ.kind_first (Γ.isConnected_first hW)
        (Γ.not_mem_first_of_castPred hW j h))
      (T.contractTransfer_preservesOrientation _ _ _ _ _)).congrIndex
      (Γ.contractIndex_castPred hW j h)),
      (congrArg GoodData.{u} (PieceBlock.congrIndex_data _ _)).mpr (Γ.rest _ _).property⟩

theorem nextGroup_disjoint (a b : Fin n) (hab : a ≠ b) :
    Disjoint (Γ.nextGroup hW a).set (Γ.nextGroup hW b).set := by
  refine Finset.disjoint_left.mpr fun j ha hb => ?_
  obtain ⟨i, hi, hia, rfl⟩ := (Γ.group a.succ).mem_transfer_set _ _ _ _ ha
  obtain ⟨i', hi', hib, he⟩ := (Γ.group b.succ).mem_transfer_set _ _ _ _ hb
  have hii := T.contractIndex_injective _ _ _ _ hi hi' he
  subst hii
  exact Finset.disjoint_left.mp (Γ.disjoint _ _ (fun e => hab (Fin.succ_injective _ e))) hia hib

def nextGrouping : Grouping (Γ.next hW) n where
  data a := Γ.data a.succ
  group := Γ.nextGroup hW
  arm_pos a := Γ.arm_pos a.succ
  good a := Γ.good a.succ
  disjoint := Γ.nextGroup_disjoint hW
  rest := Γ.nextRest hW

end Grouping

theorem Grouping.exists_isGood {W : CompactCarrier.{u}} :
    ∀ (n : ℕ) {T : TorusPresentation.{u} W}, T.externalCount = 0 → Grouping T n →
      ∃ B : BlockedPresentation W, B.IsGood
  | 0, _, _, Γ => Γ.exists_isGood_zero
  | n + 1, _, hW, Γ => Grouping.exists_isGood n (T := Γ.next hW) hW (Γ.nextGrouping hW)

end GC.Seifert

namespace GC.Seifert

theorem exists_cone_of_two_le_delta (s : PrimitiveSlope)
    (h : 2 ≤ PrimitiveSlope.delta s fiberSlope) :
    ∃ c : ℕ × ℤ, ∃ hc : Int.gcd (c.1 : ℤ) c.2 = 1, 2 ≤ c.1 ∧
      s = PrimitiveSlope.mk ((c.1 : ℤ), c.2) hc := by
  induction s using PrimitiveSlope.ind with
  | h v hv =>
    rw [fiberSlope, PrimitiveSlope.delta_mk] at h
    simp only [slopeDet, mul_one, mul_zero, sub_zero] at h
    rcases le_or_gt 0 v.1 with h0 | h0
    · have hv1 : ((v.1.natAbs : ℕ) : ℤ) = v.1 := Int.natAbs_of_nonneg h0
      have hc : Int.gcd ((v.1.natAbs : ℕ) : ℤ) v.2 = 1 := by rw [hv1]; exact hv
      exact ⟨(v.1.natAbs, v.2), hc, h,
        (PrimitiveSlope.mk_eq_mk_iff (w := ((v.1.natAbs : ℤ), v.2)) hv hc).mpr
          (Or.inl (Prod.ext hv1 rfl))⟩
    · have hv1 : ((v.1.natAbs : ℕ) : ℤ) = -v.1 := Int.ofNat_natAbs_of_nonpos h0.le
      have hc : Int.gcd ((v.1.natAbs : ℕ) : ℤ) (-v.2) = 1 := by
        rw [hv1, Int.gcd_neg, Int.neg_gcd]
        exact hv
      exact ⟨(v.1.natAbs, -v.2), hc, h,
        (PrimitiveSlope.mk_eq_mk_iff (w := ((v.1.natAbs : ℤ), -v.2)) hv hc).mpr
          (Or.inr (Prod.ext hv1 rfl))⟩

def coneData (m : ℕ) (hm : m ≤ 3) (c : Fin m → ℕ × ℤ) (hc2 : ∀ l, 2 ≤ (c l).1)
    (hcg : ∀ l, Int.gcd ((c l).1 : ℤ) (c l).2 = 1) : SeifertData where
  k := 3
  ports := 3 - m
  cones := List.ofFn c
  normals := []
  one_le_k := by norm_num
  k_le_three := le_rfl
  two_le_of_mem_cones x hx := by
    obtain ⟨l, rfl⟩ := List.mem_ofFn.mp hx
    exact hc2 l
  gcd_eq_one_of_mem_cones x hx := by
    obtain ⟨l, rfl⟩ := List.mem_ofFn.mp hx
    exact hcg l
  ports_add_length_add_length := by
    simp only [List.length_ofFn, List.length_nil, add_zero]
    omega

theorem coneData_fillingCount (m : ℕ) (hm : m ≤ 3) (c : Fin m → ℕ × ℤ) (hc2 : ∀ l, 2 ≤ (c l).1)
    (hcg : ∀ l, Int.gcd ((c l).1 : ℤ) (c l).2 = 1) :
    (coneData m hm c hc2 hcg).fillingCount = m := by
  simp [coneData, SeifertData.fillingCount]

theorem coneData_fillingSlope (m : ℕ) (hm : m ≤ 3) (c : Fin m → ℕ × ℤ)
    (hc2 : ∀ l, 2 ≤ (c l).1) (hcg : ∀ l, Int.gcd ((c l).1 : ℤ) (c l).2 = 1)
    (l : Fin (coneData m hm c hc2 hcg).fillingCount) :
    (coneData m hm c hc2 hcg).fillingSlope l =
      (((c (l.cast (coneData_fillingCount m hm c hc2 hcg))).1 : ℤ),
        (c (l.cast (coneData_fillingCount m hm c hc2 hcg))).2) := by
  have h0 : (coneData m hm c hc2 hcg).fillingCount =
      (coneData m hm c hc2 hcg).cones.length := by
    simp [coneData, SeifertData.fillingCount]
  have hl : l = Fin.castAdd (coneData m hm c hc2 hcg).normals.length (l.cast h0) :=
    Fin.ext rfl
  unfold SeifertData.fillingSlope
  conv_lhs => rw [hl, Fin.append_left]
  simp only [coneData, Fin.getElem_fin, List.getElem_ofFn]
  rfl

theorem goodData_coneData_one (c : Fin 1 → ℕ × ℤ) (hc2 : ∀ l, 2 ≤ (c l).1)
    (hcg : ∀ l, Int.gcd ((c l).1 : ℤ) (c l).2 = 1) :
    GoodData.{u} (coneData 1 (by norm_num) c hc2 hcg) :=
  fun _ B => B.isGoodBlock_of_one_filling rfl (coneData_fillingCount _ _ _ _ _)

end GC.Seifert

namespace GC.Seifert

theorem goodData_coneData_three (c : Fin 3 → ℕ × ℤ) (hc2 : ∀ l, 2 ≤ (c l).1)
    (hcg : ∀ l, Int.gcd ((c l).1 : ℤ) (c l).2 = 1) :
    GoodData.{u} (coneData 3 le_rfl c hc2 hcg) :=
  fun _ B => B.isGoodBlock_of_ports_eq_zero rfl

theorem goodData_productData (k : ℕ) (hk1 : 1 ≤ k) (hk2 : 2 ≤ k) (hk3 : k ≤ 3) :
    GoodData.{u} (productData k hk1 hk3) :=
  fun _ B => SeifertBlock.isGoodBlock_of_fillingCount_eq_zero B (by exact hk2) rfl

end GC.Seifert

namespace GC.Seifert

namespace ElementaryPresentation

variable {W : CompactCarrier.{u}} (E : ElementaryPresentation W)

def pieceOfKind {i : Fin E.toTorus.components.count} {k : ℕ} (h : E.kind i = k) :
    ProductFibredPiece E.toTorus i k :=
  h ▸ E.piece i

theorem eq_of_leftPiece_eq {j j' : Fin E.toTorus.pairing.count}
    (hj : E.kind (E.toTorus.leftPiece j) = 1)
    (h : E.toTorus.leftPiece j = E.toTorus.leftPiece j') : j = j' := by
  have hsub := (E.pieceOfKind hj).card_ownedSide
  have h1 : Subsingleton (E.toTorus.OwnedSide (E.toTorus.leftPiece j)) :=
    Fintype.card_le_one_iff_subsingleton.mp hsub.le
  have := congrArg Subtype.val (Subsingleton.elim
    (⟨.inl j, rfl⟩ : E.toTorus.OwnedSide (E.toTorus.leftPiece j)) ⟨.inl j', h.symm⟩)
  exact Sum.inl_injective this

def IsArm (c : Fin E.toTorus.components.count) (j : Fin E.toTorus.pairing.count) : Prop :=
  E.toTorus.rightPiece j = c ∧ E.kind (E.toTorus.leftPiece j) = 1

open Classical in
noncomputable instance (c : Fin E.toTorus.components.count) :
    Fintype {j // E.IsArm c j} :=
  Subtype.fintype _

def armSide (c : Fin E.toTorus.components.count) (j : {j // E.IsArm c j}) :
    E.toTorus.OwnedSide c :=
  ⟨.inr (.inl j.val), j.property.1⟩

theorem armSide_injective (c : Fin E.toTorus.components.count) :
    Function.Injective (E.armSide c) := by
  intro a b h
  exact Subtype.ext (Sum.inl_injective (Sum.inr_injective (congrArg Subtype.val h)))

theorem card_arm_le (c : Fin E.toTorus.components.count) :
    Fintype.card {j // E.IsArm c j} ≤ E.kind c := by
  have h := Fintype.card_le_of_injective _ (E.armSide_injective c)
  rwa [(E.piece c).card_ownedSide] at h

theorem two_le_fillingDistance (hE : E.IsMoveFree)
    (hR : ∀ j, E.kind (E.toTorus.rightPiece j) ≠ 1) {c : Fin E.toTorus.components.count}
    (j : {j // E.IsArm c j}) :
    E.kind c = 3 ∧ 2 ≤ E.fillingDistance j.val true := by
  rcases hE j.val true j.property.2 with h | h
  · exact absurd h (hR j.val)
  · have hc : E.hostPiece j.val true = c := j.property.1
    rw [hc] at h
    exact h

end ElementaryPresentation

end GC.Seifert

namespace GC.Seifert

namespace ElementaryPresentation

variable {W : CompactCarrier.{u}} (E : ElementaryPresentation W) (hE : E.IsMoveFree)
  (hR : ∀ j, E.kind (E.toTorus.rightPiece j) ≠ 1) (c : Fin E.toTorus.components.count)

def armCount : ℕ := Fintype.card {j // E.IsArm c j}

def armEquiv : Fin (E.armCount c) ≃ {j // E.IsArm c j} := (Fintype.equivFin _).symm

def armSlope (l : Fin (E.armCount c)) : PrimitiveSlope :=
  torusUnit (E.toTorus.pairing.matching (E.armEquiv c l).val) • meridianSlope

include hE hR in
theorem two_le_delta_armSlope (l : Fin (E.armCount c)) :
    2 ≤ PrimitiveSlope.delta (E.armSlope c l) fiberSlope :=
  (E.two_le_fillingDistance hE hR (E.armEquiv c l)).2

def armCone (l : Fin (E.armCount c)) : ℕ × ℤ :=
  Classical.choose (exists_cone_of_two_le_delta _ (E.two_le_delta_armSlope hE hR c l))

theorem armCone_spec (l : Fin (E.armCount c)) :
    ∃ hc : Int.gcd ((E.armCone hE hR c l).1 : ℤ) (E.armCone hE hR c l).2 = 1,
      2 ≤ (E.armCone hE hR c l).1 ∧
        E.armSlope c l = PrimitiveSlope.mk (((E.armCone hE hR c l).1 : ℤ),
          (E.armCone hE hR c l).2) hc :=
  Classical.choose_spec (exists_cone_of_two_le_delta _ (E.two_le_delta_armSlope hE hR c l))

theorem armCount_le_three : E.armCount c ≤ 3 := by
  have h1 := E.card_arm_le c
  have h2 := E.kind_eq_one_or_two_or_three c
  unfold armCount
  omega

def centreData : SeifertData :=
  coneData (E.armCount c) (E.armCount_le_three c) (E.armCone hE hR c)
    (fun l => (E.armCone_spec hE hR c l).2.1) (fun l => (E.armCone_spec hE hR c l).1)

theorem centreData_fillingCount : (E.centreData hE hR c).fillingCount = E.armCount c :=
  coneData_fillingCount _ _ _ _ _

def centreArm (l : Fin (E.centreData hE hR c).fillingCount) : {j // E.IsArm c j} :=
  E.armEquiv c (l.cast (E.centreData_fillingCount hE hR c))

def centreGroup (hc3 : E.kind c = 3)
    (hS : ∀ k, E.toTorus.leftPiece k = c → E.toTorus.rightPiece k ≠ c) :
    StarGroup E.toTorus (E.centreData hE hR c) where
  center := c
  product := E.pieceOfKind hc3
  arm l := (E.centreArm hE hR c l).val
  solid l := E.pieceOfKind (E.centreArm hE hR c l).property.2
  arm_right l := (E.centreArm hE hR c l).property.1
  arm_injective l l' h := by
    have h1 := (E.armEquiv c).injective (Subtype.ext h)
    exact Fin.cast_injective _ h1
  no_self := hS
  slope l := by
    refine (E.armCone_spec hE hR c _).2.2.trans ((PrimitiveSlope.mk_eq_mk_iff _ _).mpr
      (Or.inl ?_))
    exact coneData_fillingSlope _ _ _ _ _ l

end ElementaryPresentation

end GC.Seifert

namespace GC.Seifert

theorem goodData_coneData_two (c : Fin 2 → ℕ × ℤ) (hc2 : ∀ l, 2 ≤ (c l).1)
    (hcg : ∀ l, Int.gcd ((c l).1 : ℤ) (c l).2 = 1) :
    GoodData.{u} (coneData 2 (by norm_num) c hc2 hcg) := by
  intro V B
  refine filledBlockGoodness V _ B (by simp [coneData]) ?_
  simp [SeifertData.IsSolidTorus, coneData]

theorem goodData_coneData (m : ℕ) (hm : m ≤ 3) (h1 : 1 ≤ m) (c : Fin m → ℕ × ℤ)
    (hc2 : ∀ l, 2 ≤ (c l).1) (hcg : ∀ l, Int.gcd ((c l).1 : ℤ) (c l).2 = 1) :
    GoodData.{u} (coneData m hm c hc2 hcg) := by
  interval_cases m
  · exact goodData_coneData_one c hc2 hcg
  · exact goodData_coneData_two c hc2 hcg
  · exact goodData_coneData_three c hc2 hcg

namespace ElementaryPresentation

variable {W : CompactCarrier.{u}} (E : ElementaryPresentation W) (hE : E.IsMoveFree)
  (hR : ∀ j, E.kind (E.toTorus.rightPiece j) ≠ 1)
  (hS : ∀ c, 0 < E.armCount c → ∀ k, E.toTorus.leftPiece k = c → E.toTorus.rightPiece k ≠ c)

def IsCentre (c : Fin E.toTorus.components.count) : Prop := E.kind c = 3 ∧ 0 < E.armCount c

open Classical in
noncomputable instance : Fintype {c // E.IsCentre c} :=
  Subtype.fintype _

def centreEquiv : Fin (Fintype.card {c // E.IsCentre c}) ≃ {c // E.IsCentre c} :=
  (Fintype.equivFin _).symm

def groupOf (a : Fin (Fintype.card {c // E.IsCentre c})) :
    StarGroup E.toTorus (E.centreData hE hR (E.centreEquiv a).val) :=
  E.centreGroup hE hR _ (E.centreEquiv a).property.1 (hS _ (E.centreEquiv a).property.2)

theorem mem_groupOf_set {a : Fin (Fintype.card {c // E.IsCentre c})}
    {i : Fin E.toTorus.components.count} (hi : i ∈ (E.groupOf hE hR hS a).set) :
    i = (E.centreEquiv a).val ∨ ∃ j, E.IsArm (E.centreEquiv a).val j ∧
      i = E.toTorus.leftPiece j := by
  rcases (E.groupOf hE hR hS a).mem_set hi with h | ⟨l, h⟩
  · exact Or.inl h
  · exact Or.inr ⟨_, (E.centreArm hE hR _ l).property, h⟩

theorem groupOf_disjoint (a b : Fin (Fintype.card {c // E.IsCentre c})) (hab : a ≠ b) :
    Disjoint (E.groupOf hE hR hS a).set (E.groupOf hE hR hS b).set := by
  have hne : (E.centreEquiv a).val ≠ (E.centreEquiv b).val :=
    fun h => hab ((E.centreEquiv).injective (Subtype.ext h))
  refine Finset.disjoint_left.mpr fun i ha hb => ?_
  rcases E.mem_groupOf_set hE hR hS ha with h1 | ⟨j, hj, h1⟩ <;>
    rcases E.mem_groupOf_set hE hR hS hb with h2 | ⟨j', hj', h2⟩
  · exact hne (h1.symm.trans h2)
  · have := (E.centreEquiv a).property.1
    rw [← h1, h2, hj'.2] at this
    exact absurd this (by norm_num)
  · have := (E.centreEquiv b).property.1
    rw [← h2, h1, hj.2] at this
    exact absurd this (by norm_num)
  · have hjj := E.eq_of_leftPiece_eq hj.2 (h1.symm.trans h2)
    subst hjj
    exact hne (hj.1.symm.trans hj'.1)

theorem armCount_pos_of_arm {c : Fin E.toTorus.components.count} {j : Fin E.toTorus.pairing.count}
    (hj : E.IsArm c j) : 0 < E.armCount c :=
  Fintype.card_pos_iff.mpr ⟨⟨j, hj⟩⟩

theorem kind_ne_one_of_not_mem (hW : E.toTorus.externalCount = 0)
    (i : Fin E.toTorus.components.count)
    (hi : ∀ a, i ∉ (E.groupOf hE hR hS a).set) : E.kind i ≠ 1 := by
  intro h1
  have hcard := (E.pieceOfKind h1).card_ownedSide
  obtain ⟨s⟩ : Nonempty (E.toTorus.OwnedSide i) := Fintype.card_pos_iff.mp (by omega)
  rcases s with ⟨j | j | e, hs⟩
  · change E.toTorus.leftPiece j = i at hs
    have hj : E.IsArm (E.toTorus.rightPiece j) j := ⟨rfl, hs ▸ h1⟩
    have hc : E.IsCentre (E.toTorus.rightPiece j) :=
      ⟨(E.two_le_fillingDistance hE hR ⟨j, hj⟩).1, E.armCount_pos_of_arm hj⟩
    obtain ⟨a, ha⟩ := (E.centreEquiv).surjective ⟨_, hc⟩
    apply hi a
    have hj' : E.IsArm (E.centreEquiv a).val j := by rw [ha]; exact hj
    obtain ⟨l, hl⟩ := (E.armEquiv (E.centreEquiv a).val).surjective ⟨j, hj'⟩
    have hmem := (E.groupOf hE hR hS a).solid_mem
      (l.cast (E.centreData_fillingCount hE hR _).symm)
    change E.toTorus.leftPiece (E.centreArm hE hR _ _).val ∈ _ at hmem
    unfold centreArm at hmem
    rw [Fin.cast_cast, Fin.cast_eq_self, hl] at hmem
    exact hs ▸ hmem
  · change E.toTorus.rightPiece j = i at hs
    exact hR j (hs ▸ h1)
  · exact Fin.elim0 (e.cast hW)

end ElementaryPresentation

end GC.Seifert

namespace GC.Seifert

namespace ElementaryPresentation

variable {W : CompactCarrier.{u}} (E : ElementaryPresentation W) (hE : E.IsMoveFree)
  (hR : ∀ j, E.kind (E.toTorus.rightPiece j) ≠ 1)
  (hS : ∀ c, 0 < E.armCount c → ∀ k, E.toTorus.leftPiece k = c → E.toTorus.rightPiece k ≠ c)
  (hW : E.toTorus.externalCount = 0)

def restBlock (i : Fin E.toTorus.components.count)
    (hi : ∀ a, i ∉ (E.groupOf hE hR hS a).set) :
    {B : PieceBlock E.toTorus i // GoodData.{u} B.data} :=
  have h1 := E.kind_ne_one_of_not_mem hE hR hS hW i hi
  have h3 := E.kind_eq_one_or_two_or_three i
  ⟨(E.piece i).pieceBlock (by omega) (by omega), goodData_productData _ _ (by omega) _⟩

def groupingOf : Grouping E.toTorus (Fintype.card {c // E.IsCentre c}) where
  data a := E.centreData hE hR (E.centreEquiv a).val
  group := E.groupOf hE hR hS
  arm_pos a := by
    rw [centreData_fillingCount]
    exact (E.centreEquiv a).property.2
  good a := goodData_coneData _ _ (E.centreEquiv a).property.2 _ _ _
  disjoint := E.groupOf_disjoint hE hR hS
  rest := E.restBlock hE hR hS hW

include hE hR hS hW in
theorem exists_isGood_blockedPresentation : ∃ B : BlockedPresentation W, B.IsGood :=
  Grouping.exists_isGood _ hW (E.groupingOf hE hR hS hW)

end ElementaryPresentation

theorem seifertFactor_of_isMoveFree_of_normal {Q : ConnectedClosedOrientedManifold.{u} 3}
    (E : ElementaryPresentation (NoCuts.carrier Q)) (hE : E.IsMoveFree)
    (hR : ∀ j, E.kind (E.toTorus.rightPiece j) ≠ 1)
    (hS : ∀ c, 0 < E.armCount c → ∀ k, E.toTorus.leftPiece k = c →
      E.toTorus.rightPiece k ≠ c) : SeifertFactor Q :=
  Or.inr (Or.inr (E.exists_isGood_blockedPresentation hE hR hS
    E.toTorus.externalCount_eq_zero))

end GC.Seifert

namespace GC.Seifert

namespace ElementaryPresentation

variable {W : CompactCarrier.{u}} (E : ElementaryPresentation W)

theorem isMoveFree_flip (σ : Fin E.toTorus.pairing.count → Bool) (hE : E.IsMoveFree) :
    (E.flip σ).IsMoveFree := by
  intro j b h
  have e1 := E.seamPiece_flip σ j b
  have e2 := E.hostPiece_flip σ j b
  have e3 := E.fillingDistance_flip σ j b
  have h' : E.kind (E.seamPiece j (b ^^ σ j)) = 1 := e1 ▸ h
  have key := hE j (b ^^ σ j) h'
  rw [← e2, ← e3] at key
  exact key

def solidFlip (j : Fin E.toTorus.pairing.count) : Bool :=
  decide (E.kind (E.toTorus.rightPiece j) = 1 ∧ E.kind (E.toTorus.leftPiece j) ≠ 1)

theorem kind_rightPiece_flip_ne
    (hNS : ∀ j, ¬(E.kind (E.toTorus.leftPiece j) = 1 ∧ E.kind (E.toTorus.rightPiece j) = 1))
    (j : Fin E.toTorus.pairing.count) :
    (E.flip E.solidFlip).kind ((E.flip E.solidFlip).toTorus.rightPiece j) ≠ 1 := by
  change E.kind ((E.flip E.solidFlip).seamPiece j false) ≠ 1
  rw [seamPiece_flip, Bool.false_xor]
  by_cases h1 : E.kind (E.toTorus.rightPiece j) = 1 ∧ E.kind (E.toTorus.leftPiece j) ≠ 1
  · have hs : E.solidFlip j = true := decide_eq_true h1
    rw [hs]
    exact h1.2
  · have hs : E.solidFlip j = false := decide_eq_false h1
    rw [hs]
    intro h2
    exact hNS j ⟨not_not.mp fun h3 => h1 ⟨h2, h3⟩, h2⟩

end ElementaryPresentation

end GC.Seifert

namespace GC.Seifert

namespace TorusPresentation

theorem mem_of_not_isCrossing {Q : ConnectedClosedOrientedManifold.{u} 3}
    (T : TorusPresentation (NoCuts.carrier Q)) (S : Finset (Fin T.components.count))
    (hS : S.Nonempty) (hnc : ∀ k, ¬ T.IsCrossing S k) (i : Fin T.components.count) : i ∈ S := by
  have hcross : T.crossingSurface S = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro y hy
    obtain ⟨k', hk', -⟩ := Set.mem_iUnion₂.mp hy
    exact hnc k' hk'
  have hdisj : ∀ y, y ∈ Set.range (T.restrictMap S) → y ∉ T.complImage S := fun y h1 h2 => by
    have := T.range_inter_complImage_subset_crossing S ⟨h1, h2⟩
    rw [hcross] at this
    exact this
  have hcov := T.range_union_complImage S
  have hrange : Set.range (T.restrictMap S) = (T.complImage S)ᶜ := by
    ext y
    constructor
    · exact hdisj y
    · intro hy
      have hu : y ∈ Set.range (T.restrictMap S) ∪ T.complImage S := hcov ▸ Set.mem_univ y
      rcases hu with h1 | h1
      · exact h1
      · exact absurd h1 hy
  obtain ⟨i0, hi0⟩ := hS
  obtain ⟨x0⟩ := (T.components.connected i0).toNonempty
  have hne : (Set.range (T.restrictMap S)).Nonempty :=
    ⟨_, Set.mem_range_self ((T.restrictPairing S).quotientMap
      ⟨x0.val, T.piece_subset_subPiece S hi0 x0.property⟩)⟩
  have huniv : Set.range (T.restrictMap S) = Set.univ :=
    IsClopen.eq_univ ⟨T.isClosed_range_restrictMap S,
      hrange ▸ (T.isClosed_complImage S).isOpen_compl⟩ hne
  by_contra hi
  obtain ⟨x⟩ := (T.components.connected i).toNonempty
  have hx : x.val ∉ T.subPiece S := fun hxS => hi (T.mem_of_mem_subPiece S hxS x.property)
  exact hdisj _ (huniv ▸ Set.mem_univ _) ⟨x.val, hx, rfl⟩

end TorusPresentation

end GC.Seifert

namespace GC.Seifert

theorem exists_pos_of_one_le_delta (s : PrimitiveSlope)
    (h : 1 ≤ PrimitiveSlope.delta s fiberSlope) :
    ∃ c : ℕ × ℤ, ∃ hc : Int.gcd (c.1 : ℤ) c.2 = 1, 1 ≤ c.1 ∧
      s = PrimitiveSlope.mk ((c.1 : ℤ), c.2) hc := by
  induction s using PrimitiveSlope.ind with
  | h v hv =>
    rw [fiberSlope, PrimitiveSlope.delta_mk] at h
    simp only [slopeDet, mul_one, mul_zero, sub_zero] at h
    rcases le_or_gt 0 v.1 with h0 | h0
    · have hv1 : ((v.1.natAbs : ℕ) : ℤ) = v.1 := Int.natAbs_of_nonneg h0
      have hc : Int.gcd ((v.1.natAbs : ℕ) : ℤ) v.2 = 1 := by rw [hv1]; exact hv
      exact ⟨(v.1.natAbs, v.2), hc, h,
        (PrimitiveSlope.mk_eq_mk_iff (w := ((v.1.natAbs : ℤ), v.2)) hv hc).mpr
          (Or.inl (Prod.ext hv1 rfl))⟩
    · have hv1 : ((v.1.natAbs : ℕ) : ℤ) = -v.1 := Int.ofNat_natAbs_of_nonpos h0.le
      have hc : Int.gcd ((v.1.natAbs : ℕ) : ℤ) (-v.2) = 1 := by
        rw [hv1, Int.gcd_neg, Int.neg_gcd]
        exact hv
      exact ⟨(v.1.natAbs, -v.2), hc, h,
        (PrimitiveSlope.mk_eq_mk_iff (w := ((v.1.natAbs : ℤ), -v.2)) hv hc).mpr
          (Or.inr (Prod.ext hv1 rfl))⟩

def lensConeData (c : ℕ × ℤ) (h2 : 2 ≤ c.1) (hc : Int.gcd (c.1 : ℤ) c.2 = 1) : SeifertData :=
  ⟨1, 0, [c], [], le_rfl, by norm_num, by simpa using h2, by simpa using hc, rfl⟩

def lensNormalData (q : ℤ) : SeifertData :=
  ⟨1, 0, [], [q], le_rfl, by norm_num, by simp, by simp, rfl⟩

theorem lensConeData_fillingSlope (c : ℕ × ℤ) (h2 : 2 ≤ c.1) (hc : Int.gcd (c.1 : ℤ) c.2 = 1)
    (l : Fin (lensConeData c h2 hc).fillingCount) :
    (lensConeData c h2 hc).fillingSlope l = ((c.1 : ℤ), c.2) := by
  obtain rfl : l = ⟨0, by simp [lensConeData, SeifertData.fillingCount]⟩ :=
    Fin.ext (by have := l.isLt; simp [lensConeData, SeifertData.fillingCount] at this; omega)
  rfl

theorem lensNormalData_fillingSlope (q : ℤ) (l : Fin (lensNormalData q).fillingCount) :
    (lensNormalData q).fillingSlope l = (1, q) := by
  obtain rfl : l = ⟨0, by simp [lensNormalData, SeifertData.fillingCount]⟩ :=
    Fin.ext (by have := l.isLt; simp [lensNormalData, SeifertData.fillingCount] at this; omega)
  rfl

end GC.Seifert

namespace GC.Seifert

namespace ElementaryPresentation

section Lens

variable {Q : ConnectedClosedOrientedManifold.{u} 3} (E : ElementaryPresentation (NoCuts.carrier Q))
  {j : Fin E.toTorus.pairing.count} (hL : E.kind (E.toTorus.leftPiece j) = 1)
  (hR1 : E.kind (E.toTorus.rightPiece j) = 1)

theorem side_eq_of_kind_one {i : Fin E.toTorus.components.count} (hi : E.kind i = 1)
    (s s' : E.toTorus.OwnedSide i) : s = s' :=
  have h := (E.pieceOfKind hi).card_ownedSide
  (Fintype.card_le_one_iff_subsingleton.mp h.le).elim s s'

def lensGroup (d : SeifertData) (hk : d.k = 1) (hcount : d.fillingCount = 1)
    (hslope : ∀ l, torusUnit (E.toTorus.pairing.matching j) • meridianSlope =
      PrimitiveSlope.mk (d.fillingSlope l) (d.isPrimitive_fillingSlope l)) :
    StarGroup E.toTorus d where
  center := E.toTorus.rightPiece j
  product := E.pieceOfKind (hR1.trans hk.symm)
  arm _ := j
  solid _ := E.pieceOfKind hL
  arm_right _ := rfl
  arm_injective l l' _ := Fin.ext (by have := l.isLt; have := l'.isLt; omega)
  no_self k hk' _ := by
    have := congrArg Subtype.val (E.side_eq_of_kind_one hR1 ⟨.inl k, hk'⟩ ⟨.inr (.inl j), rfl⟩)
    exact absurd this (by simp)
  slope := hslope

theorem mem_lensGroup_set (d : SeifertData) (hk : d.k = 1) (hcount : d.fillingCount = 1)
    (hslope : ∀ l, torusUnit (E.toTorus.pairing.matching j) • meridianSlope =
      PrimitiveSlope.mk (d.fillingSlope l) (d.isPrimitive_fillingSlope l))
    (i : Fin E.toTorus.components.count) :
    i ∈ (E.lensGroup hL hR1 d hk hcount hslope).set := by
  let G := E.lensGroup hL hR1 d hk hcount hslope
  have l0 : Fin d.fillingCount := ⟨0, by omega⟩
  have hl : E.toTorus.leftPiece j ∈ G.set := G.solid_mem l0
  have hr : E.toTorus.rightPiece j ∈ G.set := G.center_mem
  have key : ∀ i ∈ G.set, i = E.toTorus.rightPiece j ∨ i = E.toTorus.leftPiece j := by
    intro i hi
    rcases G.mem_set hi with h | ⟨l, h⟩
    · exact Or.inl h
    · exact Or.inr h
  refine TorusPresentation.mem_of_not_isCrossing E.toTorus G.set ⟨_, hr⟩ (fun k hk' => ?_) i
  rcases hk' with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rcases key _ h1 with he | he
    · have := congrArg Subtype.val (E.side_eq_of_kind_one hR1 ⟨.inl k, he⟩ ⟨.inr (.inl j), rfl⟩)
      exact absurd this (by simp)
    · have := congrArg Subtype.val (E.side_eq_of_kind_one hL ⟨.inl k, he⟩ ⟨.inl j, rfl⟩)
      obtain rfl : k = j := Sum.inl_injective this
      exact h2 hr
  · rcases key _ h1 with he | he
    · have := congrArg Subtype.val
        (E.side_eq_of_kind_one hR1 ⟨.inr (.inl k), he⟩ ⟨.inr (.inl j), rfl⟩)
      obtain rfl : k = j := Sum.inl_injective (Sum.inr_injective this)
      exact h2 hl
    · have := congrArg Subtype.val (E.side_eq_of_kind_one hL ⟨.inr (.inl k), he⟩ ⟨.inl j, rfl⟩)
      exact absurd this (by simp)

def lensGrouping (d : SeifertData) (hk : d.k = 1) (hcount : d.fillingCount = 1)
    (hports : d.ports = 0)
    (hslope : ∀ l, torusUnit (E.toTorus.pairing.matching j) • meridianSlope =
      PrimitiveSlope.mk (d.fillingSlope l) (d.isPrimitive_fillingSlope l)) :
    Grouping E.toTorus 1 where
  data _ := d
  group _ := E.lensGroup hL hR1 d hk hcount hslope
  arm_pos _ := by omega
  good _ := fun _ B => B.isGoodBlock_of_ports_eq_zero hports
  disjoint a b hab := absurd (Subsingleton.elim a b) hab
  rest i hi := absurd (E.mem_lensGroup_set hL hR1 d hk hcount hslope i) (hi 0)

include hL hR1 in
theorem seifertFactor_of_solidSeam (hpos : 1 ≤ E.fillingDistance j true) : SeifertFactor Q := by
  obtain ⟨c, hc, h1, hs⟩ := exists_pos_of_one_le_delta
    (torusUnit (E.toTorus.pairing.matching j) • meridianSlope) hpos
  refine Or.inr (Or.inr ?_)
  by_cases h2 : 2 ≤ c.1
  · refine Grouping.exists_isGood 1 E.toTorus.externalCount_eq_zero
      (E.lensGrouping hL hR1 (lensConeData c h2 hc) rfl rfl rfl fun l => ?_)
    exact hs.trans ((PrimitiveSlope.mk_eq_mk_iff _ _).mpr
      (Or.inl (lensConeData_fillingSlope c h2 hc l)))
  · have hc1 : c.1 = 1 := by omega
    refine Grouping.exists_isGood 1 E.toTorus.externalCount_eq_zero
      (E.lensGrouping hL hR1 (lensNormalData c.2) rfl rfl rfl fun l => ?_)
    refine hs.trans ((PrimitiveSlope.mk_eq_mk_iff _ _).mpr (Or.inl ?_))
    rw [lensNormalData_fillingSlope, hc1]
    rfl

end Lens

end ElementaryPresentation

end GC.Seifert

namespace GC.Seifert

namespace ElementaryPresentation

theorem seifertFactor_of_solidSeam_flip {Q : ConnectedClosedOrientedManifold.{u} 3}
    (E : ElementaryPresentation (NoCuts.carrier Q)) {j : Fin E.toTorus.pairing.count}
    (hL : E.kind (E.toTorus.leftPiece j) = 1) (hR : E.kind (E.toTorus.rightPiece j) = 1)
    (h1 : 1 ≤ E.fillingDistance j false) : SeifertFactor Q := by
  let σ : Fin E.toTorus.pairing.count → Bool := fun k => decide (k = j)
  have hσ : σ j = true := decide_eq_true rfl
  have eL := E.seamPiece_flip σ j true
  have eR := E.seamPiece_flip σ j false
  have eD := E.fillingDistance_flip σ j true
  rw [hσ] at eL eR eD
  have hL' : (E.flip σ).kind ((E.flip σ).seamPiece j true) = 1 := by
    have h : E.kind (E.seamPiece j (true ^^ true)) = 1 := hR
    exact eL ▸ h
  have hR' : (E.flip σ).kind ((E.flip σ).seamPiece j false) = 1 := by
    have h : E.kind (E.seamPiece j (false ^^ true)) = 1 := hL
    exact eR ▸ h
  have hD : 1 ≤ (E.flip σ).fillingDistance j true := by
    rw [eD]
    exact h1
  exact (E.flip σ).seifertFactor_of_solidSeam hL' hR' hD

end ElementaryPresentation

end GC.Seifert
