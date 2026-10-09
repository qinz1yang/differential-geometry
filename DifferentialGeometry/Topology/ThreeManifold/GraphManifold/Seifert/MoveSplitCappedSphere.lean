import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MoveSplitCappedTube
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MoveSplitCappedStandard

/-!
# The split sphere of a linear split seam

Lane N2c, tier 1. For a split seam `j` on side `b` of an elementary presentation `E` of a closed
`Q` whose matching is linear, the standard product structures of tier 0 give the charts of the
split tube: `solid (z, w) = cutMap (ΘV (z, w))` on the disc of radius `3`, `hostMap (z, ν) =
cutMap (ΘH (z, ν))` on the round pants, and the seam chart of `j` read from the solid side
(`ElementaryPresentation.splitCharts`). The resulting one-tube system is `splitSeamTube`, with
middle sphere `splitSeamSphere`, a smooth embedding of the round sphere
(`splitSeamSphere_isSmoothEmbedding`).

Generic pieces: the clamp of the plane into a regular sublevel set is a local diffeomorphism at
interior points (`isLocalDiffeomorphAt_clampLift`), and a product chart of a piece followed by
the reconstruction map is a local diffeomorphism and injective at interior points
(`isLocalDiffeomorphAt_pieceChart`, `pieceChart_injOn`).
-/

set_option autoImplicit false

noncomputable section
open Set Filter Function Metric
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert

section Clamp

variable {K : Set PlaneLift.{u}} (C : SmoothBoundaryAtlas 𝓘(ℝ, ℂ) 2 K)

open Classical in
def clampLift (x₀ : K) (z : ℂ) : K := if hz : ULift.up z ∈ K then ⟨ULift.up z, hz⟩ else x₀

theorem clampLift_val (x₀ : K) {z : ℂ} (hz : ULift.up z ∈ K) :
    (clampLift x₀ z).val = ULift.up z := by
  classical
  rw [clampLift, dite_eq_left hz]

theorem isLocalDiffeomorphAt_clampLift (x₀ : K) {z : ℂ} (hz : ULift.up z ∈ interior K) :
    let _ := C.toChartedSpace
    IsLocalDiffeomorphAt 𝓘(ℝ, ℂ) (𝓡∂ 2) ∞ (clampLift x₀) z := by
  let _ := C.toChartedSpace
  refine C.isLocalDiffeomorphAt_of_subtype_val ?_ ?_
  · rw [clampLift_val x₀ (interior_subset hz)]
    exact hz
  · have hU : IsOpen {w : ℂ | ULift.up w ∈ interior K} :=
      isOpen_interior.preimage (uliftDiffeomorph (I := 𝓘(ℝ, ℂ)) (M := ℂ)).continuous
    have heq : (Subtype.val ∘ clampLift x₀) =ᶠ[𝓝 z]
        (uliftDiffeomorph (I := 𝓘(ℝ, ℂ)) (M := ℂ)) := by
      refine Filter.eventuallyEq_of_mem (hU.mem_nhds hz) fun w hw => ?_
      exact clampLift_val x₀ (interior_subset hw)
    exact IsLocalDiffeomorphAt.of_eventuallyEq heq
      ((uliftDiffeomorph (I := 𝓘(ℝ, ℂ)) (M := ℂ)).isLocalDiffeomorph z)

end Clamp

namespace TorusPresentation

variable {W : CompactCarrier.{u}} (T : TorusPresentation W)

theorem cutMap_eq_of_isInteriorPoint {x y : T.cutCarrier.Carrier}
    (hx : T.cutCarrier.model.IsInteriorPoint x) (h : T.cutMap x = T.cutMap y) : x = y := by
  have hq : T.pairing.quotientMap x = T.pairing.quotientMap y := T.reconstruction.injective h
  rcases (Quotient.exact hq : T.pairing.gluing.rel x y) with he | ⟨d, hd, -⟩
  · exact he
  · have hb : x ∈ T.cutCarrier.model.boundary T.cutCarrier.Carrier := by
      rw [T.cut_boundary_exhausted]
      exact Or.inl (mem_iUnion.2 ⟨d, hd⟩)
    exact absurd hx ((ModelWithCorners.isBoundaryPoint_iff_not_isInteriorPoint _).mp hb)

theorem eq_of_mem_piece' {x : T.cutCarrier.Carrier} {i i' : Fin T.components.count}
    (hi : x ∈ T.components.piece i) (hi' : x ∈ T.components.piece i') : i = i' := by
  by_contra h
  exact (T.components.disjoint h).le_bot ⟨hi, hi'⟩

section PieceChart

variable (i : Fin T.components.count) {k : ℕ} (B : PlanarBase.{u} k)
  (Θ : (B.surface.Carrier × Circle) ≃ₘ⟮(SurfaceModel.model B.surface.kind).prod (𝓡 1),
    T.cutCarrier.model⟯ T.components.piece i) (g : ℂ → B.surface.Carrier)

def pieceChart (q : ℂ × Circle) : W.Carrier := T.cutMap (Θ (g q.1, q.2) : T.cutCarrier.Carrier)

theorem pieceChart_isInteriorPoint {q : ℂ × Circle}
    (hg : IsLocalDiffeomorphAt 𝓘(ℝ, ℂ) (SurfaceModel.model B.surface.kind) ∞ g q.1) :
    T.cutCarrier.model.IsInteriorPoint (Θ (g q.1, q.2) : T.cutCarrier.Carrier) ∧
      IsLocalDiffeomorphAt (𝓘(ℝ, ℂ).prod (𝓡 1)) T.cutCarrier.model ∞
        (fun q : ℂ × Circle => (Θ (g q.1, q.2) : T.cutCarrier.Carrier)) q := by
  have h1 : IsLocalDiffeomorphAt (𝓘(ℝ, ℂ).prod (𝓡 1))
      ((SurfaceModel.model B.surface.kind).prod (𝓡 1)) ∞ (Prod.map g id) (q.1, q.2) :=
    hg.prodMap ((Diffeomorph.refl (𝓡 1) Circle ∞).isLocalDiffeomorph q.2)
  have h2 := h1.comp _ _ (Θ.isLocalDiffeomorph _)
  have h3 := h2.comp _ _ (DifferentialGeometry.isLocalDiffeomorph_subtype_val
    (I := T.cutCarrier.model) (T.components.piece i) _)
  refine ⟨(h3.isInteriorPoint_iff (by simp)).mp BoundarylessManifold.isInteriorPoint, h3⟩

theorem isLocalDiffeomorphAt_pieceChart {q : ℂ × Circle}
    (hg : IsLocalDiffeomorphAt 𝓘(ℝ, ℂ) (SurfaceModel.model B.surface.kind) ∞ g q.1) :
    IsLocalDiffeomorphAt (𝓘(ℝ, ℂ).prod (𝓡 1)) W.model ∞ (T.pieceChart i B Θ g) q := by
  obtain ⟨hint, hloc⟩ := T.pieceChart_isInteriorPoint i B Θ g hg
  exact hloc.comp _ _ (T.isLocalDiffeomorphAt_cutMap hint)

theorem pieceChart_injOn {q q' : ℂ × Circle}
    (hg : IsLocalDiffeomorphAt 𝓘(ℝ, ℂ) (SurfaceModel.model B.surface.kind) ∞ g q.1)
    (hgi : g q.1 = g q'.1 → q.1 = q'.1) (h : T.pieceChart i B Θ g q = T.pieceChart i B Θ g q') :
    q = q' := by
  obtain ⟨hint, -⟩ := T.pieceChart_isInteriorPoint i B Θ g hg
  have e := Θ.injective (Subtype.ext (T.cutMap_eq_of_isInteriorPoint hint h))
  simp only [Prod.mk.injEq] at e
  exact Prod.ext (hgi e.1) e.2

theorem pieceChart_ne {i' : Fin T.components.count} (hii : i ≠ i') {k' : ℕ} (B' : PlanarBase.{u} k')
    (Θ' : (B'.surface.Carrier × Circle) ≃ₘ⟮(SurfaceModel.model B'.surface.kind).prod (𝓡 1),
      T.cutCarrier.model⟯ T.components.piece i') (g' : ℂ → B'.surface.Carrier) {q q' : ℂ × Circle}
    (hg : IsLocalDiffeomorphAt 𝓘(ℝ, ℂ) (SurfaceModel.model B.surface.kind) ∞ g q.1) :
    T.pieceChart i B Θ g q ≠ T.pieceChart i' B' Θ' g' q' := by
  intro h
  obtain ⟨hint, -⟩ := T.pieceChart_isInteriorPoint i B Θ g hg
  have e := T.cutMap_eq_of_isInteriorPoint hint h
  have h1 := (Θ (g q.1, q.2)).property
  have h2 := (Θ' (g' q'.1, q'.2)).property
  rw [← e] at h2
  exact hii (T.eq_of_mem_piece' h1 h2)

theorem cutMap_ne_pieceChart {y : T.cutCarrier.Carrier}
    (hy : y ∈ T.cutCarrier.model.boundary T.cutCarrier.Carrier) {q : ℂ × Circle}
    (hg : IsLocalDiffeomorphAt 𝓘(ℝ, ℂ) (SurfaceModel.model B.surface.kind) ∞ g q.1) :
    T.cutMap y ≠ T.pieceChart i B Θ g q := by
  intro h
  obtain ⟨hint, -⟩ := T.pieceChart_isInteriorPoint i B Θ g hg
  have e := T.cutMap_eq_of_isInteriorPoint hint h.symm
  rw [e] at hint
  exact (ModelWithCorners.isBoundaryPoint_iff_not_isInteriorPoint _).mp hy hint

end PieceChart

end TorusPresentation

namespace ElementaryPresentation

section SplitData

variable {W : CompactCarrier.{u}} (E : ElementaryPresentation W) {j : Fin E.toTorus.pairing.count}
  {b : Bool}

structure SplitData (h : E.IsSplitSeam j b) where
  δ : ℝ
  hδ : 0 < δ
  ΘV : ((discPlanarBase.{u} 1).surface.Carrier × Circle) ≃ₘ⟮(SurfaceModel.model
    (discPlanarBase.{u} 1).surface.kind).prod (𝓡 1), E.toTorus.cutCarrier.model⟯
      E.toTorus.components.piece (E.seamPiece j b)
  ΘH : (pantsPlanarBase.{u}.surface.Carrier × Circle) ≃ₘ⟮(SurfaceModel.model
    pantsPlanarBase.{u}.surface.kind).prod (𝓡 1), E.toTorus.cutCarrier.model⟯
      E.toTorus.components.piece (E.hostPiece j b)
  hV : ∀ l p, p ∈ halfCollarSource → p.2.val 0 < δ →
    E.toTorus.pieceCollar (E.seamPiece j b) (E.standardPort (E.seamPiece j b) h.1 l) p =
      ΘV ((discPlanarBase.{u} 1).collar l (p.1.1, p.2), p.1.2)
  hH : ∀ l p, p ∈ halfCollarSource → p.2.val 0 < δ →
    E.toTorus.pieceCollar (E.hostPiece j b) (E.standardPort (E.hostPiece j b) h.2.1 l) p =
      ΘH (pantsPlanarBase.{u}.collar l (p.1.1, p.2), p.1.2)

theorem nonempty_splitData (h : E.IsSplitSeam j b) : Nonempty (E.SplitData h) := by
  obtain ⟨δ, hδ, ΘV, ΘH, hV, hH⟩ := E.exists_standardSplit h
  exact ⟨⟨δ, hδ, ΘV, ΘH, hV, hH⟩⟩

def splitData (h : E.IsSplitSeam j b) : E.SplitData h := Classical.choice (E.nonempty_splitData h)

def seamCoord (j : Fin E.toTorus.pairing.count) :
    Bool → (Torus × ℝ) ≃ₘ⟮signedCollarModel, signedCollarModel⟯ (Torus × ℝ)
  | true => Diffeomorph.refl signedCollarModel (Torus × ℝ) ∞
  | false => (E.toTorus.pairing.matching j).symm.prodCongr
      (ContinuousLinearEquiv.neg ℝ : ℝ ≃L[ℝ] ℝ).toDiffeomorph

theorem seamCoord_apply (j : Fin E.toTorus.pairing.count) :
    ∀ (b : Bool) (q : Torus × ℝ), E.seamCoord j b q = (E.leftOfSide j b q.1, sideHeight b (-q.2))
  | true, q => by simp [seamCoord, leftOfSide, sideHeight]
  | false, q => by
    simp only [seamCoord, leftOfSide, sideHeight]
    rfl

theorem sideHeight_neg (b : Bool) (r : ℝ) : sideHeight b (-r) = -sideHeight b r := by
  cases b <;> simp [sideHeight]

end SplitData

def discBase0 : discSet.{u} := ⟨ULift.up 0, by rw [mem_discSet_iff]; simp⟩

def pantsBase0 : planarSet.{u} 3 := ⟨ULift.up 0, by
  rw [mem_planarSet_iff (Or.inr rfl), mem_planarModel_three]
  norm_num⟩

theorem up_mem_interior_discSet {z : ℂ} (hz : ‖z‖ < 3) :
    (ULift.up z : PlaneLift.{u}) ∈ interior discSet.{u} := by
  refine interior_maximal (t := {w : PlaneLift.{u} | ‖w.down‖ < 3}) ?_ ?_
    (show (ULift.up z : PlaneLift.{u}) ∈ {w : PlaneLift.{u} | ‖w.down‖ < 3} from hz)
  · intro w hw
    rw [mem_discSet_iff]
    exact le_of_lt hw
  · exact isOpen_lt (continuous_norm.comp contMDiff_planeLift_down.continuous) continuous_const

theorem up_mem_interior_planarSet {z : ℂ} (hz : z ∈ SplitTube.pantsInterior) :
    (ULift.up z : PlaneLift.{u}) ∈ interior (planarSet.{u} 3) := by
  refine interior_maximal (t := {w : PlaneLift.{u} | w.down ∈ SplitTube.pantsInterior}) ?_ ?_
    (show (ULift.up z : PlaneLift.{u}) ∈ {w : PlaneLift.{u} | w.down ∈ SplitTube.pantsInterior}
      from hz)
  · intro w hw
    rw [mem_planarSet_iff (Or.inr rfl)]
    exact SplitTube.pantsInterior_subset hw
  · exact SplitTube.isOpen_pantsInterior.preimage contMDiff_planeLift_down.continuous

def clampDisc : ℂ → (discPlanarBase.{u} 1).surface.Carrier := clampLift discBase0

def clampPants : ℂ → pantsPlanarBase.{u}.surface.Carrier := clampLift pantsBase0

theorem isLocalDiffeomorphAt_clampDisc {z : ℂ} (hz : ‖z‖ < 3) :
    IsLocalDiffeomorphAt 𝓘(ℝ, ℂ) (SurfaceModel.model (discPlanarBase.{u} 1).surface.kind) ∞
      clampDisc z :=
  isLocalDiffeomorphAt_clampLift discAtlas discBase0 (up_mem_interior_discSet hz)

theorem isLocalDiffeomorphAt_clampPants {z : ℂ} (hz : z ∈ SplitTube.pantsInterior) :
    IsLocalDiffeomorphAt 𝓘(ℝ, ℂ) (SurfaceModel.model pantsPlanarBase.{u}.surface.kind) ∞
      clampPants z :=
  isLocalDiffeomorphAt_clampLift (planarAtlas 3) pantsBase0 (up_mem_interior_planarSet hz)

theorem clampDisc_val {z : ℂ} (hz : ‖z‖ ≤ 3) :
    (clampDisc.{u} z : discSet.{u}).val = ULift.up z :=
  clampLift_val discBase0 ((mem_discSet_iff _).mpr hz)

theorem clampPants_val {z : ℂ} (hz : z ∈ planarModel 3) :
    (clampPants.{u} z : planarSet.{u} 3).val = ULift.up z :=
  clampLift_val pantsBase0 ((mem_planarSet_iff (Or.inr rfl) _).mpr hz)

theorem seamRadius_one (r : ℝ) : seamRadius 1 r = 3 + 3 * r / 2 := by
  simp only [seamRadius, Nat.cast_one, inv_one, Real.rpow_one]
  ring

theorem discCollar_eq {θ : Circle} {s : ℝ} (hs : 0 ≤ s) (hs1 : s < 1) :
    (discPlanarBase.{u} 1).collar 0 (θ, halfPoint s hs) =
      clampDisc ((3 - 3 * s / 2 : ℝ) • (θ : ℂ)) := by
  have hq : (θ, halfPoint s hs) ∈ circleCollarSource := hs1
  apply Subtype.ext
  apply ULift.ext
  have h1 := discCollar_apply_val.{u} 1 hq
  have hn : ‖(3 - 3 * s / 2 : ℝ) • (θ : ℂ)‖ ≤ 3 := by
    rw [norm_smul, Circle.norm_coe, mul_one, Real.norm_of_nonneg (by linarith)]
    linarith
  rw [clampDisc_val hn]
  change ((discCollar.{u} 1 (θ, halfPoint s hs)).val).down = _
  rw [h1, seamRadius_one]
  change ((3 + 3 * -s / 2 : ℝ) • (θ : ℂ)) = (3 - 3 * s / 2 : ℝ) • (θ : ℂ)
  congr 1
  ring

theorem pantsCollar_eq (l : Fin 3) {θ : Circle} {s : ℝ} (hs : 0 ≤ s) (hs1 : s < 1) :
    pantsPlanarBase.{u}.collar l (θ, halfPoint s hs) =
      clampPants (planarCollarFormula 3 l (θ, s)) := by
  have hq : (θ, halfPoint s hs) ∈ circleCollarSource := hs1
  apply Subtype.ext
  rw [clampPants_val (planarCollarFormula_mem (Or.inr rfl) l θ hs hs1.le)]
  apply ULift.ext
  exact planarCollar_apply_val.{u} (Or.inr rfl) l hq

section Instance

variable {Q : ConnectedClosedOrientedManifold.{u} 3} (E : ElementaryPresentation (NoCuts.carrier Q))
  {j : Fin E.toTorus.pairing.count} {b : Bool}

def solidMap (h : E.IsSplitSeam j b) : ℂ × Circle → Q.Carrier :=
  E.toTorus.pieceChart (E.seamPiece j b) (discPlanarBase.{u} 1) (E.splitData h).ΘV clampDisc

def hostMap (h : E.IsSplitSeam j b) : ℂ × Circle → Q.Carrier :=
  E.toTorus.pieceChart (E.hostPiece j b) pantsPlanarBase.{u} (E.splitData h).ΘH clampPants

def seamMap (j : Fin E.toTorus.pairing.count) (b : Bool) (q : Torus × ℝ) : Q.Carrier :=
  E.toTorus.seam j (E.seamCoord j b q)

def hostSide (h : E.IsSplitSeam j b) : Fin 3 :=
  (E.standardPort (E.hostPiece j b) h.2.1).symm ⟨E.seamSide j !b, E.sidePiece_seamSide j !b⟩

theorem crossUnit_zero (h : E.IsSplitSeam j b) :
    (E.crossUnit j b : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = 0 := by
  have h0 := h.2.2
  rw [fillingDistance_eq_crossUnit, delta_smul_meridianSlope, Int.natAbs_eq_zero] at h0
  exact h0

theorem seamMap_zero (j : Fin E.toTorus.pairing.count) (b : Bool) (t : Torus) :
    E.seamMap j b (t, 0) =
      E.toTorus.cutMap (E.toTorus.sideCollar (E.seamSide j b) (t, halfZero)) := by
  rw [seamMap, seamCoord_apply, neg_zero]
  exact (E.cutMap_sideCollar_eq_seam j b t 0 le_rfl zero_lt_one).symm

theorem seamMap_local (j : Fin E.toTorus.pairing.count) (b : Bool) {q : Torus × ℝ}
    (hq : |q.2| < 1) :
    IsLocalDiffeomorphAt signedCollarModel (𝓡 3) ∞ (E.seamMap j b) q := by
  have hmem : E.seamCoord j b q ∈ (E.toTorus.seam j).source := by
    rw [E.toTorus.seam_source, seamCoord_apply]
    have h1 := abs_lt.mp hq
    cases b <;> simp only [sideHeight, neg_neg, id] <;> constructor <;> linarith
  exact ((E.seamCoord j b).isLocalDiffeomorph q).comp _ _
    ((E.toTorus.seam j).isLocalDiffeomorphAt _ _ ∞ hmem)

theorem seamMap_inj (j : Fin E.toTorus.pairing.count) (b : Bool) {t t' : Torus}
    (h : E.seamMap j b (t, 0) = E.seamMap j b (t', 0)) : t = t' := by
  have hmem : ∀ x : Torus, E.seamCoord j b (x, 0) ∈ (E.toTorus.seam j).source := by
    intro x
    rw [E.toTorus.seam_source, seamCoord_apply, neg_zero]
    change -1 < sideHeight b 0 ∧ sideHeight b 0 < 1
    cases b <;> simp [sideHeight]
  have := (E.toTorus.seam j).toPartialEquiv.injOn (hmem t) (hmem t') h
  exact congrArg Prod.fst ((E.seamCoord j b).injective this)

theorem standardPort_seamPiece (h : E.IsSplitSeam j b) (l : Fin 1) :
    E.standardPort (E.seamPiece j b) h.1 l = ⟨E.seamSide j b, E.sidePiece_seamSide j b⟩ := by
  have hs : Subsingleton (E.toTorus.OwnedSide (E.seamPiece j b)) :=
    Fintype.card_le_one_iff_subsingleton.mp (E.card_ownedSide_seamPiece h).le
  exact Subsingleton.elim _ _

theorem standardPort_hostSide (h : E.IsSplitSeam j b) :
    E.standardPort (E.hostPiece j b) h.2.1 (E.hostSide h) =
      ⟨E.seamSide j !b, E.sidePiece_seamSide j !b⟩ :=
  Equiv.apply_symm_apply _ _

theorem seamMap_neg (h : E.IsSplitSeam j b) (t : Torus) {r : ℝ}
    (hr : -min ((E.splitData h).δ / 2) (1 / 2) < r) (hr0 : r < 0) :
    E.seamMap j b (t, r) = E.solidMap h ((3 + 3 * r / 2 : ℝ) • (t.1 : ℂ), t.2) := by
  have hδ := (E.splitData h).hδ
  have hm1 := min_le_left ((E.splitData h).δ / 2) (1 / 2)
  have hm2 := min_le_right ((E.splitData h).δ / 2) (1 / 2)
  have hs0 : 0 ≤ -r := by linarith
  have hs1 : -r < 1 := by linarith
  rw [seamMap, seamCoord_apply, ← E.cutMap_sideCollar_eq_seam j b t (-r) hs0 hs1]
  have hp : (t, halfPoint (-r) hs0) ∈ halfCollarSource := hs1
  have e1 := TorusPresentation.pieceCollar_apply E.toTorus (E.seamPiece j b)
    ⟨E.seamSide j b, E.sidePiece_seamSide j b⟩ hp
  have e2 := (E.splitData h).hV 0 (t, halfPoint (-r) hs0) hp (by
    change -r < (E.splitData h).δ
    linarith)
  rw [E.standardPort_seamPiece h] at e2
  rw [← e1, e2]
  change E.toTorus.cutMap ((E.splitData h).ΘV ((discPlanarBase.{u} 1).collar 0
    (t.1, halfPoint (-r) hs0), t.2) : E.toTorus.cutCarrier.Carrier) =
    E.toTorus.cutMap ((E.splitData h).ΘV (clampDisc ((3 + 3 * r / 2 : ℝ) • (t.1 : ℂ)), t.2) :
      E.toTorus.cutCarrier.Carrier)
  rw [discCollar_eq hs0 hs1]
  congr 4
  ring_nf

theorem seamMap_pos (h : E.IsSplitSeam j b) (hlin : E.IsLinearSeam j) (t : Torus) {r : ℝ}
    (hr0 : 0 < r) (hr : r < min ((E.splitData h).δ / 2) (1 / 2)) :
    E.seamMap j b (t, r) = E.hostMap h (planarCollarFormula 3 (E.hostSide h)
      (((t.2 ^ (E.crossUnit j b : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : Circle) : ℂ), r),
      t.1 ^ (E.crossUnit j b : Matrix (Fin 2) (Fin 2) ℤ) 1 0 *
        t.2 ^ (E.crossUnit j b : Matrix (Fin 2) (Fin 2) ℤ) 1 1) := by
  have hδ := (E.splitData h).hδ
  have hm1 := min_le_left ((E.splitData h).δ / 2) (1 / 2)
  have hm2 := min_le_right ((E.splitData h).δ / 2) (1 / 2)
  have hs1 : r < 1 := by linarith
  have hcross : E.crossMap j b t = (t.2 ^ (E.crossUnit j b : Matrix (Fin 2) (Fin 2) ℤ) 0 1,
      t.1 ^ (E.crossUnit j b : Matrix (Fin 2) (Fin 2) ℤ) 1 0 *
        t.2 ^ (E.crossUnit j b : Matrix (Fin 2) (Fin 2) ℤ) 1 1) := by
    rw [hlin.crossMap_apply b t]
    simp [linearTorusMap, crossUnit_zero E h]
  have e0 := E.cutMap_sideCollar_eq_seam j (!b) (E.crossMap j b t) r hr0.le hs1
  rw [leftOfSide_not_crossMap, sideHeight_not] at e0
  rw [seamMap, seamCoord_apply, sideHeight_neg, ← e0]
  have hp : (E.crossMap j b t, halfPoint r hr0.le) ∈ halfCollarSource := hs1
  have e1 := TorusPresentation.pieceCollar_apply E.toTorus (E.hostPiece j b)
    ⟨E.seamSide j !b, E.sidePiece_seamSide j !b⟩ hp
  have e2 := (E.splitData h).hH (E.hostSide h) (E.crossMap j b t, halfPoint r hr0.le) hp (by
    change r < (E.splitData h).δ
    linarith)
  rw [E.standardPort_hostSide h] at e2
  rw [← e1, e2]
  change E.toTorus.cutMap ((E.splitData h).ΘH (pantsPlanarBase.{u}.collar (E.hostSide h)
    ((E.crossMap j b t).1, halfPoint r hr0.le), (E.crossMap j b t).2) :
      E.toTorus.cutCarrier.Carrier) = _
  rw [pantsCollar_eq _ hr0.le hs1, hcross]
  rfl

theorem hostMap_local (h : E.IsSplitSeam j b) {q : ℂ × Circle}
    (hq : q.1 ∈ SplitTube.pantsInterior) :
    IsLocalDiffeomorphAt (𝓘(ℝ, ℂ).prod (𝓡 1)) (𝓡 3) ∞ (E.hostMap h) q :=
  E.toTorus.isLocalDiffeomorphAt_pieceChart _ _ _ _ (isLocalDiffeomorphAt_clampPants hq)

theorem solidMap_local (h : E.IsSplitSeam j b) {q : ℂ × Circle} (hq : ‖q.1‖ < 3) :
    IsLocalDiffeomorphAt (𝓘(ℝ, ℂ).prod (𝓡 1)) (𝓡 3) ∞ (E.solidMap h) q :=
  E.toTorus.isLocalDiffeomorphAt_pieceChart _ _ _ _ (isLocalDiffeomorphAt_clampDisc hq)

def splitCharts (h : E.IsSplitSeam j b) (hlin : E.IsLinearSeam j) :
    SplitTube.SplitCharts Q.Carrier where
  host := E.hostSide h
  e₀ := (E.crossUnit j b : Matrix (Fin 2) (Fin 2) ℤ) 0 1
  e₁ := (E.crossUnit j b : Matrix (Fin 2) (Fin 2) ℤ) 1 0
  d := (E.crossUnit j b : Matrix (Fin 2) (Fin 2) ℤ) 1 1
  he₀ := (units_entries_of_zero _ (crossUnit_zero E h)).2
  he₁ := (units_entries_of_zero _ (crossUnit_zero E h)).1
  δ := min ((E.splitData h).δ / 2) (1 / 2)
  hδ := lt_min (half_pos (E.splitData h).hδ) (by norm_num)
  hδ1 := min_le_right _ _
  solid := E.solidMap h
  hostMap := E.hostMap h
  seam := E.seamMap j b
  solid_local q hq := E.solidMap_local h hq
  host_local q hq := E.hostMap_local h hq
  seam_local q hq := E.seamMap_local j b (lt_of_lt_of_le hq ((min_le_right _ _).trans
    (by norm_num)))
  solid_inj q q' hq hq' heq := by
    refine E.toTorus.pieceChart_injOn _ _ _ _ (isLocalDiffeomorphAt_clampDisc hq) ?_ heq
    intro he
    have h1 := clampDisc_val.{u} hq.le
    have h2 := clampDisc_val.{u} hq'.le
    have := congrArg (fun x : (discPlanarBase.{u} 1).surface.Carrier => (x : discSet.{u}).val) he
    change (clampDisc.{u} q.1 : discSet.{u}).val = (clampDisc.{u} q'.1 : discSet.{u}).val at this
    rw [h1, h2] at this
    exact congrArg ULift.down this
  host_inj q q' hq hq' heq := by
    refine E.toTorus.pieceChart_injOn _ _ _ _ (isLocalDiffeomorphAt_clampPants hq) ?_ heq
    intro he
    have h1 := clampPants_val.{u} (SplitTube.pantsInterior_subset hq)
    have h2 := clampPants_val.{u} (SplitTube.pantsInterior_subset hq')
    have := congrArg (fun x : pantsPlanarBase.{u}.surface.Carrier =>
      (x : planarSet.{u} 3).val) he
    change (clampPants.{u} q.1 : planarSet.{u} 3).val =
      (clampPants.{u} q'.1 : planarSet.{u} 3).val at this
    rw [h1, h2] at this
    exact congrArg ULift.down this
  seam_inj t t' := E.seamMap_inj j b
  solid_ne_host q q' hq _ :=
    E.toTorus.pieceChart_ne _ _ _ _ (E.seamPiece_ne_hostPiece h) _ _ _
      (isLocalDiffeomorphAt_clampDisc hq)
  seam_ne_solid t q hq := by
    rw [E.seamMap_zero]
    exact E.toTorus.cutMap_ne_pieceChart _ _ _ _
      (E.toTorus.sideCollar_zero_mem _ t).1 (isLocalDiffeomorphAt_clampDisc hq)
  seam_ne_host t q hq := by
    rw [E.seamMap_zero]
    exact E.toTorus.cutMap_ne_pieceChart _ _ _ _
      (E.toTorus.sideCollar_zero_mem _ t).1 (isLocalDiffeomorphAt_clampPants hq)
  seam_neg t r hr hr0 := E.seamMap_neg h t hr hr0
  seam_pos t r hr0 hr := E.seamMap_pos h hlin t hr0 hr

end Instance

variable {Q : ConnectedClosedOrientedManifold.{u} 3}

def splitSeamTube (E : ElementaryPresentation (NoCuts.carrier Q)) (j : Fin E.toTorus.pairing.count)
    (b : Bool) (h : E.IsSplitSeam j b) (hlin : E.IsLinearSeam j) :
    SphericalTubeSystem Q.toClosedOrientedManifold :=
  SplitTube.SplitCharts.tubeSystem (Q := Q.toClosedOrientedManifold) (E.splitCharts h hlin)

def splitSeamSphere (E : ElementaryPresentation (NoCuts.carrier Q))
    (j : Fin E.toTorus.pairing.count) (b : Bool) (h : E.IsSplitSeam j b)
    (hlin : E.IsLinearSeam j) : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → Q.Carrier :=
  (E.splitCharts h hlin).sphere

theorem splitSeamSphere_isSmoothEmbedding (E : ElementaryPresentation (NoCuts.carrier Q))
    (j : Fin E.toTorus.pairing.count) (b : Bool) (h : E.IsSplitSeam j b)
    (hlin : E.IsLinearSeam j) :
    Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ (E.splitSeamSphere j b h hlin) :=
  (E.splitCharts h hlin).isSmoothEmbedding_sphere

theorem tubeMiddleSphere_splitSeamTube (E : ElementaryPresentation (NoCuts.carrier Q))
    (j : Fin E.toTorus.pairing.count) (b : Bool) (h : E.IsSplitSeam j b)
    (hlin : E.IsLinearSeam j) :
    tubeMiddleSphere (E.splitSeamTube j b h hlin) () = E.splitSeamSphere j b h hlin :=
  rfl

end ElementaryPresentation

end GC.Seifert
