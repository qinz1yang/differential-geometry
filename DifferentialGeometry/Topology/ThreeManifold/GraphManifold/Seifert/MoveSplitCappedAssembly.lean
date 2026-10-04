import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MoveSplitCappedSide
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MoveSplitCappedPieces

/-!
# Assembly of the capped sides of the split sphere

Lane N2c, tier 2 (assembly). Let `j` be a split seam on side `b` of an elementary presentation
`E` of a closed `Q`, with solid torus `V`, host `H`, and let `K` be a spherical capping of `Q`
along a tube system avoiding the pieces other than `V` and `H`. Given the two capped solid tori of
`SideData` (`Seifert/MoveSplitCappedSide.lean`), `cappedSystem` is a piece system of the capped
manifold: the old pieces other than `V` and `H`, over their planar bases shrunk by `δ₂` and read
through `coreMap K`, and the two solid tori; the seams are the old seams other than `j`, read
through `coreMap K` at height `δ₂ s` and through the holonomy of a solid torus on the sides that
were ports of `H` (`CappedConditions` collects the hypotheses: the old pieces and the shrunk seams
lie in the interior of the core, the tube system has one tube). The sides of `H` other than `j`
become the ports of the two solid tori (`cappedSide`).
-/

set_option autoImplicit false

noncomputable section
open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

namespace GC.Seifert

universe u

namespace TorusPresentation

variable {W : CompactCarrier.{u}} (T : TorusPresentation W)

theorem exists_seam_of_mem_left {k : Fin T.pairing.count} {x : T.cutCarrier.Carrier}
    (hx : x ∈ T.pairing.gluing.left k) : ∃ τ, T.cutMap x = T.seam k (τ, 0) :=
  ⟨(T.pairing.leftParam k).symm ⟨x, hx⟩, by
    rw [T.seam_zero, Homeomorph.apply_symm_apply]
    rfl⟩

theorem exists_seam_of_mem_right {k : Fin T.pairing.count} {x : T.cutCarrier.Carrier}
    (hx : x ∈ T.pairing.gluing.right k) : ∃ τ, T.cutMap x = T.seam k (τ, 0) :=
  ⟨(T.pairing.matching k).symm ((T.pairing.rightParam k).symm ⟨x, hx⟩), by
    rw [T.seam_zero, T.quotientMap_leftParam_eq_rightParam_matching, Diffeomorph.apply_symm_apply,
      Homeomorph.apply_symm_apply]
    rfl⟩

theorem exists_seam_of_cutMap_eq {x y : T.cutCarrier.Carrier} {k k' : Fin T.components.count}
    (hx : x ∈ T.components.piece k) (hy : y ∈ T.components.piece k') (hkk : k ≠ k')
    (h : T.cutMap x = T.cutMap y) :
    ∃ d τ, T.cutMap x = T.seam d (τ, 0) ∧
      ((T.leftPiece d = k ∧ T.rightPiece d = k') ∨ (T.leftPiece d = k' ∧ T.rightPiece d = k)) := by
  rcases T.cutMap_eq_cases h with rfl | ⟨d, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
  · exact absurd (T.eq_of_mem_piece' hx hy) hkk
  · obtain ⟨τ, hτ⟩ := T.exists_seam_of_mem_left h1
    exact ⟨d, τ, hτ, Or.inl ⟨T.eq_of_mem_piece' (T.left_owned d h1) hx,
      T.eq_of_mem_piece' (T.right_owned d h2) hy⟩⟩
  · obtain ⟨τ, hτ⟩ := T.exists_seam_of_mem_right h1
    exact ⟨d, τ, hτ, Or.inr ⟨T.eq_of_mem_piece' (T.left_owned d h2) hy,
      T.eq_of_mem_piece' (T.right_owned d h1) hx⟩⟩

theorem exists_seam_of_cutMap_eq_of_ne {x y : T.cutCarrier.Carrier} (hxy : x ≠ y)
    (h : T.cutMap x = T.cutMap y) :
    ∃ d τ, T.cutMap x = T.seam d (τ, 0) ∧
      (x ∈ T.pairing.gluing.left d ∨ x ∈ T.pairing.gluing.right d) := by
  rcases T.cutMap_eq_cases h with he | ⟨d, ⟨h1, -⟩ | ⟨h1, -⟩⟩
  · exact absurd he hxy
  · obtain ⟨τ, hτ⟩ := T.exists_seam_of_mem_left h1
    exact ⟨d, τ, hτ, Or.inl h1⟩
  · obtain ⟨τ, hτ⟩ := T.exists_seam_of_mem_right h1
    exact ⟨d, τ, hτ, Or.inr h1⟩

end TorusPresentation

namespace ElementaryPresentation

section Collars

variable {W : CompactCarrier.{u}} (E : ElementaryPresentation W)

theorem pieceMap_shrink_collar {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (k : Fin E.toTorus.components.count) (l : Fin (E.kind k)) (u v : Circle) (s : ℝ)
    (hs : 0 ≤ s) :
    E.pieceMap k (((E.piece k).base.shrink hδ hδ1).collar l (u, halfPoint s hs), v) =
      E.pieceMap k ((E.piece k).base.collar l (u, halfPoint (δ * s) (mul_nonneg hδ.le hs)), v) := by
  change E.pieceMap k (shrinkHalfCollar hδ ((E.piece k).base.collar l) (u, halfPoint s hs), v) = _
  rw [shrinkHalfCollar_apply, halfSpaceScale_halfPoint]

end Collars

variable {Q : ConnectedClosedOrientedManifold.{u} 3} (E : ElementaryPresentation (NoCuts.carrier Q))
  {j : Fin E.toTorus.pairing.count} {b : Bool} (h : E.IsSplitSeam j b)

theorem cutMap_sideCollar_hostPort (l : Fin 3) (τ : Torus) {r : ℝ} (hr : 0 ≤ r)
    (hrδ : r < (E.splitData h).δ) (hr1 : r < 1) :
    E.toTorus.cutMap (E.toTorus.sideCollar (E.standardPort (E.hostPiece j b) h.2.1 l).val
      (τ, halfPoint r hr)) =
      E.hostMap h (planarCollarFormula 3 l ((τ.1 : ℂ), r), τ.2) := by
  have hp : (τ, halfPoint r hr) ∈ halfCollarSource := hr1
  have e1 := TorusPresentation.pieceCollar_apply E.toTorus (E.hostPiece j b)
    (E.standardPort (E.hostPiece j b) h.2.1 l) hp
  have e2 := (E.splitData h).hH l (τ, halfPoint r hr) hp hrδ
  rw [← e1, e2]
  change E.toTorus.cutMap ((E.splitData h).ΘH (pantsPlanarBase.{u}.collar l
    (τ.1, halfPoint r hr), τ.2) : E.toTorus.cutCarrier.Carrier) = _
  rw [pantsCollar_eq _ hr hr1]
  rfl

include h in
theorem seamPiece_ne_seamPiece_of_ne {c : Fin E.toTorus.pairing.count} (hc : c ≠ j) (β : Bool) :
    E.seamPiece c β ≠ E.seamPiece j b := fun he =>
  hc (E.eq_of_seamPiece_eq_of_isSplitSeam h he).1

theorem hostSide_ne_of_ne {c : Fin E.toTorus.pairing.count} (hc : c ≠ j) (β : Bool)
    (hH : E.seamPiece c β = E.hostPiece j b) :
    (E.standardPort (E.hostPiece j b) h.2.1).symm
      ⟨E.seamSide c β, (E.sidePiece_seamSide c β).trans hH⟩ ≠ E.hostSide h := by
  intro he
  have he' := congrArg Subtype.val ((E.standardPort (E.hostPiece j b) h.2.1).symm.injective
    (he.trans rfl))
  exact hc ((E.seamSide_eq_seamSide_iff).mp he').1

section Capped

variable {T : SphericalTubeSystem Q.toClosedOrientedManifold} {N : ClosedOrientedManifold.{u} 3}
  (K : SphericalCapping Q.toClosedOrientedManifold N T) (a : T.Index) {δ₂ : ℝ}

structure CappedConditions (δ₂ : ℝ) : Prop where
  pos : 0 < δ₂
  le_one : δ₂ ≤ 1
  lt_split : δ₂ < (E.splitData h).δ
  index : ∀ a' : T.Index, a' = a
  piece : ∀ k, k ≠ E.seamPiece j b → k ≠ E.hostPiece j b → ∀ y ∈ E.toTorus.components.piece k,
    E.toTorus.cutMap y ∈ T.core ∧ ∀ b' z, T.boundarySphere b' z ≠ E.toTorus.cutMap y
  seam : ∀ c, c ≠ j → ∀ τ s, |s| < δ₂ →
    E.toTorus.seam c (τ, s) ∈ T.core ∧ ∀ b' z, T.boundarySphere b' z ≠ E.toTorus.seam c (τ, s)

variable (j b) in
abbrev CappedPiece :=
  {k : Fin E.toTorus.components.count // k ≠ E.seamPiece j b ∧ k ≠ E.hostPiece j b} ⊕ Bool

variable (j) in
abbrev CappedSeam := {c : Fin E.toTorus.pairing.count // c ≠ j}

variable (j b) in
def cappedKind : E.CappedPiece j b → ℕ
  | .inl k => E.kind k.1
  | .inr _ => 1

variable {E h K a}

def cappedBase (hC : E.CappedConditions h a δ₂) :
    ∀ i : E.CappedPiece j b, PlanarBase.{u} (E.cappedKind j b i)
  | .inl k => (E.piece k.1).base.shrink hC.pos hC.le_one
  | .inr _ => discPlanarBase.{u} 1

def cappedMap (D : E.SideData h K a δ₂) (hC : E.CappedConditions h a δ₂) :
    ∀ i : E.CappedPiece j b, (cappedBase hC i).surface.Carrier × Circle → N.Carrier
  | .inl k => fun q => SplitTube.coreMap K (E.pieceMap k.1 q)
  | .inr t => D.solid t

namespace SideData

variable (D : E.SideData h K a δ₂)

def solidOf (l : Fin 3) : Bool := decide (l = D.port true)

theorem port_solidOf {l : Fin 3} (hl : l ≠ E.hostSide h) : D.port (D.solidOf l) = l := by
  unfold solidOf
  by_cases ht : l = D.port true
  · rw [decide_eq_true ht]
    exact ht.symm
  · rw [decide_eq_false ht]
    have h1 : (D.port false).val ≠ (E.hostSide h).val := fun e => D.port_ne false (Fin.ext e)
    have h2 : (D.port true).val ≠ (E.hostSide h).val := fun e => D.port_ne true (Fin.ext e)
    have h3 : (D.port false).val ≠ (D.port true).val := fun e => D.port_false_ne_true (Fin.ext e)
    have h4 : l.val ≠ (E.hostSide h).val := fun e => hl (Fin.ext e)
    have h5 : l.val ≠ (D.port true).val := fun e => ht (Fin.ext e)
    have := (D.port false).isLt
    have := (D.port true).isLt
    have := (E.hostSide h).isLt
    have := l.isLt
    apply Fin.ext
    omega

theorem solidOf_port : ∀ t, D.solidOf (D.port t) = t
  | true => decide_eq_true rfl
  | false => decide_eq_false D.port_false_ne_true

end SideData

def hostPortOf {c : Fin E.toTorus.pairing.count} {β : Bool}
    (hH : E.seamPiece c β = E.hostPiece j b) : Fin 3 :=
  (E.standardPort (E.hostPiece j b) h.2.1).symm
    ⟨E.seamSide c β, (E.sidePiece_seamSide c β).trans hH⟩

theorem standardPort_hostPortOf {c : Fin E.toTorus.pairing.count} {β : Bool}
    (hH : E.seamPiece c β = E.hostPiece j b) :
    (E.standardPort (E.hostPiece j b) h.2.1 (hostPortOf (h := h) hH)).val = E.seamSide c β := by
  unfold hostPortOf
  rw [Equiv.apply_symm_apply]

open Classical in
def cappedSide (D : E.SideData h K a δ₂) (c : E.CappedSeam j)
    (β : Bool) : Σ i : E.CappedPiece j b, Fin (E.cappedKind j b i) :=
  if hH : E.seamPiece c.1 β = E.hostPiece j b then
    ⟨.inr (D.solidOf (hostPortOf (h := h) hH)), (0 : Fin 1)⟩
  else
    ⟨.inl ⟨E.seamPiece c.1 β, E.seamPiece_ne_seamPiece_of_ne h c.2 β, hH⟩,
      (E.piece (E.seamPiece c.1 β)).port.symm ⟨E.seamSide c.1 β, E.sidePiece_seamSide c.1 β⟩⟩

open Classical in
def sideTwist (D : E.SideData h K a δ₂) (c : E.CappedSeam j) (β : Bool) :
    Torus ≃ₘ⟮torusModel, torusModel⟯ Torus :=
  if hH : E.seamPiece c.1 β = E.hostPiece j b then
    D.holonomy (D.solidOf (hostPortOf (h := h) hH))
  else Diffeomorph.refl torusModel Torus ∞

theorem cappedSide_of_host (D : E.SideData h K a δ₂) (c : E.CappedSeam j) {β : Bool}
    (hH : E.seamPiece c.1 β = E.hostPiece j b) :
    cappedSide D c β = ⟨.inr (D.solidOf (hostPortOf (h := h) hH)), (0 : Fin 1)⟩ := by
  classical
  unfold cappedSide
  rw [dite_eq_left hH]

theorem cappedSide_of_not_host (D : E.SideData h K a δ₂) (c : E.CappedSeam j) {β : Bool}
    (hH : ¬ E.seamPiece c.1 β = E.hostPiece j b) :
    cappedSide D c β =
      ⟨.inl ⟨E.seamPiece c.1 β, E.seamPiece_ne_seamPiece_of_ne h c.2 β, hH⟩,
        (E.piece (E.seamPiece c.1 β)).port.symm
          ⟨E.seamSide c.1 β, E.sidePiece_seamSide c.1 β⟩⟩ := by
  classical
  unfold cappedSide
  rw [dite_eq_right hH]

theorem sideTwist_of_host (D : E.SideData h K a δ₂) (c : E.CappedSeam j) {β : Bool}
    (hH : E.seamPiece c.1 β = E.hostPiece j b) :
    sideTwist D c β = D.holonomy (D.solidOf (hostPortOf (h := h) hH)) := by
  classical
  unfold sideTwist
  rw [dite_eq_left hH]

theorem sideTwist_of_not_host (D : E.SideData h K a δ₂) (c : E.CappedSeam j) {β : Bool}
    (hH : ¬ E.seamPiece c.1 β = E.hostPiece j b) :
    sideTwist D c β = Diffeomorph.refl torusModel Torus ∞ := by
  classical
  unfold sideTwist
  rw [dite_eq_right hH]

def cappedCollarPoint (D : E.SideData h K a δ₂) (hC : E.CappedConditions h a δ₂) (u : Circle)
    (r : EuclideanHalfSpace 1) (v : Circle)
    (x : Σ i : E.CappedPiece j b, Fin (E.cappedKind j b i)) :
    N.Carrier :=
  cappedMap D hC x.1 ((cappedBase hC x.1).collar x.2 (u, r), v)

theorem cappedCollarPoint_side (D : E.SideData h K a δ₂) (hC : E.CappedConditions h a δ₂)
    (c : E.CappedSeam j) (β : Bool) (τ : Torus) {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    cappedCollarPoint D hC τ.1 (halfPoint r hr) τ.2 (cappedSide D c β) =
      SplitTube.coreMap K (E.toTorus.cutMap (E.toTorus.sideCollar (E.seamSide c.1 β)
        (sideTwist D c β τ, halfPoint (δ₂ * r) (mul_nonneg hC.pos.le hr)))) := by
  have hδr : δ₂ * r < (E.splitData h).δ := by
    have := hC.lt_split
    have := hC.pos
    nlinarith
  have hδr1 : δ₂ * r < 1 := by
    have := hC.le_one
    have := hC.pos
    nlinarith
  by_cases hH : E.seamPiece c.1 β = E.hostPiece j b
  · rw [cappedSide_of_host D c hH, sideTwist_of_host D c hH]
    change D.solid (D.solidOf (hostPortOf (h := h) hH))
      ((discPlanarBase.{u} 1).collar 0 (τ.1, halfPoint r hr), τ.2) = _
    rw [D.collar _ τ r hr hr1,
      D.port_solidOf (l := hostPortOf (h := h) hH) (E.hostSide_ne_of_ne h c.2 β hH),
      ← E.cutMap_sideCollar_hostPort h _ _ (mul_nonneg hC.pos.le hr) hδr hδr1,
      standardPort_hostPortOf]
  · rw [cappedSide_of_not_host D c hH, sideTwist_of_not_host D c hH]
    change SplitTube.coreMap K (E.pieceMap (E.seamPiece c.1 β)
      (((E.piece (E.seamPiece c.1 β)).base.shrink hC.pos hC.le_one).collar
        ((E.piece (E.seamPiece c.1 β)).port.symm ⟨E.seamSide c.1 β, E.sidePiece_seamSide c.1 β⟩)
        (τ.1, halfPoint r hr), τ.2)) = _
    rw [E.pieceMap_shrink_collar hC.pos hC.le_one]
    congr 1
    cases β
    · exact E.pieceMap_collar (E.seamSide c.1 false) (p := (τ, halfPoint (δ₂ * r) _)) hδr1
    · exact E.pieceMap_collar (E.seamSide c.1 true) (p := (τ, halfPoint (δ₂ * r) _)) hδr1

theorem seam_eq_sideCollar_true (c : Fin E.toTorus.pairing.count) (τ : Torus) {s : ℝ}
    (hs : 0 ≤ s) (hs1 : s < 1) :
    E.toTorus.seam c (τ, -s) =
      E.toTorus.cutMap (E.toTorus.sideCollar (E.seamSide c true) (τ, halfPoint s hs)) :=
  (E.cutMap_sideCollar_eq_seam c true τ s hs hs1).symm

theorem seam_eq_sideCollar_false (c : Fin E.toTorus.pairing.count) (τ : Torus) {s : ℝ}
    (hs : 0 ≤ s) (hs1 : s < 1) :
    E.toTorus.seam c (τ, s) = E.toTorus.cutMap (E.toTorus.sideCollar (E.seamSide c false)
      (E.toTorus.pairing.matching c τ, halfPoint s hs)) := by
  rw [E.cutMap_sideCollar_eq_seam c false _ s hs hs1]
  simp [leftOfSide, sideHeight]

def cappedSeamFun (D : E.SideData h K a δ₂) (c : E.CappedSeam j) (p : Torus × ℝ) : N.Carrier :=
  SplitTube.coreMap K (E.toTorus.seam c.1 (sideTwist D c true p.1, δ₂ * p.2))

theorem seam_core (D : E.SideData h K a δ₂) (hC : E.CappedConditions h a δ₂)
    (c : E.CappedSeam j) {p : Torus × ℝ} (hp : p ∈ signedCollarSource) :
    (sideTwist D c true p.1, δ₂ * p.2) ∈ (E.toTorus.seam c.1).source ∧
      E.toTorus.seam c.1 (sideTwist D c true p.1, δ₂ * p.2) ∈ T.core ∧
        ∀ b' z, T.boundarySphere b' z ≠ E.toTorus.seam c.1 (sideTwist D c true p.1, δ₂ * p.2) := by
  have hp' : |p.2| < 1 := abs_lt.mpr ⟨hp.1, hp.2⟩
  have hδ := hC.pos
  have hlt : |δ₂ * p.2| < δ₂ := by
    rw [abs_mul, abs_of_pos hδ]
    nlinarith [abs_nonneg p.2]
  have hlt1 : |δ₂ * p.2| < 1 := lt_of_lt_of_le hlt hC.le_one
  refine ⟨?_, hC.seam c.1 c.2 _ _ hlt⟩
  rw [E.toTorus.seam_source]
  exact abs_lt.mp hlt1

theorem isLocalDiffeomorphOn_cappedSeamFun (D : E.SideData h K a δ₂)
    (hC : E.CappedConditions h a δ₂) (c : E.CappedSeam j) :
    IsLocalDiffeomorphOn signedCollarModel (𝓡 3) ∞ (cappedSeamFun D c) signedCollarSource := by
  intro x
  obtain ⟨hsrc, hcore, hne⟩ := seam_core D hC c x.2
  have hg := ((sideTwist D c true).prodCongr (realScale hC.pos)).isLocalDiffeomorph x.1
  have hs := (E.toTorus.seam c.1).isLocalDiffeomorphAt _ _ ∞ hsrc
  have hcm := SplitTube.isLocalDiffeomorphAt_coreMap K ⟨_, hcore⟩
    (SplitTube.isInteriorPoint_of_forall_ne K ⟨_, hcore⟩ hne)
  exact (hg.comp _ _ hs).comp _ _ hcm

theorem injOn_cappedSeamFun (D : E.SideData h K a δ₂) (hC : E.CappedConditions h a δ₂)
    (c : E.CappedSeam j) : InjOn (cappedSeamFun D c) signedCollarSource := by
  intro p hp p' hp' he
  obtain ⟨hsrc, hcore, -⟩ := seam_core D hC c hp
  obtain ⟨hsrc', hcore', -⟩ := seam_core D hC c hp'
  have h1 := SplitTube.coreMap_injOn K hcore hcore' he
  have h2 := (E.toTorus.seam c.1).toPartialEquiv.injOn hsrc hsrc' h1
  have h3 := ((sideTwist D c true).prodCongr (realScale hC.pos)).injective h2
  exact h3

theorem exists_cappedSeam (D : E.SideData h K a δ₂) (hC : E.CappedConditions h a δ₂)
    (c : E.CappedSeam j) :
    ∃ Φ : PartialDiffeomorph signedCollarModel (𝓡 3) (Torus × ℝ) N.Carrier ∞,
      Φ.toPartialEquiv.source = signedCollarSource ∧
        Φ.toPartialEquiv.target = cappedSeamFun D c '' signedCollarSource ∧
          Φ.toFun = cappedSeamFun D c :=
  (isLocalDiffeomorphOn_cappedSeamFun D hC c).exists_partialDiffeomorph_of_injOn
    signedCollarSource_isOpen ⟨((1 : Torus), 0), by constructor <;> norm_num⟩
    (injOn_cappedSeamFun D hC c)

def cappedSeam (D : E.SideData h K a δ₂) (hC : E.CappedConditions h a δ₂) (c : E.CappedSeam j) :
    PartialDiffeomorph signedCollarModel (𝓡 3) (Torus × ℝ) N.Carrier ∞ :=
  (exists_cappedSeam D hC c).choose

theorem cappedSeam_source (D : E.SideData h K a δ₂) (hC : E.CappedConditions h a δ₂)
    (c : E.CappedSeam j) : (cappedSeam D hC c).source = signedCollarSource :=
  (exists_cappedSeam D hC c).choose_spec.1

theorem cappedSeam_apply (D : E.SideData h K a δ₂) (hC : E.CappedConditions h a δ₂)
    (c : E.CappedSeam j) (p : Torus × ℝ) : cappedSeam D hC c p = cappedSeamFun D c p :=
  congrFun (exists_cappedSeam D hC c).choose_spec.2.2 p

def cappedMatching (D : E.SideData h K a δ₂) (c : E.CappedSeam j) :
    Torus ≃ₘ⟮torusModel, torusModel⟯ Torus :=
  ((sideTwist D c true).trans (E.toTorus.pairing.matching c.1)).trans (sideTwist D c false).symm

theorem cappedSeam_neg (D : E.SideData h K a δ₂) (hC : E.CappedConditions h a δ₂)
    (c : E.CappedSeam j) (τ : Torus) (s : ℝ) (hs : s ≤ 0) (h1 : -1 < s) :
    cappedSeam D hC c (τ, s) = cappedCollarPoint D hC τ.1 (halfPoint (-s) (neg_nonneg.2 hs)) τ.2
      (cappedSide D c true) := by
  rw [cappedCollarPoint_side D hC c true τ _ (by linarith), cappedSeam_apply]
  change SplitTube.coreMap K (E.toTorus.seam c.1 (sideTwist D c true τ, δ₂ * s)) = _
  have hδ := hC.pos
  have hδ1 := hC.le_one
  rw [show δ₂ * s = -(δ₂ * -s) by ring, E.seam_eq_sideCollar_true c.1 _ (by nlinarith)
    (by nlinarith)]

theorem cappedSeam_pos (D : E.SideData h K a δ₂) (hC : E.CappedConditions h a δ₂)
    (c : E.CappedSeam j) (τ : Torus) (s : ℝ) (hs : 0 ≤ s) (h1 : s < 1) :
    cappedSeam D hC c (τ, s) = cappedCollarPoint D hC (cappedMatching D c τ).1 (halfPoint s hs)
      (cappedMatching D c τ).2 (cappedSide D c false) := by
  rw [cappedCollarPoint_side D hC c false _ hs h1, cappedSeam_apply]
  change SplitTube.coreMap K (E.toTorus.seam c.1 (sideTwist D c true τ, δ₂ * s)) = _
  have hδ := hC.pos
  have hδ1 := hC.le_one
  rw [E.seam_eq_sideCollar_false c.1 _ (by nlinarith) (by nlinarith)]
  congr 4
  simp [cappedMatching]

theorem halfPoint_congr {s s' : ℝ} (hs : 0 ≤ s) (hs' : 0 ≤ s') (e : s = s') :
    halfPoint s hs = halfPoint s' hs' := by
  subst e
  rfl

theorem seamPiece_eq_or (β : Bool) :
    E.seamPiece j β = E.seamPiece j b ∨ E.seamPiece j β = E.hostPiece j b := by
  cases β <;> cases b <;> simp [hostPiece]

theorem ne_of_mem_block {c : Fin E.toTorus.pairing.count}
    {x : E.toTorus.cutCarrier.Carrier} {k₀ : Fin E.toTorus.components.count}
    (hk₀ : k₀ ≠ E.seamPiece j b ∧ k₀ ≠ E.hostPiece j b) (hx : x ∈ E.toTorus.components.piece k₀)
    (hb : x ∈ E.toTorus.pairing.gluing.left c ∨ x ∈ E.toTorus.pairing.gluing.right c) : c ≠ j := by
  rintro rfl
  rcases hb with hb | hb
  · have := E.toTorus.eq_of_mem_piece' (E.toTorus.left_owned c hb) hx
    rcases E.seamPiece_eq_or (j := c) (b := b) true with e | e
    · exact hk₀.1 (this.symm.trans e)
    · exact hk₀.2 (this.symm.trans e)
  · have := E.toTorus.eq_of_mem_piece' (E.toTorus.right_owned c hb) hx
    rcases E.seamPiece_eq_or (j := c) (b := b) false with e | e
    · exact hk₀.1 (this.symm.trans e)
    · exact hk₀.2 (this.symm.trans e)

theorem pieceMap_core (hC : E.CappedConditions h a δ₂)
    (k : {k : Fin E.toTorus.components.count // k ≠ E.seamPiece j b ∧ k ≠ E.hostPiece j b})
    (q : (E.piece k.1).base.surface.Carrier × Circle) :
    E.pieceMap k.1 q ∈ T.core ∧ ∀ b' z, T.boundarySphere b' z ≠ E.pieceMap k.1 q :=
  hC.piece k.1 k.2.1 k.2.2 _ ((E.piece k.1).trivialization q).2

theorem exists_cappedSeam_of_sideCollar (D : E.SideData h K a δ₂) (hC : E.CappedConditions h a δ₂)
    {c : Fin E.toTorus.pairing.count} (hc : c ≠ j) (β : Bool) (τ : Torus) :
    ∃ τ', SplitTube.coreMap K (E.toTorus.cutMap (E.toTorus.sideCollar (E.seamSide c β)
      (τ, halfZero))) = cappedSeam D hC ⟨c, hc⟩ (τ', 0) := by
  cases β
  · refine ⟨(sideTwist D ⟨c, hc⟩ true).symm ((E.toTorus.pairing.matching c).symm τ), ?_⟩
    rw [cappedSeam_apply]
    change _ = SplitTube.coreMap K (E.toTorus.seam c (sideTwist D ⟨c, hc⟩ true
      ((sideTwist D ⟨c, hc⟩ true).symm ((E.toTorus.pairing.matching c).symm τ)), δ₂ * 0))
    rw [Diffeomorph.apply_symm_apply, mul_zero,
      E.seam_eq_sideCollar_false c _ le_rfl one_pos, Diffeomorph.apply_symm_apply]
    rfl
  · refine ⟨(sideTwist D ⟨c, hc⟩ true).symm τ, ?_⟩
    rw [cappedSeam_apply]
    change _ = SplitTube.coreMap K (E.toTorus.seam c (sideTwist D ⟨c, hc⟩ true
      ((sideTwist D ⟨c, hc⟩ true).symm τ), δ₂ * 0))
    rw [Diffeomorph.apply_symm_apply, mul_zero, ← neg_zero,
      E.seam_eq_sideCollar_true c _ le_rfl one_pos]
    rfl

theorem exists_cappedSeam_of_solid_boundary (D : E.SideData h K a δ₂)
    (hC : E.CappedConditions h a δ₂) (t : Bool) (p : Torus) :
    ∃ c τ, D.solid t ((discPlanarBase.{u} 1).collar 0 (p.1, halfZero), p.2) =
      cappedSeam D hC c (τ, 0) := by
  have hδ := hC.pos
  have hlt : δ₂ * 0 < (E.splitData h).δ := by rw [mul_zero]; exact (E.splitData h).hδ
  rw [show halfZero = halfPoint 0 le_rfl from rfl, D.collar t p 0 le_rfl one_pos,
    ← E.cutMap_sideCollar_hostPort h _ _ (by rw [mul_zero]) hlt (by rw [mul_zero]; exact one_pos)]
  obtain ⟨c, β, hcβ⟩ := E.exists_seamSide_eq (E.standardPort (E.hostPiece j b) h.2.1 (D.port t)).val
  have hc : c ≠ j := by
    intro hcj
    rw [hcj] at hcβ
    have hH : E.seamPiece j β = E.hostPiece j b := by
      rw [← E.sidePiece_seamSide, ← hcβ]
      exact (E.standardPort (E.hostPiece j b) h.2.1 (D.port t)).2
    have hβ : β = !b := by
      by_contra hβ
      have hb' : β = b := by cases β <;> cases b <;> simp_all
      rw [hb'] at hH
      exact E.seamPiece_ne_hostPiece h hH
    rw [hβ] at hcβ
    have := (E.standardPort (E.hostPiece j b) h.2.1).injective (Subtype.ext
      (hcβ.trans (congrArg Subtype.val (E.standardPort_hostSide h)).symm))
    exact D.port_ne t this
  obtain ⟨τ, hτ⟩ := exists_cappedSeam_of_sideCollar D hC hc β (D.holonomy t p)
  refine ⟨⟨c, hc⟩, τ, ?_⟩
  rw [hcβ, halfPoint_congr _ le_rfl (mul_zero δ₂)]
  exact hτ

theorem seamPoint_of_pieceMap_eq_solid (D : E.SideData h K a δ₂) (hC : E.CappedConditions h a δ₂)
    (k : {k : Fin E.toTorus.components.count // k ≠ E.seamPiece j b ∧ k ≠ E.hostPiece j b})
    (q : (E.piece k.1).base.surface.Carrier × Circle) (t : Bool)
    (q' : (discPlanarBase.{u} 1).surface.Carrier × Circle)
    (he : SplitTube.coreMap K (E.pieceMap k.1 q) = D.solid t q') :
    ∃ c τ, SplitTube.coreMap K (E.pieceMap k.1 q) = cappedSeam D hC c (τ, 0) := by
  obtain ⟨hcore, hne⟩ := pieceMap_core hC k q
  rcases D.image t q' with ⟨w, hw⟩ | ⟨y, hy, hycore, hyq⟩
  · rw [hw, SplitTube.coreMap_of_mem K hcore] at he
    exact absurd he (SplitTube.coreInclusion_ne_cap_of_forall_ne K ⟨_, hcore⟩ hne _ w)
  · rw [hyq] at he
    have hcut := SplitTube.coreMap_injOn K hcore hycore he
    have hy' : ((E.piece k.1).trivialization q).val ≠ y := by
      intro hxy
      have hk := ((E.piece k.1).trivialization q).2
      rw [hxy] at hk
      rcases hy with hy | hy
      · exact k.2.1 (E.toTorus.eq_of_mem_piece' hk hy)
      · exact k.2.2 (E.toTorus.eq_of_mem_piece' hk hy)
    obtain ⟨d, τ, hτ, hb⟩ := E.toTorus.exists_seam_of_cutMap_eq_of_ne hy' hcut
    have hd : d ≠ j := ne_of_mem_block k.2 ((E.piece k.1).trivialization q).2 hb
    refine ⟨⟨d, hd⟩, (sideTwist D ⟨d, hd⟩ true).symm τ, ?_⟩
    rw [cappedSeam_apply]
    change SplitTube.coreMap K (E.toTorus.cutMap ((E.piece k.1).trivialization q).val) =
      SplitTube.coreMap K (E.toTorus.seam d (sideTwist D ⟨d, hd⟩ true
        ((sideTwist D ⟨d, hd⟩ true).symm τ), δ₂ * 0))
    rw [Diffeomorph.apply_symm_apply, mul_zero, hτ]

theorem standardPort_port_ne_seamSide (D : E.SideData h K a δ₂) (t β : Bool) :
    (E.standardPort (E.hostPiece j b) h.2.1 (D.port t)).val ≠ E.seamSide j β := by
  intro hcβ
  have hH : E.seamPiece j β = E.hostPiece j b := by
    rw [← E.sidePiece_seamSide, ← hcβ]
    exact (E.standardPort (E.hostPiece j b) h.2.1 (D.port t)).2
  have hβ : β = !b := by
    by_contra hβ
    have hb' : β = b := by cases β <;> cases b <;> simp_all
    rw [hb'] at hH
    exact E.seamPiece_ne_hostPiece h hH
  rw [hβ] at hcβ
  have := (E.standardPort (E.hostPiece j b) h.2.1).injective (Subtype.ext
    (hcβ.trans (congrArg Subtype.val (E.standardPort_hostSide h)).symm))
  exact D.port_ne t this

def recover (D : E.SideData h K a δ₂) :
    (Σ i : E.CappedPiece j b, Fin (E.cappedKind j b i)) → E.toTorus.Side
  | ⟨.inl k, l⟩ => ((E.piece k.1).port l).val
  | ⟨.inr t, _⟩ => (E.standardPort (E.hostPiece j b) h.2.1 (D.port t)).val

theorem recover_cappedSide (D : E.SideData h K a δ₂) (c : E.CappedSeam j) (β : Bool) :
    recover D (cappedSide D c β) = E.seamSide c.1 β := by
  by_cases hH : E.seamPiece c.1 β = E.hostPiece j b
  · rw [cappedSide_of_host D c hH]
    change (E.standardPort (E.hostPiece j b) h.2.1
      (D.port (D.solidOf (hostPortOf (h := h) hH)))).val = _
    rw [D.port_solidOf (l := hostPortOf (h := h) hH) (E.hostSide_ne_of_ne h c.2 β hH),
      standardPort_hostPortOf]
  · rw [cappedSide_of_not_host D c hH]
    change ((E.piece (E.seamPiece c.1 β)).port ((E.piece (E.seamPiece c.1 β)).port.symm
      ⟨E.seamSide c.1 β, E.sidePiece_seamSide c.1 β⟩)).val = _
    rw [Equiv.apply_symm_apply]

theorem recover_injective (D : E.SideData h K a δ₂) : Injective (recover D) := by
  rintro ⟨i, l⟩ ⟨i', l'⟩ he
  rcases i with k | t <;> rcases i' with k' | t'
  · change ((E.piece k.1).port l).val = ((E.piece k'.1).port l').val at he
    have hk : k = k' := Subtype.ext (((E.piece k.1).port l).2.symm.trans
      ((congrArg E.toTorus.sidePiece he).trans ((E.piece k'.1).port l').2))
    subst hk
    rw [(E.piece k.1).port.injective (Subtype.ext he)]
  · change ((E.piece k.1).port l).val =
      (E.standardPort (E.hostPiece j b) h.2.1 (D.port t')).val at he
    exact absurd (((E.piece k.1).port l).2.symm.trans ((congrArg E.toTorus.sidePiece he).trans
      (E.standardPort (E.hostPiece j b) h.2.1 (D.port t')).2)) k.2.2
  · change (E.standardPort (E.hostPiece j b) h.2.1 (D.port t)).val =
      ((E.piece k'.1).port l').val at he
    exact absurd (((E.piece k'.1).port l').2.symm.trans
      ((congrArg E.toTorus.sidePiece he).symm.trans
        (E.standardPort (E.hostPiece j b) h.2.1 (D.port t)).2)) k'.2.2
  · change (E.standardPort (E.hostPiece j b) h.2.1 (D.port t)).val =
      (E.standardPort (E.hostPiece j b) h.2.1 (D.port t')).val at he
    have ht := (E.standardPort (E.hostPiece j b) h.2.1).injective (Subtype.ext he)
    have htt : t = t' := by rw [← D.solidOf_port t, ht, D.solidOf_port]
    subst htt
    have hl : l = l' := Subsingleton.elim (α := Fin 1) _ _
    rw [hl]

theorem cappedSide_bijective (D : E.SideData h K a δ₂) :
    Bijective (uncurry (cappedSide D)) := by
  refine ⟨fun x y hxy => ?_, fun z => ?_⟩
  · obtain ⟨c, β⟩ := x
    obtain ⟨c', β'⟩ := y
    have he : E.seamSide c.1 β = E.seamSide c'.1 β' := by
      rw [← recover_cappedSide D, ← recover_cappedSide D]
      exact congrArg (recover D) hxy
    obtain ⟨h1, h2⟩ := E.seamSide_eq_seamSide_iff.mp he
    exact Prod.ext (Subtype.ext h1) h2
  · obtain ⟨c, β, hcβ⟩ := E.exists_seamSide_eq (recover D z)
    have hc : c ≠ j := by
      intro hcj
      rw [hcj] at hcβ
      obtain ⟨i, l⟩ := z
      rcases i with k | t
      · change ((E.piece k.1).port l).val = E.seamSide j β at hcβ
        have hk := ((E.piece k.1).port l).2.symm.trans ((congrArg E.toTorus.sidePiece hcβ).trans
          (E.sidePiece_seamSide j β))
        rcases E.seamPiece_eq_or (j := j) (b := b) β with e | e
        · exact k.2.1 (hk.trans e)
        · exact k.2.2 (hk.trans e)
      · exact standardPort_port_ne_seamSide D t β hcβ
    refine ⟨(⟨c, hc⟩, β), recover_injective D ?_⟩
    change recover D (cappedSide D ⟨c, hc⟩ β) = _
    rw [recover_cappedSide, ← hcβ]

theorem cappedMap_covers (D : E.SideData h K a δ₂) (hC : E.CappedConditions h a δ₂) :
    ⋃ i, range (cappedMap D hC i) = univ := by
  refine eq_univ_of_forall fun x => ?_
  have hx : x ∈ range K.coreInclusion ∪ ⋃ b', range (K.cap b') := K.exhaustive ▸ mem_univ x
  rcases hx with ⟨y, rfl⟩ | hx
  · have hy : y.val ∈ ⋃ k, range fun z : E.toTorus.components.piece k => E.toTorus.cutMap z.val :=
      E.toTorus.covers_cutMap ▸ mem_univ y.val
    obtain ⟨k, z, hz⟩ := mem_iUnion.mp hy
    have hz : E.toTorus.cutMap z.val = y.val := hz
    by_cases hk : k = E.seamPiece j b ∨ k = E.hostPiece j b
    · have hreg : E.InSplitRegion (j := j) (b := b) z.val := by
        rcases hk with rfl | rfl
        · exact Or.inl z.2
        · exact Or.inr z.2
      obtain ⟨t, q, hq⟩ := D.core_mem z.val hreg (by rw [hz]; exact y.2)
      refine mem_iUnion.mpr ⟨.inr t, q, ?_⟩
      change D.solid t q = _
      rw [hq, hz, SplitTube.coreMap_val]
    · push Not at hk
      obtain ⟨q, hq⟩ := (E.piece k).trivialization.surjective z
      have hq : (E.piece k).trivialization q = z := hq
      refine mem_iUnion.mpr ⟨.inl ⟨k, hk⟩, q, ?_⟩
      change SplitTube.coreMap K (E.toTorus.cutMap ((E.piece k).trivialization q).val) = _
      rw [hq, hz, SplitTube.coreMap_val]
  · obtain ⟨⟨a', t'⟩, w, rfl⟩ := mem_iUnion.mp hx
    obtain rfl := hC.index a'
    obtain ⟨q, hq⟩ := D.cap_mem t' w
    exact mem_iUnion.mpr ⟨.inr t', q, hq⟩

theorem isLocalDiffeomorphAt_coreMap_pieceMap (hC : E.CappedConditions h a δ₂)
    (k : {k : Fin E.toTorus.components.count // k ≠ E.seamPiece j b ∧ k ≠ E.hostPiece j b})
    (q : (E.piece k.1).base.surface.Carrier × Circle) :
    IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ (SplitTube.coreMap K) (E.pieceMap k.1 q) :=
  SplitTube.isLocalDiffeomorphAt_coreMap K ⟨_, (pieceMap_core hC k q).1⟩
    (SplitTube.isInteriorPoint_of_forall_ne K ⟨_, (pieceMap_core hC k q).1⟩
      (pieceMap_core hC k q).2)

theorem contMDiff_pieceMap (k : Fin E.toTorus.components.count) :
    ContMDiff ((SurfaceModel.model (E.piece k).base.surface.kind).prod (𝓡 1)) (𝓡 3) ∞
      (E.pieceMap k) :=
  E.toTorus.quotient_smooth.comp (contMDiff_subtype_val.comp (E.piece k).trivialization.contMDiff)

theorem cappedMap_smooth (D : E.SideData h K a δ₂) (hC : E.CappedConditions h a δ₂) :
    ∀ i : E.CappedPiece j b, ContMDiff ((SurfaceModel.model (cappedBase hC i).surface.kind).prod
      (𝓡 1)) (𝓡 3) ∞ (cappedMap D hC i)
  | .inl k => fun q => (isLocalDiffeomorphAt_coreMap_pieceMap (K := K) hC k q).contMDiffAt.comp q
      ((E.contMDiff_pieceMap k.1) q)
  | .inr t => D.smooth t

theorem bijective_mfderiv_coreMap_pieceMap (hC : E.CappedConditions h a δ₂)
    (k : {k : Fin E.toTorus.components.count // k ≠ E.seamPiece j b ∧ k ≠ E.hostPiece j b})
    (q : (E.piece k.1).base.surface.Carrier × Circle) :
    Bijective (mfderiv ((SurfaceModel.model (E.piece k.1).base.surface.kind).prod (𝓡 1)) (𝓡 3)
      (SplitTube.coreMap K ∘ E.pieceMap k.1) q) := by
  have hcm := isLocalDiffeomorphAt_coreMap_pieceMap (K := K) hC k q
  rw [mfderiv_comp q (hcm.mdifferentiableAt (by simp))
    ((E.contMDiff_pieceMap k.1).mdifferentiableAt (by simp)), ContinuousLinearMap.coe_comp]
  exact (bijective_mfderiv_of_isLocalDiffeomorphAt hcm).comp (E.bijective_mfderiv_pieceMap k.1 q)

theorem cappedMap_mfderiv_bijective (D : E.SideData h K a δ₂) (hC : E.CappedConditions h a δ₂) :
    ∀ (i : E.CappedPiece j b) (q : (cappedBase hC i).surface.Carrier × Circle),
      Bijective (mfderiv ((SurfaceModel.model (cappedBase hC i).surface.kind).prod (𝓡 1)) (𝓡 3)
        (cappedMap D hC i) q)
  | .inl k, q => bijective_mfderiv_coreMap_pieceMap hC k q
  | .inr t, q => D.mfderiv_bijective t q

theorem cappedMap_overlap (D : E.SideData h K a δ₂) (hC : E.CappedConditions h a δ₂) :
    ∀ (i i' : E.CappedPiece j b) (q : (cappedBase hC i).surface.Carrier × Circle)
      (q' : (cappedBase hC i').surface.Carrier × Circle),
      cappedMap D hC i q = cappedMap D hC i' q' →
      (⟨i, q⟩ : Σ i, (cappedBase hC i).surface.Carrier × Circle) = ⟨i', q'⟩ ∨
        ∃ c t, cappedMap D hC i q = cappedSeam D hC c (t, 0)
  | .inl k, .inl k', q, q', he => by
    change SplitTube.coreMap K (E.pieceMap k.1 q) = SplitTube.coreMap K (E.pieceMap k'.1 q') at he
    have hcut := SplitTube.coreMap_injOn K (pieceMap_core hC k q).1 (pieceMap_core hC k' q').1 he
    by_cases hxy : ((E.piece k.1).trivialization q).val = ((E.piece k'.1).trivialization q').val
    · left
      have hk : k = k' := Subtype.ext (E.toTorus.eq_of_mem_piece'
        ((E.piece k.1).trivialization q).2 (hxy ▸ ((E.piece k'.1).trivialization q').2))
      subst hk
      have hq : q = q' := (E.piece k.1).trivialization.injective (Subtype.ext hxy)
      subst hq
      rfl
    · right
      obtain ⟨d, τ, hτ, hb⟩ := E.toTorus.exists_seam_of_cutMap_eq_of_ne hxy hcut
      have hd : d ≠ j := ne_of_mem_block k.2 ((E.piece k.1).trivialization q).2 hb
      refine ⟨⟨d, hd⟩, (sideTwist D ⟨d, hd⟩ true).symm τ, ?_⟩
      rw [cappedSeam_apply]
      change SplitTube.coreMap K (E.toTorus.cutMap ((E.piece k.1).trivialization q).val) =
        SplitTube.coreMap K (E.toTorus.seam d (sideTwist D ⟨d, hd⟩ true
          ((sideTwist D ⟨d, hd⟩ true).symm τ), δ₂ * 0))
      rw [Diffeomorph.apply_symm_apply, mul_zero, hτ]
  | .inl k, .inr t, q, q', he => Or.inr (seamPoint_of_pieceMap_eq_solid D hC k q t q' he)
  | .inr t, .inl k, q, q', he => by
    right
    obtain ⟨c, τ, hc⟩ := seamPoint_of_pieceMap_eq_solid D hC k q' t q he.symm
    exact ⟨c, τ, he.trans hc⟩
  | .inr t, .inr t', q, q', he => by
    by_cases htt : t = t'
    · subst htt
      left
      rw [D.injective t he]
    · right
      have hfb : (t = false ∧ t' = true) ∨ (t = true ∧ t' = false) := by
        cases t <;> cases t' <;> simp_all
      rcases hfb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · obtain ⟨⟨p, rfl⟩, -⟩ := D.boundary_of_eq q q' he
        exact exists_cappedSeam_of_solid_boundary D hC false p
      · obtain ⟨-, ⟨p, rfl⟩⟩ := D.boundary_of_eq q' q he.symm
        exact exists_cappedSeam_of_solid_boundary D hC true p

def cappedSystem (D : E.SideData h K a δ₂) (hC : E.CappedConditions h a δ₂) :
    ClosedPieceSystem.{u} N.Carrier where
  Piece := E.CappedPiece j b
  Seam := E.CappedSeam j
  nonempty := ⟨.inr true⟩
  kind := E.cappedKind j b
  kind_mem
    | .inl k => E.kind_mem k.1
    | .inr _ => by simp [cappedKind]
  base := cappedBase hC
  map := cappedMap D hC
  smooth := cappedMap_smooth D hC
  mfderiv_bijective := cappedMap_mfderiv_bijective D hC
  covers := cappedMap_covers D hC
  side := cappedSide D
  side_bijective := cappedSide_bijective D
  matching := cappedMatching D
  seam := cappedSeam D hC
  seam_source := cappedSeam_source D hC
  seam_neg := cappedSeam_neg D hC
  seam_pos := cappedSeam_pos D hC
  overlap := cappedMap_overlap D hC

theorem card_seam_cappedSystem (D : E.SideData h K a δ₂) (hC : E.CappedConditions h a δ₂) :
    Fintype.card (cappedSystem D hC).Seam + 1 = E.complexity := by
  change Fintype.card {c : Fin E.toTorus.pairing.count // c ≠ j} + 1 = E.toTorus.pairing.count
  rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_unique]
  have : 0 < E.toTorus.pairing.count := Fin.pos j
  omega

end Capped

section Transition

variable {P : ClosedOrientedManifold.{u} 3}
  (X : SphericalCutCapTransition Q.toClosedOrientedManifold P) (a : X.tubes.Index) {δ₂ : ℝ}

theorem pieceComp_cappedSystem_inr (D : E.SideData h X.capping a δ₂)
    (hC : E.CappedConditions h a δ₂) (t : Bool) :
    (cappedSystem D hC).pieceComp (.inr t) = X.cutCapVertex a t := by
  obtain ⟨q, hq⟩ := D.cap_mem t (sphereToClosedCell SplitTube.poleS2)
  rw [← (cappedSystem D hC).mk_map (.inr t) q]
  change ConnectedComponents.mk (D.solid t q) = _
  rw [hq]
  exact X.capRange_subset_componentSet a t ⟨_, rfl⟩

theorem exists_cappedElementary_of_sideData [Subsingleton X.tubes.Index]
    (D : E.SideData h X.capping a δ₂) (hC : E.CappedConditions h a δ₂) :
    (X.cutCapVertex a false ≠ X.cutCapVertex a true →
      ∃ (EA : ElementaryPresentation (NoCuts.carrier (X.capped.component (X.cutCapVertex a false))))
        (EB : ElementaryPresentation (NoCuts.carrier (X.capped.component (X.cutCapVertex a true)))),
        EA.complexity + EB.complexity + 1 = E.complexity) ∧
    (X.cutCapVertex a false = X.cutCapVertex a true →
      ∃ EA : ElementaryPresentation (NoCuts.carrier (X.capped.component (X.cutCapVertex a false))),
        EA.complexity + 1 = E.complexity) := by
  set PS := cappedSystem D hC
  have hf : ∃ i, PS.pieceComp i = X.cutCapVertex a false :=
    ⟨.inr false, pieceComp_cappedSystem_inr E h X a D hC false⟩
  have ht : ∃ i, PS.pieceComp i = X.cutCapVertex a true :=
    ⟨.inr true, pieceComp_cappedSystem_inr E h X a D hC true⟩
  have hall : ∀ c, PS.seamComp c = X.cutCapVertex a false ∨ PS.seamComp c = X.cutCapVertex a true :=
    fun c => eq_cutCapVertex_of_subsingleton X a _
  have hcount := card_seam_cappedSystem D hC
  refine ⟨fun hne => ?_, fun heq => ?_⟩
  · refine ⟨((PS.restrict _ hf).toEmbeddedPieceSystem).toElementaryPresentation,
      ((PS.restrict _ ht).toEmbeddedPieceSystem).toElementaryPresentation, ?_⟩
    rw [ClosedPieceSystem.complexity_toElementaryPresentation,
      ClosedPieceSystem.complexity_toElementaryPresentation,
      PS.card_seam_restrict_add _ _ hne hf ht hall]
    exact hcount
  · refine ⟨((PS.restrict _ hf).toEmbeddedPieceSystem).toElementaryPresentation, ?_⟩
    rw [ClosedPieceSystem.complexity_toElementaryPresentation,
      PS.card_seam_restrict_of_forall _ hf (fun c => (hall c).elim id (fun e => e.trans heq.symm))]
    exact hcount

end Transition

end ElementaryPresentation

end GC.Seifert
