import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ElementarizeWiringComponent

/-!
# Planar and Möbius pieces of a core decomposition

Lane P1X2 (P1 wiring, the Möbius branch).

For a non-orientable base the core decomposition has planar pieces and Möbius pieces
(`ElementaryBase.mobius`). A `MobiusCore D` records it in the form the wiring needs, with the two
kinds of pieces as two separate families (`CorePieces`): planar bases `base j` (`j : PI`) and Möbius
bases `mob m` (`m : MI`) embedded in the core of `D`, the sides `(Σ j, Fin (kind j)) ⊕ MI` (a
Möbius base has one boundary circle), the cuts as bicollars of the base `B` lying above level 0,
the cut sides and the bottom sides (level-0 bicollars) with their collar formulas, and the overlap
on the cut circles. This is `PlanarCore` with Möbius pieces allowed.

As for `PlanarCore`: the pieces embed into the interior of `B` (`isSmoothEmbedding_ιP`,
`isSmoothEmbedding_ιM`), the points of height `ℓ = level 0` are exactly the zero sections of the
bottom sides, each on exactly one (`exists_bottom_of_level`, `bottom_unique`), every side carries
a bicollar of `B` with a lifted flow (`exists_sideData`; cuts get `cutLift`, bottom sides
`bottomLift`), MD5's `exists_syncedPiece` gives the synchronised planar piece maps
(`exists_planarPieceMap`), and a synchronised Möbius piece map
`χ : mobiusBundleCarrier → U` comes from the frozen hypothesis `hMD5` of tier T4
(`exists_mobiusPieceMap`). The frozen text of `hMD5` writes the model of `mobiusBundleCarrier` as
`𝓡∂ 3`; the two instances at the top (the charts and the manifold structure of
`mobiusBundleSet`, which are those of `mobiusBundleCarrier` by definition) let it elaborate.
-/

set_option autoImplicit false

noncomputable section
open Set Function Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert

instance : ChartedSpace (EuclideanHalfSpace 3) mobiusBundleCarrier.{u}.Carrier :=
  inferInstanceAs (ChartedSpace (EuclideanHalfSpace 3) mobiusBundleSet.{u})

instance : IsManifold (𝓡∂ 3) ∞ mobiusBundleCarrier.{u}.Carrier :=
  inferInstanceAs (IsManifold (𝓡∂ 3) ∞ mobiusBundleSet.{u})

structure CorePieces {B : CompactSurface.{u}} (D : BaseMorseData B) where
  PI : Type
  [fintypePI : Fintype PI]
  MI : Type
  [fintypeMI : Fintype MI]
  kind : PI → ℕ
  kind_mem : ∀ j, kind j ∈ ({1, 2, 3} : Finset ℕ)
  base : ∀ j, PlanarBase.{u} (kind j)
  incl : ∀ j, (base j).surface.Carrier → D.core.Carrier
  emb : ∀ j, Manifold.IsSmoothEmbedding (SurfaceModel.model (base j).surface.kind)
    (SurfaceModel.model D.core.kind) ∞ (incl j)
  mob : MI → MobiusBase.{u}
  inclM : ∀ m, (mob m).surface.Carrier → D.core.Carrier
  embM : ∀ m, Manifold.IsSmoothEmbedding (SurfaceModel.model (mob m).surface.kind)
    (SurfaceModel.model D.core.kind) ∞ (inclM m)

namespace CorePieces

attribute [instance] CorePieces.fintypePI CorePieces.fintypeMI

variable {B : CompactSurface.{u}} {D : BaseMorseData B} (Q : CorePieces D)

abbrev Side : Type := (Σ j : Q.PI, Fin (Q.kind j)) ⊕ Q.MI

abbrev Pt : Type u :=
  (Σ j : Q.PI, (Q.base j).surface.Carrier) ⊕ Σ m : Q.MI, (Q.mob m).surface.Carrier

def pt : Q.Pt → D.core.Carrier
  | .inl y => Q.incl y.1 y.2
  | .inr y => Q.inclM y.1 y.2

def piece : Q.Pt → Q.PI ⊕ Q.MI
  | .inl y => .inl y.1
  | .inr y => .inr y.1

def sideCollar : Q.Side → Circle × EuclideanHalfSpace 1 → D.core.Carrier
  | .inl w => fun p => Q.incl w.1 ((Q.base w.1).collar w.2 p)
  | .inr m => fun p => Q.inclM m ((Q.mob m).collar p)

def ιP (j : Q.PI) (x : (Q.base j).surface.Carrier) : B.Carrier := (Q.incl j x).val

def ιM (m : Q.MI) (x : (Q.mob m).surface.Carrier) : B.Carrier := (Q.inclM m x).val

def sidePt (w : Q.Side) (p : Circle × EuclideanHalfSpace 1) : B.Carrier := (Q.sideCollar w p).val

theorem sidePt_inl (j : Q.PI) (l : Fin (Q.kind j)) (p : Circle × EuclideanHalfSpace 1) :
    Q.sidePt (.inl ⟨j, l⟩) p = Q.ιP j ((Q.base j).collar l p) := rfl

theorem sidePt_inr (m : Q.MI) (p : Circle × EuclideanHalfSpace 1) :
    Q.sidePt (.inr m) p = Q.ιM m ((Q.mob m).collar p) := rfl

theorem level_le_ιP (j : Q.PI) (x : (Q.base j).surface.Carrier) : D.level 0 ≤ D.f (Q.ιP j x) :=
  (Q.incl j x).2

theorem level_le_ιM (m : Q.MI) (x : (Q.mob m).surface.Carrier) : D.level 0 ≤ D.f (Q.ιM m x) :=
  (Q.inclM m x).2

theorem isInteriorPoint_ιP (j : Q.PI) (x : (Q.base j).surface.Carrier) :
    (SurfaceModel.model B.kind).IsInteriorPoint (Q.ιP j x) :=
  D.isInteriorPoint_of_pos (D.level_zero_pos.trans_le (Q.level_le_ιP j x))

theorem isInteriorPoint_ιM (m : Q.MI) (x : (Q.mob m).surface.Carrier) :
    (SurfaceModel.model B.kind).IsInteriorPoint (Q.ιM m x) :=
  D.isInteriorPoint_of_pos (D.level_zero_pos.trans_le (Q.level_le_ιM m x))

theorem injective_ιP (j : Q.PI) : Injective (Q.ιP j) :=
  Subtype.val_injective.comp (Q.emb j).isEmbedding.injective

theorem injective_ιM (m : Q.MI) : Injective (Q.ιM m) :=
  Subtype.val_injective.comp (Q.embM m).isEmbedding.injective

theorem isSmoothEmbedding_ιP (j : Q.PI) :
    Manifold.IsSmoothEmbedding (SurfaceModel.model (Q.base j).surface.kind)
      (SurfaceModel.model B.kind) ∞ (Q.ιP j) :=
  isSmoothEmbedding_core_val_comp D (Q.emb j)

theorem isSmoothEmbedding_ιM (m : Q.MI) :
    Manifold.IsSmoothEmbedding (SurfaceModel.model (Q.mob m).surface.kind)
      (SurfaceModel.model B.kind) ∞ (Q.ιM m) :=
  isSmoothEmbedding_core_val_comp D (Q.embM m)

end CorePieces

theorem isBoundaryPoint_of_core_level {B : CompactSurface.{u}} {D : BaseMorseData B}
    {k : SurfaceModel} {X : Type u} [TopologicalSpace X] [ChartedSpace (SurfaceModel.Space k) X]
    [IsManifold (SurfaceModel.model k) ∞ X] {g : X → D.core.Carrier}
    (hg : Manifold.IsSmoothEmbedding (SurfaceModel.model k) (SurfaceModel.model D.core.kind) ∞ g)
    {x : X} (hx : D.f (g x).val = D.level 0) : (SurfaceModel.model k).IsBoundaryPoint x := by
  rw [ModelWithCorners.isBoundaryPoint_iff_not_isInteriorPoint]
  intro hint
  have hb := DifferentialGeometry.Topology.Manifold.bijective_mfderiv_of_isImmersionAt _ _
    g x (hg.isImmersion.isImmersionAt x) (by simp)
  have hloc := isLocalDiffeomorphAt_of_isInteriorPoint_of_bijective hg.contMDiff hint hb
  have hi := (hloc.isInteriorPoint_iff (by simp)).mp hint
  exact ((SurfaceModel.model D.core.kind).isInteriorPoint_iff_not_isBoundaryPoint _).mp hi
    ((D.core_isBoundaryPoint_iff _).mpr hx)

structure MobiusCore {B : CompactSurface.{u}} (D : BaseMorseData B) where
  pieces : CorePieces D
  cutCount : ℕ
  cut : Fin cutCount → PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ)) (SurfaceModel.model B.kind)
    (Circle × ℝ) B.Carrier ∞
  cut_source : ∀ c, (cut c).source = {p | -1 < p.2 ∧ p.2 < 1}
  cut_level : ∀ c t s, -1 < s → s < 1 → D.level 0 < D.f (cut c (t, s))
  covers : ∀ x : D.core.Carrier, ∃ y : pieces.Pt, pieces.pt y = x
  cutSide : Fin cutCount → Bool → pieces.Side
  cutSide_injective : Function.Injective (Function.uncurry cutSide)
  cutSide_collar : ∀ c b, ∃ σ : Circle ≃ₘ⟮𝓡 1, 𝓡 1⟯ Circle, ∀ t s (hs : 0 ≤ s), s < 1 →
    pieces.sidePt (cutSide c b) (t, halfPoint s hs) = cut c (σ t, if b then s else -s)
  bottom_collar : ∀ w, (∀ c b, cutSide c b ≠ w) → ∃ (x₀ : B.Carrier)
    (hx₀ : D.f x₀ = D.level 0) (σ : Circle ≃ₘ⟮𝓡 1, 𝓡 1⟯ Circle), ∀ t s (hs : 0 ≤ s), s < 1 →
      pieces.sidePt w (t, halfPoint s hs) = Classical.choose (D.exists_levelBicollar 0 hx₀) (σ t, s)
  overlap : ∀ y y' : pieces.Pt, pieces.piece y ≠ pieces.piece y' → pieces.pt y = pieces.pt y' →
    ∃ c t, (pieces.pt y).val = cut c (t, 0)

namespace MobiusCore

variable {B : CompactSurface.{u}} {D : BaseMorseData B} (P : MobiusCore D)

theorem exists_pt_of_level {x : B.Carrier} (hx : D.level 0 ≤ D.f x) :
    ∃ y : P.pieces.Pt, (P.pieces.pt y).val = x := by
  obtain ⟨y, hy⟩ := P.covers ⟨x, hx⟩
  exact ⟨y, congrArg Subtype.val hy⟩

def IsBottom (w : P.pieces.Side) : Prop := ∀ c b, P.cutSide c b ≠ w

def bottomPoint (w : P.pieces.Side) (h : P.IsBottom w) : B.Carrier :=
  (P.bottom_collar w h).choose

theorem bottomPoint_level (w : P.pieces.Side) (h : P.IsBottom w) :
    D.f (P.bottomPoint w h) = D.level 0 :=
  (P.bottom_collar w h).choose_spec.choose

def bottomBicollar (w : P.pieces.Side) (h : P.IsBottom w) :
    PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ)) (SurfaceModel.model B.kind) (Circle × ℝ)
      B.Carrier ∞ :=
  Classical.choose (D.exists_levelBicollar 0 (P.bottomPoint_level w h))

theorem bottomBicollar_spec (w : P.pieces.Side) (h : P.IsBottom w) :
    (P.bottomBicollar w h).source = {p | -1 < p.2 ∧ p.2 < 1} ∧
      range (fun t => P.bottomBicollar w h (t, 0)) =
        connectedComponentIn (D.f ⁻¹' {D.level 0}) (P.bottomPoint w h) ∧
      (∀ t s, -1 < s → s < 1 →
        D.f (P.bottomBicollar w h (t, s)) = D.level 0 + D.κ * s) ∧
      ∀ t, IsMIntegralCurveOn (fun s => P.bottomBicollar w h (t, s))
        (fun x => D.κ • D.field x) (Ioo (-1) 1) :=
  Classical.choose_spec (D.exists_levelBicollar 0 (P.bottomPoint_level w h))

def bottomSigma (w : P.pieces.Side) (h : P.IsBottom w) : Circle ≃ₘ⟮𝓡 1, 𝓡 1⟯ Circle :=
  (P.bottom_collar w h).choose_spec.choose_spec.choose

theorem bottomSigma_spec (w : P.pieces.Side) (h : P.IsBottom w) (t : Circle) (s : ℝ)
    (hs : 0 ≤ s) (hs1 : s < 1) :
    P.pieces.sidePt w (t, halfPoint s hs) = P.bottomBicollar w h (P.bottomSigma w h t, s) :=
  (P.bottom_collar w h).choose_spec.choose_spec.choose_spec t s hs hs1

def cutSigma (c : Fin P.cutCount) (b : Bool) : Circle ≃ₘ⟮𝓡 1, 𝓡 1⟯ Circle :=
  (P.cutSide_collar c b).choose

theorem cutSigma_spec (c : Fin P.cutCount) (b : Bool) (t : Circle) (s : ℝ) (hs : 0 ≤ s)
    (hs1 : s < 1) :
    P.pieces.sidePt (P.cutSide c b) (t, halfPoint s hs) =
      P.cut c (P.cutSigma c b t, if b then s else -s) :=
  (P.cutSide_collar c b).choose_spec t s hs hs1

theorem cutSide_collar_eq {c : Fin P.cutCount} {b : Bool} {w : P.pieces.Side}
    (h : P.cutSide c b = w) (t : Circle) (s : ℝ) (hs : 0 ≤ s) (hs1 : s < 1) :
    P.pieces.sidePt w (t, halfPoint s hs) = P.cut c (P.cutSigma c b t, if b then s else -s) := by
  rw [← h]
  exact P.cutSigma_spec c b t s hs hs1

theorem level_lt_of_not_isBottom {w : P.pieces.Side} (h : ¬ P.IsBottom w) (t : Circle) :
    D.level 0 < D.f (P.pieces.sidePt w (t, halfZero)) := by
  simp only [IsBottom, not_forall, not_not] at h
  obtain ⟨c, b, hcb⟩ := h
  rw [show halfZero = halfPoint 0 le_rfl from rfl, P.cutSide_collar_eq hcb t 0 le_rfl one_pos]
  exact P.cut_level c _ _ (by cases b <;> norm_num) (by cases b <;> norm_num)

theorem level_bottom {w : P.pieces.Side} (h : P.IsBottom w) (t : Circle) :
    D.f (P.pieces.sidePt w (t, halfZero)) = D.level 0 := by
  rw [show halfZero = halfPoint 0 le_rfl from rfl, P.bottomSigma_spec w h t 0 le_rfl one_pos,
    (P.bottomBicollar_spec w h).2.2.1 _ 0 (by norm_num) (by norm_num), mul_zero, add_zero]

def zeroSec (w : P.pieces.Side) : Set B.Carrier := range fun t => P.pieces.sidePt w (t, halfZero)

theorem zeroSec_eq {w : P.pieces.Side} (h : P.IsBottom w) :
    P.zeroSec w = range (fun θ => P.bottomBicollar w h (θ, 0)) := by
  ext y
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨P.bottomSigma w h t, (P.bottomSigma_spec w h t 0 le_rfl one_pos).symm⟩
  · rintro ⟨θ, rfl⟩
    refine ⟨(P.bottomSigma w h).symm θ, ?_⟩
    change P.pieces.sidePt w ((P.bottomSigma w h).symm θ, halfPoint 0 le_rfl) = _
    rw [P.bottomSigma_spec w h _ 0 le_rfl one_pos, Diffeomorph.apply_symm_apply]

theorem zeroSec_eq_cut {c : Fin P.cutCount} {b : Bool} {w : P.pieces.Side}
    (h : P.cutSide c b = w) : P.zeroSec w = range (fun θ => P.cut c (θ, 0)) := by
  ext y
  constructor
  · rintro ⟨t, rfl⟩
    refine ⟨P.cutSigma c b t, ?_⟩
    change P.cut c (P.cutSigma c b t, 0) = P.pieces.sidePt w (t, halfPoint 0 le_rfl)
    rw [P.cutSide_collar_eq h t 0 le_rfl one_pos]
    cases b <;> simp
  · rintro ⟨θ, rfl⟩
    refine ⟨(P.cutSigma c b).symm θ, ?_⟩
    change P.pieces.sidePt w ((P.cutSigma c b).symm θ, halfPoint 0 le_rfl) = P.cut c (θ, 0)
    rw [P.cutSide_collar_eq h _ 0 le_rfl one_pos, Diffeomorph.apply_symm_apply]
    cases b <;> simp

theorem level_of_mem_zeroSec {w : P.pieces.Side} (h : P.IsBottom w) {y : B.Carrier}
    (hy : y ∈ P.zeroSec w) : D.f y = D.level 0 := by
  obtain ⟨t, rfl⟩ := hy
  exact P.level_bottom h t

theorem exists_bottom_of_level {y : B.Carrier} (hy : D.f y = D.level 0) :
    ∃ (w : P.pieces.Side) (_ : P.IsBottom w) (t : Circle),
      P.pieces.sidePt w (t, halfZero) = y := by
  obtain ⟨z, hz⟩ := P.exists_pt_of_level hy.ge
  have key : ∃ (w : P.pieces.Side) (t : Circle), P.pieces.sidePt w (t, halfZero) = y := by
    rcases z with ⟨j, x⟩ | ⟨m, x⟩
    · have hb := isBoundaryPoint_of_core_level (P.pieces.emb j) (x := x) (hz ▸ hy)
      have hb' : x ∈ (SurfaceModel.model (P.pieces.base j).surface.kind).boundary
          (P.pieces.base j).surface.Carrier := hb
      rw [(P.pieces.base j).boundary_exhausted] at hb'
      obtain ⟨l, t, ht⟩ := mem_iUnion.mp hb'
      change (P.pieces.base j).collar l (t, halfZero) = x at ht
      refine ⟨.inl ⟨j, l⟩, t, ?_⟩
      rw [CorePieces.sidePt_inl, ht]
      exact hz
    · have hb := isBoundaryPoint_of_core_level (P.pieces.embM m) (x := x) (hz ▸ hy)
      have hb' : x ∈ (SurfaceModel.model (P.pieces.mob m).surface.kind).boundary
          (P.pieces.mob m).surface.Carrier := hb
      rw [(P.pieces.mob m).boundary_exhausted] at hb'
      obtain ⟨t, ht⟩ := hb'
      change (P.pieces.mob m).collar (t, halfZero) = x at ht
      refine ⟨.inr m, t, ?_⟩
      rw [CorePieces.sidePt_inr, ht]
      exact hz
  obtain ⟨w, t, ht⟩ := key
  have hbot : P.IsBottom w := by
    by_contra hnb
    have h := P.level_lt_of_not_isBottom hnb t
    rw [ht, hy] at h
    exact lt_irrefl _ h
  exact ⟨w, hbot, t, ht⟩

theorem bottom_unique {w w' : P.pieces.Side} (h : P.IsBottom w) (h' : P.IsBottom w')
    {t t' : Circle} (he : P.pieces.sidePt w (t, halfZero) = P.pieces.sidePt w' (t', halfZero)) :
    w = w' := by
  have hz : ∀ {k : ℕ} (Q : PlanarBase.{u} k) (l : Fin k) (τ : Circle),
      ((τ, halfZero) : Circle × EuclideanHalfSpace 1) ∈ (Q.collar l).source := fun Q l τ => by
    rw [Q.source_eq l]
    change (0 : ℝ) < 1
    exact one_pos
  have hcontra : ∀ (y y' : P.pieces.Pt), P.pieces.piece y ≠ P.pieces.piece y' →
      P.pieces.pt y = P.pieces.pt y' → (P.pieces.pt y).val = P.pieces.sidePt w (t, halfZero) →
      False := by
    intro y y' hne hyy hyw
    obtain ⟨c, τ, hc⟩ := P.overlap y y' hne hyy
    have h1 := P.level_bottom h t
    rw [← hyw, hc] at h1
    have h2 := P.cut_level c τ 0 (by norm_num) (by norm_num)
    rw [h1] at h2
    exact absurd h2 (lt_irrefl _)
  rcases w with ⟨j, l⟩ | m <;> rcases w' with ⟨j', l'⟩ | m'
  · by_cases hjj : j = j'
    · subst hjj
      have he' := P.pieces.injective_ιP j he
      by_contra hne
      have hll : l ≠ l' := fun e => hne (by rw [e])
      exact ((P.pieces.base j).disjoint hll).le_bot
        ⟨((P.pieces.base j).collar l).map_source (hz _ l t),
          he' ▸ ((P.pieces.base j).collar l').map_source (hz _ l' t')⟩
    · exact (hcontra (.inl ⟨j, _⟩) (.inl ⟨j', _⟩) (fun e => hjj (Sum.inl_injective e))
        (Subtype.ext he) rfl).elim
  · exact (hcontra (.inl ⟨j, _⟩) (.inr ⟨m', _⟩) Sum.inl_ne_inr (Subtype.ext he) rfl).elim
  · exact (hcontra (.inr ⟨m, _⟩) (.inl ⟨j', _⟩) Sum.inr_ne_inl (Subtype.ext he) rfl).elim
  · by_cases hmm : m = m'
    · rw [hmm]
    · exact (hcontra (.inr ⟨m, _⟩) (.inr ⟨m', _⟩) (fun e => hmm (Sum.inr_injective e))
        (Subtype.ext he) rfl).elim

section Lift

variable {C : CompactCarrier.{u}} {U : TopologicalSpace.Opens C.Carrier} (F : CircleFibration C U)
  {D : BaseMorseData F.base} (P : MobiusCore D)

def cutLift (c : Fin P.cutCount) : LiftedBicollar F (P.cut c) :=
  (CircleFibration.exists_liftFlow F (P.cut c) (R := 1 / 2) (by norm_num)
    (PlanarCore.mem_source_of_abs_le_half F (P.cut_source c))).choose

theorem cutLift_width (c : Fin P.cutCount) : (cutLift F P c).width = 1 / 16 :=
  (CircleFibration.exists_liftFlow F (P.cut c) (R := 1 / 2) (by norm_num)
    (PlanarCore.mem_source_of_abs_le_half F (P.cut_source c))).choose_spec.1.trans (by norm_num)

def bottomLift (w : P.pieces.Side) (h : P.IsBottom w) : LiftedBicollar F (P.bottomBicollar w h) :=
  (CircleFibration.exists_liftFlow F (P.bottomBicollar w h) (R := 1 / 2) (by norm_num)
    (PlanarCore.mem_source_of_abs_le_half F (P.bottomBicollar_spec w h).1)).choose

theorem bottomLift_width (w : P.pieces.Side) (h : P.IsBottom w) :
    (bottomLift F P w h).width = 1 / 16 :=
  (CircleFibration.exists_liftFlow F (P.bottomBicollar w h) (R := 1 / 2) (by norm_num)
    (PlanarCore.mem_source_of_abs_le_half F (P.bottomBicollar_spec w h).1)).choose_spec.1.trans
      (by norm_num)

theorem exists_sideData (w : P.pieces.Side) :
    ∃ (cB : PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ)) (SurfaceModel.model F.base.kind)
      (Circle × ℝ) F.base.Carrier ∞) (_ : cB.source = {p | -1 < p.2 ∧ p.2 < 1}) (b : Bool)
      (σ : Circle ≃ₘ⟮𝓡 1, 𝓡 1⟯ Circle) (L : LiftedBicollar F cB),
      (∀ t s (hs : 0 ≤ s), s < 1 →
        P.pieces.sidePt w (t, halfPoint s hs) = cB (σ t, if b then s else -s)) ∧
      (∀ c b', P.cutSide c b' = w → b = b' ∧ L.flow = (cutLift F P c).flow) ∧
      ∀ h : P.IsBottom w, b = true ∧ L.flow = (bottomLift F P w h).flow := by
  by_cases h : P.IsBottom w
  · refine ⟨P.bottomBicollar w h, (P.bottomBicollar_spec w h).1, true, P.bottomSigma w h,
      bottomLift F P w h, fun t s hs hs1 => ?_, fun c b' hcb => absurd hcb (h c b'),
      fun _ => ⟨rfl, rfl⟩⟩
    rw [P.bottomSigma_spec w h t s hs hs1]
    simp
  · have h' : ∃ c b, P.cutSide c b = w := by
      by_contra hne
      push Not at hne
      exact h hne
    obtain ⟨c, b, hcb⟩ := h'
    refine ⟨P.cut c, P.cut_source c, b, P.cutSigma c b, cutLift F P c,
      fun t s hs hs1 => P.cutSide_collar_eq hcb t s hs hs1, fun c' b' hcb' => ?_,
      fun hb => absurd hcb (hb c b)⟩
    have he : (c, b) = (c', b') := P.cutSide_injective (hcb.trans hcb'.symm)
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
    exact ⟨rfl, rfl⟩

theorem exists_planarPieceMap (j : P.pieces.PI) :
    ∃ Φ : (P.pieces.base j).surface.Carrier × Circle → U,
      ContMDiff ((SurfaceModel.model (P.pieces.base j).surface.kind).prod (𝓡 1)) C.model ∞
        (fun q => (Φ q).val) ∧ Injective Φ ∧
      (∀ q, Bijective (mfderiv ((SurfaceModel.model (P.pieces.base j).surface.kind).prod (𝓡 1))
        C.model (fun q => (Φ q).val) q)) ∧
      (∀ q, F.projection (Φ q) = P.pieces.ιP j q.1) ∧
      range Φ = F.projection ⁻¹' range (P.pieces.ιP j) ∧
      ∃ δ > 0, (∀ (l : Fin (P.pieces.kind j)) (c : Fin P.cutCount) (b : Bool),
          P.cutSide c b = .inl ⟨j, l⟩ →
          ∀ t v s (hs : 0 ≤ s), s < δ → Φ ((P.pieces.base j).collar l (t, halfPoint s hs), v) =
            (cutLift F P c).flow (if b then s else -s)
              (Φ ((P.pieces.base j).collar l (t, halfZero), v))) ∧
        ∀ (l : Fin (P.pieces.kind j)) (h : P.IsBottom (.inl ⟨j, l⟩)) t v s (hs : 0 ≤ s), s < δ →
          Φ ((P.pieces.base j).collar l (t, halfPoint s hs), v) =
            (bottomLift F P _ h).flow s (Φ ((P.pieces.base j).collar l (t, halfZero), v)) := by
  classical
  choose cB hcB b σ L hcol hcut hbot using fun l : Fin (P.pieces.kind j) =>
    exists_sideData F P (.inl ⟨j, l⟩)
  obtain ⟨Φ, hΦs, hΦe, hΦb, hΦπ, hΦr, δ, hδ, hΦsync⟩ := exists_syncedPiece F
    (P.pieces.kind_mem j) (P.pieces.base j) (P.pieces.isSmoothEmbedding_ιP j) cB hcB b σ hcol
    (P.pieces.isInteriorPoint_ιP j) L
  refine ⟨Φ, hΦs, hΦe.injective, hΦb, hΦπ, hΦr, δ, hδ, fun l c b' hcb t v s hs hs1 => ?_,
    fun l h t v s hs hs1 => ?_⟩
  · obtain ⟨e1, e2⟩ := hcut l c b' hcb
    rw [hΦsync l t v s hs hs1, e2, e1]
  · obtain ⟨e1, e2⟩ := hbot l h
    rw [hΦsync l t v s hs hs1, e2, e1]
    simp

theorem exists_mobiusPieceMap
    (hMD5 : ∀ {C : CompactCarrier.{u}} {U : TopologicalSpace.Opens C.Carrier}
      (F : CircleFibration C U) (M : MobiusBase.{u}) {ι : M.surface.Carrier → F.base.Carrier}
      (_hι : Manifold.IsSmoothEmbedding
        (SurfaceModel.model M.surface.kind) (SurfaceModel.model F.base.kind) ∞ ι)
      (c : PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ)) (SurfaceModel.model F.base.kind) (Circle × ℝ)
        F.base.Carrier ∞)
      (_hc : c.source = {p | -1 < p.2 ∧ p.2 < 1}) (b : Bool) (σ : Circle ≃ₘ⟮𝓡 1, 𝓡 1⟯ Circle)
      (_hcol : ∀ t s (hs : 0 ≤ s), s < 1 →
        ι (M.collar (t, halfPoint s hs)) = c (σ t, if b then s else -s))
      (_hint : ∀ q, (SurfaceModel.model F.base.kind).IsInteriorPoint (ι q))
      (L : LiftedBicollar F c),
      ∃ χ : mobiusBundleCarrier.{u}.Carrier → U, ContMDiff (𝓡∂ 3) C.model ∞ (fun q => (χ q).val) ∧
        Function.Injective χ ∧
        (∀ q, Function.Bijective (mfderiv (𝓡∂ 3) C.model (fun q => (χ q).val) q)) ∧
        range χ = F.projection ⁻¹' range ι ∧
        range (fun t => χ (mobiusExternalCollar (t, halfZero))) =
          F.projection ⁻¹' range (fun θ => c (θ, 0)) ∧
        ∃ δ > 0, ∀ t s (hs : 0 ≤ s), s < δ → χ (mobiusExternalCollar (t, halfPoint s hs)) =
          L.flow (if b then s else -s) (χ (mobiusExternalCollar (t, halfZero))))
    (m : P.pieces.MI) :
    ∃ χ : mobiusBundleCarrier.{u}.Carrier → U, ContMDiff (𝓡∂ 3) C.model ∞ (fun q => (χ q).val) ∧
      Function.Injective χ ∧
      (∀ q, Function.Bijective (mfderiv (𝓡∂ 3) C.model (fun q => (χ q).val) q)) ∧
      range χ = F.projection ⁻¹' range (P.pieces.ιM m) ∧
      range (fun t => χ (mobiusExternalCollar (t, halfZero))) =
        F.projection ⁻¹' P.zeroSec (.inr m) ∧
      ∃ δ > 0, (∀ (c : Fin P.cutCount) (b : Bool), P.cutSide c b = .inr m →
          ∀ t s (hs : 0 ≤ s), s < δ → χ (mobiusExternalCollar (t, halfPoint s hs)) =
            (cutLift F P c).flow (if b then s else -s) (χ (mobiusExternalCollar (t, halfZero)))) ∧
        ∀ (h : P.IsBottom (.inr m)) t s (hs : 0 ≤ s), s < δ →
          χ (mobiusExternalCollar (t, halfPoint s hs)) =
            (bottomLift F P _ h).flow s (χ (mobiusExternalCollar (t, halfZero))) := by
  obtain ⟨cB, hcB, b, σ, L, hcol, hcut, hbot⟩ := exists_sideData F P (.inr m)
  obtain ⟨χ, hχs, hχi, hχb, hχr, hχz, δ, hδ, hχsync⟩ := hMD5 F (P.pieces.mob m)
    (P.pieces.isSmoothEmbedding_ιM m) cB hcB b σ hcol (P.pieces.isInteriorPoint_ιM m) L
  have hz : P.zeroSec (.inr m) = range (fun θ => cB (θ, 0)) := by
    ext y
    constructor
    · rintro ⟨t, rfl⟩
      refine ⟨σ t, ?_⟩
      change cB (σ t, 0) = P.pieces.sidePt (.inr m) (t, halfPoint 0 le_rfl)
      rw [hcol t 0 le_rfl one_pos]
      cases b <;> simp
    · rintro ⟨θ, rfl⟩
      refine ⟨σ.symm θ, ?_⟩
      change P.pieces.sidePt (.inr m) (σ.symm θ, halfPoint 0 le_rfl) = _
      rw [hcol _ 0 le_rfl one_pos, Diffeomorph.apply_symm_apply]
      cases b <;> simp
  refine ⟨χ, hχs, hχi, hχb, hχr, hz ▸ hχz, δ, hδ, fun c b' hcb t s hs hs1 => ?_,
    fun h t s hs hs1 => ?_⟩
  · obtain ⟨e1, e2⟩ := hcut c b' hcb
    rw [hχsync t s hs hs1, e2, e1]
  · obtain ⟨e1, e2⟩ := hbot h
    rw [hχsync t s hs hs1, e2, e1]
    simp

end Lift

end MobiusCore

end GC.Seifert
