import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ElementarizeWiringMobiusData
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ElementarizeWiringMobiusSystem
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ElementarizeWiringRefinement

/-!
# The component refinement of one old piece with Möbius core pieces

Lane P1X2 (P1 wiring, the Möbius branch), assembly.

Let `S` be a piece system of `mobiusBundleCarrier` with one external side `e₀`, whose collar is
`mobiusExternalCollar` (for instance `E.toPieceSystem` for the elementary presentation `E` of
the frozen hypothesis `hE`). From `MixedWiringData T i F P` and `0 < δ ≤ δ₀` the `BlockData` of
the component is:

* pieces `PI ⊕ (MI × Fin S.count) ⊕ T.OwnedSide i`: the planar pieces `Φ j` with base
  `(P.pieces.base j).shrink δ`, for every Möbius piece `m` the pieces of `S` carried over along
  `χ m` (`χ m ∘ S.map a`, base `(S.base a).shrink δ`), and the collar pieces;
* synchronised seams `Fin P.cutCount ⊕ T.OwnedSide i`, as in P1W's wiring: the cuts and the tops of
  the collar pieces. A side of the core is a side of a planar piece or the external side of the
  carried-over `S` (`toSide`); the synchronisation on the external side of `S` is the
  synchronisation of `χ m` with the flow of the side (`MixedWiringData.cutSyncχ`, `bottomSyncχ`),
  read through `mobiusExternalCollar`;
* given seams `MI × Fin S.seamCount`: the seams of `S` carried over along `χ m` and shrunk by `δ`
  (`gseam`, a partial diffeomorphism because `χ m` is an injective local diffeomorphism at the
  interior points of `mobiusBundleCarrier`);
* external sides: the ports `0` of the collar pieces, equal to the old side collars of
  `(T.reparam id).shrink δ`.

`exists_componentRefinement_mobius` is the resulting component refinement for every small `δ`.
-/

set_option autoImplicit false

noncomputable section
open Set Function Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert.Wiring

section Index

variable {W : CompactCarrier.{u}} (T : TorusPresentation W) (i : Fin T.components.count)
  {B : CompactSurface.{u}} {D : BaseMorseData B} (P : MobiusCore D)
  (S : EmbeddedPieceSystem mobiusBundleCarrier.{u})

abbrev MIdx : Type := P.pieces.PI ⊕ (P.pieces.MI × Fin S.count) ⊕ T.OwnedSide i

abbrev mkind : MIdx T i P S → ℕ :=
  Sum.elim P.pieces.kind (Sum.elim (fun a => S.kind a.2) fun _ => 2)

abbrev MSide : Type := Σ x : MIdx T i P S, Fin (mkind T i P S x)

def mobSide (m : P.pieces.MI) (w : Σ a, Fin (S.kind a)) : MSide T i P S :=
  ⟨.inr (.inl (m, w.1)), w.2⟩

def toSide (e₀ : Fin S.externalCount) : P.pieces.Side → MSide T i P S
  | .inl w => ⟨.inl w.1, w.2⟩
  | .inr m => mobSide T i P S m (S.externalSide e₀)

theorem mobSide_inj {m m' : P.pieces.MI} {w w' : Σ a, Fin (S.kind a)}
    (h : mobSide T i P S m w = mobSide T i P S m' w') : m = m' ∧ w = w' := by
  obtain ⟨a, l⟩ := w
  obtain ⟨a', l'⟩ := w'
  have h1 := (Sigma.mk.inj_iff.mp h).1
  have h2 := (Sigma.mk.inj_iff.mp h).2
  have h3 : (m, a) = (m', a') := Sum.inl_injective (Sum.inr_injective h1)
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj h3
  have h2' : l = l' := eq_of_heq h2
  exact ⟨rfl, by rw [h2']⟩

theorem toSide_ne_col (e₀ : Fin S.externalCount) (w : P.pieces.Side) (s : T.OwnedSide i)
    (l : Fin 2) : toSide T i P S e₀ w ≠ (⟨.inr (.inr s), l⟩ : MSide T i P S) := by
  intro h
  have h1 := congrArg Sigma.fst h
  rcases w with w | m
  · exact Sum.inl_ne_inr h1
  · exact Sum.inl_ne_inr (Sum.inr_injective h1)

theorem mobSide_ne_col (m : P.pieces.MI) (w : Σ a, Fin (S.kind a)) (s : T.OwnedSide i)
    (l : Fin 2) : mobSide T i P S m w ≠ (⟨.inr (.inr s), l⟩ : MSide T i P S) := by
  intro h
  exact Sum.inl_ne_inr (Sum.inr_injective (congrArg Sigma.fst h))

theorem toSide_ne_gside (e₀ : Fin S.externalCount) (w : P.pieces.Side) (m : P.pieces.MI)
    (c : Fin S.seamCount) (b : Bool) : toSide T i P S e₀ w ≠ mobSide T i P S m (S.side c b) := by
  intro h
  rcases w with w | m'
  · exact Sum.inl_ne_inr (congrArg Sigma.fst h)
  · have h' := (mobSide_inj T i P S h).2
    have := S.sides_bijective.1 (a₁ := Sum.inr e₀) (a₂ := Sum.inl (c, b)) h'
    exact Sum.inr_ne_inl this

theorem toSide_injective (e₀ : Fin S.externalCount) : Injective (toSide T i P S e₀) := by
  rintro (⟨j, l⟩ | m) (⟨j', l'⟩ | m') h
  · have h1 : j = j' := Sum.inl_injective (congrArg Sigma.fst h)
    subst h1
    have h2 : l = l' := eq_of_heq (Sigma.mk.inj_iff.mp h).2
    rw [h2]
  · exact absurd (congrArg Sigma.fst h) Sum.inl_ne_inr
  · exact absurd (congrArg Sigma.fst h) Sum.inr_ne_inl
  · rw [(mobSide_inj T i P S h).1]

theorem col_inj {s s' : T.OwnedSide i} {l l' : Fin 2}
    (h : (⟨.inr (.inr s), l⟩ : MSide T i P S) = ⟨.inr (.inr s'), l'⟩) : s = s' ∧ l = l' := by
  have h1 : s = s' := Sum.inr_injective (Sum.inr_injective (congrArg Sigma.fst h))
  subst h1
  exact ⟨rfl, eq_of_heq (Sigma.mk.inj_iff.mp h).2⟩

end Index

variable {W : CompactCarrier.{u}} {T : TorusPresentation W} {i : Fin T.components.count}
  {F : CircleFibration T.cutCarrier (T.components.piece i)} {D : BaseMorseData F.base}
  {P : MobiusCore D} [Fact (0 < D.level 0)] (Wd : MixedWiringData T i F P)
  (S : EmbeddedPieceSystem mobiusBundleCarrier.{u}) (e₀ : Fin S.externalCount)
  (hS1 : ∀ e, e = e₀)
  (hSc : ∀ p, p ∈ halfCollarSource → S.map (S.externalSide e₀).1
    ((S.base _).collar (S.externalSide e₀).2 (p.1.1, p.2), p.1.2) = mobiusExternalCollar p)
  {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hδ0 : δ ≤ Wd.δ₀)

namespace MixedWiringData

include hδ0 in
theorem eta_le : 10 * δ / D.level 0 ≤ 1 := by
  have h : 0 < D.level 0 := Fact.out
  rw [div_le_one h]
  linarith [Wd.δ₀_le_level]

def base : ∀ x : MIdx T i P S, PlanarBase.{u} (mkind T i P S x)
  | .inl j => (P.pieces.base j).shrink hδ hδ1
  | .inr (.inl a) => (S.base a.2).shrink hδ hδ1
  | .inr (.inr _) => (planarBase.{u} 2 (Or.inl rfl)).shrink (WiringData.eta_pos_of D hδ)
      (Wd.eta_le hδ0)

def map : ∀ x, (Wd.base S hδ hδ1 hδ0 x).surface.Carrier × Circle → T.components.piece i
  | .inl j => Wd.Φ j
  | .inr (.inl a) => fun q => Wd.χ a.1 (S.map a.2 q)
  | .inr (.inr s) => collarPieceMap (D.level 0) (Wd.K s)

def flow : Fin P.cutCount ⊕ T.OwnedSide i → ℝ →
    (T.components.piece i ≃ₘ⟮T.cutCarrier.model, T.cutCarrier.model⟯ T.components.piece i)
  | .inl c => (MobiusCore.cutLift F P c).flow
  | .inr s => (MobiusCore.bottomLift F P (Wd.β s) (Wd.βh s)).flow

def side : Fin P.cutCount ⊕ T.OwnedSide i → Bool → MSide T i P S
  | .inl c, b => toSide T i P S e₀ (P.cutSide c (!b))
  | .inr s, true => ⟨.inr (.inr s), (1 : Fin 2)⟩
  | .inr s, false => toSide T i P S e₀ (Wd.β s)

omit [Fact (0 < D.level 0)] in
theorem kind_mem (x : MIdx T i P S) : mkind T i P S x ∈ ({1, 2, 3} : Finset ℕ) := by
  rcases x with j | a | s
  · exact P.pieces.kind_mem j
  · exact S.kind_mem a.2
  · change (2 : ℕ) ∈ ({1, 2, 3} : Finset ℕ)
    decide

theorem smooth_map (x : MIdx T i P S) :
    ContMDiff ((SurfaceModel.model (Wd.base S hδ hδ1 hδ0 x).surface.kind).prod (𝓡 1))
      T.cutCarrier.model ∞ (Wd.map S hδ hδ1 hδ0 x) := by
  rcases x with j | a | s
  · exact Wd.smoothΦ j
  · exact (Wd.smoothχ a.1).comp (S.smooth a.2)
  · exact contMDiff_collarPieceMap (D.level 0) (Wd.smoothK s)

theorem bijective_map (x : MIdx T i P S) (q) :
    Bijective (mfderiv ((SurfaceModel.model (Wd.base S hδ hδ1 hδ0 x).surface.kind).prod (𝓡 1))
      T.cutCarrier.model (Wd.map S hδ hδ1 hδ0 x) q) := by
  rcases x with j | a | s
  · exact Wd.bijΦ j q
  · have key : ∀ q' : (S.base a.2).surface.Carrier × Circle,
        Bijective (mfderiv ((SurfaceModel.model (S.base a.2).surface.kind).prod (𝓡 1))
          T.cutCarrier.model (Wd.χ a.1 ∘ S.map a.2) q') := by
      intro q'
      rw [mfderiv_comp q' ((Wd.smoothχ a.1).mdifferentiableAt (by simp))
        ((S.smooth a.2).mdifferentiableAt (by simp)), ContinuousLinearMap.coe_comp]
      exact (Wd.bijχ a.1 _).comp (S.mfderiv_bijective a.2 q')
    exact key q
  · exact bijective_mfderiv_collarPieceMap (D.level 0) (Wd.smoothK s) (Wd.bijK s) q

theorem flow_add (c : Fin P.cutCount ⊕ T.OwnedSide i) (a b : ℝ) (x : T.components.piece i) :
    Wd.flow c (a + b) x = Wd.flow c a (Wd.flow c b x) := by
  rcases c with c | s
  · exact (MobiusCore.cutLift F P c).flow_add a b x
  · exact (MobiusCore.bottomLift F P _ _).flow_add a b x

theorem halfSpace_ext {h h' : EuclideanHalfSpace 1} (e : h.val 0 = h'.val 0) : h = h' := by
  rw [← halfPoint_eq_self h h.2 rfl, ← halfPoint_eq_self h' h'.2 rfl]
  have key : ∀ (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b), a = b → halfPoint a ha = halfPoint b hb := by
    rintro a _ ha hb rfl
    rfl
  exact key _ _ _ _ e

include hSc in
theorem mob_collar (m : P.pieces.MI) (t v : Circle) {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    Wd.map S hδ hδ1 hδ0 (.inr (.inl (m, (S.externalSide e₀).1)))
      (((S.base (S.externalSide e₀).1).shrink hδ hδ1).collar (S.externalSide e₀).2
        (t, halfPoint r hr), v) =
      Wd.χ m (mobiusExternalCollar ((t, v), halfPoint (δ * r) (mul_nonneg hδ.le hr))) := by
  change Wd.χ m (S.map (S.externalSide e₀).1 (((S.base (S.externalSide e₀).1).shrink hδ hδ1).collar
    (S.externalSide e₀).2 (t, halfPoint r hr), v)) = _
  rw [shrink_collar_halfPoint]
  exact congrArg (Wd.χ m) (hSc ((t, v), halfPoint (δ * r) (mul_nonneg hδ.le hr))
    (show δ * r < 1 by nlinarith))

include hSc in
theorem mob_collar_zero (m : P.pieces.MI) (t v : Circle) :
    Wd.map S hδ hδ1 hδ0 (.inr (.inl (m, (S.externalSide e₀).1)))
      (((S.base (S.externalSide e₀).1).shrink hδ hδ1).collar (S.externalSide e₀).2
        (t, halfZero), v) = Wd.χ m (mobiusExternalCollar ((t, v), halfZero)) := by
  change Wd.χ m (S.map (S.externalSide e₀).1 (((S.base (S.externalSide e₀).1).shrink hδ hδ1).collar
    (S.externalSide e₀).2 (t, halfZero), v)) = _
  rw [shrink_collar_halfZero]
  exact congrArg (Wd.χ m) (hSc ((t, v), halfZero) (zero_mem_halfCollarSource _))

include hSc in
theorem sync_toSide_cut (w : P.pieces.Side) (c : Fin P.cutCount) (b : Bool)
    (h : P.cutSide c b = w) (t v : Circle) (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) :
    Wd.map S hδ hδ1 hδ0 (toSide T i P S e₀ w).1 ((Wd.base S hδ hδ1 hδ0 _).collar
      (toSide T i P S e₀ w).2 (t, halfPoint r hr), v) =
      (MobiusCore.cutLift F P c).flow (if b then δ * r else -(δ * r))
        (Wd.map S hδ hδ1 hδ0 (toSide T i P S e₀ w).1 ((Wd.base S hδ hδ1 hδ0 _).collar
          (toSide T i P S e₀ w).2 (t, halfZero), v)) := by
  have hlt : δ * r < Wd.δ₀ := by nlinarith [Wd.δ₀_pos]
  rcases w with ⟨j, l⟩ | m
  · change Wd.Φ j (((P.pieces.base j).shrink hδ hδ1).collar l (t, halfPoint r hr), v) =
      (MobiusCore.cutLift F P c).flow (if b then δ * r else -(δ * r))
        (Wd.Φ j (((P.pieces.base j).shrink hδ hδ1).collar l (t, halfZero), v))
    rw [shrink_collar_halfPoint, shrink_collar_halfZero]
    exact Wd.cutSync j l c b h t v (δ * r) (mul_nonneg hδ.le hr) hlt
  · exact (Wd.mob_collar S e₀ hSc hδ hδ1 hδ0 m t v hr hr1).trans
      ((Wd.cutSyncχ m c b h (t, v) (δ * r) (mul_nonneg hδ.le hr) hlt).trans
        (congrArg _ (Wd.mob_collar_zero S e₀ hSc hδ hδ1 hδ0 m t v).symm))

include hSc in
theorem sync_toSide_bottom (w : P.pieces.Side) (h : P.IsBottom w) (t v : Circle) (r : ℝ)
    (hr : 0 ≤ r) (hr1 : r < 1) :
    Wd.map S hδ hδ1 hδ0 (toSide T i P S e₀ w).1 ((Wd.base S hδ hδ1 hδ0 _).collar
      (toSide T i P S e₀ w).2 (t, halfPoint r hr), v) =
      (MobiusCore.bottomLift F P w h).flow (δ * r)
        (Wd.map S hδ hδ1 hδ0 (toSide T i P S e₀ w).1 ((Wd.base S hδ hδ1 hδ0 _).collar
          (toSide T i P S e₀ w).2 (t, halfZero), v)) := by
  have hlt : δ * r < Wd.δ₀ := by nlinarith [Wd.δ₀_pos]
  rcases w with ⟨j, l⟩ | m
  · change Wd.Φ j (((P.pieces.base j).shrink hδ hδ1).collar l (t, halfPoint r hr), v) =
      (MobiusCore.bottomLift F P _ h).flow (δ * r)
        (Wd.Φ j (((P.pieces.base j).shrink hδ hδ1).collar l (t, halfZero), v))
    rw [shrink_collar_halfPoint, shrink_collar_halfZero]
    exact Wd.bottomSync j l h t v (δ * r) (mul_nonneg hδ.le hr) hlt
  · exact (Wd.mob_collar S e₀ hSc hδ hδ1 hδ0 m t v hr hr1).trans
      ((Wd.bottomSyncχ m h (t, v) (δ * r) (mul_nonneg hδ.le hr) hlt).trans
        (congrArg _ (Wd.mob_collar_zero S e₀ hSc hδ hδ1 hδ0 m t v).symm))

include hSc in
theorem range_toSide (w : P.pieces.Side) :
    range (sideTorus (Wd.base S hδ hδ1 hδ0 (toSide T i P S e₀ w).1) (toSide T i P S e₀ w).2
      (Wd.map S hδ hδ1 hδ0 (toSide T i P S e₀ w).1)) = F.projection ⁻¹' P.zeroSec w := by
  rcases w with ⟨j, l⟩ | m
  · change range (sideTorus ((P.pieces.base j).shrink hδ hδ1) l (Wd.Φ j)) = _
    rw [sideTorus_shrink]
    exact range_sideTorus_planar T i F P l (Wd.projΦ j) (Wd.rangeΦ j)
  · refine (congrArg range (funext fun t => ?_)).trans (Wd.zeroχ m)
    exact Wd.mob_collar_zero S e₀ hSc hδ hδ1 hδ0 m t.1 t.2

include hSc in
theorem injOn_toSide (w : P.pieces.Side) :
    InjOn (fun p : Torus × EuclideanHalfSpace 1 => Wd.map S hδ hδ1 hδ0 (toSide T i P S e₀ w).1
      ((Wd.base S hδ hδ1 hδ0 _).collar (toSide T i P S e₀ w).2 (p.1.1, p.2), p.1.2))
      halfCollarSource := by
  rcases w with ⟨j, l⟩ | m
  · exact injOn_collar_of_injective ((P.pieces.base j).shrink hδ hδ1) l (Wd.injΦ j)
  · intro p hp p' hp' h
    have key : ∀ q : Torus × EuclideanHalfSpace 1, q ∈ halfCollarSource →
        Wd.map S hδ hδ1 hδ0 (toSide T i P S e₀ (.inr m)).1
          ((Wd.base S hδ hδ1 hδ0 _).collar (toSide T i P S e₀ (.inr m)).2 (q.1.1, q.2), q.1.2) =
        Wd.χ m (mobiusExternalCollar (q.1, halfSpaceScale hδ q.2)) := fun q hq =>
      congrArg (Wd.χ m) (hSc (q.1, halfSpaceScale hδ q.2) (halfSpaceScale_mem hδ hδ1 hq))
    have h' := Wd.injχ m (((key p hp).symm.trans h).trans (key p' hp'))
    have hm : ∀ q : Torus × EuclideanHalfSpace 1, q ∈ halfCollarSource →
        (q.1, halfSpaceScale hδ q.2) ∈ mobiusExternalCollar.{u}.source := fun q hq => by
      rw [mobiusExternalCollar_source]
      exact halfSpaceScale_mem hδ hδ1 hq
    have h'' := mobiusExternalCollar.injOn (hm p hp) (hm p' hp') h'
    refine Prod.ext (Prod.mk.inj h'').1 (halfSpace_ext ?_)
    have e := congrArg (fun q : EuclideanHalfSpace 1 => q.val 0) (Prod.mk.inj h'').2
    simp only [halfSpaceScale_coord] at e
    exact mul_left_cancel₀ hδ.ne' e

include hδ hδ1 in
theorem exists_gseam (a : P.pieces.MI × Fin S.seamCount) :
    ∃ G : PartialDiffeomorph signedCollarModel T.cutCarrier.model (Torus × ℝ)
      (T.components.piece i) ∞,
      G.source = signedCollarSource ∧ (∀ y, G y = Wd.χ a.1 (S.seam a.2 (y.1, δ * y.2))) ∧
      ∀ y ∈ G.target, T.cutCarrier.model.IsInteriorPoint y := by
  set g := shrinkSignedCollar hδ (S.seam a.2) with hg
  have hgs : g.source = signedCollarSource := shrinkSignedCollar_source hδ hδ1 (S.seam_source a.2)
  have hgint : ∀ y ∈ g.source, mobiusBundleCarrier.{u}.model.IsInteriorPoint (g y) := fun y hy =>
    S.seam_interior a.2 (shrinkSignedCollar_target_subset hδ _ (g.map_source hy))
  have hχloc : ∀ y ∈ g.source, IsLocalDiffeomorphAt mobiusBundleCarrier.{u}.model
      T.cutCarrier.model ∞ (Wd.χ a.1) (g y) := fun y hy =>
    isLocalDiffeomorphAt_of_isInteriorPoint_of_bijective (Wd.smoothχ a.1) (hgint y hy)
      (Wd.bijχ a.1 _)
  have hloc : IsLocalDiffeomorphOn signedCollarModel T.cutCarrier.model ∞ (Wd.χ a.1 ∘ g)
      signedCollarSource := by
    rintro ⟨y, hy⟩
    have hy' : y ∈ g.source := hgs ▸ hy
    exact (g.isLocalDiffeomorphAt _ _ _ hy').comp _ _ (hχloc y hy')
  have hinj : InjOn (Wd.χ a.1 ∘ g) signedCollarSource := fun y hy y' hy' h =>
    g.injOn (hgs ▸ hy) (hgs ▸ hy') (Wd.injχ a.1 h)
  have hne : (signedCollarSource : Set (Torus × ℝ)).Nonempty :=
    ⟨((1 : Torus), 0), by norm_num, by norm_num⟩
  obtain ⟨G, hGs, hGt, hGf⟩ :=
    hloc.exists_partialDiffeomorph_of_injOn isOpen_signedCollarSource' hne hinj
  refine ⟨G, hGs, fun y => congrFun hGf y, ?_⟩
  intro y hy
  rw [hGt] at hy
  obtain ⟨z, hz, rfl⟩ := hy
  have hz' : z ∈ g.source := hgs ▸ hz
  exact ((hχloc z hz').isInteriorPoint_iff (by simp)).mp (hgint z hz')

def gseam (a : P.pieces.MI × Fin S.seamCount) :
    PartialDiffeomorph signedCollarModel T.cutCarrier.model (Torus × ℝ) (T.components.piece i) ∞ :=
  (Wd.exists_gseam S hδ hδ1 a).choose

theorem gseam_source (a : P.pieces.MI × Fin S.seamCount) :
    (Wd.gseam S hδ hδ1 a).source = signedCollarSource :=
  (Wd.exists_gseam S hδ hδ1 a).choose_spec.1

theorem gseam_apply (a : P.pieces.MI × Fin S.seamCount) (y : Torus × ℝ) :
    Wd.gseam S hδ hδ1 a y = Wd.χ a.1 (S.seam a.2 (y.1, δ * y.2)) :=
  (Wd.exists_gseam S hδ hδ1 a).choose_spec.2.1 y

theorem gseam_interior (a : P.pieces.MI × Fin S.seamCount) :
    ∀ y ∈ (Wd.gseam S hδ hδ1 a).target, T.cutCarrier.model.IsInteriorPoint y :=
  (Wd.exists_gseam S hδ hδ1 a).choose_spec.2.2

theorem gseam_neg (a : P.pieces.MI × Fin S.seamCount) (t : Torus) (s : ℝ) (hs : s ≤ 0)
    (h1 : -1 < s) :
    Wd.gseam S hδ hδ1 a (t, s) = Wd.map S hδ hδ1 hδ0 (.inr (.inl (a.1, (S.side a.2 true).1)))
      (((S.base (S.side a.2 true).1).shrink hδ hδ1).collar (S.side a.2 true).2
        (t.1, halfPoint (-s) (neg_nonneg.2 hs)), t.2) := by
  rw [Wd.gseam_apply, S.seam_neg a.2 t (δ * s) (by nlinarith) (by nlinarith)]
  change _ = Wd.χ a.1 (S.map (S.side a.2 true).1 (((S.base (S.side a.2 true).1).shrink hδ
    hδ1).collar (S.side a.2 true).2 (t.1, halfPoint (-s) (neg_nonneg.2 hs)), t.2))
  rw [shrink_collar_halfPoint]
  have e : halfPoint (-(δ * s)) (neg_nonneg.2 (mul_nonpos_of_nonneg_of_nonpos hδ.le hs)) =
      halfPoint (δ * -s) (mul_nonneg hδ.le (neg_nonneg.2 hs)) :=
    halfSpace_ext (by change -(δ * s) = δ * -s; ring)
  rw [e]

theorem gseam_pos (a : P.pieces.MI × Fin S.seamCount) (t : Torus) (s : ℝ) (hs : 0 ≤ s)
    (h1 : s < 1) :
    Wd.gseam S hδ hδ1 a (t, s) = Wd.map S hδ hδ1 hδ0 (.inr (.inl (a.1, (S.side a.2 false).1)))
      (((S.base (S.side a.2 false).1).shrink hδ hδ1).collar (S.side a.2 false).2
        ((S.matching a.2 t).1, halfPoint s hs), (S.matching a.2 t).2) := by
  rw [Wd.gseam_apply, S.seam_pos a.2 t (δ * s) (mul_nonneg hδ.le hs) (by nlinarith)]
  change _ = Wd.χ a.1 (S.map (S.side a.2 false).1 (((S.base (S.side a.2 false).1).shrink hδ
    hδ1).collar (S.side a.2 false).2 ((S.matching a.2 t).1, halfPoint s hs), (S.matching a.2 t).2))
  rw [shrink_collar_halfPoint]

include hS1 in
theorem sides_bijective :
    Bijective (Sum.elim (uncurry (Wd.side S e₀)) (Sum.elim
      (uncurry fun (a : P.pieces.MI × Fin S.seamCount) b => mobSide T i P S a.1 (S.side a.2 b))
      fun s : T.OwnedSide i => (⟨.inr (.inr s), (0 : Fin 2)⟩ : MSide T i P S))) := by
  constructor
  · rintro (⟨c | s, b⟩ | ⟨a, b⟩ | s) (⟨c' | s', b'⟩ | ⟨a', b'⟩ | s') h
    · change toSide T i P S e₀ (P.cutSide c (!b)) = toSide T i P S e₀ (P.cutSide c' (!b')) at h
      have h' : (c, !b) = (c', !b') := P.cutSide_injective (toSide_injective T i P S e₀ h)
      obtain ⟨rfl, hb⟩ := Prod.mk.inj h'
      rw [Bool.not_inj hb]
    · cases b'
      · change toSide T i P S e₀ (P.cutSide c (!b)) = toSide T i P S e₀ (Wd.β s') at h
        exact absurd (toSide_injective T i P S e₀ h) (Wd.βh s' c (!b))
      · exact absurd h (toSide_ne_col T i P S e₀ _ s' 1)
    · exact absurd h (toSide_ne_gside T i P S e₀ _ a'.1 a'.2 b')
    · exact absurd h (toSide_ne_col T i P S e₀ _ s' 0)
    · cases b
      · change toSide T i P S e₀ (Wd.β s) = toSide T i P S e₀ (P.cutSide c' (!b')) at h
        exact absurd (toSide_injective T i P S e₀ h).symm (Wd.βh s c' (!b'))
      · exact absurd h.symm (toSide_ne_col T i P S e₀ _ s 1)
    · cases b <;> cases b'
      · change toSide T i P S e₀ (Wd.β s) = toSide T i P S e₀ (Wd.β s') at h
        rw [Wd.β_inj (toSide_injective T i P S e₀ h)]
      · exact absurd h (toSide_ne_col T i P S e₀ _ s' 1)
      · exact absurd h.symm (toSide_ne_col T i P S e₀ _ s 1)
      · rw [(col_inj T i P S h).1]
    · cases b
      · exact absurd h (toSide_ne_gside T i P S e₀ _ a'.1 a'.2 b')
      · exact absurd h.symm (mobSide_ne_col T i P S _ _ s 1)
    · cases b
      · exact absurd h (toSide_ne_col T i P S e₀ _ s' 0)
      · exact absurd (col_inj T i P S h).2 (by decide)
    · exact absurd h.symm (toSide_ne_gside T i P S e₀ _ a.1 a.2 b)
    · cases b'
      · exact absurd h.symm (toSide_ne_gside T i P S e₀ _ a.1 a.2 b)
      · exact absurd h (mobSide_ne_col T i P S _ _ s' 1)
    · obtain ⟨h1, h2⟩ := mobSide_inj T i P S h
      have h3 := S.sides_bijective.1 (a₁ := Sum.inl (a.2, b)) (a₂ := Sum.inl (a'.2, b')) h2
      obtain ⟨h4, rfl⟩ := Prod.mk.inj (Sum.inl_injective h3)
      have h1' : a.1 = a'.1 := h1
      rw [Prod.ext h1' h4]
    · exact absurd h (mobSide_ne_col T i P S _ _ s' 0)
    · exact absurd h.symm (toSide_ne_col T i P S e₀ _ s 0)
    · cases b'
      · exact absurd h.symm (toSide_ne_col T i P S e₀ _ s 0)
      · exact absurd (col_inj T i P S h).2 (by decide)
    · exact absurd h.symm (mobSide_ne_col T i P S _ _ s 0)
    · rw [(col_inj T i P S h).1]
  · have hP : ∀ w : P.pieces.Side, ∃ z, Sum.elim (uncurry (Wd.side S e₀)) (Sum.elim
        (uncurry fun (a : P.pieces.MI × Fin S.seamCount) b => mobSide T i P S a.1 (S.side a.2 b))
        fun s : T.OwnedSide i => (⟨.inr (.inr s), (0 : Fin 2)⟩ : MSide T i P S)) z =
          toSide T i P S e₀ w := by
      intro w
      by_cases hb : P.IsBottom w
      · obtain ⟨s, hs⟩ := Wd.β_surj w hb
        exact ⟨Sum.inl (Sum.inr s, false), by rw [← hs]; rfl⟩
      · simp only [MobiusCore.IsBottom, not_forall, not_not] at hb
        obtain ⟨c, b, hcb⟩ := hb
        refine ⟨Sum.inl (Sum.inl c, !b), ?_⟩
        change toSide T i P S e₀ (P.cutSide c (!!b)) = _
        rw [Bool.not_not, hcb]
    rintro ⟨j | ⟨m, a⟩ | s, l⟩
    · exact hP (.inl ⟨j, l⟩)
    · obtain ⟨z₀, hz₀⟩ := S.sides_bijective.2 ⟨a, l⟩
      rcases z₀ with ⟨c, b⟩ | e
      · refine ⟨Sum.inr (Sum.inl ((m, c), b)), ?_⟩
        change mobSide T i P S m (S.side c b) = _
        rw [show S.side c b = ⟨a, l⟩ from hz₀]
        rfl
      · have he : S.externalSide e = ⟨a, l⟩ := hz₀
        rw [hS1 e] at he
        obtain ⟨z, hz⟩ := hP (.inr m)
        refine ⟨z, hz.trans ?_⟩
        change mobSide T i P S m (S.externalSide e₀) = _
        rw [he]
        rfl
    · rcases l with ⟨_ | _ | k, hk⟩
      · exact ⟨Sum.inr (Sum.inr s), rfl⟩
      · exact ⟨Sum.inl (Sum.inr s, true), rfl⟩
      · exact absurd hk (by change ¬ (k + 2 < 2); omega)

theorem collarRange (s : T.OwnedSide i) :
    range (sideTorus ((planarBase.{u} 2 (Or.inl rfl)).shrink (WiringData.eta_pos_of D hδ)
      (Wd.eta_le hδ0)) 1 (collarPieceMap (D.level 0) (Wd.K s))) =
        F.projection ⁻¹' P.zeroSec (Wd.β s) := by
  rw [← Wd.top_range s]
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    rw [sideTorus_collarPiece]
    exact ⟨(t.1⁻¹, t.2), rfl⟩
  · rintro ⟨p, rfl⟩
    refine ⟨(p.1⁻¹, p.2), ?_⟩
    rw [sideTorus_collarPiece]
    simp only [inv_inv]
    rfl

theorem mem_collarTop {s : T.OwnedSide i} {z : T.components.piece i}
    (hz : D.level 0 ≤ portHeight F D z) (hzK : z ∈ range (collarPieceMap (D.level 0) (Wd.K s)))
    {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) :
    ∃ t, z = sideTorus ((planarBase.{u} 2 (Or.inl rfl)).shrink hη hη1) 1
      (collarPieceMap (D.level 0) (Wd.K s)) t := by
  obtain ⟨q', rfl⟩ := hzK
  change D.level 0 ≤ portHeight F D (Wd.K s (annulusProduct (D.level 0) q')) at hz
  change ∃ t, Wd.K s (annulusProduct (D.level 0) q') = _
  generalize annulusProduct (D.level 0) q' = w at hz ⊢
  have hmem : (Wd.K s w).val ∈ connectedComponentIn (lowSet F D)
      (T.sideCollar s.val (1, halfZero)) := by
    rw [← Wd.region s]
    exact ⟨w, rfl⟩
  have hle := val_mem_lowSet.mp (connectedComponentIn_subset _ _ hmem)
  have htop := Wd.top_eq s w (le_antisymm hle hz)
  obtain ⟨⟨a, b⟩, c⟩ := w
  change c = topPoint D at htop
  subst htop
  refine ⟨(a⁻¹, b), ?_⟩
  rw [sideTorus_collarPiece]
  simp only [inv_inv]
  rfl

theorem level_le_Φ (j : P.pieces.PI) (q) : D.level 0 ≤ portHeight F D (Wd.Φ j q) := by
  change D.level 0 ≤ D.f (F.projection (Wd.Φ j q))
  rw [Wd.projΦ]
  exact P.pieces.level_le_ιP j q.1

theorem exists_core_χ (m : P.pieces.MI) (y : mobiusBundleCarrier.{u}.Carrier) :
    ∃ x, P.pieces.ιM m x = F.projection (Wd.χ m y) := by
  have h : Wd.χ m y ∈ range (Wd.χ m) := mem_range_self y
  rw [Wd.rangeχ m] at h
  exact h

theorem level_le_χ (m : P.pieces.MI) (y) : D.level 0 ≤ portHeight F D (Wd.χ m y) := by
  obtain ⟨x, hx⟩ := Wd.exists_core_χ m y
  change D.level 0 ≤ D.f (F.projection (Wd.χ m y))
  rw [← hx]
  exact P.pieces.level_le_ιM m x

theorem covers_map : ⋃ x, range (Wd.map S hδ hδ1 hδ0 x) = univ := by
  refine eq_univ_of_forall fun z => ?_
  rcases le_total (portHeight F D z) (D.level 0) with hz | hz
  · obtain ⟨s, hs⟩ := Wd.cover z hz
    obtain ⟨q, hq⟩ : z.val ∈ range (fun q => (Wd.K s q).val) := by
      rw [Wd.region s]
      exact hs
    have hzK : z ∈ range (collarPieceMap (D.level 0) (Wd.K s)) := by
      rw [range_collarPieceMap]
      exact ⟨q, Subtype.ext hq⟩
    exact mem_iUnion.mpr ⟨.inr (.inr s), hzK⟩
  · obtain ⟨y, hy⟩ := P.exists_pt_of_level hz
    rcases y with ⟨j, x⟩ | ⟨m, x⟩
    · have hzΦ : z ∈ range (Wd.Φ j) := by
        rw [Wd.rangeΦ j]
        exact ⟨x, hy⟩
      exact mem_iUnion.mpr ⟨.inl j, hzΦ⟩
    · have hzχ : z ∈ range (Wd.χ m) := by
        rw [Wd.rangeχ m]
        exact ⟨x, hy⟩
      obtain ⟨w, rfl⟩ := hzχ
      have hw : w ∈ ⋃ a, range (S.map a) := S.covers ▸ mem_univ w
      obtain ⟨a, q, rfl⟩ := mem_iUnion.mp hw
      exact mem_iUnion.mpr ⟨.inr (.inl (m, a)), q, rfl⟩

theorem port_collar (e : T.OwnedSide i) (p : Torus × EuclideanHalfSpace 1)
    (hp : p ∈ halfCollarSource) :
    (collarPieceMap (D.level 0) (Wd.K e) (((planarBase.{u} 2 (Or.inl rfl)).shrink
      (WiringData.eta_pos_of D hδ) (Wd.eta_le hδ0)).collar 0 (p.1.1, p.2), p.1.2)).val =
      ((T.reparam fun _ => Diffeomorph.refl torusModel Torus ∞).shrink hδ hδ1).sideCollar
        e.val p := by
  obtain ⟨⟨t, v⟩, h⟩ := p
  have hr : 0 ≤ h.val 0 := h.2
  have hh : halfPoint (h.val 0) hr = h := halfPoint_eq_self h hr rfl
  have hp' : h.val 0 < 1 := hp
  rw [sideCollar_shrink_reparam]
  change (collarPieceMap (D.level 0) (Wd.K e) (((planarBase.{u} 2 (Or.inl rfl)).shrink
    (WiringData.eta_pos_of D hδ) (Wd.eta_le hδ0)).collar 0 (t, h), v)).val =
      T.sideCollar e.val ((t, v), halfSpaceScale hδ h)
  rw [← hh, collarPiece_port_zero (D.level 0) (Wd.K e) hδ (hδ0.trans Wd.δ₀_le_level)
    (WiringData.eta_pos_of D hδ) (Wd.eta_le hδ0) t v hr hp', halfSpaceScale_halfPoint]
  exact Wd.lowK e (t, v) _ (by
    change δ * h.val 0 < Wd.δ₀
    nlinarith [Wd.δ₀_pos])

include hδ1 in
theorem external_local (e : T.OwnedSide i) (t : Torus) :
    IsLocalDiffeomorphAt ((SurfaceModel.model (planarBase.{u} 2 (Or.inl rfl)).surface.kind).prod
      (𝓡 1)) T.cutCarrier.model ∞
      (collarPieceMap (D.level 0) (Wd.K e))
      (((planarBase.{u} 2 (Or.inl rfl)).shrink (WiringData.eta_pos_of D hδ)
        (Wd.eta_le hδ0)).collar 0 (t.1, halfZero), t.2) := by
  let c : PartialDiffeomorph halfCollarModel T.cutCarrier.model (Torus × EuclideanHalfSpace 1)
      (T.components.piece i) ∞ :=
    ((T.reparam fun _ => Diffeomorph.refl torusModel Torus ∞).shrink hδ hδ1).pieceCollar
      i (portEquiv T i hδ hδ1 e)
  have hcs : c.source = halfCollarSource := TorusPresentation.pieceCollar_source _ _ _
  have hca : ∀ q ∈ halfCollarSource, (c q).val =
      ((T.reparam fun _ => Diffeomorph.refl torusModel Torus ∞).shrink hδ hδ1).sideCollar
        e.val q := fun q hq => TorusPresentation.pieceCollar_apply _ _ _ hq
  refine isLocalDiffeomorphAt_of_comp_eq (collarPieceMap (D.level 0) (Wd.K e))
    (trivCollar (S := (planarBase.{u} 2 (Or.inl rfl)).surface)
      (((planarBase.{u} 2 (Or.inl rfl)).shrink (WiringData.eta_pos_of D hδ)
        (Wd.eta_le hδ0)).collar 0)
      (Diffeomorph.refl ((SurfaceModel.model (planarBase.{u} 2 (Or.inl rfl)).surface.kind).prod
        (𝓡 1)) ((planarBase.{u} 2 (Or.inl rfl)).surface.Carrier × Circle) ∞))
    c (p := (t, halfZero)) ?_ ?_ ?_
  · have hA := trivCollar_source (S := (planarBase.{u} 2 (Or.inl rfl)).surface)
      (((planarBase.{u} 2 (Or.inl rfl)).shrink (WiringData.eta_pos_of D hδ)
        (Wd.eta_le hδ0)).source_eq 0)
      (Diffeomorph.refl ((SurfaceModel.model (planarBase.{u} 2 (Or.inl rfl)).surface.kind).prod
        (𝓡 1)) ((planarBase.{u} 2 (Or.inl rfl)).surface.Carrier × Circle) ∞)
    rw [hA]
    exact zero_mem_halfCollarSource t
  · rw [hcs]
    exact zero_mem_halfCollarSource t
  · intro q hq
    have hq2 : q ∈ halfCollarSource := by
      have h := hq.2
      rwa [hcs] at h
    apply Subtype.ext
    rw [hca q hq2]
    exact Wd.port_collar hδ hδ1 hδ0 e q hq2

include hSc in
theorem collarInj (c : Fin P.cutCount ⊕ T.OwnedSide i) (b : Bool) :
    InjOn (fun p : Torus × EuclideanHalfSpace 1 => Wd.map S hδ hδ1 hδ0 (Wd.side S e₀ c b).1
      ((Wd.base S hδ hδ1 hδ0 _).collar (Wd.side S e₀ c b).2 (p.1.1, p.2), p.1.2))
      halfCollarSource := by
  rcases c with c | s
  · exact Wd.injOn_toSide S e₀ hSc hδ hδ1 hδ0 (P.cutSide c (!b))
  · cases b
    · exact Wd.injOn_toSide S e₀ hSc hδ hδ1 hδ0 (Wd.β s)
    · exact injOn_collar_of_injective _ (1 : Fin 2)
        (injective_collarPieceMap (D.level 0) (Wd.injK s))

include hSc in
theorem sync_left (c : Fin P.cutCount ⊕ T.OwnedSide i) (t v : Circle) (r : ℝ) (hr : 0 ≤ r)
    (hr1 : r < 1) :
    Wd.map S hδ hδ1 hδ0 (Wd.side S e₀ c true).1 ((Wd.base S hδ hδ1 hδ0 _).collar
      (Wd.side S e₀ c true).2 (t, halfPoint r hr), v) =
      Wd.flow c (-(δ * r)) (Wd.map S hδ hδ1 hδ0 (Wd.side S e₀ c true).1
        ((Wd.base S hδ hδ1 hδ0 _).collar (Wd.side S e₀ c true).2 (t, halfZero), v)) := by
  rcases c with c | s
  · have h := Wd.sync_toSide_cut S e₀ hSc hδ hδ1 hδ0 (P.cutSide c false) c false rfl t v r hr hr1
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    exact h
  · exact collarPiece_sync_one (D.level 0) (Wd.K s)
      (fun a x => (MobiusCore.bottomLift F P (Wd.β s) (Wd.βh s)).flow a x) hδ hδ0
      (hδ0.trans Wd.δ₀_le_level) (Wd.topK s) (WiringData.eta_pos_of D hδ) (Wd.eta_le hδ0) t v hr
      hr1

include hSc in
theorem sync_right (c : Fin P.cutCount ⊕ T.OwnedSide i) (t v : Circle) (r : ℝ) (hr : 0 ≤ r)
    (hr1 : r < 1) :
    Wd.map S hδ hδ1 hδ0 (Wd.side S e₀ c false).1 ((Wd.base S hδ hδ1 hδ0 _).collar
      (Wd.side S e₀ c false).2 (t, halfPoint r hr), v) =
      Wd.flow c (δ * r) (Wd.map S hδ hδ1 hδ0 (Wd.side S e₀ c false).1
        ((Wd.base S hδ hδ1 hδ0 _).collar (Wd.side S e₀ c false).2 (t, halfZero), v)) := by
  rcases c with c | s
  · have h := Wd.sync_toSide_cut S e₀ hSc hδ hδ1 hδ0 (P.cutSide c true) c true rfl t v r hr hr1
    simp only [↓reduceIte] at h
    exact h
  · exact Wd.sync_toSide_bottom S e₀ hSc hδ hδ1 hδ0 (Wd.β s) (Wd.βh s) t v r hr hr1

include hSc in
theorem range_eq (c : Fin P.cutCount ⊕ T.OwnedSide i) :
    range (sideTorus (Wd.base S hδ hδ1 hδ0 (Wd.side S e₀ c true).1) (Wd.side S e₀ c true).2
      (Wd.map S hδ hδ1 hδ0 (Wd.side S e₀ c true).1)) =
    range (sideTorus (Wd.base S hδ hδ1 hδ0 (Wd.side S e₀ c false).1) (Wd.side S e₀ c false).2
      (Wd.map S hδ hδ1 hδ0 (Wd.side S e₀ c false).1)) := by
  rcases c with c | s
  · have e : F.projection ⁻¹' P.zeroSec (P.cutSide c false) =
        F.projection ⁻¹' P.zeroSec (P.cutSide c true) := by
      rw [P.zeroSec_eq_cut (c := c) (b := false) rfl, P.zeroSec_eq_cut (c := c) (b := true) rfl]
    exact ((Wd.range_toSide S e₀ hSc hδ hδ1 hδ0 (P.cutSide c false)).trans e).trans
      (Wd.range_toSide S e₀ hSc hδ hδ1 hδ0 (P.cutSide c true)).symm
  · exact (Wd.collarRange hδ hδ0 s).trans (Wd.range_toSide S e₀ hSc hδ hδ1 hδ0 (Wd.β s)).symm

include hSc in
theorem injOn_sweep (c : Fin P.cutCount ⊕ T.OwnedSide i) :
    InjOn (fun y : Torus × ℝ => Wd.flow c (δ * y.2)
      (sideTorus (Wd.base S hδ hδ1 hδ0 (Wd.side S e₀ c true).1) (Wd.side S e₀ c true).2
        (Wd.map S hδ hδ1 hδ0 (Wd.side S e₀ c true).1) y.1)) signedCollarSource := by
  rcases c with c | s
  · set w := P.cutSide c false with hw
    refine injOn_liftSweep F (P.cut_source c) (MobiusCore.cutLift F P c)
      (y := sideTorus (Wd.base S hδ hδ1 hδ0 (toSide T i P S e₀ w).1) (toSide T i P S e₀ w).2
        (Wd.map S hδ hδ1 hδ0 (toSide T i P S e₀ w).1))
      (injective_sideTorus_of_injOn _ _ (Wd.injOn_toSide S e₀ hSc hδ hδ1 hδ0 w)) (fun t => ?_) hδ
      (by rw [MobiusCore.cutLift_width]; exact hδ0.trans Wd.δ₀_le_width)
    have hm : sideTorus (Wd.base S hδ hδ1 hδ0 (toSide T i P S e₀ w).1) (toSide T i P S e₀ w).2
        (Wd.map S hδ hδ1 hδ0 (toSide T i P S e₀ w).1) t ∈ range (sideTorus
          (Wd.base S hδ hδ1 hδ0 (toSide T i P S e₀ w).1) (toSide T i P S e₀ w).2
          (Wd.map S hδ hδ1 hδ0 (toSide T i P S e₀ w).1)) := ⟨t, rfl⟩
    rw [Wd.range_toSide S e₀ hSc hδ hδ1 hδ0, P.zeroSec_eq_cut hw.symm] at hm
    obtain ⟨θ, hθ⟩ := hm
    exact ⟨θ, hθ.symm⟩
  · refine injOn_liftSweep F (P.bottomBicollar_spec (Wd.β s) (Wd.βh s)).1
      (MobiusCore.bottomLift F P (Wd.β s) (Wd.βh s))
      (y := sideTorus ((planarBase.{u} 2 (Or.inl rfl)).shrink (WiringData.eta_pos_of D hδ)
        (Wd.eta_le hδ0)) 1 (collarPieceMap (D.level 0) (Wd.K s)))
      (injective_sideTorus _ 1 (injective_collarPieceMap (D.level 0) (Wd.injK s)))
      (fun t => ?_) hδ (by rw [MobiusCore.bottomLift_width]; exact hδ0.trans Wd.δ₀_le_width)
    have h : sideTorus ((planarBase.{u} 2 (Or.inl rfl)).shrink (WiringData.eta_pos_of D hδ)
        (Wd.eta_le hδ0)) 1 (collarPieceMap (D.level 0) (Wd.K s)) t ∈ range (sideTorus
          ((planarBase.{u} 2 (Or.inl rfl)).shrink (WiringData.eta_pos_of D hδ) (Wd.eta_le hδ0)) 1
            (collarPieceMap (D.level 0) (Wd.K s))) := ⟨t, rfl⟩
    rw [Wd.collarRange hδ hδ0 s, P.zeroSec_eq (Wd.βh s)] at h
    obtain ⟨θ, hθ⟩ := h
    exact ⟨θ, hθ.symm⟩

include hSc in
theorem exists_cut_of_core {z : T.components.piece i} (y y' : P.pieces.Pt)
    (hne : P.pieces.piece y ≠ P.pieces.piece y') (he : P.pieces.pt y = P.pieces.pt y')
    (hz : F.projection z = (P.pieces.pt y).val) :
    ∃ c t, z = sideTorus (Wd.base S hδ hδ1 hδ0 (Wd.side S e₀ (.inl c) true).1)
      (Wd.side S e₀ (.inl c) true).2 (Wd.map S hδ hδ1 hδ0 (Wd.side S e₀ (.inl c) true).1) t := by
  obtain ⟨c, τ, hc⟩ := P.overlap y y' hne he
  have hm : z ∈ range (sideTorus (Wd.base S hδ hδ1 hδ0 (toSide T i P S e₀ (P.cutSide c false)).1)
      (toSide T i P S e₀ (P.cutSide c false)).2
      (Wd.map S hδ hδ1 hδ0 (toSide T i P S e₀ (P.cutSide c false)).1)) := by
    rw [Wd.range_toSide S e₀ hSc hδ hδ1 hδ0, P.zeroSec_eq_cut (c := c) (b := false) rfl]
    exact ⟨τ, (hz.trans hc).symm⟩
  obtain ⟨t, ht⟩ := hm
  exact ⟨c, t, ht.symm⟩

include hSc in
theorem overlap (x x' : MIdx T i P S) (q : (Wd.base S hδ hδ1 hδ0 x).surface.Carrier × Circle)
    (q' : (Wd.base S hδ hδ1 hδ0 x').surface.Carrier × Circle)
    (h : Wd.map S hδ hδ1 hδ0 x q = Wd.map S hδ hδ1 hδ0 x' q') :
    (⟨x, q⟩ : Σ x, (Wd.base S hδ hδ1 hδ0 x).surface.Carrier × Circle) = ⟨x', q'⟩ ∨
      (∃ c t, Wd.map S hδ hδ1 hδ0 x q = sideTorus (Wd.base S hδ hδ1 hδ0 (Wd.side S e₀ c true).1)
        (Wd.side S e₀ c true).2 (Wd.map S hδ hδ1 hδ0 (Wd.side S e₀ c true).1) t) ∨
      ∃ c t, Wd.map S hδ hδ1 hδ0 x q = Wd.gseam S hδ hδ1 c (t, 0) := by
  have hcut : ∀ (y y' : P.pieces.Pt), P.pieces.piece y ≠ P.pieces.piece y' →
      P.pieces.pt y = P.pieces.pt y' → F.projection (Wd.map S hδ hδ1 hδ0 x q) =
        (P.pieces.pt y).val → (∃ c t, Wd.map S hδ hδ1 hδ0 x q = sideTorus
          (Wd.base S hδ hδ1 hδ0 (Wd.side S e₀ c true).1) (Wd.side S e₀ c true).2
          (Wd.map S hδ hδ1 hδ0 (Wd.side S e₀ c true).1) t) := by
    intro y y' hne he hz
    obtain ⟨c, t, ht⟩ := Wd.exists_cut_of_core S e₀ hSc hδ hδ1 hδ0 y y' hne he hz
    exact ⟨Sum.inl c, t, ht⟩
  have htop : ∀ (s : T.OwnedSide i), D.level 0 ≤ portHeight F D (Wd.map S hδ hδ1 hδ0 x q) →
      Wd.map S hδ hδ1 hδ0 x q ∈ range (collarPieceMap (D.level 0) (Wd.K s)) →
      (∃ c t, Wd.map S hδ hδ1 hδ0 x q = sideTorus
          (Wd.base S hδ hδ1 hδ0 (Wd.side S e₀ c true).1) (Wd.side S e₀ c true).2
          (Wd.map S hδ hδ1 hδ0 (Wd.side S e₀ c true).1) t) := by
    intro s hz hzK
    obtain ⟨t, ht⟩ := Wd.mem_collarTop hz hzK (WiringData.eta_pos_of D hδ) (Wd.eta_le hδ0)
    exact ⟨Sum.inr s, t, ht⟩
  rcases x with j | ⟨m, a⟩ | s <;> rcases x' with j' | ⟨m', a'⟩ | s'
  · change Wd.Φ j q = Wd.Φ j' q' at h
    by_cases hjj : j = j'
    · subst hjj
      left
      rw [Wd.injΦ j h]
    · right
      left
      exact hcut (.inl ⟨j, q.1⟩) (.inl ⟨j', q'.1⟩) (fun e => hjj (Sum.inl_injective e))
        (Subtype.ext ((Wd.projΦ j q).symm.trans ((congrArg F.projection h).trans
          (Wd.projΦ j' q')))) (Wd.projΦ j q)
  · change Wd.Φ j q = Wd.χ m' (S.map a' q') at h
    right
    left
    obtain ⟨x₀, hx₀⟩ := Wd.exists_core_χ m' (S.map a' q')
    exact hcut (.inl ⟨j, q.1⟩) (.inr ⟨m', x₀⟩) Sum.inl_ne_inr
      (Subtype.ext ((Wd.projΦ j q).symm.trans ((congrArg F.projection h).trans hx₀.symm)))
      (Wd.projΦ j q)
  · right
    left
    exact htop s' (Wd.level_le_Φ j q) ⟨q', h.symm⟩
  · change Wd.χ m (S.map a q) = Wd.Φ j' q' at h
    right
    left
    obtain ⟨x₀, hx₀⟩ := Wd.exists_core_χ m (S.map a q)
    exact hcut (.inr ⟨m, x₀⟩) (.inl ⟨j', q'.1⟩) Sum.inr_ne_inl
      (Subtype.ext (hx₀.trans ((congrArg F.projection h).trans (Wd.projΦ j' q')))) hx₀.symm
  · change Wd.χ m (S.map a q) = Wd.χ m' (S.map a' q') at h
    by_cases hmm : m = m'
    · subst hmm
      rcases S.overlap a a' q q' (Wd.injχ m h) with h' | ⟨c, t, h'⟩
      · left
        obtain ⟨rfl, hq⟩ := Sigma.mk.inj_iff.mp h'
        rw [eq_of_heq hq]
      · right
        right
        refine ⟨(m, c), t, ?_⟩
        rw [Wd.gseam_apply, mul_zero]
        exact congrArg (Wd.χ m) h'
    · right
      left
      obtain ⟨x₀, hx₀⟩ := Wd.exists_core_χ m (S.map a q)
      obtain ⟨x₀', hx₀'⟩ := Wd.exists_core_χ m' (S.map a' q')
      exact hcut (.inr ⟨m, x₀⟩) (.inr ⟨m', x₀'⟩) (fun e => hmm (Sum.inr_injective e))
        (Subtype.ext (hx₀.trans ((congrArg F.projection h).trans hx₀'.symm))) hx₀.symm
  · right
    left
    exact htop s' (Wd.level_le_χ m (S.map a q)) ⟨q', h.symm⟩
  · right
    left
    exact htop s (h ▸ Wd.level_le_Φ j' q') ⟨q, rfl⟩
  · right
    left
    exact htop s (h ▸ Wd.level_le_χ m' (S.map a' q')) ⟨q, rfl⟩
  · change collarPieceMap (D.level 0) (Wd.K s) q = collarPieceMap (D.level 0) (Wd.K s') q' at h
    by_cases hss : s = s'
    · subst hss
      left
      rw [injective_collarPieceMap (D.level 0) (Wd.injK s) h]
    · exfalso
      have hm : ∀ (s'' : T.OwnedSide i) (q'' : (planarBase.{u} 2 (Or.inl rfl)).surface.Carrier ×
          Circle), (collarPieceMap (D.level 0) (Wd.K s'') q'').val ∈
            connectedComponentIn (lowSet F D) (T.sideCollar s''.val (1, halfZero)) :=
        fun s'' q'' => by
          rw [← Wd.region s'']
          exact ⟨_, rfl⟩
      exact hss (Wd.disjoint s s' _ (hm s q) (h ▸ hm s' q'))

include hS1 hSc in
def blockData :
    BlockData (((T.reparam fun _ => Diffeomorph.refl torusModel Torus ∞).shrink hδ hδ1).Component
      i) where
  ι := MIdx T i P S
  nonempty := by
    obtain ⟨x⟩ := Wd.nonempty
    rcases x with j | m
    · exact ⟨.inl j⟩
    · exact ⟨.inr (.inl (m, ⟨0, S.count_pos⟩))⟩
  γ := Fin P.cutCount ⊕ T.OwnedSide i
  η := P.pieces.MI × Fin S.seamCount
  ε := T.OwnedSide i
  kind := mkind T i P S
  kind_mem := kind_mem S
  base := Wd.base S hδ hδ1 hδ0
  map := Wd.map S hδ hδ1 hδ0
  smooth := Wd.smooth_map S hδ hδ1 hδ0
  mfderiv_bijective := Wd.bijective_map S hδ hδ1 hδ0
  covers := Wd.covers_map S hδ hδ1 hδ0
  side := Wd.side S e₀
  gside a b := mobSide T i P S a.1 (S.side a.2 b)
  ext s := ⟨.inr (.inr s), (0 : Fin 2)⟩
  sides_bijective := Wd.sides_bijective S e₀ hS1
  collarInj := Wd.collarInj S e₀ hSc hδ hδ1 hδ0
  flow := Wd.flow
  flow_add := Wd.flow_add
  rate := δ
  sync_left := Wd.sync_left S e₀ hSc hδ hδ1 hδ0
  sync_right := Wd.sync_right S e₀ hSc hδ hδ1 hδ0
  range_eq := Wd.range_eq S e₀ hSc hδ hδ1 hδ0
  injOn := Wd.injOn_sweep S e₀ hSc hδ hδ1 hδ0
  gmatching a := S.matching a.2
  gseam := Wd.gseam S hδ hδ1
  gseam_source := Wd.gseam_source S hδ hδ1
  gseam_neg := Wd.gseam_neg S hδ hδ1 hδ0
  gseam_pos := Wd.gseam_pos S hδ hδ1 hδ0
  gseam_interior a y hy := Wd.gseam_interior S hδ hδ1 a y hy
  external_local e t := Wd.external_local hδ hδ1 hδ0 e t
  overlap := Wd.overlap S e₀ hSc hδ hδ1 hδ0

end MixedWiringData

end GC.Seifert.Wiring

namespace GC.Seifert.Wiring

variable {W : CompactCarrier.{u}}

theorem exists_componentRefinement_mobius (T : TorusPresentation W) (i : Fin T.components.count)
    (F : CircleFibration T.cutCarrier (T.components.piece i)) {D : BaseMorseData F.base}
    (P : MobiusCore D) (S : EmbeddedPieceSystem mobiusBundleCarrier.{u})
    (e₀ : Fin S.externalCount) (hS1 : ∀ e, e = e₀)
    (hSc : ∀ p, p ∈ halfCollarSource → S.map (S.externalSide e₀).1
      ((S.base _).collar (S.externalSide e₀).2 (p.1.1, p.2), p.1.2) = mobiusExternalCollar p)
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
          L.flow (if b then s else -s) (χ (mobiusExternalCollar (t, halfZero)))) :
    ∃ δ₀ > 0, ∀ (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1), δ ≤ δ₀ →
      Nonempty (((T.reparam fun _ => Diffeomorph.refl torusModel Torus ∞).shrink hδ hδ1)
        |>.ComponentRefinement i) := by
  have : Fact (0 < D.level 0) := ⟨D.level_zero_pos⟩
  obtain ⟨Wd⟩ := nonempty_mixedWiringData T i F P hMD5
  exact ⟨Wd.δ₀, Wd.δ₀_pos, fun δ hδ hδ1 hδ0 =>
    ⟨(Wd.blockData S e₀ hS1 hSc hδ hδ1 hδ0).toComponentRefinement (portEquiv T i hδ hδ1)
      fun e p hp => Wd.port_collar hδ hδ1 hδ0 e p hp⟩⟩

end GC.Seifert.Wiring
