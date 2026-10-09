import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ElementarizeWiringCore
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ElementarizeWiringTopology
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ElementarizeWiringSeam
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.PlanarBundlePieces
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ElementarizeWiringEmbedding
import DifferentialGeometry.Topology.Manifold.ImmersionDifferential

/-!
# Synchronised planar pieces over a planar core

Lane P1W (P1 wiring), tier T2, the per-piece inputs.

For a planar core `P : PlanarCore D` of Morse data on the base of a circle fibration `F`, the piece
maps `P.ι j = val ∘ P.inclusion j` embed the planar bases into the interior of the base
(`isSmoothEmbedding_ι`; its proof needs that the composite of a smooth embedding into the core with
the inclusion of the core is a smooth embedding, `isSmoothEmbedding_core_val_comp`, proved in
`ElementarizeWiringEmbedding` through the ambient charts of the core). Every side of a piece is
either a cut side or a bottom side (`IsBottom`), whose collar is a level-0 bicollar
(`bottomBicollar`, `bottomSigma`). Each cut and each bottom side gets one lifted bicollar
(`cutLift`, `bottomLift`, width `1/16`). MD5's `exists_syncedPiece` then gives a product map `Φ_j :
Q_j × S¹ → U` over `P.ι j` onto `π⁻¹ (range P.ι j)`, synchronised on every cut side with the flow of
the cut and on every bottom side with the flow of its level bicollar (`exists_planarPieceMap`). The
points of height `ℓ` are exactly the zero sections of the bottom sides, each on exactly one
(`exists_bottom_of_level`, `bottom_unique`), and the side torus of a piece over a bicollar circle is
the preimage of that circle (`range_sideTorus_eq`).
-/

set_option autoImplicit false

noncomputable section
open Set Function Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert

theorem isSmoothEmbedding_core_val_comp {B : CompactSurface.{u}} (D : BaseMorseData B)
    {k : SurfaceModel} {X : Type u} [TopologicalSpace X] [ChartedSpace (SurfaceModel.Space k) X]
    [IsManifold (SurfaceModel.model k) ∞ X] {g : X → D.core.Carrier}
    (hg : Manifold.IsSmoothEmbedding (SurfaceModel.model k) (SurfaceModel.model D.core.kind) ∞ g) :
    Manifold.IsSmoothEmbedding (SurfaceModel.model k) (SurfaceModel.model B.kind) ∞
      (fun x => (g x).val) :=
  isSmoothEmbedding_val_comp_of_core D hg

namespace PlanarCore

variable {B : CompactSurface.{u}} {D : BaseMorseData B} (P : PlanarCore D)

def ι (j : Fin P.pieceCount) (x : (P.base j).surface.Carrier) : B.Carrier := (P.inclusion j x).val

theorem level_le_ι (j : Fin P.pieceCount) (x : (P.base j).surface.Carrier) :
    D.level 0 ≤ D.f (P.ι j x) :=
  (P.inclusion j x).2

theorem isInteriorPoint_ι (j : Fin P.pieceCount) (x : (P.base j).surface.Carrier) :
    (SurfaceModel.model B.kind).IsInteriorPoint (P.ι j x) :=
  D.isInteriorPoint_of_pos (D.level_zero_pos.trans_le (P.level_le_ι j x))

theorem injective_ι (j : Fin P.pieceCount) : Injective (P.ι j) :=
  Subtype.val_injective.comp (P.isSmoothEmbedding j).isEmbedding.injective

theorem isSmoothEmbedding_ι (j : Fin P.pieceCount) :
    Manifold.IsSmoothEmbedding (SurfaceModel.model (P.base j).surface.kind)
      (SurfaceModel.model B.kind) ∞ (P.ι j) :=
  isSmoothEmbedding_core_val_comp D (P.isSmoothEmbedding j)

theorem iUnion_range_ι : ⋃ j, range (P.ι j) = {x | D.level 0 ≤ D.f x} := by
  ext x
  constructor
  · rintro hx
    obtain ⟨j, y, rfl⟩ := mem_iUnion.mp hx
    exact P.level_le_ι j y
  · intro hx
    have h : (⟨x, hx⟩ : D.core.Carrier) ∈ ⋃ j, range (P.inclusion j) := by
      rw [P.covers]
      exact mem_univ _
    obtain ⟨j, y, hy⟩ := mem_iUnion.mp h
    exact mem_iUnion.mpr ⟨j, y, congrArg Subtype.val hy⟩

def IsBottom (j : Fin P.pieceCount) (l : Fin (P.kind j)) : Prop := ∀ c b, P.cutSide c b ≠ ⟨j, l⟩

def bottomPoint (j : Fin P.pieceCount) (l : Fin (P.kind j)) (h : P.IsBottom j l) : B.Carrier :=
  (P.bottom_collar j l h).choose

theorem bottomPoint_level (j : Fin P.pieceCount) (l : Fin (P.kind j)) (h : P.IsBottom j l) :
    D.f (P.bottomPoint j l h) = D.level 0 :=
  (P.bottom_collar j l h).choose_spec.choose

def bottomBicollar (j : Fin P.pieceCount) (l : Fin (P.kind j)) (h : P.IsBottom j l) :
    PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ)) (SurfaceModel.model B.kind) (Circle × ℝ)
      B.Carrier ∞ :=
  Classical.choose (D.exists_levelBicollar 0 (P.bottomPoint_level j l h))

theorem bottomBicollar_spec (j : Fin P.pieceCount) (l : Fin (P.kind j)) (h : P.IsBottom j l) :
    (P.bottomBicollar j l h).source = {p | -1 < p.2 ∧ p.2 < 1} ∧
      range (fun t => P.bottomBicollar j l h (t, 0)) =
        connectedComponentIn (D.f ⁻¹' {D.level 0}) (P.bottomPoint j l h) ∧
      (∀ t s, -1 < s → s < 1 →
        D.f (P.bottomBicollar j l h (t, s)) = D.level 0 + D.κ * s) ∧
      ∀ t, IsMIntegralCurveOn (fun s => P.bottomBicollar j l h (t, s))
        (fun x => D.κ • D.field x) (Ioo (-1) 1) :=
  Classical.choose_spec (D.exists_levelBicollar 0 (P.bottomPoint_level j l h))

def bottomSigma (j : Fin P.pieceCount) (l : Fin (P.kind j)) (h : P.IsBottom j l) :
    Circle ≃ₘ⟮𝓡 1, 𝓡 1⟯ Circle :=
  (P.bottom_collar j l h).choose_spec.choose_spec.choose

theorem bottomSigma_spec (j : Fin P.pieceCount) (l : Fin (P.kind j)) (h : P.IsBottom j l)
    (t : Circle) (s : ℝ) (hs : 0 ≤ s) (hs1 : s < 1) :
    P.ι j ((P.base j).collar l (t, halfPoint s hs)) =
      P.bottomBicollar j l h (P.bottomSigma j l h t, s) :=
  (P.bottom_collar j l h).choose_spec.choose_spec.choose_spec t s hs hs1

def cutSigma (c : Fin P.cutCount) (b : Bool) : Circle ≃ₘ⟮𝓡 1, 𝓡 1⟯ Circle :=
  (P.cutSide_collar c b).choose

theorem cutSigma_spec (c : Fin P.cutCount) (b : Bool) (t : Circle) (s : ℝ) (hs : 0 ≤ s)
    (hs1 : s < 1) :
    P.ι (P.cutSide c b).1 ((P.base _).collar (P.cutSide c b).2 (t, halfPoint s hs)) =
      P.cut c (P.cutSigma c b t, if b then s else -s) :=
  (P.cutSide_collar c b).choose_spec t s hs hs1

theorem cutSide_collar_eq {c : Fin P.cutCount} {b : Bool} {j : Fin P.pieceCount}
    {l : Fin (P.kind j)} (h : P.cutSide c b = ⟨j, l⟩) (t : Circle) (s : ℝ) (hs : 0 ≤ s)
    (hs1 : s < 1) :
    P.ι j ((P.base j).collar l (t, halfPoint s hs)) =
      P.cut c (P.cutSigma c b t, if b then s else -s) := by
  have e := P.cutSigma_spec c b t s hs hs1
  rw [h] at e
  exact e

theorem level_lt_of_not_isBottom {j : Fin P.pieceCount} {l : Fin (P.kind j)}
    (h : ¬ P.IsBottom j l) (t : Circle) :
    D.level 0 < D.f (P.ι j ((P.base j).collar l (t, halfZero))) := by
  simp only [IsBottom, not_forall, not_not] at h
  obtain ⟨c, b, hcb⟩ := h
  rw [show halfZero = halfPoint 0 le_rfl from rfl, P.cutSide_collar_eq hcb t 0 le_rfl one_pos]
  exact P.cut_level c _ _ (by cases b <;> norm_num) (by cases b <;> norm_num)

theorem level_bottom {j : Fin P.pieceCount} {l : Fin (P.kind j)} (h : P.IsBottom j l)
    (t : Circle) : D.f (P.ι j ((P.base j).collar l (t, halfZero))) = D.level 0 := by
  rw [show halfZero = halfPoint 0 le_rfl from rfl, P.bottomSigma_spec j l h t 0 le_rfl one_pos,
    (P.bottomBicollar_spec j l h).2.2.1 _ 0 (by norm_num) (by norm_num), mul_zero, add_zero]

theorem range_bottom {j : Fin P.pieceCount} {l : Fin (P.kind j)} (h : P.IsBottom j l) :
    range (fun t => P.ι j ((P.base j).collar l (t, halfZero))) =
      range (fun θ => P.bottomBicollar j l h (θ, 0)) := by
  ext y
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨P.bottomSigma j l h t, (P.bottomSigma_spec j l h t 0 le_rfl one_pos).symm⟩
  · rintro ⟨θ, rfl⟩
    refine ⟨(P.bottomSigma j l h).symm θ, ?_⟩
    change P.ι j ((P.base j).collar l ((P.bottomSigma j l h).symm θ, halfPoint 0 le_rfl)) = _
    rw [P.bottomSigma_spec j l h _ 0 le_rfl one_pos, Diffeomorph.apply_symm_apply]

theorem isBoundaryPoint_of_level {j : Fin P.pieceCount} {x : (P.base j).surface.Carrier}
    (hx : D.f (P.ι j x) = D.level 0) :
    (SurfaceModel.model (P.base j).surface.kind).IsBoundaryPoint x := by
  rw [ModelWithCorners.isBoundaryPoint_iff_not_isInteriorPoint]
  intro hint
  have hemb := P.isSmoothEmbedding j
  have hb := DifferentialGeometry.Topology.Manifold.bijective_mfderiv_of_isImmersionAt _ _
    (P.inclusion j) x (hemb.isImmersion.isImmersionAt x) (by simp)
  have hloc := isLocalDiffeomorphAt_of_isInteriorPoint_of_bijective hemb.contMDiff hint hb
  have hi := (hloc.isInteriorPoint_iff (by simp)).mp hint
  exact ((SurfaceModel.model D.core.kind).isInteriorPoint_iff_not_isBoundaryPoint _).mp hi
    ((D.core_isBoundaryPoint_iff _).mpr hx)

theorem exists_bottom_of_level {y : B.Carrier} (hy : D.f y = D.level 0) :
    ∃ (j : Fin P.pieceCount) (l : Fin (P.kind j)) (_ : P.IsBottom j l) (t : Circle),
      P.ι j ((P.base j).collar l (t, halfZero)) = y := by
  have hy' : y ∈ ⋃ j, range (P.ι j) := by
    rw [P.iUnion_range_ι]
    exact hy.ge
  obtain ⟨j, x, rfl⟩ := mem_iUnion.mp hy'
  have hb := P.isBoundaryPoint_of_level hy
  have hb' : x ∈ (SurfaceModel.model (P.base j).surface.kind).boundary
      (P.base j).surface.Carrier := hb
  rw [(P.base j).boundary_exhausted] at hb'
  obtain ⟨l, t, ht⟩ := mem_iUnion.mp hb'
  change (P.base j).collar l (t, halfZero) = x at ht
  have hbot : P.IsBottom j l := by
    by_contra hnb
    have h := P.level_lt_of_not_isBottom hnb t
    rw [ht, hy] at h
    exact lt_irrefl _ h
  exact ⟨j, l, hbot, t, by rw [ht]⟩

theorem bottom_unique {j j' : Fin P.pieceCount} {l : Fin (P.kind j)} {l' : Fin (P.kind j')}
    (h : P.IsBottom j l) (h' : P.IsBottom j' l') {t t' : Circle}
    (he : P.ι j ((P.base j).collar l (t, halfZero)) =
      P.ι j' ((P.base j').collar l' (t', halfZero))) :
    (⟨j, l⟩ : Σ j, Fin (P.kind j)) = ⟨j', l'⟩ := by
  by_cases hjj : j = j'
  · subst hjj
    have he' := P.injective_ι j he
    by_contra hne
    have hll : l ≠ l' := fun e => hne (by rw [e])
    have hz : ∀ (m : Fin (P.kind j)) (τ : Circle),
        ((τ, halfZero) : Circle × EuclideanHalfSpace 1) ∈ ((P.base j).collar m).source :=
      fun m τ => by
        rw [(P.base j).source_eq m]
        change (0 : ℝ) < 1
        exact one_pos
    exact ((P.base j).disjoint hll).le_bot
      ⟨((P.base j).collar l).map_source (hz l t),
        he' ▸ ((P.base j).collar l').map_source (hz l' t')⟩
  · obtain ⟨c, τ, hc⟩ := P.overlap j j' _ _ hjj (Subtype.ext he)
    have h1 := P.level_bottom h t
    change D.f (P.inclusion j _).val = _ at h1
    rw [hc] at h1
    have h2 := P.cut_level c τ 0 (by norm_num) (by norm_num)
    rw [h1] at h2
    exact absurd h2 (lt_irrefl _)

section Lift

variable {C : CompactCarrier.{u}} {U : TopologicalSpace.Opens C.Carrier} (F : CircleFibration C U)
  {D : BaseMorseData F.base} (P : PlanarCore D)

theorem mem_source_of_abs_le_half {c : PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ))
    (SurfaceModel.model F.base.kind) (Circle × ℝ) F.base.Carrier ∞}
    (hc : c.source = {p | -1 < p.2 ∧ p.2 < 1}) (θ : Circle) (s : ℝ) (hs : |s| ≤ 1 / 2) :
    (θ, s) ∈ c.source := by
  rw [hc]
  constructor <;> linarith [abs_le.mp hs]

def cutLift (c : Fin P.cutCount) : LiftedBicollar F (P.cut c) :=
  (CircleFibration.exists_liftFlow F (P.cut c) (R := 1 / 2) (by norm_num)
    (mem_source_of_abs_le_half F (P.cut_source c))).choose

theorem cutLift_width (c : Fin P.cutCount) : (cutLift F P c).width = 1 / 16 :=
  (CircleFibration.exists_liftFlow F (P.cut c) (R := 1 / 2) (by norm_num)
    (mem_source_of_abs_le_half F (P.cut_source c))).choose_spec.1.trans (by norm_num)

def bottomLift (j : Fin P.pieceCount) (l : Fin (P.kind j)) (h : P.IsBottom j l) :
    LiftedBicollar F (P.bottomBicollar j l h) :=
  (CircleFibration.exists_liftFlow F (P.bottomBicollar j l h) (R := 1 / 2) (by norm_num)
    (mem_source_of_abs_le_half F (P.bottomBicollar_spec j l h).1)).choose

theorem bottomLift_width (j : Fin P.pieceCount) (l : Fin (P.kind j)) (h : P.IsBottom j l) :
    (bottomLift F P j l h).width = 1 / 16 :=
  (CircleFibration.exists_liftFlow F (P.bottomBicollar j l h) (R := 1 / 2) (by norm_num)
    (mem_source_of_abs_le_half F (P.bottomBicollar_spec j l h).1)).choose_spec.1.trans
      (by norm_num)

theorem exists_planarPieceMap (j : Fin P.pieceCount) :
    ∃ Φ : (P.base j).surface.Carrier × Circle → U,
      ContMDiff ((SurfaceModel.model (P.base j).surface.kind).prod (𝓡 1)) C.model ∞
        (fun q => (Φ q).val) ∧ Injective Φ ∧
      (∀ q, Bijective (mfderiv ((SurfaceModel.model (P.base j).surface.kind).prod (𝓡 1))
        C.model (fun q => (Φ q).val) q)) ∧
      (∀ q, F.projection (Φ q) = P.ι j q.1) ∧ range Φ = F.projection ⁻¹' range (P.ι j) ∧
      ∃ δ > 0, (∀ (l : Fin (P.kind j)) (c : Fin P.cutCount) (b : Bool), P.cutSide c b = ⟨j, l⟩ →
          ∀ t v s (hs : 0 ≤ s), s < δ → Φ ((P.base j).collar l (t, halfPoint s hs), v) =
            (cutLift F P c).flow (if b then s else -s)
              (Φ ((P.base j).collar l (t, halfZero), v))) ∧
        ∀ (l : Fin (P.kind j)) (h : P.IsBottom j l) t v s (hs : 0 ≤ s), s < δ →
          Φ ((P.base j).collar l (t, halfPoint s hs), v) =
            (bottomLift F P j l h).flow s (Φ ((P.base j).collar l (t, halfZero), v)) := by
  classical
  have hdata : ∀ l : Fin (P.kind j), ∃ (cB : PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ))
      (SurfaceModel.model F.base.kind) (Circle × ℝ) F.base.Carrier ∞)
      (_ : cB.source = {p | -1 < p.2 ∧ p.2 < 1}) (b : Bool) (σ : Circle ≃ₘ⟮𝓡 1, 𝓡 1⟯ Circle)
      (L : LiftedBicollar F cB),
      (∀ t s (hs : 0 ≤ s), s < 1 →
        P.ι j ((P.base j).collar l (t, halfPoint s hs)) = cB (σ t, if b then s else -s)) ∧
      (∀ c b', P.cutSide c b' = ⟨j, l⟩ → b = b' ∧ L.flow = (cutLift F P c).flow) ∧
      ∀ h : P.IsBottom j l, b = true ∧ L.flow = (bottomLift F P j l h).flow := by
    intro l
    by_cases h : P.IsBottom j l
    · refine ⟨P.bottomBicollar j l h, (P.bottomBicollar_spec j l h).1, true, P.bottomSigma j l h,
        bottomLift F P j l h, fun t s hs hs1 => ?_, fun c b' hcb => absurd hcb (h c b'),
        fun _ => ⟨rfl, rfl⟩⟩
      rw [P.bottomSigma_spec j l h t s hs hs1]
      simp
    · have h' : ∃ c b, P.cutSide c b = ⟨j, l⟩ := by
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
  choose cB hcB b σ L hcol hcut hbot using hdata
  obtain ⟨Φ, hΦs, hΦe, hΦb, hΦπ, hΦr, δ, hδ, hΦsync⟩ := exists_syncedPiece F (P.kind_mem j)
    (P.base j) (P.isSmoothEmbedding_ι j) cB hcB b σ hcol (P.isInteriorPoint_ι j) L
  refine ⟨Φ, hΦs, hΦe.injective, hΦb, hΦπ, hΦr, δ, hδ, fun l c b' hcb t v s hs hs1 => ?_,
    fun l h t v s hs hs1 => ?_⟩
  · obtain ⟨e1, e2⟩ := hcut l c b' hcb
    rw [hΦsync l t v s hs hs1, e2, e1]
  · obtain ⟨e1, e2⟩ := hbot l h
    rw [hΦsync l t v s hs hs1, e2, e1]
    simp

end Lift

end PlanarCore

section SideTorus

variable {C : CompactCarrier.{u}} {U : TopologicalSpace.Opens C.Carrier} (F : CircleFibration C U)

theorem range_sideTorus_eq {k : ℕ} (Q : PlanarBase.{u} k) {ι : Q.surface.Carrier → F.base.Carrier}
    (hι : Injective ι) {Φ : Q.surface.Carrier × Circle → U}
    (hπ : ∀ q, F.projection (Φ q) = ι q.1) (hrange : range Φ = F.projection ⁻¹' range ι)
    (l : Fin k) {cB : PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ)) (SurfaceModel.model F.base.kind)
      (Circle × ℝ) F.base.Carrier ∞} {σ : Circle ≃ₘ⟮𝓡 1, 𝓡 1⟯ Circle}
    (hcol : ∀ t, ι (Q.collar l (t, halfZero)) = cB (σ t, 0)) :
    range (Wiring.sideTorus Q l Φ) = F.projection ⁻¹' range (fun θ => cB (θ, 0)) := by
  ext x
  constructor
  · rintro ⟨t, rfl⟩
    refine ⟨σ t.1, ?_⟩
    change cB (σ t.1, 0) = F.projection (Φ (Q.collar l (t.1, halfZero), t.2))
    rw [hπ, hcol]
  · rintro ⟨θ, hθ⟩
    have hx : x ∈ range Φ := by
      rw [hrange]
      refine ⟨Q.collar l (σ.symm θ, halfZero), ?_⟩
      rw [hcol, Diffeomorph.apply_symm_apply]
      exact hθ
    obtain ⟨⟨q, v⟩, rfl⟩ := hx
    have hq : ι q = ι (Q.collar l (σ.symm θ, halfZero)) := by
      rw [hcol, Diffeomorph.apply_symm_apply]
      exact (hπ (q, v)).symm.trans hθ.symm
    refine ⟨(σ.symm θ, v), ?_⟩
    change Φ (Q.collar l (σ.symm θ, halfZero), v) = Φ (q, v)
    rw [hι hq]

end SideTorus

theorem sideTorus_shrink {X : Type*} {k : ℕ} (Q : PlanarBase.{u} k) {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (l : Fin k) (Φ : Q.surface.Carrier × Circle → X) :
    Wiring.sideTorus (Q.shrink hδ hδ1) l Φ = Wiring.sideTorus Q l Φ := by
  funext t
  change Φ (Q.collar l (t.1, halfSpaceScale hδ halfZero), t.2) = Φ (Q.collar l (t.1, halfZero), t.2)
  rw [halfSpaceScale_halfZero]

theorem shrink_collar_halfPoint {k : ℕ} (Q : PlanarBase.{u} k) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (l : Fin k) (t : Circle) {s : ℝ} (hs : 0 ≤ s) :
    (Q.shrink hδ hδ1).collar l (t, halfPoint s hs) =
      Q.collar l (t, halfPoint (δ * s) (mul_nonneg hδ.le hs)) := by
  change Q.collar l (t, halfSpaceScale hδ (halfPoint s hs)) = _
  rw [halfSpaceScale_halfPoint]

end GC.Seifert
