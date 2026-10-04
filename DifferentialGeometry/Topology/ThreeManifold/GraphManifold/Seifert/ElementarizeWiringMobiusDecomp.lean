import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ElementarizeWiringMobiusCore

/-!
# A Möbius core from a planar decomposition of the core

Lane P1X2 (P1 wiring, the Möbius branch).

The frozen hypothesis `hMD3` of tier T4 (lane MD3's S-Asm statement) gives, for Morse data `D'`
of the base, a `PlanarDecomposition D'.core` whose cuts are pointwise bicollars of the base and
whose sides that are not cut sides are level-0 bicollars. Its pieces are `ElementaryBase`s, planar
or Möbius. `nonempty_mobiusCore_of_decomposition` sorts them into the two families of a
`MobiusCore D'`: the planar pieces are indexed by the subtype of indices with a planar base, the
Möbius pieces by the complement (`planarData`, `mobiusData`: the case split on the base, with
the same inclusion and the same collars), the sides are translated by `toSide` (a bijection, a
Möbius base having one boundary circle), and the cuts are the base bicollars of `hMD3`. They lie
above level 0 because the cut circles lie in the interior of the core.
-/

set_option autoImplicit false

noncomputable section
open Set Function Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert

namespace ElementaryBase

def IsPlanar : ElementaryBase.{u} → Prop
  | planar _ _ _ => True
  | mobius _ => False

theorem planarData {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanHalfSpace 2) X]
    (e : ElementaryBase.{u}) (he : e.IsPlanar) (incl : e.surface.Carrier → X)
    (hemb : Manifold.IsSmoothEmbedding (SurfaceModel.model e.surface.kind) (𝓡∂ 2) ∞ incl) :
    ∃ (k : ℕ) (_ : k ∈ ({1, 2, 3} : Finset ℕ)) (Q : PlanarBase.{u} k)
      (incl' : Q.surface.Carrier → X) (eq : Fin k ≃ Fin e.boundaryCount),
      Manifold.IsSmoothEmbedding (SurfaceModel.model Q.surface.kind) (𝓡∂ 2) ∞ incl' ∧
      range incl' = range incl ∧ ∀ l p, incl' (Q.collar l p) = incl (e.collar (eq l) p) := by
  cases e with
  | planar k hk Q => exact ⟨k, hk, Q, incl, Equiv.refl _, hemb, rfl, fun _ _ => rfl⟩
  | mobius M => exact he.elim

theorem mobiusData {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanHalfSpace 2) X]
    (e : ElementaryBase.{u}) (he : ¬ e.IsPlanar) (incl : e.surface.Carrier → X)
    (hemb : Manifold.IsSmoothEmbedding (SurfaceModel.model e.surface.kind) (𝓡∂ 2) ∞ incl) :
    ∃ (M : MobiusBase.{u}) (incl' : M.surface.Carrier → X) (l₀ : Fin e.boundaryCount),
      Manifold.IsSmoothEmbedding (SurfaceModel.model M.surface.kind) (𝓡∂ 2) ∞ incl' ∧
      range incl' = range incl ∧ (∀ l, l = l₀) ∧
        ∀ p, incl' (M.collar p) = incl (e.collar l₀ p) := by
  cases e with
  | planar k hk Q => exact (he trivial).elim
  | mobius M => exact ⟨M, incl, ⟨0, Nat.one_pos⟩, hemb, rfl,
      fun l => Fin.ext (Nat.lt_one_iff.mp l.2), fun _ => rfl⟩

end ElementaryBase

section Decomposition

variable {B : CompactSurface.{u}} (D : BaseMorseData B) (P : PlanarDecomposition D.core)

theorem cut_val_level (c : Fin P.cutCount) {t : Circle} {s : ℝ} (hs1 : -1 < s) (hs2 : s < 1) :
    D.level 0 < D.f (P.cut c (t, s)).val := by
  have hmem : (t, s) ∈ (P.cut c).source := by
    rw [P.cut_source c]
    exact ⟨hs1, hs2⟩
  have hint : (SurfaceModel.model D.core.kind).IsInteriorPoint (P.cut c (t, s)) :=
    P.cut_interior c ((P.cut c).map_source hmem)
  have hnb : ¬ (𝓡∂ 2).IsBoundaryPoint (P.cut c (t, s)) :=
    ((SurfaceModel.model D.core.kind).isInteriorPoint_iff_not_isBoundaryPoint _).mp hint
  rw [D.core_isBoundaryPoint_iff] at hnb
  exact lt_of_le_of_ne (P.cut c (t, s)).2 (Ne.symm hnb)

theorem nonempty_mobiusCore_of_decomposition
    (hcut : ∀ c, ∃ cB : PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ)) (SurfaceModel.model B.kind)
        (Circle × ℝ) B.Carrier ∞, cB.source = {p | -1 < p.2 ∧ p.2 < 1} ∧
          ∀ t s, -1 < s → s < 1 → (P.cut c (t, s)).val = cB (t, s))
    (hbot : ∀ j l, (∀ c b, P.cutSide c b ≠ ⟨j, l⟩) → ∃ (x₀ : B.Carrier)
      (hx₀ : D.f x₀ = D.level 0) (σ : Circle ≃ₘ⟮𝓡 1, 𝓡 1⟯ Circle), ∀ t s (hs : 0 ≤ s), s < 1 →
        (P.inclusion j ((P.piece j).collar l (t, halfPoint s hs))).val =
          Classical.choose (D.exists_levelBicollar 0 hx₀) (σ t, s)) :
    Nonempty (MobiusCore D) := by
  classical
  let PI := {j : Fin P.pieceCount // (P.piece j).IsPlanar}
  let MI := {j : Fin P.pieceCount // ¬ (P.piece j).IsPlanar}
  choose kP hkP QP inclP eqP hembP hrangeP hcolP using fun j : PI =>
    (P.piece j.1).planarData j.2 (P.inclusion j.1) (P.isSmoothEmbedding j.1)
  choose MM inclM l₀ hembM hrangeM hl₀ hcolM using fun m : MI =>
    (P.piece m.1).mobiusData m.2 (P.inclusion m.1) (P.isSmoothEmbedding m.1)
  choose cB hcBs hcB using hcut
  let Q : CorePieces D :=
    { PI := PI
      MI := MI
      kind := kP
      kind_mem := hkP
      base := QP
      incl := inclP
      emb := hembP
      mob := MM
      inclM := inclM
      embM := hembM }
  let toSide : (Σ j, Fin (P.piece j).boundaryCount) → Q.Side := fun w =>
    if h : (P.piece w.1).IsPlanar then .inl ⟨⟨w.1, h⟩, (eqP ⟨w.1, h⟩).symm w.2⟩
    else .inr ⟨w.1, h⟩
  have hside : ∀ w p, Q.sidePt (toSide w) p =
      (P.inclusion w.1 ((P.piece w.1).collar w.2 p)).val := by
    rintro ⟨j, l⟩ p
    by_cases h : (P.piece j).IsPlanar
    · have e : toSide ⟨j, l⟩ = .inl ⟨⟨j, h⟩, (eqP ⟨j, h⟩).symm l⟩ := dite_eq_left h
      rw [e, CorePieces.sidePt_inl]
      change (inclP ⟨j, h⟩ ((QP ⟨j, h⟩).collar ((eqP ⟨j, h⟩).symm l) p)).val = _
      rw [hcolP, Equiv.apply_symm_apply]
    · have e : toSide ⟨j, l⟩ = .inr ⟨j, h⟩ := dite_eq_right h
      rw [e, CorePieces.sidePt_inr]
      change (inclM ⟨j, h⟩ ((MM ⟨j, h⟩).collar p)).val = _
      rw [hcolM, ← hl₀ ⟨j, h⟩ l]
  have hinj : Injective toSide := by
    rintro ⟨j, l⟩ ⟨j', l'⟩ hw
    by_cases h : (P.piece j).IsPlanar <;> by_cases h' : (P.piece j').IsPlanar
    · have e : toSide ⟨j, l⟩ = .inl ⟨⟨j, h⟩, (eqP ⟨j, h⟩).symm l⟩ := dite_eq_left h
      have e' : toSide ⟨j', l'⟩ = .inl ⟨⟨j', h'⟩, (eqP ⟨j', h'⟩).symm l'⟩ := dite_eq_left h'
      rw [e, e'] at hw
      have hw' := Sum.inl_injective hw
      have hj : (⟨j, h⟩ : PI) = ⟨j', h'⟩ := congrArg Sigma.fst hw'
      obtain rfl : j = j' := congrArg Subtype.val hj
      have hl := eq_of_heq (Sigma.mk.inj_iff.mp hw').2
      rw [(eqP ⟨j, h⟩).symm.injective hl]
    · have e : toSide ⟨j, l⟩ = .inl ⟨⟨j, h⟩, (eqP ⟨j, h⟩).symm l⟩ := dite_eq_left h
      have e' : toSide ⟨j', l'⟩ = .inr ⟨j', h'⟩ := dite_eq_right h'
      rw [e, e'] at hw
      exact absurd hw Sum.inl_ne_inr
    · have e : toSide ⟨j, l⟩ = .inr ⟨j, h⟩ := dite_eq_right h
      have e' : toSide ⟨j', l'⟩ = .inl ⟨⟨j', h'⟩, (eqP ⟨j', h'⟩).symm l'⟩ := dite_eq_left h'
      rw [e, e'] at hw
      exact absurd hw Sum.inr_ne_inl
    · have e : toSide ⟨j, l⟩ = .inr ⟨j, h⟩ := dite_eq_right h
      have e' : toSide ⟨j', l'⟩ = .inr ⟨j', h'⟩ := dite_eq_right h'
      rw [e, e'] at hw
      have hj : (⟨j, h⟩ : MI) = ⟨j', h'⟩ := Sum.inr_injective hw
      obtain rfl : j = j' := congrArg Subtype.val hj
      rw [hl₀ ⟨j, h⟩ l, hl₀ ⟨j, h⟩ l']
  have hsurj : ∀ w : Q.Side, ∃ w', toSide w' = w := by
    rintro (⟨⟨j, h⟩, l⟩ | ⟨j, h⟩)
    · refine ⟨⟨j, eqP ⟨j, h⟩ l⟩, ?_⟩
      change (if h : (P.piece j).IsPlanar then _ else _) = _
      rw [dite_eq_left h, Equiv.symm_apply_apply]
    · refine ⟨⟨j, l₀ ⟨j, h⟩⟩, ?_⟩
      change (if h : (P.piece j).IsPlanar then _ else _) = _
      rw [dite_eq_right h]
  have hptP : ∀ (j : PI) (x : (QP j).surface.Carrier), ∃ z, P.inclusion j.1 z = inclP j x :=
    fun j x => by
      have hx : inclP j x ∈ range (P.inclusion j.1) := hrangeP j ▸ mem_range_self x
      exact hx
  have hptM : ∀ (m : MI) (x : (MM m).surface.Carrier), ∃ z, P.inclusion m.1 z = inclM m x :=
    fun m x => by
      have hx : inclM m x ∈ range (P.inclusion m.1) := hrangeM m ▸ mem_range_self x
      exact hx
  let idx : Q.Pt → Fin P.pieceCount := fun y =>
    Sum.elim (fun j : PI => j.1) (fun m : MI => m.1) (Q.piece y)
  have key : ∀ y : Q.Pt, ∃ z, P.inclusion (idx y) z = Q.pt y := by
    rintro (⟨j, x⟩ | ⟨m, x⟩)
    · exact hptP j x
    · exact hptM m x
  have hidx : ∀ y y' : Q.Pt, Q.piece y ≠ Q.piece y' → idx y ≠ idx y' := by
    intro y y' hne he
    change Sum.elim (fun j : PI => j.1) (fun m : MI => m.1) (Q.piece y) =
      Sum.elim (fun j : PI => j.1) (fun m : MI => m.1) (Q.piece y') at he
    revert hne he
    rcases Q.piece y with j | m <;> rcases Q.piece y' with j' | m' <;> intro hne he
    · exact hne (congrArg Sum.inl (Subtype.ext he))
    · have he' : j.1 = m'.1 := he
      exact m'.2 (he' ▸ j.2)
    · have he' : m.1 = j'.1 := he
      exact m.2 (he'.symm ▸ j'.2)
    · exact hne (congrArg Sum.inr (Subtype.ext he))
  exact ⟨{
    pieces := Q
    cutCount := P.cutCount
    cut := cB
    cut_source := hcBs
    cut_level := fun c t s hs1 hs2 => by
      rw [← hcB c t s hs1 hs2]
      exact cut_val_level D P c hs1 hs2
    covers := fun x => by
      have hx : x ∈ ⋃ j, range (P.inclusion j) := P.covers ▸ mem_univ x
      obtain ⟨j, z, rfl⟩ := mem_iUnion.mp hx
      by_cases h : (P.piece j).IsPlanar
      · have hz : P.inclusion j z ∈ range (inclP ⟨j, h⟩) :=
          (hrangeP ⟨j, h⟩).symm ▸ mem_range_self z
        obtain ⟨z', hz'⟩ := hz
        exact ⟨.inl ⟨⟨j, h⟩, z'⟩, hz'⟩
      · have hz : P.inclusion j z ∈ range (inclM ⟨j, h⟩) :=
          (hrangeM ⟨j, h⟩).symm ▸ mem_range_self z
        obtain ⟨z', hz'⟩ := hz
        exact ⟨.inr ⟨⟨j, h⟩, z'⟩, hz'⟩
    cutSide := fun c b => toSide (P.cutSide c b)
    cutSide_injective := fun x y hxy => P.cutSide_injective (hinj hxy)
    cutSide_collar := fun c b => by
      obtain ⟨σ, hσ⟩ := P.cutSide_collar c b
      refine ⟨σ, fun t s hs hs1 => ?_⟩
      rw [hside, hσ t s hs hs1]
      exact hcB c _ _ (by cases b <;> simp <;> linarith)
        (by cases b <;> simp <;> linarith)
    bottom_collar := fun w hw => by
      obtain ⟨w', rfl⟩ := hsurj w
      have hw' : ∀ c b, P.cutSide c b ≠ ⟨w'.1, w'.2⟩ := fun c b h =>
        hw c b (congrArg toSide h)
      obtain ⟨x₀, hx₀, σ, hσ⟩ := hbot w'.1 w'.2 hw'
      exact ⟨x₀, hx₀, σ, fun t s hs hs1 => (hside w' _).trans (hσ t s hs hs1)⟩
    overlap := fun y y' hne he => by
      obtain ⟨z, hz⟩ := key y
      obtain ⟨z', hz'⟩ := key y'
      obtain ⟨c, t, hc⟩ := P.overlap (idx y) (idx y') z z' (hidx y y' hne)
        (hz.trans (he.trans hz'.symm))
      refine ⟨c, t, ?_⟩
      rw [← hz, hc]
      exact hcB c t 0 (by norm_num) (by norm_num) }⟩

end Decomposition

end GC.Seifert
