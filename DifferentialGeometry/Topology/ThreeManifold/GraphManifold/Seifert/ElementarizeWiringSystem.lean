import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ElementarizeWiringSeam
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ElementarizeProof

/-!
# Piece systems from synchronised product pieces

Lane P1W (P1 wiring), bookkeeping part of tier T2.

A `SyncedData W` lists product pieces `map x : Q_x × S¹ → W` (smooth, injective, bijective
differential, covering `W`) indexed by a finite type, seams indexed by a finite type with a left
and a right side each, and external sides, such that every side occurs exactly once. Each seam
carries a flow of `W` synchronising both collars at one common rate (`sync_left`, `sync_right`),
the two side tori have the same image and the flow sweep is injective; then `exists_syncedSeam`
gives the seam chart and the matching. Two pieces meet only on the zero section of a seam
(`overlap`), and the pieces are local diffeomorphisms at the external tori.

`SyncedData.toSystem` renumbers pieces, seams and external sides by `Fintype.equivFin` and returns
the `EmbeddedPieceSystem W`; sides are transported by `Equiv.sigmaCongrLeft`
(`SyncedData.map_collar_symm`). A `ComponentRefinement` of a component of a torus presentation is
a piece system of that component with its ports (one component's share of a `PieceRefinement`);
`SyncedData.toComponentRefinement` builds it from synced data whose external collars are the port
collars, and `PieceRefinement.ofComponents` collects one per component.
-/

set_option autoImplicit false

noncomputable section
open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert.Wiring

structure SyncedData (W : CompactCarrier.{u}) where
  ι : Type
  [fintypeι : Fintype ι]
  nonempty : Nonempty ι
  γ : Type
  [fintypeγ : Fintype γ]
  ε : Type
  [fintypeε : Fintype ε]
  kind : ι → ℕ
  kind_mem : ∀ x, kind x ∈ ({1, 2, 3} : Finset ℕ)
  base : ∀ x, PlanarBase.{u} (kind x)
  map : ∀ x, (base x).surface.Carrier × Circle → W.Carrier
  smooth : ∀ x, ContMDiff ((SurfaceModel.model (base x).surface.kind).prod (𝓡 1)) W.model ∞
    (map x)
  mfderiv_bijective : ∀ x q, Bijective
    (mfderiv ((SurfaceModel.model (base x).surface.kind).prod (𝓡 1)) W.model (map x) q)
  injective : ∀ x, Injective (map x)
  covers : ⋃ x, range (map x) = univ
  side : γ → Bool → Σ x, Fin (kind x)
  ext : ε → Σ x, Fin (kind x)
  sides_bijective : Bijective (Sum.elim (uncurry side) ext)
  flow : γ → ℝ → (W.Carrier ≃ₘ⟮W.model, W.model⟯ W.Carrier)
  flow_add : ∀ c s t x, flow c (s + t) x = flow c s (flow c t x)
  rate : ℝ
  sync_left : ∀ c t v s (hs : 0 ≤ s), s < 1 →
    map (side c true).1 ((base _).collar (side c true).2 (t, halfPoint s hs), v) =
      flow c (-(rate * s)) (map (side c true).1 ((base _).collar (side c true).2 (t, halfZero), v))
  sync_right : ∀ c t v s (hs : 0 ≤ s), s < 1 →
    map (side c false).1 ((base _).collar (side c false).2 (t, halfPoint s hs), v) =
      flow c (rate * s) (map (side c false).1 ((base _).collar (side c false).2 (t, halfZero), v))
  range_eq : ∀ c, range (sideTorus (base (side c true).1) (side c true).2 (map (side c true).1)) =
    range (sideTorus (base (side c false).1) (side c false).2 (map (side c false).1))
  injOn : ∀ c, InjOn (fun y : Torus × ℝ => flow c (rate * y.2)
    (sideTorus (base (side c true).1) (side c true).2 (map (side c true).1) y.1))
    signedCollarSource
  external_local : ∀ e (t : Torus), IsLocalDiffeomorphAt
    ((SurfaceModel.model (base (ext e).1).surface.kind).prod (𝓡 1)) W.model ∞
    (map (ext e).1) ((base _).collar (ext e).2 (t.1, halfZero), t.2)
  overlap : ∀ x x' q q', map x q = map x' q' →
    (⟨x, q⟩ : Σ x, (base x).surface.Carrier × Circle) = ⟨x', q'⟩ ∨
      ∃ c t, map x q = sideTorus (base (side c true).1) (side c true).2 (map (side c true).1) t

namespace SyncedData

attribute [instance] SyncedData.fintypeι SyncedData.fintypeγ SyncedData.fintypeε

variable {W : CompactCarrier.{u}} (S : SyncedData W)

open scoped Classical in
def eι : Fin (Fintype.card S.ι) ≃ S.ι := (Fintype.equivFin S.ι).symm

open scoped Classical in
def eγ : Fin (Fintype.card S.γ) ≃ S.γ := (Fintype.equivFin S.γ).symm

open scoped Classical in
def eε : Fin (Fintype.card S.ε) ≃ S.ε := (Fintype.equivFin S.ε).symm

def sideEquiv : (Σ J : Fin (Fintype.card S.ι), Fin (S.kind (S.eι J))) ≃ Σ x, Fin (S.kind x) :=
  Equiv.sigmaCongrLeft (β := fun x => Fin (S.kind x)) S.eι

theorem transport (P : ∀ x : S.ι, Fin (S.kind x) → Prop) (w : Σ x, Fin (S.kind x)) :
    P (S.eι (S.sideEquiv.symm w).1) (S.sideEquiv.symm w).2 ↔ P w.1 w.2 := by
  obtain ⟨σ, rfl⟩ := S.sideEquiv.surjective w
  rw [Equiv.symm_apply_apply]
  rfl

theorem map_collar_symm (w : Σ x, Fin (S.kind x)) (p : Circle × EuclideanHalfSpace 1)
    (v : Circle) :
    S.map (S.eι (S.sideEquiv.symm w).1) ((S.base (S.eι (S.sideEquiv.symm w).1)).collar
      (S.sideEquiv.symm w).2 p, v) = S.map w.1 ((S.base w.1).collar w.2 p, v) :=
  (S.transport (fun x l => S.map x ((S.base x).collar l p, v) =
    S.map w.1 ((S.base w.1).collar w.2 p, v)) w).mpr rfl

theorem flow_zero (c : S.γ) (x : W.Carrier) : S.flow c 0 x = x := by
  have h := S.flow_add c 0 0 x
  rw [add_zero] at h
  exact ((S.flow c 0).injective h).symm

theorem exists_seam (c : S.γ) :
    ∃ (Sm : PartialDiffeomorph signedCollarModel W.model (Torus × ℝ) W.Carrier ∞)
      (m : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus),
      Sm.source = signedCollarSource ∧
      (∀ y, Sm y = S.flow c (S.rate * y.2)
        (sideTorus (S.base (S.side c true).1) (S.side c true).2 (S.map (S.side c true).1) y.1)) ∧
      (∀ t s (hs : s ≤ 0), -1 < s →
        Sm (t, s) = S.map (S.side c true).1 ((S.base _).collar (S.side c true).2
          (t.1, halfPoint (-s) (neg_nonneg.2 hs)), t.2)) ∧
      (∀ t s (hs : 0 ≤ s), s < 1 →
        Sm (t, s) = S.map (S.side c false).1 ((S.base _).collar (S.side c false).2
          ((m t).1, halfPoint s hs), (m t).2)) ∧
      (∀ y ∈ Sm.target, W.model.IsInteriorPoint y) ∧
      ∀ t, sideTorus (S.base (S.side c false).1) (S.side c false).2 (S.map (S.side c false).1)
        (m t) =
          sideTorus (S.base (S.side c true).1) (S.side c true).2 (S.map (S.side c true).1) t :=
  exists_syncedSeam _ _ _ _ (S.smooth _) (S.smooth _) (S.mfderiv_bijective _)
    (S.mfderiv_bijective _) (S.injective _) (S.injective _) (S.flow_add c) (S.sync_left c)
    (S.sync_right c) (S.range_eq c) (S.injOn c)

def seam (c : S.γ) : PartialDiffeomorph signedCollarModel W.model (Torus × ℝ) W.Carrier ∞ :=
  (S.exists_seam c).choose

def matching (c : S.γ) : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus :=
  (S.exists_seam c).choose_spec.choose

theorem seam_spec (c : S.γ) :
    (S.seam c).source = signedCollarSource ∧
      (∀ y, S.seam c y = S.flow c (S.rate * y.2)
        (sideTorus (S.base (S.side c true).1) (S.side c true).2 (S.map (S.side c true).1) y.1)) ∧
      (∀ t s (hs : s ≤ 0), -1 < s →
        S.seam c (t, s) = S.map (S.side c true).1 ((S.base _).collar (S.side c true).2
          (t.1, halfPoint (-s) (neg_nonneg.2 hs)), t.2)) ∧
      (∀ t s (hs : 0 ≤ s), s < 1 →
        S.seam c (t, s) = S.map (S.side c false).1 ((S.base _).collar (S.side c false).2
          ((S.matching c t).1, halfPoint s hs), (S.matching c t).2)) ∧
      (∀ y ∈ (S.seam c).target, W.model.IsInteriorPoint y) ∧
      ∀ t, sideTorus (S.base (S.side c false).1) (S.side c false).2 (S.map (S.side c false).1)
        (S.matching c t) =
          sideTorus (S.base (S.side c true).1) (S.side c true).2 (S.map (S.side c true).1) t :=
  (S.exists_seam c).choose_spec.choose_spec

theorem sides_bijective_aux :
    Bijective (Sum.elim (uncurry fun (c : Fin (Fintype.card S.γ)) b =>
      S.sideEquiv.symm (S.side (S.eγ c) b)) fun e => S.sideEquiv.symm (S.ext (S.eε e))) := by
  have h : (Sum.elim (uncurry fun (c : Fin (Fintype.card S.γ)) b =>
      S.sideEquiv.symm (S.side (S.eγ c) b)) fun e => S.sideEquiv.symm (S.ext (S.eε e))) =
      S.sideEquiv.symm ∘ Sum.elim (uncurry S.side) S.ext ∘
        (Equiv.sumCongr (Equiv.prodCongr S.eγ (Equiv.refl Bool)) S.eε) := by
    funext z
    rcases z with ⟨c, b⟩ | e <;> rfl
  rw [h]
  exact S.sideEquiv.symm.bijective.comp (S.sides_bijective.comp
    (Equiv.sumCongr (Equiv.prodCongr S.eγ (Equiv.refl Bool)) S.eε).bijective)

def toSystem : EmbeddedPieceSystem W where
  count := Fintype.card S.ι
  count_pos := by
    have := S.nonempty
    exact Fintype.card_pos
  kind J := S.kind (S.eι J)
  kind_mem J := S.kind_mem _
  base J := S.base (S.eι J)
  map J := S.map (S.eι J)
  smooth J := S.smooth _
  mfderiv_bijective J := S.mfderiv_bijective _
  covers := by
    rw [← S.covers]
    exact S.eι.surjective.iUnion_comp fun x => range (S.map x)
  seamCount := Fintype.card S.γ
  side c b := S.sideEquiv.symm (S.side (S.eγ c) b)
  externalCount := Fintype.card S.ε
  externalSide e := S.sideEquiv.symm (S.ext (S.eε e))
  sides_bijective := S.sides_bijective_aux
  matching c := S.matching (S.eγ c)
  seam c := S.seam (S.eγ c)
  seam_source c := (S.seam_spec _).1
  seam_neg c t s hs hs1 := ((S.seam_spec _).2.2.1 t s hs hs1).trans (S.map_collar_symm _ _ _).symm
  seam_pos c t s hs hs1 := ((S.seam_spec _).2.2.2.1 t s hs hs1).trans
    (S.map_collar_symm _ _ _).symm
  seam_interior c y hy := (S.seam_spec _).2.2.2.2.1 y hy
  external_local e t := (S.transport (fun x l => IsLocalDiffeomorphAt
    ((SurfaceModel.model (S.base x).surface.kind).prod (𝓡 1)) W.model ∞
    (S.map x) ((S.base x).collar l (t.1, halfZero), t.2)) (S.ext (S.eε e))).mpr
      (S.external_local _ t)
  overlap J J' q q' h := by
    rcases S.overlap _ _ q q' h with h' | ⟨c, t, h'⟩
    · left
      have h1 : S.eι J = S.eι J' := congrArg Sigma.fst h'
      obtain rfl : J = J' := S.eι.injective h1
      have h2 := (Sigma.mk.inj_iff.mp h').2
      rw [eq_of_heq h2]
    · right
      refine ⟨S.eγ.symm c, t, ?_⟩
      rw [Equiv.apply_symm_apply, (S.seam_spec c).2.1, mul_zero, S.flow_zero]
      exact h'

theorem toSystem_map (J : Fin (Fintype.card S.ι)) : S.toSystem.map J = S.map (S.eι J) := rfl

theorem toSystem_externalCount : S.toSystem.externalCount = Fintype.card S.ε := rfl

theorem toSystem_external_collar (e : Fin S.toSystem.externalCount)
    (p : Circle × EuclideanHalfSpace 1) (v : Circle) :
    S.toSystem.map (S.toSystem.externalSide e).1
      ((S.toSystem.base _).collar (S.toSystem.externalSide e).2 p, v) =
        S.map (S.ext (S.eε e)).1 ((S.base _).collar (S.ext (S.eε e)).2 p, v) :=
  S.map_collar_symm _ p v

end SyncedData

end GC.Seifert.Wiring

namespace GC.Seifert.TorusPresentation

variable {W : CompactCarrier.{u}} (T : TorusPresentation W)

structure ComponentRefinement (i : Fin T.components.count) where
  system : EmbeddedPieceSystem (T.Component i)
  port : Fin system.externalCount ≃ T.OwnedSide i
  port_collar : ∀ l p, p ∈ halfCollarSource →
    Subtype.val (system.map (system.externalSide l).1
      ((system.base _).collar (system.externalSide l).2 (p.1.1, p.2), p.1.2)) =
      T.sideCollar (port l).val p

def PieceRefinement.ofComponents (R : ∀ i, T.ComponentRefinement i) : T.PieceRefinement where
  system i := (R i).system
  port i := (R i).port
  port_collar i := (R i).port_collar

variable {T}

def _root_.GC.Seifert.Wiring.SyncedData.toComponentRefinement {i : Fin T.components.count}
    (S : GC.Seifert.Wiring.SyncedData (T.Component i)) (port : S.ε ≃ T.OwnedSide i)
    (hport : ∀ e p, p ∈ halfCollarSource →
      Subtype.val (S.map (S.ext e).1 ((S.base _).collar (S.ext e).2 (p.1.1, p.2), p.1.2)) =
        T.sideCollar (port e).val p) :
    T.ComponentRefinement i where
  system := S.toSystem
  port := S.eε.trans port
  port_collar l p hp := (congrArg Subtype.val (S.toSystem_external_collar l _ _)).trans
    (hport _ p hp)

end GC.Seifert.TorusPresentation
