import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MixedSplitCapped
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.RelativeCutCapPresentationFixed

/-!
# The fixed reparametrisation of a mixed split

Lane MS, tier MS3 (design `handoffs/20261004-design-ms-mixed-split.md` §1.1, answer to Codex X45's
contract question). Let `D` be side data of a split seam `j` on side `b` of a mixed stage `σ` with
split datum `S`. A side of a seam `c` that is a port of the host `H` is a host circle
`hostPortOf` different from `hostSide` (`hostPortOf_ne_hostSide`), hence the port of exactly one
capped solid torus `D.solidOf`. `sideTwist D c β` is the holonomy of that solid torus on host ports
and the identity on every other side; `capReparam D` collects these on all sides. The torus
parameters and width of the new presentation are fixed AFTER the side data:
`T̃ = σ.fixedCapPresentation (capReparam D) δ₂` (Codex X45's `fixedCapPresentation`).

With this choice no meridian-preserving extension of a torus diffeomorphism is needed:
* (I1) the seam of `T̃` is the old seam at `(sideTwist D c true t, δ₂ s)`
  (`fixedCapPresentation_seam`),
* (I2) its matching is `sideTwist D c true ; m ; (sideTwist D c false)⁻¹`
  (`fixedCapPresentation_matching`),
* (I3) on a host port the collar of the capped solid torus is the collar of `T̃` read through the
  core (`solid_collar_eq_fixed`), from `SideData.collar` and the agreement of the standard host
  chart with the actual host collars on the sub-collar of the split datum
  (`cutMap_sideCollar_hostPort`); on every other side the collar of `T̃` is the old collar at
  height `δ₂ s` (`fixedCapPresentation_sideCollar_of_not_host`).
-/

set_option autoImplicit false

noncomputable section
open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert.RelativeNormalization.MixedStage

open GC.Seifert.ElementaryPresentation (pantsCollar_eq)

variable {Q : ConnectedClosedOrientedManifold.{u} 3} (σ : MixedStage Q)
  {j : Fin σ.toTorus.pairing.count} {b : Bool} {h : σ.IsSplitSeam j b} (S : σ.SplitData h)

theorem cutMap_sideCollar_hostPort (l : Fin 3) (τ : Torus) {r : ℝ} (hr : 0 ≤ r)
    (hrδ : r < S.δ) (hr1 : r < 1) :
    σ.toTorus.cutMap (σ.toTorus.sideCollar
      (σ.standardPort (σ.hostPiece j b) (σ.hostPiece_not_frozen h) h.2.2.1 l).val
      (τ, halfPoint r hr)) =
      σ.hostMap S (planarCollarFormula 3 l ((τ.1 : ℂ), r), τ.2) := by
  have hp : (τ, halfPoint r hr) ∈ halfCollarSource := hr1
  have e1 := TorusPresentation.pieceCollar_apply σ.toTorus (σ.hostPiece j b)
    (σ.standardPort (σ.hostPiece j b) (σ.hostPiece_not_frozen h) h.2.2.1 l) hp
  have e2 := S.hH l (τ, halfPoint r hr) hp hrδ
  rw [← e1, e2]
  change σ.toTorus.cutMap (S.ΘH (pantsPlanarBase.{u}.collar l
    (τ.1, halfPoint r hr), τ.2) : σ.toTorus.cutCarrier.Carrier) = _
  rw [pantsCollar_eq _ hr hr1]
  rfl

variable (h) in
def hostPortOf {c : Fin σ.toTorus.pairing.count} {β : Bool}
    (hH : σ.seamPiece c β = σ.hostPiece j b) : Fin 3 :=
  (σ.standardPort (σ.hostPiece j b) (σ.hostPiece_not_frozen h) h.2.2.1).symm
    ⟨σ.seamSide c β, (σ.sidePiece_seamSide c β).trans hH⟩

theorem standardPort_hostPortOf {c : Fin σ.toTorus.pairing.count} {β : Bool}
    (hH : σ.seamPiece c β = σ.hostPiece j b) :
    (σ.standardPort (σ.hostPiece j b) (σ.hostPiece_not_frozen h) h.2.2.1
      (σ.hostPortOf h hH)).val = σ.seamSide c β := by
  unfold hostPortOf
  rw [Equiv.apply_symm_apply]

theorem hostPortOf_ne_hostSide {c : Fin σ.toTorus.pairing.count} (hc : c ≠ j) {β : Bool}
    (hH : σ.seamPiece c β = σ.hostPiece j b) : σ.hostPortOf h hH ≠ σ.hostSide h := by
  intro he
  have he' := congrArg Subtype.val
    ((σ.standardPort (σ.hostPiece j b) (σ.hostPiece_not_frozen h) h.2.2.1).symm.injective
      (he.trans rfl))
  exact hc ((σ.seamSide_eq_seamSide_iff).mp he').1

variable {T : SphericalTubeSystem Q.toClosedOrientedManifold} {N : ClosedOrientedManifold.{u} 3}
  {K : SphericalCapping Q.toClosedOrientedManifold N T} {a : T.Index} {δ₂ : ℝ}

namespace SideData

variable {σ S} (D : σ.SideData S K a δ₂)

def solidOf (l : Fin 3) : Bool := decide (l = D.port true)

theorem port_solidOf {l : Fin 3} (hl : l ≠ σ.hostSide h) : D.port (D.solidOf l) = l := by
  unfold solidOf
  by_cases ht : l = D.port true
  · rw [decide_eq_true ht]
    exact ht.symm
  · rw [decide_eq_false ht]
    have h1 : (D.port false).val ≠ (σ.hostSide h).val := fun e => D.port_ne false (Fin.ext e)
    have h2 : (D.port true).val ≠ (σ.hostSide h).val := fun e => D.port_ne true (Fin.ext e)
    have h3 : (D.port false).val ≠ (D.port true).val := fun e => D.port_false_ne_true (Fin.ext e)
    have h4 : l.val ≠ (σ.hostSide h).val := fun e => hl (Fin.ext e)
    have h5 : l.val ≠ (D.port true).val := fun e => ht (Fin.ext e)
    have := (D.port false).isLt
    have := (D.port true).isLt
    have := (σ.hostSide h).isLt
    have := l.isLt
    apply Fin.ext
    omega

theorem solidOf_port : ∀ t, D.solidOf (D.port t) = t
  | true => decide_eq_true rfl
  | false => decide_eq_false D.port_false_ne_true

end SideData

variable {σ S}

open Classical in
def sideTwist (D : σ.SideData S K a δ₂) (c : Fin σ.toTorus.pairing.count) (β : Bool) :
    Torus ≃ₘ⟮torusModel, torusModel⟯ Torus :=
  if hH : σ.seamPiece c β = σ.hostPiece j b then D.holonomy (D.solidOf (σ.hostPortOf h hH))
  else Diffeomorph.refl torusModel Torus ∞

theorem sideTwist_of_host (D : σ.SideData S K a δ₂) (c : Fin σ.toTorus.pairing.count)
    {β : Bool} (hH : σ.seamPiece c β = σ.hostPiece j b) :
    sideTwist D c β = D.holonomy (D.solidOf (σ.hostPortOf h hH)) := by
  classical
  unfold sideTwist
  rw [dite_eq_left hH]

theorem sideTwist_of_not_host (D : σ.SideData S K a δ₂) (c : Fin σ.toTorus.pairing.count)
    {β : Bool} (hH : ¬ σ.seamPiece c β = σ.hostPiece j b) :
    sideTwist D c β = Diffeomorph.refl torusModel Torus ∞ := by
  classical
  unfold sideTwist
  rw [dite_eq_right hH]

def capReparam (D : σ.SideData S K a δ₂) : σ.toTorus.Side → (Torus ≃ₘ⟮torusModel, torusModel⟯ Torus)
  | .inl c => sideTwist D c true
  | .inr (.inl c) => sideTwist D c false
  | .inr (.inr _) => Diffeomorph.refl torusModel Torus ∞

theorem capReparam_seamSide (D : σ.SideData S K a δ₂) (c : Fin σ.toTorus.pairing.count) :
    ∀ β, capReparam D (σ.seamSide c β) = sideTwist D c β
  | true => rfl
  | false => rfl

variable (D : σ.SideData S K a δ₂) (hδ : 0 < δ₂) (hδ1 : δ₂ ≤ 1)

theorem fixedCapPresentation_seam (c : Fin σ.toTorus.pairing.count) (p : Torus × ℝ) :
    (σ.fixedCapPresentation (capReparam D) hδ hδ1).seam c p =
      σ.toTorus.seam c (sideTwist D c true p.1, δ₂ * p.2) := rfl

theorem fixedCapPresentation_matching (c : Fin σ.toTorus.pairing.count) :
    (σ.fixedCapPresentation (capReparam D) hδ hδ1).pairing.matching c =
      ((sideTwist D c true).trans (σ.toTorus.pairing.matching c)).trans
        (sideTwist D c false).symm := rfl

theorem fixedCapPresentation_sideCollar (s : σ.toTorus.Side)
    (p : Torus × EuclideanHalfSpace 1) :
    (σ.fixedCapPresentation (capReparam D) hδ hδ1).sideCollar s p =
      σ.toTorus.sideCollar s (capReparam D s p.1, halfSpaceScale hδ p.2) := by
  rcases s with c | c | i <;> rfl

theorem fixedCapPresentation_sideCollar_seamSide (c : Fin σ.toTorus.pairing.count) (β : Bool)
    (τ : Torus) {r : ℝ} (hr : 0 ≤ r) :
    (σ.fixedCapPresentation (capReparam D) hδ hδ1).sideCollar (σ.seamSide c β)
      (τ, halfPoint r hr) =
      σ.toTorus.sideCollar (σ.seamSide c β)
        (sideTwist D c β τ, halfPoint (δ₂ * r) (mul_nonneg hδ.le hr)) := by
  rw [fixedCapPresentation_sideCollar, capReparam_seamSide, halfSpaceScale_halfPoint]

theorem fixedCapPresentation_sideCollar_of_not_host (c : Fin σ.toTorus.pairing.count) {β : Bool}
    (hH : ¬ σ.seamPiece c β = σ.hostPiece j b) (τ : Torus) {r : ℝ} (hr : 0 ≤ r) :
    (σ.fixedCapPresentation (capReparam D) hδ hδ1).sideCollar (σ.seamSide c β)
      (τ, halfPoint r hr) =
      σ.toTorus.sideCollar (σ.seamSide c β) (τ, halfPoint (δ₂ * r) (mul_nonneg hδ.le hr)) := by
  rw [fixedCapPresentation_sideCollar_seamSide, sideTwist_of_not_host D c hH]
  rfl

theorem solid_collar_eq_fixed {c : Fin σ.toTorus.pairing.count} (hc : c ≠ j) {β : Bool}
    (hH : σ.seamPiece c β = σ.hostPiece j b) (τ : Torus) {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (hlt : δ₂ < S.δ) :
    D.solid (D.solidOf (σ.hostPortOf h hH))
      ((discPlanarBase.{u} 1).collar 0 (τ.1, halfPoint r hr), τ.2) =
      SplitTube.coreMap K (σ.toTorus.cutMap
        ((σ.fixedCapPresentation (capReparam D) hδ hδ1).sideCollar (σ.seamSide c β)
          (τ, halfPoint r hr))) := by
  have hδr : δ₂ * r < S.δ := by nlinarith
  have hδr1 : δ₂ * r < 1 := by nlinarith
  rw [fixedCapPresentation_sideCollar_seamSide, sideTwist_of_host D c hH, D.collar _ τ r hr hr1,
    D.port_solidOf (σ.hostPortOf_ne_hostSide hc hH),
    ← σ.cutMap_sideCollar_hostPort S _ _ (mul_nonneg hδ.le hr) hδr hδr1,
    standardPort_hostPortOf]

end GC.Seifert.RelativeNormalization.MixedStage
