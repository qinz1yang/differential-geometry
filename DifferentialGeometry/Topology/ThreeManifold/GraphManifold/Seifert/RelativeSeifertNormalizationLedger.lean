import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CutCapPortInjective
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.TerminalUnionPrimeRegions

/-!
# The protected seam ledger of the relative normalisation

Lane BR, tier R3 (design `handoffs/20261004-design-br-relative-normalisation.md` §1–3; review 20
§2.2–2.4, §3.3). A protected seam is followed through the steps by exact equations, never by an
isotopy. `CollarLedger κ σ σ'` says that the signed collar `σ'` of the new stage is related by
`κ` to the old collar `σ` precomposed with a torus diffeomorphism `ψ` and a rescaling `s ↦ δ s`,
`0 < δ ≤ 1`, at every point of `signedCollarSource`: `κ (σ (ψ t, δ s)) (σ' (t, s))`. For a surgery
step `κ` is `coreTrack X c` (a core point with the old value whose core inclusion is the new value,
the form of `CappedMixedRefinement.marked_collar`); for a move on the same manifold `κ` is `Eq`.
Ledgers compose (`CollarLedger.trans`): relations compose, the diffeomorphisms compose and the
scales multiply, so a finite sequence of per-step choices gives one exact composite equation (no
minimum over future widths is ever taken).

The invariant (Inc) of the design, π₁-injectivity of the protected seam tori at every basepoint,
is transported along both kinds of steps: under a reparametrisation of the torus by a homeomorphism
(`forall_injective_comp_homeomorph_iff`) and through a spherical cut-cap transition whose
surgery region avoids the old torus, via X27's `cutCapPortInjective_iff`, when the new seam torus
is the core image of the old one (`forall_injective_seamTorus_iff_of_coreTrack`).
-/

set_option autoImplicit false

noncomputable section
open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u v w

namespace GC.Seifert.RelativeNormalization

structure CollarLedger {A : Type v} {B : Type w} (κ : A → B → Prop) (σ : Torus × ℝ → A)
    (σ' : Torus × ℝ → B) where
  reparam : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus
  scale : ℝ
  scale_pos : 0 < scale
  scale_le_one : scale ≤ 1
  tracked : ∀ p ∈ signedCollarSource, κ (σ (reparam p.1, scale * p.2)) (σ' p)

namespace CollarLedger

variable {A : Type v} {B : Type w}

def refl (σ : Torus × ℝ → A) : CollarLedger Eq σ σ where
  reparam := Diffeomorph.refl torusModel Torus ∞
  scale := 1
  scale_pos := one_pos
  scale_le_one := le_rfl
  tracked p _ := by simp

def mono {κ κ' : A → B → Prop} (h : ∀ a b, κ a b → κ' a b) {σ : Torus × ℝ → A}
    {σ' : Torus × ℝ → B} (L : CollarLedger κ σ σ') : CollarLedger κ' σ σ' where
  reparam := L.reparam
  scale := L.scale
  scale_pos := L.scale_pos
  scale_le_one := L.scale_le_one
  tracked p hp := h _ _ (L.tracked p hp)

theorem mem_signedCollarSource_scale {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (ψ : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus) {p : Torus × ℝ}
    (hp : p ∈ signedCollarSource) : (ψ p.1, δ * p.2) ∈ signedCollarSource := by
  obtain ⟨h1, h2⟩ := hp
  have habs : |p.2| < 1 := abs_lt.mpr ⟨h1, h2⟩
  have : |δ * p.2| < 1 := by
    rw [abs_mul, abs_of_pos hδ]
    calc δ * |p.2| ≤ 1 * |p.2| := mul_le_mul_of_nonneg_right hδ1 (abs_nonneg _)
      _ < 1 := by rw [one_mul]; exact habs
  exact abs_lt.mp this

def trans {C : Type*} {κ₁ : A → B → Prop} {κ₂ : B → C → Prop} {σ₀ : Torus × ℝ → A}
    {σ₁ : Torus × ℝ → B} {σ₂ : Torus × ℝ → C} (L₁ : CollarLedger κ₁ σ₀ σ₁)
    (L₂ : CollarLedger κ₂ σ₁ σ₂) : CollarLedger (Relation.Comp κ₁ κ₂) σ₀ σ₂ where
  reparam := L₂.reparam.trans L₁.reparam
  scale := L₁.scale * L₂.scale
  scale_pos := mul_pos L₁.scale_pos L₂.scale_pos
  scale_le_one := by nlinarith [L₁.scale_pos, L₂.scale_pos, L₁.scale_le_one, L₂.scale_le_one]
  tracked p hp := by
    refine ⟨σ₁ (L₂.reparam p.1, L₂.scale * p.2), ?_, L₂.tracked p hp⟩
    have h := L₁.tracked _ (mem_signedCollarSource_scale L₂.scale_pos L₂.scale_le_one
      L₂.reparam hp)
    rw [mul_assoc]
    exact h

theorem tracked_zero {κ : A → B → Prop} {σ : Torus × ℝ → A} {σ' : Torus × ℝ → B}
    (L : CollarLedger κ σ σ') (t : Torus) : κ (σ (L.reparam t, 0)) (σ' (t, 0)) := by
  have h := L.tracked (t, 0) ⟨by norm_num, by norm_num⟩
  simpa only [mul_zero] using h

end CollarLedger

section Transition

variable {M P : ClosedOrientedManifold.{u} 3} (X : SphericalCutCapTransition M P)

def coreTrack (c : ConnectedComponents X.capped.Carrier) (y : M.Carrier)
    (y' : (X.capped.component c).Carrier) : Prop :=
  ∃ x : X.tubes.core, x.val = y ∧ X.capping.coreInclusion x = y'.val

end Transition

theorem forall_injective_comp_homeomorph_iff {Y : Type*} [TopologicalSpace Y] (f : C(Torus, Y))
    (ψ : Torus ≃ₜ Torus) :
    (∀ t₀, Injective (FundamentalGroup.map (f.comp (ψ : C(Torus, Torus))) t₀)) ↔
      ∀ t₀, Injective (FundamentalGroup.map f t₀) := by
  constructor
  · intro h t₁
    obtain ⟨t₀, rfl⟩ := ψ.surjective t₁
    have h0 := h t₀
    rw [GC.Topology.fundamentalGroup_map_comp, MonoidHom.coe_comp] at h0
    intro a b hab
    obtain ⟨a', rfl⟩ := (bijective_map_homeomorph ψ t₀).2 a
    obtain ⟨b', rfl⟩ := (bijective_map_homeomorph ψ t₀).2 b
    exact congrArg _ (h0 hab)
  · intro h t₀
    rw [GC.Topology.fundamentalGroup_map_comp, MonoidHom.coe_comp]
    exact (h (ψ t₀)).comp (bijective_map_homeomorph ψ t₀).1

theorem forall_injective_seamTorus_iff_of_coreTrack {Q : ConnectedClosedOrientedManifold.{u} 3}
    {P : ClosedOrientedManifold.{u} 3} (X : SphericalCutCapTransition Q.toClosedOrientedManifold P)
    (G : TorusPresentation (NoCuts.carrier Q)) (j : Fin G.pairing.count)
    (havoid : Disjoint (range (G.seamTorus j)) X.tubes.surgeryRegion)
    (c : ConnectedComponents X.capped.Carrier)
    (G' : TorusPresentation (NoCuts.carrier (X.capped.component c))) (j' : Fin G'.pairing.count)
    (htrack : ∀ τ, coreTrack X c (G.seamTorus j τ) (G'.seamTorus j' τ)) :
    (∀ t₀, Injective (FundamentalGroup.map (G.seamTorus j) t₀)) ↔
      ∀ t₀, Injective (FundamentalGroup.map (G'.seamTorus j') t₀) := by
  have hlift : ∀ τ, X.capping.coreInclusion (cutCapPortCoreLift X G j havoid τ) =
      (G'.seamTorus j' τ).val := by
    intro τ
    obtain ⟨x, hx, he⟩ := htrack τ
    have : x = cutCapPortCoreLift X G j havoid τ := Subtype.ext hx
    rw [← this, he]
  refine forall_congr' fun t₀ => ?_
  have hc : ConnectedComponents.mk (X.capping.coreInclusion (cutCapPortCoreLift X G j havoid t₀)) =
      c := by
    rw [hlift t₀]
    exact (G'.seamTorus j' t₀).property
  subst hc
  have heq : cutCapPortCappedMap X G j havoid t₀ = G'.seamTorus j' := by
    ext τ
    apply Subtype.ext
    have h := congrArg (fun g : C(Torus, X.capped.Carrier) => g τ)
      (cutCapPortCappedMap_inclusion X G j havoid t₀)
    exact h.trans (hlift τ)
  rw [cutCapPortInjective_iff X G j havoid t₀, heq]

end GC.Seifert.RelativeNormalization
