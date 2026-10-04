import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.RelativeSeifertNormalizationMoves
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.RelativeSeifertNormalizationGraph

/-!
# The step and the termination of the relative normalisation

Lane BR, tier R5 (design `handoffs/20261004-design-br-relative-normalisation.md` §3–4, review 26
§3.4, §4–5). Stages are pairs `⟨Q, σ⟩` of a closed connected oriented `Q` and a mixed stage on
`Q`; the carrier is `Q`, the measure is `σ.innerCount`, terminal means `σ.IsTerminal`. The
marked objects of a stage are its protected seams and its frozen pieces (`stageProt`); the
transported predicate (`stagePred`) is π₁-injectivity of the protected seam tori at every
basepoint, the invariant (Inc).

One step (`step`): a non-terminal stage has an inner merge, absorb or split seam. A merge or
absorb is one application of `MX`: one output stage on the same manifold, no extra summand, and
(Inc) moves along the exact collar ledger because the new seam torus is the old one precomposed
with a torus diffeomorphism (`forall_injective_comp_homeomorph_iff`). A split is one application
of `MixedSplit`: the outputs are the stages on all actual capped components, the count of
`S² × S¹` summands is the cycle rank of the single-tube incidence graph
(`exists_singleTubeExpansion`), the oriented reconstruction is `OrientedSingleSphere` (tier R7),
and (Inc) moves through X27 (`forall_injective_iff_of_coreTrack`, the core-image form of R3's
transport for an arbitrary new torus map) after undoing the ledger's torus diffeomorphism. The
descent engine then gives, for every stage, an expansion into terminal stages
(`exists_terminalExpansion_of_moves`): the factor record with multiplicities, the total
`S² × S¹` count, the oriented reconstruction and the bijection of protected seams and frozen
pieces preserving (Inc). The three hypotheses are the frozen contracts of
`RelativeSeifertNormalizationMoves.lean`.
-/

set_option autoImplicit false

noncomputable section
open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert.RelativeNormalization

theorem forall_injective_iff_of_coreTrack {Q : ConnectedClosedOrientedManifold.{u} 3}
    {P : ClosedOrientedManifold.{u} 3} (X : SphericalCutCapTransition Q.toClosedOrientedManifold P)
    (G : TorusPresentation (NoCuts.carrier Q)) (j : Fin G.pairing.count)
    (havoid : Disjoint (range (G.seamTorus j)) X.tubes.surgeryRegion)
    (c : ConnectedComponents X.capped.Carrier) (g : C(Torus, (X.capped.component c).Carrier))
    (htrack : ∀ τ, coreTrack X c (G.seamTorus j τ) (g τ)) :
    (∀ t₀, Injective (FundamentalGroup.map (G.seamTorus j) t₀)) ↔
      ∀ t₀, Injective (FundamentalGroup.map g t₀) := by
  have hlift : ∀ τ, X.capping.coreInclusion (cutCapPortCoreLift X G j havoid τ) = (g τ).val := by
    intro τ
    obtain ⟨x, hx, he⟩ := htrack τ
    have : x = cutCapPortCoreLift X G j havoid τ := Subtype.ext hx
    rw [← this, he]
  refine forall_congr' fun t₀ => ?_
  have hc : ConnectedComponents.mk (X.capping.coreInclusion (cutCapPortCoreLift X G j havoid t₀)) =
      c := by
    rw [hlift t₀]
    exact (g t₀).property
  subst hc
  have heq : cutCapPortCappedMap X G j havoid t₀ = g := by
    ext τ
    apply Subtype.ext
    have h := congrArg (fun g' : C(Torus, X.capped.Carrier) => g' τ)
      (cutCapPortCappedMap_inclusion X G j havoid t₀)
    exact h.trans (hlift τ)
  rw [cutCapPortInjective_iff X G j havoid t₀, heq]

abbrev Stage : Type (u + 1) := Σ Q : ConnectedClosedOrientedManifold.{u} 3, MixedStage Q

def stageProt (s : Stage.{u}) : Type u := ULift.{u} (s.2.ProtSeam ⊕ s.2.Frozen)

def stagePred (s : Stage.{u}) : stageProt s → Prop
  | ⟨.inl k⟩ => ∀ t₀, Injective (FundamentalGroup.map (s.2.toTorus.seamTorus k.1) t₀)
  | ⟨.inr _⟩ => True

abbrev sphereSummand : ConnectedClosedOrientedManifold.{u} 3 :=
  sphereTwoTimesCircleLift.ulift.{0, u}

theorem seamTorus_eq_comp_of_ledger {Q : ConnectedClosedOrientedManifold.{u} 3}
    {σ σ' : MixedStage Q} {k : Fin σ.toTorus.pairing.count} {k' : Fin σ'.toTorus.pairing.count}
    (L : CollarLedger Eq (σ.toTorus.seam k) (σ'.toTorus.seam k')) :
    σ'.toTorus.seamTorus k' =
      (σ.toTorus.seamTorus k).comp (L.reparam.toHomeomorph : C(Torus, Torus)) := by
  ext t
  exact (L.tracked_zero t).symm

theorem stageInc_iff_of_ledger {Q : ConnectedClosedOrientedManifold.{u} 3}
    {σ σ' : MixedStage Q} {k : Fin σ.toTorus.pairing.count} {k' : Fin σ'.toTorus.pairing.count}
    (L : CollarLedger Eq (σ.toTorus.seam k) (σ'.toTorus.seam k')) :
    (∀ t₀, Injective (FundamentalGroup.map (σ.toTorus.seamTorus k) t₀)) ↔
      ∀ t₀, Injective (FundamentalGroup.map (σ'.toTorus.seamTorus k') t₀) := by
  rw [seamTorus_eq_comp_of_ledger L, forall_injective_comp_homeomorph_iff]

theorem stageInc_iff_of_coreLedger {Q : ConnectedClosedOrientedManifold.{u} 3}
    {P : ClosedOrientedManifold.{u} 3} (X : SphericalCutCapTransition Q.toClosedOrientedManifold P)
    (σ : MixedStage Q) (k : Fin σ.toTorus.pairing.count)
    (havoid : Disjoint (range (σ.toTorus.seamTorus k)) X.tubes.surgeryRegion)
    (c : ConnectedComponents X.capped.Carrier) (σ' : MixedStage (X.capped.component c))
    (k' : Fin σ'.toTorus.pairing.count)
    (L : CollarLedger (coreTrack X c) (σ.toTorus.seam k) (σ'.toTorus.seam k')) :
    (∀ t₀, Injective (FundamentalGroup.map (σ.toTorus.seamTorus k) t₀)) ↔
      ∀ t₀, Injective (FundamentalGroup.map (σ'.toTorus.seamTorus k') t₀) := by
  let ψ : Torus ≃ₜ Torus := L.reparam.toHomeomorph
  let g : C(Torus, (X.capped.component c).Carrier) :=
    (σ'.toTorus.seamTorus k').comp (ψ.symm : C(Torus, Torus))
  have htrack : ∀ τ, coreTrack X c (σ.toTorus.seamTorus k τ) (g τ) := by
    intro τ
    have h := L.tracked_zero (ψ.symm τ)
    have hψ : L.reparam (ψ.symm τ) = τ := ψ.apply_symm_apply τ
    rw [hψ] at h
    exact h
  rw [forall_injective_iff_of_coreTrack X σ.toTorus k havoid c g htrack]
  exact forall_injective_comp_homeomorph_iff _ ψ.symm

private theorem step_mx (hMX : MX.{u}) {Q : ConnectedClosedOrientedManifold.{u} 3}
    (σ : MixedStage Q) (j : Fin σ.toTorus.pairing.count) (b : Bool)
    (h : σ.IsMergeSeam j b ∨ σ.IsAbsorbSeam j b) :
    Nonempty (Expansion Sigma.fst sphereSummand stageProt stagePred
      (fun t : Stage.{u} => t.2.innerCount < σ.innerCount) ⟨Q, σ⟩) := by
  obtain ⟨σ', e, f, hcount, hL, -⟩ := hMX Q σ j b h
  refine ⟨
    { Index := PUnit.{u + 1}
      stage := fun _ => ⟨Q, σ'⟩
      enum := [PUnit.unit]
      nodup := List.nodup_singleton _
      complete := fun _ => List.mem_singleton.mpr rfl
      count := 0
      good := fun _ => by change σ'.innerCount < σ.innerCount; omega
      reconstruction := ⟨ClosedOrientedManifold.OrientedDiffeomorph.refl _⟩
      seam := Equiv.ulift.trans ((Equiv.sumCongr e f).trans (Equiv.ulift.symm.trans
        (Equiv.uniqueSigma fun _ : PUnit.{u + 1} => stageProt ⟨Q, σ'⟩).symm))
      seam_pred := ?_ }⟩
  rintro ⟨k | i⟩
  · obtain ⟨L⟩ := hL k
    exact stageInc_iff_of_ledger L
  · exact Iff.rfl

private theorem step_split (hS : MixedSplit.{u}) (hO : OrientedSingleSphere.{u})
    {Q : ConnectedClosedOrientedManifold.{u} 3} (σ : MixedStage Q)
    (j : Fin σ.toTorus.pairing.count) (b : Bool) (hsplit : σ.IsSplitSeam j b) :
    Nonempty (Expansion Sigma.fst sphereSummand stageProt stagePred
      (fun t : Stage.{u} => t.2.innerCount < σ.innerCount) ⟨Q, σ⟩) := by
  obtain ⟨P, X, τ, e, f, hsub, ⟨a⟩, havoid, hcount, hL, -⟩ := hS Q σ j b hsplit
  let stageOf : ConnectedComponents X.capped.Carrier → Stage.{u} :=
    fun c => ⟨X.capped.component c, τ c⟩
  let seam : stageProt ⟨Q, σ⟩ ≃ Σ c, stageProt (stageOf c) :=
    (Equiv.ulift.trans ((Equiv.sumCongr e f).trans (Equiv.sigmaSumDistrib _ _).symm)).trans
      (Equiv.sigmaCongrRight fun _ => Equiv.ulift.symm)
  have hseam : ∀ p, stagePred ⟨Q, σ⟩ p ↔ stagePred (stageOf (seam p).1) (seam p).2 := by
    rintro ⟨k | i⟩
    · obtain ⟨L⟩ := hL k
      exact stageInc_iff_of_coreLedger X σ k.1 (havoid k.1 k.2) (e k).1 (τ (e k).1) (e k).2.1 L
    · exact Iff.rfl
  obtain ⟨E, -⟩ := exists_singleTubeExpansion X Sigma.fst sphereSummand stageProt stagePred
    (fun t : Stage.{u} => t.2.innerCount < σ.innerCount) ⟨Q, σ⟩ a stageOf
    (fun _ => ⟨ClosedOrientedManifold.OrientedDiffeomorph.refl _⟩) hcount
    (hO Q P X a hsub).1 (hO Q P X a hsub).2
    ⟨ClosedOrientedManifold.OrientedDiffeomorph.refl _⟩ seam hseam
  exact ⟨E⟩

theorem step (hMX : MX.{u}) (hS : MixedSplit.{u}) (hO : OrientedSingleSphere.{u}) (s : Stage.{u})
    (hs : ¬ s.2.IsTerminal) :
    Nonempty (Expansion Sigma.fst sphereSummand stageProt stagePred
      (fun t : Stage.{u} => t.2.innerCount < s.2.innerCount) s) := by
  obtain ⟨Q, σ⟩ := s
  obtain ⟨j, b, hmove⟩ := σ.exists_move_of_not_isTerminal hs
  rcases hmove with hm | hsplit | ha
  · exact step_mx hMX σ j b (Or.inl hm)
  · exact step_split hS hO σ j b hsplit
  · exact step_mx hMX σ j b (Or.inr ha)

theorem exists_terminalExpansion_of_moves (hMX : MX.{u}) (hS : MixedSplit.{u})
    (hO : OrientedSingleSphere.{u}) (s : Stage.{u}) :
    Nonempty (Expansion Sigma.fst sphereSummand stageProt stagePred
      (fun t : Stage.{u} => t.2.IsTerminal) s) :=
  exists_terminalExpansion Sigma.fst sphereSummand stageProt stagePred
    (fun t : Stage.{u} => t.2.innerCount) (fun t : Stage.{u} => t.2.IsTerminal)
    (step hMX hS hO) s

end GC.Seifert.RelativeNormalization
