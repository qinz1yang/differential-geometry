import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageSlimOnly74
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0SingletonRows

/-!
# Draft 74, A0 inhabitant: the closed slim loop `S² × S¹` (X136 `slimW`)

Lane S-JUNCTIONS (suffix `_JN74`). The NON-EMPTY slim inhabitant of the contracts: the actual slim
stage `f₃ : S² × S¹ → S¹` (the second factor, through the whole piece), `K₃ = D₃ = S¹` (the whole
circle component, never excluded in the closed route, D74-9), the slim piece the whole `S² × S¹`
with its `overCircle` model, no zero domain, no cusp, no residual face. `M₁ = W`, the slim set is
`W`, `M₂ = M₃ = ∅`.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0.X136

/-- `slimW` as a reducible abbreviation (so that instance search sees the carrier). -/
abbrev slimWc : CompactCarrier.{0} := NoCuts.carrier sphereTwoTimesCircleLift

/-- The whole-piece diffeomorphism, from the carrier to the slim piece. -/
def slimBack74 : slimWc.Carrier ≃ₘ⟮𝓡 3, 𝓡∂ 3⟯ slimPiece.Piece :=
  (wholeDiffeomorph sphereTwoTimesCircleLift).symm

/-- The slim stage map `f₃ = slimProjection ∘ (whole diffeomorphism)⁻¹` on the open parent `⊤`. -/
def slimLoopProj74 : C((⊤ : TopologicalSpace.Opens slimWc.Carrier), Circle) where
  toFun x := slimProjection (slimBack74 x.1)
  continuous_toFun :=
    slimProjection_smooth.continuous.comp (slimBack74.continuous.comp continuous_subtype_val)

theorem slimLoopProj74_smooth : ContMDiff slimWc.model (𝓡 1) ∞ slimLoopProj74 :=
  slimProjection_smooth.comp (slimBack74.contMDiff.comp contMDiff_subtype_val)

theorem slimLoopProj74_submersion (x : (⊤ : TopologicalSpace.Opens slimWc.Carrier)) :
    Surjective (mfderiv slimWc.model (𝓡 1) slimLoopProj74 x) := by
  intro v
  obtain ⟨u', hu'⟩ := slimProjection_submersion (slimBack74 x.1) v
  obtain ⟨u, hu⟩ := (slimBack74.mfderivToContinuousLinearEquiv (by simp) x.1).surjective u'
  refine ⟨u, ?_⟩
  have h1 := mfderiv_comp (I := slimWc.model) (I' := 𝓡∂ 3) (I'' := 𝓡 1) x
    (g := slimProjection) (f := fun y : (⊤ : TopologicalSpace.Opens slimWc.Carrier) =>
      slimBack74 y.1) (slimProjection_smooth.mdifferentiableAt (by simp))
    ((slimBack74.contMDiff.comp contMDiff_subtype_val).mdifferentiableAt (by simp))
  have h2 := mfderiv_comp (I := slimWc.model) (I' := slimWc.model) (I'' := 𝓡∂ 3) x
    (g := slimBack74) (f := (Subtype.val : (⊤ : TopologicalSpace.Opens slimWc.Carrier) →
      slimWc.Carrier)) (slimBack74.contMDiff.mdifferentiableAt (by simp))
    ((contMDiff_subtype_val (n := ∞)).mdifferentiableAt (by simp))
  have h3 := DifferentialGeometry.mfderiv_subtype_val (I := slimWc.model)
    (⊤ : TopologicalSpace.Opens slimWc.Carrier) x
  have h4 := congrArg (fun L => L u) h1
  have h5 := congrArg (fun L => L u) h2
  have h6 := congrArg (fun L => L u) h3
  refine h4.trans ?_
  refine (congrArg (mfderiv (𝓡∂ 3) (𝓡 1) slimProjection (slimBack74 x.1)) h5).trans ?_
  exact (congrArg _ ((congrArg _ h6).trans hu)).trans hu'

/-- **The actual slim stage of `S² × S¹`**: the circle base, the parent `⊤`, the second-factor map;
`C₃` is the whole circle, no slab image, no face points. -/
def slimLoopStage74 : SlimStage74 slimWc where
  Base := Circle
  parent := ⊤
  parent_interior := fun x _ =>
    ((NoCuts.interiorDiffeomorph sphereTwoTimesCircleLift).symm x).property
  proj := slimLoopProj74
  proj_smooth := slimLoopProj74_smooth
  proj_submersion := slimLoopProj74_submersion
  C₃ := univ
  slabImage := ∅
  facePoints := ∅

/-- `A`: the actual stage geometry of the `S² × S¹` loop (no zero domain, one slim stage over the
circle, empty edge and circle stages). -/
def slimLoopStageGeometry74 : SmoothStageGeometry74 slimWc (BoundaryTori.empty slimWc) :=
  SmoothStageGeometry74.ofSlim74 slimZero slimCusps slimLoopStage74

theorem slimLoopReq74 : slimLoopStage74.slabImage ∪ slimLoopStage74.facePoints ⊆
    interior (univ : Set slimLoopStage74.Base) := by
  change (∅ : Set Circle) ∪ ∅ ⊆ interior univ
  simp

/-- `D`: the cut choice with `K₃ = D₃ = S¹` (the whole circle component of the closed route). -/
def slimLoopCutChoice74 : StageCutChoice74 slimLoopStageGeometry74 :=
  StageCutChoice74.ofSlim74 slimZero slimCusps slimLoopStage74 univ univ
    (isCompact_univ : IsCompact (univ : Set Circle))
    (isCompact_univ : IsCompact (univ : Set Circle))
    (univ_inter univ).symm slimLoopReq74 (by simp)

theorem slimLoopCutChoice74_slimSet : slimLoopCutChoice74.slimSet = univ :=
  eq_univ_of_univ_subset fun _ _ => ⟨trivial, mem_univ _⟩

theorem actualComponent_univ_circle74 (K : ActualComponent (univ : Set Circle)) : K.1 = univ := by
  obtain ⟨x, -, hK⟩ := K.2
  rw [hK, connectedComponentIn_univ]
  exact PreconnectedSpace.connectedComponent_eq_univ x

/-- The slim piece of the loop: the whole `S² × S¹` over the single component `D₃ = S¹`. -/
def slimLoopSlimCut74 : SlimCutPieces74 slimLoopStageGeometry74 slimLoopCutChoice74 where
  pieces := slimPieces
  componentEquiv :=
    { toFun := fun _ => ActualComponent.of (mem_univ (1 : Circle))
      invFun := fun _ => (0 : Fin 1)
      left_inv := fun j => Subsingleton.elim (α := Fin 1) _ _
      right_inv := fun K => Subtype.ext
        ((actualComponent_univ_circle74 (ActualComponent.of (mem_univ (1 : Circle)))).trans
          (actualComponent_univ_circle74 K).symm) }
  piece_range := fun j => by
    ext x
    refine ⟨fun _ => ⟨trivial, ?_⟩, fun _ => ?_⟩
    · change slimLoopProj74 ⟨x, trivial⟩ ∈ (ActualComponent.of (mem_univ (1 : Circle))).1
      rw [actualComponent_univ_circle74]
      exact mem_univ _
    · exact (wholePiece_range sphereTwoTimesCircleLift).symm ▸ mem_univ x
  shared_eq := fun e _ _ => e.2.elim

theorem slimRegionM1_c : regionM1 (W := slimWc) slimZero slimCusps = univ := slimRegionM1

theorem relativeInteriorUniv_c : relInt (univ : Set slimWc.Carrier) univ = univ :=
  relativeInteriorUniv _

theorem slimLoopCutChoice74_M₂ : slimLoopCutChoice74.M₂ = ∅ := by
  change regionM1 (W := slimWc) slimZero slimCusps \ relInt (regionM1 (W := slimWc) slimZero
    slimCusps) slimLoopCutChoice74.slimSet = ∅
  rw [slimRegionM1_c, slimLoopCutChoice74_slimSet, relativeInteriorUniv_c, sdiff_self]

/-- `H`: the cut geometry of the `S² × S¹` loop. -/
def slimLoopCutGeometry74 : StageCutGeometry74 slimLoopStageGeometry74 slimLoopCutChoice74 :=
  StageCutGeometry74.slimOnly74 slimZero slimCusps slimLoopStage74 slimLoopCutChoice74
    slimLoopSlimCut74 slimLoopCutChoice74_M₂
    (eq_univ_of_univ_subset fun x _ => Or.inl (Or.inr (slimLoopCutChoice74_slimSet ▸ mem_univ x)))
    (fun x _ => slimRegionM1_c ▸ mem_univ x)
    (fun i _ => i.elim0)
    (configurationResidualEmpty true) (configurationSharedEmpty true)

end GC.GraphManifold.Assembly.FC39P0.X136
