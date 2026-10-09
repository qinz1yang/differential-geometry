import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.SphereCapAtlas
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.SphereCapOrientations

/-!
The actual spherical cap quotient carries an orientation preserving the original core and the
coherent signed and ball patch orientations. Standard-oriented caps use the same chosen ball maps.
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter Manifold TopologicalSpace
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert
open DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold

attribute [local instance] Handle.closedCellChartedSpaceSucc Handle.closedCellIsManifold

local instance sphereCapGlobalBallLiftCharts :
    ChartedSpace (EuclideanHalfSpace 3) (ULift.{u} MixedBoundaryCertificate.sphereCapBallOpen) :=
  uliftChartedSpace (EuclideanHalfSpace 3) MixedBoundaryCertificate.sphereCapBallOpen

local instance sphereCapGlobalBallLiftSmooth :
    IsManifold (𝓡∂ 3) ∞ (ULift.{u} MixedBoundaryCertificate.sphereCapBallOpen) :=
  isManifold_ulift (𝓡∂ 3) MixedBoundaryCertificate.sphereCapBallOpen

structure SphereCapOrientationData {C : CompactCarrier.{u}} (B : MixedBoundaryCertificate C) where
  signed : Fin B.sphereCount →
    ManifoldOrientation sphereSignedCollarModel (ClosureSphere.{u} × ℝ) 3
  ball : Fin B.sphereCount → ManifoldOrientation (𝓡∂ 3) (ClosedCell 3) 3
  reparameterization : Fin B.sphereCount →
    (ClosedCell 3 ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ ClosedCell 3)
  attaching : Fin B.sphereCount →
    (ClosureSphere.{u} ≃ₘ⟮𝓡 2, 𝓡 2⟯ ClosureSphere.{u})
  choices : ∀ i,
    ((reparameterization i = Diffeomorph.refl (𝓡∂ 3) (ClosedCell 3) ∞ ∧
      attaching i = Diffeomorph.refl (𝓡 2) ClosureSphere.{u} ∞) ∨
     (reparameterization i = sphereCapBallReflection ∧ attaching i = sphereCapBoundaryReflection))
  boundary : ∀ i z, reparameterization i (closureSphereToBall z) =
    closureSphereToBall (attaching i z)
  standard_transport : ∀ i,
    (reparameterization i).preservesOrientation sphereCapBallStandardOrientation (ball i)
  core_transport : ∀ i (p : ClosureSphere.{u} × ℝ)
    (hp : p ∈ (B.sphereCapCoreTransition i).source),
    Orientation.map (Fin 3) (carrierSurgeryPatchTangentEquiv (B.sphereCapCoreTransition i) hp)
      ((signed i).orientation p) = C.orientation.orientation (B.sphereCapCoreTransition i p)
  ball_transport : ∀ i (p : ClosureSphere.{u} × ℝ)
    (hp : p ∈ MixedBoundaryCertificate.sphereCapBallTransition.source),
    Orientation.map (Fin 3)
      (carrierSurgeryPatchTangentEquiv MixedBoundaryCertificate.sphereCapBallTransition hp)
      ((signed i).orientation p) =
        (ball i).orientation (MixedBoundaryCertificate.sphereCapBallTransition p)

namespace MixedBoundaryCertificate

variable {C : CompactCarrier.{u}} (B : MixedBoundaryCertificate C)


local instance sphereCapGlobalCorePatchSmooth (x : B.sphereCapCoreOpen) :
    IsManifold (B.sphereCapPatchModel (.inl x)) ∞ (B.SphereCapPatchSpace (.inl x)) :=
  B.sphereCapPatchSmooth (.inl x)

local instance sphereCapGlobalBallPatchSmooth (i : Fin B.sphereCount) :
    IsManifold (B.sphereCapPatchModel (.inr (.inl i))) ∞
      (B.SphereCapPatchSpace (.inr (.inl i))) := B.sphereCapPatchSmooth (.inr (.inl i))

local instance sphereCapGlobalSignedPatchSmooth (i : Fin B.sphereCount) :
    IsManifold (B.sphereCapPatchModel (.inr (.inr i))) ∞
      (B.SphereCapPatchSpace (.inr (.inr i))) := B.sphereCapPatchSmooth (.inr (.inr i))

def sphereCapOrientationData : SphereCapOrientationData B := by
  choose S V D A hchoices hboundary hstandard hcore hball using B.exists_sphereCapOrientations
  exact ⟨S, V, D, A, hchoices, hboundary, hstandard, hcore, hball⟩

set_option backward.isDefEq.respectTransparency false in
def sphereCapPatchOrientation (a : B.SphereCapPatchIndex) :
    ManifoldOrientation (B.sphereCapPatchModel a) (B.SphereCapPatchSpace a) 3 := by
  cases a with
  | inl x => exact C.orientation.restrictOpen B.sphereCapCoreOpen
  | inr a =>
    cases a with
    | inl i =>
      exact uliftOrientation (𝓡∂ 3) sphereCapBallOpen
        ((B.sphereCapOrientationData.ball i).restrictOpen sphereCapBallOpen)
    | inr i => exact B.sphereCapOrientationData.signed i

local instance sphereCapGlobalCharts :
    ChartedSpace (EuclideanHalfSpace 3) B.SphereCapQuotient := B.sphereCapQuotientChartedSpace

local instance sphereCapGlobalSmooth : IsManifold (𝓡∂ 3) ∞ B.SphereCapQuotient :=
  B.sphereCapQuotientIsManifold

def sphereCapCanonicalPatchDiffeomorph (a : B.SphereCapPatchIndex) :
    PartialDiffeomorph (B.sphereCapPatchModel a) (𝓡∂ 3)
      (B.SphereCapPatchSpace a) B.SphereCapQuotient ∞ :=
  B.sphereCapPatchDiffeomorph B.exists_sphereCapQuotientAtlas.choose_spec.2 a

theorem sphereCapPatchOrientation_core_apply (x y : B.sphereCapCoreOpen) :
    (B.sphereCapPatchOrientation (.inl x)).orientation y = C.orientation.orientation y.val := rfl

set_option backward.isDefEq.respectTransparency false in
theorem sphereCapPatchOrientation_ball_apply (i : Fin B.sphereCount)
    (y : ULift.{u} sphereCapBallOpen) :
    (B.sphereCapPatchOrientation (.inr (.inl i))).orientation y =
      (B.sphereCapOrientationData.ball i).orientation y.down.val := by
  cases y with
  | up y =>
    exact uliftTangentOrientation_apply (𝓡∂ 3) sphereCapBallOpen
      ((B.sphereCapOrientationData.ball i).restrictOpen sphereCapBallOpen) y

private def sphereCapOrientationTransition (a b : B.SphereCapPatchIndex) :
    PartialDiffeomorph (B.sphereCapPatchModel a) (B.sphereCapPatchModel b)
      (B.SphereCapPatchSpace a) (B.SphereCapPatchSpace b) ∞ :=
  (B.sphereCapCanonicalPatchDiffeomorph a).trans (B.sphereCapCanonicalPatchDiffeomorph b).symm

end MixedBoundaryCertificate

section OrientationTransitions

variable {E F H K M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] [TopologicalSpace K]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F K}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N]

set_option backward.isDefEq.respectTransparency false in
private theorem sphereCapTransition_identity
    (d : PartialDiffeomorph I I M M ∞) (O : ManifoldOrientation I M 3)
    (h : ∀ p, p ∈ d.source → d p = p) {p : M} (hp : p ∈ d.source) :
    Orientation.map (Fin 3) (carrierSurgeryPatchTangentEquiv d hp) (O.orientation p) =
      O.orientation (d p) := by
  have he : (d : M → M) =ᶠ[𝓝 p] id := by
    filter_upwards [d.open_source.mem_nhds hp] with q hq
    exact h q hq
  have hL : carrierSurgeryPatchTangentEquiv d hp = LinearEquiv.refl ℝ E := by
    apply LinearEquiv.ext
    intro v
    change mfderiv I I d p v = v
    rw [he.mfderiv_eq, mfderiv_id]
    rfl
  rw [hL, Orientation.map_refl, h p hp]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem sphereCapTransition_reverse
    (d : PartialDiffeomorph I J M N ∞) (e : PartialDiffeomorph J I N M ∞)
    (OM : ManifoldOrientation I M 3) (ON : ManifoldOrientation J N 3)
    (hm : ∀ p, p ∈ d.source → d p ∈ e.source ∧ e (d p) = p)
    (ho : ∀ q (hq : q ∈ e.source),
      Orientation.map (Fin 3) (carrierSurgeryPatchTangentEquiv e hq) (ON.orientation q) =
        OM.orientation (e q)) {p : M} (hp : p ∈ d.source) :
    Orientation.map (Fin 3) (carrierSurgeryPatchTangentEquiv d hp) (OM.orientation p) =
      ON.orientation (d p) := by
  have he := hm p hp
  have hid : (e : N → M) ∘ (d : M → N) =ᶠ[𝓝 p] id := by
    filter_upwards [d.open_source.mem_nhds hp] with q hq
    exact (hm q hq).2
  have hL : (carrierSurgeryPatchTangentEquiv d hp).trans
      (carrierSurgeryPatchTangentEquiv e he.1) = LinearEquiv.refl ℝ E := by
    apply LinearEquiv.ext
    intro v
    change mfderiv J I e (d p) (mfderiv I J d p v) = v
    rw [← mfderiv_comp_apply p (e.mdifferentiableAt (by simp) he.1)
      (d.mdifferentiableAt (by simp) hp), hid.mfderiv_eq, mfderiv_id]
    rfl
  apply (Orientation.map (Fin 3) (carrierSurgeryPatchTangentEquiv e he.1)).injective
  rw [← DifferentialGeometry.orientation_map_trans, hL, Orientation.map_refl, ho, he.2]
  rfl

omit [FiniteDimensional ℝ E] in
set_option backward.isDefEq.respectTransparency false in
private theorem sphereCapLiftedBall_mfderiv_val
    {X : Type*} [TopologicalSpace X] [ChartedSpace H X]
    (f : X → ULift.{u} MixedBoundaryCertificate.sphereCapBallOpen) {p : X}
    (hf : MDifferentiableAt I (𝓡∂ 3) f p) :
    mfderiv I (𝓡∂ 3) (fun q => (f q).down.val) p = mfderiv I (𝓡∂ 3) f p := by
  let U := MixedBoundaryCertificate.sphereCapBallOpen
  let d := (uliftDiffeomorph (𝓡∂ 3) U).symm
  have hdown (y : ULift.{u} U) :
      mfderiv (𝓡∂ 3) (𝓡∂ 3) d y = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 3)) := by
    cases y with
    | up y =>
      have hc := mfderiv_comp y (d.mdifferentiable (by simp) (ULift.up y))
        ((hasMFDerivAt_ulift_up (𝓡∂ 3) U y).mdifferentiableAt)
      have he : (d : ULift.{u} U → U) ∘ (ULift.up : U → ULift.{u} U) = id := rfl
      rw [he, mfderiv_id, mfderiv_ulift_up] at hc
      change ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 3)) =
        (mfderiv (𝓡∂ 3) (𝓡∂ 3) d (ULift.up y)).comp (ContinuousLinearMap.id ℝ _) at hc
      rw [ContinuousLinearMap.comp_id] at hc
      exact hc.symm
  have hc := mfderiv_comp p (d.mdifferentiable (by simp) (f p)) hf
  rw [hdown] at hc
  have hv := DifferentialGeometry.mfderiv_subtypeVal_comp (I := I) (J := 𝓡∂ 3)
    (fun q => (f q).down) p
  change mfderiv I (𝓡∂ 3) (fun q => (f q).down) p =
    (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 3))).comp (mfderiv I (𝓡∂ 3) f p) at hc
  rw [ContinuousLinearMap.id_comp] at hc
  exact hv.trans hc

end OrientationTransitions

namespace MixedBoundaryCertificate

variable {C : CompactCarrier.{u}} (B : MixedBoundaryCertificate C)


attribute [local instance] sphereCapGlobalCharts sphereCapGlobalSmooth
  sphereCapGlobalCorePatchSmooth sphereCapGlobalBallPatchSmooth sphereCapGlobalSignedPatchSmooth

set_option backward.isDefEq.respectTransparency false in
private theorem sphereCapSignedCore_orientation (x : B.sphereCapCoreOpen)
    (i : Fin B.sphereCount) {p : ClosureSphere.{u} × ℝ}
    (hp : p ∈ (B.sphereCapOrientationTransition (.inr (.inr i)) (.inl x)).source) :
    Orientation.map (Fin 3)
      (carrierSurgeryPatchTangentEquiv
        (B.sphereCapOrientationTransition (.inr (.inr i)) (.inl x)) hp)
      ((B.sphereCapPatchOrientation (.inr (.inr i))).orientation p) =
        (B.sphereCapPatchOrientation (.inl x)).orientation
          (B.sphereCapOrientationTransition (.inr (.inr i)) (.inl x) p) := by
  let d := B.sphereCapOrientationTransition (.inr (.inr i)) (.inl x)
  have hm := B.sphereCapSignedCoreTransition_mem x i hp
  have he : (fun q => (d q).val) =ᶠ[𝓝 p] B.sphereCapCoreTransition i := by
    filter_upwards [d.open_source.mem_nhds hp] with q hq
    exact B.sphereCapSignedCoreTransition_apply x i hq
  have hL : carrierSurgeryPatchTangentEquiv d hp =
      carrierSurgeryPatchTangentEquiv (B.sphereCapCoreTransition i) hm := by
    apply LinearEquiv.ext
    intro v
    change mfderiv sphereSignedCollarModel C.model d p v =
      mfderiv sphereSignedCollarModel C.model (B.sphereCapCoreTransition i) p v
    rw [← DifferentialGeometry.mfderiv_subtypeVal_comp d p, he.mfderiv_eq]
    rfl
  change Orientation.map (Fin 3) (carrierSurgeryPatchTangentEquiv d hp)
    ((B.sphereCapOrientationData.signed i).orientation p) = C.orientation.orientation (d p).val
  rw [hL, B.sphereCapOrientationData.core_transport i p hm]
  exact congrArg (β := Orientation ℝ (EuclideanSpace ℝ (Fin 3)) (Fin 3))
    (fun q : C.Carrier => (C.orientation.orientation q :
    Orientation ℝ (EuclideanSpace ℝ (Fin 3)) (Fin 3))) he.eq_of_nhds.symm

set_option backward.isDefEq.respectTransparency false in
private theorem sphereCapSignedBall_orientation (i : Fin B.sphereCount)
    {p : ClosureSphere.{u} × ℝ}
    (hp : p ∈ (B.sphereCapOrientationTransition (.inr (.inr i)) (.inr (.inl i))).source) :
    Orientation.map (Fin 3)
      (carrierSurgeryPatchTangentEquiv
        (B.sphereCapOrientationTransition (.inr (.inr i)) (.inr (.inl i))) hp)
      ((B.sphereCapPatchOrientation (.inr (.inr i))).orientation p) =
        (B.sphereCapPatchOrientation (.inr (.inl i))).orientation
          (B.sphereCapOrientationTransition (.inr (.inr i)) (.inr (.inl i)) p) := by
  let d := B.sphereCapOrientationTransition (.inr (.inr i)) (.inr (.inl i))
  have hm := B.sphereCapSignedBallTransition_mem i hp
  have he : (fun q => (d q).down.val) =ᶠ[𝓝 p] sphereCapBallTransition := by
    filter_upwards [d.open_source.mem_nhds hp] with q hq
    exact B.sphereCapSignedBallTransition_apply i hq
  have hL : carrierSurgeryPatchTangentEquiv d hp =
      carrierSurgeryPatchTangentEquiv sphereCapBallTransition hm := by
    apply LinearEquiv.ext
    intro v
    change mfderiv sphereSignedCollarModel (𝓡∂ 3) d p v =
      mfderiv sphereSignedCollarModel (𝓡∂ 3) sphereCapBallTransition p v
    have hv := congrArg (fun L : (EuclideanSpace ℝ (Fin 2) × ℝ) →L[ℝ]
        EuclideanSpace ℝ (Fin 3) => L v)
      (sphereCapLiftedBall_mfderiv_val (I := sphereSignedCollarModel) d
        (d.mdifferentiableAt (by simp) hp))
    calc
      mfderiv sphereSignedCollarModel (𝓡∂ 3) d p v =
          mfderiv sphereSignedCollarModel (𝓡∂ 3) (fun q => (d q).down.val) p v := hv.symm
      _ = mfderiv sphereSignedCollarModel (𝓡∂ 3) sphereCapBallTransition p v := by
        rw [he.mfderiv_eq]
        rfl
  rw [B.sphereCapPatchOrientation_ball_apply]
  change Orientation.map (Fin 3) (carrierSurgeryPatchTangentEquiv d hp)
    ((B.sphereCapOrientationData.signed i).orientation p) =
      (B.sphereCapOrientationData.ball i).orientation (d p).down.val
  rw [hL, B.sphereCapOrientationData.ball_transport i p hm]
  exact congrArg (β := Orientation ℝ (EuclideanSpace ℝ (Fin 3)) (Fin 3))
    (fun q : ClosedCell 3 =>
    ((B.sphereCapOrientationData.ball i).orientation q :
      Orientation ℝ (EuclideanSpace ℝ (Fin 3)) (Fin 3))) he.eq_of_nhds.symm

private theorem sphereCapOrientationTransition_inverse (a b : B.SphereCapPatchIndex)
    (p : B.SphereCapPatchSpace a)
    (hp : p ∈ (B.sphereCapOrientationTransition a b).source) :
    B.sphereCapOrientationTransition a b p ∈ (B.sphereCapOrientationTransition b a).source ∧
      B.sphereCapOrientationTransition b a (B.sphereCapOrientationTransition a b p) = p := by
  let e := B.sphereCapCanonicalPatchDiffeomorph a
  let f := B.sphereCapCanonicalPatchDiffeomorph b
  change f.symm (e p) ∈ (f.trans e.symm).source ∧ e.symm (f (f.symm (e p))) = p
  change p ∈ e.source ∧ e p ∈ f.target at hp
  have hf : f.symm (e p) ∈ f.source := f.map_target' hp.2
  have hfe : f (f.symm (e p)) = e p := f.right_inv' hp.2
  refine ⟨⟨hf, ?_⟩, ?_⟩
  · change f (f.symm (e p)) ∈ e.target
    rw [hfe]
    exact e.map_source' hp.1
  · rw [hfe]
    exact e.left_inv' hp.1

set_option backward.isDefEq.respectTransparency false in
private theorem sphereCapPatch_orientation_compatible (a b : B.SphereCapPatchIndex)
    (p : B.SphereCapPatchSpace a)
    (hp : p ∈ (B.sphereCapOrientationTransition a b).source) :
    Orientation.map (Fin 3)
      (carrierSurgeryPatchTangentEquiv (B.sphereCapOrientationTransition a b) hp)
      ((B.sphereCapPatchOrientation a).orientation p) =
        (B.sphereCapPatchOrientation b).orientation (B.sphereCapOrientationTransition a b p) := by
  cases a with
  | inl x =>
    cases b with
    | inl y =>
      exact sphereCapTransition_identity (B.sphereCapOrientationTransition (.inl x) (.inl y))
        (C.orientation.restrictOpen B.sphereCapCoreOpen)
        (fun q hq => B.sphereCapCoreCoreTransition_apply x y q hq) hp
    | inr b =>
      cases b with
      | inl j =>
        have h : p ∈ (∅ : Set B.sphereCapCoreOpen) :=
          B.sphereCapCoreBallTransition_empty x j ▸ hp
        exact h.elim
      | inr j =>
        exact sphereCapTransition_reverse
          (B.sphereCapOrientationTransition (.inl x) (.inr (.inr j)))
          (B.sphereCapOrientationTransition (.inr (.inr j)) (.inl x))
          (B.sphereCapPatchOrientation (.inl x)) (B.sphereCapPatchOrientation (.inr (.inr j)))
          (B.sphereCapOrientationTransition_inverse (.inl x) (.inr (.inr j)))
          (fun q hq => B.sphereCapSignedCore_orientation x j hq) hp
  | inr a =>
    cases a with
    | inl i =>
      cases b with
      | inl x =>
        have h : p ∈ (∅ : Set (ULift.{u} sphereCapBallOpen)) :=
          B.sphereCapBallCoreTransition_empty i x ▸ hp
        exact h.elim
      | inr b =>
        cases b with
        | inl j =>
          by_cases hij : i = j
          · subst j
            exact sphereCapTransition_identity
              (B.sphereCapOrientationTransition (.inr (.inl i)) (.inr (.inl i)))
              (B.sphereCapPatchOrientation (.inr (.inl i)))
              (fun q hq => (B.sphereCapPatch (.inr (.inl i))).left_inv hq.1) hp
          · have h : p ∈ (∅ : Set (ULift.{u} sphereCapBallOpen)) :=
              B.sphereCapBallBallTransition_empty i j hij ▸ hp
            exact h.elim
        | inr j =>
          have hij := B.sphereCapBallSignedTransition_index i j hp
          subst j
          exact sphereCapTransition_reverse
            (B.sphereCapOrientationTransition (.inr (.inl i)) (.inr (.inr i)))
            (B.sphereCapOrientationTransition (.inr (.inr i)) (.inr (.inl i)))
            (B.sphereCapPatchOrientation (.inr (.inl i)))
            (B.sphereCapPatchOrientation (.inr (.inr i)))
            (B.sphereCapOrientationTransition_inverse (.inr (.inl i)) (.inr (.inr i)))
            (fun q hq => B.sphereCapSignedBall_orientation i hq) hp
    | inr i =>
      cases b with
      | inl x => exact B.sphereCapSignedCore_orientation x i hp
      | inr b =>
        cases b with
        | inl j =>
          have hij := B.sphereCapSignedBallTransition_index i j hp
          subst j
          exact B.sphereCapSignedBall_orientation i hp
        | inr j =>
          by_cases hij : i = j
          · subst j
            exact sphereCapTransition_identity
              (B.sphereCapOrientationTransition (.inr (.inr i)) (.inr (.inr i)))
              (B.sphereCapPatchOrientation (.inr (.inr i)))
              (fun q hq => (B.sphereCapSignedSeam i).left_inv hq.1) hp
          · have h : p ∈ (∅ : Set (ClosureSphere.{u} × ℝ)) :=
              B.sphereCapSignedSignedTransition_empty i j hij ▸ hp
            exact h.elim

theorem exists_sphereCapGlobalOrientation :
    ∃ O : ManifoldOrientation (𝓡∂ 3) B.SphereCapQuotient 3,
      ∀ (a : B.SphereCapPatchIndex) (p : B.SphereCapPatchSpace a)
        (hp : p ∈ (B.sphereCapCanonicalPatchDiffeomorph a).source),
        Orientation.map (Fin 3)
          (carrierSurgeryPatchTangentEquiv (B.sphereCapCanonicalPatchDiffeomorph a) hp)
          ((B.sphereCapPatchOrientation a).orientation p) =
            O.orientation (B.sphereCapCanonicalPatchDiffeomorph a p) := by
  refine exists_carrierSurgeryOrientation_of_openCover B.sphereCapCanonicalPatchDiffeomorph
    B.sphereCapPatch_cover B.sphereCapPatchOrientation (by simp) ?_
  intro a b p hp
  exact B.sphereCapPatch_orientation_compatible a b p hp

def sphereCapQuotientOrientation : ManifoldOrientation (𝓡∂ 3) B.SphereCapQuotient 3 :=
  B.exists_sphereCapGlobalOrientation.choose

theorem sphereCapQuotientOrientation_transport (a : B.SphereCapPatchIndex)
    (p : B.SphereCapPatchSpace a)
    (hp : p ∈ (B.sphereCapCanonicalPatchDiffeomorph a).source) :
    Orientation.map (Fin 3)
      (carrierSurgeryPatchTangentEquiv (B.sphereCapCanonicalPatchDiffeomorph a) hp)
      ((B.sphereCapPatchOrientation a).orientation p) =
        B.sphereCapQuotientOrientation.orientation (B.sphereCapCanonicalPatchDiffeomorph a p) :=
  B.exists_sphereCapGlobalOrientation.choose_spec a p hp

set_option backward.isDefEq.respectTransparency false in
theorem sphereCapCore_positive (x : B.sphereCapCoreOpen) :
    ∃ h : Bijective (mfderiv C.model (𝓡∂ 3) B.sphereCapCore x.val),
      Orientation.map (Fin 3)
        (LinearEquiv.ofBijective (mfderiv C.model (𝓡∂ 3) B.sphereCapCore x.val).toLinearMap h)
        (C.orientation.orientation x.val) =
          B.sphereCapQuotientOrientation.orientation (B.sphereCapCore x.val) := by
  let d := B.sphereCapCanonicalPatchDiffeomorph (.inl x)
  have hp : x ∈ d.source := mem_univ _
  have he : mfderiv C.model (𝓡∂ 3) d x =
      mfderiv C.model (𝓡∂ 3) B.sphereCapCore x.val :=
    DifferentialGeometry.mfderiv_restrict_open B.sphereCapCore B.sphereCapCoreOpen x
  have hb : Bijective (mfderiv C.model (𝓡∂ 3) B.sphereCapCore x.val) := by
    rw [← he]
    exact (carrierSurgeryPatchTangentEquiv d hp).bijective
  refine ⟨hb, ?_⟩
  have hL : LinearEquiv.ofBijective
      (mfderiv C.model (𝓡∂ 3) B.sphereCapCore x.val).toLinearMap hb =
      carrierSurgeryPatchTangentEquiv d hp := by
    apply LinearEquiv.ext
    intro v
    exact congrArg (fun L : EuclideanSpace ℝ (Fin 3) →L[ℝ]
      EuclideanSpace ℝ (Fin 3) => L v) he.symm
  rw [hL]
  exact B.sphereCapQuotientOrientation_transport (.inl x) x hp

def sphereCapReparameterizedCap (i : Fin B.sphereCount) :
    C(ClosedCell 3, B.SphereCapQuotient) :=
  (B.sphereCapBall i).comp
    ⟨B.sphereCapOrientationData.reparameterization i,
      (B.sphereCapOrientationData.reparameterization i).continuous⟩

theorem sphereCapReparameterizedCap_boundary (i : Fin B.sphereCount)
    (z : ClosureSphere.{u}) :
    B.sphereCapReparameterizedCap i (closureSphereToBall z) =
      B.sphereCapCore (B.sphere i (B.sphereCapOrientationData.attaching i z, halfZero)) := by
  change B.sphereCapBall i
    (B.sphereCapOrientationData.reparameterization i (closureSphereToBall z)) = _
  rw [B.sphereCapOrientationData.boundary]
  exact (B.sphereCap_attachment i (B.sphereCapOrientationData.attaching i z)).symm

set_option backward.isDefEq.respectTransparency false in
private theorem sphereCapBall_patch_differential (i : Fin B.sphereCount)
    (y : sphereCapBallOpen) :
    MDifferentiableAt (𝓡∂ 3) (𝓡∂ 3) (B.sphereCapBall i) y.val ∧
      mfderiv (𝓡∂ 3) (𝓡∂ 3) (B.sphereCapBall i) y.val =
        mfderiv (B.sphereCapPatchModel (.inr (.inl i))) (𝓡∂ 3)
          (B.sphereCapCanonicalPatchDiffeomorph (.inr (.inl i))) (ULift.up y) := by
  let d : PartialDiffeomorph (𝓡∂ 3) (𝓡∂ 3) (ULift.{u} sphereCapBallOpen)
      B.SphereCapQuotient ∞ := B.sphereCapCanonicalPatchDiffeomorph (.inr (.inl i))
  have hp : ULift.up y ∈ d.source := by
    change ULift.up y ∈ (B.sphereCapPatch (.inr (.inl i))).source
    change ULift.up y ∈ (univ ∩ _ ⁻¹' univ)
    exact ⟨mem_univ _, mem_univ _⟩
  have hdup := (d.mdifferentiableAt (by simp) hp).comp y
    ((hasMFDerivAt_ulift_up (𝓡∂ 3) sphereCapBallOpen y).mdifferentiableAt)
  have he : (d : ULift.{u} sphereCapBallOpen → B.SphereCapQuotient) ∘ ULift.up =
      (fun q : sphereCapBallOpen => B.sphereCapBall i q.val) := rfl
  rw [he] at hdup
  refine ⟨DifferentialGeometry.mdifferentiableAt_subtype_iff.mp hdup, ?_⟩
  have hc := mfderiv_comp y (d.mdifferentiableAt (by simp) hp)
    ((hasMFDerivAt_ulift_up (𝓡∂ 3) sphereCapBallOpen y).mdifferentiableAt)
  rw [he, DifferentialGeometry.mfderiv_restrict_open, mfderiv_ulift_up] at hc
  exact hc.trans (ContinuousLinearMap.comp_id _)

set_option backward.isDefEq.respectTransparency false in
private theorem sphereCapBall_positive (i : Fin B.sphereCount) (y : sphereCapBallOpen) :
    ∃ h : Bijective (mfderiv (𝓡∂ 3) (𝓡∂ 3) (B.sphereCapBall i) y.val),
      Orientation.map (Fin 3)
        (LinearEquiv.ofBijective
          (mfderiv (𝓡∂ 3) (𝓡∂ 3) (B.sphereCapBall i) y.val).toLinearMap h)
        ((B.sphereCapOrientationData.ball i).orientation y.val) =
          B.sphereCapQuotientOrientation.orientation (B.sphereCapBall i y.val) := by
  let d := B.sphereCapCanonicalPatchDiffeomorph (.inr (.inl i))
  have hp : ULift.up y ∈ d.source := by
    change ULift.up y ∈ (B.sphereCapPatch (.inr (.inl i))).source
    change ULift.up y ∈ (univ ∩ _ ⁻¹' univ)
    exact ⟨mem_univ _, mem_univ _⟩
  have he := (B.sphereCapBall_patch_differential i y).2
  have hb : Bijective (mfderiv (𝓡∂ 3) (𝓡∂ 3) (B.sphereCapBall i) y.val) := by
    rw [he]
    exact (carrierSurgeryPatchTangentEquiv d hp).bijective
  refine ⟨hb, ?_⟩
  have hL : LinearEquiv.ofBijective
      (mfderiv (𝓡∂ 3) (𝓡∂ 3) (B.sphereCapBall i) y.val).toLinearMap hb =
      carrierSurgeryPatchTangentEquiv d hp := by
    apply LinearEquiv.ext
    intro v
    exact congrArg (fun L : EuclideanSpace ℝ (Fin 3) →L[ℝ]
      EuclideanSpace ℝ (Fin 3) => L v) he
  rw [hL]
  have ho := B.sphereCapQuotientOrientation_transport (.inr (.inl i)) (ULift.up y) hp
  rw [B.sphereCapPatchOrientation_ball_apply] at ho
  exact ho

private theorem sphereCapBallOpen_of_interior (x : ClosedCell 3)
    (hx : (𝓡∂ 3).IsInteriorPoint x) : x ∈ sphereCapBallOpen := by
  have hn : ‖x.val‖ ≤ 1 := by simpa using x.property
  have hne : ‖x.val‖ ≠ 1 := by
    intro he
    have hb : (𝓡∂ 3).IsBoundaryPoint x := by
      change x ∈ (𝓡∂ 3).boundary (ClosedCell 3)
      rw [closedCell_boundary_eq_sphere 2]
      exact he
    exact ((𝓡∂ 3).isInteriorPoint_iff_not_isBoundaryPoint x).mp hx hb
  exact lt_of_le_of_ne hn hne

set_option backward.isDefEq.respectTransparency false in
theorem sphereCapReparameterizedCap_positive (i : Fin B.sphereCount) (x : ClosedCell 3)
    (hx : (𝓡∂ 3).IsInteriorPoint x) :
    ∃ hi : Bijective (mfderiv (𝓡∂ 3) (𝓡 3)
      (Subtype.val : ClosedCell 3 → EuclideanSpace ℝ (Fin 3)) x),
    ∃ hj : Bijective (mfderiv (𝓡∂ 3) (𝓡∂ 3) (B.sphereCapReparameterizedCap i) x),
      Orientation.map (Fin 3)
        ((LinearEquiv.ofBijective (mfderiv (𝓡∂ 3) (𝓡 3)
          (Subtype.val : ClosedCell 3 → EuclideanSpace ℝ (Fin 3)) x).toLinearMap hi).symm.trans
          (LinearEquiv.ofBijective
            (mfderiv (𝓡∂ 3) (𝓡∂ 3) (B.sphereCapReparameterizedCap i) x).toLinearMap hj))
        ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.orientation) =
          B.sphereCapQuotientOrientation.orientation (B.sphereCapReparameterizedCap i x) := by
  let D := B.sphereCapOrientationData.reparameterization i
  have hDx : (𝓡∂ 3).IsInteriorPoint (D x) :=
    ((D.isLocalDiffeomorph x).isInteriorPoint_iff (by simp)).mp hx
  let y : sphereCapBallOpen := ⟨D x, sphereCapBallOpen_of_interior (D x) hDx⟩
  obtain ⟨hb, hball⟩ := B.sphereCapBall_positive i y
  have hc : mfderiv (𝓡∂ 3) (𝓡∂ 3) (B.sphereCapReparameterizedCap i) x =
      (mfderiv (𝓡∂ 3) (𝓡∂ 3) (B.sphereCapBall i) (D x)).comp
        (mfderiv (𝓡∂ 3) (𝓡∂ 3) D x) :=
    mfderiv_comp x (B.sphereCapBall_patch_differential i y).1 (D.mdifferentiable (by simp) x)
  have hj : Bijective (mfderiv (𝓡∂ 3) (𝓡∂ 3) (B.sphereCapReparameterizedCap i) x) := by
    rw [hc]
    exact hb.comp (D.mfderivToContinuousLinearEquiv (by simp) x).bijective
  let hi := closedCell_inclusion_mfderiv_bijective 2 x
  let L := LinearEquiv.ofBijective
    (mfderiv (𝓡∂ 3) (𝓡 3)
      (Subtype.val : ClosedCell 3 → EuclideanSpace ℝ (Fin 3)) x).toLinearMap hi
  have hLi : Orientation.map (Fin 3) L.symm sphereCapEuclideanOrientation =
      sphereCapBallStandardOrientation.orientation x := by
    apply (Orientation.map (Fin 3) L).injective
    rw [← DifferentialGeometry.orientation_map_trans, LinearEquiv.symm_trans_self,
      Orientation.map_refl]
    exact (sphereCapBallStandardOrientation_inclusion x).symm
  have hL : LinearEquiv.ofBijective
      (mfderiv (𝓡∂ 3) (𝓡∂ 3) (B.sphereCapReparameterizedCap i) x).toLinearMap hj =
      (D.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv.trans
        (LinearEquiv.ofBijective
          (mfderiv (𝓡∂ 3) (𝓡∂ 3) (B.sphereCapBall i) y.val).toLinearMap hb) := by
    apply LinearEquiv.ext
    intro v
    exact congrArg (fun f : EuclideanSpace ℝ (Fin 3) →L[ℝ]
      EuclideanSpace ℝ (Fin 3) => f v) hc
  refine ⟨hi, hj, ?_⟩
  change Orientation.map (Fin 3) (L.symm.trans _) sphereCapEuclideanOrientation = _
  rw [hL, DifferentialGeometry.orientation_map_trans, hLi,
    DifferentialGeometry.orientation_map_trans, B.sphereCapOrientationData.standard_transport i x]
  exact hball

end MixedBoundaryCertificate

end GC.GraphManifold
