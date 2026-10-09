import DifferentialGeometry.Topology.Covering.UniversalDeckGroup
import DifferentialGeometry.Geometry.Metric.UniversalCover.DeckIsometry
import DifferentialGeometry.Geometry.Metric.UniversalCover.DeckIsometryGlobal
import DifferentialGeometry.Geometry.Metric.Pullback.Completeness

/-!
# `deckIsometryHom` (S-HG-INTAKE, suffix `_HGI`)

Verbatim: the declarations `deckIsometryHom`, `deckIsometryHom_apply`,
`deckIsometryHom_injective` that the donor branch `codex/della-mostow-smooth-adapter-20261004`
(467465bc6c) adds to `Geometry/Metric/UniversalCover/DeckIsometryGlobal.lean`; the tracked file
does not have them.
-/

set_option autoImplicit false
noncomputable section
open Set Function Manifold Bundle
open scoped Topology ContDiff Manifold
namespace DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M] [LocallyPathConnectedSpace M]
  [DifferentialGeometry.Geometry.Riemannian.Topology.SemilocallySimplyConnectedSpace M]
  [Inhabited M]

omit [I.Boundaryless] [SigmaCompactSpace M] [ConnectedSpace M] in
attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace in
def deckIsometryHom (g : SmoothRiemannianMetric I M) :
    let ĝ := liftedMetric (I := I) g
    letI : RiemannianBundle (TangentSpace I : UniversalCover M → Type _) := ⟨ĝ.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (TangentSpace I : UniversalCover M → Type _) :=
      ⟨ĝ.inner, ĝ.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : RegularSpace (UniversalCover M) := uc_regularSpace I
    letI : PseudoEMetricSpace (UniversalCover M) := PseudoEMetricSpace.ofRiemannianMetric I _
    FundamentalGroup M (default : M) →* (UniversalCover M ≃ᵢ UniversalCover M) := by
  let ĝ := liftedMetric (I := I) g
  let _ : RiemannianBundle (TangentSpace I : UniversalCover M → Type _) := ⟨ĝ.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E (TangentSpace I : UniversalCover M → Type _) :=
    ⟨ĝ.inner, ĝ.contMDiff.continuous, fun _ _ _ => rfl⟩
  let _ : RegularSpace (UniversalCover M) := uc_regularSpace I
  let _ : PseudoEMetricSpace (UniversalCover M) := PseudoEMetricSpace.ofRiemannianMetric I _
  refine
    { toFun := fun γ =>
        { toEquiv := (deckDiffeo (I := I) γ).toEquiv
          isometry_toFun := universalCover_deck_isometry_of_liftedMetric g γ }
      map_one' := ?_
      map_mul' := ?_ }
  · apply IsometryEquiv.ext
    intro z
    exact one_smul (FundamentalGroup M (default : M)) z
  · intro γ δ
    apply IsometryEquiv.ext
    intro z
    exact mul_smul γ δ z

omit [I.Boundaryless] [SigmaCompactSpace M] [ConnectedSpace M] in
attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace in
@[simp] theorem deckIsometryHom_apply (g : SmoothRiemannianMetric I M) :
    let ĝ := liftedMetric (I := I) g
    letI : RiemannianBundle (TangentSpace I : UniversalCover M → Type _) := ⟨ĝ.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (TangentSpace I : UniversalCover M → Type _) :=
      ⟨ĝ.inner, ĝ.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : RegularSpace (UniversalCover M) := uc_regularSpace I
    letI : PseudoEMetricSpace (UniversalCover M) := PseudoEMetricSpace.ofRiemannianMetric I _
    ∀ (γ : FundamentalGroup M (default : M)) (z : UniversalCover M),
      deckIsometryHom g γ z = deckDiffeo (I := I) γ z := by
  let ĝ := liftedMetric (I := I) g
  let _ : RiemannianBundle (TangentSpace I : UniversalCover M → Type _) := ⟨ĝ.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E (TangentSpace I : UniversalCover M → Type _) :=
    ⟨ĝ.inner, ĝ.contMDiff.continuous, fun _ _ _ => rfl⟩
  let _ : RegularSpace (UniversalCover M) := uc_regularSpace I
  let _ : PseudoEMetricSpace (UniversalCover M) := PseudoEMetricSpace.ofRiemannianMetric I _
  dsimp only
  intro γ z
  rfl

omit [I.Boundaryless] [SigmaCompactSpace M] [ConnectedSpace M] in
attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace in
theorem deckIsometryHom_injective (g : SmoothRiemannianMetric I M) :
    let ĝ := liftedMetric (I := I) g
    letI : RiemannianBundle (TangentSpace I : UniversalCover M → Type _) := ⟨ĝ.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (TangentSpace I : UniversalCover M → Type _) :=
      ⟨ĝ.inner, ĝ.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : RegularSpace (UniversalCover M) := uc_regularSpace I
    letI : PseudoEMetricSpace (UniversalCover M) := PseudoEMetricSpace.ofRiemannianMetric I _
    Function.Injective (deckIsometryHom g) := by
  let ĝ := liftedMetric (I := I) g
  let _ : RiemannianBundle (TangentSpace I : UniversalCover M → Type _) := ⟨ĝ.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E (TangentSpace I : UniversalCover M → Type _) :=
    ⟨ĝ.inner, ĝ.contMDiff.continuous, fun _ _ _ => rfl⟩
  let _ : RegularSpace (UniversalCover M) := uc_regularSpace I
  let _ : PseudoEMetricSpace (UniversalCover M) := PseudoEMetricSpace.ofRiemannianMetric I _
  dsimp only
  intro γ δ h
  apply DifferentialGeometry.Topology.Covering.fundamentalGroupToDeck_injective
  apply Subtype.ext
  apply Homeomorph.ext
  intro z
  exact congrArg (fun e : UniversalCover M ≃ᵢ UniversalCover M => e z) h

end DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover
