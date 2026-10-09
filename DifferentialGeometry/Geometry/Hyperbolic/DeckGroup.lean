import DifferentialGeometry.Geometry.Hyperbolic.DeckRepresentation
import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.FixedPoint
import DifferentialGeometry.Geometry.Metric.Isometry.Covering

noncomputable section

open scoped Manifold ContDiff Bundle

namespace DifferentialGeometry.Geometry.Hyperbolic

open Riemannian.Topology (UniversalCover SemilocallySimplyConnectedSpace
  manifold_semilocallySimplyConnectedSpace)

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E₃ H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem discreteTopology_range_normalizedUniversalCoverDeckRepresentation (g : SmoothRiemannianMetric I M)
    (hg : RiemannianMetricComplete (I := I) g) (κ : ℝ) (hκ : κ < 0) (x₀ : M)
    (hsec : ∀ (x : M) (X Y : TangentSpace I x),
      Curvature.metricRm04StandardAt g x X Y Y X =
        κ * (g.inner x X X * g.inner x Y Y - g.inner x X Y * g.inner x X Y)) :
    letI : Inhabited M := ⟨x₀⟩
    letI : LocallyPathConnectedSpace H := I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
    letI : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace H M
    letI : SemilocallySimplyConnectedSpace M := manifold_semilocallySimplyConnectedSpace (I := I)
    letI : SecondCountableTopology H := ModelWithCorners.secondCountableTopology I
    letI : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
    let gN := scaleMetric (-κ) (neg_pos.mpr hκ) g
    let ĝ := UniversalCover.liftedMetric (I := I) gN
    let hĝ : RiemannianMetricComplete ĝ := UniversalCover.liftedMetric_complete gN (hg.scaleMetric _ _)
    letI : IsManifold I 1 (UniversalCover M) :=
      IsManifold.of_le (I := I) (M := UniversalCover M) (n := ∞) (by decide)
    letI : TopologicalSpace.MetrizableSpace (UniversalCover M) := Manifold.metrizableSpace I (UniversalCover M)
    letI : T3Space (UniversalCover M) := inferInstance
    letI : Bundle.RiemannianBundle (TangentSpace I : UniversalCover M → Type _) := ⟨ĝ.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E₃ (TangentSpace I : UniversalCover M → Type _) :=
      ⟨⟨ĝ.inner, ĝ.contMDiff.continuous, by intro x v w; rfl⟩⟩
    letI : EMetricSpace (UniversalCover M) := EMetricSpace.ofRiemannianMetric I (UniversalCover M)
    letI : PseudoEMetricSpace (UniversalCover M) :=
      (EMetricSpace.ofRiemannianMetric I (UniversalCover M)).toPseudoEMetricSpace
    letI : CompleteSpace (UniversalCover M) := hĝ.complete
    ∀ (i : E₃ ≃ₗᵢ[ℝ] TangentSpace I (UniversalCover.basePoint (X := M))),
      DiscreteTopology (normalizedUniversalCoverDeckRepresentation g hg κ hκ x₀ hsec i).range := by
  let _ : Inhabited M := ⟨x₀⟩
  let _ : LocallyPathConnectedSpace H := I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  let _ : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace H M
  let _ : SemilocallySimplyConnectedSpace M := manifold_semilocallySimplyConnectedSpace (I := I)
  let _ : SecondCountableTopology H := ModelWithCorners.secondCountableTopology I
  let _ : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
  let gN := scaleMetric (-κ) (neg_pos.mpr hκ) g
  let ĝ := UniversalCover.liftedMetric (I := I) gN
  let hĝ : RiemannianMetricComplete ĝ := UniversalCover.liftedMetric_complete gN (hg.scaleMetric _ _)
  let _ : IsManifold I 1 (UniversalCover M) :=
    IsManifold.of_le (I := I) (M := UniversalCover M) (n := ∞) (by decide)
  let _ : TopologicalSpace.MetrizableSpace (UniversalCover M) := Manifold.metrizableSpace I (UniversalCover M)
  let _ : T3Space (UniversalCover M) := inferInstance
  let _ : Bundle.RiemannianBundle (TangentSpace I : UniversalCover M → Type _) := ⟨ĝ.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E₃ (TangentSpace I : UniversalCover M → Type _) :=
    ⟨⟨ĝ.inner, ĝ.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let _ : EMetricSpace (UniversalCover M) := EMetricSpace.ofRiemannianMetric I (UniversalCover M)
  let _ : PseudoEMetricSpace (UniversalCover M) :=
    (EMetricSpace.ofRiemannianMetric I (UniversalCover M)).toPseudoEMetricSpace
  let _ : CompleteSpace (UniversalCover M) := hĝ.complete
  dsimp only
  intro i
  let e := normalizedUniversalCoverIsometryEquiv g hg κ hκ x₀ hsec i
  let ρ := normalizedUniversalCoverDeckRepresentation g hg κ hκ x₀ hsec i
  let pH : Hyperboloid E₃ → M := fun z => UniversalCover.proj (e z)
  have hpH : IsCoveringMap pH :=
    UniversalCover.proj_isCoveringMap.comp_homeomorph e.toHomeomorph
  let : ConnectedSpace (Hyperboloid E₃) :=
    (Hyperboloid.spaceHomeomorph (E := E₃)).symm.surjective.connectedSpace
      (Hyperboloid.spaceHomeomorph (E := E₃)).symm.continuous
  have hρ : ∀ a : ρ.range, ∀ z, pH ((a : Hyperboloid E₃ ≃ᵢ Hyperboloid E₃) z) = pH z := by
    intro a z
    obtain ⟨γ, hγ⟩ := a.property
    rw [← hγ]
    exact proj_normalizedUniversalCoverDeckRepresentation g hg κ hκ x₀ hsec i γ z
  exact IsometryEquiv.discreteTopology_subgroup_of_isCoveringMap hpH ρ.range hρ

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem normalizedUniversalCoverDeckRepresentation_range_isOfFinOrder_iff_eq_one (g : SmoothRiemannianMetric I M)
    (hg : RiemannianMetricComplete (I := I) g) (κ : ℝ) (hκ : κ < 0) (x₀ : M)
    (hsec : ∀ (x : M) (X Y : TangentSpace I x),
      Curvature.metricRm04StandardAt g x X Y Y X =
        κ * (g.inner x X X * g.inner x Y Y - g.inner x X Y * g.inner x X Y)) :
    letI : Inhabited M := ⟨x₀⟩
    letI : LocallyPathConnectedSpace H := I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
    letI : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace H M
    letI : SemilocallySimplyConnectedSpace M := manifold_semilocallySimplyConnectedSpace (I := I)
    letI : SecondCountableTopology H := ModelWithCorners.secondCountableTopology I
    letI : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
    let gN := scaleMetric (-κ) (neg_pos.mpr hκ) g
    let ĝ := UniversalCover.liftedMetric (I := I) gN
    let hĝ : RiemannianMetricComplete ĝ := UniversalCover.liftedMetric_complete gN (hg.scaleMetric _ _)
    letI : IsManifold I 1 (UniversalCover M) :=
      IsManifold.of_le (I := I) (M := UniversalCover M) (n := ∞) (by decide)
    letI : TopologicalSpace.MetrizableSpace (UniversalCover M) := Manifold.metrizableSpace I (UniversalCover M)
    letI : T3Space (UniversalCover M) := inferInstance
    letI : Bundle.RiemannianBundle (TangentSpace I : UniversalCover M → Type _) := ⟨ĝ.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E₃ (TangentSpace I : UniversalCover M → Type _) :=
      ⟨⟨ĝ.inner, ĝ.contMDiff.continuous, by intro x v w; rfl⟩⟩
    letI : EMetricSpace (UniversalCover M) := EMetricSpace.ofRiemannianMetric I (UniversalCover M)
    letI : PseudoEMetricSpace (UniversalCover M) :=
      (EMetricSpace.ofRiemannianMetric I (UniversalCover M)).toPseudoEMetricSpace
    letI : CompleteSpace (UniversalCover M) := hĝ.complete
    ∀ (i : E₃ ≃ₗᵢ[ℝ] TangentSpace I (UniversalCover.basePoint (X := M)))
      (a : (normalizedUniversalCoverDeckRepresentation g hg κ hκ x₀ hsec i).range),
      IsOfFinOrder a ↔ a = 1 := by
  let _ : Inhabited M := ⟨x₀⟩
  let _ : LocallyPathConnectedSpace H := I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  let _ : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace H M
  let _ : SemilocallySimplyConnectedSpace M := manifold_semilocallySimplyConnectedSpace (I := I)
  let _ : SecondCountableTopology H := ModelWithCorners.secondCountableTopology I
  let _ : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
  let gN := scaleMetric (-κ) (neg_pos.mpr hκ) g
  let ĝ := UniversalCover.liftedMetric (I := I) gN
  let hĝ : RiemannianMetricComplete ĝ := UniversalCover.liftedMetric_complete gN (hg.scaleMetric _ _)
  let _ : IsManifold I 1 (UniversalCover M) :=
    IsManifold.of_le (I := I) (M := UniversalCover M) (n := ∞) (by decide)
  let _ : TopologicalSpace.MetrizableSpace (UniversalCover M) := Manifold.metrizableSpace I (UniversalCover M)
  let _ : T3Space (UniversalCover M) := inferInstance
  let _ : Bundle.RiemannianBundle (TangentSpace I : UniversalCover M → Type _) := ⟨ĝ.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E₃ (TangentSpace I : UniversalCover M → Type _) :=
    ⟨⟨ĝ.inner, ĝ.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let _ : EMetricSpace (UniversalCover M) := EMetricSpace.ofRiemannianMetric I (UniversalCover M)
  let _ : PseudoEMetricSpace (UniversalCover M) :=
    (EMetricSpace.ofRiemannianMetric I (UniversalCover M)).toPseudoEMetricSpace
  let _ : CompleteSpace (UniversalCover M) := hĝ.complete
  dsimp only
  intro i a
  let e := normalizedUniversalCoverIsometryEquiv g hg κ hκ x₀ hsec i
  let ρ := normalizedUniversalCoverDeckRepresentation g hg κ hκ x₀ hsec i
  let pH : Hyperboloid E₃ → M := fun z => UniversalCover.proj (e z)
  have hpH : IsCoveringMap pH :=
    UniversalCover.proj_isCoveringMap.comp_homeomorph e.toHomeomorph
  let : ConnectedSpace (Hyperboloid E₃) :=
    (Hyperboloid.spaceHomeomorph (E := E₃)).symm.surjective.connectedSpace
      (Hyperboloid.spaceHomeomorph (E := E₃)).symm.continuous
  have hρ : ∀ a : ρ.range, ∀ z, pH ((a : Hyperboloid E₃ ≃ᵢ Hyperboloid E₃) z) = pH z := by
    intro a z
    obtain ⟨γ, hγ⟩ := a.property
    rw [← hγ]
    exact proj_normalizedUniversalCoverDeckRepresentation g hg κ hκ x₀ hsec i γ z
  let : IsIsometricSMul ρ.range (Hyperboloid E₃) :=
    ⟨fun b => (b : Hyperboloid E₃ ≃ᵢ Hyperboloid E₃).isometry⟩
  let : IsCancelSMul ρ.range (Hyperboloid E₃) :=
    isCancelSMul_iff_eq_one_of_smul_eq.mpr (by
      intro b z hz
      apply Subtype.ext
      apply IsometryEquiv.ext
      have heq : ((b : Hyperboloid E₃ ≃ᵢ Hyperboloid E₃) : Hyperboloid E₃ → Hyperboloid E₃) = id :=
        hpH.eq_of_comp_eq (b : Hyperboloid E₃ ≃ᵢ Hyperboloid E₃).continuous
          continuous_id (funext (hρ b)) z hz
      exact congrFun heq)
  exact Hyperboloid.isOfFinOrder_iff_eq_one (E := E₃) ρ.range a

end DifferentialGeometry.Geometry.Hyperbolic
