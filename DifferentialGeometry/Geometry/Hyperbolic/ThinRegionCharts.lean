import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Cusps.SmoothGraphChart
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Orbifolds.AxialGraphChart
import DifferentialGeometry.Geometry.Hyperbolic.ProjectiveDeckGroup
import DifferentialGeometry.Geometry.Hyperbolic.ProjectiveQuotient
import DifferentialGeometry.Geometry.Hyperbolic.DeckGroup
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.OpenCodRestrict

noncomputable section

open scoped Manifold ContDiff Bundle ENNReal

namespace DifferentialGeometry.Geometry.Hyperbolic

open Riemannian.Topology (UniversalCover SemilocallySimplyConnectedSpace
  manifold_semilocallySimplyConnectedSpace)
open ProjectiveOrthogonalGroup (PO)
open HyperbolicBoundary (BoundaryH poBoundaryMulAction)

local notation "E₃" => EuclideanSpace ℝ (Fin 3)
local notation "I₃" => 𝓘(ℝ, E₃)
local notation "H₃" => DifferentialGeometry.Hyperbolic.HUpper 3
local notation "K₂" => 𝓘(ℝ, Fin 2 → ℝ)
local notation "J₂" => ModelWithCorners.prod K₂ 𝓘(ℝ, ℝ)

private local instance (Γ : Subgroup (PO 3 1)) : MulAction Γ H₃ :=
  EquivariantMap.subAction (Nat.le_add_left 1 2) Γ

private local instance (Γ : Subgroup (PO 3 1)) : ContinuousConstSMul Γ H₃ :=
  ⟨fun γ => (HyperbolicAction.contMDiff_po_smul 2 ∞ (γ : PO 3 1)).continuous⟩

private local instance (Γ : Subgroup (PO 3 1)) : ContMDiffConstSMul I₃ ∞ Γ H₃ :=
  ⟨fun γ => HyperbolicAction.contMDiff_po_smul 2 ∞ (γ : PO 3 1)⟩

private local instance (Γ : Subgroup (PO 3 1)) [DiscreteTopology Γ] :
    ProperlyDiscontinuousSMul Γ H₃ :=
  OrbifoldCompactness.properlyDiscontinuous_subAction (Nat.le_add_left 1 2) Γ
    (isDiscrete_iff_discreteTopology.mpr (inferInstance : DiscreteTopology Γ))

private theorem thin_pair_preserved (Γ : Subgroup (PO 3 1)) (ξ η : BoundaryH 3)
    (γ : CuspCrossSections.endStabilizer (Nat.le_add_left 1 2) Γ {ξ, η}) :
    (poBoundaryMulAction (Nat.le_add_left 1 2)).smul (γ : PO 3 1) ξ ∈ ({ξ, η} : Set (BoundaryH 3)) ∧
      (poBoundaryMulAction (Nat.le_add_left 1 2)).smul (γ : PO 3 1) η ∈ ({ξ, η} : Set (BoundaryH 3)) := by
  have he := (ElementaryEnds.mem_setStabilizer (Nat.le_add_left 1 2) {ξ, η} γ).mp γ.property.2
  exact ⟨he.subset ⟨ξ, by simp, rfl⟩, he.subset ⟨η, by simp, rfl⟩⟩

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E₃ H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
  (g : SmoothRiemannianMetric I M) (hg : RiemannianMetricComplete (I := I) g)
  (κ : ℝ) (hκ : κ < 0) (x₀ : M)
  (hsec : ∀ (x : M) (X Y : TangentSpace I x),
    Curvature.metricRm04StandardAt g x X Y Y X =
      κ * (g.inner x X X * g.inner x Y Y - g.inner x X Y * g.inner x X Y))


attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_normalizedUniversalCoverThinRegionCharts :
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
      let ρ := normalizedUniversalCoverDeckRepresentation g hg κ hκ x₀ hsec i
      let σ := (Hyperboloid.projectiveOrthogonalGroupEquiv 2 :
        (Hyperboloid E₃ ≃ᵢ Hyperboloid E₃) →* PO 3 1).comp ρ
      ∃ hΓ : IsDiscrete (SetLike.coe σ.range),
      letI : DiscreteTopology σ.range := isDiscrete_iff_discreteTopology.mp hΓ
      letI : IsCancelSMul σ.range H₃ :=
        isCancelSMul_projective_range_normalizedUniversalCoverDeckRepresentation g hg κ hκ x₀ hsec i
      let e := normalizedUniversalCoverProjectiveQuotientHomeomorph g hg κ hκ x₀ hsec i
      (∀ {r : ℝ} (D : CuspTruncation.FiniteCuspTruncation (Nat.le_add_left 1 2) σ.range r)
        (ξ : D.centers),
        let P := CuspCrossSections.endStabilizer (Nat.le_add_left 1 2) σ.range (Set.singleton ξ.val)
        letI : MulAction P H₃ := EquivariantMap.subAction (Nat.le_add_left 1 2) P
        letI : IsCancelSMul P H₃ := EquivariantMap.isCancelSMul_subAction
          (Nat.le_add_left 1 2) (show P ≤ σ.range from inf_le_left)
        let S := (Quotient.mk (MulAction.orbitRel P H₃)) '' Busemann.horosphere ξ.val (D.level ξ)
        letI : ChartedSpace (Fin 2 → ℝ) S := D.horosphereQuotientChartedSpace hΓ ξ
        ∃ Φ : PartialDiffeomorph J₂ I (S × ℝ) M ∞,
          Φ.toOpenPartialHomeomorph = (D.horosphereGraphChart hΓ ξ).transHomeomorph e) ∧
      (∀ (ξ η : BoundaryH 3) (hne : ξ ≠ η) (r : ℝ),
        let P := CuspCrossSections.endStabilizer (Nat.le_add_left 1 2) σ.range {ξ, η}
        letI : MulAction P H₃ := EquivariantMap.subAction (Nat.le_add_left 1 2) P
        letI : DiscreteTopology P := isDiscrete_iff_discreteTopology.mp
          (hΓ.mono (show P ≤ σ.range from inf_le_left))
        letI : IsCancelSMul P H₃ := EquivariantMap.isCancelSMul_subAction
          (Nat.le_add_left 1 2) (show P ≤ σ.range from inf_le_left)
        let hpair := thin_pair_preserved σ.range ξ η
        let S := {q : MulAction.orbitRel.Quotient P H₃ //
          AxisGeometry.quotientAxisDistance 2 P ξ η hne hpair q = Real.arsinh 1}
        letI : ChartedSpace (Fin 2 → ℝ) S := AxisGeometry.axisSectionChartedSpace 2 P ξ η hne hpair
        ∃ Φ : PartialDiffeomorph J₂ I (S × ℝ) M ∞,
          Φ.toOpenPartialHomeomorph =
            (OrbifoldThinRegions.axialGraphChart 2 σ.range ξ η hne (by decide) r).transHomeomorph e) := by
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
  let ρ := normalizedUniversalCoverDeckRepresentation g hg κ hκ x₀ hsec i
  let σ := (Hyperboloid.projectiveOrthogonalGroupEquiv 2 :
    (Hyperboloid E₃ ≃ᵢ Hyperboloid E₃) →* PO 3 1).comp ρ
  let : DiscreteTopology ρ.range :=
    discreteTopology_range_normalizedUniversalCoverDeckRepresentation g hg κ hκ x₀ hsec i
  have hΓ : IsDiscrete (SetLike.coe σ.range) := by
    change IsDiscrete (SetLike.coe
      ((Hyperboloid.projectiveOrthogonalGroupEquiv 2).toMulEquiv.toMonoidHom.comp ρ).range)
    rw [MonoidHom.range_comp]
    exact (SetLike.isDiscrete_iff_discreteTopology.mpr
      (inferInstance : DiscreteTopology ρ.range)).image
        (Hyperboloid.projectiveOrthogonalGroupEquiv 2).toHomeomorph.isInducing
  refine ⟨hΓ, ?_⟩
  let : DiscreteTopology σ.range := isDiscrete_iff_discreteTopology.mp hΓ
  let : IsCancelSMul σ.range H₃ :=
    isCancelSMul_projective_range_normalizedUniversalCoverDeckRepresentation g hg κ hκ x₀ hsec i
  let e := normalizedUniversalCoverProjectiveQuotientHomeomorph g hg κ hκ x₀ hsec i
  let : ChartedSpace E₃ (MulAction.orbitRel.Quotient σ.range H₃) :=
    MulAction.instChartedSpaceQuotient
  have hπ := MulAction.isLocalDiffeomorph_quotientMk_of_properlyDiscontinuousSMul
    (G := σ.range) (M := H₃) (n := ∞) I₃
  have hcomp : IsLocalDiffeomorph I₃ I ∞ (e ∘ Quotient.mk (MulAction.orbitRel σ.range H₃)) := by
    have heq : e ∘ Quotient.mk (MulAction.orbitRel σ.range H₃) =
        normalizedUniversalCoverProjection g hg κ hκ x₀ hsec i :=
      funext (normalizedUniversalCoverProjectiveQuotientHomeomorph_apply_mk g hg κ hκ x₀ hsec i)
    rw [heq]
    exact normalizedUniversalCoverProjection_isLocalDiffeomorph g hg κ hκ x₀ hsec i
  have he : IsLocalDiffeomorph I₃ I ∞ e := by
    intro q
    obtain ⟨p, rfl⟩ := Quotient.mk_surjective q
    exact DifferentialGeometry.isLocalDiffeomorphAt_of_comp (hcomp p) (hπ p)
  constructor
  · intro r D ξ
    let P := CuspCrossSections.endStabilizer (Nat.le_add_left 1 2) σ.range (Set.singleton ξ.val)
    let : MulAction P H₃ := EquivariantMap.subAction (Nat.le_add_left 1 2) P
    let : IsCancelSMul P H₃ := EquivariantMap.isCancelSMul_subAction
      (Nat.le_add_left 1 2) (show P ≤ σ.range from inf_le_left)
    let S := (Quotient.mk (MulAction.orbitRel P H₃)) '' Busemann.horosphere ξ.val (D.level ξ)
    let : ChartedSpace (Fin 2 → ℝ) S := D.horosphereQuotientChartedSpace hΓ ξ
    let A := (D.horosphereGraphChart hΓ ξ).transHomeomorph e
    have hA : IsLocalDiffeomorph J₂ I ∞ A := by
      have h := DifferentialGeometry.isLocalDiffeomorph_comp
        (f := D.horosphereGraphChart hΓ ξ) he (D.isLocalDiffeomorph_horosphereGraphChart ξ)
      exact h
    exact ⟨A.toPartialDiffeomorph (hA.isLocalDiffeomorphOn A.source), rfl⟩
  · intro ξ η hne r
    let P := CuspCrossSections.endStabilizer (Nat.le_add_left 1 2) σ.range {ξ, η}
    let : MulAction P H₃ := EquivariantMap.subAction (Nat.le_add_left 1 2) P
    let : DiscreteTopology P := isDiscrete_iff_discreteTopology.mp
      (hΓ.mono (show P ≤ σ.range from inf_le_left))
    let : IsCancelSMul P H₃ := EquivariantMap.isCancelSMul_subAction
      (Nat.le_add_left 1 2) (show P ≤ σ.range from inf_le_left)
    let hpair := thin_pair_preserved σ.range ξ η
    let S := {q : MulAction.orbitRel.Quotient P H₃ //
      AxisGeometry.quotientAxisDistance 2 P ξ η hne hpair q = Real.arsinh 1}
    let : ChartedSpace (Fin 2 → ℝ) S := AxisGeometry.axisSectionChartedSpace 2 P ξ η hne hpair
    let A := (OrbifoldThinRegions.axialGraphChart 2 σ.range ξ η hne (by decide) r).transHomeomorph e
    have hA : IsLocalDiffeomorph J₂ I ∞ A := by
      have h := DifferentialGeometry.isLocalDiffeomorph_comp
        (f := OrbifoldThinRegions.axialGraphChart 2 σ.range ξ η hne (by decide) r) he
        (OrbifoldThinRegions.isLocalDiffeomorph_axialGraphAmbientPoint 2 σ.range ξ η hne)
      exact h
    exact ⟨A.toPartialDiffeomorph (hA.isLocalDiffeomorphOn A.source), rfl⟩

end DifferentialGeometry.Geometry.Hyperbolic
