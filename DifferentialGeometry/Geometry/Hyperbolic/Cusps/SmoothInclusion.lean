import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Cusps.SmoothInclusion
import DifferentialGeometry.Geometry.Hyperbolic.Cusps.Inclusion
import DifferentialGeometry.Geometry.Hyperbolic.ProjectiveDeckGroup
import DifferentialGeometry.Geometry.Hyperbolic.DeckGroup

noncomputable section

open scoped Manifold ContDiff Bundle ENNReal

namespace DifferentialGeometry.Geometry.Hyperbolic

open Riemannian.Topology (UniversalCover SemilocallySimplyConnectedSpace
  manifold_semilocallySimplyConnectedSpace)
open ProjectiveOrthogonalGroup (PO)

local notation "E₃" => EuclideanSpace ℝ (Fin 3)
local notation "I₃" => 𝓘(ℝ, E₃)
local notation "H₃" => DifferentialGeometry.Hyperbolic.HUpper 3

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
theorem exists_normalizedUniversalCoverCuspPartialDiffeomorph :
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
      ∀ {r : ℝ} (D : CuspTruncation.FiniteCuspTruncation (Nat.le_add_left 1 2) σ.range r)
        (ξ : D.centers),
      let P := CuspCrossSections.endStabilizer (Nat.le_add_left 1 2) σ.range (Set.singleton ξ.val)
      letI := EquivariantMap.subAction (Nat.le_add_left 1 2) σ.range
      letI := EquivariantMap.subAction (Nat.le_add_left 1 2) P
      letI : IsCancelSMul σ.range H₃ :=
        isCancelSMul_projective_range_normalizedUniversalCoverDeckRepresentation g hg κ hκ x₀ hsec i
      letI : IsCancelSMul P H₃ := EquivariantMap.isCancelSMul_subAction
        (Nat.le_add_left 1 2) (show P ≤ σ.range from inf_le_left)
      letI : ContinuousConstSMul P H₃ :=
        ⟨fun γ => (HyperbolicAction.contMDiff_po_smul 2 ∞ (γ : PO 3 1)).continuous⟩
      ∃ hΓ : IsDiscrete (SetLike.coe σ.range),
      letI := OrbifoldCompactness.properlyDiscontinuous_subAction
        (Nat.le_add_left 1 2) P (hΓ.mono inf_le_left)
      let QP := MulAction.orbitRel.Quotient P H₃
      let πP := Quotient.mk (MulAction.orbitRel P H₃)
      let F := (normalizedUniversalCoverProjectiveQuotientHomeomorph g hg κ hκ x₀ hsec i :
        MulAction.orbitRel.Quotient σ.range H₃ → M) ∘
        EquivariantMap.quotientInclusion (Nat.le_add_left 1 2) (show P ≤ σ.range from inf_le_left)
      ∃ Φ : PartialDiffeomorph I₃ I QP M ∞,
        Φ.source = D.openHoroballQuotient hΓ ξ ∧
        Φ.target = (normalizedUniversalCoverProjection g hg κ hκ x₀ hsec i) ''
          {p : H₃ | Busemann.busemann ξ.val p < D.level ξ} ∧
        Φ.toFun = F ∧
        (∀ p : H₃, Φ (πP p) = normalizedUniversalCoverProjection g hg κ hκ x₀ hsec i p) ∧
        (∀ p : H₃, Busemann.busemann ξ.val p < D.level ξ →
          Φ.symm (normalizedUniversalCoverProjection g hg κ hκ x₀ hsec i p) = πP p) ∧
        (∀ z : (πP '' Busemann.horosphere ξ.val (D.level ξ)) × Set.Ici (0 : ℝ),
          Φ (((D.horoballQuotientHomeomorph hΓ ξ).symm z).val) =
            normalizedUniversalCoverCuspCylinderMap g hg κ hκ x₀ hsec i D ξ z) := by
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
  intro i r D ξ
  let ρ := normalizedUniversalCoverDeckRepresentation g hg κ hκ x₀ hsec i
  let σ := (Hyperboloid.projectiveOrthogonalGroupEquiv 2 :
    (Hyperboloid E₃ ≃ᵢ Hyperboloid E₃) →* PO 3 1).comp ρ
  let P := CuspCrossSections.endStabilizer (Nat.le_add_left 1 2) σ.range (Set.singleton ξ.val)
  let := EquivariantMap.subAction (Nat.le_add_left 1 2) σ.range
  let := EquivariantMap.subAction (Nat.le_add_left 1 2) P
  let : IsCancelSMul σ.range H₃ :=
    isCancelSMul_projective_range_normalizedUniversalCoverDeckRepresentation g hg κ hκ x₀ hsec i
  let : IsCancelSMul P H₃ := EquivariantMap.isCancelSMul_subAction
    (Nat.le_add_left 1 2) (show P ≤ σ.range from inf_le_left)
  let : ContinuousConstSMul P H₃ :=
    ⟨fun γ => (HyperbolicAction.contMDiff_po_smul 2 ∞ (γ : PO 3 1)).continuous⟩
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
  let := OrbifoldCompactness.properlyDiscontinuous_subAction
    (Nat.le_add_left 1 2) P (hΓ.mono inf_le_left)
  let QP := MulAction.orbitRel.Quotient P H₃
  let πP := Quotient.mk (MulAction.orbitRel P H₃)
  let e := normalizedUniversalCoverProjectiveQuotientHomeomorph g hg κ hκ x₀ hsec i
  let j := EquivariantMap.quotientInclusion (Nat.le_add_left 1 2) (show P ≤ σ.range from inf_le_left)
  let F : QP → M := e ∘ j
  let pH := normalizedUniversalCoverProjection g hg κ hκ x₀ hsec i
  have hrep (p : H₃) : F (πP p) = pH p :=
    normalizedUniversalCoverProjectiveQuotientHomeomorph_apply_mk g hg κ hκ x₀ hsec i p
  have hprojection : IsLocalDiffeomorph I₃ I ∞
      (e ∘ Quotient.mk (MulAction.orbitRel σ.range H₃)) := by
    have heq : e ∘ Quotient.mk (MulAction.orbitRel σ.range H₃) = pH :=
      funext (normalizedUniversalCoverProjectiveQuotientHomeomorph_apply_mk g hg κ hκ x₀ hsec i)
    rw [heq]
    exact normalizedUniversalCoverProjection_isLocalDiffeomorph g hg κ hκ x₀ hsec i
  have hex := @CuspTruncation.FiniteCuspTruncation.exists_openHoroballQuotientPartialDiffeomorph_of_projection
    2 σ.range r D hΓ ξ (inferInstance : IsCancelSMul σ.range H₃)
    E₃ inferInstance inferInstance H inferInstance I M inferInstance inferInstance e hprojection
  obtain ⟨Φ, hsource, htarget, hmap⟩ := hex
  have htarget' : Φ.target = pH '' {p : H₃ | Busemann.busemann ξ.val p < D.level ξ} := by
    rw [htarget]
    apply Set.image_congr
    intro p hp
    exact normalizedUniversalCoverProjectiveQuotientHomeomorph_apply_mk g hg κ hκ x₀ hsec i p
  refine ⟨Φ, hsource, htarget', hmap, ?_, ?_, ?_⟩
  · intro p
    exact congrFun hmap (πP p) |>.trans (hrep p)
  · intro p hp
    have hs : πP p ∈ Φ.source := by rw [hsource]; exact ⟨p, hp, rfl⟩
    have hv : Φ (πP p) = pH p := (congrFun hmap (πP p)).trans (hrep p)
    rw [← hv]
    exact Φ.left_inv hs
  · rintro ⟨⟨q, p, hp, rfl⟩, t⟩
    change Φ (πP (AsymptoticRays.rayTo p ξ.val t.val)) = _
    exact ((congrFun hmap (πP (AsymptoticRays.rayTo p ξ.val t.val))).trans
      (hrep (AsymptoticRays.rayTo p ξ.val t.val))).trans
        (normalizedUniversalCoverCuspCylinderMap_apply_mk g hg κ hκ x₀ hsec i D ξ p hp t).symm

end DifferentialGeometry.Geometry.Hyperbolic
