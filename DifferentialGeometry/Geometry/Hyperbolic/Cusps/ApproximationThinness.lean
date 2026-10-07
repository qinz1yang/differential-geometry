import DifferentialGeometry.Geometry.Hyperbolic.Cusps.Inclusion
import DifferentialGeometry.Geometry.Hyperbolic.ProjectionMetric
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Cusps.MeasureDecay
import DifferentialGeometry.Geometry.Hyperbolic.ApproximationThinness
import DifferentialGeometry.Geometry.Comparison.HopfRinow.Proper
import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.Volume

noncomputable section

open scoped Manifold ContDiff Bundle ENNReal Topology
open DifferentialGeometry.Integral.Measure (riemannianVolumeMeasure)

namespace DifferentialGeometry.Geometry.Hyperbolic

open Riemannian.Topology (UniversalCover SemilocallySimplyConnectedSpace
  manifold_semilocallySimplyConnectedSpace)

local notation "E₃" => EuclideanSpace ℝ (Fin 3)
local notation "H₃" => DifferentialGeometry.Hyperbolic.HUpper 3

private instance : NeZero (Module.finrank ℝ E₃) := ⟨by simp⟩

private theorem exists_uniform_tail_measure_lt
    {ι X : Type*} [Finite ι] {A : ι → Type*} [∀ i, TopologicalSpace (A i)]
    [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (μ : MeasureTheory.Measure X) (e : ∀ i, A i × Set.Ici (0 : ℝ) → X)
    (he : ∀ i, _root_.Topology.IsClosedEmbedding (e i))
    (hfinite : ∀ i, μ (Set.range (e i)) ≠ ⊤) {η : ℝ≥0∞} (hη : 0 < η) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ i, μ ((e i) '' {z | R ≤ z.2.val}) < η := by
  have hev (i : ι) : ∀ᶠ R : ℝ in Filter.atTop, μ ((e i) '' {z | R ≤ z.2.val}) < η :=
    ((he i).tendsto_measure_image_cylinder_tail μ (hfinite i)).eventually (Iio_mem_nhds hη)
  have hall : ∀ᶠ R : ℝ in Filter.atTop, (0 : ℝ) ≤ R ∧
      ∀ i, μ ((e i) '' {z | R ≤ z.2.val}) < η :=
    (Filter.eventually_ge_atTop 0).and (Filter.eventually_all.mpr hev)
  exact hall.exists

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E₃ H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
  (g : SmoothRiemannianMetric I M) (hg : RiemannianMetricComplete (I := I) g)
  (κ : ℝ) (hκ : κ < 0) (x₀ : M)
  (hsec : ∀ (x : M) (X Y : TangentSpace I x),
    Curvature.metricRm04StandardAt g x X Y Y X =
      κ * (g.inner x X X * g.inner x Y Y - g.inner x X Y * g.inner x X Y))

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem normalizedUniversalCoverCuspCylinderMap_image_tail :
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
        (Hyperboloid E₃ ≃ᵢ Hyperboloid E₃) →* ProjectiveOrthogonalGroup.PO 3 1).comp ρ
      ∀ {r : ℝ} (D : CuspTruncation.FiniteCuspTruncation (by decide : 1 ≤ 3) σ.range r)
        (ξ : D.centers) (R : ℝ), 0 ≤ R →
        (normalizedUniversalCoverCuspCylinderMap g hg κ hκ x₀ hsec i D ξ) '' {z | R ≤ z.2.val} =
          (normalizedUniversalCoverProjection g hg κ hκ x₀ hsec i) '' Busemann.horoball ξ.val (D.level ξ - R) := by
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
  intro i r D ξ R hR
  let ρ := normalizedUniversalCoverDeckRepresentation g hg κ hκ x₀ hsec i
  let _ : DiscreteTopology ρ.range :=
    discreteTopology_range_normalizedUniversalCoverDeckRepresentation g hg κ hκ x₀ hsec i
  have hΓ : IsDiscrete (SetLike.coe ((Hyperboloid.projectiveOrthogonalGroupEquiv 2 :
      (Hyperboloid E₃ ≃ᵢ Hyperboloid E₃) →* ProjectiveOrthogonalGroup.PO 3 1).comp ρ).range) := by
    have hd : IsDiscrete (SetLike.coe ρ.range) := SetLike.isDiscrete_iff_discreteTopology.mpr inferInstance
    rw [MonoidHom.range_comp]
    exact hd.image (Hyperboloid.projectiveOrthogonalGroupEquiv 2).toHomeomorph.isInducing
  let F := normalizedUniversalCoverProjectiveQuotientHomeomorph g hg κ hκ x₀ hsec i
  calc
    (normalizedUniversalCoverCuspCylinderMap g hg κ hκ x₀ hsec i D ξ) '' {z | R ≤ z.2.val} =
        F '' ((D.horoballCylinderMap hΓ ξ) '' {z | R ≤ z.2.val}) :=
      (Set.image_image F (D.horoballCylinderMap hΓ ξ) _).symm
    _ = F '' ((Quotient.mk _) '' Busemann.horoball ξ.val (D.level ξ - R)) := by
      rw [D.horoballCylinderMap_image_tail hΓ ξ hR]
    _ = _ := by
      rw [Set.image_image]
      apply Set.image_congr
      intro p hp
      exact normalizedUniversalCoverProjectiveQuotientHomeomorph_apply_mk g hg κ hκ x₀ hsec i p

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem riemannianClosedBallOf_normalizedUniversalCoverCuspCylinderMap_subset_tail :
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
        (Hyperboloid E₃ ≃ᵢ Hyperboloid E₃) →* ProjectiveOrthogonalGroup.PO 3 1).comp ρ
      ∀ {r : ℝ} (D : CuspTruncation.FiniteCuspTruncation (by decide : 1 ≤ 3) σ.range r)
        (ξ : D.centers),
        let P := CuspCrossSections.endStabilizer (by decide : 1 ≤ 3) σ.range {ξ.val}
        letI := EquivariantMap.subAction (by decide : 1 ≤ 3) P
        let C := (Quotient.mk (MulAction.orbitRel P H₃)) '' Busemann.horosphere ξ.val (D.level ξ)
        ∀ (c : C) (t : Set.Ici (0 : ℝ)) (R δ : ℝ), 0 ≤ R → 0 < δ →
          R + Real.sqrt (-κ) * (5 * δ) ≤ t.val →
          riemannianClosedBallOf g
            (normalizedUniversalCoverCuspCylinderMap g hg κ hκ x₀ hsec i D ξ (c, t)) (4 * δ) ⊆
            (normalizedUniversalCoverCuspCylinderMap g hg κ hκ x₀ hsec i D ξ) '' {z | R ≤ z.2.val} := by
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
  intro i r D ξ c t R δ hR hδ ht
  obtain ⟨q, u, hu, rfl⟩ := c
  have hp := normalizedUniversalCoverCuspCylinderMap_apply_mk g hg κ hκ x₀ hsec i D ξ u hu t
  have htimage := normalizedUniversalCoverCuspCylinderMap_image_tail g hg κ hκ x₀ hsec i D ξ R hR
  intro y hy
  have hcenter := congrArg (fun a : M => y ∈ riemannianClosedBallOf g a (4 * δ)) hp
  have hyP := hcenter.mp hy
  apply (congrArg (fun A : Set M => y ∈ A) htimage).mpr
  have hyopen : y ∈ riemannianBallOf g
      (normalizedUniversalCoverProjection g hg κ hκ x₀ hsec i (AsymptoticRays.rayTo u ξ.val t.val)) (5 * δ) :=
    hyP.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by positivity : 0 < 5 * δ)).mpr (by linarith))
  rw [← image_ball_normalizedUniversalCoverProjection_original_metric
    g hg κ hκ x₀ hsec i] at hyopen
  obtain ⟨z, hz, hzy⟩ := hyopen
  refine ⟨z, ?_, hzy⟩
  have hb := (abs_le.mp (Busemann.busemann_lipschitz ξ.val z (AsymptoticRays.rayTo u ξ.val t.val))).2
  have hdepth : Busemann.busemann ξ.val (AsymptoticRays.rayTo u ξ.val t.val) = D.level ξ - t.val := by
    rw [HorosphereProjection.busemann_rayTo, show Busemann.busemann ξ.val u = D.level ξ from hu]
  rw [hdepth] at hb
  change Busemann.busemann ξ.val z ≤ D.level ξ - R
  have hdist : dist z (AsymptoticRays.rayTo u ξ.val t.val) < Real.sqrt (-κ) * (5 * δ) := hz
  linarith

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem exists_depth_volume_closedBall_lt :
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
        (Hyperboloid E₃ ≃ᵢ Hyperboloid E₃) →* ProjectiveOrthogonalGroup.PO 3 1).comp ρ
      ∀ {r : ℝ} (D : CuspTruncation.FiniteCuspTruncation (by decide : 1 ≤ 3) σ.range r),
        let e (ξ : D.centers) := normalizedUniversalCoverCuspCylinderMap g hg κ hκ x₀ hsec i D ξ
        (∀ ξ : D.centers, riemannianVolumeMeasure I M g (Set.range (e ξ)) ≠ ⊤) →
        ∀ (δ : ℝ), 0 < δ → ∀ (η : ℝ≥0∞), 0 < η →
        ∃ T : ℝ, 0 ≤ T ∧ ∀ ξ : D.centers,
        let P := CuspCrossSections.endStabilizer (by decide : 1 ≤ 3) σ.range {ξ.val}
        letI := EquivariantMap.subAction (by decide : 1 ≤ 3) P
        let C := (Quotient.mk (MulAction.orbitRel P H₃)) '' Busemann.horosphere ξ.val (D.level ξ)
        ∀ (c : C) (t : Set.Ici (0 : ℝ)), T ≤ t.val →
          riemannianVolumeMeasure I M g (riemannianClosedBallOf g (e ξ (c, t)) (4 * δ)) < η := by
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
  intro i r D hfinite δ hδ η hη
  let ρ := normalizedUniversalCoverDeckRepresentation g hg κ hκ x₀ hsec i
  let σ := (Hyperboloid.projectiveOrthogonalGroupEquiv 2 :
    (Hyperboloid E₃ ≃ᵢ Hyperboloid E₃) →* ProjectiveOrthogonalGroup.PO 3 1).comp ρ
  let A (ξ : D.centers) : Type _ :=
    let P := CuspCrossSections.endStabilizer (by decide : 1 ≤ 3) σ.range {ξ.val}
    letI := EquivariantMap.subAction (by decide : 1 ≤ 3) P
    (Quotient.mk (MulAction.orbitRel P H₃)) '' Busemann.horosphere ξ.val (D.level ξ)
  let e (ξ : D.centers) : A ξ × Set.Ici (0 : ℝ) → M :=
    normalizedUniversalCoverCuspCylinderMap g hg κ hκ x₀ hsec i D ξ
  let _ : Finite D.centers := D.finite_centers
  have he (ξ : D.centers) : _root_.Topology.IsClosedEmbedding (e ξ) :=
    normalizedUniversalCoverCuspCylinderMap_isClosedEmbedding g hg κ hκ x₀ hsec i D ξ
  have hfin (ξ : D.centers) : riemannianVolumeMeasure I M g (Set.range (e ξ)) ≠ ⊤ := hfinite ξ
  have hall := exists_uniform_tail_measure_lt (A := A) (riemannianVolumeMeasure I M g) e he hfin hη
  obtain ⟨R, hR, hmass⟩ := hall
  refine ⟨R + Real.sqrt (-κ) * (5 * δ),
    add_nonneg hR (mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg (by norm_num) hδ.le)), ?_⟩
  intro ξ c t ht
  exact (MeasureTheory.measure_mono
    (riemannianClosedBallOf_normalizedUniversalCoverCuspCylinderMap_subset_tail g hg κ hκ x₀ hsec i D ξ c t R δ hR hδ ht)).trans_lt
      (hmass ξ)

universe v

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_depth_deck_displacement_lt_of_metric_approximation :
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
        (Hyperboloid E₃ ≃ᵢ Hyperboloid E₃) →* ProjectiveOrthogonalGroup.PO 3 1).comp ρ
      ∀ {r : ℝ} (D : CuspTruncation.FiniteCuspTruncation (by decide : 1 ≤ 3) σ.range r),
        let e (ξ : D.centers) := normalizedUniversalCoverCuspCylinderMap g hg κ hκ x₀ hsec i D ξ
        (∀ ξ : D.centers, riemannianVolumeMeasure I M g (Set.range (e ξ)) ≠ ⊤) →
        ∀ (δ : ℝ), 0 < δ → ∃ T : ℝ, 0 ≤ T ∧
        ∀ (N : Type v) [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
          [T2Space N] [SigmaCompactSpace N] [ConnectedSpace N]
          (h : SmoothRiemannianMetric I N) (_ : RiemannianMetricComplete h) (y₀ : N),
          (∀ (q : N) (v w : TangentSpace I q),
            Curvature.metricRm04StandardAt h q v w w v =
              (-1 / 4 : ℝ) * (h.inner q v v * h.inner q w w - h.inner q v w * h.inner q v w)) →
          ∀ (Φ : PartialDiffeomorph I I M N ∞) (k : ℕ) (ε : ℝ), ε ≤ 1 / 2 →
          ∀ ξ : D.centers,
        let P := CuspCrossSections.endStabilizer (by decide : 1 ≤ 3) σ.range {ξ.val}
        letI := EquivariantMap.subAction (by decide : 1 ≤ 3) P
        let C := (Quotient.mk (MulAction.orbitRel P H₃)) '' Busemann.horosphere ξ.val (D.level ξ)
        ∀ (c : C) (t : Set.Ici (0 : ℝ)), T ≤ t.val →
          DifferentialGeometry.PartialDiffeomorph.isMetricApproximationOn Φ
            (riemannianClosedBallOf g (e ξ (c, t)) (4 * δ)) k ε g h →
          letI : Inhabited N := ⟨y₀⟩
          letI : LocallyPathConnectedSpace H := I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
          letI : LocallyPathConnectedSpace N := ChartedSpace.locallyPathConnectedSpace H N
          letI : SemilocallySimplyConnectedSpace N := manifold_semilocallySimplyConnectedSpace (I := I)
          ∀ x : UniversalCover N, UniversalCover.proj x = Φ (e ξ (c, t)) →
            ∃ γ : FundamentalGroup N (default : N), γ ≠ 1 ∧
              riemannianEDistOf (UniversalCover.liftedMetric (I := I)
                (scaleMetric (1 / 4) (by norm_num) h)) x (γ • x) < ENNReal.ofReal δ := by
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
  intro i r D hfinite δ hδ
  let V := riemannianVolumeMeasure 𝓘(ℝ, E₃) (Hyperboloid E₃) Hyperboloid.riemannianMetric
    (Metric.ball Hyperboloid.origin (δ / 2))
  have hV : 0 < V := Hyperboloid.riemannianVolumeMeasure_ball_pos Hyperboloid.origin (by positivity)
  have hdepth := exists_depth_volume_closedBall_lt g hg κ hκ x₀ hsec i D hfinite δ hδ V hV
  obtain ⟨T, hT, hsmall⟩ := hdepth
  refine ⟨T, hT, ?_⟩
  intro N topN chartN smoothN t2N sigmaN connN h hh y₀ hcurv Φ k ε hε ξ c t ht happrox
  let p := normalizedUniversalCoverCuspCylinderMap g hg κ hκ x₀ hsec i D ξ (c, t)
  exact exists_deck_displacement_lt_of_small_volume_metric_approximation
    g h hh y₀ hcurv p hδ Φ (hg.closedEBall_isCompact p (4 * δ)) k hε happrox
      (hsmall ξ c t ht)

end DifferentialGeometry.Geometry.Hyperbolic
