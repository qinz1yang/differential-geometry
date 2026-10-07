import DifferentialGeometry.Geometry.Hyperbolic.ProjectionMetric
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Horosphere.Distance
import DifferentialGeometry.Geometry.Metric.Distance.Topology

noncomputable section

open scoped Manifold ContDiff Bundle ENNReal NNReal Topology

namespace DifferentialGeometry.Geometry.Hyperbolic

open Riemannian.Topology (UniversalCover SemilocallySimplyConnectedSpace
  manifold_semilocallySimplyConnectedSpace)

local notation "E₃" => EuclideanSpace ℝ (Fin 3)
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
theorem lipschitzWith_normalizedUniversalCoverProjection_original_metric :
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
      letI : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
      letI : T3Space M := inferInstance
      letI : PseudoMetricSpace M := g.toPseudoMetricSpace
      LipschitzWith ⟨(Real.sqrt (-κ))⁻¹, inv_nonneg.mpr (Real.sqrt_nonneg _)⟩
        (normalizedUniversalCoverProjection g hg κ hκ x₀ hsec i) := by
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
  let _ : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let _ : T3Space M := inferInstance
  let _ : PseudoMetricSpace M := g.toPseudoMetricSpace
  apply LipschitzWith.of_dist_le_mul
  intro x y
  apply le_of_forall_gt_imp_ge_of_dense
  intro r hr
  change (Real.sqrt (-κ))⁻¹ * dist x y < r at hr
  have hs : 0 < Real.sqrt (-κ) := Real.sqrt_pos.mpr (neg_pos.mpr hκ)
  have hym : y ∈ Metric.ball x (Real.sqrt (-κ) * r) := by
    rw [Metric.mem_ball, dist_comm]
    calc
      dist x y = Real.sqrt (-κ) * ((Real.sqrt (-κ))⁻¹ * dist x y) := by
        rw [← mul_assoc, mul_inv_cancel₀ hs.ne', one_mul]
      _ < Real.sqrt (-κ) * r := mul_lt_mul_of_pos_left hr hs
  have hmem : normalizedUniversalCoverProjection g hg κ hκ x₀ hsec i y ∈
      riemannianBallOf g (normalizedUniversalCoverProjection g hg κ hκ x₀ hsec i x) r := by
    rw [← image_ball_normalizedUniversalCoverProjection_original_metric g hg κ hκ x₀ hsec i]
    exact ⟨y, hym, rfl⟩
  have he : edist (normalizedUniversalCoverProjection g hg κ hκ x₀ hsec i x)
      (normalizedUniversalCoverProjection g hg κ hκ x₀ hsec i y) < ENNReal.ofReal r := hmem
  exact (edist_lt_ofReal.mp he).le

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem edist_normalizedUniversalCoverProjection_le_ediam_horosphere_add_height :
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
      letI : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
      letI : T3Space M := inferInstance
      letI : PseudoMetricSpace M := g.toPseudoMetricSpace
      let pH := normalizedUniversalCoverProjection g hg κ hκ x₀ hsec i
      ∀ (ξ : HyperbolicBoundary.BoundaryH 3) (x y : H₃),
        edist (pH x) (pH y) ≤ Metric.ediam (pH '' Busemann.horosphere ξ (Busemann.busemann ξ x)) +
          ENNReal.ofReal ((Real.sqrt (-κ))⁻¹ * |Busemann.busemann ξ y - Busemann.busemann ξ x|) := by
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
  let _ : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let _ : T3Space M := inferInstance
  let _ : PseudoMetricSpace M := g.toPseudoMetricSpace
  intro ξ x y
  have h := HorosphereProjection.edist_le_ediam_horosphere_add_busemann_sub ξ
    (normalizedUniversalCoverProjection g hg κ hκ x₀ hsec i)
    (lipschitzWith_normalizedUniversalCoverProjection_original_metric g hg κ hκ x₀ hsec i) x y
  rw [ENNReal.ofReal_mul (inv_nonneg.mpr (Real.sqrt_nonneg _)),
    ENNReal.ofReal_eq_coe_nnreal (inv_nonneg.mpr (Real.sqrt_nonneg _))]
  exact h

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem edist_normalizedUniversalCoverProjection_le_of_ediam_horosphere_le :
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
      letI : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
      letI : T3Space M := inferInstance
      letI : PseudoMetricSpace M := g.toPseudoMetricSpace
      let pH := normalizedUniversalCoverProjection g hg κ hκ x₀ hsec i
      ∀ (ξ : HyperbolicBoundary.BoundaryH 3) (x y : H₃) {D A : ℝ}, 0 ≤ D →
        Metric.ediam (pH '' Busemann.horosphere ξ (Busemann.busemann ξ x)) ≤ ENNReal.ofReal D →
        (Real.sqrt (-κ))⁻¹ * |Busemann.busemann ξ y - Busemann.busemann ξ x| ≤ A →
        edist (pH x) (pH y) ≤ ENNReal.ofReal (D + A) := by
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
  let _ : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let _ : T3Space M := inferInstance
  let _ : PseudoMetricSpace M := g.toPseudoMetricSpace
  intro ξ x y D A hD hdiam hheight
  have hA : 0 ≤ A := (mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) (abs_nonneg _)).trans hheight
  rw [ENNReal.ofReal_add hD hA]
  exact (edist_normalizedUniversalCoverProjection_le_ediam_horosphere_add_height
    g hg κ hκ x₀ hsec i ξ x y).trans (add_le_add hdiam (ENNReal.ofReal_le_ofReal hheight))

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem eventually_edist_normalizedUniversalCoverProjection_le_of_busemann_eq :
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
      letI : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
      letI : T3Space M := inferInstance
      letI : PseudoMetricSpace M := g.toPseudoMetricSpace
      let pH := normalizedUniversalCoverProjection g hg κ hκ x₀ hsec i
      let ρ := normalizedUniversalCoverDeckRepresentation g hg κ hκ x₀ hsec i
      let σ := (Hyperboloid.projectiveOrthogonalGroupEquiv 2 :
        (Hyperboloid E₃ ≃ᵢ Hyperboloid E₃) →* ProjectiveOrthogonalGroup.PO 3 1).comp ρ
      ∀ (P : Subgroup (ProjectiveOrthogonalGroup.PO 3 1)) (_ : P ≤ σ.range)
        (ξ : HyperbolicBoundary.BoundaryH 3) (c : ℝ)
        (_ : ∀ γ : P,
          (HyperbolicBoundary.poBoundaryMulAction (by decide : 1 ≤ 3)).smul
            (γ : ProjectiveOrthogonalGroup.PO 3 1) ξ = ξ ∧
          BusemannCocycle.poConfFactor (by decide : 1 ≤ 3)
            (γ : ProjectiveOrthogonalGroup.PO 3 1) ξ = 1)
        (_ : IsCompact ((Quotient.mk (@MulAction.orbitRel P H₃ _
          (EquivariantMap.subAction (by decide : 1 ≤ 3) P))) '' Busemann.horosphere ξ c))
        {D : ℝ≥0∞}, 0 < D →
        ∀ᶠ t : ℝ in Filter.atTop, ∀ x y : H₃, Busemann.busemann ξ x = c - t →
          edist (pH x) (pH y) ≤ D + ENNReal.ofReal
            ((Real.sqrt (-κ))⁻¹ * |Busemann.busemann ξ y - Busemann.busemann ξ x|) := by
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
  let _ : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let _ : T3Space M := inferInstance
  let _ : PseudoMetricSpace M := g.toPseudoMetricSpace
  let pH := normalizedUniversalCoverProjection g hg κ hκ x₀ hsec i
  let ρ := normalizedUniversalCoverDeckRepresentation g hg κ hκ x₀ hsec i
  let σ := (Hyperboloid.projectiveOrthogonalGroupEquiv 2 :
    (Hyperboloid E₃ ≃ᵢ Hyperboloid E₃) →* ProjectiveOrthogonalGroup.PO 3 1).comp ρ
  intro P hP ξ c hhor hcompact D hD
  have hinv (γ : P) (x : H₃) :
      pH ((HyperbolicAction.poMulAction (by decide : 1 ≤ 3)).smul
        (γ : ProjectiveOrthogonalGroup.PO 3 1) x) = pH x := by
    let _ := EquivariantMap.subAction (by decide : 1 ≤ 3) σ.range
    let e := normalizedUniversalCoverProjectiveQuotientHomeomorph g hg κ hκ x₀ hsec i
    have he (y : H₃) : e (Quotient.mk (MulAction.orbitRel σ.range H₃) y) = pH y :=
      normalizedUniversalCoverProjectiveQuotientHomeomorph_apply_mk g hg κ hκ x₀ hsec i y
    rw [← he, ← he]
    apply congrArg e
    apply Quotient.sound
    exact ⟨⟨γ, hP γ.property⟩, rfl⟩
  have ht := HorosphereProjection.eventually_edist_le_of_busemann_eq (by decide) P ξ c hhor
    hcompact pH (lipschitzWith_normalizedUniversalCoverProjection_original_metric g hg κ hκ x₀ hsec i)
    hinv hD
  filter_upwards [ht] with t ht
  intro x y hx
  rw [ENNReal.ofReal_mul (inv_nonneg.mpr (Real.sqrt_nonneg _)),
    ENNReal.ofReal_eq_coe_nnreal (inv_nonneg.mpr (Real.sqrt_nonneg _))]
  exact ht x y hx

end DifferentialGeometry.Geometry.Hyperbolic
