import DifferentialGeometry.Geometry.Hyperbolic.AxialClosedGeodesic
import DifferentialGeometry.Geometry.Hyperbolic.Cusps.PeriodicGeodesic

noncomputable section
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace DifferentialGeometry.Geometry.Hyperbolic

open Riemannian.Topology
  (UniversalCover SemilocallySimplyConnectedSpace manifold_semilocallySimplyConnectedSpace)

local notation "E₃" => EuclideanSpace ℝ (Fin 3)
local notation "H₃" => DifferentialGeometry.Hyperbolic.HUpper 3
local notation "B₃" => HyperbolicBoundary.BoundaryH 3
private theorem quarter_negative : (-1 / 4 : ℝ) < 0 := by norm_num

universe u v
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E₃ H} [I.Boundaryless]
  {M : Type u} {N : Type v} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  [T2Space N] [SigmaCompactSpace N] [ConnectedSpace N]
  (g : SmoothRiemannianMetric I M) (hg : RiemannianMetricComplete (I := I) g) (x₀ : M)
  (hsec : ∀ (x : M) (X Y : TangentSpace I x),
    Curvature.metricRm04StandardAt g x X Y Y X =
      (-1 / 4 : ℝ) * (g.inner x X X * g.inner x Y Y - g.inner x X Y * g.inner x X Y))
  (gTarget : SmoothRiemannianMetric I N) (hgTarget : RiemannianMetricComplete (I := I) gTarget)
  (xTarget : N)
  (hsecTarget : ∀ (x : N) (X Y : TangentSpace I x),
    Curvature.metricRm04StandardAt gTarget x X Y Y X =
      (-1 / 4 : ℝ) * (gTarget.inner x X X * gTarget.inner x Y Y - gTarget.inner x X Y * gTarget.inner x X Y))

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem not_mem_axial_core_of_metric_approximation_in_cusp
    (Φ : PartialDiffeomorph I I M N ∞) (o : M) {R ε : ℝ} {p : ℕ}
    (hp : 1 ≤ p) (hε : ε ≤ 1 / 100)
    (hΦ : PartialDiffeomorph.isMetricApproximationOn Φ (riemannianClosedBallOf g o R) p ε g gTarget) :
    letI : Inhabited M := ⟨x₀⟩
    letI : LocallyPathConnectedSpace H := I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
    letI : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace H M
    letI : SemilocallySimplyConnectedSpace M := manifold_semilocallySimplyConnectedSpace (I := I)
    letI : SecondCountableTopology H := ModelWithCorners.secondCountableTopology I
    letI : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
    let gN := scaleMetric (-(-1 / 4 : ℝ)) (neg_pos.mpr quarter_negative) g
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
    letI : Inhabited N := ⟨xTarget⟩
    letI : LocallyPathConnectedSpace H := I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
    letI : LocallyPathConnectedSpace N := ChartedSpace.locallyPathConnectedSpace H N
    letI : SemilocallySimplyConnectedSpace N := manifold_semilocallySimplyConnectedSpace (I := I)
    letI : SecondCountableTopology H := ModelWithCorners.secondCountableTopology I
    letI : SecondCountableTopology N := ChartedSpace.secondCountable_of_sigmaCompact H N
    let gTargetN := scaleMetric (-(-1 / 4 : ℝ)) (neg_pos.mpr quarter_negative) gTarget
    let ĝTarget := UniversalCover.liftedMetric (I := I) gTargetN
    let hĝTarget : RiemannianMetricComplete ĝTarget := UniversalCover.liftedMetric_complete gTargetN (hgTarget.scaleMetric _ _)
    letI : IsManifold I 1 (UniversalCover N) :=
      IsManifold.of_le (I := I) (M := UniversalCover N) (n := ∞) (by decide)
    letI : TopologicalSpace.MetrizableSpace (UniversalCover N) := Manifold.metrizableSpace I (UniversalCover N)
    letI : T3Space (UniversalCover N) := inferInstance
    letI : Bundle.RiemannianBundle (TangentSpace I : UniversalCover N → Type _) := ⟨ĝTarget.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E₃ (TangentSpace I : UniversalCover N → Type _) :=
      ⟨⟨ĝTarget.inner, ĝTarget.contMDiff.continuous, by intro x v w; rfl⟩⟩
    letI : EMetricSpace (UniversalCover N) := EMetricSpace.ofRiemannianMetric I (UniversalCover N)
    letI : PseudoEMetricSpace (UniversalCover N) :=
      (EMetricSpace.ofRiemannianMetric I (UniversalCover N)).toPseudoEMetricSpace
    letI : CompleteSpace (UniversalCover N) := hĝTarget.complete
    ∀ (i : E₃ ≃ₗᵢ[ℝ] TangentSpace I (UniversalCover.basePoint (X := M)))
      (iTarget : E₃ ≃ₗᵢ[ℝ] TangentSpace I (UniversalCover.basePoint (X := N))),
      let ρ := normalizedUniversalCoverDeckRepresentation g hg (-1 / 4) quarter_negative x₀ hsec i
      let σ := (Hyperboloid.projectiveOrthogonalGroupEquiv 2 :
        (Hyperboloid E₃ ≃ᵢ Hyperboloid E₃) →* ProjectiveOrthogonalGroup.PO 3 1).comp ρ
      let ρTarget := normalizedUniversalCoverDeckRepresentation gTarget hgTarget (-1 / 4)
        quarter_negative xTarget hsecTarget iTarget
      let ΓTarget := ((Hyperboloid.projectiveOrthogonalGroupEquiv 2 :
        (Hyperboloid E₃ ≃ᵢ Hyperboloid E₃) →* ProjectiveOrthogonalGroup.PO 3 1).comp ρTarget).range
      ∀ {rSource : ℝ} (D : CuspTruncation.FiniteCuspTruncation (by decide : 1 ≤ 3) σ.range rSource)
        (ξSource : D.centers) (ξ η : B₃), ξ ≠ η → ∀ r : ℝ,
        8 * r < R →
        riemannianClosedBallOf g o (8 * r) ⊆
          (normalizedUniversalCoverProjection g hg (-1 / 4) quarter_negative x₀ hsec i) ''
            {z : H₃ | Busemann.busemann ξSource.val z < D.level ξSource} →
        Φ o ∉ (normalizedUniversalCoverProjection gTarget hgTarget (-1 / 4) quarter_negative
          xTarget hsecTarget iTarget) ''
            (AxisGeometry.axis ξ η ∩ OrbifoldThinRegions.thinRegion (by decide) ΓTarget r {ξ, η}) := by
  let _ : Inhabited M := ⟨x₀⟩
  let _ : LocallyPathConnectedSpace H := I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  let _ : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace H M
  let _ : SemilocallySimplyConnectedSpace M := manifold_semilocallySimplyConnectedSpace (I := I)
  let _ : SecondCountableTopology H := ModelWithCorners.secondCountableTopology I
  let _ : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
  let gN := scaleMetric (-(-1 / 4 : ℝ)) (neg_pos.mpr quarter_negative) g
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
  let _ : Inhabited N := ⟨xTarget⟩
  let _ : LocallyPathConnectedSpace H := I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  let _ : LocallyPathConnectedSpace N := ChartedSpace.locallyPathConnectedSpace H N
  let _ : SemilocallySimplyConnectedSpace N := manifold_semilocallySimplyConnectedSpace (I := I)
  let _ : SecondCountableTopology H := ModelWithCorners.secondCountableTopology I
  let _ : SecondCountableTopology N := ChartedSpace.secondCountable_of_sigmaCompact H N
  let gTargetN := scaleMetric (-(-1 / 4 : ℝ)) (neg_pos.mpr quarter_negative) gTarget
  let ĝTarget := UniversalCover.liftedMetric (I := I) gTargetN
  let hĝTarget : RiemannianMetricComplete ĝTarget := UniversalCover.liftedMetric_complete gTargetN (hgTarget.scaleMetric _ _)
  let _ : IsManifold I 1 (UniversalCover N) :=
    IsManifold.of_le (I := I) (M := UniversalCover N) (n := ∞) (by decide)
  let _ : TopologicalSpace.MetrizableSpace (UniversalCover N) := Manifold.metrizableSpace I (UniversalCover N)
  let _ : T3Space (UniversalCover N) := inferInstance
  let _ : Bundle.RiemannianBundle (TangentSpace I : UniversalCover N → Type _) := ⟨ĝTarget.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E₃ (TangentSpace I : UniversalCover N → Type _) :=
    ⟨⟨ĝTarget.inner, ĝTarget.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let _ : EMetricSpace (UniversalCover N) := EMetricSpace.ofRiemannianMetric I (UniversalCover N)
  let _ : PseudoEMetricSpace (UniversalCover N) :=
    (EMetricSpace.ofRiemannianMetric I (UniversalCover N)).toPseudoEMetricSpace
  let _ : CompleteSpace (UniversalCover N) := hĝTarget.complete
  dsimp only
  intro i iTarget rSource D ξSource ξ η hne r hmargin hcollar hmem
  obtain ⟨y, ⟨hy, hthin⟩, hcenter⟩ := hmem
  obtain ⟨a, τ, γ, ha, ha2, hshort, hτeq, hτ, hT, hTbound, hshift, hγeq, hγ0,
      hpγ, hsγ, hgγ, huγ, hcapγ⟩ := exists_periodic_geodesic_of_mem_axial_thinRegion
        gTarget hgTarget xTarget hsecTarget iTarget ξ η hne y r hy hthin
  have hA : 0 ≤ 4 * r := by linarith
  have hmargin' : 2 * (4 * r) < R := by linarith
  have hcaptured : Set.MapsTo γ (Set.Icc (0 : ℝ) (2 * |τ|))
      (riemannianClosedBallOf gTarget (Φ o) (4 * r)) := by
    intro t ht
    simpa only [hγ0, hcenter] using hcapγ t ht
  have hcollar' : riemannianClosedBallOf g o (2 * (4 * r)) ⊆
      (normalizedUniversalCoverProjection g hg (-1 / 4) quarter_negative x₀ hsec i) ''
        {z : H₃ | Busemann.busemann ξSource.val z < D.level ξSource} := by
    simpa only [show (2 : ℝ) * (4 * r) = 8 * r by ring] using hcollar
  exact not_periodic_of_captured_geodesic_in_cusp g hg x₀ hsec gTarget Φ o hp hA hmargin' hε hΦ
    γ hT (fun t _ => hsγ t) (fun t _ => hgγ t) (fun t _ => huγ t) hcaptured
    i D ξSource hcollar' hpγ

end DifferentialGeometry.Geometry.Hyperbolic
