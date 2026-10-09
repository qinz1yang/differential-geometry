import DifferentialGeometry.Geometry.Hyperbolic.ProjectionGeodesic
import DifferentialGeometry.Geometry.Hyperbolic.Cusps.HeightDistance
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Geodesic.RadialCoordinates

noncomputable section

open scoped Manifold ContDiff Bundle ENNReal NNReal

namespace DifferentialGeometry.Geometry.Hyperbolic

open Riemannian.Geodesic (IsGeodesic)
open Riemannian.Topology (UniversalCover SemilocallySimplyConnectedSpace
  manifold_semilocallySimplyConnectedSpace)
open AsymptoticRays (rayTo)
open HyperbolicConvexity (geodFromTo)
open AxisGeometry (axisFoot)

local notation "E₃" => EuclideanSpace ℝ (Fin 3)
local notation "I₃" => 𝓘(ℝ, E₃)
local notation "H₃" => DifferentialGeometry.Hyperbolic.HUpper 3
local notation "B₃" => HyperbolicBoundary.BoundaryH 3

private theorem quarter_negative : (-1 / 4 : ℝ) < 0 := by norm_num

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E₃ H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
  (g : SmoothRiemannianMetric I M) (hg : RiemannianMetricComplete (I := I) g) (x₀ : M)
  (hsec : ∀ (x : M) (X Y : TangentSpace I x),
    Curvature.metricRm04StandardAt g x X Y Y X =
      (-1 / 4 : ℝ) * (g.inner x X X * g.inner x Y Y - g.inner x X Y * g.inner x X Y))

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem normalizedUniversalCoverProjection_outward_ray :
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
    ∀ (i : E₃ ≃ₗᵢ[ℝ] TangentSpace I (UniversalCover.basePoint (X := M))) (p : H₃) (ξ : B₃),
      let pH := normalizedUniversalCoverProjection g hg (-1 / 4) quarter_negative x₀ hsec i
      let c := fun t : ℝ => rayTo p ξ (-t / 2)
      let γ := fun t : ℝ => pH (c t)
      γ 0 = pH p ∧ ContMDiff 𝓘(ℝ, ℝ) I ∞ γ ∧ IsGeodesic g γ ∧
        (∀ t : ℝ, g.inner (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))
          (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)) = 1) ∧
        (∀ t : ℝ, 0 ≤ t → γ t ∈ riemannianClosedBallOf g (pH p) t) ∧
        Set.MapsTo γ (Set.Icc 0 1) (riemannianClosedBallOf g (pH p) 1) ∧
        ∀ t : ℝ, 2 * Busemann.busemann ξ (c t) - 2 * Busemann.busemann ξ p = t := by
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
  dsimp only
  intro i p ξ
  let pH := normalizedUniversalCoverProjection g hg (-1 / 4) quarter_negative x₀ hsec i
  let c := fun t : ℝ => rayTo p ξ (-t / 2)
  let γ := fun t : ℝ => pH (c t)
  have hzero : γ 0 = pH p := by
    dsimp only [γ, c]
    rw [neg_zero, zero_div, AsymptoticRays.rayTo_zero]
  have hgeo := normalizedUniversalCoverProjection_rayTo_neg_half_unit_geodesic g hg x₀ hsec i p ξ
  let _ : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let _ : T3Space M := inferInstance
  let _ : PseudoMetricSpace M := g.toPseudoMetricSpace
  have hL := lipschitzWith_normalizedUniversalCoverProjection_original_metric
    g hg (-1 / 4) quarter_negative x₀ hsec i
  have hscale : (⟨(Real.sqrt (-(-1 / 4 : ℝ)))⁻¹,
      inv_nonneg.mpr (Real.sqrt_nonneg _)⟩ : ℝ≥0) = 2 := by
    apply Subtype.ext
    change (Real.sqrt (-(-1 / 4 : ℝ)))⁻¹ = (2 : ℝ)
    norm_num [Real.sqrt_div]
  rw [hscale] at hL
  have hball (t : ℝ) (ht : 0 ≤ t) : γ t ∈ riemannianClosedBallOf g (pH p) t := by
    have hd := hL.dist_le_mul p (c t)
    have hmodel : dist p (c t) = t / 2 := by
      rw [AsymptoticRays.dist_rayTo_self, abs_div, abs_neg, abs_of_nonneg ht]
      norm_num
    change dist (pH p) (γ t) ≤ 2 * dist p (c t) at hd
    rw [hmodel] at hd
    have hdist : dist (pH p) (γ t) ≤ t := by linarith only [hd]
    change edist (pH p) (γ t) ≤ ENNReal.ofReal t
    rw [edist_dist]
    exact ENNReal.ofReal_le_ofReal hdist
  refine ⟨hzero, hgeo.1, hgeo.2.1, hgeo.2.2, hball, ?_, ?_⟩
  · intro t ht
    exact riemannianClosedBallOf_mono g (pH p) ht.2 (hball t ht.1)
  · intro t
    rw [HorosphereProjection.busemann_rayTo_neg_half]
    ring

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem normalizedUniversalCoverProjection_outward_normal_geodesic :
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
    ∀ (i : E₃ ≃ₗᵢ[ℝ] TangentSpace I (UniversalCover.basePoint (X := M)))
      (ξ η : B₃) (hne : ξ ≠ η) (p : H₃) (hp : axisFoot ξ η hne p ≠ p),
      let pH := normalizedUniversalCoverProjection g hg (-1 / 4) quarter_negative x₀ hsec i
      let r₀ := dist (axisFoot ξ η hne p) p
      let c := fun t : ℝ => geodFromTo (axisFoot ξ η hne p) p hp (r₀ + t / 2)
      let γ := fun t : ℝ => pH (c t)
      γ 0 = pH p ∧ ContMDiff 𝓘(ℝ, ℝ) I ∞ γ ∧ IsGeodesic g γ ∧
        (∀ t : ℝ, g.inner (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))
          (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)) = 1) ∧
        (∀ t : ℝ, 0 ≤ t → γ t ∈ riemannianClosedBallOf g (pH p) t) ∧
        Set.MapsTo γ (Set.Icc 0 1) (riemannianClosedBallOf g (pH p) 1) ∧
        ∀ t : ℝ, 0 ≤ t → 2 * dist (c t) (axisFoot ξ η hne (c t)) - 2 * r₀ = t := by
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
  dsimp only
  intro i ξ η hne p hp
  let pH := normalizedUniversalCoverProjection g hg (-1 / 4) quarter_negative x₀ hsec i
  let r₀ := dist (axisFoot ξ η hne p) p
  let c := fun t : ℝ => geodFromTo (axisFoot ξ η hne p) p hp (r₀ + t / 2)
  let γ := fun t : ℝ => pH (c t)
  have hzero : γ 0 = pH p := by
    dsimp only [γ, c, r₀]
    rw [zero_div, add_zero, HyperbolicConvexity.geodFromTo_dist]
  have hgeo := normalizedUniversalCoverProjection_geodFromTo_half_unit_geodesic
    g hg x₀ hsec i (axisFoot ξ η hne p) p hp r₀
  let _ : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let _ : T3Space M := inferInstance
  let _ : PseudoMetricSpace M := g.toPseudoMetricSpace
  have hL := lipschitzWith_normalizedUniversalCoverProjection_original_metric
    g hg (-1 / 4) quarter_negative x₀ hsec i
  have hscale : (⟨(Real.sqrt (-(-1 / 4 : ℝ)))⁻¹,
      inv_nonneg.mpr (Real.sqrt_nonneg _)⟩ : ℝ≥0) = 2 := by
    apply Subtype.ext
    change (Real.sqrt (-(-1 / 4 : ℝ)))⁻¹ = (2 : ℝ)
    norm_num [Real.sqrt_div]
  rw [hscale] at hL
  have hball (t : ℝ) (ht : 0 ≤ t) : γ t ∈ riemannianClosedBallOf g (pH p) t := by
    have hd := hL.dist_le_mul p (c t)
    have hmodel : dist p (c t) = t / 2 := by
      calc
        dist p (c t) = dist (geodFromTo (axisFoot ξ η hne p) p hp r₀)
            (geodFromTo (axisFoot ξ η hne p) p hp (r₀ + t / 2)) := by
          rw [HyperbolicConvexity.geodFromTo_dist]
        _ = |r₀ - (r₀ + t / 2)| := HyperbolicConvexity.dist_geodFromTo hp _ _
        _ = t / 2 := by
          rw [show r₀ - (r₀ + t / 2) = -(t / 2) by ring, abs_neg,
            abs_of_nonneg (div_nonneg ht (by norm_num))]
    change dist (pH p) (γ t) ≤ 2 * dist p (c t) at hd
    rw [hmodel] at hd
    have hdist : dist (pH p) (γ t) ≤ t := by linarith only [hd]
    change edist (pH p) (γ t) ≤ ENNReal.ofReal t
    rw [edist_dist]
    exact ENNReal.ofReal_le_ofReal hdist
  refine ⟨hzero, hgeo.1, hgeo.2.1, hgeo.2.2, hball, ?_, ?_⟩
  · intro t ht
    exact riemannianClosedBallOf_mono g (pH p) ht.2 (hball t ht.1)
  · intro t ht
    rw [AxisGeometry.dist_axisFoot_normal_geod_add_half ξ η hne p hp
      (add_nonneg dist_nonneg (div_nonneg ht (by norm_num)))]
    ring

end DifferentialGeometry.Geometry.Hyperbolic
