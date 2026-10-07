import DifferentialGeometry.Geometry.Hyperbolic.ProjectionMetric
import DifferentialGeometry.Geometry.Hyperbolic.DeckGroup
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Orbifolds.ThinRegionMetric

noncomputable section

open scoped Manifold ContDiff Bundle ENNReal

namespace DifferentialGeometry.Geometry.Hyperbolic

open Riemannian.Topology (UniversalCover SemilocallySimplyConnectedSpace
  manifold_semilocallySimplyConnectedSpace)
open OrbifoldThinRegions (thinRegion)

local notation "E₃" => EuclideanSpace ℝ (Fin 3)
local notation "H₃" => DifferentialGeometry.Hyperbolic.HUpper 3
local notation "B₃" => DifferentialGeometry.HyperbolicBoundary.BoundaryH 3

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
theorem min_le_riemannianEDistOf_of_thinRegion_scalar :
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
      let pH := normalizedUniversalCoverProjection g hg κ hκ x₀ hsec i
      ∀ (r : ℝ) (S : Set B₃) (p q : H₃) (R : ℝ),
        p ∈ interior (thinRegion (by decide : 1 ≤ 3) σ.range r S) →
        q ∈ interior (thinRegion (by decide : 1 ≤ 3) σ.range r S) →
        riemannianBallOf g (pH p) R ⊆ pH '' interior (thinRegion (by decide : 1 ≤ 3) σ.range r S) →
        ∀ (b : H₃ → ℝ), LipschitzWith 1 b →
        (∀ γ : CuspCrossSections.endStabilizer (by decide : 1 ≤ 3) σ.range S, ∀ z : H₃,
          b ((HyperbolicAction.poMulAction (by decide : 1 ≤ 3)).smul (γ : ProjectiveOrthogonalGroup.PO 3 1) z) = b z) →
        ENNReal.ofReal (min R (|b q - b p| / Real.sqrt (-κ))) ≤ riemannianEDistOf g (pH p) (pH q) := by
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
  intro i r S p q R hp hq hball b hLip hinv
  let ρ := normalizedUniversalCoverDeckRepresentation g hg κ hκ x₀ hsec i
  let σ := (Hyperboloid.projectiveOrthogonalGroupEquiv 2 :
    (Hyperboloid E₃ ≃ᵢ Hyperboloid E₃) →* ProjectiveOrthogonalGroup.PO 3 1).comp ρ
  let pH := normalizedUniversalCoverProjection g hg κ hκ x₀ hsec i
  let _ := EquivariantMap.subAction (by decide : 1 ≤ 3) σ.range
  let piQ : H₃ → MulAction.orbitRel.Quotient σ.range H₃ := Quotient.mk _
  let F := normalizedUniversalCoverProjectiveQuotientHomeomorph g hg κ hκ x₀ hsec i
  have hF (z : H₃) : F (piQ z) = pH z :=
    normalizedUniversalCoverProjectiveQuotientHomeomorph_apply_mk g hg κ hκ x₀ hsec i z
  have hfiber {y z : H₃} (he : pH y = pH z) : piQ y = piQ z :=
    F.injective ((hF y).trans (he.trans (hF z).symm))
  let _ : DiscreteTopology ρ.range :=
    discreteTopology_range_normalizedUniversalCoverDeckRepresentation g hg κ hκ x₀ hsec i
  have hΓ : IsDiscrete (SetLike.coe σ.range) := by
    have hd : IsDiscrete (SetLike.coe ρ.range) := SetLike.isDiscrete_iff_discreteTopology.mpr inferInstance
    rw [show σ = (Hyperboloid.projectiveOrthogonalGroupEquiv 2 :
      (Hyperboloid E₃ ≃ᵢ Hyperboloid E₃) →* ProjectiveOrthogonalGroup.PO 3 1).comp ρ from rfl,
      MonoidHom.range_comp]
    exact hd.image (Hyperboloid.projectiveOrthogonalGroupEquiv 2).toHomeomorph.isInducing
  have hmodel : piQ '' Metric.ball p (Real.sqrt (-κ) * R) ⊆
      piQ '' interior (thinRegion (by decide : 1 ≤ 3) σ.range r S) := by
    rintro z ⟨y, hy, rfl⟩
    have hyimage : pH y ∈ riemannianBallOf g (pH p) R := by
      have he := image_ball_normalizedUniversalCoverProjection_original_metric g hg κ hκ x₀ hsec i p R
      exact he ▸ ⟨y, hy, rfl⟩
    obtain ⟨u, hu, heu⟩ := hball hyimage
    exact ⟨u, hu, hfiber heu⟩
  have hlabel := OrbifoldThinRegions.ball_subset_interior_thinRegion_of_quotient_image_subset
    (by decide : 1 ≤ 3) σ.range hΓ r S hp hmodel
  by_contra hnot
  have hd := lt_of_not_ge hnot
  obtain ⟨a, ha0, hda, ham⟩ := ENNReal.lt_iff_exists_real_btwn.mp hd
  have hminpos : 0 < min R (|b q - b p| / Real.sqrt (-κ)) :=
    ENNReal.ofReal_pos.mp (lt_of_le_of_lt bot_le hd)
  have ha : a < min R (|b q - b p| / Real.sqrt (-κ)) :=
    (ENNReal.ofReal_lt_ofReal_iff hminpos).mp ham
  have haR := ha.trans_le (min_le_left _ _)
  have hascalar := ha.trans_le (min_le_right _ _)
  have hs : 0 < Real.sqrt (-κ) := Real.sqrt_pos.mpr (neg_pos.mpr hκ)
  have hy : pH q ∈ riemannianBallOf g (pH p) a := hda
  have he := image_ball_normalizedUniversalCoverProjection_original_metric g hg κ hκ x₀ hsec i p a
  have hyimage : pH q ∈ pH '' Metric.ball p (Real.sqrt (-κ) * a) := he.symm ▸ hy
  obtain ⟨z, hz, hzq⟩ := hyimage
  have hzR : z ∈ Metric.ball p (Real.sqrt (-κ) * R) :=
    (Metric.ball_subset_ball (mul_le_mul_of_nonneg_left haR.le hs.le)) hz
  have hb : b z = b q := OrbifoldThinRegions.eq_of_quotient_eq_of_mem_interior_thinRegion
    (by decide : 1 ≤ 3) σ.range hΓ r S b hinv (hlabel hzR) hq (hfiber hzq)
  have hl : |b z - b p| ≤ dist z p := by simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using hLip.dist_le_mul z p
  have hzdist : dist z p < Real.sqrt (-κ) * a := hz
  rw [hb] at hl
  have hmul : Real.sqrt (-κ) * a < |b q - b p| := by
    simpa only [mul_comm] using (lt_div_iff₀ hs).mp hascalar
  linarith

end DifferentialGeometry.Geometry.Hyperbolic
