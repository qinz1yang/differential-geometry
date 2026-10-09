import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Cusps.Section
import DifferentialGeometry.Geometry.Hyperbolic.ThinRegionCharts
import DifferentialGeometry.Geometry.Hyperbolic.Cusps.Inclusion
import DifferentialGeometry.Geometry.Hyperbolic.ThinRegionDistance
import DifferentialGeometry.Geometry.Hyperbolic.RadialCurves
import DifferentialGeometry.Topology.Manifold.TransverseGraph
import DifferentialGeometry.Topology.Manifold.CurveTransversality
import DifferentialGeometry.Geometry.Hyperbolic.Cusps.Height
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Geodesic.TubeLevel
import DifferentialGeometry.Geometry.Hyperbolic.Cusps.HeightTransversality

noncomputable section

section
open scoped Manifold ContDiff Bundle Topology
private theorem contMDiff_injective_mfderiv_of_eq_comp
    {E F G H H' H'' X Y Z : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace H'']
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'} {K : ModelWithCorners ℝ G H''}
    [TopologicalSpace X] [ChartedSpace H X] [TopologicalSpace Y] [ChartedSpace H' Y]
    [TopologicalSpace Z] [ChartedSpace H'' Z]
    (f : X → Z) (e : Y → Z) (β : X → Y) (he : IsLocalDiffeomorph J K ∞ e)
    (hβ : ContMDiff I J ∞ β) (hinj : ∀ x, Function.Injective (mfderiv I J β x))
    (heq : f = e ∘ β) : ContMDiff I K ∞ f ∧ ∀ x, Function.Injective (mfderiv I K f x) := by
  subst f
  refine ⟨he.contMDiff.comp hβ, ?_⟩
  intro x
  rw [mfderiv_comp x (he.contMDiff.mdifferentiableAt (by simp)) (hβ.mdifferentiableAt (by simp))]
  have hei : Function.Injective (mfderiv J K e (β x)) := by
    rw [← he.mfderivToContinuousLinearEquiv_coe (by simp : (∞ : ℕ∞ω) ≠ 0)]
    exact (he.mfderivToContinuousLinearEquiv (by simp : (∞ : ℕ∞ω) ≠ 0) (β x)).injective
  exact hei.comp (hinj x)

namespace DifferentialGeometry.Geometry.Hyperbolic
open Riemannian.Topology (UniversalCover SemilocallySimplyConnectedSpace
  manifold_semilocallySimplyConnectedSpace)
open ProjectiveOrthogonalGroup (PO)
local notation "E₃" => EuclideanSpace ℝ (Fin 3)
local notation "I₃" => 𝓘(ℝ, E₃)
local notation "K₂" => 𝓘(ℝ, Fin 2 → ℝ)
local notation "H₃" => DifferentialGeometry.Hyperbolic.HUpper 3

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E₃ H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem native_slice_geometry
    (g : SmoothRiemannianMetric I M) (hg : RiemannianMetricComplete (I := I) g)
    (κ : ℝ) (hκ : κ < 0) (x₀ : M)
    (hsec : ∀ (x : M) (v w : TangentSpace I x),
      Curvature.metricRm04StandardAt g x v w w v =
        κ * (g.inner x v v * g.inner x w w - g.inner x v w * g.inner x v w)) :
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
      let hΓ : IsDiscrete (SetLike.coe σ.range) :=
        (exists_normalizedUniversalCoverThinRegionCharts g hg κ hκ x₀ hsec i).choose
      let P := CuspCrossSections.endStabilizer (Nat.le_add_left 1 2) σ.range (Set.singleton ξ.val)
      letI := EquivariantMap.subAction (Nat.le_add_left 1 2) σ.range
      letI := EquivariantMap.subAction (Nat.le_add_left 1 2) P
      letI : IsCancelSMul σ.range H₃ :=
        isCancelSMul_projective_range_normalizedUniversalCoverDeckRepresentation g hg κ hκ x₀ hsec i
      letI : IsCancelSMul P H₃ := EquivariantMap.isCancelSMul_subAction
        (Nat.le_add_left 1 2) (show P ≤ σ.range from inf_le_left)
      let S := (Quotient.mk (MulAction.orbitRel P H₃)) '' Busemann.horosphere ξ.val (D.level ξ)
      letI : ChartedSpace (Fin 2 → ℝ) S := D.horosphereQuotientChartedSpace hΓ ξ
      ∀ d : Set.Ici (0 : ℝ),
      let β : S → M := fun s => normalizedUniversalCoverCuspCylinderMap g hg κ hκ x₀ hsec i D ξ (s, d)
      CompactSpace S ∧ PathConnectedSpace S ∧
        ContMDiff K₂ I ∞ β ∧ Function.Injective β ∧
          ∀ s, Function.Injective (mfderiv K₂ I β s) := by
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
  let hΓ : IsDiscrete (SetLike.coe σ.range) :=
    (exists_normalizedUniversalCoverThinRegionCharts g hg κ hκ x₀ hsec i).choose
  let P := CuspCrossSections.endStabilizer (Nat.le_add_left 1 2) σ.range (Set.singleton ξ.val)
  let := EquivariantMap.subAction (Nat.le_add_left 1 2) σ.range
  let := EquivariantMap.subAction (Nat.le_add_left 1 2) P
  let : DiscreteTopology σ.range := isDiscrete_iff_discreteTopology.mp hΓ
  let : IsCancelSMul σ.range H₃ :=
    isCancelSMul_projective_range_normalizedUniversalCoverDeckRepresentation g hg κ hκ x₀ hsec i
  let : IsCancelSMul P H₃ := EquivariantMap.isCancelSMul_subAction
    (Nat.le_add_left 1 2) (show P ≤ σ.range from inf_le_left)
  let : ContinuousConstSMul σ.range H₃ :=
    ⟨fun a => (HyperbolicAction.contMDiff_po_smul 2 ∞ (a : PO 3 1)).continuous⟩
  let : ContMDiffConstSMul I₃ ∞ σ.range H₃ :=
    ⟨fun a => HyperbolicAction.contMDiff_po_smul 2 ∞ (a : PO 3 1)⟩
  let : ProperlyDiscontinuousSMul σ.range H₃ :=
    OrbifoldCompactness.properlyDiscontinuous_subAction (Nat.le_add_left 1 2) σ.range hΓ
  let S := (Quotient.mk (MulAction.orbitRel P H₃)) '' Busemann.horosphere ξ.val (D.level ξ)
  let : ChartedSpace (Fin 2 → ℝ) S := D.horosphereQuotientChartedSpace hΓ ξ
  intro d
  let e := normalizedUniversalCoverProjectiveQuotientHomeomorph g hg κ hκ x₀ hsec i
  let πG := Quotient.mk (MulAction.orbitRel σ.range H₃)
  have hπ := MulAction.isLocalDiffeomorph_quotientMk_of_properlyDiscontinuousSMul
    (G := σ.range) (M := H₃) (n := ∞) I₃
  have hpH : IsLocalDiffeomorph I₃ I ∞ (e ∘ πG) := by
    have heq : e ∘ πG = normalizedUniversalCoverProjection g hg κ hκ x₀ hsec i :=
      funext (normalizedUniversalCoverProjectiveQuotientHomeomorph_apply_mk g hg κ hκ x₀ hsec i)
    rw [heq]
    exact normalizedUniversalCoverProjection_isLocalDiffeomorph g hg κ hκ x₀ hsec i
  have he : IsLocalDiffeomorph I₃ I ∞ e := by
    intro x
    obtain ⟨z, rfl⟩ := Quotient.mk_surjective x
    exact DifferentialGeometry.isLocalDiffeomorphAt_of_comp (hpH z) (hπ z)
  let βQ : S → MulAction.orbitRel.Quotient σ.range H₃ := fun s => D.horoballCylinderMap hΓ ξ (s,d)
  have hβQ := D.contMDiff_horoballCylinderMap_slice ξ d
  have hβQinj := D.injective_mfderiv_horoballCylinderMap_slice ξ d
  have hcompact : CompactSpace S := isCompact_iff_compactSpace.mp
    (D.isCompact_quotient_horosphere_of_compact_core hΓ ξ)
  have hpath : PathConnectedSpace S := D.pathConnectedSpace_quotient_horosphere ξ
  have heq : (fun s : S => normalizedUniversalCoverCuspCylinderMap g hg κ hκ x₀ hsec i D ξ (s,d)) =
      e ∘ βQ := by
    funext s
    obtain ⟨s, z, hz, rfl⟩ := s
    have hleft := normalizedUniversalCoverCuspCylinderMap_apply_mk g hg κ hκ x₀ hsec i D ξ z hz d
    have hright := D.horoballCylinderMap_apply_mk hΓ ξ z hz d
    exact hleft.trans ((normalizedUniversalCoverProjectiveQuotientHomeomorph_apply_mk
      g hg κ hκ x₀ hsec i (AsymptoticRays.rayTo z ξ.val d.val)).symm.trans
        (congrArg e hright).symm)
  have hgeom := contMDiff_injective_mfderiv_of_eq_comp _ e βQ he hβQ hβQinj heq
  refine ⟨hcompact, hpath, hgeom.1, ?_, hgeom.2⟩
  intro s t hst
  exact congrArg Prod.fst ((normalizedUniversalCoverCuspCylinderMap_isClosedEmbedding
    g hg κ hκ x₀ hsec i D ξ).injective hst)

end DifferentialGeometry.Geometry.Hyperbolic
end

section
open scoped Manifold ContDiff Bundle ENNReal Topology
namespace DifferentialGeometry.Geometry.Hyperbolic
open Riemannian.Topology (UniversalCover SemilocallySimplyConnectedSpace
  manifold_semilocallySimplyConnectedSpace)
local notation "E₃" => EuclideanSpace ℝ (Fin 3)
local notation "H₃" => DifferentialGeometry.Hyperbolic.HUpper 3
local notation "B₃" => DifferentialGeometry.HyperbolicBoundary.BoundaryH 3

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E₃ H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem radial_endpoint_separated
    (g : SmoothRiemannianMetric I M) (hg : RiemannianMetricComplete (I := I) g) (x₀ : M)
    (hsec : ∀ (x : M) (v w : TangentSpace I x),
      Curvature.metricRm04StandardAt g x v w w v =
        (-1 / 4 : ℝ) * (g.inner x v v * g.inner x w w - g.inner x v w * g.inner x v w)) :
    letI : Inhabited M := ⟨x₀⟩
    letI : LocallyPathConnectedSpace H := I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
    letI : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace H M
    letI : SemilocallySimplyConnectedSpace M := manifold_semilocallySimplyConnectedSpace (I := I)
    letI : SecondCountableTopology H := ModelWithCorners.secondCountableTopology I
    letI : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
    let gN := scaleMetric (-(-1 / 4 : ℝ)) (neg_pos.mpr (by norm_num)) g
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
      let ρ := normalizedUniversalCoverDeckRepresentation g hg (-1 / 4) (by norm_num) x₀ hsec i
      let σ := (Hyperboloid.projectiveOrthogonalGroupEquiv 2 :
        (Hyperboloid E₃ ≃ᵢ Hyperboloid E₃) →* ProjectiveOrthogonalGroup.PO 3 1).comp ρ
      let pH := normalizedUniversalCoverProjection g hg (-1 / 4) (by norm_num) x₀ hsec i
      ∀ (r : ℝ) (S : Set B₃) (y z : H₃),
        y ∈ interior (OrbifoldThinRegions.thinRegion (by decide : 1 ≤ 3) σ.range r S) →
        dist y z ≤ 1 / 2 →
        riemannianBallOf g (pH y) 2 ⊆
          pH '' interior (OrbifoldThinRegions.thinRegion (by decide : 1 ≤ 3) σ.range r S) →
        ∀ (b : H₃ → ℝ), LipschitzWith 1 b →
        (∀ a : CuspCrossSections.endStabilizer (by decide : 1 ≤ 3) σ.range S, ∀ w : H₃,
          b ((HyperbolicAction.poMulAction (by decide : 1 ≤ 3)).smul
            (a : ProjectiveOrthogonalGroup.PO 3 1) w) = b w) →
        |b z - b y| = 1 / 2 →
        ENNReal.ofReal 1 ≤ riemannianEDistOf g (pH y) (pH z) := by
  let _ : Inhabited M := ⟨x₀⟩
  let _ : LocallyPathConnectedSpace H := I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  let _ : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace H M
  let _ : SemilocallySimplyConnectedSpace M := manifold_semilocallySimplyConnectedSpace (I := I)
  let _ : SecondCountableTopology H := ModelWithCorners.secondCountableTopology I
  let _ : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
  let gN := scaleMetric (-(-1 / 4 : ℝ)) (neg_pos.mpr (by norm_num)) g
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
  intro i r S y z hy hdist hball b hLip hinv hscalar
  let ρ := normalizedUniversalCoverDeckRepresentation g hg (-1 / 4) (by norm_num) x₀ hsec i
  let σ := (Hyperboloid.projectiveOrthogonalGroupEquiv 2 :
    (Hyperboloid E₃ ≃ᵢ Hyperboloid E₃) →* ProjectiveOrthogonalGroup.PO 3 1).comp ρ
  let pH := normalizedUniversalCoverProjection g hg (-1 / 4) (by norm_num) x₀ hsec i
  let _ := EquivariantMap.subAction (by decide : 1 ≤ 3) σ.range
  let πG := Quotient.mk (MulAction.orbitRel σ.range H₃)
  let e := normalizedUniversalCoverProjectiveQuotientHomeomorph g hg (-1 / 4) (by norm_num) x₀ hsec i
  have hrep (w : H₃) : e (πG w) = pH w :=
    normalizedUniversalCoverProjectiveQuotientHomeomorph_apply_mk g hg (-1 / 4) (by norm_num) x₀ hsec i w
  have hΓ : IsDiscrete (SetLike.coe σ.range) :=
    (exists_normalizedUniversalCoverThinRegionCharts g hg (-1 / 4) (by norm_num) x₀ hsec i).choose
  have hmodel : πG '' Metric.ball y 1 ⊆
      πG '' interior (OrbifoldThinRegions.thinRegion (by decide : 1 ≤ 3) σ.range r S) := by
    rintro u ⟨w, hw, rfl⟩
    have himage := image_ball_normalizedUniversalCoverProjection_original_metric
      g hg (-1 / 4) (by norm_num) x₀ hsec i y 2
    norm_num [Real.sqrt_div] at himage
    have hwball : pH w ∈ riemannianBallOf g (pH y) 2 := himage ▸ ⟨w, hw, rfl⟩
    obtain ⟨w', hw', heq⟩ := hball hwball
    refine ⟨w', hw', e.injective ?_⟩
    exact (hrep w').trans (heq.trans (hrep w).symm)
  have hz : z ∈ interior (OrbifoldThinRegions.thinRegion (by decide : 1 ≤ 3) σ.range r S) := by
    apply OrbifoldThinRegions.ball_subset_interior_thinRegion_of_quotient_image_subset
      (by decide : 1 ≤ 3) σ.range hΓ r S hy hmodel
    change dist z y < 1
    rw [dist_comm]
    linarith
  have h := min_le_riemannianEDistOf_of_thinRegion_scalar
    g hg (-1 / 4) (by norm_num) x₀ hsec i r S y z 2 hy hz hball b hLip hinv
  have hnum : min (2 : ℝ) (|b z - b y| / Real.sqrt (-(-1 / 4 : ℝ))) = 1 := by
    rw [hscalar]
    norm_num [Real.sqrt_div]
  rw [hnum] at h
  exact h

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem cusp_radial_endpoint_separated
    (g : SmoothRiemannianMetric I M) (hg : RiemannianMetricComplete (I := I) g) (x₀ : M)
    (hsec : ∀ (x : M) (v w : TangentSpace I x),
      Curvature.metricRm04StandardAt g x v w w v =
        (-1 / 4 : ℝ) * (g.inner x v v * g.inner x w w - g.inner x v w * g.inner x v w)) :
    letI : Inhabited M := ⟨x₀⟩
    letI : LocallyPathConnectedSpace H := I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
    letI : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace H M
    letI : SemilocallySimplyConnectedSpace M := manifold_semilocallySimplyConnectedSpace (I := I)
    letI : SecondCountableTopology H := ModelWithCorners.secondCountableTopology I
    letI : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
    let gN := scaleMetric (-(-1 / 4 : ℝ)) (neg_pos.mpr (by norm_num)) g
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
      let ρ := normalizedUniversalCoverDeckRepresentation g hg (-1 / 4) (by norm_num) x₀ hsec i
      let σ := (Hyperboloid.projectiveOrthogonalGroupEquiv 2 :
        (Hyperboloid E₃ ≃ᵢ Hyperboloid E₃) →* ProjectiveOrthogonalGroup.PO 3 1).comp ρ
      let pH := normalizedUniversalCoverProjection g hg (-1 / 4) (by norm_num) x₀ hsec i
      ∀ {r : ℝ} (D : CuspTruncation.FiniteCuspTruncation (Nat.le_add_left 1 2) σ.range r)
        (ξ : D.centers) (y : H₃),
        y ∈ interior (OrbifoldThinRegions.thinRegion (Nat.le_add_left 1 2) σ.range r {ξ.val}) →
        riemannianBallOf g (pH y) 2 ⊆
          pH '' interior (OrbifoldThinRegions.thinRegion (Nat.le_add_left 1 2) σ.range r {ξ.val}) →
        ENNReal.ofReal 1 ≤ riemannianEDistOf g (pH y)
          (pH (AsymptoticRays.rayTo y ξ.val (-1 / 2))) := by
  let _ : Inhabited M := ⟨x₀⟩
  let _ : LocallyPathConnectedSpace H := I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  let _ : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace H M
  let _ : SemilocallySimplyConnectedSpace M := manifold_semilocallySimplyConnectedSpace (I := I)
  let _ : SecondCountableTopology H := ModelWithCorners.secondCountableTopology I
  let _ : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
  let gN := scaleMetric (-(-1 / 4 : ℝ)) (neg_pos.mpr (by norm_num)) g
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
  intro i r D ξ y hy hball
  let ρ := normalizedUniversalCoverDeckRepresentation g hg (-1 / 4) (by norm_num) x₀ hsec i
  let σ := (Hyperboloid.projectiveOrthogonalGroupEquiv 2 :
    (Hyperboloid E₃ ≃ᵢ Hyperboloid E₃) →* ProjectiveOrthogonalGroup.PO 3 1).comp ρ
  have hΓ : IsDiscrete (SetLike.coe σ.range) :=
    (exists_normalizedUniversalCoverThinRegionCharts g hg (-1 / 4) (by norm_num) x₀ hsec i).choose
  have hhor := CuspCrossSections.horospherical_endStabilizer
    (Nat.le_add_left 1 2) σ.range hΓ (D.region_nonempty ξ)
  have hLip : LipschitzWith 1 (Busemann.busemann ξ.val) := by
    apply LipschitzWith.of_dist_le_mul
    intro z w
    simpa only [NNReal.coe_one, one_mul, Real.dist_eq] using Busemann.busemann_lipschitz ξ.val z w
  have hinv (a : CuspCrossSections.endStabilizer (Nat.le_add_left 1 2) σ.range {ξ.val}) (w : H₃) :
      Busemann.busemann ξ.val ((HyperbolicAction.poMulAction (Nat.le_add_left 1 2)).smul
        (a : ProjectiveOrthogonalGroup.PO 3 1) w) = Busemann.busemann ξ.val w := by
    have h := BusemannCocycle.po_busemann_smul (Nat.le_add_left 1 2) a ξ.val w
    rw [(hhor a).1, (hhor a).2, Real.log_one, sub_zero] at h
    exact h
  have hdist : dist y (AsymptoticRays.rayTo y ξ.val (-1 / 2)) ≤ (1 / 2 : ℝ) := by
    rw [AsymptoticRays.dist_rayTo_self]
    norm_num
  have hscalar : |Busemann.busemann ξ.val (AsymptoticRays.rayTo y ξ.val (-1 / 2)) -
      Busemann.busemann ξ.val y| = (1 / 2 : ℝ) := by
    rw [HorosphereProjection.busemann_rayTo]
    ring_nf
    norm_num
  exact radial_endpoint_separated g hg x₀ hsec i r {ξ.val} y _ hy hdist hball _ hLip hinv hscalar

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem axial_radial_endpoint_separated
    (g : SmoothRiemannianMetric I M) (hg : RiemannianMetricComplete (I := I) g) (x₀ : M)
    (hsec : ∀ (x : M) (v w : TangentSpace I x),
      Curvature.metricRm04StandardAt g x v w w v =
        (-1 / 4 : ℝ) * (g.inner x v v * g.inner x w w - g.inner x v w * g.inner x v w)) :
    letI : Inhabited M := ⟨x₀⟩
    letI : LocallyPathConnectedSpace H := I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
    letI : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace H M
    letI : SemilocallySimplyConnectedSpace M := manifold_semilocallySimplyConnectedSpace (I := I)
    letI : SecondCountableTopology H := ModelWithCorners.secondCountableTopology I
    letI : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
    let gN := scaleMetric (-(-1 / 4 : ℝ)) (neg_pos.mpr (by norm_num)) g
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
      let ρ := normalizedUniversalCoverDeckRepresentation g hg (-1 / 4) (by norm_num) x₀ hsec i
      let σ := (Hyperboloid.projectiveOrthogonalGroupEquiv 2 :
        (Hyperboloid E₃ ≃ᵢ Hyperboloid E₃) →* ProjectiveOrthogonalGroup.PO 3 1).comp ρ
      let pH := normalizedUniversalCoverProjection g hg (-1 / 4) (by norm_num) x₀ hsec i
      ∀ (r : ℝ) (ξ η : B₃) (hne : ξ ≠ η) (y : H₃)
        (hoff : AxisGeometry.axisFoot ξ η hne y ≠ y),
        y ∈ interior (OrbifoldThinRegions.thinRegion (by decide : 1 ≤ 3) σ.range r {ξ,η}) →
        riemannianBallOf g (pH y) 2 ⊆
          pH '' interior (OrbifoldThinRegions.thinRegion (by decide : 1 ≤ 3) σ.range r {ξ,η}) →
        ENNReal.ofReal 1 ≤ riemannianEDistOf g (pH y)
          (pH (HyperbolicConvexity.geodFromTo (AxisGeometry.axisFoot ξ η hne y) y hoff
            (dist (AxisGeometry.axisFoot ξ η hne y) y + 1 / 2))) := by
  let _ : Inhabited M := ⟨x₀⟩
  let _ : LocallyPathConnectedSpace H := I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  let _ : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace H M
  let _ : SemilocallySimplyConnectedSpace M := manifold_semilocallySimplyConnectedSpace (I := I)
  let _ : SecondCountableTopology H := ModelWithCorners.secondCountableTopology I
  let _ : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
  let gN := scaleMetric (-(-1 / 4 : ℝ)) (neg_pos.mpr (by norm_num)) g
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
  intro i r ξ η hne y hoff hy hball
  let ρ := normalizedUniversalCoverDeckRepresentation g hg (-1 / 4) (by norm_num) x₀ hsec i
  let σ := (Hyperboloid.projectiveOrthogonalGroupEquiv 2 :
    (Hyperboloid E₃ ≃ᵢ Hyperboloid E₃) →* ProjectiveOrthogonalGroup.PO 3 1).comp ρ
  let c := HyperbolicConvexity.geodFromTo (AxisGeometry.axisFoot ξ η hne y) y hoff
  let r₀ := dist (AxisGeometry.axisFoot ξ η hne y) y
  have hc0 : c r₀ = y := HyperbolicConvexity.geodFromTo_dist hoff
  have hdist : dist y (c (r₀ + 1 / 2)) ≤ (1 / 2 : ℝ) := by
    calc
      _ = dist (c r₀) (c (r₀ + 1 / 2)) := congrArg (fun w => dist w (c (r₀ + 1 / 2))) hc0.symm
      _ = |r₀ - (r₀ + 1 / 2)| := HyperbolicConvexity.dist_geodFromTo hoff _ _
      _ ≤ 1 / 2 := by ring_nf; norm_num
  let b : H₃ → ℝ := fun w => dist w (AxisGeometry.axisFoot ξ η hne w)
  have hinv (a : CuspCrossSections.endStabilizer (by decide : 1 ≤ 3) σ.range {ξ,η}) (w : H₃) :
      b ((HyperbolicAction.poMulAction (by decide : 1 ≤ 3)).smul
        (a : ProjectiveOrthogonalGroup.PO 3 1) w) = b w := by
    have he := (ElementaryEnds.mem_setStabilizer (by decide : 1 ≤ 3) {ξ,η} a).mp a.property.2
    have hp :
        (HyperbolicBoundary.poBoundaryMulAction (by decide : 1 ≤ 3)).smul
          (a : ProjectiveOrthogonalGroup.PO 3 1) ξ ∈ ({ξ,η} : Set B₃) ∧
        (HyperbolicBoundary.poBoundaryMulAction (by decide : 1 ≤ 3)).smul
          (a : ProjectiveOrthogonalGroup.PO 3 1) η ∈ ({ξ,η} : Set B₃) :=
      ⟨he.subset ⟨ξ, by simp, rfl⟩, he.subset ⟨η, by simp, rfl⟩⟩
    exact AxisGeometry.dist_axisFoot_smul (by decide : 1 ≤ 3) a ξ η hne hp w
  have hscalar : |b (c (r₀ + 1 / 2)) - b y| = (1 / 2 : ℝ) := by
    have h := AxisGeometry.dist_axisFoot_normal_geod_add_half ξ η hne y hoff
      (t := 1) (by positivity)
    change b (c (r₀ + 1 / 2)) = r₀ + 1 / 2 at h
    have hby : b y = r₀ := dist_comm _ _
    rw [h,hby]
    ring_nf
    norm_num
  exact radial_endpoint_separated g hg x₀ hsec i r {ξ,η} y _ hy hdist hball b
    (AxisGeometry.lipschitzWith_dist_axisFoot ξ η hne) hinv hscalar

end DifferentialGeometry.Geometry.Hyperbolic
end

section
open scoped Topology Manifold ContDiff

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace in
private theorem mfderiv_eq_vertical_of_eventuallyEq
    {E H N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace N] [ChartedSpace H N]
    (e : ℝ → N × ℝ) (p : N) (f : ℝ → ℝ) (c : ℝ)
    (he : e =ᶠ[𝓝 0] fun t => (p, f t)) (hf : HasDerivAt f c 0) :
    mfderiv 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ)) e 0 (1 : ℝ) = (0, c) := by
  rw [he.mfderiv_eq]
  change mfderiv 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ)) (fun t => (p, f t)) 0 (1 : ℝ) = (0, c)
  rw [mfderiv_prodMk mdifferentiableAt_const hf.differentiableAt.mdifferentiableAt]
  change (mfderiv 𝓘(ℝ, ℝ) I (fun _ : ℝ => p) 0 (1 : ℝ),
    mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) f 0 (1 : ℝ)) = (0, c)
  apply Prod.ext
  · change mfderiv 𝓘(ℝ, ℝ) I (fun _ : ℝ => p) 0 (1 : ℝ) = 0
    rw [mfderiv_const]
    rfl
  · change mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) f 0 (1 : ℝ) = c
    rw [mfderiv_eq_fderiv]
    change fderiv ℝ f 0 (1 : ℝ) = c
    rw [fderiv_apply_one_eq_deriv, hf.deriv]

namespace DifferentialGeometry.CuspTruncation.FiniteCuspTruncation

open ProjectiveOrthogonalGroup (PO)
open Hyperbolic (HUpper)
open CuspCrossSections (endStabilizer)

variable {m : ℕ}

private local instance (Δ : Subgroup (PO (m + 1) 1)) : MulAction Δ (HUpper (m + 1)) :=
  EquivariantMap.subAction (Nat.le_add_left 1 m) Δ

private local instance (Δ : Subgroup (PO (m + 1) 1)) : ContinuousConstSMul Δ (HUpper (m + 1)) :=
  ⟨fun γ => (HyperbolicAction.contMDiff_po_smul m ∞ (γ : PO (m + 1) 1)).continuous⟩

private local instance (Δ : Subgroup (PO (m + 1) 1)) :
    ContMDiffConstSMul 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) ∞ Δ (HUpper (m + 1)) :=
  ⟨fun γ => HyperbolicAction.contMDiff_po_smul m ∞ (γ : PO (m + 1) 1)⟩

variable {Γ : Subgroup (PO (m + 1) 1)} [DiscreteTopology Γ]
  [IsCancelSMul Γ (HUpper (m + 1))] {r : ℝ}
  (D : FiniteCuspTruncation (Nat.le_add_left 1 m) Γ r) (ξ : D.centers)

local notation "P" => endStabilizer (Nat.le_add_left 1 m) Γ (Set.singleton ξ.val)
local notation "hΓ" => (isDiscrete_iff_discreteTopology.mpr (inferInstance : DiscreteTopology Γ))
local notation "QP" => MulAction.orbitRel.Quotient P (HUpper (m + 1))
local notation "QΓ" => MulAction.orbitRel.Quotient Γ (HUpper (m + 1))
local notation "πP" => Quotient.mk (MulAction.orbitRel P (HUpper (m + 1)))
local notation "S" => (πP '' Busemann.horosphere ξ.val (D.level ξ))
local notation "I" => 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1)))
local notation "K" => 𝓘(ℝ, Fin m → ℝ)
local notation "J" => ModelWithCorners.prod K 𝓘(ℝ, ℝ)
local notation "E" => D.horosphereHeightHomeomorph hΓ ξ
local notation "A" => D.horosphereGraphChart hΓ ξ

private local instance : IsCancelSMul P (HUpper (m + 1)) :=
  EquivariantMap.isCancelSMul_subAction (Nat.le_add_left 1 m) (show P ≤ Γ from inf_le_left)

private local instance : ProperlyDiscontinuousSMul P (HUpper (m + 1)) :=
  OrbifoldCompactness.properlyDiscontinuous_subAction (Nat.le_add_left 1 m) P ((hΓ).mono inf_le_left)

private local instance : ProperlyDiscontinuousSMul Γ (HUpper (m + 1)) :=
  OrbifoldCompactness.properlyDiscontinuous_subAction (Nat.le_add_left 1 m) Γ hΓ

private local instance : ChartedSpace (Fin m → ℝ) S := D.horosphereQuotientChartedSpace hΓ ξ

private local instance : IsManifold K ∞ S := D.isManifold_quotient_horosphere hΓ ξ

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace in
private theorem cusp_chart_radial_velocity (p : HUpper (m + 1))
    (hp : p ∈ interior (OrbifoldThinRegions.thinRegion (Nat.le_add_left 1 m) Γ r (Set.singleton ξ.val))) :
    mfderiv 𝓘(ℝ, ℝ) J (fun t : ℝ => (A).symm
      (Quotient.mk (MulAction.orbitRel Γ (HUpper (m + 1)))
        (AsymptoticRays.rayTo p ξ.val (-t / 2)))) 0 (1 : ℝ) = (0, (1 / 2 : ℝ)) := by
  exact mfderiv_eq_vertical_of_eventuallyEq _ _ _ _
    (eventually_horosphereGraphChart_symm_rayTo_neg_half D hΓ ξ p hp)
    (((hasDerivAt_id (0 : ℝ)).div_const 2).const_add _)

end DifferentialGeometry.CuspTruncation.FiniteCuspTruncation

namespace DifferentialGeometry.OrbifoldThinRegions

open ProjectiveOrthogonalGroup (PO)
open Hyperbolic (HUpper)
open HyperbolicBoundary (BoundaryH poBoundaryMulAction)
open CuspCrossSections (endStabilizer)
open AxisGeometry (quotientAxisDistance quotientAxisRadialFlow axisProductDiffeomorph axisOffCore)

variable (m : ℕ) (Γ : Subgroup (PO (m + 1) 1)) [DiscreteTopology Γ]
  (ξ η : BoundaryH (m + 1)) (hne : ξ ≠ η)

local notation "hn" => Nat.succ_le_succ (Nat.zero_le m)
local notation "P" => endStabilizer hn Γ (Set.insert ξ (Set.singleton η))

omit [DiscreteTopology Γ] in
attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace in
private theorem end_stabilizer_preserves_pair (γ : P) :
    (poBoundaryMulAction hn).smul (γ : PO (m + 1) 1) ξ ∈ ({ξ, η} : Set (BoundaryH (m + 1))) ∧
      (poBoundaryMulAction hn).smul (γ : PO (m + 1) 1) η ∈ ({ξ, η} : Set (BoundaryH (m + 1))) := by
  have he := (ElementaryEnds.mem_setStabilizer hn {ξ, η} γ).mp γ.property.2
  exact ⟨he ▸ Set.mem_image_of_mem _ (by simp), he ▸ Set.mem_image_of_mem _ (by simp)⟩

local notation "hP" => end_stabilizer_preserves_pair m Γ ξ η

private local instance : MulAction Γ (HUpper (m + 1)) := EquivariantMap.subAction hn Γ
private local instance : MulAction P (HUpper (m + 1)) := EquivariantMap.subAction hn P
private local instance : DiscreteTopology P := isDiscrete_iff_discreteTopology.mp
  ((isDiscrete_iff_discreteTopology.mpr (inferInstance : DiscreteTopology Γ)).mono
    (show P ≤ Γ from inf_le_left))
private local instance : ContinuousConstSMul Γ (HUpper (m + 1)) :=
  ⟨fun γ => (HyperbolicAction.contMDiff_po_smul m ∞ (γ : PO (m + 1) 1)).continuous⟩
private local instance : ContinuousConstSMul P (HUpper (m + 1)) :=
  ⟨fun γ => (HyperbolicAction.contMDiff_po_smul m ∞ (γ : PO (m + 1) 1)).continuous⟩
private local instance : ProperlyDiscontinuousSMul Γ (HUpper (m + 1)) :=
  OrbifoldCompactness.properlyDiscontinuous_subAction hn Γ
    (isDiscrete_iff_discreteTopology.mpr inferInstance)
private local instance : ProperlyDiscontinuousSMul P (HUpper (m + 1)) :=
  OrbifoldCompactness.properlyDiscontinuous_subAction hn P
    ((isDiscrete_iff_discreteTopology.mpr (inferInstance : DiscreteTopology Γ)).mono
      (show P ≤ Γ from inf_le_left))

variable [IsCancelSMul Γ (HUpper (m + 1))]

private local instance : IsCancelSMul P (HUpper (m + 1)) :=
  EquivariantMap.isCancelSMul_subAction hn (show P ≤ Γ from inf_le_left)

local notation "I" => 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1)))
local notation "Q" => MulAction.orbitRel.Quotient Γ (HUpper (m + 1))
local notation "QP" => MulAction.orbitRel.Quotient P (HUpper (m + 1))
local notation "π" => Quotient.mk (MulAction.orbitRel Γ (HUpper (m + 1)))
local notation "πP" => Quotient.mk (MulAction.orbitRel P (HUpper (m + 1)))
local notation "R" => quotientAxisDistance m P ξ η hne hP
local notation "S" => {z : QP // R z = Real.arsinh 1}
local notation "O" => axisOffCore m P ξ η hne hP
local notation "K" => 𝓘(ℝ, Fin m → ℝ)
local notation "J" => ModelWithCorners.prod K 𝓘(ℝ, ℝ)
local notation "j" => EquivariantMap.quotientInclusion («P» := P) (Γ := Γ) hn inf_le_left
local notation "d" => axisProductDiffeomorph m P ξ η hne hP
local notation "a" => Function.uncurry (axialGraphAmbientPoint m Γ ξ η hne)

private local instance : ChartedSpace (Fin m → ℝ) S :=
  AxisGeometry.axisSectionChartedSpace m P ξ η hne hP

private local instance : IsManifold K ∞ S := AxisGeometry.axisSection_isManifold m P ξ η hne hP

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace in
private theorem axial_chart_radial_velocity (hm : 1 ≤ m) (r : ℝ) (p : HUpper (m + 1))
    (hp : AxisGeometry.axisFoot ξ η hne p ≠ p)
    (hthin : p ∈ interior (thinRegion hn Γ r {ξ, η})) :
    let r₀ := dist (AxisGeometry.axisFoot ξ η hne p) p
    let A := axialGraphPartialDiffeomorph m Γ ξ η hne hm r
    mfderiv 𝓘(ℝ, ℝ) J (fun t : ℝ => (A).symm (π
      (HyperbolicConvexity.geodFromTo (AxisGeometry.axisFoot ξ η hne p) p hp (r₀ + t / 2))))
      0 (1 : ℝ) = (0, Real.cosh r₀ / (2 * Real.sinh r₀)) := by
  let r₀ := dist (AxisGeometry.axisFoot ξ η hne p) p
  have hr : 0 < r₀ := dist_pos.mpr hp
  have hd : HasDerivAt (fun t : ℝ => Real.log (Real.sinh (r₀ + t / 2)))
      (Real.cosh r₀ / (2 * Real.sinh r₀)) 0 := by
    have hd0 : HasDerivAt (fun t : ℝ => r₀ + t / 2) (1 / 2) 0 :=
      ((hasDerivAt_id (0 : ℝ)).div_const 2).const_add r₀
    have h := hd0.sinh.log
      (by simpa only [zero_div, add_zero] using (Real.sinh_pos_iff.mpr hr).ne')
    simp only [zero_div, add_zero] at h
    have hc : Real.cosh r₀ * (1 / 2) / Real.sinh r₀ = Real.cosh r₀ / (2 * Real.sinh r₀) := by ring
    rwa [hc] at h
  exact mfderiv_eq_vertical_of_eventuallyEq _ _ _ _
    (eventually_axialGraphPartialDiffeomorph_symm_normal_geod_add_half m Γ ξ η hne hm r p hp hthin) hd

end DifferentialGeometry.OrbifoldThinRegions

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace in
private theorem native_chart_symm_apply
    {X Q N W : Type*} [TopologicalSpace X] [TopologicalSpace Q] [TopologicalSpace N]
    (C : OpenPartialHomeomorph X Q) (e : Q ≃ₜ N) (A : OpenPartialHomeomorph X N)
    (hA : A = C.transHomeomorph e) (π : W → Q) (pH : W → N)
    (hrep : ∀ w, e (π w) = pH w) (w : W) : A.symm (pH w) = C.symm (π w) := by
  rw [hA, ← hrep w]
  change C.symm (e.symm (e (π w))) = C.symm (π w)
  rw [e.symm_apply_apply]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace in
private theorem native_chart_mem_target
    {X Q N : Type*} [TopologicalSpace X] [TopologicalSpace Q] [TopologicalSpace N]
    (C : OpenPartialHomeomorph X Q) (e : Q ≃ₜ N) (A : OpenPartialHomeomorph X N)
    (hA : A = C.transHomeomorph e) (q : Q) (hq : q ∈ C.target) : e q ∈ A.target := by
  rw [hA]
  change e.symm (e q) ∈ C.target
  simpa only [e.symm_apply_apply] using hq
end

section
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Hyperbolic

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace in
private theorem graph_of_nonzero_height_derivatives
    {E H M N S T : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace H N]
    [TopologicalSpace S] [ChartedSpace (Fin 2 → ℝ) S] [IsManifold 𝓘(ℝ, Fin 2 → ℝ) ∞ S]
    [CompactSpace S] [PathConnectedSpace S]
    [TopologicalSpace T] [ChartedSpace (Fin 2 → ℝ) T] [IsManifold 𝓘(ℝ, Fin 2 → ℝ) ∞ T]
    [T2Space T] [ConnectedSpace T]
    (Φ : PartialDiffeomorph I I M N ∞)
    (A : PartialDiffeomorph ((𝓘(ℝ, Fin 2 → ℝ)).prod 𝓘(ℝ, ℝ)) I (T × ℝ) N ∞)
    (β : S → M) (hβ : ContMDiff 𝓘(ℝ, Fin 2 → ℝ) I ∞ β)
    (hinj : Function.Injective β)
    (himm : ∀ s, Function.Injective (mfderiv 𝓘(ℝ, Fin 2 → ℝ) I β s))
    (hsource : ∀ s, β s ∈ Φ.source) (htarget : ∀ s, Φ (β s) ∈ A.target)
    (B : M → ℝ) (a : ℝ) (hB : ∀ s, MDifferentiableAt I 𝓘(ℝ, ℝ) B (β s))
    (hlevel : ∀ s, B (β s) = a)
    (hcurves : ∀ s, ∃ (γ : C(ℝ, N)) (b c : ℝ),
      MDifferentiableAt 𝓘(ℝ, ℝ) I γ 0 ∧ γ 0 = Φ (β s) ∧
      HasDerivAt ((B ∘ Φ.symm) ∘ γ) b 0 ∧ b ≠ 0 ∧
      mfderiv 𝓘(ℝ, ℝ) ((𝓘(ℝ, Fin 2 → ℝ)).prod 𝓘(ℝ, ℝ)) (A.symm ∘ γ) 0
        ((NormedSpace.fromTangentSpace (𝕜 := ℝ) (0 : ℝ)).symm 1) = (0, c)) :
    ∃ (η : T ≃ₘ⟮𝓘(ℝ, Fin 2 → ℝ), 𝓘(ℝ, Fin 2 → ℝ)⟯ S) (h : T → ℝ),
      ContMDiff 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, ℝ) ∞ h ∧
      (∀ t, A.symm (Φ (β (η t))) = (t, h t)) ∧
      (∀ t, (t, h t) ∈ A.source) ∧
      (∀ t, Φ (β (η t)) = A (t, h t)) ∧
      Set.range (Φ ∘ β) = Set.range (fun t => A (t, h t)) := by
  let e : S → T × ℝ := A.symm ∘ (Φ ∘ β)
  have hΦ (s : S) : ContMDiffAt I I ∞ (Φ : M → N) (β s) := Φ.contMDiffOn_toFun.contMDiffAt (Φ.open_source.mem_nhds (hsource s))
  have hA (s : S) : ContMDiffAt I ((𝓘(ℝ, Fin 2 → ℝ)).prod 𝓘(ℝ, ℝ)) ∞ (A.symm : N → T × ℝ) (Φ (β s)) := A.contMDiffOn_invFun.contMDiffAt (A.open_target.mem_nhds (htarget s))
  have he : ContMDiff 𝓘(ℝ, Fin 2 → ℝ) ((𝓘(ℝ, Fin 2 → ℝ)).prod 𝓘(ℝ, ℝ)) ∞ e :=
    fun s => (hA s).comp s ((hΦ s).comp s (hβ s))
  have hei : Function.Injective e := by
    intro s t hst
    apply hinj
    apply Φ.injOn (hsource s) (hsource t)
    exact A.symm.injOn (htarget s) (htarget t) hst
  have heim (s : S) : Function.Injective
      (mfderiv 𝓘(ℝ, Fin 2 → ℝ) ((𝓘(ℝ, Fin 2 → ℝ)).prod 𝓘(ℝ, ℝ)) e s) := by
    have hiΦ : Function.Injective (mfderiv I I Φ (β s)) :=
      (Φ.isLocalDiffeomorphAt I I ∞ (hsource s)).mfderivToContinuousLinearEquiv
        (by simp : (∞ : ℕ∞ω) ≠ 0) |>.injective
    have hiA : Function.Injective
        (mfderiv I ((𝓘(ℝ, Fin 2 → ℝ)).prod 𝓘(ℝ, ℝ)) A.symm (Φ (β s))) :=
      (A.symm.isLocalDiffeomorphAt I ((𝓘(ℝ, Fin 2 → ℝ)).prod 𝓘(ℝ, ℝ)) ∞ (htarget s)).mfderivToContinuousLinearEquiv (by simp : (∞ : ℕ∞ω) ≠ 0) |>.injective
    change Function.Injective (mfderiv _ _ (A.symm ∘ (Φ ∘ β)) s)
    rw [mfderiv_comp s ((hA s).mdifferentiableAt (by simp))
      (((hΦ s).comp s (hβ s)).mdifferentiableAt (by simp)),
      mfderiv_comp s ((hΦ s).mdifferentiableAt (by simp)) (hβ.mdifferentiableAt (by simp))]
    exact hiA.comp (hiΦ.comp (himm s))
  have htransverse (s : S) : (0, (1 : ℝ)) ∉
      Set.range (mfderiv 𝓘(ℝ, Fin 2 → ℝ) ((𝓘(ℝ, Fin 2 → ℝ)).prod 𝓘(ℝ, ℝ)) e s) := by
    obtain ⟨γ, b, c, hγ, hγpoint, hder, hb, hvel⟩ := hcurves s
    exact Manifold.vertical_not_mem_range_mfderiv_of_scalar_deriv Φ (by simp) A (by simp)
      (hβ.mdifferentiableAt (by simp)) (hB s) (Filter.Eventually.of_forall hlevel)
      (hsource s) hγ hγpoint (hγpoint.symm ▸ htarget s) hder hb hvel
  obtain ⟨η, h, hs, heq⟩ := Topology.Manifold.exists_diffeomorph_graph_of_transverse_embedding
    e he hei heim rfl htransverse
  have ht (t : T) : (t, h t) ∈ A.source := by
    rw [← heq t]
    exact A.map_target (htarget (η t))
  have hgraph (t : T) : Φ (β (η t)) = A (t, h t) := by
    rw [← heq t]
    exact (A.right_inv (htarget (η t))).symm
  refine ⟨η, h, hs, heq, ht, hgraph, ?_⟩
  ext y
  constructor
  · rintro ⟨s, rfl⟩
    refine ⟨η.symm s, ?_⟩
    simpa only [η.apply_symm_apply, Function.comp_apply] using (hgraph (η.symm s)).symm
  · rintro ⟨t, rfl⟩
    exact ⟨η t, hgraph t⟩

end DifferentialGeometry.Geometry.Hyperbolic
end

section
open scoped Manifold ContDiff Bundle ENNReal Topology
namespace DifferentialGeometry.Geometry.Hyperbolic
open Riemannian.Topology (UniversalCover SemilocallySimplyConnectedSpace
  manifold_semilocallySimplyConnectedSpace)
open ProjectiveOrthogonalGroup (PO)
local notation "E₃" => EuclideanSpace ℝ (Fin 3)
local notation "I₃" => 𝓘(ℝ, E₃)
local notation "K₂" => 𝓘(ℝ, Fin 2 → ℝ)
local notation "J₂" => ModelWithCorners.prod K₂ 𝓘(ℝ, ℝ)
local notation "H₃" => DifferentialGeometry.Hyperbolic.HUpper 3

universe u v
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E₃ H} [I.Boundaryless]
  {M : Type u} {N : Type v} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [T2Space N]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem native_graph_of_radial_curves
    {T : Type*} [TopologicalSpace T] [ChartedSpace (Fin 2 → ℝ) T]
    [IsManifold K₂ ∞ T] [T2Space T] [ConnectedSpace T]
    (g : SmoothRiemannianMetric I M) (hg : RiemannianMetricComplete (I := I) g) (x₀ : M)
    (hsec : ∀ (x : M) (v w : TangentSpace I x),
      Curvature.metricRm04StandardAt g x v w w v =
        (-1 / 4 : ℝ) * (g.inner x v v * g.inner x w w - g.inner x v w * g.inner x v w))
    (gTarget : SmoothRiemannianMetric I N) (Φ : PartialDiffeomorph I I M N ∞)
    (A : PartialDiffeomorph J₂ I (T × ℝ) N ∞)
    {R ε : ℝ} {p : ℕ} (hp : 1 ≤ p) (hR : 2 < R) (hε : ε ≤ 1 / 100) :
    letI : Inhabited M := ⟨x₀⟩
    letI : LocallyPathConnectedSpace H := I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
    letI : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace H M
    letI : SemilocallySimplyConnectedSpace M := manifold_semilocallySimplyConnectedSpace (I := I)
    letI : SecondCountableTopology H := ModelWithCorners.secondCountableTopology I
    letI : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
    let gN := scaleMetric (-(-1 / 4 : ℝ)) (neg_pos.mpr (by norm_num)) g
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
      let pH := normalizedUniversalCoverProjection g hg (-1 / 4) (by norm_num) x₀ hsec i
      let ρ := normalizedUniversalCoverDeckRepresentation g hg (-1 / 4) (by norm_num) x₀ hsec i
      let σ := (Hyperboloid.projectiveOrthogonalGroupEquiv 2 :
        (Hyperboloid E₃ ≃ᵢ Hyperboloid E₃) →* PO 3 1).comp ρ
      ∀ {r : ℝ} (D : CuspTruncation.FiniteCuspTruncation (Nat.le_add_left 1 2) σ.range r)
        (ξ : D.centers),
      let hΓ : IsDiscrete (SetLike.coe σ.range) :=
        (exists_normalizedUniversalCoverThinRegionCharts g hg (-1 / 4) (by norm_num) x₀ hsec i).choose
      let P := CuspCrossSections.endStabilizer (Nat.le_add_left 1 2) σ.range (Set.singleton ξ.val)
      letI := EquivariantMap.subAction (Nat.le_add_left 1 2) σ.range
      letI := EquivariantMap.subAction (Nat.le_add_left 1 2) P
      letI : IsCancelSMul σ.range H₃ :=
        isCancelSMul_projective_range_normalizedUniversalCoverDeckRepresentation g hg (-1 / 4) (by norm_num) x₀ hsec i
      letI : IsCancelSMul P H₃ := EquivariantMap.isCancelSMul_subAction
        (Nat.le_add_left 1 2) (show P ≤ σ.range from inf_le_left)
      let S := (Quotient.mk (MulAction.orbitRel P H₃)) '' Busemann.horosphere ξ.val (D.level ξ)
      letI : ChartedSpace (Fin 2 → ℝ) S := D.horosphereQuotientChartedSpace hΓ ξ
      ∀ (d : ℝ) (hd : 0 < d),
      let β : S → M := fun s => normalizedUniversalCoverCuspCylinderMap
        g hg (-1 / 4) (by norm_num) x₀ hsec i D ξ (s, ⟨d, hd.le⟩)
      ∀ (B : M → ℝ),
      (∀ z : H₃, Busemann.busemann ξ.val z < D.level ξ → B (pH z) = 2 * Busemann.busemann ξ.val z) →
      (∀ s, PartialDiffeomorph.isMetricApproximationOn Φ (riemannianClosedBallOf g (β s) R) p ε g gTarget) →
      (∀ s, riemannianClosedBallOf g (β s) 2 ⊆ pH '' {z : H₃ | Busemann.busemann ξ.val z < D.level ξ}) →
      Metric.ediam (pH '' Busemann.horosphere ξ.val (D.level ξ - d)) ≤ ENNReal.ofReal (1 / 10) →
      (∀ s, Φ (β s) ∈ A.target) →
      (∀ s, ∃ (γ : C(ℝ, N)) (c : ℝ),
        ContMDiff 𝓘(ℝ, ℝ) I ∞ γ ∧
        Riemannian.Geodesic.IsGeodesicOn gTarget γ (Set.Icc (0 : ℝ) 1) ∧
        (∀ t ∈ Set.Icc (0 : ℝ) 1,
          gTarget.inner (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t 1) (mfderiv 𝓘(ℝ, ℝ) I γ t 1) = 1) ∧
        Set.MapsTo γ (Set.Icc (0 : ℝ) 1) (riemannianClosedBallOf gTarget (Φ (β s)) 1) ∧
        γ 0 = Φ (β s) ∧ ENNReal.ofReal 1 ≤ riemannianEDistOf gTarget (γ 0) (γ 1) ∧
        mfderiv 𝓘(ℝ, ℝ) J₂ (A.symm ∘ γ) 0
          ((NormedSpace.fromTangentSpace (𝕜 := ℝ) (0 : ℝ)).symm 1) = (0, c)) →
      ∃ (η : T ≃ₘ⟮K₂, K₂⟯ S) (h : T → ℝ), ContMDiff K₂ 𝓘(ℝ, ℝ) ∞ h ∧
        (∀ t, A.symm (Φ (β (η t))) = (t, h t)) ∧
        (∀ t, (t, h t) ∈ A.source) ∧
        (∀ t, Φ (β (η t)) = A (t, h t)) ∧
        Set.range (Φ ∘ β) = Set.range (fun t => A (t, h t)) := by
  let _ : Inhabited M := ⟨x₀⟩
  let _ : LocallyPathConnectedSpace H := I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  let _ : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace H M
  let _ : SemilocallySimplyConnectedSpace M := manifold_semilocallySimplyConnectedSpace (I := I)
  let _ : SecondCountableTopology H := ModelWithCorners.secondCountableTopology I
  let _ : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
  let gN := scaleMetric (-(-1 / 4 : ℝ)) (neg_pos.mpr (by norm_num)) g
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
  intro r D ξ
  let ρ := normalizedUniversalCoverDeckRepresentation g hg (-1 / 4) (by norm_num) x₀ hsec i
  let σ := (Hyperboloid.projectiveOrthogonalGroupEquiv 2 :
    (Hyperboloid E₃ ≃ᵢ Hyperboloid E₃) →* PO 3 1).comp ρ
  let hΓ : IsDiscrete (SetLike.coe σ.range) :=
    (exists_normalizedUniversalCoverThinRegionCharts g hg (-1 / 4) (by norm_num) x₀ hsec i).choose
  let P := CuspCrossSections.endStabilizer (Nat.le_add_left 1 2) σ.range (Set.singleton ξ.val)
  let := EquivariantMap.subAction (Nat.le_add_left 1 2) σ.range
  let := EquivariantMap.subAction (Nat.le_add_left 1 2) P
  let : DiscreteTopology σ.range := isDiscrete_iff_discreteTopology.mp hΓ
  let : IsCancelSMul σ.range H₃ :=
    isCancelSMul_projective_range_normalizedUniversalCoverDeckRepresentation g hg (-1 / 4) (by norm_num) x₀ hsec i
  let : IsCancelSMul P H₃ := EquivariantMap.isCancelSMul_subAction
    (Nat.le_add_left 1 2) (show P ≤ σ.range from inf_le_left)
  let : ContinuousConstSMul σ.range H₃ :=
    ⟨fun a => (HyperbolicAction.contMDiff_po_smul 2 ∞ (a : PO 3 1)).continuous⟩
  let : ContMDiffConstSMul I₃ ∞ σ.range H₃ :=
    ⟨fun a => HyperbolicAction.contMDiff_po_smul 2 ∞ (a : PO 3 1)⟩
  let : ProperlyDiscontinuousSMul σ.range H₃ :=
    OrbifoldCompactness.properlyDiscontinuous_subAction (Nat.le_add_left 1 2) σ.range hΓ
  let S := (Quotient.mk (MulAction.orbitRel P H₃)) '' Busemann.horosphere ξ.val (D.level ξ)
  let : ChartedSpace (Fin 2 → ℝ) S := D.horosphereQuotientChartedSpace hΓ ξ
  intro d hd
  let β : S → M := fun s => normalizedUniversalCoverCuspCylinderMap
    g hg (-1 / 4) (by norm_num) x₀ hsec i D ξ (s, ⟨d, hd.le⟩)
  let pH := normalizedUniversalCoverProjection g hg (-1 / 4) (by norm_num) x₀ hsec i
  intro B htie hΦ hcollar hdiam htarget hcurves
  have hgeom := native_slice_geometry g hg (-1 / 4) (by norm_num) x₀ hsec i D ξ ⟨d, hd.le⟩
  let _ : CompactSpace S := hgeom.1
  let _ : PathConnectedSpace S := hgeom.2.1
  let _ : IsManifold K₂ ∞ S := D.isManifold_quotient_horosphere hΓ ξ
  have hlevel (s : S) : B (β s) = 2 * (D.level ξ - d) := by
    obtain ⟨s, z, hz, rfl⟩ := s
    have hzlevel : Busemann.busemann ξ.val z = D.level ξ := hz
    have hin : Busemann.busemann ξ.val (AsymptoticRays.rayTo z ξ.val d) < D.level ξ := by
      rw [HorosphereProjection.busemann_rayTo, hzlevel]
      linarith
    rw [show β ⟨_, z, hz, rfl⟩ = pH (AsymptoticRays.rayTo z ξ.val d) from
      normalizedUniversalCoverCuspCylinderMap_apply_mk g hg (-1 / 4) (by norm_num) x₀ hsec i D ξ z hz ⟨d,hd.le⟩,
      htie _ hin, HorosphereProjection.busemann_rayTo, hzlevel]
  have hsource (s : S) : β s ∈ Φ.source := by
    apply (hΦ s).1
    change riemannianEDistOf g (β s) (β s) ≤ ENNReal.ofReal R
    rw [riemannianEDistOf_self]
    exact zero_le
  have hinside (s : S) : β s ∈ pH '' {z : H₃ | Busemann.busemann ξ.val z < D.level ξ} := by
    apply hcollar s
    change riemannianEDistOf g (β s) (β s) ≤ ENNReal.ofReal 2
    rw [riemannianEDistOf_self]
    exact zero_le
  have hopen : IsOpen (pH '' {z : H₃ | Busemann.busemann ξ.val z < D.level ξ}) :=
    (normalizedUniversalCoverProjection_isLocalDiffeomorph g hg (-1 / 4) (by norm_num) x₀ hsec i).isOpenMap
      _ (isOpen_lt (Busemann.contMDiff_busemann ξ.val ∞).continuous continuous_const)
  have hBsmooth := contMDiffOn_height_of_normalizedUniversalCoverProjection_eq
    g hg (-1 / 4) (by norm_num) x₀ hsec i ξ.val (D.level ξ) B htie
  have hB (s : S) : MDifferentiableAt I 𝓘(ℝ, ℝ) B (β s) :=
    (hBsmooth.contMDiffAt (hopen.mem_nhds (hinside s))).mdifferentiableAt (by simp)
  apply graph_of_nonzero_height_derivatives Φ A β hgeom.2.2.1 hgeom.2.2.2.1 hgeom.2.2.2.2
    hsource htarget B (2 * (D.level ξ - d)) hB hlevel
  intro s
  obtain ⟨γ, c, hγ, hgeo, hunit, hcap, hpoint, hsep, hvel⟩ := hcurves s
  have hInv : ContMDiffAt I I ∞ (Φ.symm : N → M) (γ 0) := by
    apply Φ.contMDiffOn_invFun.contMDiffAt
    apply Φ.open_target.mem_nhds
    rw [hpoint]
    exact Φ.map_source (hsource s)
  have heq : Φ.symm (γ 0) = β s := hpoint ▸ Φ.left_inv (hsource s)
  have hcomp : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ((B ∘ Φ.symm) ∘ γ) 0 :=
    ((heq.symm ▸ hB s).comp (γ 0) (hInv.mdifferentiableAt (by simp))).comp 0
      (hγ.mdifferentiableAt (by simp))
  have hdiff : DifferentiableAt ℝ ((B ∘ Φ.symm) ∘ γ) 0 :=
    mdifferentiableAt_iff_differentiableAt.mp hcomp
  refine ⟨γ, deriv ((B ∘ Φ.symm) ∘ γ) 0, c, hγ.mdifferentiableAt (by simp), hpoint,
    hdiff.hasDerivAt, ?_, hvel⟩
  have hdlev : B (β s) / 2 = D.level ξ - d := by rw [hlevel]; ring
  apply deriv_height_ne_zero_of_captured_geodesic_in_cusp g hg x₀ hsec gTarget Φ (β s)
    hp (by simpa using hR) hε (hΦ s) γ (fun t _ => hγ t) hgeo hunit hcap B hpoint hsep i D ξ
  · simpa only [mul_one] using hcollar s
  · exact htie
  · simpa only [hdlev] using hdiam

end DifferentialGeometry.Geometry.Hyperbolic
end

section
open scoped Manifold ContDiff Bundle ENNReal Topology
namespace DifferentialGeometry.Geometry.Hyperbolic
open Riemannian.Topology (UniversalCover SemilocallySimplyConnectedSpace
  manifold_semilocallySimplyConnectedSpace)
open ProjectiveOrthogonalGroup (PO)
local notation "E₃" => EuclideanSpace ℝ (Fin 3)
local notation "I₃" => 𝓘(ℝ, E₃)
local notation "K₂" => 𝓘(ℝ, Fin 2 → ℝ)
local notation "J₂" => ModelWithCorners.prod K₂ 𝓘(ℝ, ℝ)
local notation "H₃" => DifferentialGeometry.Hyperbolic.HUpper 3

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E₃ H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem native_cusp_chart_radial_curves
    {X : Type*} (g : SmoothRiemannianMetric I M) (hg : RiemannianMetricComplete (I := I) g) (x₀ : M)
    (hsec : ∀ (x : M) (v w : TangentSpace I x),
      Curvature.metricRm04StandardAt g x v w w v =
        (-1 / 4 : ℝ) * (g.inner x v v * g.inner x w w - g.inner x v w * g.inner x v w)) :
    letI : Inhabited M := ⟨x₀⟩
    letI : LocallyPathConnectedSpace H := I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
    letI : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace H M
    letI : SemilocallySimplyConnectedSpace M := manifold_semilocallySimplyConnectedSpace (I := I)
    letI : SecondCountableTopology H := ModelWithCorners.secondCountableTopology I
    letI : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
    let gN := scaleMetric (-(-1 / 4 : ℝ)) (neg_pos.mpr (by norm_num)) g
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
      let ρ := normalizedUniversalCoverDeckRepresentation g hg (-1 / 4) (by norm_num) x₀ hsec i
      let σ := (Hyperboloid.projectiveOrthogonalGroupEquiv 2 :
        (Hyperboloid E₃ ≃ᵢ Hyperboloid E₃) →* PO 3 1).comp ρ
      ∀ {r : ℝ} (D : CuspTruncation.FiniteCuspTruncation (Nat.le_add_left 1 2) σ.range r)
        (ξ : D.centers),
      let hΓ : IsDiscrete (SetLike.coe σ.range) :=
        (exists_normalizedUniversalCoverThinRegionCharts g hg (-1 / 4) (by norm_num) x₀ hsec i).choose
      let P := CuspCrossSections.endStabilizer (Nat.le_add_left 1 2) σ.range (Set.singleton ξ.val)
      letI := EquivariantMap.subAction (Nat.le_add_left 1 2) σ.range
      letI := EquivariantMap.subAction (Nat.le_add_left 1 2) P
      letI : IsCancelSMul σ.range H₃ :=
        isCancelSMul_projective_range_normalizedUniversalCoverDeckRepresentation g hg (-1 / 4) (by norm_num) x₀ hsec i
      letI : IsCancelSMul P H₃ := EquivariantMap.isCancelSMul_subAction
        (Nat.le_add_left 1 2) (show P ≤ σ.range from inf_le_left)
      let S := (Quotient.mk (MulAction.orbitRel P H₃)) '' Busemann.horosphere ξ.val (D.level ξ)
      letI : ChartedSpace (Fin 2 → ℝ) S := D.horosphereQuotientChartedSpace hΓ ξ
      let pH := normalizedUniversalCoverProjection g hg (-1 / 4) (by norm_num) x₀ hsec i
      let e := normalizedUniversalCoverProjectiveQuotientHomeomorph g hg (-1 / 4) (by norm_num) x₀ hsec i
      ∀ f : X → M,
      (∀ x, riemannianBallOf g (f x) 2 ⊆
        pH '' interior (OrbifoldThinRegions.thinRegion (Nat.le_add_left 1 2) σ.range r {ξ.val})) →
      ∃ A : PartialDiffeomorph J₂ I (S × ℝ) M ∞,
        A.toOpenPartialHomeomorph = (D.horosphereGraphChart hΓ ξ).transHomeomorph e ∧
        (∀ x, f x ∈ A.target) ∧
        ∀ x, ∃ (γ : C(ℝ, M)) (c : ℝ),
          ContMDiff 𝓘(ℝ, ℝ) I ∞ γ ∧
          Riemannian.Geodesic.IsGeodesicOn g γ (Set.Icc (0 : ℝ) 1) ∧
          (∀ t ∈ Set.Icc (0 : ℝ) 1,
            g.inner (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t 1) (mfderiv 𝓘(ℝ, ℝ) I γ t 1) = 1) ∧
          Set.MapsTo γ (Set.Icc (0 : ℝ) 1) (riemannianClosedBallOf g (f x) 1) ∧
          γ 0 = f x ∧ ENNReal.ofReal 1 ≤ riemannianEDistOf g (γ 0) (γ 1) ∧
          mfderiv 𝓘(ℝ, ℝ) J₂ (A.symm ∘ γ) 0
            ((NormedSpace.fromTangentSpace (𝕜 := ℝ) (0 : ℝ)).symm 1) = (0, c) := by
  let _ : Inhabited M := ⟨x₀⟩
  let _ : LocallyPathConnectedSpace H := I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  let _ : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace H M
  let _ : SemilocallySimplyConnectedSpace M := manifold_semilocallySimplyConnectedSpace (I := I)
  let _ : SecondCountableTopology H := ModelWithCorners.secondCountableTopology I
  let _ : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
  let gN := scaleMetric (-(-1 / 4 : ℝ)) (neg_pos.mpr (by norm_num)) g
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
  let ρ := normalizedUniversalCoverDeckRepresentation g hg (-1 / 4) (by norm_num) x₀ hsec i
  let σ := (Hyperboloid.projectiveOrthogonalGroupEquiv 2 :
    (Hyperboloid E₃ ≃ᵢ Hyperboloid E₃) →* PO 3 1).comp ρ
  let hΓ : IsDiscrete (SetLike.coe σ.range) :=
    (exists_normalizedUniversalCoverThinRegionCharts g hg (-1 / 4) (by norm_num) x₀ hsec i).choose
  let P := CuspCrossSections.endStabilizer (Nat.le_add_left 1 2) σ.range (Set.singleton ξ.val)
  let := EquivariantMap.subAction (Nat.le_add_left 1 2) σ.range
  let := EquivariantMap.subAction (Nat.le_add_left 1 2) P
  let : DiscreteTopology σ.range := isDiscrete_iff_discreteTopology.mp hΓ
  let : IsCancelSMul σ.range H₃ :=
    isCancelSMul_projective_range_normalizedUniversalCoverDeckRepresentation g hg (-1 / 4) (by norm_num) x₀ hsec i
  let : IsCancelSMul P H₃ := EquivariantMap.isCancelSMul_subAction
    (Nat.le_add_left 1 2) (show P ≤ σ.range from inf_le_left)
  let : ContinuousConstSMul σ.range H₃ :=
    ⟨fun a => (HyperbolicAction.contMDiff_po_smul 2 ∞ (a : PO 3 1)).continuous⟩
  let : ContMDiffConstSMul I₃ ∞ σ.range H₃ :=
    ⟨fun a => HyperbolicAction.contMDiff_po_smul 2 ∞ (a : PO 3 1)⟩
  let : ProperlyDiscontinuousSMul σ.range H₃ :=
    OrbifoldCompactness.properlyDiscontinuous_subAction (Nat.le_add_left 1 2) σ.range hΓ
  let S := (Quotient.mk (MulAction.orbitRel P H₃)) '' Busemann.horosphere ξ.val (D.level ξ)
  let : ChartedSpace (Fin 2 → ℝ) S := D.horosphereQuotientChartedSpace hΓ ξ
  let pH := normalizedUniversalCoverProjection g hg (-1 / 4) (by norm_num) x₀ hsec i
  let e := normalizedUniversalCoverProjectiveQuotientHomeomorph g hg (-1 / 4) (by norm_num) x₀ hsec i
  let πG := Quotient.mk (MulAction.orbitRel σ.range H₃)
  have hrep (y : H₃) : e (πG y) = pH y :=
    normalizedUniversalCoverProjectiveQuotientHomeomorph_apply_mk g hg (-1 / 4) (by norm_num) x₀ hsec i y
  intro f hball
  have hex : ∃ A : PartialDiffeomorph J₂ I (S × ℝ) M ∞,
      A.toOpenPartialHomeomorph = (D.horosphereGraphChart hΓ ξ).transHomeomorph e :=
    (exists_normalizedUniversalCoverThinRegionCharts
      g hg (-1 / 4) (by norm_num) x₀ hsec i).choose_spec.1 D ξ
  obtain ⟨A, hA⟩ := hex
  have hrepPoint (x : X) : ∃ y : H₃,
      y ∈ interior (OrbifoldThinRegions.thinRegion (Nat.le_add_left 1 2) σ.range r {ξ.val}) ∧ pH y = f x := by
    apply hball x
    change riemannianEDistOf g (f x) (f x) < ENNReal.ofReal 2
    rw [riemannianEDistOf_self]
    norm_num
  have htarget (x : X) : f x ∈ A.target := by
    obtain ⟨y, hy, hpoint⟩ := hrepPoint x
    have hyt : πG y ∈ (D.horosphereGraphChart hΓ ξ).target := by
      rw [D.horosphereGraphChart_target]
      exact ⟨y, hy, rfl⟩
    have hmem : e (πG y) ∈ A.target :=
      native_chart_mem_target _ e A.toOpenPartialHomeomorph hA _ hyt
    exact (congrArg (fun z => z ∈ A.target) ((hrep y).trans hpoint)).mp hmem
  refine ⟨A, hA, htarget, ?_⟩
  intro x
  let y : H₃ := (hrepPoint x).choose
  have hy : y ∈ interior (OrbifoldThinRegions.thinRegion
      (Nat.le_add_left 1 2) σ.range r {ξ.val}) := (hrepPoint x).choose_spec.1
  have hpoint : pH y = f x := (hrepPoint x).choose_spec.2
  have hrad := normalizedUniversalCoverProjection_outward_ray g hg x₀ hsec i y ξ.val
  let γ : C(ℝ, M) := ⟨fun t => pH (AsymptoticRays.rayTo y ξ.val (-t / 2)), hrad.2.1.continuous⟩
  have hzero : γ 0 = pH y := hrad.1
  have hcap : Set.MapsTo γ (Set.Icc (0 : ℝ) 1) (riemannianClosedBallOf g (f x) 1) := by
    rw [← hpoint]
    exact hrad.2.2.2.2.2.1
  have hball' : riemannianBallOf g (pH y) 2 ⊆
      pH '' interior (OrbifoldThinRegions.thinRegion (Nat.le_add_left 1 2) σ.range r {ξ.val}) :=
    hpoint.symm ▸ hball x
  have hsep : ENNReal.ofReal 1 ≤ riemannianEDistOf g (γ 0) (γ 1) := by
    rw [hzero]
    exact cusp_radial_endpoint_separated g hg x₀ hsec i D ξ y hy hball'
  refine ⟨γ, 1 / 2, hrad.2.1, hrad.2.2.1.isGeodesicOn _,
    fun t _ => hrad.2.2.2.1 t, hcap, hzero.trans hpoint, hsep, ?_⟩
  have heq : A.symm ∘ γ = fun t : ℝ => (D.horosphereGraphChart hΓ ξ).symm
      (πG (AsymptoticRays.rayTo y ξ.val (-t / 2))) := by
    funext t
    exact native_chart_symm_apply _ e A.toOpenPartialHomeomorph hA πG pH hrep _
  have hvel := CuspTruncation.FiniteCuspTruncation.cusp_chart_radial_velocity D ξ y hy
  exact (congrArg (fun f : ℝ → S × ℝ =>
    (mfderiv 𝓘(ℝ, ℝ) J₂ f 0 (1 : ℝ) : (Fin 2 → ℝ) × ℝ)) heq).trans hvel

end DifferentialGeometry.Geometry.Hyperbolic
end

section
open scoped Manifold ContDiff Bundle ENNReal Topology
namespace DifferentialGeometry.Geometry.Hyperbolic
open Riemannian.Topology (UniversalCover SemilocallySimplyConnectedSpace
  manifold_semilocallySimplyConnectedSpace)
open ProjectiveOrthogonalGroup (PO)
local notation "E₃" => EuclideanSpace ℝ (Fin 3)
local notation "I₃" => 𝓘(ℝ, E₃)
local notation "K₂" => 𝓘(ℝ, Fin 2 → ℝ)
local notation "J₂" => ModelWithCorners.prod K₂ 𝓘(ℝ, ℝ)
local notation "H₃" => DifferentialGeometry.Hyperbolic.HUpper 3

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E₃ H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem native_axial_chart_radial_curves
    {X : Type*} (g : SmoothRiemannianMetric I M) (hg : RiemannianMetricComplete (I := I) g) (x₀ : M)
    (hsec : ∀ (x : M) (v w : TangentSpace I x),
      Curvature.metricRm04StandardAt g x v w w v =
        (-1 / 4 : ℝ) * (g.inner x v v * g.inner x w w - g.inner x v w * g.inner x v w)) :
    letI : Inhabited M := ⟨x₀⟩
    letI : LocallyPathConnectedSpace H := I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
    letI : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace H M
    letI : SemilocallySimplyConnectedSpace M := manifold_semilocallySimplyConnectedSpace (I := I)
    letI : SecondCountableTopology H := ModelWithCorners.secondCountableTopology I
    letI : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
    let gN := scaleMetric (-(-1 / 4 : ℝ)) (neg_pos.mpr (by norm_num)) g
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
      let ρ := normalizedUniversalCoverDeckRepresentation g hg (-1 / 4) (by norm_num) x₀ hsec i
      let σ := (Hyperboloid.projectiveOrthogonalGroupEquiv 2 :
        (Hyperboloid E₃ ≃ᵢ Hyperboloid E₃) →* PO 3 1).comp ρ
      ∀ (ξ η : HyperbolicBoundary.BoundaryH 3) (hne : ξ ≠ η) (r : ℝ),
      let hΓ : IsDiscrete (SetLike.coe σ.range) :=
        (exists_normalizedUniversalCoverThinRegionCharts g hg (-1 / 4) (by norm_num) x₀ hsec i).choose
      letI : DiscreteTopology σ.range := isDiscrete_iff_discreteTopology.mp hΓ
      let P := CuspCrossSections.endStabilizer (Nat.le_add_left 1 2) σ.range ({ξ, η})
      letI := EquivariantMap.subAction (Nat.le_add_left 1 2) σ.range
      letI := EquivariantMap.subAction (Nat.le_add_left 1 2) P
      letI : IsCancelSMul σ.range H₃ :=
        isCancelSMul_projective_range_normalizedUniversalCoverDeckRepresentation g hg (-1 / 4) (by norm_num) x₀ hsec i
      letI : IsCancelSMul P H₃ := EquivariantMap.isCancelSMul_subAction
        (Nat.le_add_left 1 2) (show P ≤ σ.range from inf_le_left)
      letI : DiscreteTopology P := isDiscrete_iff_discreteTopology.mp
        (hΓ.mono (show P ≤ σ.range from inf_le_left))
      let hpair := OrbifoldThinRegions.end_stabilizer_preserves_pair 2 σ.range ξ η
      let S := {q : MulAction.orbitRel.Quotient P H₃ //
        AxisGeometry.quotientAxisDistance 2 P ξ η hne hpair q = Real.arsinh 1}
      letI : ChartedSpace (Fin 2 → ℝ) S := AxisGeometry.axisSectionChartedSpace 2 P ξ η hne hpair
      let pH := normalizedUniversalCoverProjection g hg (-1 / 4) (by norm_num) x₀ hsec i
      let e := normalizedUniversalCoverProjectiveQuotientHomeomorph g hg (-1 / 4) (by norm_num) x₀ hsec i
      ∀ f : X → M,
      (∀ x, riemannianBallOf g (f x) 2 ⊆
        pH '' interior (OrbifoldThinRegions.thinRegion (Nat.le_add_left 1 2) σ.range r {ξ, η})) →
      (∀ x, f x ∉ pH '' (AxisGeometry.axis ξ η ∩
        OrbifoldThinRegions.thinRegion (Nat.le_add_left 1 2) σ.range r {ξ, η})) →
      ∃ A : PartialDiffeomorph J₂ I (S × ℝ) M ∞,
        A.toOpenPartialHomeomorph = (OrbifoldThinRegions.axialGraphChart 2 σ.range ξ η hne (by decide) r).transHomeomorph e ∧
        (∀ x, f x ∈ A.target) ∧
        ∀ x, ∃ (γ : C(ℝ, M)) (c : ℝ),
          ContMDiff 𝓘(ℝ, ℝ) I ∞ γ ∧
          Riemannian.Geodesic.IsGeodesicOn g γ (Set.Icc (0 : ℝ) 1) ∧
          (∀ t ∈ Set.Icc (0 : ℝ) 1,
            g.inner (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t 1) (mfderiv 𝓘(ℝ, ℝ) I γ t 1) = 1) ∧
          Set.MapsTo γ (Set.Icc (0 : ℝ) 1) (riemannianClosedBallOf g (f x) 1) ∧
          γ 0 = f x ∧ ENNReal.ofReal 1 ≤ riemannianEDistOf g (γ 0) (γ 1) ∧
          mfderiv 𝓘(ℝ, ℝ) J₂ (A.symm ∘ γ) 0
            ((NormedSpace.fromTangentSpace (𝕜 := ℝ) (0 : ℝ)).symm 1) = (0, c) := by
  let _ : Inhabited M := ⟨x₀⟩
  let _ : LocallyPathConnectedSpace H := I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  let _ : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace H M
  let _ : SemilocallySimplyConnectedSpace M := manifold_semilocallySimplyConnectedSpace (I := I)
  let _ : SecondCountableTopology H := ModelWithCorners.secondCountableTopology I
  let _ : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
  let gN := scaleMetric (-(-1 / 4 : ℝ)) (neg_pos.mpr (by norm_num)) g
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
  intro i ξ η hne r
  let ρ := normalizedUniversalCoverDeckRepresentation g hg (-1 / 4) (by norm_num) x₀ hsec i
  let σ := (Hyperboloid.projectiveOrthogonalGroupEquiv 2 :
    (Hyperboloid E₃ ≃ᵢ Hyperboloid E₃) →* PO 3 1).comp ρ
  let hΓ : IsDiscrete (SetLike.coe σ.range) :=
    (exists_normalizedUniversalCoverThinRegionCharts g hg (-1 / 4) (by norm_num) x₀ hsec i).choose
  let P := CuspCrossSections.endStabilizer (Nat.le_add_left 1 2) σ.range ({ξ, η})
  let := EquivariantMap.subAction (Nat.le_add_left 1 2) σ.range
  let := EquivariantMap.subAction (Nat.le_add_left 1 2) P
  let : DiscreteTopology σ.range := isDiscrete_iff_discreteTopology.mp hΓ
  let : IsCancelSMul σ.range H₃ :=
    isCancelSMul_projective_range_normalizedUniversalCoverDeckRepresentation g hg (-1 / 4) (by norm_num) x₀ hsec i
  let : IsCancelSMul P H₃ := EquivariantMap.isCancelSMul_subAction
    (Nat.le_add_left 1 2) (show P ≤ σ.range from inf_le_left)
  let : ContinuousConstSMul σ.range H₃ :=
    ⟨fun a => (HyperbolicAction.contMDiff_po_smul 2 ∞ (a : PO 3 1)).continuous⟩
  let : ContMDiffConstSMul I₃ ∞ σ.range H₃ :=
    ⟨fun a => HyperbolicAction.contMDiff_po_smul 2 ∞ (a : PO 3 1)⟩
  let : ProperlyDiscontinuousSMul σ.range H₃ :=
    OrbifoldCompactness.properlyDiscontinuous_subAction (Nat.le_add_left 1 2) σ.range hΓ
  let : DiscreteTopology P := isDiscrete_iff_discreteTopology.mp
    (hΓ.mono (show P ≤ σ.range from inf_le_left))
  let hpair := OrbifoldThinRegions.end_stabilizer_preserves_pair 2 σ.range ξ η
  let S := {q : MulAction.orbitRel.Quotient P H₃ //
    AxisGeometry.quotientAxisDistance 2 P ξ η hne hpair q = Real.arsinh 1}
  let : ChartedSpace (Fin 2 → ℝ) S := AxisGeometry.axisSectionChartedSpace 2 P ξ η hne hpair
  let pH := normalizedUniversalCoverProjection g hg (-1 / 4) (by norm_num) x₀ hsec i
  let e := normalizedUniversalCoverProjectiveQuotientHomeomorph g hg (-1 / 4) (by norm_num) x₀ hsec i
  let πG := Quotient.mk (MulAction.orbitRel σ.range H₃)
  have hrep (y : H₃) : e (πG y) = pH y :=
    normalizedUniversalCoverProjectiveQuotientHomeomorph_apply_mk g hg (-1 / 4) (by norm_num) x₀ hsec i y
  intro f hball hoff
  have hex : ∃ A : PartialDiffeomorph J₂ I (S × ℝ) M ∞,
      A.toOpenPartialHomeomorph = (OrbifoldThinRegions.axialGraphChart 2 σ.range ξ η hne (by decide) r).transHomeomorph e :=
    (exists_normalizedUniversalCoverThinRegionCharts
      g hg (-1 / 4) (by norm_num) x₀ hsec i).choose_spec.2 ξ η hne r
  obtain ⟨A, hA⟩ := hex
  have hrepPoint (x : X) : ∃ y : H₃,
      y ∈ interior (OrbifoldThinRegions.thinRegion (Nat.le_add_left 1 2) σ.range r {ξ, η}) ∧ pH y = f x := by
    apply hball x
    change riemannianEDistOf g (f x) (f x) < ENNReal.ofReal 2
    rw [riemannianEDistOf_self]
    norm_num
  have htarget (x : X) : f x ∈ A.target := by
    obtain ⟨y, hy, hpoint⟩ := hrepPoint x
    have hyoff : y ∉ AxisGeometry.axis ξ η := by
      intro ha
      exact hoff x ⟨y, ⟨ha, interior_subset hy⟩, hpoint⟩
    have hyt : πG y ∈ (OrbifoldThinRegions.axialGraphChart 2 σ.range ξ η hne (by decide) r).target := by
      rw [OrbifoldThinRegions.axialGraphChart_target]
      exact ⟨y, ⟨hyoff, hy⟩, rfl⟩
    have hmem : e (πG y) ∈ A.target :=
      native_chart_mem_target _ e A.toOpenPartialHomeomorph hA _ hyt
    exact (congrArg (fun z => z ∈ A.target) ((hrep y).trans hpoint)).mp hmem
  refine ⟨A, hA, htarget, ?_⟩
  intro x
  let y : H₃ := (hrepPoint x).choose
  have hy : y ∈ interior (OrbifoldThinRegions.thinRegion
      (Nat.le_add_left 1 2) σ.range r {ξ, η}) := (hrepPoint x).choose_spec.1
  have hpoint : pH y = f x := (hrepPoint x).choose_spec.2
  have hyoff : y ∉ AxisGeometry.axis ξ η := by
    intro ha
    exact hoff x ⟨y, ⟨ha, interior_subset hy⟩, hpoint⟩
  have hfoot : AxisGeometry.axisFoot ξ η hne y ≠ y :=
    fun he => hyoff (he ▸ AxisGeometry.axisFoot_mem ξ η hne y)
  let r₀ := dist (AxisGeometry.axisFoot ξ η hne y) y
  have hrad := normalizedUniversalCoverProjection_outward_normal_geodesic g hg x₀ hsec i ξ η hne y hfoot
  let γ : C(ℝ, M) := ⟨fun t => pH (HyperbolicConvexity.geodFromTo (AxisGeometry.axisFoot ξ η hne y) y hfoot (r₀ + t / 2)), hrad.2.1.continuous⟩
  have hzero : γ 0 = pH y := hrad.1
  have hcap : Set.MapsTo γ (Set.Icc (0 : ℝ) 1) (riemannianClosedBallOf g (f x) 1) := by
    rw [← hpoint]
    exact hrad.2.2.2.2.2.1
  have hball' : riemannianBallOf g (pH y) 2 ⊆
      pH '' interior (OrbifoldThinRegions.thinRegion (Nat.le_add_left 1 2) σ.range r {ξ, η}) :=
    hpoint.symm ▸ hball x
  have hsep : ENNReal.ofReal 1 ≤ riemannianEDistOf g (γ 0) (γ 1) := by
    rw [hzero]
    exact axial_radial_endpoint_separated g hg x₀ hsec i r ξ η hne y hfoot hy hball'
  refine ⟨γ, Real.cosh r₀ / (2 * Real.sinh r₀), hrad.2.1, hrad.2.2.1.isGeodesicOn _,
    fun t _ => hrad.2.2.2.1 t, hcap, hzero.trans hpoint, hsep, ?_⟩
  have heq : A.symm ∘ γ = fun t : ℝ => (OrbifoldThinRegions.axialGraphChart 2 σ.range ξ η hne (by decide) r).symm
      (πG (HyperbolicConvexity.geodFromTo (AxisGeometry.axisFoot ξ η hne y) y hfoot (r₀ + t / 2))) := by
    funext t
    exact native_chart_symm_apply _ e A.toOpenPartialHomeomorph hA πG pH hrep _
  have hvel := OrbifoldThinRegions.axial_chart_radial_velocity 2 σ.range ξ η hne (by decide) r y hfoot hy
  exact (congrArg (fun f : ℝ → S × ℝ =>
    (mfderiv 𝓘(ℝ, ℝ) J₂ f 0 (1 : ℝ) : (Fin 2 → ℝ) × ℝ)) heq).trans hvel

end DifferentialGeometry.Geometry.Hyperbolic
end

section
open scoped Manifold ContDiff Bundle ENNReal Topology
namespace DifferentialGeometry.Geometry.Hyperbolic
open Riemannian.Topology (UniversalCover SemilocallySimplyConnectedSpace
  manifold_semilocallySimplyConnectedSpace)
open ProjectiveOrthogonalGroup (PO)
local notation "E₃" => EuclideanSpace ℝ (Fin 3)
local notation "I₃" => 𝓘(ℝ, E₃)
local notation "K₂" => 𝓘(ℝ, Fin 2 → ℝ)
local notation "J₂" => ModelWithCorners.prod K₂ 𝓘(ℝ, ℝ)
local notation "H₃" => DifferentialGeometry.Hyperbolic.HUpper 3

universe u v
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E₃ H} [I.Boundaryless]
  {M : Type u} {N : Type v} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [T2Space N] [SigmaCompactSpace N] [ConnectedSpace N]

private theorem quarter_curvature_neg : (-1 / 4 : ℝ) < 0 := by norm_num

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_cusp_image_graph_of_metric_approximation
    (g : SmoothRiemannianMetric I M) (hg : RiemannianMetricComplete (I := I) g) (x₀ : M)
    (hsec : ∀ (x : M) (v w : TangentSpace I x),
      Curvature.metricRm04StandardAt g x v w w v =
        (-1 / 4 : ℝ) * (g.inner x v v * g.inner x w w - g.inner x v w * g.inner x v w))
    (gTarget : SmoothRiemannianMetric I N) (hgTarget : RiemannianMetricComplete (I := I) gTarget)
    (xTarget : N)
    (hsecTarget : ∀ (x : N) (v w : TangentSpace I x),
      Curvature.metricRm04StandardAt gTarget x v w w v =
        (-1 / 4 : ℝ) * (gTarget.inner x v v * gTarget.inner x w w -
          gTarget.inner x v w * gTarget.inner x v w))
    (Φ : PartialDiffeomorph I I M N ∞)
    {R ε : ℝ} {p : ℕ} (hp : 1 ≤ p) (hR : 2 < R) (hε : ε ≤ 1 / 100) :
    letI : Inhabited M := ⟨x₀⟩
    letI : LocallyPathConnectedSpace H := I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
    letI : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace H M
    letI : SemilocallySimplyConnectedSpace M := manifold_semilocallySimplyConnectedSpace (I := I)
    letI : SecondCountableTopology H := ModelWithCorners.secondCountableTopology I
    letI : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
    let gN := scaleMetric (-(-1 / 4 : ℝ)) (neg_pos.mpr quarter_curvature_neg) g
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
      let pH := normalizedUniversalCoverProjection g hg (-1 / 4) quarter_curvature_neg x₀ hsec i
      let ρ := normalizedUniversalCoverDeckRepresentation g hg (-1 / 4) quarter_curvature_neg x₀ hsec i
      let σ := (Hyperboloid.projectiveOrthogonalGroupEquiv 2 :
        (Hyperboloid E₃ ≃ᵢ Hyperboloid E₃) →* PO 3 1).comp ρ
      ∀ {r : ℝ} (D : CuspTruncation.FiniteCuspTruncation (Nat.le_add_left 1 2) σ.range r)
        (ξ : D.centers),
      let hΓ : IsDiscrete (SetLike.coe σ.range) :=
        (exists_normalizedUniversalCoverThinRegionCharts g hg (-1 / 4) quarter_curvature_neg x₀ hsec i).choose
      let P := CuspCrossSections.endStabilizer (Nat.le_add_left 1 2) σ.range (Set.singleton ξ.val)
      letI := EquivariantMap.subAction (Nat.le_add_left 1 2) σ.range
      letI := EquivariantMap.subAction (Nat.le_add_left 1 2) P
      letI : IsCancelSMul σ.range H₃ :=
        isCancelSMul_projective_range_normalizedUniversalCoverDeckRepresentation g hg (-1 / 4) quarter_curvature_neg x₀ hsec i
      letI : IsCancelSMul P H₃ := EquivariantMap.isCancelSMul_subAction
        (Nat.le_add_left 1 2) (show P ≤ σ.range from inf_le_left)
      let S := (Quotient.mk (MulAction.orbitRel P H₃)) '' Busemann.horosphere ξ.val (D.level ξ)
      letI : ChartedSpace (Fin 2 → ℝ) S := D.horosphereQuotientChartedSpace hΓ ξ
      ∀ (d : ℝ) (hd : 0 < d),
      let β : S → M := fun s => normalizedUniversalCoverCuspCylinderMap
        g hg (-1 / 4) quarter_curvature_neg x₀ hsec i D ξ (s, ⟨d, hd.le⟩)
      ∀ (B : M → ℝ),
      (∀ z : H₃, Busemann.busemann ξ.val z < D.level ξ → B (pH z) = 2 * Busemann.busemann ξ.val z) →
      (∀ s, PartialDiffeomorph.isMetricApproximationOn Φ (riemannianClosedBallOf g (β s) R) p ε g gTarget) →
      (∀ s, riemannianClosedBallOf g (β s) 2 ⊆ pH '' {z : H₃ | Busemann.busemann ξ.val z < D.level ξ}) →
      Metric.ediam (pH '' Busemann.horosphere ξ.val (D.level ξ - d)) ≤ ENNReal.ofReal (1 / 10) →
    letI : Inhabited N := ⟨xTarget⟩
    letI : LocallyPathConnectedSpace H := I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
    letI : LocallyPathConnectedSpace N := ChartedSpace.locallyPathConnectedSpace H N
    letI : SemilocallySimplyConnectedSpace N := manifold_semilocallySimplyConnectedSpace (I := I)
    letI : SecondCountableTopology H := ModelWithCorners.secondCountableTopology I
    letI : SecondCountableTopology N := ChartedSpace.secondCountable_of_sigmaCompact H N
    let gNTarget := scaleMetric (-(-1 / 4 : ℝ)) (neg_pos.mpr quarter_curvature_neg) gTarget
    let ĝTarget := UniversalCover.liftedMetric (I := I) gNTarget
    let hĝTarget : RiemannianMetricComplete ĝTarget := UniversalCover.liftedMetric_complete gNTarget (hgTarget.scaleMetric _ _)
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
    ∀ (iTarget : E₃ ≃ₗᵢ[ℝ] TangentSpace I (UniversalCover.basePoint (X := N))),
      let ρTarget := normalizedUniversalCoverDeckRepresentation gTarget hgTarget (-1 / 4) quarter_curvature_neg xTarget hsecTarget iTarget
      let σTarget := (Hyperboloid.projectiveOrthogonalGroupEquiv 2 :
        (Hyperboloid E₃ ≃ᵢ Hyperboloid E₃) →* PO 3 1).comp ρTarget
      ∀ {rTarget : ℝ} (DTarget : CuspTruncation.FiniteCuspTruncation (Nat.le_add_left 1 2) σTarget.range rTarget)
        (ξTarget : DTarget.centers),
      let hΓTarget : IsDiscrete (SetLike.coe σTarget.range) :=
        (exists_normalizedUniversalCoverThinRegionCharts gTarget hgTarget (-1 / 4) quarter_curvature_neg xTarget hsecTarget iTarget).choose
      let PTarget := CuspCrossSections.endStabilizer (Nat.le_add_left 1 2) σTarget.range (Set.singleton ξTarget.val)
      letI := EquivariantMap.subAction (Nat.le_add_left 1 2) σTarget.range
      letI := EquivariantMap.subAction (Nat.le_add_left 1 2) PTarget
      letI : IsCancelSMul σTarget.range H₃ :=
        isCancelSMul_projective_range_normalizedUniversalCoverDeckRepresentation gTarget hgTarget (-1 / 4) quarter_curvature_neg xTarget hsecTarget iTarget
      letI : IsCancelSMul PTarget H₃ := EquivariantMap.isCancelSMul_subAction
        (Nat.le_add_left 1 2) (show PTarget ≤ σTarget.range from inf_le_left)
      let T := (Quotient.mk (MulAction.orbitRel PTarget H₃)) '' Busemann.horosphere ξTarget.val (DTarget.level ξTarget)
      letI : ChartedSpace (Fin 2 → ℝ) T := DTarget.horosphereQuotientChartedSpace hΓTarget ξTarget
      let pHTarget := normalizedUniversalCoverProjection gTarget hgTarget (-1 / 4) quarter_curvature_neg xTarget hsecTarget iTarget
      let eTarget := normalizedUniversalCoverProjectiveQuotientHomeomorph gTarget hgTarget (-1 / 4) quarter_curvature_neg xTarget hsecTarget iTarget
      (∀ s, riemannianBallOf gTarget (Φ (β s)) 2 ⊆
        pHTarget '' interior (OrbifoldThinRegions.thinRegion
          (Nat.le_add_left 1 2) σTarget.range rTarget {ξTarget.val})) →
      ∃ A : PartialDiffeomorph J₂ I (T × ℝ) N ∞,
        A.toOpenPartialHomeomorph =
          (DTarget.horosphereGraphChart hΓTarget ξTarget).transHomeomorph eTarget ∧
      ∃ (η : T ≃ₘ⟮K₂, K₂⟯ S) (h : T → ℝ), ContMDiff K₂ 𝓘(ℝ, ℝ) ∞ h ∧
        (∀ t, A.symm (Φ (β (η t))) = (t, h t)) ∧
        (∀ t, (t, h t) ∈ A.source) ∧
        (∀ t, Φ (β (η t)) = A (t, h t)) ∧
        Set.range (Φ ∘ β) = Set.range (fun t => A (t, h t)) := by
  let _ : Inhabited M := ⟨x₀⟩
  let _ : LocallyPathConnectedSpace H := I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  let _ : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace H M
  let _ : SemilocallySimplyConnectedSpace M := manifold_semilocallySimplyConnectedSpace (I := I)
  let _ : SecondCountableTopology H := ModelWithCorners.secondCountableTopology I
  let _ : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
  let gN := scaleMetric (-(-1 / 4 : ℝ)) (neg_pos.mpr quarter_curvature_neg) g
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
  intro r D ξ
  let ρ := normalizedUniversalCoverDeckRepresentation g hg (-1 / 4) quarter_curvature_neg x₀ hsec i
  let σ := (Hyperboloid.projectiveOrthogonalGroupEquiv 2 :
    (Hyperboloid E₃ ≃ᵢ Hyperboloid E₃) →* PO 3 1).comp ρ
  let hΓ : IsDiscrete (SetLike.coe σ.range) :=
    (exists_normalizedUniversalCoverThinRegionCharts g hg (-1 / 4) quarter_curvature_neg x₀ hsec i).choose
  let P := CuspCrossSections.endStabilizer (Nat.le_add_left 1 2) σ.range (Set.singleton ξ.val)
  let := EquivariantMap.subAction (Nat.le_add_left 1 2) σ.range
  let := EquivariantMap.subAction (Nat.le_add_left 1 2) P
  let : DiscreteTopology σ.range := isDiscrete_iff_discreteTopology.mp hΓ
  let : IsCancelSMul σ.range H₃ :=
    isCancelSMul_projective_range_normalizedUniversalCoverDeckRepresentation g hg (-1 / 4) quarter_curvature_neg x₀ hsec i
  let : IsCancelSMul P H₃ := EquivariantMap.isCancelSMul_subAction
    (Nat.le_add_left 1 2) (show P ≤ σ.range from inf_le_left)
  let : ContinuousConstSMul σ.range H₃ :=
    ⟨fun a => (HyperbolicAction.contMDiff_po_smul 2 ∞ (a : PO 3 1)).continuous⟩
  let : ContMDiffConstSMul I₃ ∞ σ.range H₃ :=
    ⟨fun a => HyperbolicAction.contMDiff_po_smul 2 ∞ (a : PO 3 1)⟩
  let : ProperlyDiscontinuousSMul σ.range H₃ :=
    OrbifoldCompactness.properlyDiscontinuous_subAction (Nat.le_add_left 1 2) σ.range hΓ
  let S := (Quotient.mk (MulAction.orbitRel P H₃)) '' Busemann.horosphere ξ.val (D.level ξ)
  let : ChartedSpace (Fin 2 → ℝ) S := D.horosphereQuotientChartedSpace hΓ ξ
  intro d hd
  let β : S → M := fun s => normalizedUniversalCoverCuspCylinderMap
    g hg (-1 / 4) quarter_curvature_neg x₀ hsec i D ξ (s, ⟨d, hd.le⟩)
  let pH := normalizedUniversalCoverProjection g hg (-1 / 4) quarter_curvature_neg x₀ hsec i
  intro B htie hΦ hcollar hdiam
  let _ : Inhabited N := ⟨xTarget⟩
  let _ : LocallyPathConnectedSpace H := I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  let _ : LocallyPathConnectedSpace N := ChartedSpace.locallyPathConnectedSpace H N
  let _ : SemilocallySimplyConnectedSpace N := manifold_semilocallySimplyConnectedSpace (I := I)
  let _ : SecondCountableTopology H := ModelWithCorners.secondCountableTopology I
  let _ : SecondCountableTopology N := ChartedSpace.secondCountable_of_sigmaCompact H N
  let gNTarget := scaleMetric (-(-1 / 4 : ℝ)) (neg_pos.mpr quarter_curvature_neg) gTarget
  let ĝTarget := UniversalCover.liftedMetric (I := I) gNTarget
  let hĝTarget : RiemannianMetricComplete ĝTarget := UniversalCover.liftedMetric_complete gNTarget (hgTarget.scaleMetric _ _)
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
  intro iTarget rTarget DTarget ξTarget
  let ρTarget := normalizedUniversalCoverDeckRepresentation gTarget hgTarget (-1 / 4) quarter_curvature_neg xTarget hsecTarget iTarget
  let σTarget := (Hyperboloid.projectiveOrthogonalGroupEquiv 2 :
    (Hyperboloid E₃ ≃ᵢ Hyperboloid E₃) →* PO 3 1).comp ρTarget
  let hΓTarget : IsDiscrete (SetLike.coe σTarget.range) :=
    (exists_normalizedUniversalCoverThinRegionCharts gTarget hgTarget (-1 / 4) quarter_curvature_neg xTarget hsecTarget iTarget).choose
  let PTarget := CuspCrossSections.endStabilizer (Nat.le_add_left 1 2) σTarget.range (Set.singleton ξTarget.val)
  let := EquivariantMap.subAction (Nat.le_add_left 1 2) σTarget.range
  let := EquivariantMap.subAction (Nat.le_add_left 1 2) PTarget
  let : DiscreteTopology σTarget.range := isDiscrete_iff_discreteTopology.mp hΓTarget
  let : IsCancelSMul σTarget.range H₃ :=
    isCancelSMul_projective_range_normalizedUniversalCoverDeckRepresentation gTarget hgTarget (-1 / 4) quarter_curvature_neg xTarget hsecTarget iTarget
  let : IsCancelSMul PTarget H₃ := EquivariantMap.isCancelSMul_subAction
    (Nat.le_add_left 1 2) (show PTarget ≤ σTarget.range from inf_le_left)
  let : ContinuousConstSMul σTarget.range H₃ :=
    ⟨fun a => (HyperbolicAction.contMDiff_po_smul 2 ∞ (a : PO 3 1)).continuous⟩
  let : ContMDiffConstSMul I₃ ∞ σTarget.range H₃ :=
    ⟨fun a => HyperbolicAction.contMDiff_po_smul 2 ∞ (a : PO 3 1)⟩
  let : ProperlyDiscontinuousSMul σTarget.range H₃ :=
    OrbifoldCompactness.properlyDiscontinuous_subAction (Nat.le_add_left 1 2) σTarget.range hΓTarget
  let T := (Quotient.mk (MulAction.orbitRel PTarget H₃)) '' Busemann.horosphere ξTarget.val (DTarget.level ξTarget)
  let : ChartedSpace (Fin 2 → ℝ) T := DTarget.horosphereQuotientChartedSpace hΓTarget ξTarget
  let pHTarget := normalizedUniversalCoverProjection gTarget hgTarget (-1 / 4) quarter_curvature_neg xTarget hsecTarget iTarget
  let eTarget := normalizedUniversalCoverProjectiveQuotientHomeomorph gTarget hgTarget (-1 / 4) quarter_curvature_neg xTarget hsecTarget iTarget
  intro hball
  let _ : DiscreteTopology PTarget := isDiscrete_iff_discreteTopology.mp
    (hΓTarget.mono (show PTarget ≤ σTarget.range from inf_le_left))
  let _ : ProperlyDiscontinuousSMul PTarget H₃ :=
    OrbifoldCompactness.properlyDiscontinuous_subAction (Nat.le_add_left 1 2) PTarget
      (hΓTarget.mono (show PTarget ≤ σTarget.range from inf_le_left))
  let _ : ContinuousConstSMul PTarget H₃ :=
    ⟨fun a => (HyperbolicAction.contMDiff_po_smul 2 ∞ (a : PO 3 1)).continuous⟩
  let _ : IsManifold K₂ ∞ T := DTarget.isManifold_quotient_horosphere hΓTarget ξTarget
  let _ : ConnectedSpace T := isConnected_iff_connectedSpace.mp
    (DTarget.isConnected_quotient_horosphere ξTarget)
  have hproducer := native_cusp_chart_radial_curves
    gTarget hgTarget xTarget hsecTarget iTarget DTarget ξTarget (Φ ∘ β) hball
  let A : PartialDiffeomorph J₂ I (T × ℝ) N ∞ := hproducer.choose
  refine ⟨A, hproducer.choose_spec.1, ?_⟩
  exact native_graph_of_radial_curves g hg x₀ hsec gTarget Φ A hp hR hε i D ξ d hd B
    htie hΦ hcollar hdiam hproducer.choose_spec.2.1 hproducer.choose_spec.2.2

end DifferentialGeometry.Geometry.Hyperbolic
end

section
open scoped Manifold ContDiff Bundle ENNReal Topology
namespace DifferentialGeometry.Geometry.Hyperbolic
open Riemannian.Topology (UniversalCover SemilocallySimplyConnectedSpace
  manifold_semilocallySimplyConnectedSpace)
open ProjectiveOrthogonalGroup (PO)
local notation "E₃" => EuclideanSpace ℝ (Fin 3)
local notation "I₃" => 𝓘(ℝ, E₃)
local notation "K₂" => 𝓘(ℝ, Fin 2 → ℝ)
local notation "J₂" => ModelWithCorners.prod K₂ 𝓘(ℝ, ℝ)
local notation "H₃" => DifferentialGeometry.Hyperbolic.HUpper 3

universe u v
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E₃ H} [I.Boundaryless]
  {M : Type u} {N : Type v} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [T2Space N] [SigmaCompactSpace N] [ConnectedSpace N]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_axial_image_graph_of_metric_approximation
    (g : SmoothRiemannianMetric I M) (hg : RiemannianMetricComplete (I := I) g) (x₀ : M)
    (hsec : ∀ (x : M) (v w : TangentSpace I x),
      Curvature.metricRm04StandardAt g x v w w v =
        (-1 / 4 : ℝ) * (g.inner x v v * g.inner x w w - g.inner x v w * g.inner x v w))
    (gTarget : SmoothRiemannianMetric I N) (hgTarget : RiemannianMetricComplete (I := I) gTarget)
    (xTarget : N)
    (hsecTarget : ∀ (x : N) (v w : TangentSpace I x),
      Curvature.metricRm04StandardAt gTarget x v w w v =
        (-1 / 4 : ℝ) * (gTarget.inner x v v * gTarget.inner x w w -
          gTarget.inner x v w * gTarget.inner x v w))
    (Φ : PartialDiffeomorph I I M N ∞)
    {R ε : ℝ} {p : ℕ} (hp : 1 ≤ p) (hR : 2 < R) (hε : ε ≤ 1 / 100) :
    letI : Inhabited M := ⟨x₀⟩
    letI : LocallyPathConnectedSpace H := I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
    letI : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace H M
    letI : SemilocallySimplyConnectedSpace M := manifold_semilocallySimplyConnectedSpace (I := I)
    letI : SecondCountableTopology H := ModelWithCorners.secondCountableTopology I
    letI : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
    let gN := scaleMetric (-(-1 / 4 : ℝ)) (neg_pos.mpr quarter_curvature_neg) g
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
      let pH := normalizedUniversalCoverProjection g hg (-1 / 4) quarter_curvature_neg x₀ hsec i
      let ρ := normalizedUniversalCoverDeckRepresentation g hg (-1 / 4) quarter_curvature_neg x₀ hsec i
      let σ := (Hyperboloid.projectiveOrthogonalGroupEquiv 2 :
        (Hyperboloid E₃ ≃ᵢ Hyperboloid E₃) →* PO 3 1).comp ρ
      ∀ {r : ℝ} (D : CuspTruncation.FiniteCuspTruncation (Nat.le_add_left 1 2) σ.range r)
        (ξ : D.centers),
      let hΓ : IsDiscrete (SetLike.coe σ.range) :=
        (exists_normalizedUniversalCoverThinRegionCharts g hg (-1 / 4) quarter_curvature_neg x₀ hsec i).choose
      let P := CuspCrossSections.endStabilizer (Nat.le_add_left 1 2) σ.range (Set.singleton ξ.val)
      letI := EquivariantMap.subAction (Nat.le_add_left 1 2) σ.range
      letI := EquivariantMap.subAction (Nat.le_add_left 1 2) P
      letI : IsCancelSMul σ.range H₃ :=
        isCancelSMul_projective_range_normalizedUniversalCoverDeckRepresentation g hg (-1 / 4) quarter_curvature_neg x₀ hsec i
      letI : IsCancelSMul P H₃ := EquivariantMap.isCancelSMul_subAction
        (Nat.le_add_left 1 2) (show P ≤ σ.range from inf_le_left)
      let S := (Quotient.mk (MulAction.orbitRel P H₃)) '' Busemann.horosphere ξ.val (D.level ξ)
      letI : ChartedSpace (Fin 2 → ℝ) S := D.horosphereQuotientChartedSpace hΓ ξ
      ∀ (d : ℝ) (hd : 0 < d),
      let β : S → M := fun s => normalizedUniversalCoverCuspCylinderMap
        g hg (-1 / 4) quarter_curvature_neg x₀ hsec i D ξ (s, ⟨d, hd.le⟩)
      ∀ (B : M → ℝ),
      (∀ z : H₃, Busemann.busemann ξ.val z < D.level ξ → B (pH z) = 2 * Busemann.busemann ξ.val z) →
      (∀ s, PartialDiffeomorph.isMetricApproximationOn Φ (riemannianClosedBallOf g (β s) R) p ε g gTarget) →
      (∀ s, riemannianClosedBallOf g (β s) 2 ⊆ pH '' {z : H₃ | Busemann.busemann ξ.val z < D.level ξ}) →
      Metric.ediam (pH '' Busemann.horosphere ξ.val (D.level ξ - d)) ≤ ENNReal.ofReal (1 / 10) →
    letI : Inhabited N := ⟨xTarget⟩
    letI : LocallyPathConnectedSpace H := I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
    letI : LocallyPathConnectedSpace N := ChartedSpace.locallyPathConnectedSpace H N
    letI : SemilocallySimplyConnectedSpace N := manifold_semilocallySimplyConnectedSpace (I := I)
    letI : SecondCountableTopology H := ModelWithCorners.secondCountableTopology I
    letI : SecondCountableTopology N := ChartedSpace.secondCountable_of_sigmaCompact H N
    let gNTarget := scaleMetric (-(-1 / 4 : ℝ)) (neg_pos.mpr quarter_curvature_neg) gTarget
    let ĝTarget := UniversalCover.liftedMetric (I := I) gNTarget
    let hĝTarget : RiemannianMetricComplete ĝTarget := UniversalCover.liftedMetric_complete gNTarget (hgTarget.scaleMetric _ _)
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
    ∀ (iTarget : E₃ ≃ₗᵢ[ℝ] TangentSpace I (UniversalCover.basePoint (X := N))),
      let ρTarget := normalizedUniversalCoverDeckRepresentation gTarget hgTarget (-1 / 4) quarter_curvature_neg xTarget hsecTarget iTarget
      let σTarget := (Hyperboloid.projectiveOrthogonalGroupEquiv 2 :
        (Hyperboloid E₃ ≃ᵢ Hyperboloid E₃) →* PO 3 1).comp ρTarget
      ∀ (ξTarget ηTarget : HyperbolicBoundary.BoundaryH 3) (hneTarget : ξTarget ≠ ηTarget) (rTarget : ℝ),
      let hΓTarget : IsDiscrete (SetLike.coe σTarget.range) :=
        (exists_normalizedUniversalCoverThinRegionCharts gTarget hgTarget (-1 / 4) quarter_curvature_neg xTarget hsecTarget iTarget).choose
      letI : DiscreteTopology σTarget.range := isDiscrete_iff_discreteTopology.mp hΓTarget
      let PTarget := CuspCrossSections.endStabilizer (Nat.le_add_left 1 2) σTarget.range ({ξTarget, ηTarget})
      letI := EquivariantMap.subAction (Nat.le_add_left 1 2) σTarget.range
      letI := EquivariantMap.subAction (Nat.le_add_left 1 2) PTarget
      letI : IsCancelSMul σTarget.range H₃ :=
        isCancelSMul_projective_range_normalizedUniversalCoverDeckRepresentation gTarget hgTarget (-1 / 4) quarter_curvature_neg xTarget hsecTarget iTarget
      letI : IsCancelSMul PTarget H₃ := EquivariantMap.isCancelSMul_subAction
        (Nat.le_add_left 1 2) (show PTarget ≤ σTarget.range from inf_le_left)
      letI : DiscreteTopology PTarget := isDiscrete_iff_discreteTopology.mp
        (hΓTarget.mono (show PTarget ≤ σTarget.range from inf_le_left))
      let hpairTarget := OrbifoldThinRegions.end_stabilizer_preserves_pair 2 σTarget.range ξTarget ηTarget
      let T := {q : MulAction.orbitRel.Quotient PTarget H₃ //
        AxisGeometry.quotientAxisDistance 2 PTarget ξTarget ηTarget hneTarget hpairTarget q = Real.arsinh 1}
      letI : ChartedSpace (Fin 2 → ℝ) T := AxisGeometry.axisSectionChartedSpace 2 PTarget ξTarget ηTarget hneTarget hpairTarget
      let pHTarget := normalizedUniversalCoverProjection gTarget hgTarget (-1 / 4) quarter_curvature_neg xTarget hsecTarget iTarget
      let eTarget := normalizedUniversalCoverProjectiveQuotientHomeomorph gTarget hgTarget (-1 / 4) quarter_curvature_neg xTarget hsecTarget iTarget
      (∀ s, riemannianBallOf gTarget (Φ (β s)) 2 ⊆
        pHTarget '' interior (OrbifoldThinRegions.thinRegion
          (Nat.le_add_left 1 2) σTarget.range rTarget {ξTarget, ηTarget})) →
      (∀ s, Φ (β s) ∉ pHTarget '' (AxisGeometry.axis ξTarget ηTarget ∩
        OrbifoldThinRegions.thinRegion (Nat.le_add_left 1 2) σTarget.range rTarget {ξTarget, ηTarget})) →
      ∃ A : PartialDiffeomorph J₂ I (T × ℝ) N ∞,
        A.toOpenPartialHomeomorph =
          (OrbifoldThinRegions.axialGraphChart 2 σTarget.range ξTarget ηTarget hneTarget
            (by decide) rTarget).transHomeomorph eTarget ∧
      ∃ (η : T ≃ₘ⟮K₂, K₂⟯ S) (h : T → ℝ), ContMDiff K₂ 𝓘(ℝ, ℝ) ∞ h ∧
        (∀ t, A.symm (Φ (β (η t))) = (t, h t)) ∧
        (∀ t, (t, h t) ∈ A.source) ∧
        (∀ t, Φ (β (η t)) = A (t, h t)) ∧
        Set.range (Φ ∘ β) = Set.range (fun t => A (t, h t)) := by
  let _ : Inhabited M := ⟨x₀⟩
  let _ : LocallyPathConnectedSpace H := I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  let _ : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace H M
  let _ : SemilocallySimplyConnectedSpace M := manifold_semilocallySimplyConnectedSpace (I := I)
  let _ : SecondCountableTopology H := ModelWithCorners.secondCountableTopology I
  let _ : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
  let gN := scaleMetric (-(-1 / 4 : ℝ)) (neg_pos.mpr quarter_curvature_neg) g
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
  intro r D ξ
  let ρ := normalizedUniversalCoverDeckRepresentation g hg (-1 / 4) quarter_curvature_neg x₀ hsec i
  let σ := (Hyperboloid.projectiveOrthogonalGroupEquiv 2 :
    (Hyperboloid E₃ ≃ᵢ Hyperboloid E₃) →* PO 3 1).comp ρ
  let hΓ : IsDiscrete (SetLike.coe σ.range) :=
    (exists_normalizedUniversalCoverThinRegionCharts g hg (-1 / 4) quarter_curvature_neg x₀ hsec i).choose
  let P := CuspCrossSections.endStabilizer (Nat.le_add_left 1 2) σ.range (Set.singleton ξ.val)
  let := EquivariantMap.subAction (Nat.le_add_left 1 2) σ.range
  let := EquivariantMap.subAction (Nat.le_add_left 1 2) P
  let : DiscreteTopology σ.range := isDiscrete_iff_discreteTopology.mp hΓ
  let : IsCancelSMul σ.range H₃ :=
    isCancelSMul_projective_range_normalizedUniversalCoverDeckRepresentation g hg (-1 / 4) quarter_curvature_neg x₀ hsec i
  let : IsCancelSMul P H₃ := EquivariantMap.isCancelSMul_subAction
    (Nat.le_add_left 1 2) (show P ≤ σ.range from inf_le_left)
  let : ContinuousConstSMul σ.range H₃ :=
    ⟨fun a => (HyperbolicAction.contMDiff_po_smul 2 ∞ (a : PO 3 1)).continuous⟩
  let : ContMDiffConstSMul I₃ ∞ σ.range H₃ :=
    ⟨fun a => HyperbolicAction.contMDiff_po_smul 2 ∞ (a : PO 3 1)⟩
  let : ProperlyDiscontinuousSMul σ.range H₃ :=
    OrbifoldCompactness.properlyDiscontinuous_subAction (Nat.le_add_left 1 2) σ.range hΓ
  let S := (Quotient.mk (MulAction.orbitRel P H₃)) '' Busemann.horosphere ξ.val (D.level ξ)
  let : ChartedSpace (Fin 2 → ℝ) S := D.horosphereQuotientChartedSpace hΓ ξ
  intro d hd
  let β : S → M := fun s => normalizedUniversalCoverCuspCylinderMap
    g hg (-1 / 4) quarter_curvature_neg x₀ hsec i D ξ (s, ⟨d, hd.le⟩)
  let pH := normalizedUniversalCoverProjection g hg (-1 / 4) quarter_curvature_neg x₀ hsec i
  intro B htie hΦ hcollar hdiam
  let _ : Inhabited N := ⟨xTarget⟩
  let _ : LocallyPathConnectedSpace H := I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  let _ : LocallyPathConnectedSpace N := ChartedSpace.locallyPathConnectedSpace H N
  let _ : SemilocallySimplyConnectedSpace N := manifold_semilocallySimplyConnectedSpace (I := I)
  let _ : SecondCountableTopology H := ModelWithCorners.secondCountableTopology I
  let _ : SecondCountableTopology N := ChartedSpace.secondCountable_of_sigmaCompact H N
  let gNTarget := scaleMetric (-(-1 / 4 : ℝ)) (neg_pos.mpr quarter_curvature_neg) gTarget
  let ĝTarget := UniversalCover.liftedMetric (I := I) gNTarget
  let hĝTarget : RiemannianMetricComplete ĝTarget := UniversalCover.liftedMetric_complete gNTarget (hgTarget.scaleMetric _ _)
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
  intro iTarget ξTarget ηTarget hneTarget rTarget
  let ρTarget := normalizedUniversalCoverDeckRepresentation gTarget hgTarget (-1 / 4) quarter_curvature_neg xTarget hsecTarget iTarget
  let σTarget := (Hyperboloid.projectiveOrthogonalGroupEquiv 2 :
    (Hyperboloid E₃ ≃ᵢ Hyperboloid E₃) →* PO 3 1).comp ρTarget
  let hΓTarget : IsDiscrete (SetLike.coe σTarget.range) :=
    (exists_normalizedUniversalCoverThinRegionCharts gTarget hgTarget (-1 / 4) quarter_curvature_neg xTarget hsecTarget iTarget).choose
  let PTarget := CuspCrossSections.endStabilizer (Nat.le_add_left 1 2) σTarget.range ({ξTarget, ηTarget})
  let := EquivariantMap.subAction (Nat.le_add_left 1 2) σTarget.range
  let := EquivariantMap.subAction (Nat.le_add_left 1 2) PTarget
  let : DiscreteTopology σTarget.range := isDiscrete_iff_discreteTopology.mp hΓTarget
  let : IsCancelSMul σTarget.range H₃ :=
    isCancelSMul_projective_range_normalizedUniversalCoverDeckRepresentation gTarget hgTarget (-1 / 4) quarter_curvature_neg xTarget hsecTarget iTarget
  let : IsCancelSMul PTarget H₃ := EquivariantMap.isCancelSMul_subAction
    (Nat.le_add_left 1 2) (show PTarget ≤ σTarget.range from inf_le_left)
  let : ContinuousConstSMul σTarget.range H₃ :=
    ⟨fun a => (HyperbolicAction.contMDiff_po_smul 2 ∞ (a : PO 3 1)).continuous⟩
  let : ContMDiffConstSMul I₃ ∞ σTarget.range H₃ :=
    ⟨fun a => HyperbolicAction.contMDiff_po_smul 2 ∞ (a : PO 3 1)⟩
  let : ProperlyDiscontinuousSMul σTarget.range H₃ :=
    OrbifoldCompactness.properlyDiscontinuous_subAction (Nat.le_add_left 1 2) σTarget.range hΓTarget
  let : DiscreteTopology PTarget := isDiscrete_iff_discreteTopology.mp
    (hΓTarget.mono (show PTarget ≤ σTarget.range from inf_le_left))
  let hpairTarget := OrbifoldThinRegions.end_stabilizer_preserves_pair 2 σTarget.range ξTarget ηTarget
  let T := {q : MulAction.orbitRel.Quotient PTarget H₃ //
    AxisGeometry.quotientAxisDistance 2 PTarget ξTarget ηTarget hneTarget hpairTarget q = Real.arsinh 1}
  let : ChartedSpace (Fin 2 → ℝ) T := AxisGeometry.axisSectionChartedSpace 2 PTarget ξTarget ηTarget hneTarget hpairTarget
  let pHTarget := normalizedUniversalCoverProjection gTarget hgTarget (-1 / 4) quarter_curvature_neg xTarget hsecTarget iTarget
  let eTarget := normalizedUniversalCoverProjectiveQuotientHomeomorph gTarget hgTarget (-1 / 4) quarter_curvature_neg xTarget hsecTarget iTarget
  intro hball hoff
  let _ : ProperlyDiscontinuousSMul PTarget H₃ :=
    OrbifoldCompactness.properlyDiscontinuous_subAction (Nat.le_add_left 1 2) PTarget
      (hΓTarget.mono (show PTarget ≤ σTarget.range from inf_le_left))
  let _ : ContinuousConstSMul PTarget H₃ :=
    ⟨fun a => (HyperbolicAction.contMDiff_po_smul 2 ∞ (a : PO 3 1)).continuous⟩
  let _ : IsManifold K₂ ∞ T := AxisGeometry.axisSection_isManifold
    2 PTarget ξTarget ηTarget hneTarget hpairTarget
  let _ : ConnectedSpace T := isConnected_iff_connectedSpace.mp
    (AxisGeometry.isPathConnected_setOf_quotientAxisDistance_eq 2 PTarget (by decide)
      ξTarget ηTarget hneTarget hpairTarget (Real.arsinh 1)
        (Real.arsinh_nonneg_iff.mpr (by norm_num))).isConnected
  have hproducer := native_axial_chart_radial_curves
    gTarget hgTarget xTarget hsecTarget iTarget ξTarget ηTarget hneTarget rTarget (Φ ∘ β) hball hoff
  let A : PartialDiffeomorph J₂ I (T × ℝ) N ∞ := hproducer.choose
  refine ⟨A, hproducer.choose_spec.1, ?_⟩
  exact native_graph_of_radial_curves g hg x₀ hsec gTarget Φ A hp hR hε i D ξ d hd B
    htie hΦ hcollar hdiam hproducer.choose_spec.2.1 hproducer.choose_spec.2.2

end DifferentialGeometry.Geometry.Hyperbolic
end
