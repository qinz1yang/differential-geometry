import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Geodesic.PeriodicAxis
import DifferentialGeometry.Geometry.Hyperbolic.ProjectionGeodesic
import DifferentialGeometry.Geometry.Hyperbolic.ProjectiveDeckGroup
import DifferentialGeometry.Geometry.Hyperbolic.ProjectionMetric
import DifferentialGeometry.Geometry.Hyperbolic.DeckGroup
import Mathlib.Algebra.Field.Periodic

noncomputable section

open scoped Manifold ContDiff Bundle ENNReal

namespace DifferentialGeometry.Geometry.Hyperbolic

open Riemannian.Geodesic (IsGeodesic HasGeodesicEquationAt)
open Riemannian.Topology (UniversalCover SemilocallySimplyConnectedSpace
  manifold_semilocallySimplyConnectedSpace)
open AsymptoticRays (rayTo)

local notation "E₃" => EuclideanSpace ℝ (Fin 3)
local notation "I₃" => 𝓘(ℝ, E₃)
local notation "H₃" => DifferentialGeometry.Hyperbolic.HUpper 3
local notation "B₃" => HyperbolicBoundary.BoundaryH 3

private instance : NeZero (Module.finrank ℝ E₃) := ⟨by simp⟩

private theorem periodic_projected_half_ray {M : Type*} [TopologicalSpace M]
    (F : C(H₃, M)) (y : H₃) (ξ : B₃) (a : ProjectiveOrthogonalGroup.PO 3 1) (τ : ℝ)
    (hshift : ∀ t : ℝ, (DifferentialGeometry.HyperbolicAction.poMulAction (by decide)).smul a
      (rayTo y ξ t) = rayTo y ξ (t + τ))
    (hproj : ∀ z : H₃, F ((DifferentialGeometry.HyperbolicAction.poMulAction (by decide)).smul a z) = F z) :
    Function.Periodic (fun t => F (rayTo y ξ (t / 2))) (2 * |τ|) := by
  have hperiod : Function.Periodic (fun t => F (rayTo y ξ t)) τ := by
    intro t
    change F (rayTo y ξ (t + τ)) = F (rayTo y ξ t)
    exact (congrArg F (hshift t)).symm.trans (hproj _)
  have hpabs : Function.Periodic (fun t => F (rayTo y ξ t)) |τ| := by
    rcases le_total 0 τ with h | h
    · simpa only [abs_of_nonneg h] using hperiod
    · simpa only [abs_of_nonpos h] using hperiod.neg
  rw [mul_comm]
  exact hpabs.div_const 2

private theorem capture_periodic_half_ray
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E₃ H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (g : SmoothRiemannianMetric I M) (F : C(H₃, M)) (y : H₃) (ξ : B₃)
    (γ : C(ℝ, M)) (T r : ℝ)
    (heq : ∀ t : ℝ, γ t = F (rayTo y ξ (t / 2))) (hγ0 : γ 0 = F y)
    (hperiod : Function.Periodic γ T) (hbound : T ≤ 4 * r)
    (hball : F '' Metric.ball y (2 * r) = riemannianBallOf g (F y) (4 * r)) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, γ t ∈ riemannianClosedBallOf g (γ 0) (4 * r) := by
  intro t ht
  by_cases hte : t = T
  · have he : γ t = γ 0 := by
      rw [hte]
      simpa only [zero_add] using hperiod 0
    rw [he]
    change riemannianEDistOf g (γ 0) (γ 0) ≤ ENNReal.ofReal (4 * r)
    rw [riemannianEDistOf_self]
    exact bot_le
  · have htlt : t < T := lt_of_le_of_ne ht.2 hte
    have hdist : dist (rayTo y ξ (t / 2)) y < 2 * r := by
      rw [dist_comm, AsymptoticRays.dist_rayTo_self, abs_of_nonneg (div_nonneg ht.1 (by norm_num))]
      linarith
    have hmem : F (rayTo y ξ (t / 2)) ∈ riemannianBallOf g (F y) (4 * r) :=
      hball ▸ Set.mem_image_of_mem F (Metric.mem_ball.mpr hdist)
    change riemannianEDistOf g (γ 0) (γ t) ≤ ENNReal.ofReal (4 * r)
    rw [hγ0, heq t]
    exact le_of_lt hmem

private theorem quarter_negative : (-1 / 4 : ℝ) < 0 := by norm_num

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E₃ H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem projection_projective_smul
    (g : SmoothRiemannianMetric I M) (hg : RiemannianMetricComplete (I := I) g) (x₀ : M)
    (hsec : ∀ (x : M) (X Y : TangentSpace I x),
      Curvature.metricRm04StandardAt g x X Y Y X =
        (-1 / 4 : ℝ) * (g.inner x X X * g.inner x Y Y - g.inner x X Y * g.inner x X Y)) :
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
    ∀ (i : E₃ ≃ₗᵢ[ℝ] TangentSpace I (UniversalCover.basePoint (X := M))),
      let ρ := normalizedUniversalCoverDeckRepresentation g hg (-1 / 4) quarter_negative x₀ hsec i
      let σ := (Hyperboloid.projectiveOrthogonalGroupEquiv 2 :
        (Hyperboloid E₃ ≃ᵢ Hyperboloid E₃) →* ProjectiveOrthogonalGroup.PO 3 1).comp ρ
      ∀ (b : σ.range) (z : H₃),
        normalizedUniversalCoverProjection g hg (-1 / 4) quarter_negative x₀ hsec i
          ((DifferentialGeometry.HyperbolicAction.poMulAction (by decide)).smul
            (b : ProjectiveOrthogonalGroup.PO 3 1) z) =
        normalizedUniversalCoverProjection g hg (-1 / 4) quarter_negative x₀ hsec i z := by
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
  intro i b z
  let ρ := normalizedUniversalCoverDeckRepresentation g hg (-1 / 4) quarter_negative x₀ hsec i
  let σ := (Hyperboloid.projectiveOrthogonalGroupEquiv 2 :
    (Hyperboloid E₃ ≃ᵢ Hyperboloid E₃) →* ProjectiveOrthogonalGroup.PO 3 1).comp ρ
  obtain ⟨δ, hδ⟩ := b.property
  have hJ := Hyperboloid.projectiveOrthogonalGroupEquiv_smul 2 (ρ δ) z
  change Hyperboloid.hUpperIsometryEquiv 3
    ((DifferentialGeometry.HyperbolicAction.poMulAction (by decide)).smul (σ δ) z) =
      ρ δ (Hyperboloid.hUpperIsometryEquiv 3 z) at hJ
  rw [hδ] at hJ
  let e := normalizedUniversalCoverIsometryEquiv g hg (-1 / 4) quarter_negative x₀ hsec i
  exact (congrArg (fun w : Hyperboloid E₃ => UniversalCover.proj (e w)) hJ).trans
    (proj_normalizedUniversalCoverDeckRepresentation
      g hg (-1 / 4) quarter_negative x₀ hsec i δ (Hyperboloid.hUpperIsometryEquiv 3 z))


attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_periodic_geodesic_of_mem_axial_thinRegion
    (g : SmoothRiemannianMetric I M) (hg : RiemannianMetricComplete (I := I) g) (x₀ : M)
    (hsec : ∀ (x : M) (X Y : TangentSpace I x),
      Curvature.metricRm04StandardAt g x X Y Y X =
        (-1 / 4 : ℝ) * (g.inner x X X * g.inner x Y Y - g.inner x X Y * g.inner x X Y)) :
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
    ∀ (i : E₃ ≃ₗᵢ[ℝ] TangentSpace I (UniversalCover.basePoint (X := M))),
      let ρ := normalizedUniversalCoverDeckRepresentation g hg (-1 / 4) quarter_negative x₀ hsec i
      let Γ := ((Hyperboloid.projectiveOrthogonalGroupEquiv 2 :
        (Hyperboloid E₃ ≃ᵢ Hyperboloid E₃) →* ProjectiveOrthogonalGroup.PO 3 1).comp ρ).range
      ∀ (ξ η : B₃) (hne : ξ ≠ η) (y : H₃) (r : ℝ),
        y ∈ AxisGeometry.axis ξ η → y ∈ OrbifoldThinRegions.thinRegion (by decide) Γ r {ξ, η} →
        ∃ (a : Γ) (τ : ℝ) (γ : C(ℝ, M)),
          a ≠ 1 ∧ a ^ 2 ≠ 1 ∧
          dist ((DifferentialGeometry.HyperbolicAction.poMulAction (by decide)).smul
            (a : ProjectiveOrthogonalGroup.PO 3 1) y) y ≤ r ∧
          τ = Real.log (BusemannCocycle.poConfFactor (by decide)
            ((a : ProjectiveOrthogonalGroup.PO 3 1) ^ 2) ξ) ∧
          τ ≠ 0 ∧ 0 < 2 * |τ| ∧ 2 * |τ| ≤ 4 * r ∧
          (∀ t : ℝ, (DifferentialGeometry.HyperbolicAction.poMulAction (by decide)).smul
            ((a : ProjectiveOrthogonalGroup.PO 3 1) ^ 2) (rayTo y ξ t) = rayTo y ξ (t + τ)) ∧
          (∀ t : ℝ, γ t = normalizedUniversalCoverProjection g hg (-1 / 4) quarter_negative
            x₀ hsec i (rayTo y ξ (t / 2))) ∧
          γ 0 = normalizedUniversalCoverProjection g hg (-1 / 4) quarter_negative x₀ hsec i y ∧
          Function.Periodic γ (2 * |τ|) ∧ ContMDiff 𝓘(ℝ, ℝ) I ∞ γ ∧ IsGeodesic g γ ∧
          (∀ t : ℝ, g.inner (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))
            (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)) = 1) ∧
          ∀ t ∈ Set.Icc (0 : ℝ) (2 * |τ|),
            γ t ∈ riemannianClosedBallOf g (γ 0) (4 * r) := by
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
  intro i ξ η hne y r hy hthin
  let ρ := normalizedUniversalCoverDeckRepresentation g hg (-1 / 4) quarter_negative x₀ hsec i
  let Φ := Hyperboloid.projectiveOrthogonalGroupEquiv 2
  let σ := (Φ : (Hyperboloid E₃ ≃ᵢ Hyperboloid E₃) →* ProjectiveOrthogonalGroup.PO 3 1).comp ρ
  let Γ := σ.range
  let F := normalizedUniversalCoverProjection g hg (-1 / 4) quarter_negative x₀ hsec i
  let := EquivariantMap.subAction (by decide : 1 ≤ 3) Γ
  have hfree : IsCancelSMul Γ H₃ :=
    isCancelSMul_projective_range_normalizedUniversalCoverDeckRepresentation
      g hg (-1 / 4) quarter_negative x₀ hsec i
  have htorsion (a : Γ) (ha : IsOfFinOrder a) : a = 1 :=
    (projective_range_normalizedUniversalCoverDeckRepresentation_isOfFinOrder_iff_eq_one
      g hg (-1 / 4) quarter_negative x₀ hsec i a).mp ha
  obtain ⟨a, τ, ha, ha2, hshort, hτeq, hτ, hτbound, hshift⟩ :=
    AxisGeometry.exists_short_shift_sq_of_mem_axial_thinRegion
      (by decide) Γ ξ η hne hy hthin htorsion hfree
  obtain ⟨hsmooth, hgeo, hunit⟩ :=
    normalizedUniversalCoverProjection_rayTo_half_unit_geodesic g hg x₀ hsec i y ξ
  let γ : C(ℝ, M) := ⟨fun t => F (rayTo y ξ (t / 2)), hsmooth.continuous⟩
  have hγ0 : γ 0 = F y := by
    change F (rayTo y ξ (0 / 2)) = F y
    rw [zero_div, AsymptoticRays.rayTo_zero]
  have hproj := projection_projective_smul g hg x₀ hsec i
  have hproj_sq (z : H₃) :
      F ((DifferentialGeometry.HyperbolicAction.poMulAction (by decide)).smul
        ((a : ProjectiveOrthogonalGroup.PO 3 1) ^ 2) z) = F z := by
    have h := hproj (a ^ 2) z
    simpa only [Subgroup.coe_pow] using h
  have hγperiod : Function.Periodic γ (2 * |τ|) :=
    periodic_projected_half_ray F y ξ ((a : ProjectiveOrthogonalGroup.PO 3 1) ^ 2) τ hshift hproj_sq
  have hTpos : 0 < 2 * |τ| := mul_pos (by norm_num) (abs_pos.mpr hτ)
  have hTbound : 2 * |τ| ≤ 4 * r := by linarith
  have hball : F '' Metric.ball y (2 * r) = riemannianBallOf g (F y) (4 * r) := by
    have hb := image_ball_normalizedUniversalCoverProjection_original_metric
      g hg (-1 / 4) quarter_negative x₀ hsec i y (4 * r)
    have hradius : Real.sqrt (-(-1 / 4 : ℝ)) * (4 * r) = 2 * r := by
      norm_num [Real.sqrt_div, Real.sqrt_one]
      ring
    exact (congrArg (fun R : ℝ => F '' Metric.ball y R) hradius).symm.trans hb
  exact ⟨a, τ, γ, ha, ha2, hshort, hτeq, hτ, hTpos, hTbound, hshift,
    fun _ => rfl, hγ0, hγperiod, hsmooth, hgeo, hunit,
    capture_periodic_half_ray g F y ξ γ (2 * |τ|) r (fun _ => rfl) hγ0 hγperiod hTbound hball⟩

end DifferentialGeometry.Geometry.Hyperbolic
