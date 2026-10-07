import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.UpperSheetGeodesic
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Horosphere.SmoothProjection
import DifferentialGeometry.Geometry.Hyperbolic.ProjectiveQuotient
import DifferentialGeometry.Geometry.Geodesic.Naturality.LocalIsometry.Geodesic
import DifferentialGeometry.Geometry.Connection.ParallelTransport.Derivative.CovariantDerivativeScaling

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

private theorem mfderiv_comp_affine
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    (c : ℝ → M) (hc : ContMDiff 𝓘(ℝ, ℝ) I ∞ c) (a b t : ℝ) :
    mfderiv 𝓘(ℝ, ℝ) I (fun s => c (a * s + b)) t (1 : ℝ) =
      a • mfderiv 𝓘(ℝ, ℝ) I c (a * t + b) (1 : ℝ) := by
  let h : ℝ → ℝ := fun s => a * s + b
  have hh : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ h :=
    ((contDiff_const.mul contDiff_id).add contDiff_const).contMDiff
  have hd : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) h t (1 : ℝ) = a := by
    rw [mfderiv_eq_fderiv]
    change fderiv ℝ h t (1 : ℝ) = _
    rw [fderiv_apply_one_eq_deriv]
    simpa only [h, id_eq, mul_one] using (((hasDerivAt_id t).const_mul a).add_const b).deriv
  have hchain := mfderiv_comp_apply (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, ℝ)) (I'' := I)
    (f := h) (g := c) t (hc.mdifferentiableAt (by simp)) (hh.mdifferentiableAt (by simp)) (1 : ℝ)
  rw [hd] at hchain
  apply hchain.trans
  let A : ℝ →L[ℝ] E := mfderiv 𝓘(ℝ, ℝ) I c (a * t + b)
  change A a = a • A 1
  simpa only [smul_eq_mul, mul_one] using A.map_smul a (1 : ℝ)

private theorem isGeodesic_scale
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (g : SmoothRiemannianMetric I M) (c : ℝ) (hc : 0 < c)
    (γ : ℝ → M) (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ) (hgeo : IsGeodesic g γ) :
    IsGeodesic (scaleMetric c hc g) γ := by
  intro t
  apply (Riemannian.CovariantDerivativeAlong.covDerivAlong_velocity_eq_zero_iff_hasGeodesicEquationAt
    (scaleMetric c hc g) γ t hγ).mp
  rw [Riemannian.CovariantDerivativeAlong.covDerivAlong_scale]
  exact (Riemannian.CovariantDerivativeAlong.covDerivAlong_velocity_eq_zero_iff_hasGeodesicEquationAt
    g γ t hγ).mpr (hgeo t)

private theorem projected_affine_geodesic_properties
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E₃ H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M] [BoundarylessManifold I M]
    (g : SmoothRiemannianMetric I M) (F : C(H₃, M))
    (hF : IsLocalDiffeomorph I₃ I ∞ F)
    (hpres : ∀ (p : H₃) (v w : TangentSpace I₃ p),
      g.inner (F p) (mfderiv I₃ I F p v) (mfderiv I₃ I F p w) =
      4 * Hyperboloid.riemannianMetric.inner ((Hyperboloid.hUpperDiffeomorph 3) p)
        (mfderiv I₃ I₃ (Hyperboloid.hUpperDiffeomorph 3) p v)
        (mfderiv I₃ I₃ (Hyperboloid.hUpperDiffeomorph 3) p w))
    (c : ℝ → H₃) (hc : ContMDiff 𝓘(ℝ, ℝ) I₃ ∞ c)
    (hcgeo : IsGeodesic Hyperboloid.riemannianMetric (fun t => Hyperboloid.hUpperIsometryEquiv 3 (c t)))
    (hcunit : ∀ t, Hyperboloid.riemannianMetric.inner (Hyperboloid.hUpperIsometryEquiv 3 (c t))
      (mfderiv 𝓘(ℝ, ℝ) I₃ (fun s => Hyperboloid.hUpperIsometryEquiv 3 (c s)) t (1 : ℝ))
      (mfderiv 𝓘(ℝ, ℝ) I₃ (fun s => Hyperboloid.hUpperIsometryEquiv 3 (c s)) t (1 : ℝ)) = 1)
    (a b : ℝ) (ha : 4 * a ^ 2 = 1)
    (φ : ℝ → ℝ) (hφ : φ = fun t => a * t + b) :
    let γ := fun t : ℝ => F (c (φ t))
    ContMDiff 𝓘(ℝ, ℝ) I ∞ γ ∧ IsGeodesic g γ ∧
      ∀ t : ℝ, g.inner (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))
        (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)) = 1 := by
  subst φ
  let J := Hyperboloid.hUpperDiffeomorph 3
  let d : ℝ → H₃ := fun t => c (a * t + b)
  let Hmetric := Diffeomorph.pullbackMetricCross Hyperboloid.riemannianMetric J
  have hd : ContMDiff 𝓘(ℝ, ℝ) I₃ ∞ d :=
    hc.comp ((contDiff_const.mul contDiff_id).add contDiff_const).contMDiff
  have hcgeoH : IsGeodesic Hmetric c := by
    intro t
    exact Riemannian.Geodesic.geoEq_of_mapCrossAt Hyperboloid.riemannianMetric J c t
      hc.contMDiffAt (hcgeo t)
  have hdgeo : IsGeodesic Hmetric d := by
    intro t
    exact Riemannian.Geodesic.hasGeodesicEquationAt_comp_affine
      (c := a) (d := b) (t := t) (hcgeoH (a * t + b))
  have hdgeo4 := isGeodesic_scale Hmetric 4 (by norm_num) d hd hdgeo
  have hmetric (p : H₃) (v w : TangentSpace I₃ p) :
      (scaleMetric 4 (by norm_num) Hmetric).inner p v w =
        g.inner (F p) (mfderiv I₃ I F p v) (mfderiv I₃ I F p w) := by
    rw [scaleMetric_inner, Diffeomorph.pullbackMetricCross_inner]
    exact (hpres p v w).symm
  refine ⟨hF.contMDiff.comp hd, ?_, ?_⟩
  · intro t
    exact Riemannian.Geodesic.geoEq_map_localIso (scaleMetric 4 (by norm_num) Hmetric)
      g hF hmetric d t hd.contMDiffAt (hdgeo4 t)
  · intro t
    let V := mfderiv 𝓘(ℝ, ℝ) I₃ c (a * t + b) (1 : ℝ)
    have hf := mfderiv_comp_apply (I := 𝓘(ℝ, ℝ)) (I' := I₃) (I'' := I)
      (f := c) (g := F) (a * t + b) (hF.contMDiff.mdifferentiableAt (by simp))
      (hc.mdifferentiableAt (by simp)) (1 : ℝ)
    have hj := mfderiv_comp_apply (I := 𝓘(ℝ, ℝ)) (I' := I₃) (I'' := I₃)
      (f := c) (g := J) (a * t + b) (J.contMDiff.mdifferentiableAt (by simp))
      (hc.mdifferentiableAt (by simp)) (1 : ℝ)
    have hunit : Hyperboloid.riemannianMetric.inner (J (c (a * t + b)))
        (mfderiv I₃ I₃ J (c (a * t + b)) V) (mfderiv I₃ I₃ J (c (a * t + b)) V) = 1 := by
      have h := hcunit (a * t + b)
      change Hyperboloid.riemannianMetric.inner (J (c (a * t + b)))
        (mfderiv 𝓘(ℝ, ℝ) I₃ (J ∘ c) (a * t + b) (1 : ℝ))
        (mfderiv 𝓘(ℝ, ℝ) I₃ (J ∘ c) (a * t + b) (1 : ℝ)) = 1 at h
      rw [hj] at h
      exact h
    have hspeed : g.inner (F (c (a * t + b)))
        (mfderiv 𝓘(ℝ, ℝ) I (F ∘ c) (a * t + b) (1 : ℝ))
        (mfderiv 𝓘(ℝ, ℝ) I (F ∘ c) (a * t + b) (1 : ℝ)) = 4 := by
      rw [hf, hpres, hunit, mul_one]
    have hh := mfderiv_comp_affine (F ∘ c) (hF.contMDiff.comp hc) a b t
    change g.inner (F (c (a * t + b)))
      (mfderiv 𝓘(ℝ, ℝ) I (fun s => (F ∘ c) (a * s + b)) t (1 : ℝ))
      (mfderiv 𝓘(ℝ, ℝ) I (fun s => (F ∘ c) (a * s + b)) t (1 : ℝ)) = 1
    rw [hh]
    simp only [map_smul, smul_apply, smul_eq_mul]
    rw [hspeed]
    nlinarith only [ha]

private theorem quarter_negative : (-1 / 4 : ℝ) < 0 := by norm_num

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E₃ H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem normalizedUniversalCoverProjection_rayTo_half_unit_geodesic
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
    ∀ (i : E₃ ≃ₗᵢ[ℝ] TangentSpace I (UniversalCover.basePoint (X := M))) (y : H₃) (ξ : B₃),
      let γ := fun t : ℝ => normalizedUniversalCoverProjection g hg (-1 / 4) quarter_negative
        x₀ hsec i (rayTo y ξ (t / 2))
      ContMDiff 𝓘(ℝ, ℝ) I ∞ γ ∧ IsGeodesic g γ ∧
        ∀ t : ℝ, g.inner (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))
          (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)) = 1 := by
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
  intro i y ξ
  let F := normalizedUniversalCoverProjection g hg (-1 / 4) quarter_negative x₀ hsec i
  have hF : IsLocalDiffeomorph I₃ I ∞ F :=
    normalizedUniversalCoverProjection_isLocalDiffeomorph g hg (-1 / 4) quarter_negative x₀ hsec i
  have hpres (p : H₃) (v w : TangentSpace I₃ p) :
      g.inner (F p) (mfderiv I₃ I F p v) (mfderiv I₃ I F p w) =
      4 * Hyperboloid.riemannianMetric.inner ((Hyperboloid.hUpperDiffeomorph 3) p)
        (mfderiv I₃ I₃ (Hyperboloid.hUpperDiffeomorph 3) p v)
        (mfderiv I₃ I₃ (Hyperboloid.hUpperDiffeomorph 3) p w) := by
    have h := normalizedUniversalCoverProjection_inner g hg (-1 / 4) quarter_negative x₀ hsec i p v w
    have hfactor : (-(-1 / 4 : ℝ))⁻¹ = 4 := by norm_num
    rw [hfactor] at h
    exact h
  have hc : ContMDiff 𝓘(ℝ, ℝ) I₃ ∞ (rayTo y ξ) :=
    (HorosphereProjection.contMDiff_rayTo ξ ∞).comp (contMDiff_const.prodMk contMDiff_id)
  exact projected_affine_geodesic_properties g F hF hpres (rayTo y ξ) hc
    (Hyperboloid.isGeodesic_hUpperIsometryEquiv_rayTo y ξ)
    (Hyperboloid.hUpperIsometryEquiv_rayTo_unit_speed y ξ) (1 / 2) 0 (by norm_num)
    (fun t => t / 2) (by funext t; ring)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem normalizedUniversalCoverProjection_rayTo_neg_half_unit_geodesic
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
    ∀ (i : E₃ ≃ₗᵢ[ℝ] TangentSpace I (UniversalCover.basePoint (X := M))) (y : H₃) (ξ : B₃),
      let γ := fun t : ℝ => normalizedUniversalCoverProjection g hg (-1 / 4) quarter_negative
        x₀ hsec i (rayTo y ξ (-t / 2))
      ContMDiff 𝓘(ℝ, ℝ) I ∞ γ ∧ IsGeodesic g γ ∧
        ∀ t : ℝ, g.inner (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))
          (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)) = 1 := by
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
  intro i y ξ
  let F := normalizedUniversalCoverProjection g hg (-1 / 4) quarter_negative x₀ hsec i
  have hF : IsLocalDiffeomorph I₃ I ∞ F :=
    normalizedUniversalCoverProjection_isLocalDiffeomorph g hg (-1 / 4) quarter_negative x₀ hsec i
  have hpres (p : H₃) (v w : TangentSpace I₃ p) :
      g.inner (F p) (mfderiv I₃ I F p v) (mfderiv I₃ I F p w) =
      4 * Hyperboloid.riemannianMetric.inner ((Hyperboloid.hUpperDiffeomorph 3) p)
        (mfderiv I₃ I₃ (Hyperboloid.hUpperDiffeomorph 3) p v)
        (mfderiv I₃ I₃ (Hyperboloid.hUpperDiffeomorph 3) p w) := by
    have h := normalizedUniversalCoverProjection_inner g hg (-1 / 4) quarter_negative x₀ hsec i p v w
    have hfactor : (-(-1 / 4 : ℝ))⁻¹ = 4 := by norm_num
    rw [hfactor] at h
    exact h
  have hc : ContMDiff 𝓘(ℝ, ℝ) I₃ ∞ (rayTo y ξ) :=
    (HorosphereProjection.contMDiff_rayTo ξ ∞).comp (contMDiff_const.prodMk contMDiff_id)
  exact projected_affine_geodesic_properties g F hF hpres (rayTo y ξ) hc
    (Hyperboloid.isGeodesic_hUpperIsometryEquiv_rayTo y ξ)
    (Hyperboloid.hUpperIsometryEquiv_rayTo_unit_speed y ξ) (-1 / 2) 0 (by norm_num)
    (fun t => -t / 2) (by funext t; ring)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem normalizedUniversalCoverProjection_geodFromTo_half_unit_geodesic
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
    ∀ (i : E₃ ≃ₗᵢ[ℝ] TangentSpace I (UniversalCover.basePoint (X := M))) (x y : H₃) (hxy : x ≠ y) (a : ℝ),
      let γ := fun t : ℝ => normalizedUniversalCoverProjection g hg (-1 / 4) quarter_negative
        x₀ hsec i (HyperbolicConvexity.geodFromTo x y hxy (a + t / 2))
      ContMDiff 𝓘(ℝ, ℝ) I ∞ γ ∧ IsGeodesic g γ ∧
        ∀ t : ℝ, g.inner (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))
          (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)) = 1 := by
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
  intro i x y hxy a
  let F := normalizedUniversalCoverProjection g hg (-1 / 4) quarter_negative x₀ hsec i
  have hF : IsLocalDiffeomorph I₃ I ∞ F :=
    normalizedUniversalCoverProjection_isLocalDiffeomorph g hg (-1 / 4) quarter_negative x₀ hsec i
  have hpres (p : H₃) (v w : TangentSpace I₃ p) :
      g.inner (F p) (mfderiv I₃ I F p v) (mfderiv I₃ I F p w) =
      4 * Hyperboloid.riemannianMetric.inner ((Hyperboloid.hUpperDiffeomorph 3) p)
        (mfderiv I₃ I₃ (Hyperboloid.hUpperDiffeomorph 3) p v)
        (mfderiv I₃ I₃ (Hyperboloid.hUpperDiffeomorph 3) p w) := by
    have h := normalizedUniversalCoverProjection_inner g hg (-1 / 4) quarter_negative x₀ hsec i p v w
    have hfactor : (-(-1 / 4 : ℝ))⁻¹ = 4 := by norm_num
    rw [hfactor] at h
    exact h
  have hcJ : ContMDiff 𝓘(ℝ, ℝ) I₃ ∞
      (fun t => Hyperboloid.hUpperIsometryEquiv 3 (HyperbolicConvexity.geodFromTo x y hxy t)) := by
    simp_rw [Hyperboloid.hUpperIsometryEquiv_geodFromTo]
    exact Hyperboloid.contMDiff_geodesicLine _ _ _ _
  have hc : ContMDiff 𝓘(ℝ, ℝ) I₃ ∞ (HyperbolicConvexity.geodFromTo x y hxy) := by
    have h := (Hyperboloid.hUpperDiffeomorph 3).symm.contMDiff.comp hcJ
    simpa only [Function.comp_def, Hyperboloid.hUpperDiffeomorph_apply,
      Hyperboloid.hUpperDiffeomorph_symm_apply, IsometryEquiv.symm_apply_apply] using h
  exact projected_affine_geodesic_properties g F hF hpres
    (HyperbolicConvexity.geodFromTo x y hxy) hc
    (Hyperboloid.isGeodesic_hUpperIsometryEquiv_geodFromTo x y hxy)
    (Hyperboloid.hUpperIsometryEquiv_geodFromTo_unit_speed x y hxy) (1 / 2) a (by norm_num)
    (fun t => a + t / 2) (by funext t; ring)

end DifferentialGeometry.Geometry.Hyperbolic
