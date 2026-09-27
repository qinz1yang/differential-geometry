import DifferentialGeometry.Geometry.Comparison.Nonnegative.RauchParallel
import DifferentialGeometry.Geometry.Comparison.Variation.GeodesicVariationJacobi
import DifferentialGeometry.Geometry.Comparison.HopfRinow.GeodesicSpeedBound
import DifferentialGeometry.Geometry.Exponential.Variation.Jacobi

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set
open scoped Topology ContDiff Manifold NNReal
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

namespace DifferentialGeometry.Geometry.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [ConnectedSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace



omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M]
  [ConnectedSpace M] [FiniteDimensional ℝ E] in
theorem arcLength_le_of_speed_le (g : SmoothRiemannianMetric I M) {η : ℝ → M}
    {a b : ℝ} (hab : a ≤ b)
    (hspeed : ∀ t ∈ Icc a b,
      g.inner (η t) (mfderiv 𝓘(ℝ, ℝ) I η t (1 : ℝ))
        (mfderiv 𝓘(ℝ, ℝ) I η t (1 : ℝ)) ≤ 1) :
    arcLength (I := I) g η a b ≤ b - a := by
  classical
  set F : ℝ → ℝ := fun t =>
    Real.sqrt (g.inner (η t) (mfderiv 𝓘(ℝ, ℝ) I η t (1 : ℝ))
      (mfderiv 𝓘(ℝ, ℝ) I η t (1 : ℝ))) with hF
  have hle : ∀ t ∈ Icc a b, F t ≤ 1 := by
    intro t ht
    calc F t ≤ Real.sqrt 1 := Real.sqrt_le_sqrt (hspeed t ht)
      _ = 1 := Real.sqrt_one
  have harc : arcLength (I := I) g η a b = ∫ t in a..b, F t := rfl
  rw [harc]
  by_cases hint : IntervalIntegrable F MeasureTheory.volume a b
  · calc (∫ t in a..b, F t) ≤ ∫ _t in a..b, (1 : ℝ) :=
          intervalIntegral.integral_mono_on hab hint intervalIntegrable_const hle
      _ = b - a := by simp
  · rw [intervalIntegral.integral_undef hint]
    linarith

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]



omit [ConnectedSpace M] in
theorem parallelShift_eq_intrinsicGeodesic (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (y : M) (u : TangentSpace I y)
    (ξ : ∀ t : ℝ, TangentSpace I (intrinsicGeodesic (I := I) g hEnorm y u t))
    (t : ℝ) :
    (fun h : ℝ => parallelShift (I := I) g hEnorm y u ξ h t)
      = intrinsicGeodesic (I := I) g hEnorm
          (intrinsicGeodesic (I := I) g hEnorm y u t) (ξ t) := by
  funext h
  rw [parallelShift, expMapIntrinsic_def]
  exact intrinsicGeodesic_smul (I := I) g hEnorm _ (ξ t) h

omit [ConnectedSpace M] in
theorem parallelShift_isGeodesic (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (y : M) (u : TangentSpace I y)
    (ξ : ∀ t : ℝ, TangentSpace I (intrinsicGeodesic (I := I) g hEnorm y u t))
    (t : ℝ) :
    Geodesic.IsGeodesic (I := I) g
      (fun h : ℝ => parallelShift (I := I) g hEnorm y u ξ h t) := by
  rw [parallelShift_eq_intrinsicGeodesic (I := I) g hEnorm y u ξ t]
  exact intrinsicGeodesic_isGeodesic (I := I) g hEnorm _ (ξ t)

omit [ConnectedSpace M] in
theorem parallelShift_transverse_velocity_zero (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (y : M) (u : TangentSpace I y)
    (ξ : ∀ t : ℝ, TangentSpace I (intrinsicGeodesic (I := I) g hEnorm y u t))
    (t : ℝ) :
    (mfderiv 𝓘(ℝ, ℝ) I (fun h : ℝ => parallelShift (I := I) g hEnorm y u ξ h t)
      0 (1 : ℝ) : E) = (ξ t : E) := by
  rw [parallelShift_eq_intrinsicGeodesic (I := I) g hEnorm y u ξ t]
  exact intrinsicGeodesic_mfderiv_zero (I := I) g hEnorm _ (ξ t)

omit [ConnectedSpace M] in
theorem exists_smooth_eq_of_isParallelPerpUnitField
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (y : M) (u : TangentSpace I y)
    (ξ : ∀ t : ℝ, TangentSpace I (intrinsicGeodesic (I := I) g hEnorm y u t))
    {L : ℝ} (hL : 0 < L)
    (hξ : IsParallelPerpUnitField (I := I) g hEnorm y u ξ L) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ V : ∀ t : ℝ,
        TangentSpace I (intrinsicGeodesic (I := I) g hEnorm y u t),
      (∀ t ∈ Icc (0 : ℝ) L, V t = ξ t) ∧
      (∀ t ∈ Ioo (-δ) (L + δ), covDerivAlong (I := I) g
        (intrinsicGeodesic (I := I) g hEnorm y u) V t = 0) ∧
      ContMDiffOn 𝓘(ℝ, ℝ) I.tangent ∞
        (fun t : ℝ => TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (intrinsicGeodesic (I := I) g hEnorm y u t) (V t))
        (Ioo (-δ) (L + δ)) := by
  classical
  have hsm : ContMDiff 𝓘(ℝ, ℝ) I ∞ (intrinsicGeodesic (I := I) g hEnorm y u) :=
    intrinsicGeodesic_contMDiff (I := I) g hEnorm y u
  have hsm2 : ContMDiff 𝓘(ℝ, ℝ) I ((2 : ℕ) : ℕ∞)
      (intrinsicGeodesic (I := I) g hEnorm y u) :=
    hsm.of_le (by exact_mod_cast le_top)
  obtain ⟨δ, hδ, V, hV0, hVdiff, hVpar, hVsmooth⟩ :=
    parallelTransport_section_contMDiffOn_Ioo (I := I) g
      (intrinsicGeodesic (I := I) g hEnorm y u) hsm hL (ξ 0)
  have hsub : Icc (0 : ℝ) L ⊆ Ioo (-δ) (L + δ) := fun t ht =>
    ⟨by linarith [ht.1, hδ], by linarith [ht.2, hδ]⟩
  refine ⟨δ, hδ, V, ?_, hVpar, hVsmooth⟩
  exact parallel_transport_unique_of_eq_at_point (I := I) g
    (intrinsicGeodesic (I := I) g hEnorm y u) (N := 2) le_rfl hsm2
    V ξ (fun t ht => hVdiff t (hsub ht)) hξ.1
    (fun t ht => hVpar t (hsub ht)) hξ.2.1 ⟨le_rfl, hL.le⟩ hV0



omit [ConnectedSpace M] in
theorem isJacobiAlong_parallelShift_velocity (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (y : M) (u : TangentSpace I y)
    (ξ : ∀ t : ℝ, TangentSpace I (intrinsicGeodesic (I := I) g hEnorm y u t))
    (hsm : IsSmoothVariation (I := I)
      (fun t h : ℝ => parallelShift (I := I) g hEnorm y u ξ h t))
    (t₀ : ℝ) :
    IsJacobiAlong (I := I) g
      (fun h : ℝ => parallelShift (I := I) g hEnorm y u ξ h t₀)
      (fun h : ℝ => mfderiv 𝓘(ℝ, ℝ) I
        (fun r : ℝ => parallelShift (I := I) g hEnorm y u ξ h r) t₀ (1 : ℝ)) :=
  isJacobiAlong_varFst_of_isGeodesic_at (I := I) g
    (fun t h : ℝ => parallelShift (I := I) g hEnorm y u ξ h t) hsm
    (fun a => parallelShift_isGeodesic (I := I) g hEnorm y u ξ a) t₀

omit [ConnectedSpace M] in
theorem inner_velocity_intrinsicGeodesic (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (y : M) (u : TangentSpace I y)
    (hu : g.inner y u u = 1) (t : ℝ) :
    g.inner (intrinsicGeodesic (I := I) g hEnorm y u t)
        (mfderiv 𝓘(ℝ, ℝ) I (intrinsicGeodesic (I := I) g hEnorm y u) t (1 : ℝ))
        (mfderiv 𝓘(ℝ, ℝ) I (intrinsicGeodesic (I := I) g hEnorm y u) t (1 : ℝ))
      = 1 := by
  have hC1 : ContMDiff 𝓘(ℝ, ℝ) I 1 (intrinsicGeodesic (I := I) g hEnorm y u) :=
    (intrinsicGeodesic_contMDiff (I := I) g hEnorm y u).of_le
      (by exact_mod_cast le_top)
  have hzero : intrinsicGeodesic (I := I) g hEnorm y u 0 = y :=
    intrinsicGeodesic_zero (I := I) g hEnorm y u
  have hvel : (mfderiv 𝓘(ℝ, ℝ) I (intrinsicGeodesic (I := I) g hEnorm y u) 0
      (1 : ℝ) : E) = (u : E) :=
    intrinsicGeodesic_mfderiv_zero (I := I) g hEnorm y u
  have key : g.inner (intrinsicGeodesic (I := I) g hEnorm y u 0)
      (mfderiv 𝓘(ℝ, ℝ) I (intrinsicGeodesic (I := I) g hEnorm y u) 0 (1 : ℝ))
      (mfderiv 𝓘(ℝ, ℝ) I (intrinsicGeodesic (I := I) g hEnorm y u) 0 (1 : ℝ))
      = 1 := by
    rw [hvel]
    have hpt : g.inner (intrinsicGeodesic (I := I) g hEnorm y u 0)
        (show TangentSpace I (intrinsicGeodesic (I := I) g hEnorm y u 0) from u)
        (show TangentSpace I (intrinsicGeodesic (I := I) g hEnorm y u 0) from u)
        = g.inner y u u := by rw [hzero]
    rw [hpt, hu]
  exact (DifferentialGeometry.Geometry.Riemannian.HopfRinow.geodesic_speed_constant
    (I := I) g (intrinsicGeodesic_isGeodesic (I := I) g hEnorm y u) hC1 t 0).trans key

omit [ConnectedSpace M] in
theorem parallelShift_velocity_zero (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (y : M) (u : TangentSpace I y)
    (ξ : ∀ t : ℝ, TangentSpace I (intrinsicGeodesic (I := I) g hEnorm y u t))
    (t : ℝ) :
    (mfderiv 𝓘(ℝ, ℝ) I
        (fun r : ℝ => parallelShift (I := I) g hEnorm y u ξ 0 r) t (1 : ℝ) : E)
      = (mfderiv 𝓘(ℝ, ℝ) I
        (intrinsicGeodesic (I := I) g hEnorm y u) t (1 : ℝ) : E) :=
  congrArg (fun c : ℝ → M => (mfderiv 𝓘(ℝ, ℝ) I c t (1 : ℝ) : E))
    (funext (parallelShift_zero (I := I) g hEnorm y u ξ))

omit [ConnectedSpace M] in
theorem inner_parallelShift_velocity_zero (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (y : M) (u : TangentSpace I y)
    (hu : g.inner y u u = 1)
    (ξ : ∀ t : ℝ, TangentSpace I (intrinsicGeodesic (I := I) g hEnorm y u t))
    (t : ℝ) :
    g.inner (parallelShift (I := I) g hEnorm y u ξ 0 t)
        (mfderiv 𝓘(ℝ, ℝ) I
          (fun r : ℝ => parallelShift (I := I) g hEnorm y u ξ 0 r) t (1 : ℝ))
        (mfderiv 𝓘(ℝ, ℝ) I
          (fun r : ℝ => parallelShift (I := I) g hEnorm y u ξ 0 r) t (1 : ℝ))
      = 1 := by
  have hcongr := congrArg
    (fun c : ℝ → M => g.inner (c t) (mfderiv 𝓘(ℝ, ℝ) I c t (1 : ℝ))
      (mfderiv 𝓘(ℝ, ℝ) I c t (1 : ℝ)))
    (funext (parallelShift_zero (I := I) g hEnorm y u ξ))
  refine hcongr.trans ?_
  exact inner_velocity_intrinsicGeodesic (I := I) g hEnorm y u hu t

omit [ConnectedSpace M] in
theorem covDerivAlong_parallelShift_velocity_zero (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (y : M) (u : TangentSpace I y)
    (ξ : ∀ t : ℝ, TangentSpace I (intrinsicGeodesic (I := I) g hEnorm y u t))
    (hsm : IsSmoothVariation (I := I)
      (fun t h : ℝ => parallelShift (I := I) g hEnorm y u ξ h t))
    {L : ℝ} (hξ : IsParallelPerpUnitField (I := I) g hEnorm y u ξ L)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Icc (0 : ℝ) L) :
    covDerivAlong (I := I) g
        (fun h : ℝ => parallelShift (I := I) g hEnorm y u ξ h t₀)
        (fun h : ℝ => mfderiv 𝓘(ℝ, ℝ) I
          (fun r : ℝ => parallelShift (I := I) g hEnorm y u ξ h r) t₀ (1 : ℝ)) 0
      = 0 := by
  classical
  have hsymm := covDerivAlong_varFst_eq_covDerivAlong_varSnd (I := I) g
    (fun t h : ℝ => parallelShift (I := I) g hEnorm y u ξ h t) hsm t₀ 0
  simp only [covSnd, covFst, varFst, varSnd] at hsymm
  rw [hsymm]
  have hcong := covDerivAlong_congr_curve (I := I) g
    (γ := fun r : ℝ => parallelShift (I := I) g hEnorm y u ξ 0 r)
    (γ' := intrinsicGeodesic (I := I) g hEnorm y u)
    (fun r : ℝ => mfderiv 𝓘(ℝ, ℝ) I
      (fun v : ℝ => parallelShift (I := I) g hEnorm y u ξ v r) 0 (1 : ℝ)) ξ
    (t := t₀)
    (Filter.Eventually.of_forall (parallelShift_zero (I := I) g hEnorm y u ξ))
    (Filter.Eventually.of_forall
      (parallelShift_transverse_velocity_zero (I := I) g hEnorm y u ξ))
  have hzero : (covDerivAlong (I := I) g
      (intrinsicGeodesic (I := I) g hEnorm y u) ξ t₀ : E) = (0 : E) := by
    rw [hξ.2.1 t₀ ht₀]
    rfl
  exact hcong.trans hzero



def HasParallelVariationSpeedBound (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) : Prop :=
  ∀ (x : M) (L : ℝ), 0 < L → ∃ ρ : ℝ, 0 < ρ ∧ ∀ y : M, dist x y < ρ →
    ∀ u : TangentSpace I y, g.inner y u u = 1 →
      ∀ ξ : ∀ t : ℝ, TangentSpace I (intrinsicGeodesic (I := I) g hEnorm y u t),
        IsParallelPerpUnitField (I := I) g hEnorm y u ξ L →
        ∀ h : ℝ, 0 ≤ h → h < ρ →
          ContMDiffOn 𝓘(ℝ, ℝ) I 1
              (parallelShift (I := I) g hEnorm y u ξ h) (Icc 0 L) ∧
            ∀ t ∈ Icc (0 : ℝ) L,
              g.inner (parallelShift (I := I) g hEnorm y u ξ h t)
                  (mfderiv 𝓘(ℝ, ℝ) I
                    (parallelShift (I := I) g hEnorm y u ξ h) t (1 : ℝ))
                  (mfderiv 𝓘(ℝ, ℝ) I
                    (parallelShift (I := I) g hEnorm y u ξ h) t (1 : ℝ)) ≤ 1

def HasParallelVariationC1 (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) : Prop :=
  ∀ (x : M) (L : ℝ), 0 < L → ∃ ρ : ℝ, 0 < ρ ∧ ∀ y : M, dist x y < ρ →
    ∀ u : TangentSpace I y, g.inner y u u = 1 →
      ∀ ξ : ∀ t : ℝ, TangentSpace I (intrinsicGeodesic (I := I) g hEnorm y u t),
        IsParallelPerpUnitField (I := I) g hEnorm y u ξ L →
        ∀ h : ℝ, 0 ≤ h → h < ρ →
          ContMDiffOn 𝓘(ℝ, ℝ) I 1
            (parallelShift (I := I) g hEnorm y u ξ h) (Icc 0 L)

def HasParallelVariationFocalBound (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) : Prop :=
  ∀ (x : M) (L : ℝ), 0 < L → ∃ ρ : ℝ, 0 < ρ ∧ ∀ y : M, dist x y < ρ →
    ∀ u : TangentSpace I y, g.inner y u u = 1 →
      ∀ ξ : ∀ t : ℝ, TangentSpace I (intrinsicGeodesic (I := I) g hEnorm y u t),
        IsParallelPerpUnitField (I := I) g hEnorm y u ξ L →
        ∀ h : ℝ, 0 ≤ h → h < ρ → ∀ t ∈ Icc (0 : ℝ) L,
          g.inner (parallelShift (I := I) g hEnorm y u ξ h t)
              (mfderiv 𝓘(ℝ, ℝ) I
                (parallelShift (I := I) g hEnorm y u ξ h) t (1 : ℝ))
              (mfderiv 𝓘(ℝ, ℝ) I
                (parallelShift (I := I) g hEnorm y u ξ h) t (1 : ℝ))
            ≤ g.inner (parallelShift (I := I) g hEnorm y u ξ 0 t)
              (mfderiv 𝓘(ℝ, ℝ) I
                (fun r : ℝ => parallelShift (I := I) g hEnorm y u ξ 0 r) t (1 : ℝ))
              (mfderiv 𝓘(ℝ, ℝ) I
                (fun r : ℝ => parallelShift (I := I) g hEnorm y u ξ 0 r) t (1 : ℝ))

omit [ConnectedSpace M] in
theorem hasParallelVariationSpeedBound_of_focalBound
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hC1 : HasParallelVariationC1 (I := I) g hEnorm)
    (hfocal : HasParallelVariationFocalBound (I := I) g hEnorm) :
    HasParallelVariationSpeedBound (I := I) g hEnorm := by
  intro x L hL
  obtain ⟨ρ₁, hρ₁, hb₁⟩ := hC1 x L hL
  obtain ⟨ρ₂, hρ₂, hb₂⟩ := hfocal x L hL
  refine ⟨min ρ₁ ρ₂, lt_min hρ₁ hρ₂, fun y hy u hu ξ hξ h hh0 hhρ => ?_⟩
  have hy₁ : dist x y < ρ₁ := lt_of_lt_of_le hy (min_le_left _ _)
  have hy₂ : dist x y < ρ₂ := lt_of_lt_of_le hy (min_le_right _ _)
  have hh₁ : h < ρ₁ := lt_of_lt_of_le hhρ (min_le_left _ _)
  have hh₂ : h < ρ₂ := lt_of_lt_of_le hhρ (min_le_right _ _)
  refine ⟨hb₁ y hy₁ u hu ξ hξ h hh0 hh₁, fun t ht => ?_⟩
  exact le_of_le_of_eq (hb₂ y hy₂ u hu ξ hξ h hh0 hh₂ t ht)
    (inner_parallelShift_velocity_zero (I := I) g hEnorm y u hu ξ t)

omit [ConnectedSpace M] in
theorem hasParallelVariationLengthBound_of_speedBound
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hspeed : HasParallelVariationSpeedBound (I := I) g hEnorm) :
    HasParallelVariationLengthBound (I := I) g hEnorm := by
  intro x L hL
  obtain ⟨ρ, hρ, hbound⟩ := hspeed x L hL
  refine ⟨ρ, hρ, fun y hy u hu ξ hξ h hh0 hhρ => ?_⟩
  obtain ⟨hsmooth, hpt⟩ := hbound y hy u hu ξ hξ h hh0 hhρ
  refine ⟨hsmooth, fun t₁ ht₁ t₂ ht₂ hle => ?_⟩
  refine arcLength_le_of_speed_le (I := I) g hle (fun t ht => ?_)
  exact hpt t ⟨le_trans ht₁.1 ht.1, le_trans ht.2 ht₂.2⟩

omit [ConnectedSpace M] in
theorem hasParallelShiftBound_of_speedBound
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hspeed : HasParallelVariationSpeedBound (I := I) g hEnorm) :
    HasParallelShiftBound (I := I) g hEnorm :=
  hasParallelShiftBound_of_lengthBound (I := I) g hEnorm
    (hasParallelVariationLengthBound_of_speedBound (I := I) g hEnorm hspeed)

omit [ConnectedSpace M] in
theorem hasParallelVariationLengthBound_of_focalBound
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hC1 : HasParallelVariationC1 (I := I) g hEnorm)
    (hfocal : HasParallelVariationFocalBound (I := I) g hEnorm) :
    HasParallelVariationLengthBound (I := I) g hEnorm :=
  hasParallelVariationLengthBound_of_speedBound (I := I) g hEnorm
    (hasParallelVariationSpeedBound_of_focalBound (I := I) g hEnorm hC1 hfocal)

omit [ConnectedSpace M] in
theorem hasParallelShiftBound_of_focalBound
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hC1 : HasParallelVariationC1 (I := I) g hEnorm)
    (hfocal : HasParallelVariationFocalBound (I := I) g hEnorm) :
    HasParallelShiftBound (I := I) g hEnorm :=
  hasParallelShiftBound_of_lengthBound (I := I) g hEnorm
    (hasParallelVariationLengthBound_of_focalBound (I := I) g hEnorm hC1 hfocal)

end DifferentialGeometry.Geometry.Topology

end
