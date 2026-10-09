import DifferentialGeometry.Geometry.Comparison.Soul.SoulConvexCore
import DifferentialGeometry.Geometry.Comparison.Variation.PerpendicularFrame.Basic
import DifferentialGeometry.Geometry.Comparison.Variation.Jacobi.Basic
import DifferentialGeometry.Geometry.Comparison.Variation.Curve.ArcLength
import DifferentialGeometry.Geometry.Geodesic.Maximal.Interval

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

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [ConnectedSpace M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)] in
private theorem rauch_toReal_eq_dist (p q : M) :
    (riemannianEDist I p q).toReal = dist p q := by
  rw [← IsRiemannianManifold.out (I := I), edist_dist,
    ENNReal.toReal_ofReal dist_nonneg]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [SigmaCompactSpace M] [ConnectedSpace M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)] in
theorem dist_le_arcLength (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) {η : ℝ → M} {a b : ℝ} (hab : a ≤ b)
    (hη : ContMDiffOn 𝓘(ℝ, ℝ) I 1 η (Icc a b)) :
    dist (η a) (η b) ≤ arcLength (I := I) g η a b := by
  have hnn : 0 ≤ arcLength (I := I) g η a b := by
    unfold arcLength
    exact intervalIntegral.integral_nonneg hab fun _ _ => Real.sqrt_nonneg _
  have h := Geodesic.riemannianEDist_le_arcLength (I := I) g hab hη
    fun t _ => hEnorm (η t) _
  rw [← rauch_toReal_eq_dist (I := I)]
  calc (riemannianEDist I (η a) (η b)).toReal
      ≤ (ENNReal.ofReal (arcLength (I := I) g η a b)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top h
    _ = arcLength (I := I) g η a b := ENNReal.toReal_ofReal hnn



omit [ConnectedSpace M] in
theorem exists_parallel_perp_unit_field
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    {y : M} (u w : TangentSpace I y)
    (hw : g.inner y w w = 1) (huw : g.inner y u w = 0) {L : ℝ} (hL : 0 < L) :
    ∃ ξ : ∀ t : ℝ, TangentSpace I (intrinsicGeodesic (I := I) g hEnorm y u t),
      ξ 0 = w ∧
      (∀ t ∈ Icc (0 : ℝ) L, DifferentiableAt ℝ
        (chartRepAt (I := I) (intrinsicGeodesic (I := I) g hEnorm y u) ξ t) t) ∧
      (∀ t ∈ Icc (0 : ℝ) L,
        covDerivAlong (I := I) g (intrinsicGeodesic (I := I) g hEnorm y u) ξ t = 0) ∧
      (∀ t ∈ Icc (0 : ℝ) L,
        g.inner (intrinsicGeodesic (I := I) g hEnorm y u t) (ξ t) (ξ t) = 1) ∧
      (∀ t ∈ Icc (0 : ℝ) L,
        g.inner (intrinsicGeodesic (I := I) g hEnorm y u t) (ξ t)
          (curveVelocity (I := I) (intrinsicGeodesic (I := I) g hEnorm y u) t) = 0) := by
  set τ : ℝ → M := intrinsicGeodesic (I := I) g hEnorm y u with hτdef
  have hτ0 : τ 0 = y := intrinsicGeodesic_zero (I := I) g hEnorm y u
  have hsm : ContMDiff 𝓘(ℝ, ℝ) I ∞ τ :=
    intrinsicGeodesic_contMDiff (I := I) g hEnorm y u
  have hsm2 : ContMDiff 𝓘(ℝ, ℝ) I ((2 : ℕ) : ℕ∞) τ :=
    hsm.of_le (by exact_mod_cast le_top)
  have hgeo : Geodesic.IsGeodesic (I := I) g τ :=
    intrinsicGeodesic_isGeodesic (I := I) g hEnorm y u
  obtain ⟨V, hV0, hVdiff, hVpar⟩ :=
    exists_parallel_transport_on_Icc (I := I) g τ (N := 2) le_rfl hsm2 hL
      (show TangentSpace I (τ 0) from w)
  refine ⟨V, hV0, hVdiff, hVpar, ?_, ?_⟩
  · intro t ht
    have hconst := parallel_transport_preserves_inner_product (I := I) g τ
      (N := 2) le_rfl hsm2 V V hVdiff hVdiff hVpar hVpar t ht
    rw [hconst, hV0]
    have : g.inner (τ 0) (show TangentSpace I (τ 0) from w)
        (show TangentSpace I (τ 0) from w) = g.inner y w w := by rw [hτ0]
    rw [this, hw]
  · intro t ht
    have hperp0 : g.inner (τ 0) (V 0)
        (mfderiv 𝓘(ℝ, ℝ) I τ 0 (1 : ℝ) : E) = 0 := by
      rw [hV0]
      have hvel : (mfderiv 𝓘(ℝ, ℝ) I τ 0 (1 : ℝ) : E) = u :=
        intrinsicGeodesic_mfderiv_zero (I := I) g hEnorm y u
      rw [hvel]
      have : g.inner (τ 0) (show TangentSpace I (τ 0) from w)
          (show TangentSpace I (τ 0) from u) = g.inner y w u := by rw [hτ0]
      rw [this, g.symm y w u]
      exact huw
    exact perp_to_velocity_preserved_of_parallel (I := I) g τ hsm hgeo V
      hVdiff hVpar hperp0 t ht

def IsParallelPerpUnitField (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (y : M) (u : TangentSpace I y)
    (ξ : ∀ t : ℝ, TangentSpace I (intrinsicGeodesic (I := I) g hEnorm y u t))
    (L : ℝ) : Prop :=
  (∀ t ∈ Icc (0 : ℝ) L, DifferentiableAt ℝ
      (chartRepAt (I := I) (intrinsicGeodesic (I := I) g hEnorm y u) ξ t) t) ∧
    (∀ t ∈ Icc (0 : ℝ) L,
      covDerivAlong (I := I) g (intrinsicGeodesic (I := I) g hEnorm y u) ξ t = 0) ∧
    (∀ t ∈ Icc (0 : ℝ) L,
      g.inner (intrinsicGeodesic (I := I) g hEnorm y u t) (ξ t) (ξ t) = 1) ∧
    (∀ t ∈ Icc (0 : ℝ) L,
      g.inner (intrinsicGeodesic (I := I) g hEnorm y u t) (ξ t)
        (curveVelocity (I := I) (intrinsicGeodesic (I := I) g hEnorm y u) t) = 0)

omit [ConnectedSpace M] in
theorem exists_isParallelPerpUnitField
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    {y : M} (u w : TangentSpace I y)
    (hw : g.inner y w w = 1) (huw : g.inner y u w = 0) {L : ℝ} (hL : 0 < L) :
    ∃ ξ : ∀ t : ℝ, TangentSpace I (intrinsicGeodesic (I := I) g hEnorm y u t),
      ξ 0 = w ∧ IsParallelPerpUnitField (I := I) g hEnorm y u ξ L := by
  obtain ⟨ξ, h0, h1, h2, h3, h4⟩ :=
    exists_parallel_perp_unit_field (I := I) g hEnorm u w hw huw hL
  exact ⟨ξ, h0, h1, h2, h3, h4⟩



def parallelShift (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (y : M) (u : TangentSpace I y)
    (ξ : ∀ t : ℝ, TangentSpace I (intrinsicGeodesic (I := I) g hEnorm y u t))
    (h t : ℝ) : M :=
  expMapIntrinsic (I := I) g hEnorm (intrinsicGeodesic (I := I) g hEnorm y u t)
    (h • ξ t)

omit [ConnectedSpace M] in
theorem parallelShift_apply (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (y : M) (u : TangentSpace I y)
    (ξ : ∀ t : ℝ, TangentSpace I (intrinsicGeodesic (I := I) g hEnorm y u t))
    (h t : ℝ) :
    parallelShift (I := I) g hEnorm y u ξ h t
      = expMapIntrinsic (I := I) g hEnorm
          (intrinsicGeodesic (I := I) g hEnorm y u t) (h • ξ t) := rfl

omit [ConnectedSpace M] in
@[simp] theorem parallelShift_zero (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (y : M) (u : TangentSpace I y)
    (ξ : ∀ t : ℝ, TangentSpace I (intrinsicGeodesic (I := I) g hEnorm y u t))
    (t : ℝ) :
    parallelShift (I := I) g hEnorm y u ξ 0 t
      = intrinsicGeodesic (I := I) g hEnorm y u t := by
  rw [parallelShift, zero_smul, expMapIntrinsic_zero]

omit [ConnectedSpace M] in
theorem parallelShift_zero_time (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (y : M) (u w : TangentSpace I y)
    (ξ : ∀ t : ℝ, TangentSpace I (intrinsicGeodesic (I := I) g hEnorm y u t))
    (hξ0 : ξ 0 = w) (h : ℝ) :
    parallelShift (I := I) g hEnorm y u ξ h 0
      = intrinsicGeodesic (I := I) g hEnorm y w h := by
  have hτ0 : intrinsicGeodesic (I := I) g hEnorm y u 0 = y :=
    intrinsicGeodesic_zero (I := I) g hEnorm y u
  have hbase : parallelShift (I := I) g hEnorm y u ξ h 0
      = expMapIntrinsic (I := I) g hEnorm y (h • w) := by
    rw [parallelShift, hξ0]
    exact congrArg (fun z : M => expMapIntrinsic (I := I) g hEnorm z
      (h • (show TangentSpace I z from w))) hτ0
  rw [hbase, expMapIntrinsic_def]
  exact intrinsicGeodesic_smul (I := I) g hEnorm y w h



def HasParallelVariationLengthBound (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) : Prop :=
  ∀ (x : M) (L : ℝ), 0 < L → ∃ ρ : ℝ, 0 < ρ ∧ ∀ y : M, dist x y < ρ →
    ∀ u : TangentSpace I y, g.inner y u u = 1 →
      ∀ ξ : ∀ t : ℝ, TangentSpace I (intrinsicGeodesic (I := I) g hEnorm y u t),
        IsParallelPerpUnitField (I := I) g hEnorm y u ξ L →
        ∀ h : ℝ, 0 ≤ h → h < ρ →
          ContMDiffOn 𝓘(ℝ, ℝ) I 1
              (parallelShift (I := I) g hEnorm y u ξ h) (Icc 0 L) ∧
            ∀ t₁ ∈ Icc (0 : ℝ) L, ∀ t₂ ∈ Icc (0 : ℝ) L, t₁ ≤ t₂ →
              arcLength (I := I) g (parallelShift (I := I) g hEnorm y u ξ h) t₁ t₂
                ≤ t₂ - t₁

def HasParallelShiftBound (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) : Prop :=
  ∀ (x : M) (L : ℝ), 0 < L → ∃ ρ : ℝ, 0 < ρ ∧ ∀ y : M, dist x y < ρ →
    ∀ u : TangentSpace I y, g.inner y u u = 1 →
      ∀ ξ : ∀ t : ℝ, TangentSpace I (intrinsicGeodesic (I := I) g hEnorm y u t),
        IsParallelPerpUnitField (I := I) g hEnorm y u ξ L →
        ∀ h : ℝ, 0 ≤ h → h < ρ →
          ∀ t₁ ∈ Icc (0 : ℝ) L, ∀ t₂ ∈ Icc (0 : ℝ) L,
            dist (parallelShift (I := I) g hEnorm y u ξ h t₁)
                (parallelShift (I := I) g hEnorm y u ξ h t₂) ≤ |t₁ - t₂|

omit [ConnectedSpace M] in
theorem hasParallelShiftBound_of_lengthBound
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hlen : HasParallelVariationLengthBound (I := I) g hEnorm) :
    HasParallelShiftBound (I := I) g hEnorm := by
  intro x L hL
  obtain ⟨ρ, hρ, hbound⟩ := hlen x L hL
  refine ⟨ρ, hρ, fun y hy u hu ξ hξ h hh0 hhρ t₁ ht₁ t₂ ht₂ => ?_⟩
  obtain ⟨hsmooth, harc⟩ := hbound y hy u hu ξ hξ h hh0 hhρ
  have key : ∀ s₁ ∈ Icc (0 : ℝ) L, ∀ s₂ ∈ Icc (0 : ℝ) L, s₁ ≤ s₂ →
      dist (parallelShift (I := I) g hEnorm y u ξ h s₁)
        (parallelShift (I := I) g hEnorm y u ξ h s₂) ≤ s₂ - s₁ := by
    intro s₁ hs₁ s₂ hs₂ hle
    have hsub : Icc s₁ s₂ ⊆ Icc (0 : ℝ) L := fun z hz =>
      ⟨le_trans hs₁.1 hz.1, le_trans hz.2 hs₂.2⟩
    exact le_trans (dist_le_arcLength (I := I) g hEnorm hle (hsmooth.mono hsub))
      (harc s₁ hs₁ s₂ hs₂ hle)
  rcases le_total t₁ t₂ with hle | hle
  · rw [abs_of_nonpos (by linarith), neg_sub]
    exact key t₁ ht₁ t₂ ht₂ hle
  · rw [abs_of_nonneg (by linarith), dist_comm]
    exact key t₂ ht₂ t₁ ht₁ hle

end DifferentialGeometry.Geometry.Topology

end
