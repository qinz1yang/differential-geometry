import DifferentialGeometry.Geometry.Comparison.Nonnegative.ParallelVariationRegularity

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Metric Set
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



def HasFocalJacobiBound (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) : Prop :=
  ∀ (x : M) (r : ℝ), ∃ ρ : ℝ, 0 < ρ ∧
    ∀ (z : M) (w : TangentSpace I z), dist x z ≤ r → g.inner z w w = 1 →
      ∀ σ : ℝ → M, σ = intrinsicGeodesic (I := I) g hEnorm z w →
        ∀ J : ∀ h : ℝ, TangentSpace I (σ h),
          ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞
            (fun s : ℝ => TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
              (σ s) (J s)) →
          IsJacobiAlong (I := I) g σ J →
          covDerivAlong (I := I) g σ J 0 = 0 →
          g.inner (σ 0) (J 0) (mfderiv 𝓘(ℝ, ℝ) I σ 0 (1 : ℝ)) = 0 →
          ∀ h : ℝ, 0 ≤ h → h < ρ →
            g.inner (σ h) (J h) (J h) ≤ g.inner (σ 0) (J 0) (J 0)



omit [ConnectedSpace M] in
theorem dist_intrinsicGeodesic_le (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (y : M) (u : TangentSpace I y)
    (hu : g.inner y u u = 1) {t : ℝ} (ht : 0 ≤ t) :
    dist y (intrinsicGeodesic (I := I) g hEnorm y u t) ≤ t := by
  have hC1 : ContMDiffOn 𝓘(ℝ, ℝ) I 1
      (intrinsicGeodesic (I := I) g hEnorm y u) (Icc 0 t) :=
    ((intrinsicGeodesic_contMDiff (I := I) g hEnorm y u).of_le
      (by exact_mod_cast le_top)).contMDiffOn
  have h1 := dist_le_arcLength (I := I) g hEnorm ht hC1
  have h2 := arcLength_le_of_speed_le (I := I) g ht
    (fun s _ => le_of_eq (inner_velocity_intrinsicGeodesic (I := I) g hEnorm y u hu s))
  rw [intrinsicGeodesic_zero (I := I) g hEnorm y u] at h1
  linarith



omit [ConnectedSpace M] in
theorem hasParallelVariationFocalBound_of_focalJacobiBound
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hfocal : HasFocalJacobiBound (I := I) g hEnorm) :
    HasParallelVariationFocalBound (I := I) g hEnorm := by
  classical
  intro x L hL
  obtain ⟨ρ₀, hρ₀, hb⟩ := hfocal x (L + 1)
  refine ⟨min ρ₀ 1, lt_min hρ₀ one_pos, fun y hy u hu ξ hξ h hh0 hhρ t ht => ?_⟩
  obtain ⟨W, hWξ, hWpar, hWsm⟩ :=
    exists_smooth_isParallelPerpUnitField (I := I) g hEnorm y u ξ hL hξ
  have hsm : IsSmoothVariation (I := I)
      (fun s r : ℝ => parallelShift (I := I) g hEnorm y u W r s) :=
    isSmoothVariation_parallelShift (I := I) g hEnorm y u W hWsm
  have hσeq : (fun r : ℝ => parallelShift (I := I) g hEnorm y u W r t)
      = intrinsicGeodesic (I := I) g hEnorm
          (intrinsicGeodesic (I := I) g hEnorm y u t) (W t) :=
    parallelShift_eq_intrinsicGeodesic (I := I) g hEnorm y u W t
  have hbase0 : parallelShift (I := I) g hEnorm y u W 0 t
      = intrinsicGeodesic (I := I) g hEnorm y u t :=
    parallelShift_zero (I := I) g hEnorm y u W t
  have hdist : dist x (intrinsicGeodesic (I := I) g hEnorm y u t) ≤ L + 1 := by
    have h1 := dist_intrinsicGeodesic_le (I := I) g hEnorm y u hu ht.1
    have h2 : dist x y < 1 := lt_of_lt_of_le hy (min_le_right _ _)
    have h3 := dist_triangle x y (intrinsicGeodesic (I := I) g hEnorm y u t)
    linarith [ht.2]
  have hvel0 : (mfderiv 𝓘(ℝ, ℝ) I
      (fun r : ℝ => parallelShift (I := I) g hEnorm y u W 0 r) t (1 : ℝ) : E)
      = (mfderiv 𝓘(ℝ, ℝ) I (intrinsicGeodesic (I := I) g hEnorm y u) t (1 : ℝ) : E) :=
    parallelShift_velocity_zero (I := I) g hEnorm y u W t
  have htrans : (mfderiv 𝓘(ℝ, ℝ) I
      (fun r : ℝ => parallelShift (I := I) g hEnorm y u W r t) 0 (1 : ℝ) : E)
      = (W t : E) :=
    parallelShift_transverse_velocity_zero (I := I) g hEnorm y u W t
  have hperp : g.inner (parallelShift (I := I) g hEnorm y u W 0 t)
      (mfderiv 𝓘(ℝ, ℝ) I
        (fun r : ℝ => parallelShift (I := I) g hEnorm y u W 0 r) t (1 : ℝ))
      (mfderiv 𝓘(ℝ, ℝ) I
        (fun r : ℝ => parallelShift (I := I) g hEnorm y u W r t) 0 (1 : ℝ)) = 0 := by
    rw [hvel0, htrans, hbase0]
    rw [g.symm (intrinsicGeodesic (I := I) g hEnorm y u t)]
    exact hWpar.2.2.2 t ht
  have hshift : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I ∞
      (fun p : ℝ × ℝ =>
        parallelShift (I := I) g hEnorm y u W p.2 (t + p.1)) :=
    (contMDiff_parallelShift (I := I) g hEnorm y u W hWsm).comp
      ((contMDiff_const.add contMDiff_fst).prodMk contMDiff_snd)
  have hfield : ∀ v : ℝ,
      mfderiv 𝓘(ℝ, ℝ) I
          (fun s : ℝ => parallelShift (I := I) g hEnorm y u W v (t + s)) 0 (1 : ℝ)
        = mfderiv 𝓘(ℝ, ℝ) I
          (fun r : ℝ => parallelShift (I := I) g hEnorm y u W v r) t (1 : ℝ) :=
    fun v => varFst_shift (I := I)
      (fun s r : ℝ => parallelShift (I := I) g hEnorm y u W r s) hsm t v
  have hJsm : ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞
      (fun r : ℝ => TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
        (parallelShift (I := I) g hEnorm y u W r t)
        (mfderiv 𝓘(ℝ, ℝ) I
          (fun s : ℝ => parallelShift (I := I) g hEnorm y u W r s) t (1 : ℝ))) := by
    intro v
    have hvar := varField_smoothAt (I := I)
      (fun a b : ℝ => parallelShift (I := I) g hEnorm y u W b (t + a))
      (hshift.contMDiffAt (x := ((0 : ℝ), v)))
    refine hvar.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun b => ?_))
    refine TotalSpace.ext ?_ ?_
    · exact congrArg (parallelShift (I := I) g hEnorm y u W b) (add_zero t).symm
    · exact heq_of_eq (hfield b).symm
  have hcmp := hb (intrinsicGeodesic (I := I) g hEnorm y u t) (W t) hdist
    (hWpar.2.2.1 t ht) (fun r : ℝ => parallelShift (I := I) g hEnorm y u W r t) hσeq
    (fun r : ℝ => mfderiv 𝓘(ℝ, ℝ) I
      (fun s : ℝ => parallelShift (I := I) g hEnorm y u W r s) t (1 : ℝ))
    hJsm
    (isJacobiAlong_parallelShift_velocity (I := I) g hEnorm y u W hsm t)
    (covDerivAlong_parallelShift_velocity_zero (I := I) g hEnorm y u W hsm hWpar ht)
    hperp h hh0 (lt_of_lt_of_le hhρ (min_le_left _ _))
  rw [inner_parallelShift_velocity_zero (I := I) g hEnorm y u hu W t] at hcmp
  rw [inner_parallelShift_velocity_zero (I := I) g hEnorm y u hu ξ t]
  have hagree : ∀ r ∈ Icc (0 : ℝ) L,
      parallelShift (I := I) g hEnorm y u ξ h r
        = parallelShift (I := I) g hEnorm y u W h r := by
    intro r hr
    rw [parallelShift, parallelShift, hWξ r hr]
  by_cases hdiff : MDifferentiableAt 𝓘(ℝ, ℝ) I
      (parallelShift (I := I) g hEnorm y u ξ h) t
  · have hslice : ContMDiff 𝓘(ℝ, ℝ) I ((8 : ℕ) : ℕ∞)
        (fun s : ℝ => parallelShift (I := I) g hEnorm y u W h s) :=
      (hsm : ContMDiff _ _ _ _).comp (contMDiff_id.prodMk contMDiff_const)
    have hWdiff : MDifferentiableAt 𝓘(ℝ, ℝ) I
        (fun s : ℝ => parallelShift (I := I) g hEnorm y u W h s) t :=
      hslice.mdifferentiableAt (by norm_num)
    have huniq : UniqueMDiffWithinAt 𝓘(ℝ, ℝ) (Icc (0 : ℝ) L) t :=
      (uniqueDiffOn_Icc hL t ht).uniqueMDiffWithinAt
    have hA := hdiff.hasMFDerivAt.hasMFDerivWithinAt (s := Icc (0 : ℝ) L)
    have hB := HasMFDerivWithinAt.congr_mono
      (hWdiff.hasMFDerivAt.hasMFDerivWithinAt (s := univ)) hagree (hagree t ht)
      (subset_univ _)
    have hEq := huniq.eq hA hB
    have hEq1 : (mfderiv 𝓘(ℝ, ℝ) I (parallelShift (I := I) g hEnorm y u ξ h) t
        (1 : ℝ) : E)
        = (mfderiv 𝓘(ℝ, ℝ) I
            (fun s : ℝ => parallelShift (I := I) g hEnorm y u W h s) t (1 : ℝ) : E) :=
      congrArg (fun F : ℝ →L[ℝ] E => F (1 : ℝ)) hEq
    rw [hEq1, hagree t ht]
    exact hcmp
  · have hz : mfderiv 𝓘(ℝ, ℝ) I (parallelShift (I := I) g hEnorm y u ξ h) t (1 : ℝ)
        = (0 : TangentSpace I (parallelShift (I := I) g hEnorm y u ξ h t)) := by
      rw [mfderiv_zero_of_not_mdifferentiableAt hdiff]
      rfl
    have hzero : g.inner (parallelShift (I := I) g hEnorm y u ξ h t)
        (0 : TangentSpace I (parallelShift (I := I) g hEnorm y u ξ h t))
        (0 : TangentSpace I (parallelShift (I := I) g hEnorm y u ξ h t)) = 0 := by
      simp
    rw [hz, hzero]
    norm_num

omit [ConnectedSpace M] in
theorem hasParallelShiftBound_of_focalJacobiBound
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hfocal : HasFocalJacobiBound (I := I) g hEnorm) :
    HasParallelShiftBound (I := I) g hEnorm :=
  hasParallelShiftBound_of_focalBound (I := I) g hEnorm
    (hasParallelVariationC1 (I := I) g hEnorm)
    (hasParallelVariationFocalBound_of_focalJacobiBound (I := I) g hEnorm hfocal)

end DifferentialGeometry.Geometry.Topology

end
