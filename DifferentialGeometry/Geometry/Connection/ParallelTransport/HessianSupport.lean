import DifferentialGeometry.Geometry.Connection.ParallelTransport.Support
import DifferentialGeometry.Topology.Manifold.Curve
import DifferentialGeometry.Topology.FiberBundle.Separation
import DifferentialGeometry.Geometry.Connection.LeviCivita.AlongCurve
import DifferentialGeometry.Geometry.Connection.Laplacian.VectorBundle
import DifferentialGeometry.Geometry.Exponential.RadialGeodesic
import DifferentialGeometry.Geometry.Exponential.GaussLemmaPullback

noncomputable section

open Bundle Set Filter
open scoped Manifold ContDiff Topology

namespace CovariantDerivative

open DifferentialGeometry.Analysis.Convex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  [IsContMDiffRiemannianBundle I 1 F V] [ContMDiffVectorBundle ∞ F V I]

theorem IsParallelSet.inner_covariantDerivative_eq_zero_of_fiberInfDist_localMax
    {cov : CovariantDerivative I F V} {K : Set (TotalSpace F V)}
    (hK : cov.IsParallelSet K) (hcov : ContMDiffCovariantDerivative cov ∞)
    (hmetric : cov.IsMetricCompatible)
    {σ : ∀ x, V x} {x : M} (hx : I.IsInteriorPoint x)
    (hσ : MDifferentiableAt I (I.prod 𝓘(ℝ, F)) (T% σ) x)
    (p ν : V x)
    (hν : ν ∈ normalCone {w : V x | (⟨x, w⟩ : TotalSpace F V) ∈ K} p)
    (hνnorm : ‖ν‖ ≤ 1)
    (hcontact : inner ℝ ν (σ x - p) = fiberInfDist K (⟨x, σ x⟩ : TotalSpace F V))
    (hmax : IsLocalMax (fun y => fiberInfDist K (⟨y, σ y⟩ : TotalSpace F V)) x)
    (v : TangentSpace I x) : inner ℝ ν (cov σ x v) = 0 := by
  obtain ⟨ε, hε, γ, hγ, hbound, hlaunch⟩ :=
    exists_contMDiff_curve_with_velocity (n := ∞) (by simp) hx v hmax
  have hγ₀ : γ 0 = x := congrArg TotalSpace.proj hlaunch
  have hvelocity :
      (mfderiv 𝓘(ℝ, ℝ) I γ 0 ((NormedSpace.fromTangentSpace (0 : ℝ)).symm 1) : E) = v :=
    congrArg (fun z : TangentBundle I M => (z.2 : E)) hlaunch
  have hJ : Icc (-ε) ε ∈ 𝓝 (0 : ℝ) := Icc_mem_nhds (neg_neg_of_pos hε) hε
  have hγd := (hγ.mdifferentiableOn (by simp)) 0 (mem_of_mem_nhds hJ)
  have hσ₀ : MDifferentiableAt I (I.prod 𝓘(ℝ, F)) (T% σ) (γ 0) := by
    simpa only [hγ₀] using hσ
  have hZ := hσ₀.comp_mdifferentiableWithinAt 0 hγd
  have htest (q η : V (γ 0))
      (hη : η ∈ normalCone {w : V (γ 0) | (⟨γ 0, w⟩ : TotalSpace F V) ∈ K} q)
      (hηnorm : ‖η‖ ≤ 1)
      (hc : inner ℝ η (σ (γ 0) - q) =
        fiberInfDist K (⟨γ 0, σ (γ 0)⟩ : TotalSpace F V)) :
      inner ℝ η (cov σ (γ 0)
        (mfderiv 𝓘(ℝ, ℝ) I γ 0 ((NormedSpace.fromTangentSpace (0 : ℝ)).symm 1))) = 0 := by
    have h := hK.inner_derivAlongWithin_eq_zero_of_fiberInfDist_max hcov hmetric
      ⟨neg_neg_of_pos hε, hε⟩ hγ hZ q η hη hηnorm hc (fun t ht => by
        have hb := hbound ht
        change fiberInfDist K (⟨γ t, σ (γ t)⟩ : TotalSpace F V) ≤
          fiberInfDist K (⟨x, σ x⟩ : TotalSpace F V) at hb
        change fiberInfDist K (⟨γ t, σ (γ t)⟩ : TotalSpace F V) ≤
          fiberInfDist K (⟨γ 0, σ (γ 0)⟩ : TotalSpace F V)
        rw [hγ₀]
        exact hb)
    rw [cov.derivAlongWithin_section hγd hσ₀, mfderivWithin_of_mem_nhds hJ] at h
    exact h
  rw [hvelocity] at htest
  rw [hγ₀] at htest
  exact htest p ν hν hνnorm hcontact

open DifferentialGeometry (SmoothRiemannianMetric)
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Connection

variable [I.Boundaryless]

theorem IsParallelSet.inner_hessian_nonpos_of_fiberInfDist_localMax
    {cov : CovariantDerivative I F V} {K : Set (TotalSpace F V)}
    (hK : cov.IsParallelSet K) (hcov : ContMDiffCovariantDerivative cov ∞)
    (hmetric : cov.IsMetricCompatible) (g : SmoothRiemannianMetric I M)
    {σ : ∀ x, V x} {x : M}
    (hσ : ContMDiffAt I (I.prod 𝓘(ℝ, F)) 2 (T% σ) x)
    (p ν : V x)
    (hν : ν ∈ normalCone {w : V x | (⟨x, w⟩ : TotalSpace F V) ∈ K} p)
    (hνnorm : ‖ν‖ ≤ 1)
    (hcontact : inner ℝ ν (σ x - p) = fiberInfDist K (⟨x, σ x⟩ : TotalSpace F V))
    (hmax : IsLocalMax (fun y => fiberInfDist K (⟨y, σ y⟩ : TotalSpace F V)) x)
    (v : TangentSpace I x) :
    inner ℝ ν (cov.hessian (LeviCivita g) σ x v v) ≤ 0 := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let a : E := v
  let γ : ℝ → M := fun t => expMap g x (show TangentSpace I x from t • a)
  have hγ₀ : γ 0 = x := by
    simp only [γ, zero_smul]
    exact expMap_zero g x
  have hvelocity : (mfderiv 𝓘(ℝ, ℝ) I γ 0
      ((NormedSpace.fromTangentSpace (0 : ℝ)).symm 1) : E) = v :=
    radialCurve_launch_velocity g x a
  obtain ⟨δ, hδ, hexp⟩ := expMap_contMDiffAt_infty_of_norm_lt g x
  have hc : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (fun t : ℝ => t • a) :=
    contMDiff_id.smul contMDiff_const
  have hγsmooth {t : ℝ} (ht : ‖t • a‖ < δ) : ContMDiffAt 𝓘(ℝ, ℝ) I ∞ γ t :=
    (hexp (t • a) ht).comp t hc.contMDiffAt
  have hγat := hγsmooth (t := 0) (by simpa only [zero_smul, norm_zero] using hδ)
  have hnear : ∀ᶠ t in 𝓝 (0 : ℝ), ‖t • a‖ < δ ∧
      ContMDiffAt I (I.prod 𝓘(ℝ, F)) 2 (T% σ) (γ t) ∧
      fiberInfDist K (⟨γ t, σ (γ t)⟩ : TotalSpace F V) ≤
        fiberInfDist K (⟨x, σ x⟩ : TotalSpace F V) := by
    have hnorm : ∀ᶠ t in 𝓝 (0 : ℝ), ‖t • a‖ < δ :=
      (hc.continuous.norm.continuousAt).eventually (gt_mem_nhds (by simpa using hδ))
    have hσnear := (contMDiffAt_iff_contMDiffAt_nhds (n := 2) (by norm_num)).mp hσ
    have hγtend : Tendsto γ (𝓝 (0 : ℝ)) (𝓝 x) := by
      have ht : Tendsto γ (𝓝 (0 : ℝ)) (𝓝 (γ 0)) := hγat.continuousAt
      rwa [hγ₀] at ht
    have hσγ : ∀ᶠ t in 𝓝 (0 : ℝ),
        ContMDiffAt I (I.prod 𝓘(ℝ, F)) 2 (T% σ) (γ t) := hγtend.eventually hσnear
    have hmaxγ : ∀ᶠ t in 𝓝 (0 : ℝ),
        fiberInfDist K (⟨γ t, σ (γ t)⟩ : TotalSpace F V) ≤
          fiberInfDist K (⟨x, σ x⟩ : TotalSpace F V) := hγtend.eventually hmax
    exact hnorm.and (hσγ.and hmaxγ)
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp hnear
  have hsub : Icc (-(ε / 2)) (ε / 2) ⊆ Metric.ball (0 : ℝ) ε := by
    intro t ht
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs]
    exact abs_lt.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hγon : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ γ (Icc (-(ε / 2)) (ε / 2)) :=
    fun _ ht => (hγsmooth (hεsub (hsub ht)).1).contMDiffWithinAt
  have hZ : ContMDiffOn 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, F)) 2
      (fun t => (⟨γ t, σ (γ t)⟩ : TotalSpace F V)) (Icc (-(ε / 2)) (ε / 2)) := by
    intro t ht
    exact ((hεsub (hsub ht)).2.1.comp t
      ((hγsmooth (hεsub (hsub ht)).1).of_le
        (show (2 : ℕ∞ω) ≤ ∞ from ENat.LEInfty.out))).contMDiffWithinAt
  have hJ : Icc (-(ε / 2)) (ε / 2) ∈ 𝓝 (0 : ℝ) :=
    Icc_mem_nhds (neg_neg_of_pos (half_pos hε)) (half_pos hε)
  have hσ₀ : ContMDiffAt I (I.prod 𝓘(ℝ, F)) 2 (T% σ) (γ 0) := by
    simpa only [hγ₀] using hσ
  have hgeo : Geodesic.HasGeodesicEquationAt g γ 0 := exp_radial_geo_zero g x v
  have hhessian := cov.hessian_apply_velocity_of_hasGeodesicEquationAt hcov g hJ
    (hγat.of_le (show (2 : ℕ∞ω) ≤ ∞ from ENat.LEInfty.out)) hσ₀
    BoundarylessManifold.isInteriorPoint hgeo
  dsimp only at hhessian
  rw [mfderivWithin_of_mem_nhds hJ] at hhessian
  have htest (q η : V (γ 0))
      (hη : η ∈ normalCone {w : V (γ 0) | (⟨γ 0, w⟩ : TotalSpace F V) ∈ K} q)
      (hηnorm : ‖η‖ ≤ 1)
      (hc : inner ℝ η (σ (γ 0) - q) =
        fiberInfDist K (⟨γ 0, σ (γ 0)⟩ : TotalSpace F V)) :
      inner ℝ η (cov.hessian (LeviCivita g) σ (γ 0)
        (mfderiv 𝓘(ℝ, ℝ) I γ 0 ((NormedSpace.fromTangentSpace (0 : ℝ)).symm 1))
        (mfderiv 𝓘(ℝ, ℝ) I γ 0 ((NormedSpace.fromTangentSpace (0 : ℝ)).symm 1))) ≤ 0 := by
    rw [hhessian]
    exact hK.inner_second_derivAlongWithin_nonpos_of_fiberInfDist_max hcov hmetric
      ⟨neg_neg_of_pos (half_pos hε), half_pos hε⟩ hγon hZ q η hη hηnorm hc
      (fun t ht => by
        change fiberInfDist K (⟨γ t, σ (γ t)⟩ : TotalSpace F V) ≤
          fiberInfDist K (⟨γ 0, σ (γ 0)⟩ : TotalSpace F V)
        rw [hγ₀]
        exact (hεsub (hsub ht)).2.2)
  rw [hvelocity] at htest
  rw [hγ₀] at htest
  exact htest p ν hν hνnorm hcontact

theorem IsParallelSet.inner_rawBundleConnLap_nonpos_of_fiberInfDist_localMax
    {cov : CovariantDerivative I F V} {K : Set (TotalSpace F V)}
    (hK : cov.IsParallelSet K) (hcov : ContMDiffCovariantDerivative cov ∞)
    (hmetric : cov.IsMetricCompatible) (g : SmoothRiemannianMetric I M)
    {σ : ∀ x, V x} {x : M}
    (hσ : ContMDiffAt I (I.prod 𝓘(ℝ, F)) 2 (T% σ) x)
    (p ν : V x)
    (hν : ν ∈ normalCone {w : V x | (⟨x, w⟩ : TotalSpace F V) ∈ K} p)
    (hνnorm : ‖ν‖ ≤ 1)
    (hcontact : inner ℝ ν (σ x - p) = fiberInfDist K (⟨x, σ x⟩ : TotalSpace F V))
    (hmax : IsLocalMax (fun y => fiberInfDist K (⟨y, σ y⟩ : TotalSpace F V)) x) :
    inner ℝ ν (rawBundleConnLap g cov σ x) ≤ 0 := by
  rw [rawBundleConnLap_eq_sum_hessian_of_contMDiffAt g cov hcov hσ, inner_sum]
  exact Finset.sum_nonpos (fun _ _ =>
    hK.inner_hessian_nonpos_of_fiberInfDist_localMax hcov hmetric g hσ p ν hν hνnorm
      hcontact hmax _)

end CovariantDerivative
