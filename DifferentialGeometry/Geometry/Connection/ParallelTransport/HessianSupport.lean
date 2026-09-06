import DifferentialGeometry.Geometry.Connection.ParallelTransport.Support
import DifferentialGeometry.Topology.Manifold.Curve
import DifferentialGeometry.Geometry.Connection.Laplacian.VectorBundle

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
open DifferentialGeometry.Geometry.Connection


theorem IsParallelSet.inner_hessian_nonpos_of_fiberInfDist_localMax
    {cov : CovariantDerivative I F V} {K : Set (TotalSpace F V)}
    (hK : cov.IsParallelSet K) (hcov : ContMDiffCovariantDerivative cov ∞)
    (hmetric : cov.IsMetricCompatible)
    (base : CovariantDerivative I E (TangentSpace I : M → Type _))
    {σ : ∀ x, V x} {x : M} (hx : I.IsInteriorPoint x)
    (hσ : ContMDiffAt I (I.prod 𝓘(ℝ, F)) 2 (T% σ) x)
    (p ν : V x)
    (hν : ν ∈ normalCone {w : V x | (⟨x, w⟩ : TotalSpace F V) ∈ K} p)
    (hνnorm : ‖ν‖ ≤ 1)
    (hcontact : inner ℝ ν (σ x - p) = fiberInfDist K (⟨x, σ x⟩ : TotalSpace F V))
    (hmax : IsLocalMax (fun y => fiberInfDist K (⟨y, σ y⟩ : TotalSpace F V)) x)
    (v : TangentSpace I x) :
    inner ℝ ν (cov.hessian base σ x v v) ≤ 0 := by
  have hnear := ((contMDiffAt_iff_contMDiffAt_nhds (n := 2) (by norm_num)).mp hσ).and hmax
  obtain ⟨ε, hε, γ, hγ, hbound, hlaunch⟩ :=
    exists_contMDiff_curve_with_velocity (n := ∞) (by simp) hx v hnear
  have hγ₀ : γ 0 = x := congrArg TotalSpace.proj hlaunch
  have hvelocity :
      (mfderiv 𝓘(ℝ, ℝ) I γ 0 ((NormedSpace.fromTangentSpace (0 : ℝ)).symm 1) : E) = v :=
    congrArg (fun z : TangentBundle I M => (z.2 : E)) hlaunch
  have hJ : Icc (-ε) ε ∈ 𝓝 (0 : ℝ) := Icc_mem_nhds (neg_neg_of_pos hε) hε
  have hγat : ContMDiffAt 𝓘(ℝ, ℝ) I 2 γ 0 :=
    (hγ.contMDiffAt hJ).of_le (show (2 : ℕ∞ω) ≤ ∞ from ENat.LEInfty.out)
  have hσ₀ : ContMDiffAt I (I.prod 𝓘(ℝ, F)) 2 (T% σ) (γ 0) := by
    simpa only [hγ₀] using hσ
  have hZ : ContMDiffOn 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, F)) 2
      (fun t => (⟨γ t, σ (γ t)⟩ : TotalSpace F V)) (Icc (-ε) ε) := by
    intro t ht
    exact (hbound ht).1.comp_contMDiffWithinAt t
      ((hγ t ht).of_le (show (2 : ℕ∞ω) ≤ ∞ from ENat.LEInfty.out))
  have htest (q η : V (γ 0))
      (hη : η ∈ normalCone {w : V (γ 0) | (⟨γ 0, w⟩ : TotalSpace F V) ∈ K} q)
      (hηnorm : ‖η‖ ≤ 1)
      (hc : inner ℝ η (σ (γ 0) - q) =
        fiberInfDist K (⟨γ 0, σ (γ 0)⟩ : TotalSpace F V)) :
      inner ℝ η (cov.hessian base σ (γ 0)
        (mfderiv 𝓘(ℝ, ℝ) I γ 0 ((NormedSpace.fromTangentSpace (0 : ℝ)).symm 1))
        (mfderiv 𝓘(ℝ, ℝ) I γ 0 ((NormedSpace.fromTangentSpace (0 : ℝ)).symm 1))) ≤ 0 := by
    have hmax₀ : IsLocalMax (fun y => fiberInfDist K (⟨y, σ y⟩ : TotalSpace F V)) (γ 0) := by
      simpa only [hγ₀] using hmax
    have hx₀ : I.IsInteriorPoint (γ 0) := by simpa only [hγ₀] using hx
    have hfirst := hK.inner_covariantDerivative_eq_zero_of_fiberInfDist_localMax
      hcov hmetric hx₀ (hσ₀.mdifferentiableAt (by simp)) q η hη hηnorm hc hmax₀
    have hsecond := hK.inner_second_derivAlongWithin_nonpos_of_fiberInfDist_max hcov hmetric
      ⟨neg_neg_of_pos hε, hε⟩ hγ hZ q η hη hηnorm hc (fun t ht => by
        change fiberInfDist K (⟨γ t, σ (γ t)⟩ : TotalSpace F V) ≤
          fiberInfDist K (⟨γ 0, σ (γ 0)⟩ : TotalSpace F V)
        rw [hγ₀]
        exact (hbound ht).2)
    rw [cov.derivAlongWithin_derivAlongWithin_section hcov base hJ hγat hσ₀,
      inner_add_right, hfirst, add_zero] at hsecond
    simpa only [mfderivWithin_of_mem_nhds hJ] using hsecond
  rw [hvelocity] at htest
  rw [hγ₀] at htest
  exact htest p ν hν hνnorm hcontact

theorem IsParallelSet.inner_rawBundleConnLap_nonpos_of_fiberInfDist_localMax
    {cov : CovariantDerivative I F V} {K : Set (TotalSpace F V)}
    (hK : cov.IsParallelSet K) (hcov : ContMDiffCovariantDerivative cov ∞)
    (hmetric : cov.IsMetricCompatible) (g : SmoothRiemannianMetric I M)
    {σ : ∀ x, V x} {x : M} (hx : I.IsInteriorPoint x)
    (hσ : ContMDiffAt I (I.prod 𝓘(ℝ, F)) 2 (T% σ) x)
    (p ν : V x)
    (hν : ν ∈ normalCone {w : V x | (⟨x, w⟩ : TotalSpace F V) ∈ K} p)
    (hνnorm : ‖ν‖ ≤ 1)
    (hcontact : inner ℝ ν (σ x - p) = fiberInfDist K (⟨x, σ x⟩ : TotalSpace F V))
    (hmax : IsLocalMax (fun y => fiberInfDist K (⟨y, σ y⟩ : TotalSpace F V)) x) :
    inner ℝ ν (rawBundleConnLap g cov σ x) ≤ 0 := by
  rw [rawBundleConnLap_eq_sum_hessian_of_contMDiffAt g cov hcov hσ, inner_sum]
  exact Finset.sum_nonpos (fun _ _ =>
    hK.inner_hessian_nonpos_of_fiberInfDist_localMax hcov hmetric (LeviCivita g) hx hσ p ν hν hνnorm
      hcontact hmax _)

end CovariantDerivative
