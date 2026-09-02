import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.Weak
import DifferentialGeometry.Geometry.Connection.Laplacian.VectorBundleInner

set_option autoImplicit false

noncomputable section

open Bundle CovariantDerivative Set
open DifferentialGeometry
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff Topology InnerProductSpace

namespace DifferentialGeometry.Analysis.Parabolic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F]
  [FiniteDimensional Real F]
variable {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace Real (V x)]
  [FiberBundle F V] [VectorBundle Real F V]
  [ContMDiffVectorBundle ∞ F V I]
  [IsContMDiffRiemannianBundle I ∞ F V]

theorem derivWithin_sub_heatOperatorWithDrift_inner_endomorphism_apply_of_normal_eigenvector
    [NeZero (Module.finrank Real E)] [I.Boundaryless]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (cov : CovariantDerivative I F V)
    [ContMDiffCovariantDerivative cov ∞] (hcov : cov.IsMetricCompatible)
    {T : Real} (hT : 0 < T) {t : Real} (ht : t ∈ Icc 0 T)
    (A : Real → Cₛ^∞⟮I; F →L[Real] F, (fun x : M ↦ V x →L[Real] V x)⟯)
    (v : Cₛ^∞⟮I; F, V⟯) (x : M)
    (X : Real → (y : M) → TangentSpace I y)
    {eigenvalue : Real}
    (hGconn : G.connection t = LeviCivita (I := I) (G.metric t))
    (hAt : DifferentiableAt Real (fun q ↦ A q x) t)
    (hA : ((A t x : V x →L[Real] V x) : V x →ₗ[Real] V x).IsSymmetric)
    (heigen : A t x (v x) = eigenvalue • v x)
    (hv : cov v x = 0)
    (hunit : ∀ᶠ y in 𝓝 x, inner Real (v y) (v y) = 1) :
    parabolicOperatorWithDrift (I := I) G T X
        (fun q y ↦ inner Real (A q y (v y)) (v y)) t x =
      inner Real
        ((deriv (fun q ↦ A q x) t -
            rawBundleEndomorphismConnLap (I := I) (G.metric t) cov
              (fun y ↦ A t y) x -
            HomConnectionGen.homBundleCovariantDerivativeGen
              I M F V F V cov cov (fun y ↦ A t y) x (X t x)) (v x))
        (v x) := by
  let q : C^∞⟮I, M; Real⟯ :=
    ⟨fun y ↦ inner Real (A t y (v y)) (v y),
      (ContMDiff.clm_bundle_apply (b := id) (A t).contMDiff v.contMDiff).inner_bundle
        v.contMDiff⟩
  have hAv : DifferentiableAt Real (fun r ↦ A r x (v x)) t :=
    hAt.clm_apply (differentiableAt_const (c := v x))
  have hqtime : DifferentiableAt Real
      (fun r ↦ inner Real (A r x (v x)) (v x)) t :=
    hAv.inner Real (differentiableAt_const (c := v x))
  have htime :
      deriv (fun r ↦ inner Real (A r x (v x)) (v x)) t =
        inner Real (deriv (fun r ↦ A r x) t (v x)) (v x) := by
    rw [deriv_inner_apply Real hAv (differentiableAt_const (c := v x)),
      deriv_clm_apply hAt (differentiableAt_const (c := v x))]
    simp
  have htimeWithin :
      derivWithin (fun r ↦ inner Real (A r x (v x)) (v x)) (Icc 0 T) t =
        deriv (fun r ↦ inner Real (A r x (v x)) (v x)) t :=
    hqtime.derivWithin
      ((uniqueDiffOn_Icc hT).uniqueDiffWithinAt ht)
  have hlap :
      laplacianAt (I := I) G t (fun y ↦ inner Real (A t y (v y)) (v y)) x =
        inner Real
          (rawBundleEndomorphismConnLap (I := I) (G.metric t) cov
            (fun y ↦ A t y) x (v x))
          (v x) := by
    change laplacianAt (I := I) G t q x = _
    rw [laplacianAt_eq_delta (I := I) G t q.contMDiff hGconn x]
    exact laplacian_inner_endomorphism_apply_of_normal_eigenvector
      (I := I) (G.metric t) cov hcov (A t) v x hA heigen hv hunit
  have hdrift :
      driftTerm (I := I) G t (X t)
          (fun y ↦ inner Real (A t y (v y)) (v y)) x =
        inner Real
          ((HomConnectionGen.homBundleCovariantDerivativeGen
            I M F V F V cov cov (fun y ↦ A t y) x (X t x)) (v x))
          (v x) := by
    unfold driftTerm gradientAt
    rw [(G.metric t).symm]
    rw [inner_gradientFun]
    exact mvfderiv_inner_endomorphism_apply_of_cov_eq_zero
      (I := I) cov hcov (A t) v x (X t x) hv
  unfold parabolicOperatorWithDrift
  rw [htimeWithin, htime]
  unfold heatOperatorWithDrift
  rw [hlap, hdrift]
  simp only [sub_apply, inner_sub_left]
  ring

theorem parabolicOperatorWithDrift_sum_inner_endomorphism_apply_of_normal_eigenframe
    [NeZero (Module.finrank Real E)] [I.Boundaryless]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (cov : CovariantDerivative I F V)
    [ContMDiffCovariantDerivative cov ∞] (hcov : cov.IsMetricCompatible)
    {T : Real} (hT : 0 < T) {t : Real} (ht : t ∈ Icc 0 T)
    (A : Real → Cₛ^∞⟮I; F →L[Real] F, (fun x : M ↦ V x →L[Real] V x)⟯)
    {k : Nat} (v : Fin k → Cₛ^∞⟮I; F, V⟯) (x : M)
    (X : Real → (y : M) → TangentSpace I y)
    (eigenvalue : Fin k → Real)
    (hGconn : G.connection t = LeviCivita (I := I) (G.metric t))
    (hAt : DifferentiableAt Real (fun q ↦ A q x) t)
    (hA : ((A t x : V x →L[Real] V x) : V x →ₗ[Real] V x).IsSymmetric)
    (heigen : ∀ i, A t x (v i x) = eigenvalue i • v i x)
    (hv : ∀ i, cov (v i) x = 0)
    (hunit : ∀ i, ∀ᶠ y in 𝓝 x,
      inner Real (v i y) (v i y) = 1) :
    parabolicOperatorWithDrift (I := I) G T X
        (fun q y ↦ ∑ i, inner Real (A q y (v i y)) (v i y)) t x =
      ∑ i, inner Real
        ((deriv (fun q ↦ A q x) t -
            rawBundleEndomorphismConnLap (I := I) (G.metric t) cov
              (fun y ↦ A t y) x -
            HomConnectionGen.homBundleCovariantDerivativeGen
              I M F V F V cov cov (fun y ↦ A t y) x (X t x)) (v i x))
        (v i x) := by
  let u : Fin k → Real → M → Real :=
    fun i q y ↦ inner Real (A q y (v i y)) (v i y)
  have htime (i : Fin k) : DifferentiableWithinAt Real
      (fun q ↦ u i q x) (Icc 0 T) t := by
    apply DifferentiableAt.differentiableWithinAt
    exact (hAt.clm_apply (differentiableAt_const (c := v i x))).inner Real
      (differentiableAt_const (c := v i x))
  have hsmooth (i : Fin k) : ContMDiff I 𝓘(Real, Real) ∞ (u i t) :=
    (ContMDiff.clm_bundle_apply (b := id) (A t).contMDiff
      (v i).contMDiff).inner_bundle (v i).contMDiff
  have hsum := parabolic_sum (I := I) (Finset.univ : Finset (Fin k))
    G T X u t x
    (fun i _ ↦ htime i)
    (fun i _ y ↦ (hsmooth i).mdifferentiableAt (by simp))
    (fun i _ y ↦
      (gradientFun_smooth (I := I) (G.metric t) (hsmooth i)).mdifferentiableAt
        (by simp))
  change parabolicOperatorWithDrift (I := I) G T X
      (fun q y ↦ ∑ i, u i q y) t x = _
  rw [hsum]
  apply Finset.sum_congr rfl
  intro i hi
  exact derivWithin_sub_heatOperatorWithDrift_inner_endomorphism_apply_of_normal_eigenvector
    (I := I) G cov hcov hT ht A (v i) x X hGconn hAt hA
      (heigen i) (hv i) (hunit i)

end DifferentialGeometry.Analysis.Parabolic
