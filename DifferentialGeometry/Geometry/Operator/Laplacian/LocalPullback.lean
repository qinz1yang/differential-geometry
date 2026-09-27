import DifferentialGeometry.Geometry.Operator.Pullback
import DifferentialGeometry.Geometry.Operator.OrthonormalTrace
import DifferentialGeometry.Geometry.Operator.Gradient.Regularity
import DifferentialGeometry.Bundle.SmoothScalarGerm


noncomputable section

open Bundle
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Operator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  [SigmaCompactSpace M] [T2Space M] [SigmaCompactSpace N] [T2Space N]
  [I.Boundaryless]

private theorem laplacian_localPull_smooth
    (g : SmoothRiemannianMetric I N) (Phi : M → N)
    (hPhi : IsLocalDiffeomorph I I ∞ Phi)
    (f : C^∞⟮I, N; ℝ⟯) (x : M) :
    laplacian (Connection.LeviCivita (localPullMetric g Phi hPhi))
        (localPullMetric g Phi hPhi) (f ∘ Phi) x =
      laplacian (Connection.LeviCivita g) g f (Phi x) := by
  classical
  obtain ⟨B, hB⟩ :=
    DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis (I := I) g (Phi x)
  let A : TangentSpace I x ≃L[ℝ] TangentSpace I (Phi x) :=
    hPhi.mfderivToContinuousLinearEquiv (by simp) x
  let b := B.map A.symm.toLinearEquiv
  have hA (v : TangentSpace I x) : A v = mfderiv I I Phi x v := by
    exact congrArg
      (fun L : TangentSpace I x →L[ℝ] TangentSpace I (Phi x) => L v)
      (hPhi.mfderivToContinuousLinearEquiv_coe (x := x) (by simp))
  have hb_push (j) : mfderiv I I Phi x (b j) = B j := by
    rw [← hA]
    change A (A.symm (B j)) = B j
    exact A.apply_symm_apply _
  have hb : ∀ j k, (localPullMetric g Phi hPhi).inner x (b j) (b k) =
      if j = k then (1 : ℝ) else 0 := by
    intro j k
    rw [localPullMetric_inner, hb_push, hb_push]
    exact hB j k
  rw [laplacian_eq_sum_hessFun (localPullMetric g Phi hPhi) (f ∘ Phi)
    (f.contMDiff.comp hPhi.contMDiff) x b hb,
    laplacian_eq_sum_hessFun g f f.contMDiff (Phi x) B hB]
  apply Finset.sum_congr rfl
  intro j hj
  rw [hessFun_localPull (I := I) (J := I) g Phi hPhi f x (b j) (b j)]
  simp only [hb_push]

theorem laplacian_localPull_of_contMDiffOn
    (g : SmoothRiemannianMetric I N) (Phi : M → N)
    (hPhi : IsLocalDiffeomorph I I ∞ Phi)
    {f : N → ℝ} {U : Set N} (hU : IsOpen U)
    (hf : ContMDiffOn I 𝓘(ℝ) ∞ f U) (x : M) (hx : Phi x ∈ U) :
    laplacian (Connection.LeviCivita (localPullMetric g Phi hPhi))
        (localPullMetric g Phi hPhi) (f ∘ Phi) x =
      laplacian (Connection.LeviCivita g) g f (Phi x) := by
  obtain ⟨F, hF, hFf⟩ := exists_smooth_germ hU hx hf
  have hfx : ContMDiffAt I 𝓘(ℝ) ∞ f (Phi x) :=
    hf.contMDiffAt (hU.mem_nhds hx)
  have hcomp : (F ∘ Phi) =ᶠ[𝓝 x] (f ∘ Phi) :=
    hFf.comp_tendsto hPhi.contMDiff.continuous.continuousAt
  calc
    laplacian (Connection.LeviCivita (localPullMetric g Phi hPhi))
        (localPullMetric g Phi hPhi) (f ∘ Phi) x =
        laplacian (Connection.LeviCivita (localPullMetric g Phi hPhi))
          (localPullMetric g Phi hPhi) (F ∘ Phi) x :=
      (laplacian_congr_of_eventuallyEq
        (Connection.LeviCivita (localPullMetric g Phi hPhi))
        (localPullMetric g Phi hPhi)
        (hF.contMDiffAt.comp x hPhi.contMDiff.contMDiffAt)
        (hfx.comp x hPhi.contMDiff.contMDiffAt) hcomp).symm
    _ = laplacian (Connection.LeviCivita g) g F (Phi x) :=
      laplacian_localPull_smooth g Phi hPhi ⟨F, hF⟩ x
    _ = laplacian (Connection.LeviCivita g) g f (Phi x) :=
      laplacian_congr_of_eventuallyEq (Connection.LeviCivita g) g
        hF.contMDiffAt hfx hFf

theorem laplacian_localPull
    (g : SmoothRiemannianMetric I N) (Phi : M → N)
    (hPhi : IsLocalDiffeomorph I I ∞ Phi)
    (f : C^∞⟮I, N; ℝ⟯) (x : M) :
    laplacian (Connection.LeviCivita (localPullMetric g Phi hPhi))
        (localPullMetric g Phi hPhi) (f ∘ Phi) x =
      laplacian (Connection.LeviCivita g) g f (Phi x) :=
  laplacian_localPull_of_contMDiffOn g Phi hPhi isOpen_univ
    f.contMDiff.contMDiffOn x (Set.mem_univ _)

end DifferentialGeometry.Geometry.Operator
