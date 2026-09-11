import DifferentialGeometry.Geometry.Comparison.Variation.Jacobi.EndpointPositivity

open Set Manifold
open scoped Manifold ContDiff RealInnerProductSpace

noncomputable section

namespace DifferentialGeometry.Geometry.Riemannian.Variation

open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem jacobi_eq_zero_of_endpoints_eq_zero
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (J : ∀ t : ℝ, TangentSpace I (γ t)) {U : Set ℝ} {a b : ℝ} (hab : a ≤ b)
    (hU : IsOpen U) (hseg : Icc a b ⊆ U)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I (2 : ℕ∞) γ U)
    (hJdiff : ∀ t ∈ Icc a b,
      DifferentiableAt ℝ (chartRepAt (I := I) γ J t) t)
    (hDJdiff : ∀ t ∈ Icc a b, DifferentiableAt ℝ
      (chartRepAt (I := I) γ (fun s => covDerivAlong (I := I) g γ J s) t) t)
    (hJac : ∀ t ∈ Icc a b, IsJacobiAt (I := I) g γ J t)
    (hJa : J a = 0) (hJb : J b = 0)
    {κ : ℝ} (hκ : κ * (b - a) ^ 2 < (Real.pi / 2) ^ 2)
    (hcurv : ∀ t ∈ Ioo a b,
      g.inner (γ t)
        ((DifferentialGeometry.Geometry.Curvature.riemannOp
          (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g) (γ t))
          (J t) (curveVelocity (I := I) γ t) (curveVelocity (I := I) γ t)) (J t) ≤
        κ * g.inner (γ t) (J t) (J t)) :
    ∀ t ∈ Icc a b, J t = 0 := by
  by_contra hne
  have hp := jacobi_pair_pos g γ J hab hU hseg hγ hJdiff hDJdiff hJac hJa hne hκ hcurv
  simp only [hJb, map_zero, lt_self_iff_false] at hp

end DifferentialGeometry.Geometry.Riemannian.Variation
