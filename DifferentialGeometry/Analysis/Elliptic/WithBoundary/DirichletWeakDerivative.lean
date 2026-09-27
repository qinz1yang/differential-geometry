import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletDirectionalDerivative
import DifferentialGeometry.Analysis.Elliptic.Regularity.SmoothScalar.MulLp
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.WithBoundary.Divergence.IntegrationByParts
import DifferentialGeometry.Geometry.Connection.DivergenceCovariantTrace
import DifferentialGeometry.Geometry.Operator.Divergence

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped ContDiff InnerProductSpace Manifold RealInnerProductSpace Topology

namespace DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet

open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Operator.WithBoundary
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
open DifferentialGeometry.Integral.Measure

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]

private abbrev I_half (n : ℕ) [NeZero n] :
    ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanHalfSpace n) :=
  modelWithCornersEuclideanHalfSpace n

omit [T2Space M] [CompactSpace M] in
private theorem tangentSectionAction_continuous
    (q : SmoothRiemannianMetric (I_half n) M)
    (Y : Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (u : SmoothScalarDirichlet q) :
    Continuous (tangentSectionAction (I := I_half n) Y u.toFun) := by
  have hcont : Continuous (fun x : M => q.inner x (Y x)
      ((gradGWithBoundarySection (I := I_half n) q u.smooth u.interior_support :
        Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
          (TangentSpace (I_half n) : M → Type _)⟯) x)) :=
    (contMDiff_g_inner_of_smooth_sections (I := I_half n) q Y
      (gradGWithBoundarySection (I := I_half n) q u.smooth
        u.interior_support)).continuous
  convert hcont using 1
  funext x
  rw [tangentSectionAction_grad_g_with_boundary_eq_inner (I := I_half n) q Y x]
  rfl

private theorem integral_tangentSectionAction_mul_add
    (q : SmoothRiemannianMetric (I_half n) M)
    (Y : Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (u v : SmoothScalarDirichlet q) :
    (∫ x, tangentSectionAction (I := I_half n) Y u.toFun x * v.toFun x
        ∂(riemannianVolumeMeasure (I := I_half n) (M := M) q)) +
      ∫ x, u.toFun x * tangentSectionAction (I := I_half n) Y v.toFun x
        ∂(riemannianVolumeMeasure (I := I_half n) (M := M) q) =
      -∫ x, u.toFun x * v.toFun x *
          divergence (I := I_half n)
            (leviCivitaConnectionOfMetric (I := I_half n) q) Y x
        ∂(riemannianVolumeMeasure (I := I_half n) (M := M) q) := by
  have hsupp : tsupport (u.toFun * v.toFun) ⊆ (I_half n).interior M :=
    (tsupport_mul_subset_left : tsupport (u.toFun * v.toFun) ⊆ tsupport u.toFun).trans
      u.interior_support
  have hibp :=
    DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.integral_tangentSectionAction_eq_neg_integral_smul_divergence_with_boundary_of_hasCompactSupport
      (I := I_half n) q (u.smooth.mul v.smooth)
      (HasCompactSupport.of_compactSpace _) hsupp Y
  have haction : ∀ x : M,
      tangentSectionAction (I := I_half n) Y (u.toFun * v.toFun) x =
        tangentSectionAction (I := I_half n) Y u.toFun x * v.toFun x +
          u.toFun x * tangentSectionAction (I := I_half n) Y v.toFun x :=
    fun x => tangentSectionAction_mul (I := I_half n) Y u.smooth v.smooth x
  have hdiv : ∀ x : M,
      (u.toFun * v.toFun) x * divergenceGWithBoundary (I := I_half n) q Y x =
        u.toFun x * v.toFun x *
          divergence (I := I_half n)
            (leviCivitaConnectionOfMetric (I := I_half n) q) Y x := by
    intro x
    by_cases hvx : v.toFun x = 0
    · simp [Pi.mul_apply, hvx]
    · have hx : x ∈ (I_half n).interior M :=
        v.interior_support (subset_tsupport v.toFun hvx)
      rw [divergence_g_with_boundary_eq_divergence_g_of_isInteriorPoint
        (I := I_half n) q Y hx,
        DifferentialGeometry.Geometry.Connection.divergence_g_eq_leviCivita_divergence_of_isInteriorPoint
          (I := I_half n) q Y hx]
      rfl
  have hleft :
      ∫ x, tangentSectionAction (I := I_half n) Y (u.toFun * v.toFun) x
          ∂(riemannianVolumeMeasure (I := I_half n) (M := M) q) =
        ∫ x, (tangentSectionAction (I := I_half n) Y u.toFun x * v.toFun x +
          u.toFun x * tangentSectionAction (I := I_half n) Y v.toFun x)
          ∂(riemannianVolumeMeasure (I := I_half n) (M := M) q) :=
    integral_congr_ae (Filter.Eventually.of_forall haction)
  have hright :
      ∫ x, (u.toFun * v.toFun) x * divergenceGWithBoundary (I := I_half n) q Y x
          ∂(riemannianVolumeMeasure (I := I_half n) (M := M) q) =
        ∫ x, u.toFun x * v.toFun x *
          divergence (I := I_half n)
            (leviCivitaConnectionOfMetric (I := I_half n) q) Y x
          ∂(riemannianVolumeMeasure (I := I_half n) (M := M) q) :=
    integral_congr_ae (Filter.Eventually.of_forall hdiv)
  have hA : Integrable (fun x : M =>
      tangentSectionAction (I := I_half n) Y u.toFun x * v.toFun x)
      (riemannianVolumeMeasure (I := I_half n) (M := M) q) :=
    DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.Continuous.integrable_of_hasCompactSupport_riemannianVolumeMeasure
      (I := I_half n) q
      ((tangentSectionAction_continuous q Y u).mul v.smooth.continuous)
      (HasCompactSupport.of_compactSpace _)
  have hB : Integrable (fun x : M =>
      u.toFun x * tangentSectionAction (I := I_half n) Y v.toFun x)
      (riemannianVolumeMeasure (I := I_half n) (M := M) q) :=
    DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.Continuous.integrable_of_hasCompactSupport_riemannianVolumeMeasure
      (I := I_half n) q
      (u.smooth.continuous.mul (tangentSectionAction_continuous q Y v))
      (HasCompactSupport.of_compactSpace _)
  rw [hleft, integral_add hA hB, hright] at hibp
  exact hibp

private theorem dirichletDirectionalDerivativeSmooth_ae_tangentSectionAction
    (q : SmoothRiemannianMetric (I_half n) M)
    (Y : Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (v : SmoothScalarDirichlet q) :
    (dirichletDirectionalDerivativeSmooth q Y v : M → ℝ) =ᵐ[
        riemannianVolumeMeasure (I := I_half n) (M := M) q]
      tangentSectionAction (I := I_half n) Y v.toFun := by
  filter_upwards [dirichletDirectionalDerivativeSmooth_coeFn q Y v] with x hx
  rw [hx, tangentSectionAction_grad_g_with_boundary_eq_inner (I := I_half n) q Y x]
  rfl

theorem inner_dirichletDirectionalDerivativeCLM_add_inner
    (q : SmoothRiemannianMetric (I_half n) M)
    (Y : Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (u v : H1ComplDirichlet q) :
    inner ℝ (dirichletDirectionalDerivativeCLM q Y u) (H1ComplDirichletToLp q v) +
      inner ℝ (H1ComplDirichletToLp q u) (dirichletDirectionalDerivativeCLM q Y v) =
      -inner ℝ (H1ComplDirichletToLp q u)
        (smoothMulLp q ⟨divergence (I := I_half n)
          (leviCivitaConnectionOfMetric (I := I_half n) q) Y,
            leviCivita_divergence_contMDiff q Y⟩ (H1ComplDirichletToLp q v)) := by
  let b : C^∞⟮I_half n, M; ℝ⟯ :=
    ⟨divergence (I := I_half n) (leviCivitaConnectionOfMetric (I := I_half n) q) Y,
      leviCivita_divergence_contMDiff q Y⟩
  change inner ℝ (dirichletDirectionalDerivativeCLM q Y u) (H1ComplDirichletToLp q v) +
      inner ℝ (H1ComplDirichletToLp q u) (dirichletDirectionalDerivativeCLM q Y v) =
      -inner ℝ (H1ComplDirichletToLp q u) (smoothMulLp q b (H1ComplDirichletToLp q v))
  refine UniformSpace.Completion.induction_on₂ (α := SmoothScalarDirichlet q)
    (β := SmoothScalarDirichlet q) u v (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro u v
  change inner ℝ (dirichletDirectionalDerivativeCLM q Y (smoothToH1ComplDirichlet q u))
      (H1ComplDirichletToLp q (smoothToH1ComplDirichlet q v)) +
    inner ℝ (H1ComplDirichletToLp q (smoothToH1ComplDirichlet q u))
      (dirichletDirectionalDerivativeCLM q Y (smoothToH1ComplDirichlet q v)) =
    -inner ℝ (H1ComplDirichletToLp q (smoothToH1ComplDirichlet q u))
      (smoothMulLp q b (H1ComplDirichletToLp q (smoothToH1ComplDirichlet q v)))
  rw [dirichletDirectionalDerivativeCLM_smoothToH1ComplDirichlet,
    dirichletDirectionalDerivativeCLM_smoothToH1ComplDirichlet,
    H1ComplDirichletToLp_smoothToH1ComplDirichlet,
    H1ComplDirichletToLp_smoothToH1ComplDirichlet]
  have hu : (smoothToLpDirichlet q u : M → ℝ) =ᵐ[
      riemannianVolumeMeasure (I := I_half n) (M := M) q] u.toFun :=
    MemLp.coeFn_toLp u.memLp_two
  have hv : (smoothToLpDirichlet q v : M → ℝ) =ᵐ[
      riemannianVolumeMeasure (I := I_half n) (M := M) q] v.toFun :=
    MemLp.coeFn_toLp v.memLp_two
  have hleft : inner ℝ (dirichletDirectionalDerivativeSmooth q Y u)
      (smoothToLpDirichlet q v) =
      ∫ x, tangentSectionAction (I := I_half n) Y u.toFun x * v.toFun x
        ∂(riemannianVolumeMeasure (I := I_half n) (M := M) q) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [dirichletDirectionalDerivativeSmooth_ae_tangentSectionAction q Y u, hv]
      with x hux hvx
    rw [hux, hvx, Real.inner_apply]
  have hright : inner ℝ (smoothToLpDirichlet q u)
      (dirichletDirectionalDerivativeSmooth q Y v) =
      ∫ x, u.toFun x * tangentSectionAction (I := I_half n) Y v.toFun x
        ∂(riemannianVolumeMeasure (I := I_half n) (M := M) q) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hu, dirichletDirectionalDerivativeSmooth_ae_tangentSectionAction q Y v]
      with x hux hvx
    rw [hux, hvx, Real.inner_apply]
  have hdiv : inner ℝ (smoothToLpDirichlet q u)
      (smoothMulLp q b (smoothToLpDirichlet q v)) =
      ∫ x, u.toFun x * v.toFun x * divergence (I := I_half n)
        (leviCivitaConnectionOfMetric (I := I_half n) q) Y x
        ∂(riemannianVolumeMeasure (I := I_half n) (M := M) q) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hu, hv, smoothMulLp_apply_coeFn q b (smoothToLpDirichlet q v)]
      with x hux hvx hmx
    rw [hux, hmx, hvx, Real.inner_apply]
    change u.toFun x * (divergence (I := I_half n)
      (leviCivitaConnectionOfMetric (I := I_half n) q) Y x * v.toFun x) = _
    ring
  rw [hleft, hright, hdiv]
  exact integral_tangentSectionAction_mul_add q Y u v

theorem integral_dirichletDirectionalDerivativeCLM_mul_smooth
    (q : SmoothRiemannianMetric (I_half n) M)
    (Y : Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (u : H1ComplDirichlet q) (v : SmoothScalarDirichlet q) :
    (∫ x, dirichletDirectionalDerivativeCLM q Y u x * v.toFun x
        ∂(riemannianVolumeMeasure (I := I_half n) (M := M) q)) =
      -∫ x, H1ComplDirichletToLp q u x *
        (tangentSectionAction (I := I_half n) Y v.toFun x +
          divergence (I := I_half n)
            (leviCivitaConnectionOfMetric (I := I_half n) q) Y x * v.toFun x)
        ∂(riemannianVolumeMeasure (I := I_half n) (M := M) q) := by
  let b : C^∞⟮I_half n, M; ℝ⟯ :=
    ⟨divergence (I := I_half n) (leviCivitaConnectionOfMetric (I := I_half n) q) Y,
      leviCivita_divergence_contMDiff q Y⟩
  have hgreen := inner_dirichletDirectionalDerivativeCLM_add_inner q Y u
    (smoothToH1ComplDirichlet q v)
  rw [H1ComplDirichletToLp_smoothToH1ComplDirichlet,
    dirichletDirectionalDerivativeCLM_smoothToH1ComplDirichlet] at hgreen
  have heq : inner ℝ (dirichletDirectionalDerivativeCLM q Y u) (smoothToLpDirichlet q v) =
      -inner ℝ (H1ComplDirichletToLp q u)
        (dirichletDirectionalDerivativeSmooth q Y v +
          smoothMulLp q b (smoothToLpDirichlet q v)) := by
    rw [inner_add_right]
    change _ + _ = -inner ℝ (H1ComplDirichletToLp q u)
      (smoothMulLp q b (smoothToLpDirichlet q v)) at hgreen
    linarith
  have hv : (smoothToLpDirichlet q v : M → ℝ) =ᵐ[
      riemannianVolumeMeasure (I := I_half n) (M := M) q] v.toFun :=
    MemLp.coeFn_toLp v.memLp_two
  have hleft : inner ℝ (dirichletDirectionalDerivativeCLM q Y u) (smoothToLpDirichlet q v) =
      ∫ x, dirichletDirectionalDerivativeCLM q Y u x * v.toFun x
        ∂(riemannianVolumeMeasure (I := I_half n) (M := M) q) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hv] with x hx
    rw [hx, Real.inner_apply]
  have hright : inner ℝ (H1ComplDirichletToLp q u)
      (dirichletDirectionalDerivativeSmooth q Y v +
        smoothMulLp q b (smoothToLpDirichlet q v)) =
      ∫ x, H1ComplDirichletToLp q u x *
        (tangentSectionAction (I := I_half n) Y v.toFun x +
          divergence (I := I_half n)
            (leviCivitaConnectionOfMetric (I := I_half n) q) Y x * v.toFun x)
        ∂(riemannianVolumeMeasure (I := I_half n) (M := M) q) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hv, dirichletDirectionalDerivativeSmooth_ae_tangentSectionAction q Y v,
      smoothMulLp_apply_coeFn q b (smoothToLpDirichlet q v),
      Lp.coeFn_add (dirichletDirectionalDerivativeSmooth q Y v)
        (smoothMulLp q b (smoothToLpDirichlet q v))] with x hvx hdx hmx hax
    rw [hax, Pi.add_apply, hdx, hmx, hvx, Real.inner_apply]
    rfl
  rwa [hleft, hright] at heq

end DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
