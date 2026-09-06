import DifferentialGeometry.Geometry.Connection.DivergenceCovariantTrace
import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletDirectionalDerivative
import DifferentialGeometry.Analysis.Elliptic.Regularity.SmoothScalar.MulLp
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.WithBoundary.Divergence.IntegrationByParts
import DifferentialGeometry.Analysis.Sobolev.DirichletHs.EnergyDuality
import DifferentialGeometry.Geometry.Operator.Divergence

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped ContDiff InnerProductSpace Manifold RealInnerProductSpace Topology

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet

open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
open DifferentialGeometry.Analysis.Sobolev.Hs
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

private local instance driftSubPotentialFormSeminormed
    {q : SmoothRiemannianMetric (I_half n) M} :
    SeminormedAddCommGroup
      (Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) q) →L[ℝ]
        H1ComplDirichlet q →L[ℝ] ℝ) :=
  @ContinuousLinearMap.toSeminormedAddCommGroup ℝ ℝ
    (Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) q))
    (H1ComplDirichlet q →L[ℝ] ℝ)
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (RingHom.id ℝ) inferInstance

private local instance driftSubPotentialAdjointSeminormed
    {q : SmoothRiemannianMetric (I_half n) M} :
    SeminormedAddCommGroup
      (H1ComplDirichlet q →L[ℝ]
        Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) q)) :=
  @ContinuousLinearMap.toSeminormedAddCommGroup ℝ ℝ
    (H1ComplDirichlet q)
    (Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) q))
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (RingHom.id ℝ) inferInstance

private noncomputable def driftSubPotentialAdjointCoefficient
    (q : SmoothRiemannianMetric (I_half n) M)
    (Y : Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (a : C^∞⟮I_half n, M; ℝ⟯) : C^∞⟮I_half n, M; ℝ⟯ :=
  ⟨fun x => divergence (I := I_half n)
      (leviCivitaConnectionOfMetric (I := I_half n) q) Y x + a x,
    (leviCivita_divergence_contMDiff q Y).add a.contMDiff⟩

private noncomputable def dirichletDriftSubPotentialAdjoint
    (q : SmoothRiemannianMetric (I_half n) M)
    (Y : Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (a : C^∞⟮I_half n, M; ℝ⟯) :
    H1ComplDirichlet q →L[ℝ]
      Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) q) :=
  -(dirichletDirectionalDerivativeCLM q Y +
    (smoothMulLp q (driftSubPotentialAdjointCoefficient q Y a)).comp
      (H1ComplDirichletToLp q))

noncomputable def dirichletDriftSubPotentialForm
    (q : SmoothRiemannianMetric (I_half n) M)
    (Y : Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (a : C^∞⟮I_half n, M; ℝ⟯) :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) q) →L[ℝ]
      H1ComplDirichlet q →L[ℝ] ℝ :=
  (innerSL ℝ).bilinearComp
    (ContinuousLinearMap.id ℝ _)
    (dirichletDriftSubPotentialAdjoint q Y a)

noncomputable def dirichletDriftSubPotential
    (q : SmoothRiemannianMetric (I_half n) M)
    (Y : Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (a : C^∞⟮I_half n, M; ℝ⟯) :
    DirichletHs q 0 →L[ℝ] DirichletHs q (-1) :=
  dirichletL2BilinearFormToHs q (dirichletDriftSubPotentialForm q Y a)

private theorem norm_dirichletDriftSubPotentialAdjoint_le
    (q : SmoothRiemannianMetric (I_half n) M)
    (Y : Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (a : C^∞⟮I_half n, M; ℝ⟯) :
    ‖dirichletDriftSubPotentialAdjoint q Y a‖ ≤
      ‖dirichletDirectionalDerivativeCLM q Y‖ +
        ‖smoothMulLp q (driftSubPotentialAdjointCoefficient q Y a)‖ *
          ‖H1ComplDirichletToLp q‖ := by
  rw [dirichletDriftSubPotentialAdjoint, norm_neg]
  exact (norm_add_le _ _).trans
    (add_le_add (le_refl ‖dirichletDirectionalDerivativeCLM q Y‖)
      (ContinuousLinearMap.opNorm_comp_le
        (smoothMulLp q (driftSubPotentialAdjointCoefficient q Y a))
        (H1ComplDirichletToLp q)))

private theorem norm_dirichletDriftSubPotentialForm_le_adjoint
    (q : SmoothRiemannianMetric (I_half n) M)
    (Y : Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (a : C^∞⟮I_half n, M; ℝ⟯) :
    ‖dirichletDriftSubPotentialForm q Y a‖ ≤
      ‖dirichletDriftSubPotentialAdjoint q Y a‖ := by
  apply ContinuousLinearMap.opNorm_le_bound₂ (dirichletDriftSubPotentialForm q Y a)
    (norm_nonneg (dirichletDriftSubPotentialAdjoint q Y a))
  intro u v
  rw [dirichletDriftSubPotentialForm, ContinuousLinearMap.bilinearComp_apply,
    ContinuousLinearMap.id_apply]
  calc
    ‖inner ℝ u (dirichletDriftSubPotentialAdjoint q Y a v)‖ ≤
        ‖u‖ * ‖dirichletDriftSubPotentialAdjoint q Y a v‖ :=
      abs_real_inner_le_norm u (dirichletDriftSubPotentialAdjoint q Y a v)
    _ ≤ ‖u‖ * (‖dirichletDriftSubPotentialAdjoint q Y a‖ * ‖v‖) := by
      gcongr
      exact (dirichletDriftSubPotentialAdjoint q Y a).le_opNorm v
    _ = ‖dirichletDriftSubPotentialAdjoint q Y a‖ * ‖u‖ * ‖v‖ := by ring

theorem norm_dirichletDriftSubPotentialForm_le_of_bound
    (q : SmoothRiemannianMetric (I_half n) M)
    (Y : Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (a : C^∞⟮I_half n, M; ℝ⟯)
    {B C : ℝ} (hB : 0 ≤ B)
    (hY : ∀ x : M, q.inner x (Y x) (Y x) ≤ B)
    (hC : 0 ≤ C)
    (hcoeff : ∀ x : M,
      |divergence (I := I_half n)
          (leviCivitaConnectionOfMetric (I := I_half n) q) Y x + a x| ≤ C) :
    ‖dirichletDriftSubPotentialForm q Y a‖ ≤
      Real.sqrt B + C * ‖H1ComplDirichletToLp q‖ := by
  calc
    ‖dirichletDriftSubPotentialForm q Y a‖ ≤
        ‖dirichletDriftSubPotentialAdjoint q Y a‖ :=
      norm_dirichletDriftSubPotentialForm_le_adjoint q Y a
    _ ≤ ‖dirichletDirectionalDerivativeCLM q Y‖ +
        ‖smoothMulLp q (driftSubPotentialAdjointCoefficient q Y a)‖ *
          ‖H1ComplDirichletToLp q‖ :=
      norm_dirichletDriftSubPotentialAdjoint_le q Y a
    _ ≤ Real.sqrt B + C * ‖H1ComplDirichletToLp q‖ := by
      apply add_le_add
      · exact norm_dirichletDirectionalDerivativeCLM_le q Y hB hY
      · apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        exact norm_smoothMulLp_le_of_bound q
          (driftSubPotentialAdjointCoefficient q Y a) hC hcoeff

theorem norm_dirichletDriftSubPotential_le_of_bound
    (q : SmoothRiemannianMetric (I_half n) M)
    (Y : Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (a : C^∞⟮I_half n, M; ℝ⟯)
    {B C : ℝ} (hB : 0 ≤ B)
    (hY : ∀ x : M, q.inner x (Y x) (Y x) ≤ B)
    (hC : 0 ≤ C)
    (hcoeff : ∀ x : M,
      |divergence (I := I_half n)
          (leviCivitaConnectionOfMetric (I := I_half n) q) Y x + a x| ≤ C) :
    ‖dirichletDriftSubPotential q Y a‖ ≤
      Real.sqrt B + C * ‖H1ComplDirichletToLp q‖ := by
  exact (dirichletL2BilinearFormToHs_norm_le q
    (dirichletDriftSubPotentialForm q Y a)).trans
      (norm_dirichletDriftSubPotentialForm_le_of_bound q Y a hB hY hC hcoeff)

private theorem dirichletDriftSubPotentialAdjoint_apply_smooth
    (q : SmoothRiemannianMetric (I_half n) M)
    (Y : Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (a : C^∞⟮I_half n, M; ℝ⟯)
    (v : SmoothScalarDirichlet q) :
    dirichletDriftSubPotentialAdjoint q Y a (smoothToH1ComplDirichlet q v) =
      -(dirichletDirectionalDerivativeSmooth q Y v +
        smoothMulLp q (driftSubPotentialAdjointCoefficient q Y a)
          (smoothToLpDirichlet q v)) := by
  rw [dirichletDriftSubPotentialAdjoint, neg_apply, add_apply,
    ContinuousLinearMap.comp_apply,
    dirichletDirectionalDerivativeCLM_smoothToH1ComplDirichlet,
    H1ComplDirichletToLp_smoothToH1ComplDirichlet]

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
    integral_tangentSectionAction_eq_neg_integral_smul_divergence_with_boundary_of_hasCompactSupport
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

theorem dirichletDriftSubPotentialForm_apply_smooth
    (q : SmoothRiemannianMetric (I_half n) M)
    (Y : Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (a : C^∞⟮I_half n, M; ℝ⟯)
    (u v : SmoothScalarDirichlet q) :
    dirichletDriftSubPotentialForm q Y a (smoothToLpDirichlet q u)
        (smoothToH1ComplDirichlet q v) =
      (∫ x, tangentSectionAction (I := I_half n) Y u.toFun x * v.toFun x
          ∂(riemannianVolumeMeasure (I := I_half n) (M := M) q)) -
        ∫ x, a x * u.toFun x * v.toFun x
          ∂(riemannianVolumeMeasure (I := I_half n) (M := M) q) := by
  let μ := riemannianVolumeMeasure (I := I_half n) (M := M) q
  rw [dirichletDriftSubPotentialForm, ContinuousLinearMap.bilinearComp_apply,
    ContinuousLinearMap.id_apply, innerSL_apply_apply,
    dirichletDriftSubPotentialAdjoint_apply_smooth, L2.inner_def]
  have hu : (smoothToLpDirichlet q u : M → ℝ) =ᵐ[μ] u.toFun :=
    MemLp.coeFn_toLp u.memLp_two
  have hv : (smoothToLpDirichlet q v : M → ℝ) =ᵐ[μ] v.toFun :=
    MemLp.coeFn_toLp v.memLp_two
  have hD := dirichletDirectionalDerivativeSmooth_coeFn q Y v
  have hmul := smoothMulLp_apply_coeFn q
    (driftSubPotentialAdjointCoefficient q Y a) (smoothToLpDirichlet q v)
  have hadd := Lp.coeFn_add (dirichletDirectionalDerivativeSmooth q Y v)
    (smoothMulLp q (driftSubPotentialAdjointCoefficient q Y a)
      (smoothToLpDirichlet q v))
  have hneg := Lp.coeFn_neg
    (dirichletDirectionalDerivativeSmooth q Y v +
      smoothMulLp q (driftSubPotentialAdjointCoefficient q Y a)
        (smoothToLpDirichlet q v))
  have hpoint :
      (fun x => inner ℝ (smoothToLpDirichlet q u x)
        ((-(dirichletDirectionalDerivativeSmooth q Y v +
          smoothMulLp q (driftSubPotentialAdjointCoefficient q Y a)
            (smoothToLpDirichlet q v))) x)) =ᵐ[μ]
        fun x => -(u.toFun x *
          (tangentSectionAction (I := I_half n) Y v.toFun x +
            (divergence (I := I_half n)
              (leviCivitaConnectionOfMetric (I := I_half n) q) Y x + a x) *
              v.toFun x)) := by
    filter_upwards [hu, hv, hD, hmul, hadd, hneg]
      with x hux hvx hDx hmulx haddx hnegx
    rw [hux, hnegx, Pi.neg_apply, haddx, Pi.add_apply, hDx, hmulx, hvx]
    rw [tangentSectionAction_grad_g_with_boundary_eq_inner (I := I_half n) q Y x]
    rw [show (driftSubPotentialAdjointCoefficient q Y a) x =
      divergence (I := I_half n)
        (leviCivitaConnectionOfMetric (I := I_half n) q) Y x + a x by rfl]
    rw [Real.inner_apply,
      DifferentialGeometry.Analysis.Laplacian.WithBoundary.grad_g_with_boundary_section_apply']
    ring
  rw [integral_congr_ae hpoint]
  have hYu : Integrable (fun x : M =>
      tangentSectionAction (I := I_half n) Y u.toFun x * v.toFun x) μ :=
    DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.Continuous.integrable_of_hasCompactSupport_riemannianVolumeMeasure
      (I := I_half n) q
      ((tangentSectionAction_continuous q Y u).mul v.smooth.continuous)
      (HasCompactSupport.of_compactSpace _)
  have huYv : Integrable (fun x : M =>
      u.toFun x * tangentSectionAction (I := I_half n) Y v.toFun x) μ :=
    DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.Continuous.integrable_of_hasCompactSupport_riemannianVolumeMeasure
      (I := I_half n) q
      (u.smooth.continuous.mul (tangentSectionAction_continuous q Y v))
      (HasCompactSupport.of_compactSpace _)
  have huvdiv : Integrable (fun x : M => u.toFun x * v.toFun x *
      divergence (I := I_half n)
        (leviCivitaConnectionOfMetric (I := I_half n) q) Y x) μ :=
    DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.Continuous.integrable_of_hasCompactSupport_riemannianVolumeMeasure
      (I := I_half n) q
      ((u.smooth.continuous.mul v.smooth.continuous).mul
        (leviCivita_divergence_contMDiff q Y).continuous)
      (HasCompactSupport.of_compactSpace _)
  have hauv : Integrable (fun x : M => a x * u.toFun x * v.toFun x) μ :=
    DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.Continuous.integrable_of_hasCompactSupport_riemannianVolumeMeasure
      (I := I_half n) q
      ((a.contMDiff.continuous.mul u.smooth.continuous).mul v.smooth.continuous)
      (HasCompactSupport.of_compactSpace _)
  have hibp := integral_tangentSectionAction_mul_add q Y u v
  rw [integral_neg]
  have hrewrite :
      (fun x : M => u.toFun x *
          (tangentSectionAction (I := I_half n) Y v.toFun x +
            (divergence (I := I_half n)
              (leviCivitaConnectionOfMetric (I := I_half n) q) Y x + a x) *
              v.toFun x)) =
        (fun x => u.toFun x * tangentSectionAction (I := I_half n) Y v.toFun x +
          u.toFun x * v.toFun x * divergence (I := I_half n)
            (leviCivitaConnectionOfMetric (I := I_half n) q) Y x +
          a x * u.toFun x * v.toFun x) := by
    funext x
    ring
  rw [hrewrite]
  have hsplit₁ :
      (∫ x, u.toFun x * tangentSectionAction (I := I_half n) Y v.toFun x +
          u.toFun x * v.toFun x * divergence (I := I_half n)
            (leviCivitaConnectionOfMetric (I := I_half n) q) Y x +
          a x * u.toFun x * v.toFun x ∂μ) =
        (∫ x, u.toFun x * tangentSectionAction (I := I_half n) Y v.toFun x +
          u.toFun x * v.toFun x * divergence (I := I_half n)
            (leviCivitaConnectionOfMetric (I := I_half n) q) Y x ∂μ) +
          ∫ x, a x * u.toFun x * v.toFun x ∂μ :=
    integral_add (huYv.add huvdiv) hauv
  have hsplit₂ :
      (∫ x, u.toFun x * tangentSectionAction (I := I_half n) Y v.toFun x +
          u.toFun x * v.toFun x * divergence (I := I_half n)
            (leviCivitaConnectionOfMetric (I := I_half n) q) Y x ∂μ) =
        (∫ x, u.toFun x * tangentSectionAction (I := I_half n) Y v.toFun x ∂μ) +
          ∫ x, u.toFun x * v.toFun x * divergence (I := I_half n)
            (leviCivitaConnectionOfMetric (I := I_half n) q) Y x ∂μ :=
    integral_add huYv huvdiv
  rw [hsplit₁, hsplit₂]
  dsimp only [μ] at *
  linarith

theorem dirichletHsNegOneEquivH1Dual_driftSubPotential
    (q : SmoothRiemannianMetric (I_half n) M)
    (Y : Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (a : C^∞⟮I_half n, M; ℝ⟯)
    (u : DirichletHs q 0) :
    dirichletHsNegOneEquivH1Dual q (dirichletDriftSubPotential q Y a u) =
      dirichletDriftSubPotentialForm q Y a (dirichletHsZeroEquivL2 q u) := by
  exact dirichletHsNegOneEquivH1Dual_l2BilinearFormToHs q
    (dirichletDriftSubPotentialForm q Y a) u

theorem dirichletHsNegOneEquivH1Dual_driftSubPotential_apply_smooth
    (q : SmoothRiemannianMetric (I_half n) M)
    (Y : Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (a : C^∞⟮I_half n, M; ℝ⟯)
    (u v : SmoothScalarDirichlet q) :
    dirichletHsNegOneEquivH1Dual q
        (dirichletDriftSubPotential q Y a
          ((dirichletHsZeroEquivL2 q).symm (smoothToLpDirichlet q u)))
        (smoothToH1ComplDirichlet q v) =
      (∫ x, tangentSectionAction (I := I_half n) Y u.toFun x * v.toFun x
          ∂(riemannianVolumeMeasure (I := I_half n) (M := M) q)) -
        ∫ x, a x * u.toFun x * v.toFun x
          ∂(riemannianVolumeMeasure (I := I_half n) (M := M) q) := by
  rw [DFunLike.congr_fun
    (dirichletHsNegOneEquivH1Dual_driftSubPotential q Y a
      ((dirichletHsZeroEquivL2 q).symm (smoothToLpDirichlet q u)))
    (smoothToH1ComplDirichlet q v), LinearIsometryEquiv.apply_symm_apply]
  exact dirichletDriftSubPotentialForm_apply_smooth q Y a u v

end DifferentialGeometry.Analysis.Parabolic.Dirichlet

end
