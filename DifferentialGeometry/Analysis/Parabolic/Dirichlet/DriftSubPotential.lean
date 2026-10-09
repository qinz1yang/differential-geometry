import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletWeakDerivative
import DifferentialGeometry.Analysis.Elliptic.Regularity.SmoothScalar.MulLp
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
  (tangentSectionAction_grad_g_with_boundary_eq_inner)
open DifferentialGeometry.Integral.DivergenceTheorem (tangentSectionAction)
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

theorem dirichletDriftSubPotentialForm_apply_H1ComplDirichlet
    (q : SmoothRiemannianMetric (I_half n) M)
    (Y : Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (a : C^∞⟮I_half n, M; ℝ⟯)
    (u v : H1ComplDirichlet q) :
    dirichletDriftSubPotentialForm q Y a (H1ComplDirichletToLp q u) v =
      inner ℝ (dirichletDirectionalDerivativeCLM q Y u) (H1ComplDirichletToLp q v) -
        inner ℝ (H1ComplDirichletToLp q u) (smoothMulLp q a (H1ComplDirichletToLp q v)) := by
  let b : C^∞⟮I_half n, M; ℝ⟯ :=
    ⟨divergence (I := I_half n) (leviCivitaConnectionOfMetric (I := I_half n) q) Y,
      leviCivita_divergence_contMDiff q Y⟩
  have hsplit : smoothMulLp q (driftSubPotentialAdjointCoefficient q Y a)
      (H1ComplDirichletToLp q v) =
      smoothMulLp q b (H1ComplDirichletToLp q v) +
        smoothMulLp q a (H1ComplDirichletToLp q v) := by
    apply Lp.ext
    filter_upwards [smoothMulLp_apply_coeFn q (driftSubPotentialAdjointCoefficient q Y a)
        (H1ComplDirichletToLp q v),
      smoothMulLp_apply_coeFn q b (H1ComplDirichletToLp q v),
      smoothMulLp_apply_coeFn q a (H1ComplDirichletToLp q v),
      Lp.coeFn_add (smoothMulLp q b (H1ComplDirichletToLp q v))
        (smoothMulLp q a (H1ComplDirichletToLp q v))] with x hcx hbx hax hsx
    rw [hsx, Pi.add_apply, hcx, hbx, hax]
    change (divergence (I := I_half n)
      (leviCivitaConnectionOfMetric (I := I_half n) q) Y x + a x) *
        H1ComplDirichletToLp q v x = _
    exact add_mul _ _ _
  have hgreen := inner_dirichletDirectionalDerivativeCLM_add_inner q Y u v
  rw [dirichletDriftSubPotentialForm, ContinuousLinearMap.bilinearComp_apply,
    ContinuousLinearMap.id_apply, innerSL_apply_apply, dirichletDriftSubPotentialAdjoint,
    neg_apply, add_apply, ContinuousLinearMap.comp_apply, hsplit, inner_neg_right,
    inner_add_right, inner_add_right]
  change _ + _ = -inner ℝ (H1ComplDirichletToLp q u)
    (smoothMulLp q b (H1ComplDirichletToLp q v)) at hgreen
  linarith

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
  rw [← H1ComplDirichletToLp_smoothToH1ComplDirichlet q u,
    dirichletDriftSubPotentialForm_apply_H1ComplDirichlet,
    dirichletDirectionalDerivativeCLM_smoothToH1ComplDirichlet,
    H1ComplDirichletToLp_smoothToH1ComplDirichlet,
    H1ComplDirichletToLp_smoothToH1ComplDirichlet]
  have hu : (smoothToLpDirichlet q u : M → ℝ) =ᵐ[
      riemannianVolumeMeasure (I := I_half n) (M := M) q] u.toFun :=
    MemLp.coeFn_toLp u.memLp_two
  have hv : (smoothToLpDirichlet q v : M → ℝ) =ᵐ[
      riemannianVolumeMeasure (I := I_half n) (M := M) q] v.toFun :=
    MemLp.coeFn_toLp v.memLp_two
  congr 1
  · rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [dirichletDirectionalDerivativeSmooth_coeFn q Y u, hv] with x hdx hvx
    rw [hdx, hvx, Real.inner_apply,
      tangentSectionAction_grad_g_with_boundary_eq_inner (I := I_half n) q Y x]
    rfl
  · rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hu, hv, smoothMulLp_apply_coeFn q a (smoothToLpDirichlet q v)]
      with x hux hvx hmx
    rw [hux, hmx, hvx, Real.inner_apply]
    ring

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

theorem dirichletDriftSubPotentialForm_apply_smooth_right
    (q : SmoothRiemannianMetric (I_half n) M)
    (Y : Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (a : C^∞⟮I_half n, M; ℝ⟯)
    (u : Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) q))
    (v : SmoothScalarDirichlet q) :
    dirichletDriftSubPotentialForm q Y a u (smoothToH1ComplDirichlet q v) =
      -∫ x, u x * (tangentSectionAction (I := I_half n) Y v.toFun x +
        (divergence (I := I_half n) (leviCivitaConnectionOfMetric (I := I_half n) q) Y x + a x) *
          v.toFun x) ∂riemannianVolumeMeasure (I := I_half n) (M := M) q := by
  rw [dirichletDriftSubPotentialForm, ContinuousLinearMap.bilinearComp_apply,
    ContinuousLinearMap.id_apply, innerSL_apply_apply, dirichletDriftSubPotentialAdjoint,
    neg_apply, add_apply, ContinuousLinearMap.comp_apply,
    dirichletDirectionalDerivativeCLM_smoothToH1ComplDirichlet,
    H1ComplDirichletToLp_smoothToH1ComplDirichlet, inner_neg_right, L2.inner_def]
  congr 1
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_add (dirichletDirectionalDerivativeSmooth q Y v)
      (smoothMulLp q (driftSubPotentialAdjointCoefficient q Y a) (smoothToLpDirichlet q v)),
    dirichletDirectionalDerivativeSmooth_coeFn q Y v,
    smoothMulLp_apply_coeFn q (driftSubPotentialAdjointCoefficient q Y a) (smoothToLpDirichlet q v),
    v.memLp_two.coeFn_toLp] with x hs hd hm hv
  change smoothToLpDirichlet q v x = v.toFun x at hv
  rw [Real.inner_apply, hs, Pi.add_apply, hd, hm, hv,
    tangentSectionAction_grad_g_with_boundary_eq_inner (I := I_half n) q Y x]
  rfl

theorem dirichletHsNegOneEquivH1Dual_driftSubPotential_apply_smooth_right
    (q : SmoothRiemannianMetric (I_half n) M)
    (Y : Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (a : C^∞⟮I_half n, M; ℝ⟯)
    (u : DirichletHs q 0) (v : SmoothScalarDirichlet q) :
    dirichletHsNegOneEquivH1Dual q (dirichletDriftSubPotential q Y a u)
        (smoothToH1ComplDirichlet q v) =
      -∫ x, dirichletHsZeroEquivL2 q u x *
        (tangentSectionAction (I := I_half n) Y v.toFun x +
          (divergence (I := I_half n) (leviCivitaConnectionOfMetric (I := I_half n) q) Y x + a x) *
            v.toFun x) ∂riemannianVolumeMeasure (I := I_half n) (M := M) q := by
  rw [dirichletHsNegOneEquivH1Dual_driftSubPotential,
    dirichletDriftSubPotentialForm_apply_smooth_right]

end DifferentialGeometry.Analysis.Parabolic.Dirichlet

end
