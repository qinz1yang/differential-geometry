import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Identities.TensorCommutator
import DifferentialGeometry.Geometry.Metric.TensorInner.FiberNorm.OrthonormalFrame.TensorRS
open DifferentialGeometry.Geometry.Curvature


noncomputable section


open Bundle Manifold Set FiberBundle NormedSpace Filter CovariantDerivative
open scoped Manifold Topology ContDiff BigOperators RealInnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Elliptic

open DifferentialGeometry.Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [BoundarylessManifold I M]

private local instance clm1_ts (r s : ℕ) (x : M) :
    TopologicalSpace (Tensor0SBundle.TensorRSSpace r s I x →L[ℝ]
      Tensor0SBundle.TensorRSSpace r s I x) :=
  ContinuousLinearMap.topologicalSpace
private local instance clm1_ca (r s : ℕ) (x : M) :
    ContinuousAdd (Tensor0SBundle.TensorRSSpace r s I x →L[ℝ]
      Tensor0SBundle.TensorRSSpace r s I x) :=
  ContinuousLinearMap.topologicalAddGroup.toContinuousAdd
private local instance clm1_acm (r s : ℕ) (x : M) :
    AddCommMonoid (Tensor0SBundle.TensorRSSpace r s I x →L[ℝ]
      Tensor0SBundle.TensorRSSpace r s I x) :=
  ContinuousLinearMap.addCommMonoid
private local instance clm1_mod (r s : ℕ) (x : M) :
    Module ℝ (Tensor0SBundle.TensorRSSpace r s I x →L[ℝ]
      Tensor0SBundle.TensorRSSpace r s I x) :=
  ContinuousLinearMap.module
private local instance clm2_ts (r s : ℕ) (x : M) :
    TopologicalSpace (TangentSpace I x →L[ℝ] Tensor0SBundle.TensorRSSpace r s I x →L[ℝ]
      Tensor0SBundle.TensorRSSpace r s I x) :=
  ContinuousLinearMap.topologicalSpace
private local instance clm2_ca (r s : ℕ) (x : M) :
    ContinuousAdd (TangentSpace I x →L[ℝ] Tensor0SBundle.TensorRSSpace r s I x →L[ℝ]
      Tensor0SBundle.TensorRSSpace r s I x) :=
  ContinuousLinearMap.topologicalAddGroup.toContinuousAdd
private local instance clm2_acm (r s : ℕ) (x : M) :
    AddCommMonoid (TangentSpace I x →L[ℝ] Tensor0SBundle.TensorRSSpace r s I x →L[ℝ]
      Tensor0SBundle.TensorRSSpace r s I x) :=
  ContinuousLinearMap.addCommMonoid
private local instance clm2_mod (r s : ℕ) (x : M) :
    Module ℝ (TangentSpace I x →L[ℝ] Tensor0SBundle.TensorRSSpace r s I x →L[ℝ]
      Tensor0SBundle.TensorRSSpace r s I x) :=
  ContinuousLinearMap.module

private lemma clmFinsetSum {X Y : Type*}
    [TopologicalSpace X] [AddCommMonoid X] [Module ℝ X]
    [TopologicalSpace Y] [AddCommMonoid Y] [Module ℝ Y]
    {ι : Type*} (f : X →L[ℝ] Y) (t : Finset ι) (u : ι → X) :
    f (∑ i ∈ t, u i) = ∑ i ∈ t, f (u i) := by
  classical
  induction t using Finset.induction with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, ContinuousLinearMap.map_zero]
  | insert i A hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, ContinuousLinearMap.map_add, ih]

omit [NeZero (Module.finrank ℝ E)] in
lemma riemannOp_tensorCovS_frame_expand
    (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (hv_expand : ∀ u : TangentSpace I x, u = ∑ i : Fin n, g.inner x (e i) u • e i)
    (v w : TangentSpace I x) (T : TensorRSSpace 0 s I x) :
    riemannOp (tensorCov (I := I) g 0 s) x v w T =
      ∑ i : Fin n, ∑ j : Fin n,
        (g.inner x (e i) v * g.inner x (e j) w) •
          riemannOp (tensorCov (I := I) g 0 s) x (e i) (e j) T := by
  classical
  set R := riemannOp (tensorCov (I := I) g 0 s) x with hR_def
  have hv : v = ∑ i : Fin n, g.inner x (e i) v • e i := hv_expand v
  have hw : w = ∑ j : Fin n, g.inner x (e j) w • e j := hv_expand w
  have hRv : R v = ∑ i : Fin n, g.inner x (e i) v • R (e i) := by
    conv_lhs => rw [hv]
    rw [clmFinsetSum R]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [ContinuousLinearMap.map_smul]
  have hRvw : R v w = ∑ i : Fin n, g.inner x (e i) v • R (e i) w := by
    rw [hRv, sum_apply]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [smul_apply]
  have hRei_w : ∀ i : Fin n, R (e i) w =
      ∑ j : Fin n, g.inner x (e j) w • R (e i) (e j) := by
    intro i
    conv_lhs => rw [hw]
    rw [clmFinsetSum (R (e i))]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [ContinuousLinearMap.map_smul]
  have hRvwT : R v w T = ∑ i : Fin n, g.inner x (e i) v • (R (e i) w) T := by
    rw [hRvw, sum_apply]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [smul_apply]
  rw [hRvwT]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [hRei_w i]
  rw [sum_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [smul_apply, smul_smul]

omit [NeZero (Module.finrank ℝ E)] in
lemma fiberNormSqSummand_riemannOp_tensorCovS_vw_le
    (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (hpars : ∀ u : TangentSpace I x, ∑ i : Fin n, g.inner x (e i) u ^ 2 = g.inner x u u)
    (hexpand : ∀ u : TangentSpace I x, u = ∑ i : Fin n, g.inner x (e i) u • e i)
    (v w : TangentSpace I x) (T : TensorRSSpace 0 s I x)
    (K : Fin 0 → Fin n) (J : Fin s → Fin n) :
    fiberNormSqSummand (I := I) (M := M) g x 0 s
        (riemannOp (tensorCov (I := I) g 0 s) x v w T) n e K J ≤
      g.inner x v v * g.inner x w w *
        ∑ i : Fin n, ∑ j : Fin n,
          fiberNormSqSummand (I := I) (M := M) g x 0 s
            (riemannOp (tensorCov (I := I) g 0 s) x (e i) (e j) T) n e K J := by
  classical
  set R := riemannOp (tensorCov (I := I) g 0 s) x with hR_def
  have hexp : R v w T =
      ∑ i : Fin n, ∑ j : Fin n,
        (g.inner x (e i) v * g.inner x (e j) w) • R (e i) (e j) T :=
    riemannOp_tensorCovS_frame_expand (I := I) (M := M) g x s e hexpand v w T
  set c : Fin n × Fin n → ℝ := fun p => g.inner x (e p.1) v * g.inner x (e p.2) w with hc_def
  set a : Fin n × Fin n → ℝ := fun p =>
    fiberNormSqComponent (I := I) (M := M) g x 0 s (R (e p.1) (e p.2) T) n e K J with ha_def
  have hcomp_eq :
      fiberNormSqComponent (I := I) (M := M) g x 0 s (R v w T) n e K J =
        ∑ p : Fin n × Fin n, c p * a p := by
    rw [hexp]
    rw [show (∑ i : Fin n, ∑ j : Fin n,
          (g.inner x (e i) v * g.inner x (e j) w) • R (e i) (e j) T) =
        ∑ p : Fin n × Fin n,
          (g.inner x (e p.1) v * g.inner x (e p.2) w) • R (e p.1) (e p.2) T from
      (Fintype.sum_prod_type'
        (f := fun i j => (g.inner x (e i) v * g.inner x (e j) w) • R (e i) (e j) T)).symm]
    rw [fiberNormSqComponent_sum]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [fiberNormSqComponent_smul]
  rw [fiberNormSqSummand_eq_component_sq, hcomp_eq]
  have hCS : (∑ p : Fin n × Fin n, c p * a p) ^ 2 ≤
      (∑ p : Fin n × Fin n, c p ^ 2) * ∑ p : Fin n × Fin n, a p ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ c a
  refine hCS.trans ?_
  have hcsq : (∑ p : Fin n × Fin n, c p ^ 2) =
      g.inner x v v * g.inner x w w := by
    have hsplit : (∑ p : Fin n × Fin n, c p ^ 2) =
        (∑ i : Fin n, g.inner x (e i) v ^ 2) *
          ∑ j : Fin n, g.inner x (e j) w ^ 2 := by
      rw [Finset.sum_mul_sum]
      rw [Fintype.sum_prod_type (f := fun p : Fin n × Fin n => c p ^ 2)]
      refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
      rw [hc_def]
      ring
    rw [hsplit, hpars v, hpars w]
  have hasq : (∑ p : Fin n × Fin n, a p ^ 2) =
      ∑ i : Fin n, ∑ j : Fin n,
        fiberNormSqSummand (I := I) (M := M) g x 0 s (R (e i) (e j) T) n e K J := by
    rw [Fintype.sum_prod_type (f := fun p : Fin n × Fin n => a p ^ 2)]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    rw [ha_def, fiberNormSqSummand_eq_component_sq]
  rw [hcsq, hasq]

omit [NeZero (Module.finrank ℝ E)] in
lemma sum_riemannianFiberNormSq_riemannOpS_le_Cx
    (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (bse : Module.Basis (Fin n) ℝ (TangentSpace I x))
    (hbse : ∀ i : Fin n, bse i = e i)
    (horth : ∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0)
    (hrepr : ∀ S : TensorRSSpace 0 s I x,
      riemannianFiberNormSq (I := I) (M := M) g 0 s x S =
        ∑ K : Fin 0 → Fin n, ∑ J : Fin s → Fin n,
          fiberNormSqSummand (I := I) (M := M) g x 0 s S n e K J)
    (T : TensorRSSpace 0 s I x) :
    (∑ i : Fin n, ∑ j : Fin n,
        riemannianFiberNormSq (I := I) (M := M) g 0 s x
          (riemannOp (tensorCov (I := I) g 0 s) x (e i) (e j) T)) ≤
      (∑ i : Fin n, ∑ j : Fin n, ∑ J : Fin s → Fin n,
          riemannianFiberNormSq (I := I) (M := M) g 0 s x
            (riemannOp (tensorCov (I := I) g 0 s) x (e i) (e j)
              (dualTensorFrameS (I := I) (M := M) g x s e J))) *
        riemannianFiberNormSq (I := I) (M := M) g 0 s x T := by
  classical
  let K₀ : Fin 0 → Fin n := fun k => k.elim0
  set R := riemannOp (tensorCov (I := I) g 0 s) x with hR_def
  have hParseval := riemannianFiberNormSq_eq_sum_componentS_sq
    (I := I) (M := M) g x s e hrepr T K₀
  have hTexp := tensorS_dualFrame_expansion (I := I) (M := M) g x s e bse hbse horth T K₀
  set cT : (Fin s → Fin n) → ℝ :=
    fun J => fiberNormSqComponent (I := I) (M := M) g x 0 s T n e K₀ J with hcT
  have hpair : ∀ i j : Fin n,
      riemannianFiberNormSq (I := I) (M := M) g 0 s x (R (e i) (e j) T) ≤
        (∑ J : Fin s → Fin n,
            riemannianFiberNormSq (I := I) (M := M) g 0 s x
              (R (e i) (e j) (dualTensorFrameS (I := I) (M := M) g x s e J))) *
          riemannianFiberNormSq (I := I) (M := M) g 0 s x T := by
    intro i j
    have hRT : R (e i) (e j) T =
        ∑ J : Fin s → Fin n,
          cT J • R (e i) (e j) (dualTensorFrameS (I := I) (M := M) g x s e J) := by
      conv_lhs => rw [hTexp]
      rw [clmFinsetSum (R (e i) (e j))]
      refine Finset.sum_congr rfl (fun J _ => ?_)
      rw [ContinuousLinearMap.map_smul]
    rw [hRT]
    rw [hrepr (∑ J : Fin s → Fin n,
      cT J • R (e i) (e j) (dualTensorFrameS (I := I) (M := M) g x s e J))]
    have hterm : ∀ (Kx : Fin 0 → Fin n) (Jx : Fin s → Fin n),
        fiberNormSqSummand (I := I) (M := M) g x 0 s
            (∑ J : Fin s → Fin n,
              cT J • R (e i) (e j) (dualTensorFrameS (I := I) (M := M) g x s e J))
            n e Kx Jx ≤
          (∑ J : Fin s → Fin n, cT J ^ 2) *
            ∑ J : Fin s → Fin n,
              fiberNormSqSummand (I := I) (M := M) g x 0 s
                (R (e i) (e j) (dualTensorFrameS (I := I) (M := M) g x s e J)) n e Kx Jx := by
      intro Kx Jx
      rw [fiberNormSqSummand_eq_component_sq]
      have hcomp :
          fiberNormSqComponent (I := I) (M := M) g x 0 s
              (∑ J : Fin s → Fin n,
                cT J • R (e i) (e j) (dualTensorFrameS (I := I) (M := M) g x s e J))
              n e Kx Jx =
            ∑ J : Fin s → Fin n,
              cT J *
                fiberNormSqComponent (I := I) (M := M) g x 0 s
                  (R (e i) (e j) (dualTensorFrameS (I := I) (M := M) g x s e J)) n e Kx Jx := by
        rw [fiberNormSqComponent_sum]
        refine Finset.sum_congr rfl (fun J _ => ?_)
        rw [fiberNormSqComponent_smul]
      rw [hcomp]
      exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ cT
        (fun J => fiberNormSqComponent (I := I) (M := M) g x 0 s
          (R (e i) (e j) (dualTensorFrameS (I := I) (M := M) g x s e J)) n e Kx Jx)
    calc
      (∑ Kx : Fin 0 → Fin n, ∑ Jx : Fin s → Fin n,
          fiberNormSqSummand (I := I) (M := M) g x 0 s
            (∑ J : Fin s → Fin n,
              cT J • R (e i) (e j) (dualTensorFrameS (I := I) (M := M) g x s e J))
            n e Kx Jx)
          ≤ ∑ Kx : Fin 0 → Fin n, ∑ Jx : Fin s → Fin n,
              (∑ J : Fin s → Fin n, cT J ^ 2) *
                ∑ J : Fin s → Fin n,
                  fiberNormSqSummand (I := I) (M := M) g x 0 s
                    (R (e i) (e j) (dualTensorFrameS (I := I) (M := M) g x s e J))
                    n e Kx Jx := by
            refine Finset.sum_le_sum (fun Kx _ => Finset.sum_le_sum (fun Jx _ => hterm Kx Jx))
      _ = (∑ J : Fin s → Fin n, cT J ^ 2) *
            ∑ Kx : Fin 0 → Fin n, ∑ Jx : Fin s → Fin n,
              ∑ J : Fin s → Fin n,
                fiberNormSqSummand (I := I) (M := M) g x 0 s
                  (R (e i) (e j) (dualTensorFrameS (I := I) (M := M) g x s e J))
                  n e Kx Jx := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun Kx _ => ?_)
            rw [Finset.mul_sum]
      _ = (∑ J : Fin s → Fin n, cT J ^ 2) *
            ∑ J : Fin s → Fin n,
              riemannianFiberNormSq (I := I) (M := M) g 0 s x
                (R (e i) (e j) (dualTensorFrameS (I := I) (M := M) g x s e J)) := by
            congr 1
            rw [show (∑ J : Fin s → Fin n,
                  riemannianFiberNormSq (I := I) (M := M) g 0 s x
                    (R (e i) (e j) (dualTensorFrameS (I := I) (M := M) g x s e J))) =
                ∑ J : Fin s → Fin n, ∑ Kx : Fin 0 → Fin n, ∑ Jx : Fin s → Fin n,
                  fiberNormSqSummand (I := I) (M := M) g x 0 s
                    (R (e i) (e j) (dualTensorFrameS (I := I) (M := M) g x s e J))
                    n e Kx Jx from by
              refine Finset.sum_congr rfl (fun J _ => ?_)
              rw [hrepr (R (e i) (e j) (dualTensorFrameS (I := I) (M := M) g x s e J))]]
            rw [show (∑ Kx : Fin 0 → Fin n, ∑ Jx : Fin s → Fin n, ∑ J : Fin s → Fin n,
                  fiberNormSqSummand (I := I) (M := M) g x 0 s
                    (R (e i) (e j) (dualTensorFrameS (I := I) (M := M) g x s e J))
                    n e Kx Jx) =
                ∑ Kx : Fin 0 → Fin n, ∑ J : Fin s → Fin n, ∑ Jx : Fin s → Fin n,
                  fiberNormSqSummand (I := I) (M := M) g x 0 s
                    (R (e i) (e j) (dualTensorFrameS (I := I) (M := M) g x s e J))
                    n e Kx Jx from by
              refine Finset.sum_congr rfl (fun Kx _ => ?_)
              rw [Finset.sum_comm]]
            rw [Finset.sum_comm]
      _ ≤ (∑ J : Fin s → Fin n,
              riemannianFiberNormSq (I := I) (M := M) g 0 s x
                (R (e i) (e j) (dualTensorFrameS (I := I) (M := M) g x s e J))) *
            riemannianFiberNormSq (I := I) (M := M) g 0 s x T := by
            apply le_of_eq
            rw [show (∑ J : Fin s → Fin n, cT J ^ 2) =
                riemannianFiberNormSq (I := I) (M := M) g 0 s x T from hParseval.symm]
            ring
  calc
    (∑ i : Fin n, ∑ j : Fin n,
        riemannianFiberNormSq (I := I) (M := M) g 0 s x (R (e i) (e j) T))
        ≤ ∑ i : Fin n, ∑ j : Fin n,
            (∑ J : Fin s → Fin n,
                riemannianFiberNormSq (I := I) (M := M) g 0 s x
                  (R (e i) (e j) (dualTensorFrameS (I := I) (M := M) g x s e J))) *
              riemannianFiberNormSq (I := I) (M := M) g 0 s x T := by
          refine Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hpair i j))
    _ = (∑ i : Fin n, ∑ j : Fin n, ∑ J : Fin s → Fin n,
            riemannianFiberNormSq (I := I) (M := M) g 0 s x
              (R (e i) (e j) (dualTensorFrameS (I := I) (M := M) g x s e J))) *
          riemannianFiberNormSq (I := I) (M := M) g 0 s x T := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [Finset.sum_mul]

omit [NeZero (Module.finrank ℝ E)] in
lemma riemannOp_tensorCovRS_frame_expand
    (g : SmoothRiemannianMetric I M) (x : M) (r s : ℕ)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (hv_expand : ∀ u : TangentSpace I x, u = ∑ i : Fin n, g.inner x (e i) u • e i)
    (v w : TangentSpace I x) (T : TensorRSSpace r s I x) :
    riemannOp (tensorCov (I := I) g r s) x v w T =
      ∑ i : Fin n, ∑ j : Fin n,
        (g.inner x (e i) v * g.inner x (e j) w) •
          riemannOp (tensorCov (I := I) g r s) x (e i) (e j) T := by
  classical
  set R := riemannOp (tensorCov (I := I) g r s) x with hR_def
  have hv : v = ∑ i : Fin n, g.inner x (e i) v • e i := hv_expand v
  have hw : w = ∑ j : Fin n, g.inner x (e j) w • e j := hv_expand w
  have hRv : R v = ∑ i : Fin n, g.inner x (e i) v • R (e i) := by
    conv_lhs => rw [hv]
    rw [clmFinsetSum R]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [ContinuousLinearMap.map_smul]
  have hRvw : R v w = ∑ i : Fin n, g.inner x (e i) v • R (e i) w := by
    rw [hRv, sum_apply]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [smul_apply]
  have hRei_w : ∀ i : Fin n, R (e i) w =
      ∑ j : Fin n, g.inner x (e j) w • R (e i) (e j) := by
    intro i
    conv_lhs => rw [hw]
    rw [clmFinsetSum (R (e i))]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [ContinuousLinearMap.map_smul]
  have hRvwT : R v w T = ∑ i : Fin n, g.inner x (e i) v • (R (e i) w) T := by
    rw [hRvw, sum_apply]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [smul_apply]
  rw [hRvwT]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [hRei_w i]
  rw [sum_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [smul_apply, smul_smul]

omit [NeZero (Module.finrank ℝ E)] in
lemma fiberNormSqSummand_riemannOp_tensorCovRS_vw_le
    (g : SmoothRiemannianMetric I M) (x : M) (r s : ℕ)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (hpars : ∀ u : TangentSpace I x, ∑ i : Fin n, g.inner x (e i) u ^ 2 = g.inner x u u)
    (hexpand : ∀ u : TangentSpace I x, u = ∑ i : Fin n, g.inner x (e i) u • e i)
    (v w : TangentSpace I x) (T : TensorRSSpace r s I x)
    (K : Fin r → Fin n) (J : Fin s → Fin n) :
    fiberNormSqSummand (I := I) (M := M) g x r s
        (riemannOp (tensorCov (I := I) g r s) x v w T) n e K J ≤
      g.inner x v v * g.inner x w w *
        ∑ i : Fin n, ∑ j : Fin n,
          fiberNormSqSummand (I := I) (M := M) g x r s
            (riemannOp (tensorCov (I := I) g r s) x (e i) (e j) T) n e K J := by
  classical
  set R := riemannOp (tensorCov (I := I) g r s) x with hR_def
  have hexp : R v w T =
      ∑ i : Fin n, ∑ j : Fin n,
        (g.inner x (e i) v * g.inner x (e j) w) • R (e i) (e j) T :=
    riemannOp_tensorCovRS_frame_expand (I := I) (M := M) g x r s e hexpand v w T
  set c : Fin n × Fin n → ℝ := fun p => g.inner x (e p.1) v * g.inner x (e p.2) w with hc_def
  set a : Fin n × Fin n → ℝ := fun p =>
    fiberNormSqComponent (I := I) (M := M) g x r s (R (e p.1) (e p.2) T) n e K J with ha_def
  have hcomp_eq :
      fiberNormSqComponent (I := I) (M := M) g x r s (R v w T) n e K J =
        ∑ p : Fin n × Fin n, c p * a p := by
    rw [hexp]
    rw [show (∑ i : Fin n, ∑ j : Fin n,
          (g.inner x (e i) v * g.inner x (e j) w) • R (e i) (e j) T) =
        ∑ p : Fin n × Fin n,
          (g.inner x (e p.1) v * g.inner x (e p.2) w) • R (e p.1) (e p.2) T from
      (Fintype.sum_prod_type'
        (f := fun i j => (g.inner x (e i) v * g.inner x (e j) w) • R (e i) (e j) T)).symm]
    rw [fiberNormSqComponent_sum]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [fiberNormSqComponent_smul]
  rw [fiberNormSqSummand_eq_component_sq, hcomp_eq]
  have hCS : (∑ p : Fin n × Fin n, c p * a p) ^ 2 ≤
      (∑ p : Fin n × Fin n, c p ^ 2) * ∑ p : Fin n × Fin n, a p ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ c a
  refine hCS.trans ?_
  have hcsq : (∑ p : Fin n × Fin n, c p ^ 2) =
      g.inner x v v * g.inner x w w := by
    have hsplit : (∑ p : Fin n × Fin n, c p ^ 2) =
        (∑ i : Fin n, g.inner x (e i) v ^ 2) *
          ∑ j : Fin n, g.inner x (e j) w ^ 2 := by
      rw [Finset.sum_mul_sum]
      rw [Fintype.sum_prod_type (f := fun p : Fin n × Fin n => c p ^ 2)]
      refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
      rw [hc_def]
      ring
    rw [hsplit, hpars v, hpars w]
  have hasq : (∑ p : Fin n × Fin n, a p ^ 2) =
      ∑ i : Fin n, ∑ j : Fin n,
        fiberNormSqSummand (I := I) (M := M) g x r s (R (e i) (e j) T) n e K J := by
    rw [Fintype.sum_prod_type (f := fun p : Fin n × Fin n => a p ^ 2)]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    rw [ha_def, fiberNormSqSummand_eq_component_sq]
  rw [hcsq, hasq]

omit [NeZero (Module.finrank ℝ E)] in
lemma sum_riemannianFiberNormSq_riemannOpRS_le_Cx
    (g : SmoothRiemannianMetric I M) (x : M) (r s : ℕ)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (bse : Module.Basis (Fin n) ℝ (TangentSpace I x))
    (hbse : ∀ i : Fin n, bse i = e i)
    (horth : ∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0)
    (hrepr : ∀ S : TensorRSSpace r s I x,
      riemannianFiberNormSq (I := I) (M := M) g r s x S =
        ∑ K : Fin r → Fin n, ∑ J : Fin s → Fin n,
          fiberNormSqSummand (I := I) (M := M) g x r s S n e K J)
    (T : TensorRSSpace r s I x) :
    (∑ i : Fin n, ∑ j : Fin n,
        riemannianFiberNormSq (I := I) (M := M) g r s x
          (riemannOp (tensorCov (I := I) g r s) x (e i) (e j) T)) ≤
      (∑ i : Fin n, ∑ j : Fin n, ∑ K : Fin r → Fin n, ∑ J : Fin s → Fin n,
          riemannianFiberNormSq (I := I) (M := M) g r s x
            (riemannOp (tensorCov (I := I) g r s) x (e i) (e j)
              (dualTensorFrameRS (I := I) (M := M) g x r s e K J))) *
        riemannianFiberNormSq (I := I) (M := M) g r s x T := by
  classical
  set R := riemannOp (tensorCov (I := I) g r s) x with hR_def
  have hParseval := riemannianFiberNormSq_eq_sum_componentRS_sq
    (I := I) (M := M) g x r s e hrepr T
  have hTexp := tensorRS_dualFrame_expansion (I := I) (M := M) g x r s e bse hbse horth T
  set cT : (Fin r → Fin n) × (Fin s → Fin n) → ℝ :=
    fun q => fiberNormSqComponent (I := I) (M := M) g x r s T n e q.1 q.2 with hcT
  have hpair : ∀ i j : Fin n,
      riemannianFiberNormSq (I := I) (M := M) g r s x (R (e i) (e j) T) ≤
        (∑ K : Fin r → Fin n, ∑ J : Fin s → Fin n,
            riemannianFiberNormSq (I := I) (M := M) g r s x
              (R (e i) (e j) (dualTensorFrameRS (I := I) (M := M) g x r s e K J))) *
          riemannianFiberNormSq (I := I) (M := M) g r s x T := by
    intro i j
    have hRT : R (e i) (e j) T =
        ∑ K : Fin r → Fin n, ∑ J : Fin s → Fin n,
          cT (K, J) • R (e i) (e j) (dualTensorFrameRS (I := I) (M := M) g x r s e K J) := by
      conv_lhs => rw [hTexp]
      rw [clmFinsetSum (R (e i) (e j))]
      refine Finset.sum_congr rfl (fun K _ => ?_)
      rw [clmFinsetSum (R (e i) (e j))]
      refine Finset.sum_congr rfl (fun J _ => ?_)
      rw [ContinuousLinearMap.map_smul]
    rw [hRT]
    rw [hrepr (∑ K : Fin r → Fin n, ∑ J : Fin s → Fin n,
      cT (K, J) • R (e i) (e j) (dualTensorFrameRS (I := I) (M := M) g x r s e K J))]
    have hterm : ∀ (Kx : Fin r → Fin n) (Jx : Fin s → Fin n),
        fiberNormSqSummand (I := I) (M := M) g x r s
            (∑ K : Fin r → Fin n, ∑ J : Fin s → Fin n,
              cT (K, J) • R (e i) (e j) (dualTensorFrameRS (I := I) (M := M) g x r s e K J))
            n e Kx Jx ≤
          (∑ q : (Fin r → Fin n) × (Fin s → Fin n), cT q ^ 2) *
            ∑ q : (Fin r → Fin n) × (Fin s → Fin n),
              fiberNormSqSummand (I := I) (M := M) g x r s
                (R (e i) (e j) (dualTensorFrameRS (I := I) (M := M) g x r s e q.1 q.2))
                n e Kx Jx := by
      intro Kx Jx
      rw [fiberNormSqSummand_eq_component_sq]
      have hcomp :
          fiberNormSqComponent (I := I) (M := M) g x r s
              (∑ K : Fin r → Fin n, ∑ J : Fin s → Fin n,
                cT (K, J) • R (e i) (e j) (dualTensorFrameRS (I := I) (M := M) g x r s e K J))
              n e Kx Jx =
            ∑ q : (Fin r → Fin n) × (Fin s → Fin n),
              cT q *
                fiberNormSqComponent (I := I) (M := M) g x r s
                  (R (e i) (e j) (dualTensorFrameRS (I := I) (M := M) g x r s e q.1 q.2))
                  n e Kx Jx := by
        rw [show (∑ K : Fin r → Fin n, ∑ J : Fin s → Fin n,
              cT (K, J) • R (e i) (e j) (dualTensorFrameRS (I := I) (M := M) g x r s e K J)) =
            ∑ q : (Fin r → Fin n) × (Fin s → Fin n),
              cT q • R (e i) (e j) (dualTensorFrameRS (I := I) (M := M) g x r s e q.1 q.2) from
          (Fintype.sum_prod_type'
            (f := fun K J =>
              cT (K, J) • R (e i) (e j)
                (dualTensorFrameRS (I := I) (M := M) g x r s e K J))).symm]
        rw [fiberNormSqComponent_sum]
        refine Finset.sum_congr rfl (fun q _ => ?_)
        rw [fiberNormSqComponent_smul]
      rw [hcomp]
      exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ cT
        (fun q => fiberNormSqComponent (I := I) (M := M) g x r s
          (R (e i) (e j) (dualTensorFrameRS (I := I) (M := M) g x r s e q.1 q.2)) n e Kx Jx)
    calc
      (∑ Kx : Fin r → Fin n, ∑ Jx : Fin s → Fin n,
          fiberNormSqSummand (I := I) (M := M) g x r s
            (∑ K : Fin r → Fin n, ∑ J : Fin s → Fin n,
              cT (K, J) • R (e i) (e j) (dualTensorFrameRS (I := I) (M := M) g x r s e K J))
            n e Kx Jx)
          ≤ ∑ Kx : Fin r → Fin n, ∑ Jx : Fin s → Fin n,
              (∑ q : (Fin r → Fin n) × (Fin s → Fin n), cT q ^ 2) *
                ∑ q : (Fin r → Fin n) × (Fin s → Fin n),
                  fiberNormSqSummand (I := I) (M := M) g x r s
                    (R (e i) (e j) (dualTensorFrameRS (I := I) (M := M) g x r s e q.1 q.2))
                    n e Kx Jx := by
            refine Finset.sum_le_sum (fun Kx _ => Finset.sum_le_sum (fun Jx _ => hterm Kx Jx))
      _ = (∑ q : (Fin r → Fin n) × (Fin s → Fin n), cT q ^ 2) *
            ∑ Kx : Fin r → Fin n, ∑ Jx : Fin s → Fin n,
              ∑ q : (Fin r → Fin n) × (Fin s → Fin n),
                fiberNormSqSummand (I := I) (M := M) g x r s
                  (R (e i) (e j) (dualTensorFrameRS (I := I) (M := M) g x r s e q.1 q.2))
                  n e Kx Jx := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun Kx _ => ?_)
            rw [Finset.mul_sum]
      _ = (∑ q : (Fin r → Fin n) × (Fin s → Fin n), cT q ^ 2) *
            ∑ q : (Fin r → Fin n) × (Fin s → Fin n),
              riemannianFiberNormSq (I := I) (M := M) g r s x
                (R (e i) (e j) (dualTensorFrameRS (I := I) (M := M) g x r s e q.1 q.2)) := by
            congr 1
            rw [show (∑ q : (Fin r → Fin n) × (Fin s → Fin n),
                  riemannianFiberNormSq (I := I) (M := M) g r s x
                    (R (e i) (e j) (dualTensorFrameRS (I := I) (M := M) g x r s e q.1 q.2))) =
                ∑ q : (Fin r → Fin n) × (Fin s → Fin n),
                  ∑ Kx : Fin r → Fin n, ∑ Jx : Fin s → Fin n,
                  fiberNormSqSummand (I := I) (M := M) g x r s
                    (R (e i) (e j) (dualTensorFrameRS (I := I) (M := M) g x r s e q.1 q.2))
                    n e Kx Jx from by
              refine Finset.sum_congr rfl (fun q _ => ?_)
              rw [hrepr (R (e i) (e j) (dualTensorFrameRS (I := I) (M := M) g x r s e q.1 q.2))]]
            rw [show (∑ Kx : Fin r → Fin n, ∑ Jx : Fin s → Fin n,
                  ∑ q : (Fin r → Fin n) × (Fin s → Fin n),
                  fiberNormSqSummand (I := I) (M := M) g x r s
                    (R (e i) (e j) (dualTensorFrameRS (I := I) (M := M) g x r s e q.1 q.2))
                    n e Kx Jx) =
                ∑ Kx : Fin r → Fin n,
                  ∑ q : (Fin r → Fin n) × (Fin s → Fin n), ∑ Jx : Fin s → Fin n,
                  fiberNormSqSummand (I := I) (M := M) g x r s
                    (R (e i) (e j) (dualTensorFrameRS (I := I) (M := M) g x r s e q.1 q.2))
                    n e Kx Jx from by
              refine Finset.sum_congr rfl (fun Kx _ => ?_)
              rw [Finset.sum_comm]]
            rw [Finset.sum_comm]
      _ ≤ (∑ K : Fin r → Fin n, ∑ J : Fin s → Fin n,
              riemannianFiberNormSq (I := I) (M := M) g r s x
                (R (e i) (e j) (dualTensorFrameRS (I := I) (M := M) g x r s e K J))) *
            riemannianFiberNormSq (I := I) (M := M) g r s x T := by
            apply le_of_eq
            rw [show (∑ q : (Fin r → Fin n) × (Fin s → Fin n), cT q ^ 2) =
                riemannianFiberNormSq (I := I) (M := M) g r s x T from by
              rw [hParseval, ← Fintype.sum_prod_type' (f := fun K J => cT (K, J) ^ 2)]]
            rw [show (∑ q : (Fin r → Fin n) × (Fin s → Fin n),
                  riemannianFiberNormSq (I := I) (M := M) g r s x
                    (R (e i) (e j) (dualTensorFrameRS (I := I) (M := M) g x r s e q.1 q.2))) =
                ∑ K : Fin r → Fin n, ∑ J : Fin s → Fin n,
                  riemannianFiberNormSq (I := I) (M := M) g r s x
                    (R (e i) (e j) (dualTensorFrameRS (I := I) (M := M) g x r s e K J)) from
              Fintype.sum_prod_type'
                (f := fun K J =>
                  riemannianFiberNormSq (I := I) (M := M) g r s x
                    (R (e i) (e j) (dualTensorFrameRS (I := I) (M := M) g x r s e K J)))]
            ring
  calc
    (∑ i : Fin n, ∑ j : Fin n,
        riemannianFiberNormSq (I := I) (M := M) g r s x (R (e i) (e j) T))
        ≤ ∑ i : Fin n, ∑ j : Fin n,
            (∑ K : Fin r → Fin n, ∑ J : Fin s → Fin n,
                riemannianFiberNormSq (I := I) (M := M) g r s x
                  (R (e i) (e j) (dualTensorFrameRS (I := I) (M := M) g x r s e K J))) *
              riemannianFiberNormSq (I := I) (M := M) g r s x T := by
          refine Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hpair i j))
    _ = (∑ i : Fin n, ∑ j : Fin n, ∑ K : Fin r → Fin n, ∑ J : Fin s → Fin n,
            riemannianFiberNormSq (I := I) (M := M) g r s x
              (R (e i) (e j) (dualTensorFrameRS (I := I) (M := M) g x r s e K J))) *
          riemannianFiberNormSq (I := I) (M := M) g r s x T := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [Finset.sum_mul]

omit [NeZero (Module.finrank ℝ E)] in
theorem exists_Cx_riemannianFiberNormSq_riemannOp_tensorCovS_le_rs
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M) :
    ∃ Cx : ℝ, 0 ≤ Cx ∧
      ∀ (v w : TangentSpace I x) (T : TensorRSSpace r s I x),
        riemannianFiberNormSq (I := I) (M := M) g r s x
            (riemannOp (tensorCov (I := I) g r s) x v w T) ≤
          Cx * g.inner x v v * g.inner x w w *
            riemannianFiberNormSq (I := I) (M := M) g r s x T := by
  classical
  obtain ⟨n, e, bse, _hn, hbse, horth, hpars, hexpand, hrepr⟩ :=
    tangent_orthonormalBasisRS_witness (I := I) (M := M) g r s x
  set R := riemannOp (tensorCov (I := I) g r s) x with hR_def
  set Cx : ℝ :=
    ∑ i : Fin n, ∑ j : Fin n, ∑ K : Fin r → Fin n, ∑ J : Fin s → Fin n,
      riemannianFiberNormSq (I := I) (M := M) g r s x
        (R (e i) (e j) (dualTensorFrameRS (I := I) (M := M) g x r s e K J)) with hCx_def
  have hCx_nonneg : 0 ≤ Cx := by
    rw [hCx_def]
    refine Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ =>
      Finset.sum_nonneg (fun K _ => Finset.sum_nonneg (fun J _ => ?_))))
    exact riemannianFiberNormSq_nonneg (I := I) (M := M) g r s x _
  refine ⟨Cx, hCx_nonneg, ?_⟩
  intro v w T
  have hvv_nonneg : 0 ≤ g.inner x v v := by
    rw [← hpars v]; exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hww_nonneg : 0 ≤ g.inner x w w := by
    rw [← hpars w]; exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hvw : riemannianFiberNormSq (I := I) (M := M) g r s x (R v w T) ≤
      g.inner x v v * g.inner x w w *
        ∑ i : Fin n, ∑ j : Fin n,
          riemannianFiberNormSq (I := I) (M := M) g r s x (R (e i) (e j) T) := by
    rw [hrepr (R v w T)]
    have hterm : ∀ K : Fin r → Fin n, ∀ J : Fin s → Fin n,
        fiberNormSqSummand (I := I) (M := M) g x r s (R v w T) n e K J ≤
          g.inner x v v * g.inner x w w *
            ∑ i : Fin n, ∑ j : Fin n,
              fiberNormSqSummand (I := I) (M := M) g x r s (R (e i) (e j) T) n e K J :=
      fun K J => fiberNormSqSummand_riemannOp_tensorCovRS_vw_le
        (I := I) (M := M) g x r s e hpars hexpand v w T K J
    calc
      (∑ K : Fin r → Fin n, ∑ J : Fin s → Fin n,
          fiberNormSqSummand (I := I) (M := M) g x r s (R v w T) n e K J)
          ≤ ∑ K : Fin r → Fin n, ∑ J : Fin s → Fin n,
              g.inner x v v * g.inner x w w *
                ∑ i : Fin n, ∑ j : Fin n,
                  fiberNormSqSummand (I := I) (M := M) g x r s (R (e i) (e j) T) n e K J := by
            exact Finset.sum_le_sum (fun K _ => Finset.sum_le_sum (fun J _ => hterm K J))
      _ = g.inner x v v * g.inner x w w *
            ∑ K : Fin r → Fin n, ∑ J : Fin s → Fin n,
              ∑ i : Fin n, ∑ j : Fin n,
                fiberNormSqSummand (I := I) (M := M) g x r s (R (e i) (e j) T) n e K J := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun K _ => ?_)
            rw [Finset.mul_sum]
      _ = g.inner x v v * g.inner x w w *
            ∑ i : Fin n, ∑ j : Fin n,
              riemannianFiberNormSq (I := I) (M := M) g r s x (R (e i) (e j) T) := by
            congr 1
            set F : (Fin r → Fin n) → (Fin s → Fin n) → Fin n → Fin n → ℝ :=
              fun K J i j =>
                fiberNormSqSummand (I := I) (M := M) g x r s (R (e i) (e j) T) n e K J
              with hF_def
            have hRHS_eq : (∑ i : Fin n, ∑ j : Fin n,
                  riemannianFiberNormSq (I := I) (M := M) g r s x (R (e i) (e j) T)) =
                ∑ i : Fin n, ∑ j : Fin n, ∑ K : Fin r → Fin n, ∑ J : Fin s → Fin n,
                  F K J i j := by
              refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
              rw [hF_def]
              exact hrepr (R (e i) (e j) T)
            rw [hRHS_eq]
            have hLHS : (∑ K : Fin r → Fin n, ∑ J : Fin s → Fin n,
                  ∑ i : Fin n, ∑ j : Fin n, F K J i j) =
                ∑ q : (Fin r → Fin n) × (Fin s → Fin n),
                  ∑ p : Fin n × Fin n, F q.1 q.2 p.1 p.2 := by
              calc
                (∑ K : Fin r → Fin n, ∑ J : Fin s → Fin n,
                    ∑ i : Fin n, ∑ j : Fin n, F K J i j)
                    = ∑ K : Fin r → Fin n, ∑ J : Fin s → Fin n,
                        ∑ p : Fin n × Fin n, F K J p.1 p.2 := by
                      refine Finset.sum_congr rfl (fun K _ =>
                        Finset.sum_congr rfl (fun J _ => ?_))
                      exact (Fintype.sum_prod_type' (f := fun i j => F K J i j)).symm
                _ = ∑ q : (Fin r → Fin n) × (Fin s → Fin n),
                        ∑ p : Fin n × Fin n, F q.1 q.2 p.1 p.2 :=
                      (Fintype.sum_prod_type' (f := fun K J =>
                        ∑ p : Fin n × Fin n, F K J p.1 p.2)).symm
            have hRHS : (∑ i : Fin n, ∑ j : Fin n,
                  ∑ K : Fin r → Fin n, ∑ J : Fin s → Fin n, F K J i j) =
                ∑ p : Fin n × Fin n,
                  ∑ q : (Fin r → Fin n) × (Fin s → Fin n), F q.1 q.2 p.1 p.2 := by
              calc
                (∑ i : Fin n, ∑ j : Fin n,
                    ∑ K : Fin r → Fin n, ∑ J : Fin s → Fin n, F K J i j)
                    = ∑ i : Fin n, ∑ j : Fin n,
                        ∑ q : (Fin r → Fin n) × (Fin s → Fin n), F q.1 q.2 i j := by
                      refine Finset.sum_congr rfl (fun i _ =>
                        Finset.sum_congr rfl (fun j _ => ?_))
                      exact (Fintype.sum_prod_type' (f := fun K J => F K J i j)).symm
                _ = ∑ p : Fin n × Fin n,
                        ∑ q : (Fin r → Fin n) × (Fin s → Fin n), F q.1 q.2 p.1 p.2 :=
                      (Fintype.sum_prod_type' (f := fun i j =>
                        ∑ q : (Fin r → Fin n) × (Fin s → Fin n), F q.1 q.2 i j)).symm
            rw [hLHS, hRHS]
            exact Finset.sum_comm
  have hCxT : (∑ i : Fin n, ∑ j : Fin n,
        riemannianFiberNormSq (I := I) (M := M) g r s x (R (e i) (e j) T)) ≤
      Cx * riemannianFiberNormSq (I := I) (M := M) g r s x T := by
    rw [hCx_def]
    exact sum_riemannianFiberNormSq_riemannOpRS_le_Cx
      (I := I) (M := M) g x r s e bse hbse horth hrepr T
  calc
    riemannianFiberNormSq (I := I) (M := M) g r s x (R v w T)
        ≤ g.inner x v v * g.inner x w w *
            ∑ i : Fin n, ∑ j : Fin n,
              riemannianFiberNormSq (I := I) (M := M) g r s x (R (e i) (e j) T) := hvw
    _ ≤ g.inner x v v * g.inner x w w *
            (Cx * riemannianFiberNormSq (I := I) (M := M) g r s x T) := by
          refine mul_le_mul_of_nonneg_left hCxT ?_
          exact mul_nonneg hvv_nonneg hww_nonneg
    _ = Cx * g.inner x v v * g.inner x w w *
            riemannianFiberNormSq (I := I) (M := M) g r s x T := by ring

omit [NeZero (Module.finrank ℝ E)] in
theorem exists_Cx_riemannianFiberNormSq_riemannOp_tensorCovS_le
    (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M) :
    ∃ Cx : ℝ, 0 ≤ Cx ∧
      ∀ (v w : TangentSpace I x) (T : TensorRSSpace 0 s I x),
        riemannianFiberNormSq (I := I) (M := M) g 0 s x
            (riemannOp (tensorCov (I := I) g 0 s) x v w T) ≤
          Cx * g.inner x v v * g.inner x w w *
            riemannianFiberNormSq (I := I) (M := M) g 0 s x T :=
  exists_Cx_riemannianFiberNormSq_riemannOp_tensorCovS_le_rs
    (I := I) (M := M) g 0 s x

omit [NeZero (Module.finrank ℝ E)] in
theorem riemannianFiberNormSq_riemannOp_tensorCovS_vw_factor_le
    (g : SmoothRiemannianMetric I M) (t : ℕ) (x : M)
    (v w : TangentSpace I x) (T : TensorRSSpace 0 t I x) :
    ∃ (n : ℕ) (e : Fin n → TangentSpace I x),
      (∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0) ∧
      (∀ S : TensorRSSpace 0 t I x,
        riemannianFiberNormSq (I := I) (M := M) g 0 t x S =
          ∑ K : Fin 0 → Fin n, ∑ J : Fin t → Fin n,
            fiberNormSqSummand (I := I) (M := M) g x 0 t S n e K J) ∧
      riemannianFiberNormSq (I := I) (M := M) g 0 t x
          (riemannOp (tensorCov (I := I) g 0 t) x v w T) ≤
        g.inner x v v * g.inner x w w *
          ∑ i : Fin n, ∑ j : Fin n,
            riemannianFiberNormSq (I := I) (M := M) g 0 t x
              (riemannOp (tensorCov (I := I) g 0 t) x (e i) (e j) T) := by
  classical
  obtain ⟨n, e, _bse, _hn, _hbse, horth, hpars, hexpand, hrepr⟩ :=
    tangent_orthonormalBasisRS_witness (I := I) (M := M) g 0 t x
  refine ⟨n, e, horth, hrepr, ?_⟩
  set R := riemannOp (tensorCov (I := I) g 0 t) x with hR_def
  rw [hrepr (R v w T)]
  have hterm : ∀ K : Fin 0 → Fin n, ∀ J : Fin t → Fin n,
      fiberNormSqSummand (I := I) (M := M) g x 0 t (R v w T) n e K J ≤
        g.inner x v v * g.inner x w w *
          ∑ i : Fin n, ∑ j : Fin n,
            fiberNormSqSummand (I := I) (M := M) g x 0 t (R (e i) (e j) T) n e K J :=
    fun K J => fiberNormSqSummand_riemannOp_tensorCovRS_vw_le
      (I := I) (M := M) g x 0 t e hpars hexpand v w T K J
  calc
    (∑ K : Fin 0 → Fin n, ∑ J : Fin t → Fin n,
        fiberNormSqSummand (I := I) (M := M) g x 0 t (R v w T) n e K J)
        ≤ ∑ K : Fin 0 → Fin n, ∑ J : Fin t → Fin n,
            g.inner x v v * g.inner x w w *
              ∑ i : Fin n, ∑ j : Fin n,
                fiberNormSqSummand (I := I) (M := M) g x 0 t (R (e i) (e j) T) n e K J := by
          exact Finset.sum_le_sum (fun K _ => Finset.sum_le_sum (fun J _ => hterm K J))
    _ = g.inner x v v * g.inner x w w *
          ∑ K : Fin 0 → Fin n, ∑ J : Fin t → Fin n,
            ∑ i : Fin n, ∑ j : Fin n,
              fiberNormSqSummand (I := I) (M := M) g x 0 t (R (e i) (e j) T) n e K J := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun K _ => ?_)
          rw [Finset.mul_sum]
    _ = g.inner x v v * g.inner x w w *
          ∑ i : Fin n, ∑ j : Fin n,
            riemannianFiberNormSq (I := I) (M := M) g 0 t x (R (e i) (e j) T) := by
          congr 1
          set F : (Fin 0 → Fin n) → (Fin t → Fin n) → Fin n → Fin n → ℝ :=
            fun K J i j =>
              fiberNormSqSummand (I := I) (M := M) g x 0 t (R (e i) (e j) T) n e K J
            with hF_def
          have hRHS_eq : (∑ i : Fin n, ∑ j : Fin n,
                riemannianFiberNormSq (I := I) (M := M) g 0 t x (R (e i) (e j) T)) =
              ∑ i : Fin n, ∑ j : Fin n, ∑ K : Fin 0 → Fin n, ∑ J : Fin t → Fin n,
                F K J i j := by
            refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
            rw [hF_def]
            exact hrepr (R (e i) (e j) T)
          rw [hRHS_eq]
          have hLHS : (∑ K : Fin 0 → Fin n, ∑ J : Fin t → Fin n,
                ∑ i : Fin n, ∑ j : Fin n, F K J i j) =
              ∑ q : (Fin 0 → Fin n) × (Fin t → Fin n),
                ∑ p : Fin n × Fin n, F q.1 q.2 p.1 p.2 := by
            calc
              (∑ K : Fin 0 → Fin n, ∑ J : Fin t → Fin n,
                  ∑ i : Fin n, ∑ j : Fin n, F K J i j)
                  = ∑ K : Fin 0 → Fin n, ∑ J : Fin t → Fin n,
                      ∑ p : Fin n × Fin n, F K J p.1 p.2 := by
                    refine Finset.sum_congr rfl (fun K _ =>
                      Finset.sum_congr rfl (fun J _ => ?_))
                    exact (Fintype.sum_prod_type' (f := fun i j => F K J i j)).symm
              _ = ∑ q : (Fin 0 → Fin n) × (Fin t → Fin n),
                      ∑ p : Fin n × Fin n, F q.1 q.2 p.1 p.2 :=
                    (Fintype.sum_prod_type' (f := fun K J =>
                      ∑ p : Fin n × Fin n, F K J p.1 p.2)).symm
          have hRHS : (∑ i : Fin n, ∑ j : Fin n,
                ∑ K : Fin 0 → Fin n, ∑ J : Fin t → Fin n, F K J i j) =
              ∑ p : Fin n × Fin n,
                ∑ q : (Fin 0 → Fin n) × (Fin t → Fin n), F q.1 q.2 p.1 p.2 := by
            calc
              (∑ i : Fin n, ∑ j : Fin n,
                  ∑ K : Fin 0 → Fin n, ∑ J : Fin t → Fin n, F K J i j)
                  = ∑ i : Fin n, ∑ j : Fin n,
                      ∑ q : (Fin 0 → Fin n) × (Fin t → Fin n), F q.1 q.2 i j := by
                    refine Finset.sum_congr rfl (fun i _ =>
                      Finset.sum_congr rfl (fun j _ => ?_))
                    exact (Fintype.sum_prod_type' (f := fun K J => F K J i j)).symm
              _ = ∑ p : Fin n × Fin n,
                      ∑ q : (Fin 0 → Fin n) × (Fin t → Fin n), F q.1 q.2 p.1 p.2 :=
                    (Fintype.sum_prod_type' (f := fun i j =>
                      ∑ q : (Fin 0 → Fin n) × (Fin t → Fin n), F q.1 q.2 i j)).symm
          rw [hLHS, hRHS]
          exact Finset.sum_comm

end Elliptic
end Analysis
end DifferentialGeometry

end
