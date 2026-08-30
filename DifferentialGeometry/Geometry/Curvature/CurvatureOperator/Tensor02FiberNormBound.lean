import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqRiemannOpVWFactorBound
import DifferentialGeometry.Geometry.Metric.TensorInner.FiberNorm.OrthonormalFrame.Tensor02
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
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

omit [NeZero (Module.finrank ℝ E)] in
lemma sum_riemannianFiberNormSq_riemannOp_le_Cx
    (g : SmoothRiemannianMetric I M) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (bse : Module.Basis (Fin n) ℝ (TangentSpace I x))
    (hbse : ∀ i : Fin n, bse i = e i)
    (horth : ∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0)
    (hrepr : ∀ S : TensorRSSpace 0 2 I x,
      riemannianFiberNormSq (I := I) (M := M) g 0 2 x S =
        ∑ K : Fin 0 → Fin n, ∑ J : Fin 2 → Fin n,
          fiberNormSqSummand (I := I) (M := M) g x 0 2 S n e K J)
    (T : TensorRSSpace 0 2 I x) :
    (∑ i : Fin n, ∑ j : Fin n,
        riemannianFiberNormSq (I := I) (M := M) g 0 2 x
          (riemannOp (tensorCov (I := I) g 0 2) x (e i) (e j) T)) ≤
      (∑ i : Fin n, ∑ j : Fin n, ∑ a : Fin n, ∑ b : Fin n,
          riemannianFiberNormSq (I := I) (M := M) g 0 2 x
            (riemannOp (tensorCov (I := I) g 0 2) x (e i) (e j)
              (dualTensorFrame (I := I) (M := M) g x e a b))) *
        riemannianFiberNormSq (I := I) (M := M) g 0 2 x T := by
  classical
  let K₀ : Fin 0 → Fin n := fun k => k.elim0
  set R := riemannOp (tensorCov (I := I) g 0 2) x with hR_def
  have hParseval := riemannianFiberNormSq_eq_sum_component_sq
    (I := I) (M := M) g x e hrepr T K₀
  have hTexp := tensor_dualFrame_expansion (I := I) (M := M) g x e bse hbse horth T K₀
  set cT : Fin n × Fin n → ℝ :=
    fun p => fiberNormSqComponent (I := I) (M := M) g x 0 2 T n e K₀ (![p.1, p.2]) with hcT
  have hpair : ∀ i j : Fin n,
      riemannianFiberNormSq (I := I) (M := M) g 0 2 x (R (e i) (e j) T) ≤
        (∑ a : Fin n, ∑ b : Fin n,
            riemannianFiberNormSq (I := I) (M := M) g 0 2 x
              (R (e i) (e j) (dualTensorFrame (I := I) (M := M) g x e a b))) *
          riemannianFiberNormSq (I := I) (M := M) g 0 2 x T := by
    intro i j
    have hRT : R (e i) (e j) T =
        ∑ a : Fin n, ∑ b : Fin n,
          cT (a, b) • R (e i) (e j) (dualTensorFrame (I := I) (M := M) g x e a b) := by
      conv_lhs => rw [hTexp]
      rw [map_sum]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [map_sum]
      refine Finset.sum_congr rfl (fun b _ => ?_)
      rw [ContinuousLinearMap.map_smul]
    rw [hRT]
    rw [hrepr (∑ a : Fin n, ∑ b : Fin n,
      cT (a, b) • R (e i) (e j) (dualTensorFrame (I := I) (M := M) g x e a b))]
    have hterm : ∀ (Kx : Fin 0 → Fin n) (Jx : Fin 2 → Fin n),
        fiberNormSqSummand (I := I) (M := M) g x 0 2
            (∑ a : Fin n, ∑ b : Fin n,
              cT (a, b) • R (e i) (e j) (dualTensorFrame (I := I) (M := M) g x e a b))
            n e Kx Jx ≤
          (∑ p : Fin n × Fin n, cT p ^ 2) *
            ∑ p : Fin n × Fin n,
              fiberNormSqSummand (I := I) (M := M) g x 0 2
                (R (e i) (e j) (dualTensorFrame (I := I) (M := M) g x e p.1 p.2)) n e Kx Jx := by
      intro Kx Jx
      rw [fiberNormSqSummand_eq_component_sq]
      have hcomp :
          fiberNormSqComponent (I := I) (M := M) g x 0 2
              (∑ a : Fin n, ∑ b : Fin n,
                cT (a, b) • R (e i) (e j) (dualTensorFrame (I := I) (M := M) g x e a b))
              n e Kx Jx =
            ∑ p : Fin n × Fin n,
              cT p *
                fiberNormSqComponent (I := I) (M := M) g x 0 2
                  (R (e i) (e j) (dualTensorFrame (I := I) (M := M) g x e p.1 p.2)) n e Kx Jx := by
        rw [show (∑ a : Fin n, ∑ b : Fin n,
              cT (a, b) • R (e i) (e j) (dualTensorFrame (I := I) (M := M) g x e a b)) =
            ∑ p : Fin n × Fin n,
              cT p • R (e i) (e j) (dualTensorFrame (I := I) (M := M) g x e p.1 p.2) from
          (Fintype.sum_prod_type'
            (f := fun a b =>
              cT (a, b) • R (e i) (e j)
                (dualTensorFrame (I := I) (M := M) g x e a b))).symm]
        rw [fiberNormSqComponent_sum]
        refine Finset.sum_congr rfl (fun p _ => ?_)
        rw [fiberNormSqComponent_smul]
      rw [hcomp]
      exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ cT
        (fun p => fiberNormSqComponent (I := I) (M := M) g x 0 2
          (R (e i) (e j) (dualTensorFrame (I := I) (M := M) g x e p.1 p.2)) n e Kx Jx)
    calc
      (∑ Kx : Fin 0 → Fin n, ∑ Jx : Fin 2 → Fin n,
          fiberNormSqSummand (I := I) (M := M) g x 0 2
            (∑ a : Fin n, ∑ b : Fin n,
              cT (a, b) • R (e i) (e j) (dualTensorFrame (I := I) (M := M) g x e a b))
            n e Kx Jx)
          ≤ ∑ Kx : Fin 0 → Fin n, ∑ Jx : Fin 2 → Fin n,
              (∑ p : Fin n × Fin n, cT p ^ 2) *
                ∑ p : Fin n × Fin n,
                  fiberNormSqSummand (I := I) (M := M) g x 0 2
                    (R (e i) (e j) (dualTensorFrame (I := I) (M := M) g x e p.1 p.2))
                    n e Kx Jx := by
            refine Finset.sum_le_sum (fun Kx _ => Finset.sum_le_sum (fun Jx _ => hterm Kx Jx))
      _ = (∑ p : Fin n × Fin n, cT p ^ 2) *
            ∑ Kx : Fin 0 → Fin n, ∑ Jx : Fin 2 → Fin n,
              ∑ p : Fin n × Fin n,
                fiberNormSqSummand (I := I) (M := M) g x 0 2
                  (R (e i) (e j) (dualTensorFrame (I := I) (M := M) g x e p.1 p.2))
                  n e Kx Jx := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun Kx _ => ?_)
            rw [Finset.mul_sum]
      _ = (∑ p : Fin n × Fin n, cT p ^ 2) *
            ∑ p : Fin n × Fin n,
              riemannianFiberNormSq (I := I) (M := M) g 0 2 x
                (R (e i) (e j) (dualTensorFrame (I := I) (M := M) g x e p.1 p.2)) := by
            congr 1
            rw [show (∑ p : Fin n × Fin n,
                  riemannianFiberNormSq (I := I) (M := M) g 0 2 x
                    (R (e i) (e j) (dualTensorFrame (I := I) (M := M) g x e p.1 p.2))) =
                ∑ p : Fin n × Fin n, ∑ Kx : Fin 0 → Fin n, ∑ Jx : Fin 2 → Fin n,
                  fiberNormSqSummand (I := I) (M := M) g x 0 2
                    (R (e i) (e j) (dualTensorFrame (I := I) (M := M) g x e p.1 p.2))
                    n e Kx Jx from by
              refine Finset.sum_congr rfl (fun p _ => ?_)
              rw [hrepr (R (e i) (e j) (dualTensorFrame (I := I) (M := M) g x e p.1 p.2))]]
            rw [show (∑ Kx : Fin 0 → Fin n, ∑ Jx : Fin 2 → Fin n, ∑ p : Fin n × Fin n,
                  fiberNormSqSummand (I := I) (M := M) g x 0 2
                    (R (e i) (e j) (dualTensorFrame (I := I) (M := M) g x e p.1 p.2))
                    n e Kx Jx) =
                ∑ Kx : Fin 0 → Fin n, ∑ p : Fin n × Fin n, ∑ Jx : Fin 2 → Fin n,
                  fiberNormSqSummand (I := I) (M := M) g x 0 2
                    (R (e i) (e j) (dualTensorFrame (I := I) (M := M) g x e p.1 p.2))
                    n e Kx Jx from by
              refine Finset.sum_congr rfl (fun Kx _ => ?_)
              rw [Finset.sum_comm]]
            rw [Finset.sum_comm]
      _ ≤ (∑ a : Fin n, ∑ b : Fin n,
              riemannianFiberNormSq (I := I) (M := M) g 0 2 x
                (R (e i) (e j) (dualTensorFrame (I := I) (M := M) g x e a b))) *
            riemannianFiberNormSq (I := I) (M := M) g 0 2 x T := by
            apply le_of_eq
            rw [show (∑ p : Fin n × Fin n, cT p ^ 2) =
                riemannianFiberNormSq (I := I) (M := M) g 0 2 x T from by
              rw [hParseval, ← Fintype.sum_prod_type' (f := fun a b => cT (a, b) ^ 2)]]
            rw [show (∑ p : Fin n × Fin n,
                  riemannianFiberNormSq (I := I) (M := M) g 0 2 x
                    (R (e i) (e j) (dualTensorFrame (I := I) (M := M) g x e p.1 p.2))) =
                ∑ a : Fin n, ∑ b : Fin n,
                  riemannianFiberNormSq (I := I) (M := M) g 0 2 x
                    (R (e i) (e j) (dualTensorFrame (I := I) (M := M) g x e a b)) from
              Fintype.sum_prod_type'
                (f := fun a b =>
                  riemannianFiberNormSq (I := I) (M := M) g 0 2 x
                    (R (e i) (e j) (dualTensorFrame (I := I) (M := M) g x e a b)))]
            ring
  calc
    (∑ i : Fin n, ∑ j : Fin n,
        riemannianFiberNormSq (I := I) (M := M) g 0 2 x (R (e i) (e j) T))
        ≤ ∑ i : Fin n, ∑ j : Fin n,
            (∑ a : Fin n, ∑ b : Fin n,
                riemannianFiberNormSq (I := I) (M := M) g 0 2 x
                  (R (e i) (e j) (dualTensorFrame (I := I) (M := M) g x e a b))) *
              riemannianFiberNormSq (I := I) (M := M) g 0 2 x T := by
          refine Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hpair i j))
    _ = (∑ i : Fin n, ∑ j : Fin n, ∑ a : Fin n, ∑ b : Fin n,
            riemannianFiberNormSq (I := I) (M := M) g 0 2 x
              (R (e i) (e j) (dualTensorFrame (I := I) (M := M) g x e a b))) *
          riemannianFiberNormSq (I := I) (M := M) g 0 2 x T := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [Finset.sum_mul]

omit [NeZero (Module.finrank ℝ E)] in
theorem exists_Cx_riemannianFiberNormSq_riemannOp_tensorCov_le
    (g : SmoothRiemannianMetric I M) (x : M) :
    ∃ Cx : ℝ, 0 ≤ Cx ∧
      ∀ (v w : TangentSpace I x) (T : TensorRSSpace 0 2 I x),
        riemannianFiberNormSq (I := I) (M := M) g 0 2 x
            (riemannOp (tensorCov (I := I) g 0 2) x v w T) ≤
          Cx * g.inner x v v * g.inner x w w *
            riemannianFiberNormSq (I := I) (M := M) g 0 2 x T := by
  classical
  obtain ⟨n, e, bse, _hn, hbse, horth, hpars, hexpand, hrepr⟩ :=
    tangent_orthonormalBasis_witness (I := I) (M := M) g x
  set R := riemannOp (tensorCov (I := I) g 0 2) x with hR_def
  set Cx : ℝ :=
    ∑ i : Fin n, ∑ j : Fin n, ∑ a : Fin n, ∑ b : Fin n,
      riemannianFiberNormSq (I := I) (M := M) g 0 2 x
        (R (e i) (e j) (dualTensorFrame (I := I) (M := M) g x e a b)) with hCx_def
  have hCx_nonneg : 0 ≤ Cx := by
    rw [hCx_def]
    refine Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ =>
      Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun b _ => ?_))))
    exact riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 2 x _
  refine ⟨Cx, hCx_nonneg, ?_⟩
  intro v w T
  have hvv_nonneg : 0 ≤ g.inner x v v := by
    rw [← hpars v]; exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hww_nonneg : 0 ≤ g.inner x w w := by
    rw [← hpars w]; exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hvw : riemannianFiberNormSq (I := I) (M := M) g 0 2 x (R v w T) ≤
      g.inner x v v * g.inner x w w *
        ∑ i : Fin n, ∑ j : Fin n,
          riemannianFiberNormSq (I := I) (M := M) g 0 2 x (R (e i) (e j) T) := by
    rw [hrepr (R v w T)]
    have hterm : ∀ K : Fin 0 → Fin n, ∀ J : Fin 2 → Fin n,
        fiberNormSqSummand (I := I) (M := M) g x 0 2 (R v w T) n e K J ≤
          g.inner x v v * g.inner x w w *
            ∑ i : Fin n, ∑ j : Fin n,
              fiberNormSqSummand (I := I) (M := M) g x 0 2 (R (e i) (e j) T) n e K J :=
      fun K J => fiberNormSqSummand_riemannOp_tensorCov_vw_le
        (I := I) (M := M) g x e hpars hexpand v w T K J
    calc
      (∑ K : Fin 0 → Fin n, ∑ J : Fin 2 → Fin n,
          fiberNormSqSummand (I := I) (M := M) g x 0 2 (R v w T) n e K J)
          ≤ ∑ K : Fin 0 → Fin n, ∑ J : Fin 2 → Fin n,
              g.inner x v v * g.inner x w w *
                ∑ i : Fin n, ∑ j : Fin n,
                  fiberNormSqSummand (I := I) (M := M) g x 0 2 (R (e i) (e j) T) n e K J := by
            exact Finset.sum_le_sum (fun K _ => Finset.sum_le_sum (fun J _ => hterm K J))
      _ = g.inner x v v * g.inner x w w *
            ∑ K : Fin 0 → Fin n, ∑ J : Fin 2 → Fin n,
              ∑ i : Fin n, ∑ j : Fin n,
                fiberNormSqSummand (I := I) (M := M) g x 0 2 (R (e i) (e j) T) n e K J := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun K _ => ?_)
            rw [Finset.mul_sum]
      _ = g.inner x v v * g.inner x w w *
            ∑ i : Fin n, ∑ j : Fin n,
              riemannianFiberNormSq (I := I) (M := M) g 0 2 x (R (e i) (e j) T) := by
            congr 1
            rw [show (∑ i : Fin n, ∑ j : Fin n,
                  riemannianFiberNormSq (I := I) (M := M) g 0 2 x (R (e i) (e j) T)) =
                ∑ i : Fin n, ∑ j : Fin n, ∑ K : Fin 0 → Fin n, ∑ J : Fin 2 → Fin n,
                  fiberNormSqSummand (I := I) (M := M) g x 0 2 (R (e i) (e j) T) n e K J from by
              refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
              rw [hrepr (R (e i) (e j) T)]]
            set F : (Fin 0 → Fin n) → (Fin 2 → Fin n) → Fin n → Fin n → ℝ :=
              fun K J i j =>
                fiberNormSqSummand (I := I) (M := M) g x 0 2 (R (e i) (e j) T) n e K J
              with hF_def
            have hLHS : (∑ K : Fin 0 → Fin n, ∑ J : Fin 2 → Fin n,
                  ∑ i : Fin n, ∑ j : Fin n, F K J i j) =
                ∑ q : (Fin 0 → Fin n) × (Fin 2 → Fin n),
                  ∑ p : Fin n × Fin n, F q.1 q.2 p.1 p.2 := by
              calc
                (∑ K : Fin 0 → Fin n, ∑ J : Fin 2 → Fin n,
                    ∑ i : Fin n, ∑ j : Fin n, F K J i j)
                    = ∑ K : Fin 0 → Fin n, ∑ J : Fin 2 → Fin n,
                        ∑ p : Fin n × Fin n, F K J p.1 p.2 := by
                      refine Finset.sum_congr rfl (fun K _ =>
                        Finset.sum_congr rfl (fun J _ => ?_))
                      exact (Fintype.sum_prod_type' (f := fun i j => F K J i j)).symm
                _ = ∑ q : (Fin 0 → Fin n) × (Fin 2 → Fin n),
                        ∑ p : Fin n × Fin n, F q.1 q.2 p.1 p.2 :=
                      (Fintype.sum_prod_type' (f := fun K J =>
                        ∑ p : Fin n × Fin n, F K J p.1 p.2)).symm
            have hRHS : (∑ i : Fin n, ∑ j : Fin n,
                  ∑ K : Fin 0 → Fin n, ∑ J : Fin 2 → Fin n, F K J i j) =
                ∑ p : Fin n × Fin n,
                  ∑ q : (Fin 0 → Fin n) × (Fin 2 → Fin n), F q.1 q.2 p.1 p.2 := by
              calc
                (∑ i : Fin n, ∑ j : Fin n,
                    ∑ K : Fin 0 → Fin n, ∑ J : Fin 2 → Fin n, F K J i j)
                    = ∑ i : Fin n, ∑ j : Fin n,
                        ∑ q : (Fin 0 → Fin n) × (Fin 2 → Fin n), F q.1 q.2 i j := by
                      refine Finset.sum_congr rfl (fun i _ =>
                        Finset.sum_congr rfl (fun j _ => ?_))
                      exact (Fintype.sum_prod_type' (f := fun K J => F K J i j)).symm
                _ = ∑ p : Fin n × Fin n,
                        ∑ q : (Fin 0 → Fin n) × (Fin 2 → Fin n), F q.1 q.2 p.1 p.2 :=
                      (Fintype.sum_prod_type' (f := fun i j =>
                        ∑ q : (Fin 0 → Fin n) × (Fin 2 → Fin n), F q.1 q.2 i j)).symm
            rw [hLHS, hRHS]
            exact Finset.sum_comm
  have hCxT : (∑ i : Fin n, ∑ j : Fin n,
        riemannianFiberNormSq (I := I) (M := M) g 0 2 x (R (e i) (e j) T)) ≤
      Cx * riemannianFiberNormSq (I := I) (M := M) g 0 2 x T := by
    rw [hCx_def]
    exact sum_riemannianFiberNormSq_riemannOp_le_Cx
      (I := I) (M := M) g x e bse hbse horth hrepr T
  calc
    riemannianFiberNormSq (I := I) (M := M) g 0 2 x (R v w T)
        ≤ g.inner x v v * g.inner x w w *
            ∑ i : Fin n, ∑ j : Fin n,
              riemannianFiberNormSq (I := I) (M := M) g 0 2 x (R (e i) (e j) T) := hvw
    _ ≤ g.inner x v v * g.inner x w w *
            (Cx * riemannianFiberNormSq (I := I) (M := M) g 0 2 x T) := by
          refine mul_le_mul_of_nonneg_left hCxT ?_
          exact mul_nonneg hvv_nonneg hww_nonneg
    _ = Cx * g.inner x v v * g.inner x w w *
            riemannianFiberNormSq (I := I) (M := M) g 0 2 x T := by ring

end Elliptic
end Analysis
end DifferentialGeometry

end
