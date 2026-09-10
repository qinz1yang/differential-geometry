import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Curvature.JetPolynomials
import DifferentialGeometry.Geometry.Metric.Variation.TimeDerivative
import Mathlib.Topology.Instances.Matrix

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Manifold Filter DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance timeCoefficientC1 : IsManifold I 1 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)

theorem basisInvMetric_eq_matrix_inv {n : ℕ} {x : M}
    (g : SmoothRiemannianMetric I M)
    (basis : Module.Basis (Fin n) ℝ (TangentSpace I x)) :
    basisInvMetric (I := I) g x basis =
      (Matrix.of (fun i j => g.inner x (basis i) (basis j)))⁻¹ := by
  symm
  apply Matrix.inv_eq_left_inv
  ext i j
  exact (basisInvMetric_isInverse (I := I) g x basis i j).1

theorem basisInvMetric_continuousWithinAt {n : ℕ} {x : M}
    (g : ℝ → SmoothRiemannianMetric I M)
    (basis : Module.Basis (Fin n) ℝ (TangentSpace I x))
    {J : Set ℝ} {t : ℝ}
    (hg : ∀ i j, ContinuousWithinAt (fun s => (g s).inner x (basis i) (basis j)) J t)
    (i j : Fin n) :
    ContinuousWithinAt (fun s => basisInvMetric (I := I) (g s) x basis i j) J t := by
  let G : ℝ → Matrix (Fin n) (Fin n) ℝ :=
    fun s => Matrix.of (fun i j => (g s).inner x (basis i) (basis j))
  have hG : ContinuousWithinAt G J t :=
    continuousWithinAt_pi.mpr fun i => continuousWithinAt_pi.mpr (hg i)
  have hprod : Matrix.of (basisInvMetric (I := I) (g t) x basis) * G t = 1 := by
    ext i j
    exact (basisInvMetric_isInverse (I := I) (g t) x basis i j).1
  have hdet : (G t).det ≠ 0 := Matrix.det_ne_zero_of_left_inverse hprod
  have hinverse : ContinuousAt Ring.inverse (G t).det := by
    simpa only [Ring.inverse_eq_inv'] using (continuousAt_inv₀ hdet)
  have hInv := (continuousAt_matrix_inv (G t) hinverse).comp_continuousWithinAt hG
  change ContinuousWithinAt (fun s => (G s)⁻¹) J t at hInv
  have hentry := continuousWithinAt_pi.mp (continuousWithinAt_pi.mp hInv i) j
  simpa only [basisInvMetric_eq_matrix_inv, G] using hentry

theorem basis_repr_eq_sum_inverse_inner {n : ℕ} {x : M}
    (g : SmoothRiemannianMetric I M)
    (basis : Module.Basis (Fin n) ℝ (TangentSpace I x))
    (v : TangentSpace I x) (j : Fin n) :
    basis.repr v j = ∑ k : Fin n,
      basisInvMetric (I := I) g x basis j k * g.inner x v (basis k) := by
  have hex (k : Fin n) : g.inner x v (basis k) =
      ∑ l : Fin n, basis.repr v l * g.inner x (basis l) (basis k) := by
    calc
      g.inner x v (basis k) =
          g.inner x (∑ l : Fin n, basis.repr v l • basis l) (basis k) :=
        congrArg (fun w => g.inner x w (basis k)) (basis.sum_repr v).symm
      _ = _ := by
        simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul]
  symm
  calc
    (∑ k : Fin n, basisInvMetric (I := I) g x basis j k * g.inner x v (basis k)) =
        ∑ l : Fin n, basis.repr v l *
          (∑ k : Fin n, basisInvMetric (I := I) g x basis j k *
            g.inner x (basis k) (basis l)) := by
      simp_rw [hex, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun l _ => ?_
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [g.symm x (basis l) (basis k)]
      ring
    _ = ∑ l : Fin n, basis.repr v l * (if j = l then 1 else 0) := by
      exact Finset.sum_congr rfl fun l _ =>
        congrArg (fun c => basis.repr v l * c)
          (basisInvMetric_isInverse (I := I) g x basis j l).1
    _ = basis.repr v j := by simp

section Ricci

variable [T2Space M] [BoundarylessManifold I M]

theorem ricciSharp_basis_continuousWithinAt {n : ℕ} {x : M}
    (g : ℝ → SmoothRiemannianMetric I M)
    (basis : Module.Basis (Fin n) ℝ (TangentSpace I x))
    {J : Set ℝ} {t : ℝ}
    (hg : ∀ i j, ContinuousWithinAt (fun s => (g s).inner x (basis i) (basis j)) J t)
    (hRic : ∀ i j, ContinuousWithinAt
      (fun s => ricciTensor (I := I) (g s) x (basis i) (basis j)) J t)
    (i j : Fin n) :
    ContinuousWithinAt (fun s => basis.repr (ricciSharp (g s) x (basis i)) j) J t := by
  have heq : (fun s => basis.repr (ricciSharp (g s) x (basis i)) j) =
      (fun s => ∑ k : Fin n, basisInvMetric (I := I) (g s) x basis j k *
        ricciTensor (I := I) (g s) x (basis i) (basis k)) := by
    funext s
    simpa only [inner_ricciSharp] using
      (basis_repr_eq_sum_inverse_inner (g s) basis (ricciSharp (g s) x (basis i)) j)
  rw [heq]
  exact tendsto_finsetSum Finset.univ fun k _ =>
    (basisInvMetric_continuousWithinAt g basis hg j k).mul (hRic i k)

theorem metricTimeCorrection_continuousWithinAt {n r : ℕ} {x : M}
    (g : ℝ → SmoothRiemannianMetric I M)
    (basis : Module.Basis (Fin n) ℝ (TangentSpace I x))
    {A : ℝ → Tensor0SSpace r I x} {J : Set ℝ} {t : ℝ}
    (hA : ContinuousWithinAt A J t)
    (hg : ∀ i j, ContinuousWithinAt (fun s => (g s).inner x (basis i) (basis j)) J t)
    (hRic : ∀ i j, ContinuousWithinAt
      (fun s => ricciTensor (I := I) (g s) x (basis i) (basis j)) J t) :
    ContinuousWithinAt
      (fun s => covariantEndomorphismAction0S (A s) (ricciSharp (g s) x)) J t := by
  apply tensor0S_continuousWithinAt_of_components basis
  intro slots
  have hc (slots' : Fin r → Fin n) :
      ContinuousWithinAt (fun s => component0S (I := I) basis (A s) slots') J t :=
    (tensor0SEvalCLM (I := I) (fun k => basis (slots' k))).continuous.continuousAt.comp_continuousWithinAt hA
  have heq : (fun s => component0S (I := I) basis
        (covariantEndomorphismAction0S (A s) (ricciSharp (g s) x)) slots) =
      (fun s => ∑ k : Fin r, ∑ e : Fin n,
        basis.repr (ricciSharp (g s) x (basis (slots k))) e *
          component0S (I := I) basis (A s) (Function.update slots k e)) := by
    funext s
    exact tensor0SComponent_covariantEndomorphismAction0S basis (A s) (ricciSharp (g s) x) slots
  rw [heq]
  exact tendsto_finsetSum Finset.univ fun k _ => tendsto_finsetSum Finset.univ fun e _ =>
    (ricciSharp_basis_continuousWithinAt g basis hg hRic (slots k) e).mul
      (hc (Function.update slots k e))

end Ricci

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
