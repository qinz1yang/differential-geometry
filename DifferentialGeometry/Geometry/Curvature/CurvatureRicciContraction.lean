import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.RicciTraceCarrier
import DifferentialGeometry.Geometry.Comparison.BonnetMyers.SectionalRicci

set_option autoImplicit false

noncomputable section

open Bundle
open scoped Manifold ContDiff BigOperators

namespace DifferentialGeometry.Geometry.Curvature

open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

private def curvatureRicciContractionSlots : Equiv.Perm (Fin 4) where
  toFun := ![0, 2, 3, 1]
  invFun := ![0, 3, 1, 2]
  left_inv := by decide
  right_inv := by decide

def curvatureRicciContractionAt
    (g : SmoothRiemannianMetric I M) (x : M) : Tensor0SSpace 2 I x :=
  metricTraceFirstTwo0STensor (I := I) g
    (ricSlotOpFib (I := I) (M := M) g 3 x
      ((metricRm04At (I := I) (M := M) g x).domDomCongr
        curvatureRicciContractionSlots))

omit [SigmaCompactSpace M] in
theorem curvatureRicciContractionAt_apply_eq_sum_orthonormalBasis
    (g : SmoothRiemannianMetric I M) (x : M)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (horth : ∀ i j : Idx,
      g.inner x (basis i) (basis j) = if i = j then 1 else 0)
    (v w : TangentSpace I x) :
    curvatureRicciContractionAt (I := I) (M := M) g x (vec2 (I := I) v w) =
      ∑ i : Idx,
        metricRm04StdAt (I := I) (M := M) g x
          (ricEndoRaisedFib (I := I) g x (basis i)) v w (basis i) := by
  classical
  have hinv : MetricInverseInBasisGen (I := I) g x basis
      (identityInvMetric (Idx := Idx)) :=
    metricInverseInBasis_identity_of_orthonormal (I := I) g basis horth
  rw [curvatureRicciContractionAt, metricTraceFirstTwo0STensor_apply,
    metricTraceFirstTwo0SAt_eq_sum_basis (I := I) g basis
      (identityInvMetric (Idx := Idx)) hinv]
  unfold metricTrace0S2InBasis
  rw [show (∑ i : Idx, ∑ j : Idx,
      identityInvMetric i j *
        ricSlotOpFib (I := I) (M := M) g 3 x
          ((metricRm04At (I := I) (M := M) g x).domDomCongr
            curvatureRicciContractionSlots)
          (metricTraceInput (I := I) (basis i) (basis j) (vec2 (I := I) v w))) =
      ∑ i : Idx,
        ricSlotOpFib (I := I) (M := M) g 3 x
          ((metricRm04At (I := I) (M := M) g x).domDomCongr
            curvatureRicciContractionSlots)
          (metricTraceInput (I := I) (basis i) (basis i) (vec2 (I := I) v w)) by
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      have hij : i ≠ j := Ne.symm hji
      simp [identityInvMetric, diagonalInvMetric, hij]
    · simp]
  apply Finset.sum_congr rfl
  intro i _
  have hinput :
      metricTraceInput (I := I) (basis i) (basis i) (vec2 (I := I) v w) =
        Fin.cons (basis i) (Fin.cons (basis i) (vec2 (I := I) v w)) := by
    funext a
    fin_cases a <;> rfl
  rw [hinput]
  change Tensor0SSpace.eval
      (ricSlotOpFib (I := I) (M := M) g 3 x
        ((metricRm04At (I := I) (M := M) g x).domDomCongr
          curvatureRicciContractionSlots))
      (Fin.cons (basis i) (Fin.cons (basis i) (vec2 (I := I) v w))) = _
  rw [ricSlotOpFib_apply_eval (I := I) (M := M)]
  rfl

omit [SigmaCompactSpace M] in
theorem ricciTensor_nonneg_of_sectionalNonnegative
    (g : SmoothRiemannianMetric I M) (x : M)
    (hsec : metricRm04At (I := I) (M := M) g x ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M))
    (v : TangentSpace I x) :
    0 ≤ ricciTensor (I := I) g x v v :=
  Riemannian.BonnetMyers.ricci_nonneg_of_sec (I := I) (M := M) g x hsec v

omit [SigmaCompactSpace M] in
theorem curvatureRicciContractionAt_nonneg_of_sectionalNonnegative
    (g : SmoothRiemannianMetric I M) (x : M)
    (hsec : metricRm04At (I := I) (M := M) g x ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M))
    (v : TangentSpace I x) :
    0 ≤ curvatureRicciContractionAt (I := I) (M := M) g x
      (vec2 (I := I) v v) := by
  classical
  let D := (tangentMetricDataGen (I := I) g x).metric
  let : InnerProductSpace.Core Real (TangentSpace I x) := D.toCore
  let : NormedAddCommGroup (TangentSpace I x) :=
    @InnerProductSpace.Core.toNormedAddCommGroup Real (TangentSpace I x) _ _ _
      D.toCore
  let : InnerProductSpace Real (TangentSpace I x) :=
    @InnerProductSpace.ofCore Real (TangentSpace I x) _ _ _ D.toCore.toCore
  let T : TangentSpace I x →ₗ[Real] TangentSpace I x :=
    (ricEndoRaisedFib (I := I) g x).toLinearMap
  have hT : T.IsSymmetric := by
    intro X Y
    rw [MetricFiberData.toCore_inner D (T X) Y,
      MetricFiberData.toCore_inner D X (T Y)]
    change g.inner x (ricEndoRaisedFib (I := I) g x X) Y =
      g.inner x X (ricEndoRaisedFib (I := I) g x Y)
    rw [inner_ricEndoRaisedFib (I := I) (M := M),
      g.symm x X, inner_ricEndoRaisedFib (I := I) (M := M),
      ricciTensor_symm (I := I) g x X Y]
  let n := Module.finrank Real (TangentSpace I x)
  have hn : Module.finrank Real (TangentSpace I x) = n := rfl
  let ob := hT.eigenvectorBasis hn
  let basis : Module.Basis (Fin n) Real (TangentSpace I x) := ob.toBasis
  let rho : Fin n → Real := fun i => hT.eigenvalues hn i
  have horth : ∀ i j : Fin n,
      g.inner x (basis i) (basis j) = if i = j then 1 else 0 := by
    intro i j
    have hinner : Inner.inner Real (ob i) (ob j) = D.inner (ob i) (ob j) :=
      MetricFiberData.toCore_inner D (ob i) (ob j)
    change D.inner (ob i) (ob j) = if i = j then 1 else 0
    exact hinner.symm.trans (ob.inner_eq_ite i j)
  have heigen (i : Fin n) :
      ricEndoRaisedFib (I := I) g x (basis i) = rho i • basis i := by
    change T (ob i) = rho i • ob i
    exact hT.apply_eigenvectorBasis hn i
  have hrho (i : Fin n) : 0 ≤ rho i := by
    have hric := ricciTensor_nonneg_of_sectionalNonnegative
      (I := I) (M := M) g x hsec (basis i)
    rw [← inner_ricEndoRaisedFib (I := I) (M := M) g x,
      heigen i] at hric
    have hii : g.inner x (basis i) (basis i) = 1 := by
      simpa using horth i i
    have hscale :
        g.inner x (rho i • basis i) (basis i) =
          rho i * g.inner x (basis i) (basis i) := by
      rw [map_smul]
      rfl
    rw [hscale] at hric
    rw [hii] at hric
    simpa [rho] using hric
  rw [curvatureRicciContractionAt_apply_eq_sum_orthonormalBasis
    (I := I) (M := M) g x basis horth v v]
  refine Finset.sum_nonneg fun i _ => ?_
  rw [heigen i]
  have hcurv :=
    (metricRm04At_mem_tensor04SectionalNonnegativeCone_iff
      (I := I) (M := M) g x).mp hsec (basis i) v
  change 0 ≤ metricRm04At (I := I) (M := M) g x
    (vec4 (I := I) (rho i • basis i) v v (basis i))
  have hsmul := (metricRm04At (I := I) (M := M) g x).map_update_smul
    (vec4 (I := I) (basis i) v v (basis i)) (0 : Fin 4) (rho i) (basis i)
  have hupdate : Function.update
      (vec4 (I := I) (basis i) v v (basis i)) (0 : Fin 4) (rho i • basis i) =
      vec4 (I := I) (rho i • basis i) v v (basis i) := by
    funext a
    fin_cases a <;> simp [vec4, Function.update]
  rw [hupdate] at hsmul
  rw [hsmul]
  exact mul_nonneg (hrho i) hcurv

end DifferentialGeometry.Geometry.Curvature
