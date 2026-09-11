import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifference.LoweredCoefficient
import DifferentialGeometry.Tensor.Metric.TraceDerivativeBounds
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.ConnectionDifference.Curvature
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Coordinates.MetricComparison
import DifferentialGeometry.Geometry.Metric.TensorInner.Cotangent.Riemannian
import DifferentialGeometry.Bundle.Section

set_option autoImplicit false
noncomputable section
open Bundle Manifold Set DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.PDE.RicciFlow
open scoped Manifold ContDiff BigOperators
namespace DifferentialGeometry.Geometry.Curvature
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [T2Space M]

private def differenceSection (G g : SmoothRiemannianMetric I M)
    (Z Y : ContMDiffSection I E ∞ (TangentSpace I : M → Type _)) :
    ContMDiffSection I E ∞ (TangentSpace I : M → Type _) where
  toFun x := PDE.DeTurck.connectionDifference g G x (Z x) (Y x)
  contMDiff_toFun := PDE.DeTurck.connectionDifference_contMDiff g G Z.contMDiff Y.contMDiff

theorem covStep_metricLoweredConnectionDifference_apply
    (G g : SmoothRiemannianMetric I M)
    (X Y Z W : ContMDiffSection I E ∞ (TangentSpace I : M → Type _)) (x : M) :
    covStep G 3 (metricLoweredConnectionDifferenceField G g) x
        (vec4 (X x) (Z x) (Y x) (W x)) =
      G.inner x (covDerivDiff (LeviCivita G) (LeviCivita g) X Y Z x) (W x) := by
  let L := metricLoweredConnectionDifferenceField G g
  let V : Fin 3 → ContMDiffSection I E ∞ (TangentSpace I : M → Type _) := ![Z, Y, W]
  let S := differenceSection G g Z Y
  have h := covStep_eval_smooth_slots G 3 L X V x
  have he : Fin.cons (X x) (fun i => V i x) = vec4 (X x) (Z x) (Y x) (W x) := by
    funext i
    fin_cases i <;> rfl
  have hf : (fun y => L y (fun i => V i y)) = fun y => G.inner y (S y) (W y) := by
    funext y
    rfl
  rw [he, hf] at h
  have hd := IsMetricCompatible.mvfderiv_inner
    (leviCivitaConnectionOfMetric_isMetricCompatible G) (X x)
    (S.contMDiff.mdifferentiable (by decide) x) (W.contMDiff.mdifferentiable (by decide) x)
  rw [hd, Fin.sum_univ_three] at h
  change covStep G 3 L x (vec4 (X x) (Z x) (Y x) (W x)) =
    G.inner x ((LeviCivita G) S x (X x)) (W x) +
      G.inner x (S x) ((LeviCivita G) W x (X x)) -
      (G.inner x (PDE.DeTurck.connectionDifference g G x ((LeviCivita G) Z x (X x)) (Y x)) (W x) +
        G.inner x (PDE.DeTurck.connectionDifference g G x (Z x) ((LeviCivita G) Y x (X x))) (W x) +
        G.inner x (PDE.DeTurck.connectionDifference g G x (Z x) (Y x)) ((LeviCivita G) W x (X x))) at h
  rw [h]
  change _ = G.inner x
    (((LeviCivita G) S x (X x)) -
      PDE.DeTurck.connectionDifference g G x (Z x) ((LeviCivita G) Y x (X x)) -
      PDE.DeTurck.connectionDifference g G x ((LeviCivita G) Z x (X x)) (Y x)) (W x)
  rw [map_sub, sub_apply, map_sub, sub_apply]
  change G.inner x ((LeviCivita G) S x (X x)) (W x) +
      G.inner x (S x) ((LeviCivita G) W x (X x)) -
      (G.inner x (PDE.DeTurck.connectionDifference g G x ((LeviCivita G) Z x (X x)) (Y x)) (W x) +
        G.inner x (PDE.DeTurck.connectionDifference g G x (Z x) ((LeviCivita G) Y x (X x))) (W x) +
        G.inner x (S x) ((LeviCivita G) W x (X x))) = _
  ring

open DifferentialGeometry.Tensor.RSTensor DifferentialGeometry.Geometry.Operator
private def quadraticPerm : Fin 6 ≃ Fin 6 where
  toFun := ![4, 3, 0, 1, 2, 5]
  invFun := ![2, 3, 4, 1, 0, 5]
  left_inv := by decide
  right_inv := by decide

def connectionDifferenceQuadraticField (G g : SmoothRiemannianMetric I M) :=
  metricTraceFirstTwoField G (Tensor0SField.domDomCongr ∞ quadraticPerm
    (tensor0SFieldProduct ∞ (metricLoweredConnectionDifferenceField G g)
      (metricLoweredConnectionDifferenceField G g)))

omit [CompleteSpace E] [BoundarylessManifold I M] [T2Space M] in
private theorem trace_orthonormal (G : SmoothRiemannianMetric I M)
    (T : Tensor0SField (I := I) (M := M) ∞ 6) (x : M)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ (TangentSpace I x))
    (hi : MetricInverseInBasis G x b (identityInvMetric (Idx := ι)))
    (w : Fin 4 → TangentSpace I x) :
    metricTraceFirstTwoField G T x w = ∑ i, T x (metricTraceInput (b i) (b i) w) := by
  erw [metricTraceFirstTwoField_apply, metricTraceFirstTwo0STensor_apply,
    metricTraceFirstTwo0SAt_eq_sum_basis G b (identityInvMetric (Idx := ι)) hi]
  simp only [metricTrace0S2InBasis, identityInvMetric, diagonalInvMetric,
    ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

omit [CompleteSpace E] in
private theorem quadratic_product_eval (G g : SmoothRiemannianMetric I M)
    (x : M) (a b : TangentSpace I x) (w : Fin 4 → TangentSpace I x) :
    Tensor0SField.domDomCongr ∞ quadraticPerm
      (tensor0SFieldProduct ∞ (metricLoweredConnectionDifferenceField G g)
        (metricLoweredConnectionDifferenceField G g)) x (metricTraceInput a b w) =
      G.inner x (PDE.DeTurck.connectionDifference g G x (w 2) (w 1)) a *
        G.inner x (PDE.DeTurck.connectionDifference g G x b (w 0)) (w 3) := by
  let L := metricLoweredConnectionDifferenceField G g
  let V : Fin 6 → TangentSpace I x := fun i => metricTraceInput a b w (quadraticPerm i)
  have hleft : L x (V ∘ Fin.castAdd 3) =
      G.inner x (PDE.DeTurck.connectionDifference g G x (w 2) (w 1)) a := rfl
  have hright : L x (V ∘ Fin.natAdd 3) =
      G.inner x (PDE.DeTurck.connectionDifference g G x b (w 0)) (w 3) := rfl
  exact (tensor0SField_product_apply L L x V).trans
    (congrArg₂ (fun r s : ℝ => r * s) hleft hright)

omit [CompleteSpace E] in
theorem connectionDifferenceQuadraticField_apply (G g : SmoothRiemannianMetric I M)
    (x : M) (w : Fin 4 → TangentSpace I x) :
    connectionDifferenceQuadraticField G g x w =
      G.inner x (PDE.DeTurck.connectionDifference g G x
        (PDE.DeTurck.connectionDifference g G x (w 2) (w 1)) (w 0)) (w 3) := by
  classical
  obtain ⟨b, hb⟩ := DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis G x
  have hi := metricInverseInBasis_identity_of_orthonormal G b hb
  rw [connectionDifferenceQuadraticField, trace_orthonormal G _ x b hi w]
  simp_rw [quadratic_product_eval]
  let Z := PDE.DeTurck.connectionDifference g G x (w 2) (w 1)
  have hrepr (i) : b.repr Z i = G.inner x Z (b i) := by
    rw [basis_repr_eq_sum_inv_inner G x b
      (identityInvMetric (Idx := Fin (Module.finrank ℝ (TangentSpace I x)))) hi Z i]
    simp only [identityInvMetric, diagonalInvMetric, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have he : (∑ i, G.inner x Z (b i) • b i) = Z := by
    simpa only [hrepr] using b.sum_repr Z
  calc
    (∑ i, G.inner x Z (b i) * G.inner x (PDE.DeTurck.connectionDifference g G x (b i) (w 0)) (w 3)) =
        G.inner x (PDE.DeTurck.connectionDifference g G x
          (∑ i, G.inner x Z (b i) • b i) (w 0)) (w 3) := by
      simp only [map_sum, sum_apply, map_smul, smul_apply, smul_eq_mul]
    _ = G.inner x (PDE.DeTurck.connectionDifference g G x Z (w 0)) (w 3) := by rw [he]

private def derivativeFirstPerm : Fin 4 ≃ Fin 4 := Equiv.swap 1 2
private def derivativeSecondPerm : Fin 4 ≃ Fin 4 where
  toFun := ![1, 2, 0, 3]
  invFun := ![2, 0, 1, 3]
  left_inv := by decide
  right_inv := by decide
private def flipFirstTwoPerm : Fin 4 ≃ Fin 4 := Equiv.swap 0 1

theorem exists_rm04Section_connection_difference :
    ∃ (e₁ e₂ e₃ : Fin 4 ≃ Fin 4) (e₄ : Fin 6 ≃ Fin 6),
      ∀ G g : SmoothRiemannianMetric I M,
        let L := metricLoweredConnectionDifferenceField G g
        let Q := metricTraceFirstTwoField G
          (Tensor0SField.domDomCongr ∞ e₄ (tensor0SFieldProduct ∞ L L))
        CovariantDerivative.rm04Section G (metricCov g) (metricCov_smooth g) =
          metricRm04 G + Tensor0SField.domDomCongr ∞ e₁ (covStep G 3 L) -
            Tensor0SField.domDomCongr ∞ e₂ (covStep G 3 L) + Q -
            Tensor0SField.domDomCongr ∞ e₃ Q := by
  refine ⟨derivativeFirstPerm, derivativeSecondPerm, flipFirstTwoPerm, quadraticPerm, ?_⟩
  intro G g
  dsimp only
  apply DFunLike.ext
  intro x
  apply tensor0SSpace_ext (I := I) 4 x
  intro w
  obtain ⟨X, hX⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
    (V := TangentSpace I) (n := (⊤ : ℕ∞)) x (w 0)
  obtain ⟨Y, hY⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
    (V := TangentSpace I) (n := (⊤ : ℕ∞)) x (w 1)
  obtain ⟨Z, hZ⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
    (V := TangentSpace I) (n := (⊤ : ℕ∞)) x (w 2)
  obtain ⟨W, hW⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
    (V := TangentSpace I) (n := (⊤ : ℕ∞)) x (w 3)
  let L := metricLoweredConnectionDifferenceField G g
  have hw : w = vec4 (X x) (Y x) (Z x) (W x) := by
    funext i
    fin_cases i <;> simp [vec4, hX, hY, hZ, hW]
  have hF (G₀ g₀ : SmoothRiemannianMetric I M) :
      CovariantDerivative.rm04Section G₀ (metricCov g₀) (metricCov_smooth g₀) x w =
        G₀.inner x (riemannSec (LeviCivita g₀) X Y Z x) (W x) := by
    rw [hw]
    exact (CovariantDerivative.rm04Section_apply_smooth G₀ (metricCov g₀)
      (metricCov_smooth g₀) X Y Z W x).trans (G₀.symm x _ _)
  have hbase : metricRm04 G x w = G.inner x (riemannSec (LeviCivita G) X Y Z x) (W x) := hF G G
  have hd₁ : Tensor0SField.domDomCongr ∞ derivativeFirstPerm (covStep G 3 L) x w =
      G.inner x (covDerivDiff (LeviCivita G) (LeviCivita g) X Y Z x) (W x) := by
    change covStep G 3 L x (fun i => w (derivativeFirstPerm i)) = _
    have he : (fun i => w (derivativeFirstPerm i)) = vec4 (X x) (Z x) (Y x) (W x) := by
      funext i
      fin_cases i <;> simp [derivativeFirstPerm, Equiv.swap_apply_def, vec4, hX, hY, hZ, hW]
    rw [he]
    exact covStep_metricLoweredConnectionDifference_apply G g X Y Z W x
  have hd₂ : Tensor0SField.domDomCongr ∞ derivativeSecondPerm (covStep G 3 L) x w =
      G.inner x (covDerivDiff (LeviCivita G) (LeviCivita g) Y X Z x) (W x) := by
    change covStep G 3 L x (fun i => w (derivativeSecondPerm i)) = _
    have he : (fun i => w (derivativeSecondPerm i)) = vec4 (Y x) (Z x) (X x) (W x) := by
      funext i
      fin_cases i <;> simp [derivativeSecondPerm, vec4, hX, hY, hZ, hW]
    rw [he]
    exact covStep_metricLoweredConnectionDifference_apply G g Y X Z W x
  have hq₁ : connectionDifferenceQuadraticField G g x w =
      G.inner x (PDE.DeTurck.connectionDifference g G x
        (PDE.DeTurck.connectionDifference g G x (Z x) (Y x)) (X x)) (W x) := by
    rw [connectionDifferenceQuadraticField_apply, hX, hY, hZ, hW]
  have hq₂ : Tensor0SField.domDomCongr ∞ flipFirstTwoPerm (connectionDifferenceQuadraticField G g) x w =
      G.inner x (PDE.DeTurck.connectionDifference g G x
        (PDE.DeTurck.connectionDifference g G x (Z x) (X x)) (Y x)) (W x) := by
    change connectionDifferenceQuadraticField G g x (fun i => w (flipFirstTwoPerm i)) = _
    rw [connectionDifferenceQuadraticField_apply]
    change G.inner x (PDE.DeTurck.connectionDifference g G x
      (PDE.DeTurck.connectionDifference g G x (w 2) (w 0)) (w 1)) (w 3) = _
    rw [hX, hY, hZ, hW]
  change CovariantDerivative.rm04Section G (metricCov g) (metricCov_smooth g) x w =
    metricRm04 G x w + Tensor0SField.domDomCongr ∞ derivativeFirstPerm (covStep G 3 L) x w -
      Tensor0SField.domDomCongr ∞ derivativeSecondPerm (covStep G 3 L) x w +
      connectionDifferenceQuadraticField G g x w - Tensor0SField.domDomCongr ∞ flipFirstTwoPerm (connectionDifferenceQuadraticField G g) x w
  rw [hF G g, hbase, hd₁, hd₂, hq₁, hq₂]
  have hr := riemannSec_difference (LeviCivita G) (LeviCivita g)
    X.contMDiff Y.contMDiff Z.contMDiff (LeviCivita_torsion_eq_zero G) x
  have ht := congrArg (fun v => G.inner x v (W x)) hr
  simp only [map_add, add_apply, map_sub, sub_apply] at ht
  change G.inner x (riemannSec (LeviCivita g) X Y Z x) (W x) =
    G.inner x (riemannSec (LeviCivita G) X Y Z x) (W x) +
      (G.inner x (covDerivDiff (LeviCivita G) (LeviCivita g) X Y Z x) (W x) -
        G.inner x (covDerivDiff (LeviCivita G) (LeviCivita g) Y X Z x) (W x)) +
      (G.inner x (PDE.DeTurck.connectionDifference g G x
        (PDE.DeTurck.connectionDifference g G x (Z x) (Y x)) (X x)) (W x) -
        G.inner x (PDE.DeTurck.connectionDifference g G x
          (PDE.DeTurck.connectionDifference g G x (Z x) (X x)) (Y x)) (W x)) at ht
  linarith only [ht]

end DifferentialGeometry.Geometry.Curvature
