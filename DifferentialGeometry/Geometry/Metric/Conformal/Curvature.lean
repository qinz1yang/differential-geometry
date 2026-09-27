import DifferentialGeometry.Geometry.Metric.Conformal.Connection
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.ConnectionDifference.Curvature
import DifferentialGeometry.Geometry.Operator.Gradient.Regularity
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Identities.ContractedBianchi

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Curvature

open Bundle
open Connection Operator
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [T2Space M] [BoundarylessManifold I M]

theorem covDerivDiff_conformalMetric
    (g : SmoothRiemannianMetric I M) (u : C^∞⟮I, M; Real⟯)
    (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    covDerivDiff (LeviCivita g) (LeviCivita (conformalMetric g u)) X Y Z x =
      g.inner x (LeviCivita g (gradientFun g u) x (X x)) (Y x) • Z x +
      g.inner x (LeviCivita g (gradientFun g u) x (X x)) (Z x) • Y x -
      g.inner x (Y x) (Z x) • LeviCivita g (gradientFun g u) x (X x) := by
  let G : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ⟨gradientFun g u, gradientFun_smooth g u.contMDiff⟩
  let a : M → Real := fun y => g.inner y (G y) (Y y)
  let b : M → Real := fun y => g.inner y (G y) (Z y)
  let c : M → Real := fun y => -g.inner y (Y y) (Z y)
  have ha : MDiffAt a x :=
    (contMDiff_g_inner_of_smooth_sections g G Y).mdifferentiableAt (by simp)
  have hb : MDiffAt b x :=
    (contMDiff_g_inner_of_smooth_sections g G Z).mdifferentiableAt (by simp)
  have hc : MDiffAt c x :=
    (contMDiff_g_inner_of_smooth_sections g Y Z).neg.mdifferentiableAt (by simp)
  have hdiff : diffSec (LeviCivita g) (LeviCivita (conformalMetric g u)) Y Z =
      a • (Z : (y : M) → TangentSpace I y) +
      b • (Y : (y : M) → TangentSpace I y) + c • G := by
    funext y
    change PDE.DeTurck.connectionDifference (conformalMetric g u) g y (Z y) (Y y) = _
    rw [connectionDifference_conformalMetric]
    change _ = g.inner y (gradientFun g u y) (Y y) • Z y +
      g.inner y (gradientFun g u y) (Z y) • Y y +
      (-g.inner y (Y y) (Z y)) • gradientFun g u y
    rw [inner_gradientFun, inner_gradientFun, neg_smul, sub_eq_add_neg]
  have hderiv : LeviCivita g
      (diffSec (LeviCivita g) (LeviCivita (conformalMetric g u)) Y Z) x =
      a x • LeviCivita g Z x + (mvfderiv I a x).smulRight (Z x) +
      (b x • LeviCivita g Y x + (mvfderiv I b x).smulRight (Y x)) +
      (c x • LeviCivita g G x + (mvfderiv I c x).smulRight (G x)) := by
    rw [hdiff, (LeviCivita g).isCovariantDerivativeOnUniv.add
      (mdifferentiableAt_add_section (ha.smul_section Z.mdifferentiableAt)
        (hb.smul_section Y.mdifferentiableAt)) (hc.smul_section G.mdifferentiableAt),
      (LeviCivita g).isCovariantDerivativeOnUniv.add
        (ha.smul_section Z.mdifferentiableAt) (hb.smul_section Y.mdifferentiableAt),
      (LeviCivita g).isCovariantDerivativeOnUniv.leibniz Z.mdifferentiableAt ha,
      (LeviCivita g).isCovariantDerivativeOnUniv.leibniz Y.mdifferentiableAt hb,
      (LeviCivita g).isCovariantDerivativeOnUniv.leibniz G.mdifferentiableAt hc]
  have hda := (LeviCivita_isMetricCompatible g).apply
    (x := x) G.mdifferentiableAt Y.mdifferentiableAt (X x)
  have hdb := (LeviCivita_isMetricCompatible g).apply
    (x := x) G.mdifferentiableAt Z.mdifferentiableAt (X x)
  have hdc := (LeviCivita_isMetricCompatible g).apply
    (x := x) Y.mdifferentiableAt Z.mdifferentiableAt (X x)
  change mvfderiv I a x (X x) = _ at hda
  change mvfderiv I b x (X x) = _ at hdb
  have hdc' : mvfderiv I c x (X x) =
      -(g.inner x (LeviCivita g Y x (X x)) (Z x) +
        g.inner x (Y x) (LeviCivita g Z x (X x))) := by
    change mvfderiv I (fun y => -g.inner y (Y y) (Z y)) x (X x) = _
    rw [show (fun y => -g.inner y (Y y) (Z y)) =
      -(fun y => g.inner y (Y y) (Z y)) from rfl, mvfderiv_neg, neg_apply]
    exact congrArg Neg.neg hdc
  unfold covDerivDiff
  rw [hderiv]
  change _ - PDE.DeTurck.connectionDifference (conformalMetric g u) g x
      (Z x) (covApply (LeviCivita g) X Y x) -
      PDE.DeTurck.connectionDifference (conformalMetric g u) g x
      (covApply (LeviCivita g) X Z x) (Y x) = _
  rw [connectionDifference_conformalMetric, connectionDifference_conformalMetric]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply]
  rw [hda, hdb, hdc']
  dsimp [a, b, c, G, covApply]
  simp only [inner_gradientFun, add_smul, neg_smul]
  abel

private theorem connectionDifference_quadratic_conformalMetric
    (g : SmoothRiemannianMetric I M) (u : C^∞⟮I, M; Real⟯)
    (x : M) (v w z : TangentSpace I x) :
    PDE.DeTurck.connectionDifference (conformalMetric g u) g x
        (PDE.DeTurck.connectionDifference (conformalMetric g u) g x z w) v -
      PDE.DeTurck.connectionDifference (conformalMetric g u) g x
        (PDE.DeTurck.connectionDifference (conformalMetric g u) g x z v) w =
      (mvfderiv I (u : M → Real) x w * mvfderiv I (u : M → Real) x z -
        normGradSqFun g u x * g.inner x w z) • v -
      (mvfderiv I (u : M → Real) x v * mvfderiv I (u : M → Real) x z -
        normGradSqFun g u x * g.inner x v z) • w +
      (mvfderiv I (u : M → Real) x v * g.inner x w z -
        mvfderiv I (u : M → Real) x w * g.inner x v z) • gradientFun g u x := by
  simp_rw [connectionDifference_conformalMetric]
  apply SmoothRiemannianMetric.eq_of_inner_eq g
  intro t
  simp only [map_sub, map_add, map_smul, sub_apply, add_apply, smul_apply,
    smul_eq_mul, inner_gradientFun]
  rw [g.symm x v (gradientFun g u x), g.symm x w (gradientFun g u x),
    inner_gradientFun, inner_gradientFun, g.symm x w v]
  rw [show mvfderiv I (u : M → Real) x (gradientFun g u x) =
      normGradSqFun g u x from (inner_gradientFun g u x (gradientFun g u x)).symm]
  ring

private theorem inner_LeviCivita_gradientFun_symm
    (g : SmoothRiemannianMetric I M) (u : C^∞⟮I, M; Real⟯)
    (X Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    g.inner x (LeviCivita g (gradientFun g u) x (X x)) (Y x) =
      g.inner x (LeviCivita g (gradientFun g u) x (Y x)) (X x) := by
  let : CompleteSpace E := FiniteDimensional.complete Real E
  have hgrad := gradientFun_mdiffAt g u.contMDiff x
  have hxy := (LeviCivita_isMetricCompatible g).apply
    hgrad Y.mdifferentiableAt (X x)
  have hyx := (LeviCivita_isMetricCompatible g).apply
    hgrad X.mdifferentiableAt (Y x)
  change mvfderiv I (fun y => g.inner y (gradientFun g u y) (Y y)) x (X x) = _ at hxy
  change mvfderiv I (fun y => g.inner y (gradientFun g u y) (X y)) x (Y x) = _ at hyx
  simp_rw [inner_gradientFun] at hxy hyx
  have hbr := Connection.mvfderiv_apply_mlieBracket
    X.mdifferentiableAt Y.mdifferentiableAt
    (u.contMDiff.contMDiffAt.of_le (show (2 : WithTop ℕ∞) ≤ ∞ by norm_cast))
    ((I.isInteriorPoint_iff (x := x)).mp BoundarylessManifold.isInteriorPoint)
  have ht := (CovariantDerivative.torsion_eq_zero_iff (LeviCivita g)).mp
    (LeviCivita_torsion_eq_zero g) (x := x) X.mdifferentiableAt Y.mdifferentiableAt
  change LeviCivita g Y x (X x) - LeviCivita g X x (Y x) =
    VectorField.mlieBracket I X Y x at ht
  rw [← ht, map_sub] at hbr
  change mvfderiv I (fun y => mvfderiv I (u : M → Real) y (Y y)) x (X x) = _ at hxy
  change mvfderiv I (fun y => mvfderiv I (u : M → Real) y (X y)) x (Y x) = _ at hyx
  linarith

theorem riemannOp_conformalMetric
    (g : SmoothRiemannianMetric I M) (u : C^∞⟮I, M; Real⟯)
    (x : M) (v w z : TangentSpace I x) :
    riemannOp (LeviCivita (conformalMetric g u)) x v w z =
      riemannOp (LeviCivita g) x v w z +
      g.inner x (LeviCivita g (gradientFun g u) x v) z • w -
      g.inner x (LeviCivita g (gradientFun g u) x w) z • v -
      g.inner x w z • LeviCivita g (gradientFun g u) x v +
      g.inner x v z • LeviCivita g (gradientFun g u) x w +
      (mvfderiv I (u : M → Real) x w * mvfderiv I (u : M → Real) x z -
        normGradSqFun g u x * g.inner x w z) • v -
      (mvfderiv I (u : M → Real) x v * mvfderiv I (u : M → Real) x z -
        normGradSqFun g u x * g.inner x v z) • w +
      (mvfderiv I (u : M → Real) x v * g.inner x w z -
        mvfderiv I (u : M → Real) x w * g.inner x v z) • gradientFun g u x := by
  let : CompleteSpace E := FiniteDimensional.complete Real E
  obtain ⟨X, hX⟩ := ContMDiffSection.exists_eq_at
    (I := I) (n := (⊤ : ℕ∞)) (F := E) (V := TangentSpace I) x v
  obtain ⟨Y, hY⟩ := ContMDiffSection.exists_eq_at
    (I := I) (n := (⊤ : ℕ∞)) (F := E) (V := TangentSpace I) x w
  obtain ⟨Z, hZ⟩ := ContMDiffSection.exists_eq_at
    (I := I) (n := (⊤ : ℕ∞)) (F := E) (V := TangentSpace I) x z
  have h := riemannSec_difference (LeviCivita g) (LeviCivita (conformalMetric g u))
    X.contMDiff Y.contMDiff Z.contMDiff (LeviCivita_torsion_eq_zero g) x
  rw [covDerivDiff_conformalMetric, covDerivDiff_conformalMetric] at h
  change riemannSec (LeviCivita (conformalMetric g u)) X Y Z x =
    riemannSec (LeviCivita g) X Y Z x + _ +
      (PDE.DeTurck.connectionDifference (conformalMetric g u) g x
        (PDE.DeTurck.connectionDifference (conformalMetric g u) g x (Z x) (Y x)) (X x) -
      PDE.DeTurck.connectionDifference (conformalMetric g u) g x
        (PDE.DeTurck.connectionDifference (conformalMetric g u) g x (Z x) (X x)) (Y x)) at h
  rw [connectionDifference_quadratic_conformalMetric] at h
  rw [← riemannOp_apply_smooth (cov := LeviCivita (conformalMetric g u))
    X.contMDiff Y.contMDiff Z.contMDiff,
    ← riemannOp_apply_smooth (cov := LeviCivita g) X.contMDiff Y.contMDiff Z.contMDiff,
    hX, hY, hZ] at h
  have hsymm := inner_LeviCivita_gradientFun_symm g u X Y x
  rw [hX, hY] at hsymm
  rw [h, hsymm]
  abel

theorem ricciTensor_conformalMetric
    (g : SmoothRiemannianMetric I M) (u : C^∞⟮I, M; Real⟯)
    (x : M) (v w : TangentSpace I x) :
    ricciTensor (conformalMetric g u) x v w = ricciTensor g x v w -
      ((Module.finrank Real E : Real) - 2) *
        g.inner x (LeviCivita g (gradientFun g u) x v) w -
      laplacian (LeviCivita g) g u x * g.inner x v w +
      ((Module.finrank Real E : Real) - 2) *
        (mvfderiv I (u : M → Real) x v * mvfderiv I (u : M → Real) x w -
          normGradSqFun g u x * g.inner x v w) := by
  let A := (LeviCivita g (gradientFun g u) x).toLinearMap
  let α := (mvfderiv I (u : M → Real) x).toLinearMap
  let β := (g.inner x w).toLinearMap
  let q := normGradSqFun g u x
  have hendo : ricciEndo (conformalMetric g u) x v w = ricciEndo g x v w +
      (β.comp A).smulRight v - g.inner x (A v) w • LinearMap.id -
      g.inner x v w • A + β.smulRight (A v) +
      (α v * α w - q * g.inner x v w) • LinearMap.id -
      (α w • α - q • β).smulRight v +
      (g.inner x v w • α - α v • β).smulRight (gradientFun g u x) := by
    ext t
    change riemannOp (LeviCivita (conformalMetric g u)) x t v w = _
    rw [riemannOp_conformalMetric]
    simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.smulRight_apply, LinearMap.comp_apply, LinearMap.id_apply, smul_eq_mul,
      ricciEndo_apply]
    dsimp [A, α, β, q]
    rw [g.symm x w (LeviCivita g (gradientFun g u) x t), g.symm x w t,
      mul_comm (mvfderiv I (u : M → Real) x w) (mvfderiv I (u : M → Real) x t),
      mul_comm (g.inner x v w) (mvfderiv I (u : M → Real) x t)]
  rw [ricciTensor_apply, hendo]
  simp only [map_add, map_sub, map_smul, LinearMap.trace_smulRight,
    LinearMap.trace_id, smul_eq_mul]
  dsimp [A, α, β, q, LinearMap.comp_apply]
  rw [g.symm x w (LeviCivita g (gradientFun g u) x v),
    g.symm x w v, g.symm x w (gradientFun g u x), inner_gradientFun]
  rw [show mvfderiv I (u : M → Real) x (gradientFun g u x) = normGradSqFun g u x from
    (inner_gradientFun g u x (gradientFun g u x)).symm]
  change _ = LinearMap.trace Real (TangentSpace I x) (ricciEndo g x v w) -
    _ * _ - LinearMap.trace Real (TangentSpace I x)
      (LeviCivita g (gradientFun g u) x).toLinearMap * _ + _
  rw [show Module.finrank Real (TangentSpace I x) = Module.finrank Real E from rfl]
  dsimp [normGradSqFun, gradientFun]
  ring

theorem scalarCurv_conformalMetric
    (g : SmoothRiemannianMetric I M) (u : C^∞⟮I, M; Real⟯) (x : M) :
    scalarCurv (conformalMetric g u) x = Real.exp (-(2 * u x)) *
      (scalarCurv g x - 2 * ((Module.finrank Real E : Real) - 1) *
        laplacian (LeviCivita g) g u x -
      ((Module.finrank Real E : Real) - 1) * ((Module.finrank Real E : Real) - 2) *
        normGradSqFun g u x) := by
  classical
  by_cases hn : Module.finrank Real E = 0
  · have htang : Module.finrank Real (TangentSpace I x) = 0 := hn
    let : Subsingleton (TangentSpace I x) := Module.finrank_zero_iff.1 htang
    let : IsEmpty (Fin (Module.finrank Real E)) := by rw [hn]; infer_instance
    have hgrad : gradFun g u x = 0 := Subsingleton.elim _ _
    have hcov : (LeviCivita g (gradientFun g u) x).toLinearMap = 0 := Subsingleton.elim _ _
    simp only [scalarCurv, Finset.univ_eq_empty, Finset.sum_empty, laplacian,
      divergence, hcov, map_zero, normGradSqFun, hgrad,
      sub_zero, mul_zero]
  let : NeZero (Module.finrank Real E) := ⟨hn⟩
  let B : Fin (Module.finrank Real E) → TangentSpace I x :=
    fun i => smoothOrthoFrame g x i x
  have hB (i j) : g.inner x (B i) (B j) = if i = j then (1 : Real) else 0 :=
    smoothOrthoFrame_orthonormal_at_center g x i j
  have hB' (i j) : (conformalMetric g u).inner x
      (Real.exp (-u x) • B i) (Real.exp (-u x) • B j) =
      if i = j then (1 : Real) else 0 := by
    rw [conformalMetric_inner]
    simp only [map_smul, smul_apply, smul_eq_mul]
    rw [hB]
    have hexp : Real.exp (2 * u x) * (Real.exp (-u x) * Real.exp (-u x)) = 1 := by
      rw [← Real.exp_add, ← Real.exp_add]
      ring_nf
      exact Real.exp_zero
    calc
      _ = (Real.exp (2 * u x) * (Real.exp (-u x) * Real.exp (-u x))) *
          (if i = j then (1 : Real) else 0) := by ring
      _ = _ := by rw [hexp, one_mul]
  rw [scalarCurv_eq_orthonormal_trace (conformalMetric g u) x
    (fun i => Real.exp (-u x) • B i) hB']
  simp only [map_smul, smul_apply, smul_eq_mul]
  have hscale (i) : Real.exp (-u x) *
      (Real.exp (-u x) * ricciTensor (conformalMetric g u) x (B i) (B i)) =
      Real.exp (-(2 * u x)) * ricciTensor (conformalMetric g u) x (B i) (B i) := by
    rw [← mul_assoc, ← Real.exp_add]
    congr 2
    ring
  simp_rw [hscale]
  rw [← Finset.mul_sum]
  congr 1
  have htrace := trace_eq_ortho_sum g x
    (LeviCivita g (gradientFun g u) x).toLinearMap B hB
  have hq := g_inner_eq_orthonormal_parseval_sum g x
    (gradientFun g u x) (gradientFun g u x) B hB
  simp_rw [inner_gradientFun, g.symm x (B _) (gradientFun g u x), inner_gradientFun] at hq
  rw [show mvfderiv I (u : M → Real) x (gradientFun g u x) = normGradSqFun g u x from
    (inner_gradientFun g u x (gradientFun g u x)).symm] at hq
  change laplacian (LeviCivita g) g u x =
    ∑ i, g.inner x (LeviCivita g (gradientFun g u) x (B i)) (B i) at htrace
  rw [scalarCurv_eq_orthonormal_trace g x B hB]
  simp_rw [ricciTensor_conformalMetric, hB]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ite_true, mul_one]
  rw [← htrace, ← hq]
  ring

theorem scalarCurv_conformalMetric_of_finrank_eq_two
    (g : SmoothRiemannianMetric I M) (u : C^∞⟮I, M; Real⟯)
    (hn : Module.finrank Real E = 2) (x : M) :
    scalarCurv (conformalMetric g u) x = Real.exp (-(2 * u x)) *
      (scalarCurv g x - 2 * laplacian (LeviCivita g) g u x) := by
  rw [scalarCurv_conformalMetric, hn]
  norm_num

end DifferentialGeometry.Geometry.Curvature
