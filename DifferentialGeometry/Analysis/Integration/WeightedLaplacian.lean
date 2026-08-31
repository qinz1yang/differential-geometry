import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.Green
import DifferentialGeometry.Geometry.Operator.WeightedLaplacian

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold ContDiff

namespace DifferentialGeometry.Integral.DivergenceTheorem

open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]

omit [FiniteDimensional Real E] [SigmaCompactSpace M] [T2Space M]
    [I.Boundaryless] in
private theorem tangentSectionAction_exp_neg
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (f : C^∞⟮I, M; Real⟯) (x : M) :
    tangentSectionAction (I := I) X (fun y : M => Real.exp (-f y)) x =
      -Real.exp (-f x) * tangentSectionAction (I := I) X f x := by
  have hmf := mfderiv_exp_neg_toLinearMap (I := I) (f := (f : M → Real))
    (f.contMDiff.mdifferentiableAt (by simp) :
      MDifferentiableAt I (modelWithCornersSelf Real Real) (f : M → Real) x)
  unfold tangentSectionAction
  have happly := congrArg
    (fun L : TangentSpace I x →ₗ[Real] Real => L (X x)) hmf
  change
    (show Real from mfderiv I (modelWithCornersSelf Real Real)
      (fun y : M => Real.exp (-f y)) x (X x)) =
      -Real.exp (-f x) *
        (show Real from mfderiv I (modelWithCornersSelf Real Real) f x (X x)) at happly
  exact happly

theorem integral_mul_weightedLaplacian_eq_neg_integral_inner_grad
    (g : SmoothRiemannianMetric I M) (f u v : C^∞⟮I, M; Real⟯)
    (hv : HasCompactSupport v) :
    ∫ x, u x * weightedLaplacian (I := I) g f v x * Real.exp (-f x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      -∫ x, g.inner x (gradFun (I := I) g u x) (gradFun (I := I) g v x) *
          Real.exp (-f x) ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  classical
  let e : M → Real := fun x => Real.exp (-f x)
  have he : ContMDiff I (modelWithCornersSelf Real Real) ∞ e := by
    exact Real.contDiff_exp.contMDiff.comp f.contMDiff.neg
  let V : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ := gradG (I := I) g v
  have hV : HasCompactSupport V := hasCompactSupport_grad_g (I := I) g v hv
  let q : M → Real := fun x => e x * u x
  have hq : ContMDiff I (modelWithCornersSelf Real Real) ∞ q := he.mul u.contMDiff
  let X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    smoothSmul (I := I) q hq V
  have hX : HasCompactSupport X := by
    have hsupp : Function.support (X : ∀ x, TangentSpace I x) ⊆
        Function.support (V : ∀ x, TangentSpace I x) := by
      intro x hx
      by_contra hVx
      have hVzero : V x = 0 := Function.notMem_support.mp hVx
      have hXzero : (X : ∀ x, TangentSpace I x) x = (0 : TangentSpace I x) := by
        change q x • V x = (0 : TangentSpace I x)
        rw [hVzero]
        exact smul_zero _
      exact hx hXzero
    refine HasCompactSupport.of_support_subset_isCompact (hV : IsCompact (tsupport V)) ?_
    exact hsupp.trans (subset_tsupport _)
  have hdiv (x : M) :
      divergenceG (I := I) g X x =
        Real.exp (-f x) *
          (u x * weightedLaplacian (I := I) g f v x +
            g.inner x (gradFun (I := I) g u x) (gradFun (I := I) g v x)) := by
    rw [show X = smoothSmul (I := I) q hq V by rfl,
      divergence_g_smoothSmul (I := I) g q hq V x]
    dsimp only [q]
    change e x * u x * divergenceG (I := I) g V x +
        tangentSectionAction (I := I) V (e * (u : M → Real)) x = _
    rw [
      tangentSectionAction_mul (I := I) V he u.contMDiff x,
      tangentSectionAction_exp_neg (I := I) V f x,
      tangentSectionAction_eq_inner_grad_g (I := I) g f V x,
      tangentSectionAction_eq_inner_grad_g (I := I) g u V x]
    simp only [V, grad_g_apply, weightedLaplacian_apply]
    dsimp only [q, e]
    rw [← Δ_g_def (I := I) g v x]
    rw [g.symm x (gradFun (I := I) g v x) (gradFun (I := I) g f x),
      g.symm x (gradFun (I := I) g v x) (gradFun (I := I) g u x)]
    ring
  have hzero := integral_divergence_eq_zero_of_hasCompactSupport (I := I) g X hX
  have hzero' :
      ∫ x, Real.exp (-f x) *
          (u x * weightedLaplacian (I := I) g f v x +
            g.inner x (gradFun (I := I) g u x) (gradFun (I := I) g v x))
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) = 0 := by
    rw [← hzero]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => (hdiv x).symm
  have hdivV : HasCompactSupport (divergenceG (I := I) g V) :=
    hasCompactSupport_divergence_g (I := I) g hV
  have hactF : HasCompactSupport (tangentSectionAction (I := I) V f) :=
    hasCompactSupport_tangentSectionAction (I := I) hV f
  have hactU : HasCompactSupport (tangentSectionAction (I := I) V u) :=
    hasCompactSupport_tangentSectionAction (I := I) hV u
  have hw : HasCompactSupport (fun x : M =>
      u x * (divergenceG (I := I) g V x - tangentSectionAction (I := I) V f x) * e x) :=
    ((hdivV.sub hactF).mul_left).mul_right
  have hi : HasCompactSupport (fun x : M =>
      tangentSectionAction (I := I) V u x * e x) := hactU.mul_right
  have hwcont : Continuous (fun x : M =>
      u x * (divergenceG (I := I) g V x - tangentSectionAction (I := I) V f x) * e x) :=
    (u.contMDiff.continuous.mul
      ((divergence_g_contMDiff (I := I) g V).continuous.sub
        (tangentSectionAction_contMDiff (I := I) V f.contMDiff).continuous)).mul he.continuous
  have hicont : Continuous (fun x : M =>
      tangentSectionAction (I := I) V u x * e x) :=
    (tangentSectionAction_contMDiff (I := I) V u.contMDiff).continuous.mul he.continuous
  have hwint : Integrable (fun x : M =>
      u x * (divergenceG (I := I) g V x - tangentSectionAction (I := I) V f x) * e x)
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    Continuous.integrable_of_hasCompactSupport_riemannianVolumeMeasure
      (I := I) g hwcont hw
  have hiint : Integrable (fun x : M => tangentSectionAction (I := I) V u x * e x)
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    Continuous.integrable_of_hasCompactSupport_riemannianVolumeMeasure
      (I := I) g hicont hi
  have hsplit :
      ∫ x, Real.exp (-f x) *
          (u x * weightedLaplacian (I := I) g f v x +
            g.inner x (gradFun (I := I) g u x) (gradFun (I := I) g v x))
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      (∫ x, u x * weightedLaplacian (I := I) g f v x * Real.exp (-f x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) +
      ∫ x, g.inner x (gradFun (I := I) g u x) (gradFun (I := I) g v x) *
        Real.exp (-f x) ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    have hwEq (x : M) :
        u x * weightedLaplacian (I := I) g f v x * Real.exp (-f x) =
          u x * (divergenceG (I := I) g V x -
            tangentSectionAction (I := I) V f x) * e x := by
      rw [weightedLaplacian_apply,
        tangentSectionAction_eq_inner_grad_g (I := I) g f V x]
      simp only [V, grad_g_apply, e]
      rw [← Δ_g_def (I := I) g v x]
      rw [g.symm x (gradFun (I := I) g v x) (gradFun (I := I) g f x)]
    have hiEq (x : M) :
        g.inner x (gradFun (I := I) g u x) (gradFun (I := I) g v x) *
            Real.exp (-f x) =
          tangentSectionAction (I := I) V u x * e x := by
      rw [tangentSectionAction_eq_inner_grad_g (I := I) g u V x]
      simp only [V, grad_g_apply, e]
      rw [g.symm x (gradFun (I := I) g v x) (gradFun (I := I) g u x)]
    calc
      _ = ∫ x,
          (u x * (divergenceG (I := I) g V x - tangentSectionAction (I := I) V f x) * e x +
            tangentSectionAction (I := I) V u x * e x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
            apply integral_congr_ae
            refine Filter.Eventually.of_forall ?_
            intro x
            change Real.exp (-f x) *
                (u x * weightedLaplacian (I := I) g f v x +
                  g.inner x (gradFun (I := I) g u x) (gradFun (I := I) g v x)) = _
            calc
              _ = u x * weightedLaplacian (I := I) g f v x * Real.exp (-f x) +
                  g.inner x (gradFun (I := I) g u x) (gradFun (I := I) g v x) *
                    Real.exp (-f x) := by ring
              _ = _ := by rw [hwEq x, hiEq x]
      _ = (∫ x, u x * (divergenceG (I := I) g V x -
              tangentSectionAction (I := I) V f x) * e x
            ∂(riemannianVolumeMeasure (I := I) (M := M) g)) +
          ∫ x, tangentSectionAction (I := I) V u x * e x
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
        integral_add hwint hiint
      _ = _ := by
        congr 1
        · apply integral_congr_ae
          exact Filter.Eventually.of_forall fun x => (hwEq x).symm
        · apply integral_congr_ae
          exact Filter.Eventually.of_forall fun x => (hiEq x).symm
  rw [hsplit] at hzero'
  linarith

theorem integral_mul_weightedLaplacian_comm
    (g : SmoothRiemannianMetric I M) (f u v : C^∞⟮I, M; Real⟯)
    (hu : HasCompactSupport u) (hv : HasCompactSupport v) :
    ∫ x, u x * weightedLaplacian (I := I) g f v x * Real.exp (-f x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ x, v x * weightedLaplacian (I := I) g f u x * Real.exp (-f x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  rw [integral_mul_weightedLaplacian_eq_neg_integral_inner_grad (I := I) g f u v hv,
    integral_mul_weightedLaplacian_eq_neg_integral_inner_grad (I := I) g f v u hu]
  apply congrArg Neg.neg
  apply integral_congr_ae
  refine Filter.Eventually.of_forall ?_
  intro x
  change g.inner x (gradFun (I := I) g u x) (gradFun (I := I) g v x) *
      Real.exp (-f x) =
    g.inner x (gradFun (I := I) g v x) (gradFun (I := I) g u x) *
      Real.exp (-f x)
  rw [g.symm x]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem integral_mul_weightedLaplacian_add_inner_grad_eq_zero_of_compact
    [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (f u v : C^∞⟮I, M; Real⟯) :
    ∫ x, (u x * weightedLaplacian (I := I) g f v x +
          g.inner x (gradFun (I := I) g u x) (gradFun (I := I) g v x)) *
        Real.exp (-f x) ∂(riemannianVolumeMeasure (I := I) (M := M) g) = 0 := by
  let V : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ := gradG (I := I) g v
  have hweighted : ContMDiff I 𝓘(Real, Real) ∞
      (weightedLaplacian (I := I) g f v) := by
    have hdiv := divergence_g_contMDiff (I := I) g V
    have hact := tangentSectionAction_contMDiff (I := I) V f.contMDiff
    have heq : weightedLaplacian (I := I) g f v =
        fun x : M => divergenceG (I := I) g V x -
          tangentSectionAction (I := I) V f x := by
      funext x
      rw [weightedLaplacian_apply, Δ_g_def,
        tangentSectionAction_eq_inner_grad_g (I := I) g f V x]
      simp only [V, grad_g_apply]
      rw [g.symm x (gradFun (I := I) g f x) (gradFun (I := I) g v x)]
    rw [heq]
    exact hdiv.sub hact
  have hinner : ContMDiff I 𝓘(Real, Real) ∞
      (fun x : M =>
        g.inner x (gradFun (I := I) g u x) (gradFun (I := I) g v x)) := by
    have hact := tangentSectionAction_contMDiff (I := I) V u.contMDiff
    have heq : (fun x : M =>
        g.inner x (gradFun (I := I) g u x) (gradFun (I := I) g v x)) =
        tangentSectionAction (I := I) V u := by
      funext x
      rw [tangentSectionAction_eq_inner_grad_g (I := I) g u V x]
      simp only [V, grad_g_apply]
      exact g.symm x _ _
    rw [heq]
    exact hact
  let p : M → Real := fun x =>
    u x * weightedLaplacian (I := I) g f v x * Real.exp (-f x)
  let q : M → Real := fun x =>
    g.inner x (gradFun (I := I) g u x) (gradFun (I := I) g v x) *
      Real.exp (-f x)
  have hpcont : Continuous p :=
    (u.contMDiff.continuous.mul hweighted.continuous).mul
      (Real.continuous_exp.comp f.contMDiff.continuous.neg)
  have hqcont : Continuous q :=
    hinner.continuous.mul
      (Real.continuous_exp.comp f.contMDiff.continuous.neg)
  have hpint : Integrable p (riemannianVolumeMeasure (I := I) (M := M) g) :=
    DifferentialGeometry.Integral.DivergenceTheorem.Continuous.integrable_of_hasCompactSupport_riemannianVolumeMeasure
      (I := I) g hpcont (HasCompactSupport.of_compactSpace _)
  have hqint : Integrable q (riemannianVolumeMeasure (I := I) (M := M) g) :=
    DifferentialGeometry.Integral.DivergenceTheorem.Continuous.integrable_of_hasCompactSupport_riemannianVolumeMeasure
      (I := I) g hqcont (HasCompactSupport.of_compactSpace _)
  have hibp := integral_mul_weightedLaplacian_eq_neg_integral_inner_grad
    (I := I) (M := M) g f u v (HasCompactSupport.of_compactSpace _)
  rw [show (fun x : M =>
      (u x * weightedLaplacian (I := I) g f v x +
          g.inner x (gradFun (I := I) g u x) (gradFun (I := I) g v x)) *
        Real.exp (-f x)) = fun x : M => p x + q x by
    funext x
    dsimp [p, q]
    ring]
  rw [integral_add hpint hqint]
  change (∫ x, u x * weightedLaplacian (I := I) g f v x * Real.exp (-f x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) +
      ∫ x, g.inner x (gradFun (I := I) g u x) (gradFun (I := I) g v x) *
        Real.exp (-f x) ∂(riemannianVolumeMeasure (I := I) (M := M) g) = 0
  rw [hibp]
  ring

end DifferentialGeometry.Integral.DivergenceTheorem
