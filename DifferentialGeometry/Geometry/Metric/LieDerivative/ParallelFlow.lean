import DifferentialGeometry.Geometry.Connection.Flow
import DifferentialGeometry.Bundle.PartialMfderiv.Regularity
import DifferentialGeometry.Geometry.Metric.Pullback.Basic

open Bundle Manifold Set
open scoped ContDiff Manifold

namespace DifferentialGeometry.Geometry.Riemannian

open DifferentialGeometry.Analysis.ODE
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Variation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]

private lemma differentiableAt_chartRepAt_mfderiv_curveAt
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (hcomplete : ∀ x : M, ∃ γ : ℝ → M,
      γ 0 = x ∧ IsMIntegralCurve γ (fun y : M ↦ X y))
    (x : M) (v : TangentSpace I x) (t : ℝ) :
    DifferentiableAt ℝ
      (chartRepAt (I := I)
        (fun s ↦ curveAt (fun y : M ↦ X y) hcomplete x s)
        (fun s ↦ mfderiv I I
          (fun y ↦ curveAt (fun z : M ↦ X z) hcomplete y s) x v) t) t := by
  have hV : ContMDiff 𝓘(ℝ, ℝ) I.tangent 2
      (fun s => (⟨curveAt (fun y : M ↦ X y) hcomplete x s,
        mfderiv I I (fun y ↦ curveAt (fun z : M ↦ X z) hcomplete y s) x v⟩ :
          TangentBundle I M)) :=
    (contMDiff_curveAt (I := I) (fun y : M ↦ X y) X.contMDiff hcomplete).tangentMap_const_apply
      (f := fun s y => curveAt (fun z : M ↦ X z) hcomplete y s) x v
        (WithTop.coe_le_coe.2 (le_top : (3 : ℕ∞) ≤ ⊤))
  exact differentiableAt_chartRepAt_of_contMDiff_two hV t

theorem inner_mfderiv_curveAt_eq_of_parallel
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (hcomplete : ∀ x : M, ∃ γ : ℝ → M,
      γ 0 = x ∧ IsMIntegralCurve γ (fun y : M ↦ X y))
    (hpar : ∀ x : M,
      (LeviCivita (I := I) g).toFun (fun y : M ↦ X y) x = 0)
    (x : M) (v w : TangentSpace I x) (t : ℝ) :
    g.inner (curveAt (fun y : M ↦ X y) hcomplete x t)
        (mfderiv I I
          (fun y ↦ curveAt (fun z : M ↦ X z) hcomplete y t) x v)
        (mfderiv I I
          (fun y ↦ curveAt (fun z : M ↦ X z) hcomplete y t) x w) =
      g.inner x v w := by
  classical
  let γ : ℝ → M := fun s ↦
    curveAt (fun y : M ↦ X y) hcomplete x s
  let V : ∀ s, TangentSpace I (γ s) := fun s ↦
    mfderiv I I
      (fun y ↦ curveAt (fun z : M ↦ X z) hcomplete y s) x v
  let W : ∀ s, TangentSpace I (γ s) := fun s ↦
    mfderiv I I
      (fun y ↦ curveAt (fun z : M ↦ X z) hcomplete y s) x w
  have hflow :
      ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞
        (fun p : ℝ × M ↦
          curveAt (fun y : M ↦ X y) hcomplete p.2 p.1) :=
    contMDiff_curveAt (I := I) (fun y : M ↦ X y) X.contMDiff hcomplete
  have hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ := by
    have hin : ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod I) ∞
        (fun s : ℝ ↦ (s, x)) :=
      contMDiff_id.prodMk contMDiff_const
    simpa only [γ, Function.comp_def] using hflow.comp hin
  have hinner_deriv (s : ℝ) :
      HasDerivAt (fun r : ℝ ↦ g.inner (γ r) (V r) (W r)) 0 s := by
    have hmc := metric_compat_hasDerivAt_inner (I := I) (n := ∞) (by simp)
      g γ V W s hγ
        (differentiableAt_chartRepAt_mfderiv_curveAt (I := I) X hcomplete x v s)
        (differentiableAt_chartRepAt_mfderiv_curveAt (I := I) X hcomplete x w s)
    rw [covDerivAlong_mfderiv_curveAt_eq_zero_of_parallel (I := I) g X hcomplete hpar x v s,
      covDerivAlong_mfderiv_curveAt_eq_zero_of_parallel (I := I) g X hcomplete hpar x w s] at hmc
    simpa only [map_zero, zero_apply, zero_add] using hmc
  have hconst :
      g.inner (γ t) (V t) (W t) = g.inner (γ 0) (V 0) (W 0) :=
    is_const_of_deriv_eq_zero
      (fun s ↦ (hinner_deriv s).differentiableAt)
      (fun s ↦ (hinner_deriv s).deriv) t 0
  have hflow_zero :
      (fun y : M ↦ curveAt (fun z : M ↦ X z) hcomplete y 0) = id := by
    funext y
    exact curveAt_zero (fun z : M ↦ X z) hcomplete y
  have hγ0 : γ 0 = x := curveAt_zero (fun z : M ↦ X z) hcomplete x
  have hV0 : V 0 = v := by
    change mfderiv I I
      (fun y : M ↦ curveAt (fun z : M ↦ X z) hcomplete y 0) x v = v
    rw [hflow_zero, mfderiv_id]
    rfl
  have hW0 : W 0 = w := by
    change mfderiv I I
      (fun y : M ↦ curveAt (fun z : M ↦ X z) hcomplete y 0) x w = w
    rw [hflow_zero, mfderiv_id]
    rfl
  rw [hγ0, hV0, hW0] at hconst
  exact hconst

theorem pullbackMetric_curveAtDiffeomorph_eq_of_parallel
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (hcomplete : ∀ x : M, ∃ γ : ℝ → M,
      γ 0 = x ∧ IsMIntegralCurve γ (fun y : M ↦ X y))
    (hpar : ∀ x : M,
      (LeviCivita (I := I) g).toFun (fun y : M ↦ X y) x = 0)
    (t : ℝ) :
    Diffeomorph.pullbackMetric g
        (curveAtDiffeomorph (I := I) (fun y : M ↦ X y) X.contMDiff hcomplete t) = g := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  rw [Diffeomorph.pullbackMetric_inner]
  change g.inner (curveAt (fun y : M ↦ X y) hcomplete x t)
      (mfderiv I I
        (fun y ↦ curveAt (fun z : M ↦ X z) hcomplete y t) x v)
      (mfderiv I I
        (fun y ↦ curveAt (fun z : M ↦ X z) hcomplete y t) x w) =
    g.inner x v w
  exact inner_mfderiv_curveAt_eq_of_parallel (I := I) g X hcomplete hpar x v w t

end DifferentialGeometry.Geometry.Riemannian
