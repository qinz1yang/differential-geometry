import DifferentialGeometry.Geometry.Connection.MetricCompatibility.Defs
import DifferentialGeometry.Geometry.Connection.LeviCivita.Basic
import DifferentialGeometry.Bundle.PartialMfderiv.Basic
open DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry

open Bundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private theorem mdifferentiableAt_metric_inner
    (g : SmoothRiemannianMetric I M)
    {X Y : (p : M) -> TangentSpace I p} {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    MDiffAt (fun y : M => g.inner y (X y) (Y y)) x := by
  have hg :
      MDifferentiableAt I
        (I.prod 𝓘(Real, E →L[Real] E →L[Real] Real))
        (fun y : M =>
          TotalSpace.mk' (E →L[Real] E →L[Real] Real)
            (E := fun y : M =>
              TangentSpace I y →L[Real] TangentSpace I y →L[Real] Real)
            y (g.inner y)) x :=
    g.contMDiff.mdifferentiableAt (by simp)
  have htotal :
      MDifferentiableAt I (I.prod 𝓘(Real, Real))
        (fun y : M =>
          TotalSpace.mk' Real (E := Bundle.Trivial M Real) y
            (g.inner y (X y) (Y y))) x := by
    exact MDifferentiableAt.clm_bundle_apply₂
      (F₁ := E) (F₂ := E) hg hX hY
  rw [mdifferentiableAt_totalSpace] at htotal
  exact htotal.2

private theorem contMDiff_scaleMetric_inner_section
    (c : Real) (g : SmoothRiemannianMetric I M) :
    ContMDiff I
      (I.prod 𝓘(Real, E →L[Real] E →L[Real] Real)) ∞
      (fun y : M =>
        TotalSpace.mk' (E →L[Real] E →L[Real] Real)
          (E := fun y : M =>
            TangentSpace I y →L[Real] TangentSpace I y →L[Real] Real)
          y (c • g.inner y)) := by
  simpa only [Pi.smul_apply] using
    (g.contMDiff.const_smul_section (I := I)
      (F := E →L[Real] E →L[Real] Real)
      (V := fun y : M =>
        TangentSpace I y →L[Real] TangentSpace I y →L[Real] Real)
      (a := c))


def scaleMetric (c : Real) (hc : 0 < c)
    (g : SmoothRiemannianMetric I M) : SmoothRiemannianMetric I M where
  inner x := c • g.inner x
  symm x v w := by
    simp [smul_apply, smul_eq_mul, g.symm x v w]
  pos x v hv := by
    simpa [smul_apply, smul_eq_mul] using
      mul_pos hc (g.pos x v hv)
  isVonNBounded x := by
    by_cases hlarge : 1 <= c
    · refine (g.isVonNBounded x).subset ?_
      intro v hv
      simp only [Set.mem_ofPred_eq] at hv ⊢
      by_cases hv0 : v = 0
      · simp [hv0]
      · have hpos := g.pos x v hv0
        simp only [smul_apply, smul_eq_mul] at hv
        nlinarith
    · have hsmall : c < 1 := lt_of_not_ge hlarge
      let L : TangentSpace I x →L[Real] TangentSpace I x :=
        c⁻¹ • (1 : TangentSpace I x →L[Real] TangentSpace I x)
      refine ((g.isVonNBounded x).image L).subset ?_
      intro v hv
      simp only [Set.mem_ofPred_eq] at hv
      refine ⟨c • v, ?_, ?_⟩
      · simp only [Set.mem_ofPred_eq]
        simp only [smul_apply, smul_eq_mul] at hv
        have hscale :
            g.inner x (c • v) (c • v) =
              c * (c * g.inner x v v) := by
          simp [smul_eq_mul]
        rw [hscale]
        nlinarith
      · calc
          L (c • v) = c⁻¹ • (c • v) := by
            simp [L, smul_smul, mul_comm]
          _ = v := by
            rw [smul_smul, inv_mul_cancel₀ (ne_of_gt hc), one_smul]
  contMDiff := contMDiff_scaleMetric_inner_section (I := I) c g

@[simp] theorem scaleMetric_inner
    (c : Real) (hc : 0 < c) (g : SmoothRiemannianMetric I M)
    (x : M) (v w : TangentSpace I x) :
    (scaleMetric (I := I) c hc g).inner x v w =
      c * g.inner x v w := by
  rfl


theorem scaleMetric_one
    (g : SmoothRiemannianMetric I M) :
    (scaleMetric (I := I) (1 : Real) zero_lt_one g).inner = g.inner := by
  funext x
  ext v w
  simp [scaleMetric_inner]


theorem scaleMetric_mul
    (a b : Real) (ha : 0 < a) (hb : 0 < b)
    (g : SmoothRiemannianMetric I M) :
    (scaleMetric (I := I) a ha (scaleMetric (I := I) b hb g)).inner =
      (scaleMetric (I := I) (a * b) (mul_pos ha hb) g).inner := by
  funext x
  ext v w
  simp [scaleMetric_inner, mul_assoc]

theorem scaleMetric_inv_mul
    (c : Real) (hc : 0 < c) (g : SmoothRiemannianMetric I M) :
    (scaleMetric (I := I) c⁻¹ (inv_pos.mpr hc)
      (scaleMetric (I := I) c hc g)).inner = g.inner := by
  funext x
  ext v w
  simp only [scaleMetric_inner]
  rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hc), one_mul]

theorem mc_scaleMetric
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {g : SmoothRiemannianMetric I M}
    {c : Real} (hc : 0 < c)
    (hmc : DifferentialGeometry.Geometry.Connection.IsMetricCompatible (I := I) cov g) :
    DifferentialGeometry.Geometry.Connection.IsMetricCompatible (I := I) cov
      (scaleMetric (I := I) c hc g) := by
  change DifferentialGeometry.Geometry.Connection.IsMetricCompatibleOn cov.toFun
    (scaleMetric (I := I) c hc g) Set.univ
  intro Y Z x hY hZ _ v
  let f : M -> Real := fun y : M => g.inner y (Y y) (Z y)
  have hf : MDiffAt f x :=
    mdifferentiableAt_metric_inner (I := I) g hY hZ
  have hderivMap : mvfderiv (I := I) (c • f) x = c • mvfderiv (I := I) f x := by
    change mvfderiv (I := I) (fun y : M => c * f y) x = c • mvfderiv (I := I) f x
    exact mvfderiv_const_mul I c hf
  have hcompat :=
    DifferentialGeometry.Geometry.Connection.IsMetricCompatible.apply hmc hY hZ v
  simp only [scaleMetric_inner]
  change
    mvfderiv (I := I) (c • f) x v =
      c * g.inner x (cov Y x v) (Z x) +
        c * g.inner x (Y x) (cov Z x v)
  have hcompat' :
      mvfderiv (I := I) f x v =
        g.inner x (cov Y x v) (Z x) +
          g.inner x (Y x) (cov Z x v) := by
    change mvfderiv (I := I) f x v = _ at hcompat
    exact hcompat
  rw [hderivMap, smul_apply, hcompat']
  rw [smul_eq_mul]
  ring

theorem lc_scaleMetric
    [FiniteDimensional Real E] [CompleteSpace E]
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {g : SmoothRiemannianMetric I M}
    {c : Real} (hc : 0 < c)
    (hLC : DifferentialGeometry.Geometry.Connection.IsLeviCivita (I := I) cov g) :
    DifferentialGeometry.Geometry.Connection.IsLeviCivita (I := I) cov
      (scaleMetric (I := I) c hc g) :=
  ⟨mc_scaleMetric (I := I) hc hLC.1, hLC.2⟩

end DifferentialGeometry
