import RicciFlower.Connection.MetricCompatibility
import RicciFlower.LeviCivita.Basic

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Constant scaling of smooth Riemannian metrics

This file contains the metric-side algebra needed for parabolic rescaling.
The scaling is by a positive constant and keeps the same tangent bundle.
-/

noncomputable section

namespace RicciFlower

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

set_option synthInstance.maxHeartbeats 80000 in
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

/-- Scale a smooth Riemannian metric by a positive constant. -/
def scaleMetric (c : Real) (hc : 0 < c)
    (g : SmoothRiemannianMetric I M) : SmoothRiemannianMetric I M where
  inner x := c • g.inner x
  symm x v w := by
    simp [ContinuousLinearMap.smul_apply, smul_eq_mul, g.symm x v w]
  pos x v hv := by
    simpa [ContinuousLinearMap.smul_apply, smul_eq_mul] using
      mul_pos hc (g.pos x v hv)
  isVonNBounded x := by
    by_cases hlarge : 1 <= c
    · refine (g.isVonNBounded x).subset ?_
      intro v hv
      simp only [Set.mem_setOf_eq] at hv ⊢
      by_cases hv0 : v = 0
      · simp [hv0]
      · have hpos := g.pos x v hv0
        simp only [ContinuousLinearMap.smul_apply, smul_eq_mul] at hv
        nlinarith
    · have hsmall : c < 1 := lt_of_not_ge hlarge
      let L : TangentSpace I x →L[Real] TangentSpace I x :=
        c⁻¹ • (1 : TangentSpace I x →L[Real] TangentSpace I x)
      refine ((g.isVonNBounded x).image L).subset ?_
      intro v hv
      simp only [Set.mem_setOf_eq] at hv
      refine ⟨c • v, ?_, ?_⟩
      · simp only [Set.mem_setOf_eq]
        simp only [ContinuousLinearMap.smul_apply, smul_eq_mul] at hv
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

/-- Scaling by `1` is extensionally the identity on inner products. -/
theorem scaleMetric_one
    (g : SmoothRiemannianMetric I M) :
    (scaleMetric (I := I) (1 : Real) zero_lt_one g).inner = g.inner := by
  funext x
  ext v w
  simp [scaleMetric_inner]

/-- Successive positive scalings multiply, extensionally on inner products. -/
theorem scaleMetric_mul
    (a b : Real) (ha : 0 < a) (hb : 0 < b)
    (g : SmoothRiemannianMetric I M) :
    (scaleMetric (I := I) a ha (scaleMetric (I := I) b hb g)).inner =
      (scaleMetric (I := I) (a * b) (mul_pos ha hb) g).inner := by
  funext x
  ext v w
  simp [scaleMetric_inner, mul_assoc]

/-- Scaling by `c⁻¹` after scaling by `c` returns the original metric,
extensionally on inner products. -/
theorem scaleMetric_inv_mul
    (c : Real) (hc : 0 < c) (g : SmoothRiemannianMetric I M) :
    (scaleMetric (I := I) c⁻¹ (inv_pos.mpr hc)
      (scaleMetric (I := I) c hc g)).inner = g.inner := by
  funext x
  ext v w
  simp only [scaleMetric_inner]
  rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hc), one_mul]

/-- Metric compatibility is preserved when the metric is scaled by a positive
constant and the connection is unchanged. -/
theorem mc_scaleMetric
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {g : SmoothRiemannianMetric I M}
    {c : Real} (hc : 0 < c)
    (hmc : RicciFlower.Connection.IsMetricCompatible (I := I) cov g) :
    RicciFlower.Connection.IsMetricCompatible (I := I) cov
      (scaleMetric (I := I) c hc g) := by
  intro x X Y Z hX hY hZ
  let f : M -> Real := fun y : M => g.inner y (Y y) (Z y)
  have hf : MDiffAt f x :=
    mdifferentiableAt_metric_inner (I := I) g hY hZ
  set f' : TangentSpace I x →L[Real] Real :=
    mfderiv I 𝓘(Real, Real) f x
  set cf' : TangentSpace I x →L[Real] Real :=
    mfderiv I 𝓘(Real, Real) (c • f) x
  have hderivMap :=
    const_smul_mfderiv (I := I)
      (f := f) (z := x) hf c
  have hderivMap' : cf' = c • f' := by
    simpa [f', cf'] using hderivMap
  have hcompat := hmc x X Y Z hX hY hZ
  simp only [scaleMetric_inner]
  change
    cf' (X x) =
      c * g.inner x (cov Y x (X x)) (Z x) +
        c * g.inner x (Y x) (cov Z x (X x))
  have hcompat' :
      f' (X x) =
        g.inner x (cov Y x (X x)) (Z x) +
          g.inner x (Y x) (cov Z x (X x)) := by
    simpa [f, f'] using hcompat
  rw [hderivMap', ContinuousLinearMap.smul_apply, hcompat']
  rw [smul_eq_mul]
  ring

/-- Levi-Civita-ness is preserved when the metric is scaled by a positive
constant and the connection is unchanged. -/
theorem lc_scaleMetric
    [FiniteDimensional Real E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {g : SmoothRiemannianMetric I M}
    {c : Real} (hc : 0 < c)
    (hLC : RicciFlower.LeviCivita.IsLeviCivita (I := I) cov g) :
    RicciFlower.LeviCivita.IsLeviCivita (I := I) cov
      (scaleMetric (I := I) c hc g) :=
  ⟨mc_scaleMetric (I := I) hc hLC.1, hLC.2⟩

end RicciFlower
