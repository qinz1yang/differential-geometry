import RicciFlower.RicciFlow.Basic
import RicciFlower.Metric.Scaling

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Definition 11.5: parabolic rescaling

For `R > 0` and center time `τ`, parabolic rescaling uses
`s ↦ τ + s / R` and scales the metric by `R`.
-/

noncomputable section

namespace RicciFlower
namespace RicciFlow

open Bundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M]

/-- Forward parabolic-rescaling time map: old time as a function of rescaled
time. -/
def paraTime (τ R s : Real) : Real :=
  τ + s / R

/-- Inverse parabolic-rescaling time map: rescaled time as a function of old
time. -/
def paraBack (τ R t : Real) : Real :=
  R * (t - τ)

@[simp] theorem paraTime_zero (τ R : Real) :
    paraTime τ R 0 = τ := by
  simp [paraTime]

@[simp] theorem paraBack_self (τ R : Real) :
    paraBack τ R τ = 0 := by
  simp [paraBack]

theorem paraTime_back {τ R t : Real} (hR : R ≠ 0) :
    paraTime τ R (paraBack τ R t) = t := by
  unfold paraTime paraBack
  field_simp [hR]
  ring

theorem paraBack_time {τ R s : Real} (hR : R ≠ 0) :
    paraBack τ R (paraTime τ R s) = s := by
  unfold paraTime paraBack
  field_simp [hR]
  ring

private theorem mul_paraTime_eq {τ R s : Real} (hR : R ≠ 0) :
    R * paraTime τ R s = R * τ + s := by
  unfold paraTime
  field_simp [hR]

/-- Pull back a real time interval along the parabolic-rescaling time map. -/
def paraInterval
    (D : Realized.RealTimeInterval) (τ R : Real) (_hR : 0 < R)
    (hτ : τ ∈ D.carrier) : Realized.RealTimeInterval where
  carrier := {s : Real | paraTime τ R s ∈ D.carrier}
  regular := {s : Real | paraTime τ R s ∈ D.regular}
  initial := 0
  initial_mem := by
    simpa [paraTime] using hτ
  regular_subset := by
    intro s hs
    exact D.regular_subset hs

@[simp] theorem paraInterval_carrier
    (D : Realized.RealTimeInterval) (τ R : Real) (hR : 0 < R)
    (hτ : τ ∈ D.carrier) :
    (paraInterval D τ R hR hτ).carrier =
      {s : Real | paraTime τ R s ∈ D.carrier} := by
  rfl

@[simp] theorem paraInterval_regular
    (D : Realized.RealTimeInterval) (τ R : Real) (hR : 0 < R)
    (hτ : τ ∈ D.carrier) :
    (paraInterval D τ R hR hτ).regular =
      {s : Real | paraTime τ R s ∈ D.regular} := by
  rfl

theorem paraInterval_closedOpen_carrier
    {T τ R : Real} (hT : 0 < T) (hR : 0 < R)
    (hτ : τ ∈ (Realized.RealTimeInterval.closedOpen 0 T hT).carrier) :
    (paraInterval (Realized.RealTimeInterval.closedOpen 0 T hT)
        τ R hR hτ).carrier =
      Set.Ico (-(R * τ)) (R * (T - τ)) := by
  ext s
  constructor
  · intro hs
    rcases hs with ⟨hlo, hhi⟩
    dsimp [paraTime] at hlo hhi
    have heq : R * paraTime τ R s = R * τ + s :=
      mul_paraTime_eq (τ := τ) (R := R) (s := s) (ne_of_gt hR)
    have hlo' : 0 <= R * paraTime τ R s := by
      exact mul_nonneg (le_of_lt hR) hlo
    have hhi' : R * paraTime τ R s < R * T := by
      exact mul_lt_mul_of_pos_left hhi hR
    constructor <;> nlinarith
  · intro hs
    rcases hs with ⟨hlo, hhi⟩
    have heq : R * paraTime τ R s = R * τ + s :=
      mul_paraTime_eq (τ := τ) (R := R) (s := s) (ne_of_gt hR)
    have hlo' : 0 <= R * paraTime τ R s := by
      rw [heq]
      nlinarith
    have hhi' : R * paraTime τ R s < R * T := by
      rw [heq]
      nlinarith
    constructor
    · have hdiv : 0 <= (R * paraTime τ R s) / R := div_nonneg hlo' (le_of_lt hR)
      rwa [mul_div_cancel_left₀ (paraTime τ R s) (ne_of_gt hR)] at hdiv
    · have hdiv : (R * paraTime τ R s) / R < (R * T) / R :=
        div_lt_div_of_pos_right hhi' hR
      rwa [mul_div_cancel_left₀ (paraTime τ R s) (ne_of_gt hR),
        mul_div_cancel_left₀ T (ne_of_gt hR)] at hdiv

theorem paraInterval_closedOpen_regular
    {T τ R : Real} (hT : 0 < T) (hR : 0 < R)
    (hτ : τ ∈ (Realized.RealTimeInterval.closedOpen 0 T hT).carrier) :
    (paraInterval (Realized.RealTimeInterval.closedOpen 0 T hT)
        τ R hR hτ).regular =
      Set.Ioo (-(R * τ)) (R * (T - τ)) := by
  ext s
  constructor
  · intro hs
    rcases hs with ⟨hlo, hhi⟩
    dsimp [paraTime] at hlo hhi
    have heq : R * paraTime τ R s = R * τ + s :=
      mul_paraTime_eq (τ := τ) (R := R) (s := s) (ne_of_gt hR)
    have hlo' : 0 < R * paraTime τ R s := by
      exact mul_pos hR hlo
    have hhi' : R * paraTime τ R s < R * T := by
      exact mul_lt_mul_of_pos_left hhi hR
    constructor <;> nlinarith
  · intro hs
    rcases hs with ⟨hlo, hhi⟩
    have heq : R * paraTime τ R s = R * τ + s :=
      mul_paraTime_eq (τ := τ) (R := R) (s := s) (ne_of_gt hR)
    have hlo' : 0 < R * paraTime τ R s := by
      rw [heq]
      nlinarith
    have hhi' : R * paraTime τ R s < R * T := by
      rw [heq]
      nlinarith
    constructor
    · have hdiv : 0 < (R * paraTime τ R s) / R := div_pos hlo' hR
      rwa [mul_div_cancel_left₀ (paraTime τ R s) (ne_of_gt hR)] at hdiv
    · have hdiv : (R * paraTime τ R s) / R < (R * T) / R :=
        div_lt_div_of_pos_right hhi' hR
      rwa [mul_div_cancel_left₀ (paraTime τ R s) (ne_of_gt hR),
        mul_div_cancel_left₀ T (ne_of_gt hR)] at hdiv

/-- Rescale a real-time Ricci-flow family by pulling time back via `paraTime`
and scaling the metric by `R`. -/
def paraFamily
    (G : SolutionFamily (I := I) (M := M)) (τ R : Real) (hR : 0 < R) :
    SolutionFamily (I := I) (M := M) where
  metric s := scaleMetric (I := I) R hR (G.metric (paraTime τ R s))

/-- Inverse rescaling of a real-time family. -/
def paraBackFamily
    (G : SolutionFamily (I := I) (M := M)) (τ R : Real) (hR : 0 < R) :
    SolutionFamily (I := I) (M := M) where
  metric t := scaleMetric (I := I) R⁻¹ (inv_pos.mpr hR)
    (G.metric (paraBack τ R t))

/-- The interval-indexed parabolically rescaled solution candidate. -/
def paraSolution
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (τ R : Real) (hR : 0 < R) (hτ : τ ∈ D.carrier) :
    SolutionOn (I := I) (M := M) (paraInterval D τ R hR hτ) where
  base := paraFamily (I := I) S.base τ R hR

@[simp] theorem paraSolution_metric
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (τ R : Real) (hR : 0 < R) (hτ : τ ∈ D.carrier) :
    (paraSolution (I := I) S τ R hR hτ).base.metric =
      fun s => scaleMetric (I := I) R hR (S.base.metric (paraTime τ R s)) := by
  rfl

@[simp] theorem paraSolution_connection
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (τ R : Real) (hR : 0 < R) (hτ : τ ∈ D.carrier) :
    (paraSolution (I := I) S τ R hR hτ).base.connection =
      fun s => S.base.connection (paraTime τ R s) := by
  sorry

@[simp] theorem paraSolution_ricci
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (τ R : Real) (hR : 0 < R) (hτ : τ ∈ D.carrier) :
    (paraSolution (I := I) S τ R hR hτ).base.ricci =
      fun s => S.base.ricci (paraTime τ R s) := by
  sorry

/-- Time smoothness of the rescaled metric family.  This is the exact
regularity bridge: constant scaling plus affine time pullback preserves metric
coefficient smoothness on the pulled-back interval. -/
theorem metricFamilySmooth_para
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (τ R : Real) (hR : 0 < R) (hτ : τ ∈ D.carrier) :
    Realized.MetricFamilySmoothOn (I := I) (M := M)
      (paraInterval D τ R hR hτ)
      (paraSolution (I := I) S τ R hR hτ).family := by
  intro x X Y
  have hOld := hS.smoothMetric x X Y
  have haff_global : ContDiff Real ⊤ (fun s : Real => paraTime τ R s) := by
    unfold paraTime
    exact contDiff_const.add (contDiff_id.div_const R)
  have hmaps :
      Set.MapsTo (fun s : Real => paraTime τ R s)
        (paraInterval D τ R hR hτ).carrier D.carrier := by
    intro s hs
    exact hs
  have hcomp :
      ContDiffOn Real ⊤
        (fun s : Real => (S.base.metric (paraTime τ R s)).inner x X Y)
        (paraInterval D τ R hR hτ).carrier := by
    simpa [Function.comp_def] using
      hOld.comp haff_global.contDiffOn hmaps
  simpa [SolutionOn.family, paraSolution, paraFamily, scaleMetric_inner, smul_eq_mul]
    using ContDiffOn.const_smul R hcomp

/-- Connection smoothness is preserved by the affine time pullback. -/
theorem connectionFamilySmooth_para
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (τ R : Real) (hR : 0 < R) (hτ : τ ∈ D.carrier) :
    RicciFlower.Connection.ConnectionFamilySmoothOn (I := I) (M := M)
      (paraSolution (I := I) S τ R hR hτ).family := by
  sorry

/-- Levi-Civita-ness is preserved under parabolic rescaling. -/
theorem leviCivita_para
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (τ R : Real) (hR : 0 < R) (hτ : τ ∈ D.carrier) :
    RicciFlower.LeviCivita.IsLeviCivitaFamilyOn (I := I)
      (paraSolution (I := I) S τ R hR hτ).family := by
  sorry

/-- Metric evolution equation under parabolic rescaling. -/
theorem metricVariation_para
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (τ R : Real) (hR : 0 < R) (hτ : τ ∈ D.carrier) :
    MetricVariationEquationOn (I := I)
      (paraSolution (I := I) S τ R hR hτ) := by
  sorry

/-- Parabolic rescaling sends Ricci-flow solutions to Ricci-flow solutions. -/
theorem paraSol
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (τ R : Real) (hR : 0 < R) (hτ : τ ∈ D.carrier) :
    IsSolutionOn (I := I) (paraSolution (I := I) S τ R hR hτ) where
  smoothMetric := metricFamilySmooth_para (I := I) S hS τ R hR hτ
  smoothConnection := connectionFamilySmooth_para (I := I) S hS τ R hR hτ
  equation := metricVariation_para (I := I) S hS τ R hR hτ

theorem paraBack_para_metric
    (G : SolutionFamily (I := I) (M := M))
    (τ R : Real) (hR : 0 < R) (t : Real) :
    ((paraBackFamily (I := I) (paraFamily (I := I) G τ R hR)
      τ R hR).metric t).inner = (G.metric t).inner := by
  funext x
  ext v w
  simp only [paraBackFamily, paraFamily, scaleMetric_inner]
  rw [paraTime_back (τ := τ) (R := R) (t := t) (ne_of_gt hR)]
  rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hR), one_mul]

theorem paraBack_para_connection
    (G : SolutionFamily (I := I) (M := M))
    (τ R : Real) (hR : 0 < R) (t : Real) :
    (paraBackFamily (I := I) (paraFamily (I := I) G τ R hR)
      τ R hR).connection t = G.connection t := by
  sorry

theorem paraBack_para_ricci
    (G : SolutionFamily (I := I) (M := M))
    (τ R : Real) (hR : 0 < R) (t : Real) :
    (paraBackFamily (I := I) (paraFamily (I := I) G τ R hR)
      τ R hR).ricci t = G.ricci t := by
  sorry

theorem para_paraBack_metric
    (G : SolutionFamily (I := I) (M := M))
    (τ R : Real) (hR : 0 < R) (s : Real) :
    ((paraFamily (I := I) (paraBackFamily (I := I) G τ R hR)
      τ R hR).metric s).inner = (G.metric s).inner := by
  funext x
  ext v w
  simp only [paraFamily, paraBackFamily, scaleMetric_inner]
  rw [paraBack_time (τ := τ) (R := R) (s := s) (ne_of_gt hR)]
  rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hR), one_mul]

theorem para_paraBack_connection
    (G : SolutionFamily (I := I) (M := M))
    (τ R : Real) (hR : 0 < R) (s : Real) :
    (paraFamily (I := I) (paraBackFamily (I := I) G τ R hR)
      τ R hR).connection s = G.connection s := by
  sorry

theorem para_paraBack_ricci
    (G : SolutionFamily (I := I) (M := M))
    (τ R : Real) (hR : 0 < R) (s : Real) :
    (paraFamily (I := I) (paraBackFamily (I := I) G τ R hR)
      τ R hR).ricci s = G.ricci s := by
  sorry

/-- Scalar curvature display under parabolic rescaling. -/
def ParaScalarDisplay
    (scalar scalarR : Real -> M -> Real) (τ R : Real) : Prop :=
  forall s x, scalarR s x = R⁻¹ * scalar (paraTime τ R s) x

/-- Trace-free Ricci norm-squared display under parabolic rescaling. -/
def ParaTracefreeNormSqDisplay
    (q qR : Real -> M -> Real) (τ R : Real) : Prop :=
  forall s x, qR s x = (R⁻¹) ^ 2 * q (paraTime τ R s) x

/-- The scale-invariant ratio `|Ric°|² / R²` is unchanged by parabolic
rescaling, assuming the displayed scalar and trace-free norm scaling laws. -/
theorem para_tracefree_ratio_invariant
    {scalar scalarR q qR : Real -> M -> Real}
    {τ R : Real} (hR : 0 < R)
    (hscalar : ParaScalarDisplay (M := M) scalar scalarR τ R)
    (hq : ParaTracefreeNormSqDisplay (M := M) q qR τ R)
    (s : Real) (x : M) :
    qR s x / (scalarR s x) ^ 2 =
      q (paraTime τ R s) x / (scalar (paraTime τ R s) x) ^ 2 := by
  rw [hq s x, hscalar s x]
  field_simp [ne_of_gt hR]

end RicciFlow
end RicciFlower
