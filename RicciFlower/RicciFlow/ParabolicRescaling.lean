import RicciFlower.RicciFlow.Basic
import RicciFlower.LeviCivita.Scaling
import RicciFlower.Operators.Scaling
import RicciFlower.Tensor.RSTensor.Tensor0SRiemannian.Scaling

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

open Bundle Tensor0SBundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
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
  regular_mem_nhds := by
    intro s hs
    have hcont : ContinuousAt (fun r : Real => paraTime τ R r) s := by
      unfold paraTime
      fun_prop
    simpa [Set.preimage] using hcont.preimage_mem_nhds (D.regular_mem_nhds hs)

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
  funext s
  simp [paraSolution, paraFamily, SolutionFamily.connection,
    LeviCivita.lcConn_scaleMetric]

@[simp] theorem paraSolution_ricci
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (τ R : Real) (hR : 0 < R) (hτ : τ ∈ D.carrier) :
    (paraSolution (I := I) S τ R hR hτ).base.ricci =
      fun s => S.base.ricci (paraTime τ R s) := by
  funext s
  simp [paraSolution, paraFamily, SolutionFamily.ricci, metricRicci,
    Curvature.metricRicci, Curvature.metricCov, LeviCivita.lcConn_scaleMetric]

private theorem metricRm04_scaleMetric
    (c : Real) (hc : 0 < c) (g : SmoothRiemannianMetric I M) (x : M) :
    Curvature.metricRm04 (I := I) (M := M) (scaleMetric (I := I) c hc g) x =
      c • Curvature.metricRm04 (I := I) (M := M) g x := by
  ext v
  have hv :
      v = Curvature.vec4 (I := I) (v 0) (v 1) (v 2) (v 3) := by
    funext i
    fin_cases i <;> simp [Curvature.vec4]
  rw [hv]
  simp [Curvature.metricRm04, Curvature.metricCov, scaleMetric_inner,
    LeviCivita.lcConn_scaleMetric, smul_eq_mul]

@[simp] theorem paraSolution_rm04
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (τ R : Real) (hR : 0 < R) (hτ : τ ∈ D.carrier)
    (s : Real) (x : M) :
    (paraSolution (I := I) S τ R hR hτ).base.rm04 s x =
      R • S.base.rm04 (paraTime τ R s) x := by
  simpa [paraSolution, paraFamily, SolutionFamily.rm04] using
    metricRm04_scaleMetric (I := I) R hR (S.base.metric (paraTime τ R s)) x

@[simp] private theorem paraNablaRic_eq
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (τ R : Real) (hR : 0 < R) (hτ : τ ∈ D.carrier)
    (s : Real) (x : M) :
    totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        2 ((paraSolution (I := I) S τ R hR hτ).family.connection s)
        ((paraSolution (I := I) S τ R hR hτ).ricci s) x =
      totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        2 (S.family.connection (paraTime τ R s))
        (S.ricci (paraTime τ R s)) x := by
  refine totalNabla0SFun_congr (𝕜 := Real) (E := E) (H := H)
    (I := I) (M := M) 2 ?_ ?_ x
  · have h := congrFun (paraSolution_connection (I := I) S τ R hR hτ) s
    simp [SolutionOn.family] at h ⊢
  · have h := congrFun (paraSolution_ricci (I := I) S τ R hR hτ) s
    simp [SolutionOn.ricci] at h ⊢

private theorem metricTensorField_scaleMetric
    (c : Real) (hc : 0 < c) (g : SmoothRiemannianMetric I M) (x : M) :
    metricTensorField (I := I) (scaleMetric (I := I) c hc g) x =
      c • metricTensorField (I := I) g x := by
  ext v
  simp [metricTensorField_apply, scaleMetric_inner, smul_eq_mul]

private theorem metricTracePair0SAt_scaleMetric
    (c : Real) (hc : 0 < c) (g : SmoothRiemannianMetric I M)
    {x : M} (B : Tensor0SSpace (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 2 x) :
    Realized.metricTracePair0SAt (I := I) (scaleMetric (I := I) c hc g) B =
      c⁻¹ * Realized.metricTracePair0SAt (I := I) g B := by
  classical
  let basis : Module.Basis (Coordinates.CoordinateIdx (𝕜 := Real) E) Real
      (TangentSpace I x) := Coordinates.coordinateFrameAt_toBasis (I := I) x
  let gInv : Coordinates.CoordinateIdx (𝕜 := Real) E ->
      Coordinates.CoordinateIdx (𝕜 := Real) E -> Real :=
    fun k l =>
      Coordinates.inverseMetricFlatModelInChart_component (I := I) g x k l
        (extChartAt I x x)
  have hinv : MetricInverseInBasis (I := I) g x basis gInv :=
    Coordinates.inverseMetricFlatModelInChart_metricInverseInBasis_center (I := I) g x
  have hinvScale :
      MetricInverseInBasis (I := I) (scaleMetric (I := I) c hc g) x basis
        (fun i j => c⁻¹ * gInv i j) :=
    metricInvBasis_scale (I := I) c hc g basis gInv hinv
  rw [Realized.metricTracePair0SAt_eq_sum_basis (I := I)
      (scaleMetric (I := I) c hc g) basis (fun i j => c⁻¹ * gInv i j) hinvScale,
    Realized.metricTracePair0SAt_eq_sum_basis (I := I) g basis gInv hinv]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  apply Finset.sum_congr rfl
  intro j _hj
  ring

@[simp] theorem paraSolution_scalar
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (τ R : Real) (hR : 0 < R) (hτ : τ ∈ D.carrier) :
    (paraSolution (I := I) S τ R hR hτ).scalar =
      fun s x => R⁻¹ * S.scalar (paraTime τ R s) x := by
  funext s x
  simp [SolutionOn.scalar, SolutionFamily.scalar_apply, paraSolution, paraFamily,
    SolutionFamily.ricciAt, metricRicciAt, Curvature.metricRicciAt,
    Curvature.metricCov, LeviCivita.lcConn_scaleMetric,
    metricTracePair0SAt_scaleMetric]

@[simp] theorem paraSolution_ricciNorm
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (τ R : Real) (hR : 0 < R) (hτ : τ ∈ D.carrier) :
    ricciNorm (I := I) (paraSolution (I := I) S τ R hR hτ) =
      fun s x => R⁻¹ * R⁻¹ * ricciNorm (I := I) S (paraTime τ R s) x := by
  funext s x
  have hRic :
      (paraSolution (I := I) S τ R hR hτ).ricci s x =
        S.ricci (paraTime τ R s) x := by
    have h := paraSolution_ricci (I := I) S τ R hR hτ
    change ((paraSolution (I := I) S τ R hR hτ).base.ricci s) x =
      (S.base.ricci (paraTime τ R s)) x
    exact congrArg (fun A => A x) (congrFun h s)
  rw [ricciNorm, hRic]
  simpa [SolutionOn.family, paraSolution, paraFamily, ricciNorm, mul_assoc] using
    (normSq0S_two_scale (I := I) R hR (S.family.metric (paraTime τ R s))
      (x := x) (A := S.ricci (paraTime τ R s) x))

private theorem paraRicciNormGrad_eq
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (τ R : Real) (hR : 0 < R) (hτ : τ ∈ D.carrier)
    {s : Real} (hs : s ∈ (paraInterval D τ R hR hτ).carrier) (x : M) :
    Realized.gradientFun (I := I)
        ((paraSolution (I := I) S τ R hR hτ).family.metric s)
        (ricciNorm (I := I) (paraSolution (I := I) S τ R hR hτ) s) x =
      (R⁻¹ * R⁻¹ * R⁻¹) •
        Realized.gradientFun (I := I) (S.family.metric (paraTime τ R s))
          (ricciNorm (I := I) S (paraTime τ R s)) x := by
  have hdiff :
      MDifferentiableAt I 𝓘(Real, Real)
        (ricciNorm (I := I) S (paraTime τ R s)) x :=
    hS.ricciNormSpace (paraTime τ R s) hs x
  calc
    Realized.gradientFun (I := I)
        ((paraSolution (I := I) S τ R hR hτ).family.metric s)
        (ricciNorm (I := I) (paraSolution (I := I) S τ R hR hτ) s) x =
        Realized.gradientFun (I := I)
          (scaleMetric (I := I) R hR (S.family.metric (paraTime τ R s)))
          ((R⁻¹ * R⁻¹) • ricciNorm (I := I) S (paraTime τ R s)) x := by
          have hfun :
              ricciNorm (I := I) (paraSolution (I := I) S τ R hR hτ) s =
                (R⁻¹ * R⁻¹) • ricciNorm (I := I) S (paraTime τ R s) := by
            funext y
            have h := congrFun
              (congrFun (paraSolution_ricciNorm (I := I) S τ R hR hτ) s) y
            rw [h]
            simp [Pi.smul_apply, smul_eq_mul, mul_assoc]
          rw [hfun]
          simp [SolutionOn.family, paraSolution, paraFamily]
    _ =
        R⁻¹ • Realized.gradientFun (I := I) (S.family.metric (paraTime τ R s))
          ((R⁻¹ * R⁻¹) • ricciNorm (I := I) S (paraTime τ R s)) x := by
          rw [Realized.gradientFun_scale]
    _ =
        R⁻¹ • ((R⁻¹ * R⁻¹) •
          Realized.gradientFun (I := I) (S.family.metric (paraTime τ R s))
            (ricciNorm (I := I) S (paraTime τ R s)) x) := by
          rw [Realized.gradientFun_const_smul (I := I)
            (S.family.metric (paraTime τ R s)) (a := R⁻¹ * R⁻¹) hdiff]
    _ =
        (R⁻¹ * R⁻¹ * R⁻¹) •
          Realized.gradientFun (I := I) (S.family.metric (paraTime τ R s))
            (ricciNorm (I := I) S (paraTime τ R s)) x := by
          simp [smul_smul, mul_comm]

private theorem lcConnectionSmooth
    (g : SmoothRiemannianMetric I M) :
    CovariantDerivative.ContMDiffCovariantDerivative
      (LeviCivita.leviCivitaConnectionOfMetric (I := I) g) ∞ := by
  exact
    ⟨LeviCivita.leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
      (I := I) g (u := Set.univ) isOpen_univ⟩

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
  constructor
  · intro x X Y
    have hOld := hS.smoothMetric.coeff x X Y
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
  · have hmaps :
        Set.MapsTo (fun s : Real => paraTime τ R s)
          (paraInterval D τ R hR hτ).carrier D.carrier := by
      intro s hs
      exact hs
    have htime : Continuous (fun s : Real => paraTime τ R s) := by
      unfold paraTime
      exact continuous_const.add (continuous_id.div_const R)
    have hcomp :=
      Realized.Tensor0SFamilyContinuousOnSet.comp_time (I := I) (M := M)
        hS.smoothMetric.metricTensor_cont htime hmaps
    have hscale :=
      Realized.Tensor0SFamilyContinuousOnSet.const_smul (I := I) (M := M)
        R hcomp
    simpa [SolutionOn.family, paraSolution, paraFamily, metricTensorField_scaleMetric]
      using hscale
  · intro Idx _ frame u hframe i j
    have hOld :
        ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ⊤
          (fun p : Real × M =>
            (S.family.metric p.1).inner p.2 (frame i p.2) (frame j p.2))
          (D.carrier ×ˢ u) :=
      hS.smoothMetric.frameCompSmooth frame hframe i j
    have htime :
        ContMDiff (𝓘(Real, Real).prod I) 𝓘(Real, Real) ⊤
          (fun p : Real × M => paraTime τ R p.1) := by
      unfold paraTime
      exact contMDiff_const.add (contMDiff_fst.div_const R)
    have hmapSmooth :
        ContMDiff (𝓘(Real, Real).prod I) (𝓘(Real, Real).prod I) ⊤
          (fun p : Real × M => (paraTime τ R p.1, p.2)) :=
      htime.prodMk contMDiff_snd
    have hmaps :
        Set.MapsTo (fun p : Real × M => (paraTime τ R p.1, p.2))
          ((paraInterval D τ R hR hτ).carrier ×ˢ u) (D.carrier ×ˢ u) := by
      intro p hp
      exact ⟨hp.1, hp.2⟩
    have hcomp :
        ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ⊤
          (fun p : Real × M =>
            (S.base.metric (paraTime τ R p.1)).inner p.2
              (frame i p.2) (frame j p.2))
          ((paraInterval D τ R hR hτ).carrier ×ˢ u) := by
      simpa [SolutionOn.family, Function.comp_def] using
        hOld.comp hmapSmooth.contMDiffOn hmaps
    have hscale :
        ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ⊤
          (fun p : Real × M =>
            R * (S.base.metric (paraTime τ R p.1)).inner p.2
              (frame i p.2) (frame j p.2))
          ((paraInterval D τ R hR hτ).carrier ×ˢ u) :=
      (contMDiffOn_const (c := R)).mul hcomp
    simpa [SolutionOn.family, paraSolution, paraFamily, scaleMetric_inner,
      smul_eq_mul] using hscale

/-- Connection smoothness is preserved by the affine time pullback. -/
theorem connectionFamilySmooth_para
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (_hS : IsSolutionOn (I := I) S)
    (τ R : Real) (hR : 0 < R) (hτ : τ ∈ D.carrier) :
    RicciFlower.Connection.ConnectionFamilySmoothOn (I := I) (M := M)
      (paraSolution (I := I) S τ R hR hτ).family := by
  intro t
  simpa [SolutionOn.family, paraSolution, paraFamily, SolutionFamily.connection,
    Realized.RealizedMetricFamilyOn.connectionAt]
    using lcConnectionSmooth (I := I)
      ((paraSolution (I := I) S τ R hR hτ).base.metric (t : Real))

/-- Levi-Civita-ness is preserved under parabolic rescaling. -/
theorem leviCivita_para
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (_hS : IsSolutionOn (I := I) S)
    (τ R : Real) (hR : 0 < R) (hτ : τ ∈ D.carrier) :
    RicciFlower.LeviCivita.IsLeviCivitaFamilyOn (I := I)
      (paraSolution (I := I) S τ R hR hτ).family := by
  constructor
  · intro t
    exact (paraSolution (I := I) S τ R hR hτ).metricCompatible t
  · intro t
    simpa [SolutionOn.family, paraSolution, paraFamily, SolutionFamily.connection,
      Realized.RealizedMetricFamilyOn.connectionAt]
      using LeviCivita.leviCivitaConnectionOfMetric_isTorsionFree
        (I := I) ((paraSolution (I := I) S τ R hR hτ).base.metric (t : Real))

/-- Metric evolution equation under parabolic rescaling. -/
theorem metricVariation_para
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (τ R : Real) (hR : 0 < R) (hτ : τ ∈ D.carrier) :
    MetricVariationEquationOn (I := I)
      (paraSolution (I := I) S τ R hR hτ) := by
  intro t x X Y
  let tOld : Realized.RealTimeInterval.RegularTime D :=
    ⟨paraTime τ R (t : Real), t.2⟩
  have hOld := hS.equation tOld x X Y
  have htime :
      HasDerivWithinAt (fun s : Real => paraTime τ R s) R⁻¹
        (paraInterval D τ R hR hτ).carrier (t : Real) := by
    simpa [paraTime, one_div] using
      (((hasDerivWithinAt_id (t : Real)
        (paraInterval D τ R hR hτ).carrier).div_const R).const_add τ)
  have hmaps :
      Set.MapsTo (fun s : Real => paraTime τ R s)
        (paraInterval D τ R hR hτ).carrier D.carrier := by
    intro s hs
    exact hs
  have hcomp := hOld.comp (x := (t : Real)) htime hmaps
  have hscaled := hcomp.const_mul R
  simpa [MetricVariationEquationOn, Realized.MetricVariationEquationOn,
    SolutionOn.family, paraSolution, paraFamily, RicciAtFamily.toTensorField,
    SolutionFamily.ricciAt, metricRicciAt, Curvature.metricRicciAt,
    Curvature.metricCov, scaleMetric_inner, LeviCivita.lcConn_scaleMetric,
    tOld]
    using
      (hscaled.congr_deriv (by
        simp [tOld, SolutionFamily.ricciAt, metricRicciAt, Curvature.metricRicciAt,
          Curvature.metricCov]
        field_simp [ne_of_gt hR]))

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
  scalarCont := by
    intro p
    have hOld := hS.scalarCont (paraTime τ R p.1, p.2)
    have htime : ContinuousAt (fun q : Real × M => paraTime τ R q.1) p := by
      unfold paraTime
      exact continuousAt_const.add (continuousAt_fst.div_const R)
    have hmap : ContinuousAt (fun q : Real × M => (paraTime τ R q.1, q.2)) p :=
      htime.prodMk continuousAt_snd
    have hcomp :
        ContinuousAt
          (fun q : Real × M => S.scalar (paraTime τ R q.1) q.2) p :=
      ContinuousAt.comp
        (x := p)
        (f := fun q : Real × M => (paraTime τ R q.1, q.2))
        (g := fun q : Real × M => S.scalar q.1 q.2)
        hOld hmap
    have hscale :
        ContinuousAt
          (fun q : Real × M => R⁻¹ * S.scalar (paraTime τ R q.1) q.2) p :=
      continuousAt_const.mul hcomp
    have hscalar_fun :
        (fun q : Real × M =>
          (paraSolution (I := I) S τ R hR hτ).scalar q.1 q.2) =
            fun q : Real × M => R⁻¹ * S.scalar (paraTime τ R q.1) q.2 := by
      funext q
      rw [paraSolution_scalar (I := I) S τ R hR hτ]
    rw [hscalar_fun]
    exact hscale
  scalarTime := by
    intro K t ht hK x
    let shift : Real -> Real := fun s => paraTime τ R s
    have ht' : shift t ∈ shift '' K := ⟨t, ht, rfl⟩
    have hK' : shift '' K ⊆ D.carrier := by
      intro r hr
      rcases hr with ⟨s, hs, rfl⟩
      exact hK hs
    have hOld := hS.scalarTime (K := shift '' K) (t := shift t) ht' hK' x
    have hshift : DifferentiableWithinAt Real shift K t := by
      simpa [shift, paraTime] using
        ((differentiableWithinAt_id' (𝕜 := Real) (s := K) (x := t)).div_const R).const_add τ
    have hmaps : Set.MapsTo shift K (shift '' K) := by
      intro s hs
      exact ⟨s, hs, rfl⟩
    have hcomp := hOld.comp t hshift hmaps
    have hscaled := hcomp.const_mul R⁻¹
    have hscalar :
        (fun s : Real => (paraSolution (I := I) S τ R hR hτ).scalar s x) =
          fun s : Real => R⁻¹ * S.scalar (paraTime τ R s) x := by
      funext s
      exact congrFun (congrFun (paraSolution_scalar (I := I) S τ R hR hτ) s) x
    rw [hscalar]
    simpa [shift, Function.comp_def] using hscaled
  ricciCont := by
    have hmaps :
        Set.MapsTo (fun s : Real => paraTime τ R s)
          (paraInterval D τ R hR hτ).carrier D.carrier := by
      intro s hs
      exact hs
    have htime : Continuous (fun s : Real => paraTime τ R s) := by
      unfold paraTime
      exact continuous_const.add (continuous_id.div_const R)
    have hcont :=
      Realized.Tensor0SFamilyContinuousOnSet.comp_time (I := I) (M := M)
        hS.ricciCont htime hmaps
    simpa [SolutionOn.ricci, paraSolution_ricci (I := I) S τ R hR hτ] using hcont
  rm04Cont := by
    have hmaps :
        Set.MapsTo (fun s : Real => paraTime τ R s)
          (paraInterval D τ R hR hτ).carrier D.carrier := by
      intro s hs
      exact hs
    have htime : Continuous (fun s : Real => paraTime τ R s) := by
      unfold paraTime
      exact continuous_const.add (continuous_id.div_const R)
    have hcomp :=
      Realized.Tensor0SFamilyContinuousOnSet.comp_time (I := I) (M := M)
        hS.rm04Cont htime hmaps
    have hscale :=
      Realized.Tensor0SFamilyContinuousOnSet.const_smul (I := I) (M := M)
        R hcomp
    simpa [paraSolution_rm04 (I := I) S τ R hR hτ] using hscale
  nablaRicCont := by
    have hmaps :
        Set.MapsTo (fun s : Real => paraTime τ R s)
          (paraInterval D τ R hR hτ).carrier D.carrier := by
      intro s hs
      exact hs
    have htime : Continuous (fun s : Real => paraTime τ R s) := by
      unfold paraTime
      exact continuous_const.add (continuous_id.div_const R)
    have hcont :=
      Realized.Tensor0SFamilyContinuousOnSet.comp_time (I := I) (M := M)
        hS.nablaRicCont htime hmaps
    simpa [paraNablaRic_eq (I := I) S τ R hR hτ] using hcont
  ricciNormSpace := by
    intro t ht x
    have hOld :
        MDifferentiableAt I 𝓘(Real, Real)
          (ricciNorm (I := I) S (paraTime τ R t)) x :=
      hS.ricciNormSpace (paraTime τ R t) ht x
    have hscaled := hOld.const_smul (R⁻¹ * R⁻¹)
    have hfun :
        ricciNorm (I := I) (paraSolution (I := I) S τ R hR hτ) t =
          (R⁻¹ * R⁻¹) • ricciNorm (I := I) S (paraTime τ R t) := by
      funext y
      have h := congrFun
        (congrFun (paraSolution_ricciNorm (I := I) S τ R hR hτ) t) y
      rw [h]
      simp [Pi.smul_apply, smul_eq_mul, mul_assoc]
    simpa [hfun] using hscaled
  ricciNormGrad := by
    intro t ht x
    have hOld :
        MDiffAt (T% fun y : M =>
          Realized.gradientFun (I := I) (S.family.metric (paraTime τ R t))
            (ricciNorm (I := I) S (paraTime τ R t)) y) x :=
      hS.ricciNormGrad (paraTime τ R t) ht x
    have hscaled :
        MDiffAt (T% fun y : M =>
          (R⁻¹ * R⁻¹ * R⁻¹) •
            Realized.gradientFun (I := I) (S.family.metric (paraTime τ R t))
              (ricciNorm (I := I) S (paraTime τ R t)) y) x := by
      simpa [Pi.smul_apply] using
        (mdifferentiableAt_const (I := I) (c := R⁻¹ * R⁻¹ * R⁻¹)).smul_section hOld
    have hpt : ∀ y : M,
        Realized.gradientFun (I := I)
          ((paraSolution (I := I) S τ R hR hτ).family.metric t)
          (ricciNorm (I := I) (paraSolution (I := I) S τ R hR hτ) t) y =
          (R⁻¹ * R⁻¹ * R⁻¹) •
            Realized.gradientFun (I := I) (S.family.metric (paraTime τ R t))
              (ricciNorm (I := I) S (paraTime τ R t)) y := by
      intro y
      exact paraRicciNormGrad_eq (I := I) S hS τ R hR hτ ht y
    have htotal :
        (T% fun y : M =>
          Realized.gradientFun (I := I)
            ((paraSolution (I := I) S τ R hR hτ).family.metric t)
            (ricciNorm (I := I) (paraSolution (I := I) S τ R hR hτ) t) y) =
          (T% fun y : M =>
            (R⁻¹ * R⁻¹ * R⁻¹) •
              Realized.gradientFun (I := I) (S.family.metric (paraTime τ R t))
                (ricciNorm (I := I) S (paraTime τ R t)) y) := by
      funext y
      change
          TotalSpace.mk' E y
            (Realized.gradientFun (I := I)
              ((paraSolution (I := I) S τ R hR hτ).family.metric t)
              (ricciNorm (I := I) (paraSolution (I := I) S τ R hR hτ) t) y) =
            TotalSpace.mk' E y
              ((R⁻¹ * R⁻¹ * R⁻¹) •
                Realized.gradientFun (I := I) (S.family.metric (paraTime τ R t))
                  (ricciNorm (I := I) S (paraTime τ R t)) y)
      rw [hpt y]
    rw [htotal]
    exact hscaled
  scalarEvolution := by
    intro G hmetric hconnection t x
    let tOld : Realized.RealTimeInterval.RegularTime D :=
      ⟨paraTime τ R (t : Real), t.2⟩
    have hmetricOld : ∀ r : Realized.RealTimeInterval.RegularTime D,
        (flowG (I := I) S).metric (r : Real) = S.family.metric (r : Real) := by
      intro r
      rfl
    have hconnectionOld : ∀ r : Realized.RealTimeInterval.RegularTime D,
        (flowG (I := I) S).connection (r : Real) =
          S.family.connection (r : Real) := by
      intro r
      rfl
    have hOld := hS.scalarEvolution (flowG (I := I) S)
      hmetricOld hconnectionOld tOld x
    have hscalarSmooth :
        ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
          (S.scalar (paraTime τ R (t : Real))) := by
      simpa [SolutionOn.scalar, SolutionFamily.scalar] using
        (metricScalar_smooth (I := I) (M := M)
          (S.family.metric (paraTime τ R (t : Real))))
    have hscalarSpace : ∀ y : M,
        MDifferentiableAt I 𝓘(Real, Real)
          (S.scalar (paraTime τ R (t : Real))) y := by
      intro y
      exact hscalarSmooth.contMDiffAt.mdifferentiableAt (by simp)
    have hscalarGrad :
        MDiffAt (T% fun y : M =>
          Realized.gradientFun (I := I) (S.family.metric (paraTime τ R (t : Real)))
            (S.scalar (paraTime τ R (t : Real))) y) x :=
      Realized.gradientFun_mdiffAt (I := I)
        (S.family.metric (paraTime τ R (t : Real))) hscalarSmooth x
    have hscalarAt :
        (paraSolution (I := I) S τ R hR hτ).scalar (t : Real) =
          R⁻¹ • S.scalar (paraTime τ R (t : Real)) := by
      funext y
      have h := congrFun
        (congrFun (paraSolution_scalar (I := I) S τ R hR hτ) (t : Real)) y
      simpa [Pi.smul_apply, smul_eq_mul] using h
    have hmetric_t := hmetric t
    have hconnection_t := hconnection t
    have hmetricPara :
        (paraSolution (I := I) S τ R hR hτ).family.metric (t : Real) =
          scaleMetric (I := I) R hR
            (S.family.metric (paraTime τ R (t : Real))) := by
      rfl
    have hconnectionPara :
        (paraSolution (I := I) S τ R hR hτ).family.connection (t : Real) =
          S.family.connection (paraTime τ R (t : Real)) := by
      have h := congrFun (paraSolution_connection (I := I) S τ R hR hτ) (t : Real)
      exact h
    have hLap :
        Realized.laplacianAt (I := I) G (t : Real)
            ((paraSolution (I := I) S τ R hR hτ).scalar (t : Real)) x =
          R⁻¹ * R⁻¹ *
            Realized.laplacianAt (I := I) (flowG (I := I) S)
              (paraTime τ R (t : Real))
              (S.scalar (paraTime τ R (t : Real))) x := by
      have hscale :=
        Realized.laplacian_scaleMetric_const_smul (I := I) R hR
          (S.family.connection (paraTime τ R (t : Real)))
          (S.family.metric (paraTime τ R (t : Real)))
          (f := S.scalar (paraTime τ R (t : Real))) (x := x)
          hscalarSpace hscalarGrad
      unfold Realized.laplacianAt
      rw [hmetric_t, hconnection_t, hscalarAt, hmetricPara, hconnectionPara]
      simpa [flowG, SolutionOn.family] using hscale
    have hricciAt :
        (paraSolution (I := I) S τ R hR hτ).ricci (t : Real) x =
          S.ricci (paraTime τ R (t : Real)) x := by
      have h := congrFun (paraSolution_ricci (I := I) S τ R hR hτ) (t : Real)
      change ((paraSolution (I := I) S τ R hR hτ).base.ricci (t : Real)) x =
        (S.base.ricci (paraTime τ R (t : Real))) x
      exact congrArg (fun A => A x) h
    have hNorm :
        normSq0S (I := I)
            ((paraSolution (I := I) S τ R hR hτ).family.metric (t : Real))
            x 2 ((paraSolution (I := I) S τ R hR hτ).ricci (t : Real) x) =
          R⁻¹ * R⁻¹ *
            normSq0S (I := I) (S.family.metric (paraTime τ R (t : Real)))
              x 2 (S.ricci (paraTime τ R (t : Real)) x) := by
      rw [hmetricPara, hricciAt]
      exact normSq0S_two_scale (I := I) R hR
        (S.family.metric (paraTime τ R (t : Real)))
        (x := x) (A := S.ricci (paraTime τ R (t : Real)) x)
    have hRhs :
        Realized.laplacianAt (I := I) G (t : Real)
            ((paraSolution (I := I) S τ R hR hτ).scalar (t : Real)) x +
          2 * normSq0S (I := I)
            ((paraSolution (I := I) S τ R hR hτ).family.metric (t : Real))
            x 2 ((paraSolution (I := I) S τ R hR hτ).ricci (t : Real) x) =
          R⁻¹ *
            ((Realized.laplacianAt (I := I) (flowG (I := I) S)
                (paraTime τ R (t : Real))
                (S.scalar (paraTime τ R (t : Real))) x +
              2 * normSq0S (I := I)
                (S.family.metric (paraTime τ R (t : Real))) x 2
                (S.ricci (paraTime τ R (t : Real)) x)) * R⁻¹) := by
      rw [hLap, hNorm]
      ring
    have htime :
        HasDerivWithinAt (fun s : Real => paraTime τ R s) R⁻¹
          (paraInterval D τ R hR hτ).carrier (t : Real) := by
      simpa [paraTime, one_div] using
        (((hasDerivWithinAt_id (t : Real)
          (paraInterval D τ R hR hτ).carrier).div_const R).const_add τ)
    have hmaps :
        Set.MapsTo (fun s : Real => paraTime τ R s)
          (paraInterval D τ R hR hτ).carrier D.carrier := by
      intro s hs
      exact hs
    have hcomp := hOld.comp (x := (t : Real)) htime hmaps
    have hscaled := hcomp.const_mul R⁻¹
    have hscalar :
        (fun s : Real => (paraSolution (I := I) S τ R hR hτ).scalar s x) =
          fun s : Real => R⁻¹ * S.scalar (paraTime τ R s) x := by
      funext s
      exact congrFun (congrFun (paraSolution_scalar (I := I) S τ R hR hτ) s) x
    rw [hscalar]
    exact (hscaled.congr_deriv (by
      simpa [tOld] using hRhs.symm))

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
  simp [paraBackFamily, paraFamily, SolutionFamily.connection,
    LeviCivita.lcConn_scaleMetric, paraTime_back (τ := τ) (R := R) (t := t)
      (ne_of_gt hR)]

theorem paraBack_para_ricci
    (G : SolutionFamily (I := I) (M := M))
    (τ R : Real) (hR : 0 < R) (t : Real) :
    (paraBackFamily (I := I) (paraFamily (I := I) G τ R hR)
      τ R hR).ricci t = G.ricci t := by
  simp [paraBackFamily, paraFamily, SolutionFamily.ricci, metricRicci,
    Curvature.metricRicci, Curvature.metricCov, LeviCivita.lcConn_scaleMetric,
    paraTime_back (τ := τ) (R := R) (t := t) (ne_of_gt hR)]

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
  simp [paraFamily, paraBackFamily, SolutionFamily.connection,
    LeviCivita.lcConn_scaleMetric, paraBack_time (τ := τ) (R := R) (s := s)
      (ne_of_gt hR)]

theorem para_paraBack_ricci
    (G : SolutionFamily (I := I) (M := M))
    (τ R : Real) (hR : 0 < R) (s : Real) :
    (paraFamily (I := I) (paraBackFamily (I := I) G τ R hR)
      τ R hR).ricci s = G.ricci s := by
  simp [paraFamily, paraBackFamily, SolutionFamily.ricci, metricRicci,
    Curvature.metricRicci, Curvature.metricCov, LeviCivita.lcConn_scaleMetric,
    paraBack_time (τ := τ) (R := R) (s := s) (ne_of_gt hR)]

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
