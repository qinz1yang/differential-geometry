import DifferentialGeometry.Geometry.Flow.RicciFlow.HamiltonHarnack.TraceHarnack
import DifferentialGeometry.Geometry.Flow.RicciFlow.HamiltonHarnack.Optimization
import DifferentialGeometry.Geometry.Flow.RicciFlow.HamiltonHarnack.AncientLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Scalar.JointRegularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.MetricComparison
import DifferentialGeometry.Geometry.Curvature.Bounds.RicciUpper
import DifferentialGeometry.Geometry.Exponential.MinimizingGeodesic
import DifferentialGeometry.Geometry.Geodesic.Maximal.Interval
import DifferentialGeometry.Analysis.Calculus.Derivative.Curve
import DifferentialGeometry.Analysis.Calculus.Derivative.Right

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Analysis.Calculus (PiecewiseContMDiffOn)
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [IsManifold I 1 M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]

omit [SigmaCompactSpace M] in
private theorem scalar_hasDerivAt_of_regular
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    {t : Real} (ht : t ∈ D.regular) (x : M) :
    HasDerivAt (fun s : Real => S.scalar s x)
      (deriv (fun s : Real => S.scalar s x) t) t := by
  exact ((hS.scalarTime (K := D.carrier) (D.regular_subset ht)
    (fun _ hs => hs) x).differentiableAt (D.regular_mem_nhds ht)).hasDerivAt

omit [SigmaCompactSpace M] in
private theorem path_speedSq_continuousOn
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    {a b : Real} (hab : a < b)
    (hregular : Set.Icc a b ⊆ D.regular)
    (gamma : Real → M)
    (hgamma : ContMDiffOn 𝓘(Real, Real) I 1 gamma (Set.Icc a b)) :
    ContinuousOn
      (fun t : Real =>
        (S.base.metric t).inner (gamma t)
          (mfderivWithin 𝓘(Real, Real) I gamma (Set.Icc a b) t (1 : Real))
          (mfderivWithin 𝓘(Real, Real) I gamma (Set.Icc a b) t (1 : Real)))
      (Set.Icc a b) := by
  classical
  let v : (t : Real) → TangentSpace I (gamma t) := fun t =>
    mfderivWithin 𝓘(Real, Real) I gamma (Set.Icc a b) t (1 : Real)
  have hvLiftOn :=
    DifferentialGeometry.Geometry.Riemannian.Geodesic.continuousOn_velocityWithin_totalSpace_of_contMDiffOn
      (I := I) (M := M) hab hgamma
  have hvLift : Continuous (fun t : ↥(Set.Icc a b) =>
      (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
        (gamma (t : Real)) (v (t : Real)) : TangentBundle I M)) := by
    rw [continuousOn_iff_continuous_domRestrict] at hvLiftOn
    change Continuous (fun t : ↥(Set.Icc a b) =>
      (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
        (gamma (t : Real))
        (mfderivWithin 𝓘(Real, Real) I gamma (Set.Icc a b)
          (t : Real) (1 : Real)) : TangentBundle I M)) at hvLiftOn
    simpa only [v] using hvLiftOn
  rw [continuousOn_iff_continuous_domRestrict]
  have htime : Continuous (fun t : ↥(Set.Icc a b) => (t : Real)) :=
    continuous_subtype_val
  have hbase : Continuous (fun t : ↥(Set.Icc a b) => gamma (t : Real)) :=
    hgamma.continuousOn.comp_continuous continuous_subtype_val
      (fun t => t.2)
  have hvec : ∀ _i : Fin 2, Continuous (fun t : ↥(Set.Icc a b) =>
      (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
        (gamma (t : Real)) (v (t : Real)) : TangentBundle I M)) := fun _ => hvLift
  have heval := hS.smoothMetric.metricTensor_cont.eval_continuous
    (P := ↥(Set.Icc a b)) (τ := fun t => (t : Real))
    (b := fun t => gamma (t : Real)) htime
    (fun t => D.regular_subset (hregular t.2)) hbase
    (v := fun _i t => v (t : Real)) hvec
  refine heval.congr (fun t => ?_)
  rw [Tensor0SBundle.metricTensorField_apply]
  rfl

private theorem scalar_path_differential_inequality
    [I.Boundaryless] [NeZero (Module.finrank Real E)]
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (hcomplete : ∀ t ∈ D.regular,
      RiemannianMetricComplete (I := I) (S.base.metric t))
    (hcurv : ∀ a b : Real, Set.Icc a b ⊆ D.regular →
      ∃ C : Real, ∀ t ∈ Set.Icc a b, ∀ x : M,
        normSq0S (I := I) (S.base.metric t) x 4 (S.base.rm04 t x) ≤ C)
    (hR : ∀ t ∈ D.regular, ∀ x : M,
      metricAlgebraicCurvatureTensorAt
        (I := I) (M := M) (S.base.metric t) x ∈
          algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    {origin a b t : Real} (horigin : origin < a)
    (hregular : Set.Icc origin b ⊆ D.regular)
    (gamma : Real → M)
    (ht : t ∈ Set.Ioo a b) :
    0 ≤
      (deriv (fun s : Real => S.scalar s (gamma t)) t +
        (S.base.metric t).inner (gamma t)
          (gradientAt (I := I) (flowG (I := I) S) t
            (S.scalar t) (gamma t))
          (mfderiv 𝓘(Real, Real) I gamma t (1 : Real))) +
      S.scalar t (gamma t) / (t - origin) +
      (1 / 4 : Real) *
        (S.base.metric t).inner (gamma t)
          (mfderivWithin 𝓘(Real, Real) I gamma (Set.Icc a b) t (1 : Real))
          (mfderivWithin 𝓘(Real, Real) I gamma (Set.Icc a b) t (1 : Real)) *
        S.scalar t (gamma t) := by
  let w : TangentSpace I (gamma t) :=
    mfderiv 𝓘(Real, Real) I gamma t (1 : Real)
  let clock : HarnackClock := ⟨origin, t, horigin.trans ht.1⟩
  have htreg : t ∈ D.regular :=
    hregular ⟨horigin.le.trans ht.1.le, ht.2.le⟩
  have hclock : Set.Icc clock.origin clock.time ⊆ D.regular := by
    intro s hs
    exact hregular ⟨hs.1, hs.2.trans ht.2.le⟩
  have htrace := hamilton_trace_harnack (I := I) S hS hcomplete hcurv hR
    clock hclock (gamma t) ((1 / 2 : Real) • w)
  have hinner :
      (S.base.metric t).inner (gamma t)
        (gradientAt (I := I) (flowG (I := I) S) t
          (S.scalar t) (gamma t)) ((1 / 2 : Real) • w) =
      (1 / 2 : Real) *
        (S.base.metric t).inner (gamma t)
          (gradientAt (I := I) (flowG (I := I) S) t
            (S.scalar t) (gamma t)) w := by
    rw [map_smul]
    simp [smul_eq_mul]
  have hricScale :
      metricRicci (I := I) (M := M) (S.base.metric t) (gamma t)
          (vec2 ((1 / 2 : Real) • w) ((1 / 2 : Real) • w)) =
        (1 / 4 : Real) *
          metricRicci (I := I) (M := M) (S.base.metric t) (gamma t)
            (vec2 w w) := by
    have hscale := tensor02_smul2 (I := I) (M := M)
      (metricRicci (I := I) (M := M) (S.base.metric t) (gamma t))
      (1 / 2 : Real) w w
    norm_num [pow_two] at hscale ⊢
    exact hscale
  rw [hinner, hricScale] at htrace
  have htraceRaw :
      0 ≤ deriv (fun s : Real => S.scalar s (gamma t)) t +
          S.scalar t (gamma t) / (t - origin) +
        (S.base.metric t).inner (gamma t)
          (gradientAt (I := I) (flowG (I := I) S) t
            (S.scalar t) (gamma t)) w +
        2 * ((1 / 4 : Real) *
          metricRicci (I := I) (M := M) (S.base.metric t) (gamma t)
            (vec2 w w)) := by
    simpa [clock, HarnackClock.elapsed] using htrace
  have htrace' :
      0 ≤ deriv (fun s : Real => S.scalar s (gamma t)) t +
          (S.base.metric t).inner (gamma t)
            (gradientAt (I := I) (flowG (I := I) S) t
              (S.scalar t) (gamma t)) w +
        S.scalar t (gamma t) / (t - origin) +
        (1 / 2 : Real) *
          metricRicci (I := I) (M := M) (S.base.metric t) (gamma t)
            (vec2 w w) := by
    nlinarith [htraceRaw]
  have hupper0 :=
    metricRicciAt_le_half_scalar_mul_inner_of_curvatureOperator_nonnegative
      (I := I) (M := M) (S.base.metric t) (gamma t)
      (hR t htreg (gamma t)) w
  have hupper :
      metricRicci (I := I) (M := M) (S.base.metric t) (gamma t)
          (vec2 w w) ≤
        (S.scalar t (gamma t) / 2) *
          (S.base.metric t).inner (gamma t) w w := by
    simpa [metricScalarAt, SolutionOn.scalar_eq_metricTrace,
      SolutionOn.ricciAt, SolutionFamily.ricciAt] using hupper0
  have hupperHalf := mul_le_mul_of_nonneg_left hupper
    (show 0 ≤ (1 / 2 : Real) by norm_num)
  have hwWithin :
      mfderivWithin 𝓘(Real, Real) I gamma (Set.Icc a b) t (1 : Real) = w := by
    rw [mfderivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)]
  rw [hwWithin]
  dsimp only [w] at htrace' hupperHalf ⊢
  nlinarith

omit [SigmaCompactSpace M] [IsManifold I 1 M] [CompleteSpace E] [T2Space M] in
private theorem tensor02_apply_eq_coordinate_sum
    {Idx : Type*} [Fintype Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (T : Tensor02At (I := I) (M := M) x) (X Y : TangentSpace I x) :
    T (vec2 X Y) = ∑ a, ∑ b,
      T (vec2 (basis a) (basis b)) * basis.repr X a * basis.repr Y b := by
  classical
  rw [tensor0S_apply_eq_sum (I := I) basis T (vec2 X Y), sum_fin_two_fun]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [component0S_apply]
  have hslots : (fun q : Fin 2 => basis (if q = 0 then a else b)) =
      vec2 (basis a) (basis b) := by
    funext q
    fin_cases q <;> rfl
  rw [hslots]
  simp [vec2, Fin.prod_univ_two, Module.Basis.coord_apply]
  ring

omit [SigmaCompactSpace M] [IsManifold I 1 M] [CompleteSpace E] [T2Space M] in
private theorem tensor02_apply_basis_left_eq_sum
    {Idx : Type*} [Fintype Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (T : Tensor02At (I := I) (M := M) x) (a : Idx) (Y : TangentSpace I x) :
    T (vec2 (basis a) Y) =
      ∑ b, T (vec2 (basis a) (basis b)) * basis.repr Y b := by
  classical
  rw [tensor02_apply_eq_coordinate_sum (I := I) basis T]
  rw [Finset.sum_eq_single a]
  · simp [Module.Basis.repr_self]
  · intro i _ hi
    simp [Module.Basis.repr_self, hi]
  · intro ha
    exact False.elim (ha (Finset.mem_univ a))

theorem hamilton_scalar_clock_deriv_nonneg
    [I.Boundaryless] [NeZero (Module.finrank Real E)]
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (hcomplete : ∀ t ∈ D.regular,
      RiemannianMetricComplete (I := I) (S.base.metric t))
    (hcurv : ∀ a b : Real, Set.Icc a b ⊆ D.regular →
      ∃ C : Real, ∀ t ∈ Set.Icc a b, ∀ x : M,
        normSq0S (I := I) (S.base.metric t) x 4 (S.base.rm04 t x) ≤ C)
    (hR : ∀ t ∈ D.regular, ∀ x : M,
      metricAlgebraicCurvatureTensorAt
        (I := I) (M := M) (S.base.metric t) x ∈
          algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    (clock : HarnackClock)
    (hclock : Set.Icc clock.origin clock.time ⊆ D.regular)
    (x : M) :
    0 ≤ deriv (fun s : Real => (s - clock.origin) * S.scalar s x)
      clock.time := by
  have ht : clock.time ∈ D.regular :=
    hclock ⟨clock.origin_lt_time.le, le_rfl⟩
  have htrace := hamilton_trace_harnack (I := I) S hS hcomplete hcurv hR
    clock hclock x (0 : TangentSpace I x)
  have hscalar := scalar_hasDerivAt_of_regular (I := I) S hS ht x
  have hshift := hamilton_shifted_scalar_hasDerivAt
    (R := fun s : Real => S.scalar s x)
    (dR := fun s : Real => deriv (fun r : Real => S.scalar r x) s)
    (α := clock.origin) hscalar
  rw [hshift.deriv]
  apply hamilton_shifted_scalar_deriv_nonneg
    (R := fun s : Real => S.scalar s x)
    (dR := fun s : Real => deriv (fun r : Real => S.scalar r x) s)
    clock.origin_lt_time
  have hRicZero :
      metricRicci (I := I) (M := M) (S.base.metric clock.time) x
        (vec2 (0 : TangentSpace I x) 0) = 0 := by
    exact (metricRicci (I := I) (M := M) (S.base.metric clock.time) x).map_coord_zero
      (i := 0) (by simp [vec2])
  rw [hRicZero] at htrace
  simpa [HarnackClock.elapsed] using htrace

theorem hamilton_scalar_clock_monotoneOn
    [I.Boundaryless] [NeZero (Module.finrank Real E)]
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (hcomplete : ∀ t ∈ D.regular,
      RiemannianMetricComplete (I := I) (S.base.metric t))
    (hcurv : ∀ a b : Real, Set.Icc a b ⊆ D.regular →
      ∃ C : Real, ∀ t ∈ Set.Icc a b, ∀ x : M,
        normSq0S (I := I) (S.base.metric t) x 4 (S.base.rm04 t x) ≤ C)
    (hR : ∀ t ∈ D.regular, ∀ x : M,
      metricAlgebraicCurvatureTensorAt
        (I := I) (M := M) (S.base.metric t) x ∈
          algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    {origin t₁ t₂ : Real} (horigin : origin < t₁)
    (hregular : Set.Icc origin t₂ ⊆ D.regular) (x : M) :
    MonotoneOn (fun s : Real => (s - origin) * S.scalar s x)
      (Set.Icc t₁ t₂) := by
  have hscalarCont : ContinuousOn (fun s : Real => S.scalar s x)
      (Set.Icc t₁ t₂) := by
    have hmap : Continuous (fun s : Real => (s, x)) :=
      continuous_id.prodMk continuous_const
    have hcomp := hS.scalarCont.comp hmap.continuousOn
      (fun (s : Real) (hs : s ∈ Set.Icc t₁ t₂) => ⟨
        D.regular_subset (hregular ⟨horigin.le.trans hs.1, hs.2⟩), Set.mem_univ x⟩)
    simpa [Function.comp_def] using hcomp
  apply hamilton_shifted_scalar_monotoneOn horigin.le
    ((continuousOn_id.sub continuousOn_const).mul hscalarCont)
  · intro s hs
    exact scalar_hasDerivAt_of_regular (I := I) S hS
      (hregular ⟨horigin.le.trans hs.1.le, hs.2.le⟩) x
  · intro s hs
    let clock : HarnackClock := ⟨origin, s, horigin.trans hs.1⟩
    have hclock : Set.Icc origin s ⊆ D.regular := by
      intro r hr
      exact hregular ⟨hr.1, hr.2.trans (hs.2.le)⟩
    have htrace := hamilton_trace_harnack (I := I) S hS hcomplete hcurv hR
      clock hclock x (0 : TangentSpace I x)
    have hRicZero :
        metricRicci (I := I) (M := M) (S.base.metric s) x
          (vec2 (0 : TangentSpace I x) 0) = 0 := by
      exact (metricRicci (I := I) (M := M) (S.base.metric s) x).map_coord_zero
        (i := 0) (by simp [vec2])
    rw [hRicZero] at htrace
    simpa [clock, HarnackClock.elapsed] using htrace

theorem hamilton_scalar_two_time
    [I.Boundaryless] [NeZero (Module.finrank Real E)]
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (hcomplete : ∀ t ∈ D.regular,
      RiemannianMetricComplete (I := I) (S.base.metric t))
    (hcurv : ∀ a b : Real, Set.Icc a b ⊆ D.regular →
      ∃ C : Real, ∀ t ∈ Set.Icc a b, ∀ x : M,
        normSq0S (I := I) (S.base.metric t) x 4 (S.base.rm04 t x) ≤ C)
    (hR : ∀ t ∈ D.regular, ∀ x : M,
      metricAlgebraicCurvatureTensorAt
        (I := I) (M := M) (S.base.metric t) x ∈
          algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    {origin t₁ t₂ : Real} (horigin : origin < t₁) (htimes : t₁ ≤ t₂)
    (hregular : Set.Icc origin t₂ ⊆ D.regular) (x : M) :
    (t₁ - origin) / (t₂ - origin) * S.scalar t₁ x ≤ S.scalar t₂ x := by
  have hmono := hamilton_scalar_clock_monotoneOn (I := I) S hS
    hcomplete hcurv hR horigin hregular x
  have hscaled := hamilton_shifted_scalar_two_time htimes hmono
  have hden : 0 < t₂ - origin := sub_pos.mpr (horigin.trans_le htimes)
  calc
    (t₁ - origin) / (t₂ - origin) * S.scalar t₁ x =
        ((t₁ - origin) * S.scalar t₁ x) / (t₂ - origin) := by ring
    _ ≤ ((t₂ - origin) * S.scalar t₂ x) / (t₂ - origin) :=
      (div_le_div_iff_of_pos_right hden).2 hscaled
    _ = S.scalar t₂ x := by field_simp [ne_of_gt hden]

omit [FiniteDimensional Real E] [IsManifold I 1 M] [CompleteSpace E]
    [SigmaCompactSpace M] [T2Space M] in
private theorem trace_path_energy_integral_within_eq
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    {a b : Real} (hab : a < b) (gamma : Real → M) :
    intervalIntegral
        (fun t : Real =>
          (S.base.metric t).inner (gamma t)
            (mfderivWithin 𝓘(Real, Real) I gamma (Set.Icc a b) t (1 : Real))
            (mfderivWithin 𝓘(Real, Real) I gamma (Set.Icc a b) t (1 : Real)))
        a b MeasureTheory.volume =
      intervalIntegral
        (fun t : Real =>
          (S.base.metric t).inner (gamma t)
            (mfderiv 𝓘(Real, Real) I gamma t (1 : Real))
            (mfderiv 𝓘(Real, Real) I gamma t (1 : Real)))
        a b MeasureTheory.volume := by
  apply intervalIntegral.integral_congr_Ioo_of_le hab.le
  intro t ht
  have hv :
      mfderivWithin 𝓘(Real, Real) I gamma (Set.Icc a b) t =
        mfderiv 𝓘(Real, Real) I gamma t :=
    mfderivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)
  simp only [hv]

private theorem trace_harnack_path_within_of_contMDiffOn
    [I.Boundaryless] [NeZero (Module.finrank Real E)]
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (hcomplete : ∀ t ∈ D.regular,
      RiemannianMetricComplete (I := I) (S.base.metric t))
    (hcurv : ∀ a b : Real, Set.Icc a b ⊆ D.regular →
      ∃ C : Real, ∀ t ∈ Set.Icc a b, ∀ x : M,
        normSq0S (I := I) (S.base.metric t) x 4 (S.base.rm04 t x) ≤ C)
    (hR : ∀ t ∈ D.regular, ∀ x : M,
      metricAlgebraicCurvatureTensorAt
        (I := I) (M := M) (S.base.metric t) x ∈
          algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    {origin t₁ t₂ : Real} (horigin : origin < t₁) (htimes : t₁ < t₂)
    (hregular : Set.Icc origin t₂ ⊆ D.regular)
    (gamma : Real → M)
    (hgamma : ContMDiffOn 𝓘(Real, Real) I 1 gamma (Set.Icc t₁ t₂)) :
    (t₁ - origin) / (t₂ - origin) *
        Real.exp (-(1 / 4 : Real) *
          intervalIntegral
            (fun t : Real =>
              (S.base.metric t).inner (gamma t)
                (mfderivWithin 𝓘(Real, Real) I gamma (Set.Icc t₁ t₂) t (1 : Real))
                (mfderivWithin 𝓘(Real, Real) I gamma (Set.Icc t₁ t₂) t (1 : Real)))
            t₁ t₂ MeasureTheory.volume) *
      S.scalar t₁ (gamma t₁) ≤ S.scalar t₂ (gamma t₂) := by
  let speedSq : Real → Real := fun t =>
    (S.base.metric t).inner (gamma t)
      (mfderivWithin 𝓘(Real, Real) I gamma (Set.Icc t₁ t₂) t (1 : Real))
      (mfderivWithin 𝓘(Real, Real) I gamma (Set.Icc t₁ t₂) t (1 : Real))
  let R : Real → Real := fun t => S.scalar t (gamma t)
  let dR : Real → Real := fun t =>
    deriv (fun s : Real => S.scalar s (gamma t)) t +
      (S.base.metric t).inner (gamma t)
        (gradientFun (I := I) (S.base.metric t) (S.scalar t) (gamma t))
        (mfderiv 𝓘(Real, Real) I gamma t (1 : Real))
  let q : Real → Real := (fun t : Real => t - origin) * R
  let q' : Real → Real := fun t => R t + (t - origin) * dR t
  let coeff : Real → Real := fun t => (1 / 4 : Real) * speedSq t
  have hpathRegular : Set.Icc t₁ t₂ ⊆ D.regular := by
    intro t ht
    exact hregular ⟨horigin.le.trans ht.1, ht.2⟩
  have hRcont : ContinuousOn R (Set.Icc t₁ t₂) := by
    have harg : ContinuousOn (fun t : Real => (t, gamma t)) (Set.Icc t₁ t₂) :=
      continuousOn_id.prodMk hgamma.continuousOn
    have hcomp := hS.scalarCont.comp harg
      (fun t ht => ⟨D.regular_subset (hpathRegular ht), Set.mem_univ (gamma t)⟩)
    change ContinuousOn (fun t : Real => S.scalar t (gamma t)) (Set.Icc t₁ t₂)
    exact hcomp.congr fun _ _ => rfl
  have hqcont : ContinuousOn q (Set.Icc t₁ t₂) :=
    (continuousOn_id.sub continuousOn_const).mul hRcont
  have hspeedCont : ContinuousOn speedSq (Set.Icc t₁ t₂) := by
    simpa only [speedSq] using
      path_speedSq_continuousOn (I := I) S hS htimes hpathRegular gamma hgamma
  have hcoeffCont : ContinuousOn coeff (Set.Icc t₁ t₂) :=
    hspeedCont.const_mul (1 / 4 : Real)
  have hqderiv : ∀ t ∈ Set.Ioo t₁ t₂, HasDerivAt q (q' t) t := by
    intro t ht
    have htreg : t ∈ D.regular := hpathRegular (Set.Ioo_subset_Icc_self ht)
    have hgammaAt : MDifferentiableAt 𝓘(Real, Real) I gamma t :=
      ((hgamma t (Set.Ioo_subset_Icc_self ht)).contMDiffAt
        (Icc_mem_nhds ht.1 ht.2)).mdifferentiableAt (by norm_num)
    have hscalarJoint : MDifferentiableAt
        ((𝓘(Real, Real)).prod I) 𝓘(Real, Real)
        (fun p : Real × M => S.scalar p.1 p.2) (t, gamma t) :=
      ((scalar_joint (I := I) S hS).contMDiffAt
        ((D.regular_isOpen.prod isOpen_univ).mem_nhds
          ⟨htreg, Set.mem_univ (gamma t)⟩)).mdifferentiableAt (by norm_num)
    have htime := scalar_hasDerivAt_of_regular (I := I) S hS htreg (gamma t)
    have halong :=
      DifferentialGeometry.Analysis.Calculus.hasDerivAt_along_curve
        (I := I) (g := S.base.metric t) hscalarJoint hgammaAt htime
    have halong' : HasDerivAt R (dR t) t := by
      simpa only [R, dR] using halong
    change HasDerivAt (fun s : Real => (s - origin) * R s)
      (R t + (t - origin) * dR t) t
    exact hamilton_shifted_scalar_hasDerivAt halong'
  have hqnonneg : ∀ t ∈ Set.Ioo t₁ t₂,
      0 ≤ q' t + coeff t * q t := by
    intro t ht
    have hbase0 := scalar_path_differential_inequality (I := I)
      S hS hcomplete hcurv hR horigin hregular gamma ht
    have hbase : 0 ≤ dR t + R t / (t - origin) + coeff t * R t := by
      simpa [dR, R, coeff, speedSq, gradientAt, flowG] using hbase0
    have hclock : 0 < t - origin := sub_pos.mpr (horigin.trans ht.1)
    have hscaled := mul_nonneg hclock.le hbase
    calc
      q' t + coeff t * q t =
          (t - origin) * (dR t + R t / (t - origin) + coeff t * R t) := by
        change R t + (t - origin) * dR t + coeff t * ((t - origin) * R t) =
          (t - origin) * (dR t + R t / (t - origin) + coeff t * R t)
        field_simp [ne_of_gt hclock]
        ring
      _ ≥ 0 := hscaled
  have hend := exp_neg_intervalIntegral_mul_le_of_deriv_add_mul_nonneg
    htimes hqcont hcoeffCont hqderiv hqnonneg
  have hcoeffIntegral :
      intervalIntegral coeff t₁ t₂ MeasureTheory.volume =
        (1 / 4 : Real) *
          intervalIntegral speedSq t₁ t₂ MeasureTheory.volume := by
    simpa only [coeff] using
      intervalIntegral.integral_const_mul (1 / 4 : Real) speedSq
  have hden : 0 < t₂ - origin := sub_pos.mpr (horigin.trans htimes)
  change Real.exp (-intervalIntegral coeff t₁ t₂ MeasureTheory.volume) *
      ((t₁ - origin) * R t₁) ≤ (t₂ - origin) * R t₂ at hend
  have hdiv :
      (Real.exp (-intervalIntegral coeff t₁ t₂ MeasureTheory.volume) * q t₁) /
          (t₂ - origin) ≤ R t₂ := by
    apply (div_le_iff₀ hden).2
    change Real.exp (-intervalIntegral coeff t₁ t₂ MeasureTheory.volume) *
      ((t₁ - origin) * R t₁) ≤ R t₂ * (t₂ - origin)
    nlinarith [hend]
  calc
    (t₁ - origin) / (t₂ - origin) *
          Real.exp (-(1 / 4 : Real) *
            intervalIntegral speedSq t₁ t₂ MeasureTheory.volume) * R t₁ =
        (Real.exp (-intervalIntegral coeff t₁ t₂ MeasureTheory.volume) * q t₁) /
          (t₂ - origin) := by
      rw [hcoeffIntegral]
      simp only [q, Pi.mul_apply, neg_mul]
      field_simp [ne_of_gt hden]
    _ ≤ R t₂ := hdiv

theorem hamilton_trace_harnack_path_of_contMDiffOn
    [I.Boundaryless] [NeZero (Module.finrank Real E)]
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (hcomplete : ∀ t ∈ D.regular,
      RiemannianMetricComplete (I := I) (S.base.metric t))
    (hcurv : ∀ a b : Real, Set.Icc a b ⊆ D.regular →
      ∃ C : Real, ∀ t ∈ Set.Icc a b, ∀ x : M,
        normSq0S (I := I) (S.base.metric t) x 4 (S.base.rm04 t x) ≤ C)
    (hR : ∀ t ∈ D.regular, ∀ x : M,
      metricAlgebraicCurvatureTensorAt
        (I := I) (M := M) (S.base.metric t) x ∈
          algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    {origin t₁ t₂ : Real} (horigin : origin < t₁) (htimes : t₁ < t₂)
    (hregular : Set.Icc origin t₂ ⊆ D.regular)
    (gamma : Real → M)
    (hgamma : ContMDiffOn 𝓘(Real, Real) I 1 gamma (Set.Icc t₁ t₂)) :
    (t₁ - origin) / (t₂ - origin) *
        Real.exp (-(1 / 4 : Real) *
          intervalIntegral
            (fun t : Real =>
              (S.base.metric t).inner (gamma t)
                (mfderiv 𝓘(Real, Real) I gamma t (1 : Real))
                (mfderiv 𝓘(Real, Real) I gamma t (1 : Real)))
            t₁ t₂ MeasureTheory.volume) *
      S.scalar t₁ (gamma t₁) ≤ S.scalar t₂ (gamma t₂) := by
  have hpath := trace_harnack_path_within_of_contMDiffOn (I := I)
    S hS hcomplete hcurv hR horigin htimes hregular gamma hgamma
  rw [trace_path_energy_integral_within_eq (I := I) S htimes gamma] at hpath
  exact hpath

omit [SigmaCompactSpace M] in
private theorem trace_path_energy_intervalIntegrable_of_piecewiseContMDiffOn
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    {a b : Real} (hab : a < b)
    (hregular : Set.Icc a b ⊆ D.regular)
    (gamma : Real → M)
    (hgamma : PiecewiseContMDiffOn I 1 gamma a b) :
    IntervalIntegrable
      (fun t : Real =>
        (S.base.metric t).inner (gamma t)
          (mfderiv 𝓘(Real, Real) I gamma t (1 : Real))
          (mfderiv 𝓘(Real, Real) I gamma t (1 : Real)))
      MeasureTheory.volume a b := by
  revert hab hregular
  induction hgamma with
  | @of_contMDiffOn a b hgamma =>
      intro hab hregular
      have hwithinCont := path_speedSq_continuousOn (I := I)
        S hS hab hregular gamma hgamma
      have hwithinInt : IntervalIntegrable
          (fun t : Real =>
            (S.base.metric t).inner (gamma t)
              (mfderivWithin 𝓘(Real, Real) I gamma (Set.Icc a b) t (1 : Real))
              (mfderivWithin 𝓘(Real, Real) I gamma (Set.Icc a b) t (1 : Real)))
          MeasureTheory.volume a b :=
        ContinuousOn.intervalIntegrable_of_Icc hab.le hwithinCont
      apply hwithinInt.congr_uIoo
      intro t ht
      have ht' : t ∈ Set.Ioo a b := by
        simpa only [Set.uIoo_of_le hab.le] using ht
      have hv :
          mfderivWithin 𝓘(Real, Real) I gamma (Set.Icc a b) t =
            mfderiv 𝓘(Real, Real) I gamma t :=
        mfderivWithin_of_mem_nhds (Icc_mem_nhds ht'.1 ht'.2)
      simp only [hv]
  | @trans a b c hab hbc habgamma hbcgamma ihab ihbc =>
      intro _ hregular
      have hregularAB : Set.Icc a b ⊆ D.regular := by
        intro t ht
        exact hregular ⟨ht.1, ht.2.trans hbc.le⟩
      have hregularBC : Set.Icc b c ⊆ D.regular := by
        intro t ht
        exact hregular ⟨hab.le.trans ht.1, ht.2⟩
      exact IntervalIntegrable.trans
        (ihab hab hregularAB) (ihbc hbc hregularBC)

theorem hamilton_trace_harnack_path
    [I.Boundaryless] [NeZero (Module.finrank Real E)]
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (hcomplete : ∀ t ∈ D.regular,
      RiemannianMetricComplete (I := I) (S.base.metric t))
    (hcurv : ∀ a b : Real, Set.Icc a b ⊆ D.regular →
      ∃ C : Real, ∀ t ∈ Set.Icc a b, ∀ x : M,
        normSq0S (I := I) (S.base.metric t) x 4 (S.base.rm04 t x) ≤ C)
    (hR : ∀ t ∈ D.regular, ∀ x : M,
      metricAlgebraicCurvatureTensorAt
        (I := I) (M := M) (S.base.metric t) x ∈
          algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    {origin t₁ t₂ : Real} (horigin : origin < t₁) (htimes : t₁ < t₂)
    (hregular : Set.Icc origin t₂ ⊆ D.regular)
    (gamma : Real → M)
    (hgamma : PiecewiseContMDiffOn I 1 gamma t₁ t₂) :
    (t₁ - origin) / (t₂ - origin) *
        Real.exp (-(1 / 4 : Real) *
          intervalIntegral
            (fun t : Real =>
              (S.base.metric t).inner (gamma t)
                (mfderiv 𝓘(Real, Real) I gamma t (1 : Real))
                (mfderiv 𝓘(Real, Real) I gamma t (1 : Real)))
            t₁ t₂ MeasureTheory.volume) *
      S.scalar t₁ (gamma t₁) ≤ S.scalar t₂ (gamma t₂) := by
  revert horigin htimes hregular
  induction hgamma generalizing origin with
  | @of_contMDiffOn a b hgamma =>
      intro horigin htimes hregular
      exact hamilton_trace_harnack_path_of_contMDiffOn (I := I)
        S hS hcomplete hcurv hR horigin htimes hregular gamma hgamma
  | @trans a b c hab hbc habgamma hbcgamma ihab ihbc =>
      intro horigin _ hregular
      have hregularAB : Set.Icc origin b ⊆ D.regular := by
        intro t ht
        exact hregular ⟨ht.1, ht.2.trans hbc.le⟩
      have hregularBC : Set.Icc origin c ⊆ D.regular := hregular
      have hleft := ihab (origin := origin)
        horigin hab hregularAB
      have hright := ihbc (origin := origin)
        (horigin.trans hab) hbc hregularBC
      let energy : Real → Real := fun t =>
        (S.base.metric t).inner (gamma t)
          (mfderiv 𝓘(Real, Real) I gamma t (1 : Real))
          (mfderiv 𝓘(Real, Real) I gamma t (1 : Real))
      change (a - origin) / (b - origin) *
          Real.exp (-(1 / 4 : Real) *
            intervalIntegral energy a b MeasureTheory.volume) *
        S.scalar a (gamma a) ≤ S.scalar b (gamma b) at hleft
      change (b - origin) / (c - origin) *
          Real.exp (-(1 / 4 : Real) *
            intervalIntegral energy b c MeasureTheory.volume) *
        S.scalar b (gamma b) ≤ S.scalar c (gamma c) at hright
      change (a - origin) / (c - origin) *
          Real.exp (-(1 / 4 : Real) *
            intervalIntegral energy a c MeasureTheory.volume) *
        S.scalar a (gamma a) ≤ S.scalar c (gamma c)
      have hregularPieceAB : Set.Icc a b ⊆ D.regular := by
        intro t ht
        exact hregular ⟨horigin.le.trans ht.1, ht.2.trans hbc.le⟩
      have hregularPieceBC : Set.Icc b c ⊆ D.regular := by
        intro t ht
        exact hregular ⟨horigin.le.trans (hab.le.trans ht.1), ht.2⟩
      have hIntAB := trace_path_energy_intervalIntegrable_of_piecewiseContMDiffOn
        (I := I) S hS hab hregularPieceAB gamma habgamma
      have hIntBC := trace_path_energy_intervalIntegrable_of_piecewiseContMDiffOn
        (I := I) S hS hbc hregularPieceBC gamma hbcgamma
      change IntervalIntegrable energy MeasureTheory.volume a b at hIntAB
      change IntervalIntegrable energy MeasureTheory.volume b c at hIntBC
      have henergyAdd :=
        intervalIntegral.integral_add_adjacent_intervals hIntAB hIntBC
      have hbpos : 0 < b - origin := sub_pos.mpr (horigin.trans hab)
      have hcpos : 0 < c - origin :=
        sub_pos.mpr (horigin.trans (hab.trans hbc))
      have hfactor : 0 ≤
          (b - origin) / (c - origin) *
            Real.exp (-(1 / 4 : Real) *
              intervalIntegral energy b c MeasureTheory.volume) :=
        mul_nonneg (div_nonneg hbpos.le hcpos.le) (Real.exp_pos _).le
      calc
        (a - origin) / (c - origin) *
              Real.exp (-(1 / 4 : Real) *
                intervalIntegral energy a c MeasureTheory.volume) *
            S.scalar a (gamma a) =
            ((b - origin) / (c - origin) *
              Real.exp (-(1 / 4 : Real) *
                intervalIntegral energy b c MeasureTheory.volume)) *
              ((a - origin) / (b - origin) *
                Real.exp (-(1 / 4 : Real) *
                  intervalIntegral energy a b MeasureTheory.volume) *
                S.scalar a (gamma a)) := by
          rw [← henergyAdd, mul_add, Real.exp_add]
          field_simp [ne_of_gt hbpos, ne_of_gt hcpos]
        _ ≤ ((b - origin) / (c - origin) *
              Real.exp (-(1 / 4 : Real) *
                intervalIntegral energy b c MeasureTheory.volume)) *
            S.scalar b (gamma b) :=
          mul_le_mul_of_nonneg_left hleft hfactor
        _ ≤ S.scalar c (gamma c) := hright

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem hamilton_trace_harnack_distance
    [I.Boundaryless] [NeZero (Module.finrank Real E)]
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (hcomplete : ∀ t ∈ D.regular,
      RiemannianMetricComplete (I := I) (S.base.metric t))
    (hcurv : ∀ a b : Real, Set.Icc a b ⊆ D.regular →
      ∃ C : Real, ∀ t ∈ Set.Icc a b, ∀ x : M,
        normSq0S (I := I) (S.base.metric t) x 4 (S.base.rm04 t x) ≤ C)
    (hR : ∀ t ∈ D.regular, ∀ x : M,
      metricAlgebraicCurvatureTensorAt
        (I := I) (M := M) (S.base.metric t) x ∈
          algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    {origin t₁ t₂ : Real} (horigin : origin < t₁) (htimes : t₁ < t₂)
    (hregular : Set.Icc origin t₂ ⊆ D.regular)
    (x y : M) (hy : y ∈ connectedComponent x) :
    (t₁ - origin) / (t₂ - origin) *
        Real.exp
          (-((riemannianEDistOf (I := I) (S.base.metric t₁) x y).toReal ^ 2 /
            (4 * (t₂ - t₁)))) *
      S.scalar t₁ x ≤ S.scalar t₂ y := by
  classical
  let g := S.base.metric t₁
  have ht₁reg : t₁ ∈ D.regular :=
    hregular ⟨horigin.le, htimes.le⟩
  have hfin : riemannianEDistOf (I := I) g x y ≠ (⊤ : ENNReal) := by
    let : LocallyConnectedSpace H := I.toHomeomorph.locallyConnectedSpace
    let : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace H M
    let O : TopologicalSpace.Opens M :=
      ⟨connectedComponent x, isOpen_connectedComponent⟩
    let xO : O := ⟨x, mem_connectedComponent⟩
    let yO : O := ⟨y, hy⟩
    let : SigmaCompactSpace O := isClosed_connectedComponent.sigmaCompactSpace
    let : ConnectedSpace O :=
      isConnected_iff_connectedSpace.mp isConnected_connectedComponent
    let gO := g.restrictOpen (I := I) O
    let : RiemannianBundle (fun z : O => TangentSpace I z) :=
      ⟨gO.toRiemannianMetric⟩
    let : IsContinuousRiemannianBundle E (fun z : O => TangentSpace I z) :=
      ⟨⟨gO.inner, gO.contMDiff.continuous, by intro z v w; rfl⟩⟩
    have hOFin : riemannianEDistOf (I := I) gO xO yO ≠ (⊤ : ENNReal) := by
      simpa only [riemannianEDistOf] using
        (DifferentialGeometry.Geometry.Riemannian.Exponential.riemannianEDist_ne_top
          (I := I) xO yO)
    have hle : riemannianEDistOf (I := I) g x y ≤
        riemannianEDistOf (I := I) gO xO yO := by
      simpa only [gO, xO, yO] using
        (riemannianEDistOf_le_restrictOpen (I := I) g O xO yO)
    intro htop
    apply hOFin
    apply top_unique
    simpa only [htop] using hle
  let : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let : T3Space M := inferInstance
  let : RiemannianBundle (fun z : M => TangentSpace I z) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun z : M => TangentSpace I z) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro z v w; rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  let : PseudoEMetricSpace M :=
    (EMetricSpace.ofRiemannianMetric I M).toPseudoEMetricSpace
  let : CompleteSpace M := (hcomplete t₁ ht₁reg).complete
  have hEnorm : DifferentialGeometry.Geometry.Riemannian.IsMetricNorm
      (I := I) (M := M) g := by
    intro z v
    exact
      DifferentialGeometry.Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm
        (I := I) g z v
  have hfin' : Manifold.riemannianEDist I x y ≠ (⊤ : ENNReal) := by
    simpa only [g, riemannianEDistOf] using hfin
  obtain ⟨v, hvExp, hvLen⟩ :=
    DifferentialGeometry.Geometry.Riemannian.Exponential.minExp_of_ne_top
      (I := I) g hEnorm x y hfin'
  let d := (riemannianEDistOf (I := I) g x y).toReal
  let delta := t₂ - t₁
  have hdelta : 0 < delta := by
    simpa only [delta] using sub_pos.mpr htimes
  have hvLen' : Real.sqrt (g.inner x v v) = d := by
    simpa only [d, g, riemannianEDistOf] using hvLen
  have hvSq : g.inner x v v = d ^ 2 := by
    calc
      g.inner x v v = Real.sqrt (g.inner x v v) ^ 2 :=
        (Real.sq_sqrt
          (DifferentialGeometry.Geometry.Riemannian.Exponential.gInner_self_nonneg
            (I := I) g x v)).symm
      _ = d ^ 2 := by rw [hvLen']
  let u : TangentSpace I x := delta⁻¹ • v
  let eta : Real → M :=
    DifferentialGeometry.Geometry.Riemannian.Exponential.intrinsicGeodesic
      (I := I) g hEnorm x u
  let gamma : Real → M := fun t => eta (t - t₁)
  have heta : ContMDiff 𝓘(Real, Real) I 1 eta := by
    exact contMDiffOn_univ.mp
      (DifferentialGeometry.Geometry.Riemannian.Exponential.intrinsicGeodesic_contMDiffOn
        (I := I) g hEnorm x u)
  have hshift : ContMDiff 𝓘(Real, Real) 𝓘(Real, Real) 1
      (fun t : Real => t - t₁) :=
    contMDiff_id.sub contMDiff_const
  have hgammaAll : ContMDiff 𝓘(Real, Real) I 1 gamma := by
    exact heta.comp hshift
  have hgamma : ContMDiffOn 𝓘(Real, Real) I 1 gamma
      (Set.Icc t₁ t₂) := hgammaAll.contMDiffOn
  have hgamma₁ : gamma t₁ = x := by
    simp only [gamma, sub_self]
    dsimp only [eta]
    exact DifferentialGeometry.Geometry.Riemannian.Exponential.intrinsicGeodesic_zero
      (I := I) g hEnorm x u
  have hgamma₂ : gamma t₂ = y := by
    calc
      gamma t₂ =
          DifferentialGeometry.Geometry.Riemannian.Exponential.intrinsicGeodesic
            (I := I) g hEnorm x (delta⁻¹ • v) delta := by rfl
      _ = DifferentialGeometry.Geometry.Riemannian.Exponential.intrinsicGeodesic
            (I := I) g hEnorm x v (delta⁻¹ * delta) :=
        DifferentialGeometry.Geometry.Riemannian.Exponential.intrinsicGeo_smul_apply
          (I := I) g hEnorm x v delta⁻¹ delta
      _ = DifferentialGeometry.Geometry.Riemannian.Exponential.intrinsicGeodesic
            (I := I) g hEnorm x v 1 := by
        rw [inv_mul_cancel₀ hdelta.ne']
      _ = y := by
        rw [← DifferentialGeometry.Geometry.Riemannian.Exponential.expMapIntrinsic_def]
        exact hvExp
  have hshiftDeriv : ∀ t : Real,
      mfderiv 𝓘(Real, Real) 𝓘(Real, Real) (fun s : Real => s - t₁) t
          (DifferentialGeometry.Analysis.Calculus.realTangentOne t) =
        DifferentialGeometry.Analysis.Calculus.realTangentOne (t - t₁) := by
    intro t
    apply (NormedSpace.fromTangentSpace (𝕜 := Real) (t - t₁)).injective
    rw [DifferentialGeometry.Analysis.Calculus.fromTangentSpace_realTangentOne]
    rw [mfderiv_eq_fderiv]
    change (fderiv Real (fun s : Real => s - t₁) t)
        (NormedSpace.fromTangentSpace (𝕜 := Real) t
          (DifferentialGeometry.Analysis.Calculus.realTangentOne t)) = 1
    rw [DifferentialGeometry.Analysis.Calculus.fromTangentSpace_realTangentOne]
    have hfd : fderiv Real (fun s : Real => s - t₁) t =
        ContinuousLinearMap.id Real Real := by
      simpa only [id_eq] using ((hasFDerivAt_id t).sub_const t₁).fderiv
    rw [hfd]
    rfl
  have hgammaVel : ∀ t : Real,
      mfderiv 𝓘(Real, Real) I gamma t
          (DifferentialGeometry.Analysis.Calculus.realTangentOne t) =
        mfderiv 𝓘(Real, Real) I eta (t - t₁)
          (DifferentialGeometry.Analysis.Calculus.realTangentOne (t - t₁)) := by
    intro t
    have hcomp := mfderiv_comp_apply
      (I := 𝓘(Real, Real)) (I' := 𝓘(Real, Real)) (I'' := I)
      (g := eta) (f := fun s : Real => s - t₁) (x := t)
      (heta.mdifferentiableAt (by norm_num))
      (hshift.mdifferentiableAt (by norm_num))
        (DifferentialGeometry.Analysis.Calculus.realTangentOne t)
    change mfderiv 𝓘(Real, Real) I
        (eta ∘ fun s : Real => s - t₁) t (1 : Real) = _ at hcomp
    change mfderiv 𝓘(Real, Real) I
        (eta ∘ fun s : Real => s - t₁) t (1 : Real) = _
    rw [hcomp, hshiftDeriv]
  have hspeed : ∀ t : Real,
      g.inner (gamma t)
          (mfderiv 𝓘(Real, Real) I gamma t
            (DifferentialGeometry.Analysis.Calculus.realTangentOne t))
          (mfderiv 𝓘(Real, Real) I gamma t
            (DifferentialGeometry.Analysis.Calculus.realTangentOne t)) =
        (d / delta) ^ 2 := by
    intro t
    rw [hgammaVel]
    have huSq : g.inner x u u = (d / delta) ^ 2 := by
      rw [show g.inner x u u = delta⁻¹ ^ 2 * g.inner x v v by
      exact DifferentialGeometry.Geometry.Riemannian.Exponential.gInner_smul_self
        (I := I) g x delta⁻¹ v]
      rw [hvSq]
      field_simp [hdelta.ne']
    have hspeedEta :=
      DifferentialGeometry.Geometry.Riemannian.Exponential.intrinsicGeodesic_speedSq_eq
        (I := I) g hEnorm x u (t - t₁)
    dsimp only [gamma, eta]
    with_unfolding_all exact hspeedEta.trans huSq
  have hspeed' : ∀ t : Real,
      g.inner (gamma t)
          (mfderiv 𝓘(Real, Real) I gamma t (1 : Real))
          (mfderiv 𝓘(Real, Real) I gamma t (1 : Real)) =
        (d / delta) ^ 2 := by
    intro t
    with_unfolding_all exact hspeed t
  have hpathRegular : Set.Icc t₁ t₂ ⊆ D.regular := by
    intro t ht
    exact hregular ⟨horigin.le.trans ht.1, ht.2⟩
  have hRic : ∀ t ∈ Set.Icc t₁ t₂, ∀ z : M,
      ∀ w : TangentSpace I z,
        0 ≤ ricciTensor (I := I) (S.base.metric t) z w w := by
    intro t ht z w
    simpa only [← metricRicciAt_apply_eq_ricciTensor] using
      metricRicciAt_nonnegative_of_curvatureOperator_nonnegative
        (I := I) (M := M) (S.base.metric t) z (hR t (hpathRegular ht) z) w
  have hcarrier : Set.Icc t₁ t₂ ⊆ D.carrier := by
    intro t ht
    exact D.regular_subset (hpathRegular ht)
  have hmetricAnti := metric_inner_antitoneOn_of_ricci_nonnegative
    (I := I) S hS htimes hcarrier
      (fun t ht => hpathRegular ⟨ht.1.le, ht.2⟩) hRic
  let energy : Real → Real := fun t =>
    (S.base.metric t).inner (gamma t)
      (mfderiv 𝓘(Real, Real) I gamma t (1 : Real))
      (mfderiv 𝓘(Real, Real) I gamma t (1 : Real))
  have henergyPoint : ∀ t ∈ Set.Icc t₁ t₂,
      energy t ≤ (d / delta) ^ 2 := by
    intro t ht
    calc
      energy t ≤
          g.inner (gamma t)
            (mfderiv 𝓘(Real, Real) I gamma t (1 : Real))
            (mfderiv 𝓘(Real, Real) I gamma t (1 : Real)) := by
        exact hmetricAnti (gamma t)
          (mfderiv 𝓘(Real, Real) I gamma t (1 : Real))
          ⟨le_rfl, htimes.le⟩ ht ht.1
      _ = (d / delta) ^ 2 := hspeed' t
  have henergyInt : IntervalIntegrable energy MeasureTheory.volume t₁ t₂ := by
    exact trace_path_energy_intervalIntegrable_of_piecewiseContMDiffOn
      (I := I) S hS htimes hpathRegular gamma
        (.of_contMDiffOn hgamma)
  have hconstInt : IntervalIntegrable (fun _ : Real => (d / delta) ^ 2)
      MeasureTheory.volume t₁ t₂ := intervalIntegrable_const
  have henergyIntegral :
      intervalIntegral energy t₁ t₂ MeasureTheory.volume ≤ d ^ 2 / delta := by
    calc
      intervalIntegral energy t₁ t₂ MeasureTheory.volume ≤
          intervalIntegral (fun _ : Real => (d / delta) ^ 2)
            t₁ t₂ MeasureTheory.volume :=
        intervalIntegral.integral_mono_on htimes.le henergyInt hconstInt henergyPoint
      _ = d ^ 2 / delta := by
        rw [intervalIntegral.integral_const]
        simp only [smul_eq_mul]
        dsimp only [delta]
        field_simp [sub_ne_zero.mpr htimes.ne']
  have hpath := hamilton_trace_harnack_path_of_contMDiffOn (I := I)
    S hS hcomplete hcurv hR horigin htimes hregular gamma hgamma
  change (t₁ - origin) / (t₂ - origin) *
      Real.exp (-(1 / 4 : Real) *
        intervalIntegral energy t₁ t₂ MeasureTheory.volume) *
      S.scalar t₁ (gamma t₁) ≤ S.scalar t₂ (gamma t₂) at hpath
  rw [hgamma₁, hgamma₂] at hpath
  obtain ⟨basis, hON⟩ := exists_orthonormal_basis (I := I) g x
  let i₀ : Fin (Module.finrank Real (TangentSpace I x)) :=
    ⟨0, by
      change 0 < Module.finrank Real E
      exact Nat.pos_of_ne_zero (NeZero.ne (Module.finrank Real E))⟩
  have hRicUnit := metricRicciAt_nonnegative_of_curvatureOperator_nonnegative
    (I := I) (M := M) g x (hR t₁ ht₁reg x) (basis i₀)
  have hRicUpper :=
    metricRicciAt_le_half_scalar_mul_inner_of_curvatureOperator_nonnegative
      (I := I) (M := M) g x (hR t₁ ht₁reg x) (basis i₀)
  have hscalarMetric : 0 ≤ metricScalarAt (I := I) (M := M) g x := by
    rw [hON i₀ i₀, if_pos rfl, mul_one] at hRicUpper
    nlinarith
  have hscalar : 0 ≤ S.scalar t₁ x := by
    change 0 ≤ metricScalarAt (I := I) (M := M) (S.base.metric t₁) x
    simpa only [g] using hscalarMetric
  have hexp :
      Real.exp (-(d ^ 2 / (4 * delta))) ≤
        Real.exp (-(1 / 4 : Real) *
          intervalIntegral energy t₁ t₂ MeasureTheory.volume) := by
    apply Real.exp_le_exp.mpr
    calc
      -(d ^ 2 / (4 * delta)) = -(1 / 4 : Real) * (d ^ 2 / delta) := by
        field_simp [hdelta.ne']
      _ ≤ -(1 / 4 : Real) *
          intervalIntegral energy t₁ t₂ MeasureTheory.volume := by
        nlinarith
  have hratio : 0 ≤ (t₁ - origin) / (t₂ - origin) :=
    div_nonneg (sub_pos.mpr horigin).le
      (sub_pos.mpr (horigin.trans htimes)).le
  calc
    (t₁ - origin) / (t₂ - origin) *
          Real.exp
            (-((riemannianEDistOf (I := I) (S.base.metric t₁) x y).toReal ^ 2 /
              (4 * (t₂ - t₁)))) *
        S.scalar t₁ x =
        (t₁ - origin) / (t₂ - origin) *
          Real.exp (-(d ^ 2 / (4 * delta))) * S.scalar t₁ x := by
      rfl
    _ ≤ (t₁ - origin) / (t₂ - origin) *
          Real.exp (-(1 / 4 : Real) *
            intervalIntegral energy t₁ t₂ MeasureTheory.volume) *
        S.scalar t₁ x :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hexp hratio) hscalar
    _ ≤ S.scalar t₂ y := hpath

theorem hamilton_trace_ricci_kernel_annihilation_at
    [I.Boundaryless] [NeZero (Module.finrank Real E)]
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (hcomplete : ∀ t ∈ D.regular,
      RiemannianMetricComplete (I := I) (S.base.metric t))
    (hcurv : ∀ a b : Real, Set.Icc a b ⊆ D.regular →
      ∃ C : Real, ∀ t ∈ Set.Icc a b, ∀ x : M,
        normSq0S (I := I) (S.base.metric t) x 4 (S.base.rm04 t x) ≤ C)
    (hR : ∀ t ∈ D.regular, ∀ x : M,
      metricAlgebraicCurvatureTensorAt
        (I := I) (M := M) (S.base.metric t) x ∈
          algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    (clock : HarnackClock)
    (hclock : Set.Icc clock.origin clock.time ⊆ D.regular)
    (x : M) (Z : TangentSpace I x)
    (hZ : ∀ W : TangentSpace I x,
      metricRicci (I := I) (M := M) (S.base.metric clock.time) x
        (vec2 Z W) = 0) :
    (S.base.metric clock.time).inner x
      (gradientAt (I := I) (flowG (I := I) S) clock.time
        (S.scalar clock.time) x) Z = 0 := by
  let c := deriv (fun s : Real => S.scalar s x) clock.time +
    S.scalar clock.time x / clock.elapsed
  let p := (S.base.metric clock.time).inner x
    (gradientAt (I := I) (flowG (I := I) S) clock.time
      (S.scalar clock.time) x) Z
  have hbound : ∀ s : Real, 0 ≤ c + 2 * s * p := by
    intro s
    have htrace := hamilton_trace_harnack (I := I) S hS hcomplete hcurv hR
      clock hclock x (s • Z)
    have hinner :
        (S.base.metric clock.time).inner x
          (gradientAt (I := I) (flowG (I := I) S) clock.time
            (S.scalar clock.time) x) (s • Z) = s * p := by
      rw [map_smul]
      simp [p, smul_eq_mul]
    have hric :
        metricRicci (I := I) (M := M) (S.base.metric clock.time) x
          (vec2 (s • Z) (s • Z)) = 0 := by
      have hscale := tensor02_smul2 (I := I) (M := M)
        (metricRicci (I := I) (M := M) (S.base.metric clock.time) x) s Z Z
      calc
        metricRicci (I := I) (M := M) (S.base.metric clock.time) x
            (vec2 (s • Z) (s • Z)) =
            s ^ 2 * metricRicci (I := I) (M := M)
              (S.base.metric clock.time) x (vec2 Z Z) := hscale
        _ = 0 := by rw [hZ Z]; ring
    rw [hinner, hric] at htrace
    simpa [c, mul_assoc] using htrace
  by_contra hp
  have hp' : p ≠ 0 := by simpa [p] using hp
  let s := -(c + 1) / (2 * p)
  have hs := hbound s
  have hsval : c + 2 * s * p = -1 := by
    dsimp [s]
    field_simp [hp']
    ring
  rw [hsval] at hs
  linarith

theorem hamilton_trace_harnack_optimized
    [I.Boundaryless] [NeZero (Module.finrank Real E)]
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (hcomplete : ∀ t ∈ D.regular,
      RiemannianMetricComplete (I := I) (S.base.metric t))
    (hcurv : ∀ a b : Real, Set.Icc a b ⊆ D.regular →
      ∃ C : Real, ∀ t ∈ Set.Icc a b, ∀ x : M,
        normSq0S (I := I) (S.base.metric t) x 4 (S.base.rm04 t x) ≤ C)
    (hR : ∀ t ∈ D.regular, ∀ x : M,
      metricAlgebraicCurvatureTensorAt
        (I := I) (M := M) (S.base.metric t) x ∈
          algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    (clock : HarnackClock)
    (hclock : Set.Icc clock.origin clock.time ⊆ D.regular)
    (x : M) :
    ∃ Y : TangentSpace I x,
      (∀ Z : TangentSpace I x,
        metricRicci (I := I) (M := M) (S.base.metric clock.time) x
            (vec2 Y Z) =
          (S.base.metric clock.time).inner x
            (gradientAt (I := I) (flowG (I := I) S) clock.time
              (S.scalar clock.time) x) Z) ∧
      (∀ Z : TangentSpace I x,
        (∀ W : TangentSpace I x,
          metricRicci (I := I) (M := M) (S.base.metric clock.time) x
              (vec2 Z W) =
            (S.base.metric clock.time).inner x
              (gradientAt (I := I) (flowG (I := I) S) clock.time
                (S.scalar clock.time) x) W) →
        metricRicci (I := I) (M := M) (S.base.metric clock.time) x
            (vec2 Z Z) =
          metricRicci (I := I) (M := M) (S.base.metric clock.time) x
            (vec2 Y Y)) ∧
      0 ≤ deriv (fun s : Real => S.scalar s x) clock.time +
          S.scalar clock.time x / clock.elapsed -
        (1 / 2 : Real) *
          metricRicci (I := I) (M := M) (S.base.metric clock.time) x
            (vec2 Y Y) := by
  classical
  let g := S.base.metric clock.time
  let gradR := gradientAt (I := I) (flowG (I := I) S) clock.time
    (S.scalar clock.time) x
  let RicT := metricRicci (I := I) (M := M) g x
  obtain ⟨basis, hON⟩ := exists_orthonormal_basis (I := I) g x
  let Ric : Fin (Module.finrank Real (TangentSpace I x)) →
      Fin (Module.finrank Real (TangentSpace I x)) → Real :=
    fun a b => RicT (vec2 (basis a) (basis b))
  let dR : Fin (Module.finrank Real (TangentSpace I x)) → Real :=
    fun a => g.inner x gradR (basis a)
  let c := deriv (fun s : Real => S.scalar s x) clock.time +
    S.scalar clock.time x / clock.elapsed
  have hpair (z : Fin (Module.finrank Real (TangentSpace I x)) → Real) :
      ricciCovectorPairing dR z =
        g.inner x gradR (basis.equivFun.symm z) := by
    let V := basis.equivFun.symm z
    have hrepr : ∀ a, basis.repr V a = z a := by
      intro a
      have h := congrFun (basis.equivFun.apply_symm_apply z) a
      simpa only [Module.Basis.equivFun_apply] using h
    have hsum : ∑ a, z a • basis a = V := by
      rw [← basis.sum_repr V]
      apply Finset.sum_congr rfl
      intro a _
      rw [hrepr]
    calc
      ricciCovectorPairing dR z =
          ∑ a, z a * g.inner x gradR (basis a) := by
        unfold ricciCovectorPairing
        apply Finset.sum_congr rfl
        intro a _
        simp only [dR]
        ring
      _ = g.inner x gradR (∑ a, z a • basis a) := by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro a _
        rw [map_smul]
        simp [smul_eq_mul]
      _ = g.inner x gradR V := by rw [hsum]
  have hquad (z : Fin (Module.finrank Real (TangentSpace I x)) → Real) :
      ricciQuadratic Ric z =
        RicT (vec2 (basis.equivFun.symm z) (basis.equivFun.symm z)) := by
    have hrepr : ∀ a, basis.repr (basis.equivFun.symm z) a = z a := by
      intro a
      have h := congrFun (basis.equivFun.apply_symm_apply z) a
      simpa only [Module.Basis.equivFun_apply] using h
    unfold ricciQuadratic
    symm
    rw [tensor02_apply_eq_coordinate_sum (I := I) basis RicT]
    simp only [Ric]
    simp_rw [hrepr]
  have htraceCoordinates : ∀ z, 0 ≤ c +
      2 * ricciCovectorPairing dR z + 2 * ricciQuadratic Ric z := by
    intro z
    have htrace := hamilton_trace_harnack (I := I) S hS hcomplete hcurv hR
      clock hclock x (basis.equivFun.symm z)
    change 0 ≤ c +
      2 * g.inner x gradR (basis.equivFun.symm z) +
      2 * RicT (vec2 (basis.equivFun.symm z) (basis.equivFun.symm z)) at htrace
    rw [← hpair z, ← hquad z] at htrace
    exact htrace
  have hsym : ∀ a b, Ric a b = Ric b a := by
    intro a b
    exact metricRicciAt_symm (I := I) g x (basis a) (basis b)
  obtain ⟨Yc, hYc, hchoice, hoptimized⟩ :=
    hamilton_trace_semidefinite_optimized_of_symmetric c Ric dR hsym htraceCoordinates
  let Y := basis.equivFun.symm Yc
  have hYrepr : ∀ a, basis.repr Y a = Yc a := by
    intro a
    have h := congrFun (basis.equivFun.apply_symm_apply Yc) a
    simpa only [Y, Module.Basis.equivFun_apply] using h
  have hproducer : ∀ Z : TangentSpace I x,
      RicT (vec2 Y Z) = g.inner x gradR Z := by
    intro Z
    calc
      RicT (vec2 Y Z) = RicT (vec2 Z Y) :=
        metricRicciAt_symm (I := I) g x Y Z
      _ = ∑ a, ∑ b, Ric a b * basis.repr Z a * Yc b := by
        rw [tensor02_apply_eq_coordinate_sum (I := I) basis RicT]
        simp only [Ric]
        simp_rw [hYrepr]
      _ = ∑ a, dR a * basis.repr Z a := by
        apply Finset.sum_congr rfl
        intro a _
        calc
          ∑ b, Ric a b * basis.repr Z a * Yc b =
              (∑ b, Ric a b * Yc b) * basis.repr Z a := by
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro b _
            ring
          _ = dR a * basis.repr Z a := by rw [hYc a]
      _ = ricciCovectorPairing dR (basis.equivFun Z) := by
        unfold ricciCovectorPairing
        simp only [Module.Basis.equivFun_apply]
      _ = g.inner x gradR Z := by
        simpa using hpair (basis.equivFun Z)
  refine ⟨Y, ?_, ?_, ?_⟩
  · intro Z
    simpa only [g, gradR, RicT] using hproducer Z
  · intro Z hZ
    have hZc : ∀ a, ∑ b, Ric a b * basis.repr Z b = dR a := by
      intro a
      calc
        ∑ b, Ric a b * basis.repr Z b = RicT (vec2 (basis a) Z) := by
          symm
          simpa only [Ric] using
            tensor02_apply_basis_left_eq_sum (I := I) basis RicT a Z
        _ = RicT (vec2 Z (basis a)) :=
          metricRicciAt_symm (I := I) g x (basis a) Z
        _ = g.inner x gradR (basis a) := by
          simpa only [g, gradR, RicT] using hZ (basis a)
        _ = dR a := rfl
    have hcoord := hchoice (fun a => basis.repr Z a) hZc
    have hquadZ : ricciQuadratic Ric (fun a => basis.repr Z a) =
        RicT (vec2 Z Z) := by
      simpa using hquad (basis.equivFun Z)
    have hquadY : ricciQuadratic Ric Yc = RicT (vec2 Y Y) := by
      simpa only [Y] using hquad Yc
    have hvalue : RicT (vec2 Z Z) = RicT (vec2 Y Y) :=
      hquadZ.symm.trans (hcoord.trans hquadY)
    simpa only [g, RicT] using hvalue
  · have hquadY : ricciQuadratic Ric Yc = RicT (vec2 Y Y) := by
      simpa only [Y] using hquad Yc
    rw [hquadY] at hoptimized
    simpa only [c, g, RicT] using hoptimized

theorem hamilton_ancient_trace_harnack
    [I.Boundaryless] [NeZero (Module.finrank Real E)]
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (hcomplete : ∀ t ∈ D.regular,
      RiemannianMetricComplete (I := I) (S.base.metric t))
    (hcurv : ∀ a b : Real, Set.Icc a b ⊆ D.regular →
      ∃ C : Real, ∀ t ∈ Set.Icc a b, ∀ x : M,
        normSq0S (I := I) (S.base.metric t) x 4 (S.base.rm04 t x) ≤ C)
    (hR : ∀ t ∈ D.regular, ∀ x : M,
      metricAlgebraicCurvatureTensorAt
        (I := I) (M := M) (S.base.metric t) x ∈
          algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    {t : Real} (hregular : Set.Iic t ⊆ D.regular)
    (x : M) (V : TangentSpace I x) :
    0 ≤ deriv (fun s : Real => S.scalar s x) t +
      2 * (S.base.metric t).inner x
        (gradientAt (I := I) (flowG (I := I) S) t
          (S.scalar t) x) V +
      2 * metricRicci (I := I) (M := M) (S.base.metric t) x
        (vec2 V V) := by
  have hscalarMetric :=
    metricScalarAt_nonnegative_of_curvatureOperator_nonnegative
      (I := I) (M := M) (S.base.metric t) x
      (hR t (hregular (Set.mem_Iic.mpr le_rfl)) x)
  have hscalar : 0 ≤ S.scalar t x := by
    change 0 ≤ metricScalarAt (I := I) (M := M) (S.base.metric t) x
    exact hscalarMetric
  have hlimit := hamilton_ancient_trace_expression_nonneg
    (dR := deriv (fun s : Real => S.scalar s x) t)
    (R := S.scalar t x)
    (b := 2 * (S.base.metric t).inner x
      (gradientAt (I := I) (flowG (I := I) S) t
        (S.scalar t) x) V +
      2 * metricRicci (I := I) (M := M) (S.base.metric t) x
        (vec2 V V))
    (t := t)
    (hshift := by
      intro origin horigin
      let clock : HarnackClock := ⟨origin, t, horigin⟩
      have hclock : Set.Icc origin t ⊆ D.regular := by
        intro s hs
        exact hregular hs.2
      have htrace := hamilton_trace_harnack (I := I)
        S hS hcomplete hcurv hR clock hclock x V
      simpa only [clock, HarnackClock.elapsed, add_assoc] using htrace)
    (hR := hscalar)
  simpa only [add_assoc] using hlimit

theorem hamilton_ancient_scalar_deriv_nonneg
    [I.Boundaryless] [NeZero (Module.finrank Real E)]
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (hcomplete : ∀ t ∈ D.regular,
      RiemannianMetricComplete (I := I) (S.base.metric t))
    (hcurv : ∀ a b : Real, Set.Icc a b ⊆ D.regular →
      ∃ C : Real, ∀ t ∈ Set.Icc a b, ∀ x : M,
        normSq0S (I := I) (S.base.metric t) x 4 (S.base.rm04 t x) ≤ C)
    (hR : ∀ t ∈ D.regular, ∀ x : M,
      metricAlgebraicCurvatureTensorAt
        (I := I) (M := M) (S.base.metric t) x ∈
          algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    {t : Real} (hregular : Set.Iic t ⊆ D.regular) (x : M) :
    0 ≤ deriv (fun s : Real => S.scalar s x) t := by
  have htrace := hamilton_ancient_trace_harnack (I := I)
    S hS hcomplete hcurv hR hregular x (0 : TangentSpace I x)
  have hRicZero :
      metricRicci (I := I) (M := M) (S.base.metric t) x
        (vec2 (0 : TangentSpace I x) 0) = 0 := by
    exact (metricRicci (I := I) (M := M) (S.base.metric t) x).map_coord_zero
      (i := 0) (by simp [vec2])
  rw [hRicZero] at htrace
  simpa using htrace

theorem hamilton_ancient_scalar_monotoneOn
    [I.Boundaryless] [NeZero (Module.finrank Real E)]
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (hcomplete : ∀ t ∈ D.regular,
      RiemannianMetricComplete (I := I) (S.base.metric t))
    (hcurv : ∀ a b : Real, Set.Icc a b ⊆ D.regular →
      ∃ C : Real, ∀ t ∈ Set.Icc a b, ∀ x : M,
        normSq0S (I := I) (S.base.metric t) x 4 (S.base.rm04 t x) ≤ C)
    (hR : ∀ t ∈ D.regular, ∀ x : M,
      metricAlgebraicCurvatureTensorAt
        (I := I) (M := M) (S.base.metric t) x ∈
          algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    {a b : Real} (hregular : Set.Iic b ⊆ D.regular) (x : M) :
    MonotoneOn (fun s : Real => S.scalar s x) (Set.Icc a b) := by
  have hscalarCont : ContinuousOn (fun s : Real => S.scalar s x)
      (Set.Icc a b) := by
    have hmap : Continuous (fun s : Real => (s, x)) :=
      continuous_id.prodMk continuous_const
    have hcomp := hS.scalarCont.comp hmap.continuousOn
      (fun s (hs : s ∈ Set.Icc a b) =>
        ⟨D.regular_subset (hregular hs.2), Set.mem_univ x⟩)
    simpa [Function.comp_def] using hcomp
  apply monotoneOn_of_hamilton_ancient_scalar_trace
    (R := fun s : Real => S.scalar s x)
    (dR := fun s : Real => deriv (fun r : Real => S.scalar r x) s)
    hscalarCont
  · intro s hs
    exact scalar_hasDerivAt_of_regular (I := I) S hS
      (hregular hs.2.le) x
  · intro s hs
    apply hamilton_ancient_scalar_deriv_nonneg (I := I)
      S hS hcomplete hcurv hR
    intro r hr
    exact hregular (hr.trans hs.2.le)

theorem hamilton_ancient_scalar_two_time
    [I.Boundaryless] [NeZero (Module.finrank Real E)]
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (hcomplete : ∀ t ∈ D.regular,
      RiemannianMetricComplete (I := I) (S.base.metric t))
    (hcurv : ∀ a b : Real, Set.Icc a b ⊆ D.regular →
      ∃ C : Real, ∀ t ∈ Set.Icc a b, ∀ x : M,
        normSq0S (I := I) (S.base.metric t) x 4 (S.base.rm04 t x) ≤ C)
    (hR : ∀ t ∈ D.regular, ∀ x : M,
      metricAlgebraicCurvatureTensorAt
        (I := I) (M := M) (S.base.metric t) x ∈
          algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    {t₁ t₂ : Real} (htimes : t₁ ≤ t₂)
    (hregular : Set.Iic t₂ ⊆ D.regular) (x : M) :
    S.scalar t₁ x ≤ S.scalar t₂ x := by
  exact hamilton_scalar_two_time_of_monotoneOn htimes
    (hamilton_ancient_scalar_monotoneOn (I := I)
      S hS hcomplete hcurv hR hregular x)

theorem hamilton_ancient_trace_harnack_optimized
    [I.Boundaryless] [NeZero (Module.finrank Real E)]
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (hcomplete : ∀ t ∈ D.regular,
      RiemannianMetricComplete (I := I) (S.base.metric t))
    (hcurv : ∀ a b : Real, Set.Icc a b ⊆ D.regular →
      ∃ C : Real, ∀ t ∈ Set.Icc a b, ∀ x : M,
        normSq0S (I := I) (S.base.metric t) x 4 (S.base.rm04 t x) ≤ C)
    (hR : ∀ t ∈ D.regular, ∀ x : M,
      metricAlgebraicCurvatureTensorAt
        (I := I) (M := M) (S.base.metric t) x ∈
          algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    {t : Real} (hregular : Set.Iic t ⊆ D.regular) (x : M) :
    ∃ Y : TangentSpace I x,
      (∀ Z : TangentSpace I x,
        metricRicci (I := I) (M := M) (S.base.metric t) x
            (vec2 Y Z) =
          (S.base.metric t).inner x
            (gradientAt (I := I) (flowG (I := I) S) t
              (S.scalar t) x) Z) ∧
      (∀ Z : TangentSpace I x,
        (∀ W : TangentSpace I x,
          metricRicci (I := I) (M := M) (S.base.metric t) x
              (vec2 Z W) =
            (S.base.metric t).inner x
              (gradientAt (I := I) (flowG (I := I) S) t
                (S.scalar t) x) W) →
        metricRicci (I := I) (M := M) (S.base.metric t) x
            (vec2 Z Z) =
          metricRicci (I := I) (M := M) (S.base.metric t) x
            (vec2 Y Y)) ∧
      0 ≤ deriv (fun s : Real => S.scalar s x) t -
        (1 / 2 : Real) *
          metricRicci (I := I) (M := M) (S.base.metric t) x
            (vec2 Y Y) := by
  let clock : HarnackClock := ⟨t - 1, t, by linarith⟩
  have hclock : Set.Icc clock.origin clock.time ⊆ D.regular := by
    intro s hs
    exact hregular hs.2
  obtain ⟨Y, hY, hchoice, _⟩ := hamilton_trace_harnack_optimized (I := I)
    S hS hcomplete hcurv hR clock hclock x
  have hproducer : ∀ Z : TangentSpace I x,
      metricRicci (I := I) (M := M) (S.base.metric t) x
          (vec2 Y Z) =
        (S.base.metric t).inner x
          (gradientAt (I := I) (flowG (I := I) S) t
            (S.scalar t) x) Z := by
    simpa only [clock] using hY
  have hminimal : ∀ Z : TangentSpace I x,
      (∀ W : TangentSpace I x,
        metricRicci (I := I) (M := M) (S.base.metric t) x
            (vec2 Z W) =
          (S.base.metric t).inner x
            (gradientAt (I := I) (flowG (I := I) S) t
              (S.scalar t) x) W) →
      metricRicci (I := I) (M := M) (S.base.metric t) x
          (vec2 Z Z) =
        metricRicci (I := I) (M := M) (S.base.metric t) x
          (vec2 Y Y) := by
    simpa only [clock] using hchoice
  refine ⟨Y, hproducer, hminimal, ?_⟩
  have htrace := hamilton_ancient_trace_harnack (I := I)
    S hS hcomplete hcurv hR hregular x ((-1 / 2 : Real) • Y)
  have hinner :
      (S.base.metric t).inner x
          (gradientAt (I := I) (flowG (I := I) S) t
            (S.scalar t) x) ((-1 / 2 : Real) • Y) =
        (-1 / 2 : Real) *
          metricRicci (I := I) (M := M) (S.base.metric t) x
            (vec2 Y Y) := by
    rw [map_smul]
    simp only [smul_eq_mul]
    rw [← hproducer Y]
  have hRicScale :
      metricRicci (I := I) (M := M) (S.base.metric t) x
          (vec2 ((-1 / 2 : Real) • Y) ((-1 / 2 : Real) • Y)) =
        (1 / 4 : Real) *
          metricRicci (I := I) (M := M) (S.base.metric t) x
            (vec2 Y Y) := by
    have hscale := tensor02_smul2 (I := I) (M := M)
      (metricRicci (I := I) (M := M) (S.base.metric t) x)
      (-1 / 2 : Real) Y Y
    norm_num [pow_two] at hscale ⊢
    exact hscale
  rw [hinner, hRicScale] at htrace
  nlinarith

theorem hamilton_ancient_trace_harnack_path
    [I.Boundaryless] [NeZero (Module.finrank Real E)]
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (hcomplete : ∀ t ∈ D.regular,
      RiemannianMetricComplete (I := I) (S.base.metric t))
    (hcurv : ∀ a b : Real, Set.Icc a b ⊆ D.regular →
      ∃ C : Real, ∀ t ∈ Set.Icc a b, ∀ x : M,
        normSq0S (I := I) (S.base.metric t) x 4 (S.base.rm04 t x) ≤ C)
    (hR : ∀ t ∈ D.regular, ∀ x : M,
      metricAlgebraicCurvatureTensorAt
        (I := I) (M := M) (S.base.metric t) x ∈
          algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    {t₁ t₂ : Real} (htimes : t₁ < t₂)
    (hregular : Set.Iic t₂ ⊆ D.regular)
    (gamma : Real → M)
    (hgamma : PiecewiseContMDiffOn I 1 gamma t₁ t₂) :
    Real.exp (-(1 / 4 : Real) *
        intervalIntegral
          (fun t : Real =>
            (S.base.metric t).inner (gamma t)
              (mfderiv 𝓘(Real, Real) I gamma t (1 : Real))
              (mfderiv 𝓘(Real, Real) I gamma t (1 : Real)))
          t₁ t₂ MeasureTheory.volume) *
      S.scalar t₁ (gamma t₁) ≤ S.scalar t₂ (gamma t₂) := by
  apply hamilton_ancient_two_time_limit htimes
  intro origin horigin
  have hpath := hamilton_trace_harnack_path (I := I)
    S hS hcomplete hcurv hR horigin htimes
      (fun s hs => hregular hs.2) gamma hgamma
  simpa only [mul_assoc] using hpath

theorem hamilton_ancient_trace_harnack_path_of_contMDiffOn
    [I.Boundaryless] [NeZero (Module.finrank Real E)]
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (hcomplete : ∀ t ∈ D.regular,
      RiemannianMetricComplete (I := I) (S.base.metric t))
    (hcurv : ∀ a b : Real, Set.Icc a b ⊆ D.regular →
      ∃ C : Real, ∀ t ∈ Set.Icc a b, ∀ x : M,
        normSq0S (I := I) (S.base.metric t) x 4 (S.base.rm04 t x) ≤ C)
    (hR : ∀ t ∈ D.regular, ∀ x : M,
      metricAlgebraicCurvatureTensorAt
        (I := I) (M := M) (S.base.metric t) x ∈
          algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    {t₁ t₂ : Real} (htimes : t₁ < t₂)
    (hregular : Set.Iic t₂ ⊆ D.regular)
    (gamma : Real → M)
    (hgamma : ContMDiffOn 𝓘(Real, Real) I 1 gamma (Set.Icc t₁ t₂)) :
    Real.exp (-(1 / 4 : Real) *
        intervalIntegral
          (fun t : Real =>
            (S.base.metric t).inner (gamma t)
              (mfderiv 𝓘(Real, Real) I gamma t (1 : Real))
              (mfderiv 𝓘(Real, Real) I gamma t (1 : Real)))
          t₁ t₂ MeasureTheory.volume) *
      S.scalar t₁ (gamma t₁) ≤ S.scalar t₂ (gamma t₂) := by
  exact hamilton_ancient_trace_harnack_path (I := I)
    S hS hcomplete hcurv hR htimes hregular gamma (.of_contMDiffOn hgamma)

theorem hamilton_ancient_trace_harnack_distance
    [I.Boundaryless] [NeZero (Module.finrank Real E)]
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (hcomplete : ∀ t ∈ D.regular,
      RiemannianMetricComplete (I := I) (S.base.metric t))
    (hcurv : ∀ a b : Real, Set.Icc a b ⊆ D.regular →
      ∃ C : Real, ∀ t ∈ Set.Icc a b, ∀ x : M,
        normSq0S (I := I) (S.base.metric t) x 4 (S.base.rm04 t x) ≤ C)
    (hR : ∀ t ∈ D.regular, ∀ x : M,
      metricAlgebraicCurvatureTensorAt
        (I := I) (M := M) (S.base.metric t) x ∈
          algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    {t₁ t₂ : Real} (htimes : t₁ < t₂)
    (hregular : Set.Iic t₂ ⊆ D.regular)
    (x y : M) (hy : y ∈ connectedComponent x) :
    Real.exp
          (-((riemannianEDistOf (I := I) (S.base.metric t₁) x y).toReal ^ 2 /
            (4 * (t₂ - t₁)))) *
        S.scalar t₁ x ≤
      S.scalar t₂ y := by
  apply hamilton_ancient_two_time_limit htimes
  intro origin horigin
  have hdistance := hamilton_trace_harnack_distance (I := I)
    S hS hcomplete hcurv hR horigin htimes
      (fun s hs => hregular hs.2) x y hy
  simpa only [mul_assoc] using hdistance

theorem hamilton_ancient_backward_time_trace
    [I.Boundaryless] [NeZero (Module.finrank Real E)]
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (hcomplete : ∀ t ∈ D.regular,
      RiemannianMetricComplete (I := I) (S.base.metric t))
    (hcurv : ∀ a b : Real, Set.Icc a b ⊆ D.regular →
      ∃ C : Real, ∀ t ∈ Set.Icc a b, ∀ x : M,
        normSq0S (I := I) (S.base.metric t) x 4 (S.base.rm04 t x) ≤ C)
    (hR : ∀ t ∈ D.regular, ∀ x : M,
      metricAlgebraicCurvatureTensorAt
        (I := I) (M := M) (S.base.metric t) x ∈
          algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    (T : Real) (tau : Set.Ioi (0 : Real))
    (hregular : Set.Iic (T - (tau : Real)) ⊆ D.regular)
    (x : M) (V : TangentSpace I x) :
    0 ≤ -deriv (fun s : Real => S.scalar (T - s) x) (tau : Real) -
      2 * (S.base.metric (T - (tau : Real))).inner x
        (gradientAt (I := I) (flowG (I := I) S) (T - (tau : Real))
          (S.scalar (T - (tau : Real))) x) V +
      2 * metricRicci (I := I) (M := M)
        (S.base.metric (T - (tau : Real))) x (vec2 V V) := by
  have hforward := hamilton_ancient_trace_harnack (I := I)
    S hS hcomplete hcurv hR hregular x (-V)
  have htime : deriv (fun s : Real => S.scalar (T - s) x) (tau : Real) =
      -deriv (fun s : Real => S.scalar s x) (T - (tau : Real)) := by
    exact deriv_comp_const_sub (fun s : Real => S.scalar s x) T (tau : Real)
  have hinner :
      (S.base.metric (T - (tau : Real))).inner x
          (gradientAt (I := I) (flowG (I := I) S) (T - (tau : Real))
            (S.scalar (T - (tau : Real))) x) (-V) =
        -(S.base.metric (T - (tau : Real))).inner x
          (gradientAt (I := I) (flowG (I := I) S) (T - (tau : Real))
            (S.scalar (T - (tau : Real))) x) V := by
    rw [map_neg]
  have hRic :
      metricRicci (I := I) (M := M)
          (S.base.metric (T - (tau : Real))) x (vec2 (-V) (-V)) =
        metricRicci (I := I) (M := M)
          (S.base.metric (T - (tau : Real))) x (vec2 V V) := by
    have hscale := tensor02_smul2 (I := I) (M := M)
      (metricRicci (I := I) (M := M)
        (S.base.metric (T - (tau : Real))) x) (-1 : Real) V V
    simpa [pow_two] using hscale
  rw [hinner, hRic] at hforward
  rw [htime]
  linarith

end DifferentialGeometry.PDE.RicciFlow
