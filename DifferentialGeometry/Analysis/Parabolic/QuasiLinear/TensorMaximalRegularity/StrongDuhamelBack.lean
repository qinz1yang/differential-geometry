import DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.TimeL2InterpolationLimit
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.CrossScaleParabolicTrace
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.ForcingFixedPoint
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.SolutionFieldLink

/-!
# Reverse Duhamel representation for strong tensor heat solutions

The maximal-regularity fixed-point theorem constructs solutions in Duhamel
form.  Geometric applications, however, naturally first produce a strong pair

* `u ∈ H¹([0,T]; Hᵃ)`, and
* `field ∈ L²([0,T]; H^{a+2})`

whose lower-scale representatives agree almost everywhere and which satisfies
the tensor heat equation.  This file proves that every such pair is the
canonical Duhamel pair.

The uniqueness input is genuinely independent of the Duhamel construction.
For a zero-initial-data homogeneous pair, the existing cross-scale trace
identity gives, mode by mode,

`cᵢ(t)² = ∫₀ᵗ -2 λᵢ cᵢ(s)² ds`.

Nonnegativity of the tensor Laplacian eigenvalues forces every continuous mode
to vanish.  The almost-everywhere cross-scale link then forces the top-scale
field to vanish as well.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter intervalIntegral
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace QuasiLinear

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable {g : SmoothRiemannianMetric I M} {r s : ℕ}
variable {a T : ℝ}

/-- Finite-step continuation from a uniform local forward-uniqueness window.
For each target time, divide the segment from `a` to that target into finitely
many steps shorter than `δ` and iterate the local implication. -/
theorem eqOn_of_step {X : Type*} {f₁ f₂ : ℝ → X} {a₀ b δ : ℝ}
    (hδ : 0 < δ) (h0 : f₁ a₀ = f₂ a₀)
    (hstep : ∀ t ∈ Icc a₀ b, f₁ t = f₂ t →
      ∀ s ∈ Icc t (min b (t + δ)), f₁ s = f₂ s) :
    ∀ t ∈ Icc a₀ b, f₁ t = f₂ t := by
  intro target htarget
  obtain ⟨N, hN⟩ := exists_nat_gt ((target - a₀) / δ)
  have hratio : 0 ≤ (target - a₀) / δ :=
    div_nonneg (sub_nonneg.mpr htarget.1) hδ.le
  have hNpos : 0 < N := by
    exact_mod_cast (hratio.trans_lt hN)
  let d : ℝ := (target - a₀) / N
  have hd : 0 ≤ d := by
    dsimp [d]
    exact div_nonneg (sub_nonneg.mpr htarget.1) (Nat.cast_nonneg N)
  have hNd : (N : ℝ) * d = target - a₀ := by
    dsimp [d]
    field_simp
  have hdδ : d < δ := by
    have hprod : target - a₀ < (N : ℝ) * δ :=
      (div_lt_iff₀ hδ).mp hN
    rw [show d = (target - a₀) / (N : ℝ) by rfl,
      div_lt_iff₀ (by exact_mod_cast hNpos)]
    nlinarith
  let grid : ℕ → ℝ := fun i => a₀ + (i : ℝ) * d
  have hgrid_mem : ∀ i ≤ N, grid i ∈ Icc a₀ b := by
    intro i hi
    have hi' : (i : ℝ) ≤ (N : ℝ) := by exact_mod_cast hi
    have hmul_nonneg : 0 ≤ (i : ℝ) * d :=
      mul_nonneg (Nat.cast_nonneg i) hd
    have hmul_le : (i : ℝ) * d ≤ (N : ℝ) * d :=
      mul_le_mul_of_nonneg_right hi' hd
    constructor
    · dsimp [grid]
      linarith
    · dsimp [grid]
      nlinarith [hNd, hmul_le, htarget.2]
  have hgrid_eq : ∀ i ≤ N, f₁ (grid i) = f₂ (grid i) := by
    intro i hi
    induction i with
    | zero => simpa only [grid, Nat.cast_zero, zero_mul, add_zero] using h0
    | succ i ih =>
        have hiN : i ≤ N := le_trans (Nat.le_succ i) hi
        have hprev : f₁ (grid i) = f₂ (grid i) := ih hiN
        refine hstep (grid i) (hgrid_mem i hiN) hprev (grid (i + 1)) ?_
        constructor
        · dsimp [grid]
          push_cast
          nlinarith [hd]
        · refine le_min (hgrid_mem (i + 1) hi).2 ?_
          dsimp [grid]
          push_cast
          nlinarith [hdδ]
  have hgrid_N : grid N = target := by
    dsimp [grid]
    nlinarith [hNd]
  rw [← hgrid_N]
  exact hgrid_eq N le_rfl

/-- Package an independently supplied strong pair as a `CrossScaleField`.
The hypothesis is equality of the two lower-scale `L²` classes, not a
pointwise choice of representatives. -/
def strongCross
    (field : timeL2 (tensorHs (I := I) (M := M) g r s (a + 2)) T)
    (u : timeH1 (tensorHs (I := I) (M := M) g r s a) T)
    (hlink :
      timeL2Inclusion (I := I) (M := M) (g := g) (r := r) (s := s)
          (show a ≤ a + 2 by linarith) field =
        timeH1.toTimeL2 (tensorHs (I := I) (M := M) g r s a) T u) :
    CrossScaleField (I := I) (M := M) g r s a T where
  hiL2 := field
  lo := u
  link := by
    have hincl :
        ⇑(timeL2Inclusion (I := I) (M := M) (g := g) (r := r) (s := s)
            (show a ≤ a + 2 by linarith) field) =ᵐ[timeMeasure T]
          fun t => tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
            (show a ≤ a + 2 by linarith) (field t) :=
      (tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
        (show a ≤ a + 2 by linarith)).coeFn_compLpL
          (p := 2) (μ := timeMeasure T) field
    have heq :
        ⇑(timeL2Inclusion (I := I) (M := M) (g := g) (r := r) (s := s)
            (show a ≤ a + 2 by linarith) field) =ᵐ[timeMeasure T]
          ⇑(timeH1.toTimeL2 (tensorHs (I := I) (M := M) g r s a) T u) := by
      rw [hlink]
    have hfun :
        ⇑(timeH1.toTimeL2 (tensorHs (I := I) (M := M) g r s a) T u)
            =ᵐ[timeMeasure T] u.toFun := by
      simpa only [timeH1.toTimeL2_apply] using
        (TimeSobolev.coeFn_ofContinuousOn u.continuousOn_toFun)
    exact hincl.symm.trans (heq.trans hfun)

/-- A zero-initial-data homogeneous strong pair is zero.  This is the linear
energy uniqueness theorem needed for reverse Duhamel realization. -/
theorem strongPair_zero (hT : 0 < T)
    (u : timeH1 (tensorHs (I := I) (M := M) g r s a) T)
    (field : timeL2 (tensorHs (I := I) (M := M) g r s (a + 2)) T)
    (htrace : timeH1.trace0 _ T u = 0)
    (hlink :
      timeL2Inclusion (I := I) (M := M) (g := g) (r := r) (s := s)
          (show a ≤ a + 2 by linarith) field =
        timeH1.toTimeL2 (tensorHs (I := I) (M := M) g r s a) T u)
    (heq : timeH1.timeDeriv _ T u =
      timeScaleLaplacian (I := I) (M := M) a field) :
    u = 0 ∧ field = 0 := by
  let x : CrossScaleField (I := I) (M := M) g r s a T :=
    strongCross (I := I) (M := M) field u hlink
  have hinit : u.init = 0 := by
    simpa only [timeH1.trace0_apply] using htrace
  have heq' : u.deriv = timeScaleLaplacian (I := I) (M := M) a field := by
    simpa only [timeH1.timeDeriv_apply] using heq
  have hmode : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
      ∀ᵐ t ∂(timeMeasure T),
        (u.deriv t).coeff i =
          -(TensorEigenIdx.lambda (I := I) (M := M) i) * x.coeffFun i t := by
    intro i
    have heqAe : (fun t => u.deriv t) =ᵐ[timeMeasure T]
        fun t => (timeScaleLaplacian (I := I) (M := M) a field) t := by
      rw [heq']
    have hΔ := timeScaleLaplacian_coeFn (I := I) (M := M) (τ := a) field
    filter_upwards [heqAe, hΔ, x.ae_coeffFun_eq_hiL2] with t hut hΔt hxt
    have hc := congrArg (fun z => z.coeff i) hut
    rw [hΔt] at hc
    change (u.deriv t).coeff i =
      (tensorScaleLaplacian (I := I) (M := M) a (field t)).coeff i at hc
    rw [tensorScaleLaplacian_coeff] at hc
    have hxi : x.coeffFun i t = (field t).coeff i := hxt i
    rw [hxi]
    exact hc
  have hcoeff : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s) (t : ℝ),
      t ∈ Icc (0 : ℝ) T → x.coeffFun i t = 0 := by
    intro i t ht
    have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_rfl, hT.le⟩
    have hx0 : x.coeffFun i 0 = 0 := by
      change (u.toFun 0).coeff i = 0
      rw [timeH1.toFun_zero, hinit]
      rfl
    have hsq : (x.coeffFun i t) ^ 2 =
        ∫ τ in (0 : ℝ)..t, 2 * x.coeffFun i τ * (u.deriv τ).coeff i := by
      have hsq0 := x.coeffFun_sq_eq i h0 ht
      change (x.coeffFun i t) ^ 2 = (x.coeffFun i 0) ^ 2 +
        ∫ τ in (0 : ℝ)..t, 2 * x.coeffFun i τ * (u.deriv τ).coeff i at hsq0
      simpa only [hx0, pow_two, zero_mul, zero_add] using hsq0
    have hsub : Set.Ioc (0 : ℝ) t ⊆ Set.Icc (0 : ℝ) T :=
      fun τ hτ => ⟨le_of_lt hτ.1, le_trans hτ.2 ht.2⟩
    have hmode' := ae_restrict_of_ae_restrict_of_subset (μ := volume) hsub (hmode i)
    have hint : (∫ τ in (0 : ℝ)..t,
        2 * x.coeffFun i τ * (u.deriv τ).coeff i) ≤ 0 := by
      rw [intervalIntegral.integral_of_le ht.1]
      refine integral_nonpos_of_ae ?_
      filter_upwards [hmode'] with τ hτ
      change 2 * x.coeffFun i τ * (u.deriv τ).coeff i ≤ (0 : ℝ)
      rw [hτ]
      have hlam := tensor_lambda_nonneg (I := I) (M := M) i
      have hnon : 0 ≤ 2 *
          (TensorEigenIdx.lambda (I := I) (M := M) i * (x.coeffFun i τ) ^ 2) :=
        mul_nonneg (by norm_num) (mul_nonneg hlam (sq_nonneg _))
      calc
        2 * x.coeffFun i τ *
            (-TensorEigenIdx.lambda (I := I) (M := M) i * x.coeffFun i τ) =
            -(2 * (TensorEigenIdx.lambda (I := I) (M := M) i *
              (x.coeffFun i τ) ^ 2)) := by ring
        _ ≤ 0 := neg_nonpos.mpr hnon
    have hzsq : (x.coeffFun i t) ^ 2 = 0 :=
      le_antisymm (by linarith [hsq, hint]) (sq_nonneg _)
    exact sq_eq_zero_iff.mp hzsq
  have hfield : field = 0 := by
    refine Lp.ext ?_
    have hzero := Lp.coeFn_zero
      (E := tensorHs (I := I) (M := M) g r s (a + 2))
      (p := 2) (μ := timeMeasure T)
    have hmem : ∀ᵐ t ∂(timeMeasure T), t ∈ Icc (0 : ℝ) T :=
      ae_restrict_mem measurableSet_Icc
    filter_upwards [x.ae_coeffFun_eq_hiL2, hzero, hmem] with t hxt hzt ht
    rw [hzt]
    refine tensorHs.ext (funext fun i => ?_)
    have hxi : x.coeffFun i t = (field t).coeff i := hxt i
    rw [← hxi, hcoeff i t ht]
    rfl
  have hderiv : u.deriv = 0 := by
    rw [hfield] at heq'
    simpa only [map_zero] using heq'
  constructor
  · exact timeH1.ext (by simpa only [timeH1.init_zero] using hinit)
      (by simpa only [timeH1.deriv_zero] using hderiv)
  · exact hfield

/-- The canonical top-scale Duhamel field and the canonical `timeH1` Duhamel
map represent the same lower-scale `L²` class. -/
theorem duhField_pin (hT : 0 < T) (hT1 : T ≤ 1)
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2))
    (force : timeL2 (tensorHs (I := I) (M := M) g r s a) T) :
    timeL2Inclusion (I := I) (M := M) (g := g) (r := r) (s := s)
        (show a ≤ a + 2 by linarith)
        (maxRegDuhamelSolField (I := I) (M := M) a hT hT1 u₀ force) =
      timeH1.toTimeL2 (tensorHs (I := I) (M := M) g r s a) T
        (maxRegDuhamelMap (I := I) (M := M) a hT hT1 u₀ force) := by
  rw [timeH1.toTimeL2_apply]
  refine Lp.ext ?_
  have hincl :=
    (tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
      (show a ≤ a + 2 by linarith)).coeFn_compLpL
        (p := 2) (μ := timeMeasure T)
        (maxRegDuhamelSolField (I := I) (M := M) a hT hT1 u₀ force)
  have hsol := solField_toFun_ae (I := I) (M := M)
    (a := a) hT hT1 h_compact u₀ force
  have hfun := TimeSobolev.coeFn_ofContinuousOn
    (maxRegDuhamelMap (I := I) (M := M) a hT hT1 u₀ force).continuousOn_toFun
  filter_upwards [hincl, hsol, hfun] with t hit hst hft
  change
    (timeL2Inclusion (I := I) (M := M) (g := g) (r := r) (s := s)
      (show a ≤ a + 2 by linarith)
      (maxRegDuhamelSolField (I := I) (M := M) a hT hT1 u₀ force)) t =
        (tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
          (show a ≤ a + 2 by linarith))
          (maxRegDuhamelSolField (I := I) (M := M) a hT hT1 u₀ force t) at hit
  change
    (timeH1.toFunL2 (maxRegDuhamelMap (I := I) (M := M)
      a hT hT1 u₀ force)) t =
        (maxRegDuhamelMap (I := I) (M := M) a hT hT1 u₀ force).toFun t at hft
  exact hit.trans (hst.trans hft.symm)

/-- Reverse Duhamel realization: an arbitrary strong pair with the correct
trace, cross-scale link, and linear equation is the canonical Duhamel pair. -/
theorem strongPair_eq_duh (hT : 0 < T) (hT1 : T ≤ 1)
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2))
    (force : timeL2 (tensorHs (I := I) (M := M) g r s a) T)
    (u : timeH1 (tensorHs (I := I) (M := M) g r s a) T)
    (field : timeL2 (tensorHs (I := I) (M := M) g r s (a + 2)) T)
    (htrace : timeH1.trace0 _ T u =
      tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
        (show a ≤ a + 2 by linarith) u₀)
    (hlink :
      timeL2Inclusion (I := I) (M := M) (g := g) (r := r) (s := s)
          (show a ≤ a + 2 by linarith) field =
        timeH1.toTimeL2 (tensorHs (I := I) (M := M) g r s a) T u)
    (heq : timeH1.timeDeriv _ T u =
      timeScaleLaplacian (I := I) (M := M) a field + force) :
    field = maxRegDuhamelSolField (I := I) (M := M) a hT hT1 u₀ force ∧
      u = maxRegDuhamelMap (I := I) (M := M) a hT hT1 u₀ force := by
  let ud := maxRegDuhamelMap (I := I) (M := M) a hT hT1 u₀ force
  let fd := maxRegDuhamelSolField (I := I) (M := M) a hT hT1 u₀ force
  have htraceD : timeH1.trace0 _ T ud =
      tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
        (show a ≤ a + 2 by linarith) u₀ := by
    exact maxRegDuhamelMap_trace0 (I := I) (M := M)
      (a := a) hT hT1 u₀ force
  have hlinkD :
      timeL2Inclusion (I := I) (M := M) (g := g) (r := r) (s := s)
          (show a ≤ a + 2 by linarith) fd =
        timeH1.toTimeL2 (tensorHs (I := I) (M := M) g r s a) T ud := by
    exact duhField_pin (I := I) (M := M) hT hT1 h_compact u₀ force
  have heqD : timeH1.timeDeriv _ T ud =
      timeScaleLaplacian (I := I) (M := M) a fd + force := by
    exact maxRegDuhamelMap_timeDeriv_eq (I := I) (M := M)
      (a := a) hT hT1 h_compact u₀ force
  have hzeroTrace : timeH1.trace0 _ T (u - ud) = 0 := by
    rw [map_sub, htrace, htraceD, sub_self]
  have hzeroLink :
      timeL2Inclusion (I := I) (M := M) (g := g) (r := r) (s := s)
          (show a ≤ a + 2 by linarith) (field - fd) =
        timeH1.toTimeL2 (tensorHs (I := I) (M := M) g r s a) T (u - ud) := by
    rw [map_sub, map_sub, hlink, hlinkD]
  have hzeroEq : timeH1.timeDeriv _ T (u - ud) =
      timeScaleLaplacian (I := I) (M := M) a (field - fd) := by
    rw [map_sub, map_sub, heq, heqD]
    abel
  rcases strongPair_zero (I := I) (M := M) hT (u - ud) (field - fd)
      hzeroTrace hzeroLink hzeroEq with ⟨hu, hf⟩
  exact ⟨sub_eq_zero.mp hf, sub_eq_zero.mp hu⟩

/-- A strong pair whose forcing is its Nemytskii nonlinearity yields exactly
the forcing fixed-point representation consumed by
`quasilinear_strong_unique`. -/
theorem strongNemy_fixed {L : ℝ≥0}
    {N : tensorHs (I := I) (M := M) g r s (a + 2) →
      tensorHs (I := I) (M := M) g r s a}
    (hT : 0 < T) (hT1 : T ≤ 1)
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2))
    (force : timeL2 (tensorHs (I := I) (M := M) g r s a) T)
    (u : timeH1 (tensorHs (I := I) (M := M) g r s a) T)
    (field : timeL2 (tensorHs (I := I) (M := M) g r s (a + 2)) T)
    (hN : LipschitzWith L N)
    (htrace : timeH1.trace0 _ T u =
      tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
        (show a ≤ a + 2 by linarith) u₀)
    (hlink :
      timeL2Inclusion (I := I) (M := M) (g := g) (r := r) (s := s)
          (show a ≤ a + 2 by linarith) field =
        timeH1.toTimeL2 (tensorHs (I := I) (M := M) g r s a) T u)
    (heq : timeH1.timeDeriv _ T u =
      timeScaleLaplacian (I := I) (M := M) a field + force)
    (hforce : force = nemytskii (I := I) (M := M) hN field) :
    force = nemytskii (I := I) (M := M) hN
      (maxRegDuhamelSolField (I := I) (M := M) a hT hT1 u₀ force) := by
  rcases strongPair_eq_duh (I := I) (M := M) hT hT1 h_compact
      u₀ force u field htrace hlink heq with ⟨hfield, _⟩
  calc
    force = nemytskii (I := I) (M := M) hN field := hforce
    _ = nemytskii (I := I) (M := M) hN
        (maxRegDuhamelSolField (I := I) (M := M) a hT hT1 u₀ force) := by
      rw [hfield]

/-- Two independently supplied strong pairs for the same Lipschitz
quasilinear tensor heat equation and the same initial datum coincide.  This is
the local strong-solution uniqueness theorem obtained by feeding the reverse
Duhamel representations into `quasilinear_strong_unique`. -/
theorem strongPair_unique {L : ℝ≥0}
    {N : tensorHs (I := I) (M := M) g r s (a + 2) →
      tensorHs (I := I) (M := M) g r s a}
    (hT : 0 < T) (hT1 : T ≤ 1)
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2))
    (hN : LipschitzWith L N) (hL : 2 * (L : ℝ) < 1)
    (force₁ force₂ : timeL2 (tensorHs (I := I) (M := M) g r s a) T)
    (u₁ u₂ : timeH1 (tensorHs (I := I) (M := M) g r s a) T)
    (field₁ field₂ :
      timeL2 (tensorHs (I := I) (M := M) g r s (a + 2)) T)
    (htrace₁ : timeH1.trace0 _ T u₁ =
      tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
        (show a ≤ a + 2 by linarith) u₀)
    (htrace₂ : timeH1.trace0 _ T u₂ =
      tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
        (show a ≤ a + 2 by linarith) u₀)
    (hlink₁ :
      timeL2Inclusion (I := I) (M := M) (g := g) (r := r) (s := s)
          (show a ≤ a + 2 by linarith) field₁ =
        timeH1.toTimeL2 (tensorHs (I := I) (M := M) g r s a) T u₁)
    (hlink₂ :
      timeL2Inclusion (I := I) (M := M) (g := g) (r := r) (s := s)
          (show a ≤ a + 2 by linarith) field₂ =
        timeH1.toTimeL2 (tensorHs (I := I) (M := M) g r s a) T u₂)
    (heq₁ : timeH1.timeDeriv _ T u₁ =
      timeScaleLaplacian (I := I) (M := M) a field₁ + force₁)
    (heq₂ : timeH1.timeDeriv _ T u₂ =
      timeScaleLaplacian (I := I) (M := M) a field₂ + force₂)
    (hforce₁ : force₁ = nemytskii (I := I) (M := M) hN field₁)
    (hforce₂ : force₂ = nemytskii (I := I) (M := M) hN field₂) :
    force₁ = force₂ ∧ field₁ = field₂ ∧ u₁ = u₂ := by
  have hfix₁ := strongNemy_fixed (I := I) (M := M) hT hT1 h_compact
    u₀ force₁ u₁ field₁ hN htrace₁ hlink₁ heq₁ hforce₁
  have hfix₂ := strongNemy_fixed (I := I) (M := M) hT hT1 h_compact
    u₀ force₂ u₂ field₂ hN htrace₂ hlink₂ heq₂ hforce₂
  rcases quasilinear_strong_unique (I := I) (M := M) (a := a)
      h_compact hT hT1 u₀ hN hL hfix₁ hfix₂ with ⟨hforces, hmaps⟩
  rcases strongPair_eq_duh (I := I) (M := M) hT hT1 h_compact
      u₀ force₁ u₁ field₁ htrace₁ hlink₁ heq₁ with ⟨hfield₁, hu₁⟩
  rcases strongPair_eq_duh (I := I) (M := M) hT hT1 h_compact
      u₀ force₂ u₂ field₂ htrace₂ hlink₂ heq₂ with ⟨hfield₂, hu₂⟩
  refine ⟨hforces, ?_, ?_⟩
  · calc
      field₁ = maxRegDuhamelSolField (I := I) (M := M)
          a hT hT1 u₀ force₁ := hfield₁
      _ = maxRegDuhamelSolField (I := I) (M := M)
          a hT hT1 u₀ force₂ := by rw [hforces]
      _ = field₂ := hfield₂.symm
  · calc
      u₁ = maxRegDuhamelMap (I := I) (M := M)
          a hT hT1 u₀ force₁ := hu₁
      _ = maxRegDuhamelMap (I := I) (M := M)
          a hT hT1 u₀ force₂ := hmaps
      _ = u₂ := hu₂.symm

end QuasiLinear
end Parabolic
end Analysis
end DifferentialGeometry

end
