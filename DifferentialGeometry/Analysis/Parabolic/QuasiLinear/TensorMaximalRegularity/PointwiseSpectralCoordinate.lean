import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.LocallyLipschitzExistence
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.ParabolicInteriorSmoothing

/-!
# The every-time spectral-coordinate representation of the Duhamel solution

For the affine Duhamel map `u = maxRegDuhamelMap a hT hT1 0 gforce` (initial datum
`0`), this file upgrades the *a.e.-in-time* per-mode coordinate identity of
`LocallyLipschitzExistence` to an **every-time** identity on `[0,T]`, and packages
the result as a single existential carrying a continuous, all-order-summable,
per-mode forcing coordinate family.

## The representation

The carrier solution `u ∈ H¹([0,T]; Hᵃ)` (with `u(0) = 0`) has, mode by mode, the
Duhamel-convolution coordinate

  `tensorL2Coeff (tensorHsToL2 … (u.toFun t)) i = perModeConv λᵢ φᵢ t`,

where `λᵢ = TensorEigenIdx.lambda i` and `φᵢ` is a continuous representative of the
`i`-th forcing coordinate `t ↦ (gforce t).coeff i`.  The on-disk identity
(`recentredCarrier_toFun_coeff` for the every-`t` integral form, plus
`solModeCoeff_eq_integral` and `perModeConvL2_coeFn` for the convolution) holds only
*a.e.*; both sides are continuous on `[0,T]` (the left via
`timeH1.continuousOn_toFun` and the continuous coordinate functional `coeffCLM`, the
right via `continuous_perModeConv`), so the a.e. identity upgrades to **every**
`t ∈ [0,T]` by `MeasureTheory.Measure.eqOn_of_ae_eq` (Lebesgue measure is positive
on the interior `(0,T)`, which is dense in `[0,T]`).

## The continuous forcing coordinate

The convolution `perModeConv` depends on the forcing only through its `L²` class on
`[0,t]`, and the every-`t` upgrade needs only that each eigen-coordinate of the forcing
is continuous in time.  The forcing field is therefore supplied here through an
everywhere representative `F : ℝ → Hᵃ` with `gforce =ᵐ F` together with the
**per-eigenmode coordinate continuity** `hcoord : ∀ i, ContinuousOn (t ↦ (F t).coeff i)
[0,T]` — strictly weaker than full `Hᵃ`-continuity of `F`.  This is exactly the
structure the Ricci–DeTurck consumer can provide: the forcing is `N ∘ (solution
field)`, whose order-`(a+2)` solution field has a continuous representative only into
the *lower* scale `H^{a+1}` (the Lions–Magenes parabolic trace), and the genuinely
second-order Nemytskii lowers the order further, so the forcing representative is
continuous only into a scale strictly below `Hᵃ` — but its `L²` eigen-coordinates
`t ↦ (F t).coeff i` are continuous (they factor through the `L²` coordinate functional,
which is bounded at every scale).  The per-mode coordinate `φᵢ` is obtained from
`t ↦ (F t).coeff i` by clamping the argument into `[0,T]` (`Set.IccExtend`), making it
**globally continuous** while preserving its values on `[0,T]`; the every-time identity
then reads `= perModeConv λᵢ φᵢ t` with a genuinely continuous `φᵢ`.

## All-order summability

The weighted mass `tensorSobolevWeight i c · ∫₀ᵗ (φᵢ)²` is dominated, for every
`t ∈ [0,T]`, by the **forcing mass** `forcingMass gforce c i` (the integral over
`[0,t]` is at most the integral over `[0,T]`, which is `‖timeModeCoeff gforce i‖²`).
Hence the all-order summability of the weighted forcing-coordinate masses follows
from the all-order summability of `forcingMass gforce c` by comparison — the same
hypothesis the parabolic interior-smoothing bootstrap consumes and discharges from
the first-order coupling of the nonlinearity.

## Main result

* `maxRegDuhamel_toFun_tensorL2Coeff_eq_perModeConv` — the every-time
  spectral-coordinate representation with a continuous, all-order-summable per-mode
  forcing coordinate family.
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
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable {g : SmoothRiemannianMetric I M} {r s : ℕ}
variable {a : ℝ} {T : ℝ}

/-- The homogeneous-flow coordinate of the zero initial datum vanishes:
`homModeCoeff 0 i = 0`.  Its squared `L²` norm is bounded by `T · 0² = 0`. -/
private theorem homModeCoeff_zero (hT : 0 ≤ T)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    homModeCoeff (I := I) (M := M) (a := a) (T := T)
      (0 : tensorHs (I := I) (M := M) g r s (a + 2)) i = 0 := by
  have hsq := norm_homModeCoeff_sq_le (I := I) (M := M) (a := a) (T := T) hT
    (0 : tensorHs (I := I) (M := M) g r s (a + 2)) i
  rw [tensorHs.zero_coeff] at hsq
  have hnorm : ‖homModeCoeff (I := I) (M := M) (a := a) (T := T)
      (0 : tensorHs (I := I) (M := M) g r s (a + 2)) i‖ = 0 := by
    nlinarith [norm_nonneg (homModeCoeff (I := I) (M := M) (a := a) (T := T)
      (0 : tensorHs (I := I) (M := M) g r s (a + 2)) i), hsq]
  exact norm_eq_zero.mp hnorm

/-- The homogeneous-flow time-derivative coordinate of the zero initial datum
vanishes: `homDerivModeCoeff 0 i = 0`, since it is `−λᵢ • homModeCoeff 0 i`. -/
private theorem homDerivModeCoeff_zero (hT : 0 ≤ T)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    homDerivModeCoeff (I := I) (M := M) (a := a) (T := T)
      (0 : tensorHs (I := I) (M := M) g r s (a + 2)) i = 0 := by
  rw [homDerivModeCoeff_eq_smul (I := I) (M := M) (a := a) (T := T),
    homModeCoeff_zero (I := I) (M := M) (a := a) (T := T) hT i, smul_zero]

/-- The carrier `u = maxRegDuhamelMap a hT hT1 0 gforce` agrees with the recentred
carrier `recentredCarrier hT hT1 0 gforce`: both have initial value `0` (the
inclusion of `0`) and the same `L²` time derivative. -/
private theorem maxRegDuhamelMap_zero_eq_recentredCarrier (hT : 0 < T) (hT1 : T ≤ 1)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g r s a) T) :
    maxRegDuhamelMap (I := I) (M := M) a hT hT1
        (0 : tensorHs (I := I) (M := M) g r s (a + 2)) gforce =
      recentredCarrier (I := I) (M := M) hT hT1
        (0 : tensorHs (I := I) (M := M) g r s (a + 2)) gforce := by
  refine TimeSobolev.timeH1.ext ?_ ?_
  · rw [maxRegDuhamelMap_init (I := I) (M := M) (a := a) (T := T) hT hT1, map_zero,
      recentredCarrier, TimeSobolev.timeH1.init_mk]
  · rw [recentredCarrier, TimeSobolev.timeH1.deriv_mk]

/-- **The a.e. carrier coordinate identity.**  For a.e. `t`, the `i`-th coordinate
of the carrier value `u.toFun t` (with `u = maxRegDuhamelMap a hT hT1 0 gforce`) is
the per-mode Duhamel convolution of the forcing's time-mode coordinate:

  `(u.toFun t).coeff i =ᵐ perModeConv λᵢ (timeModeCoeff gforce i) t`. -/
private theorem carrier_coeff_ae_perModeConv (hT : 0 < T) (hT1 : T ≤ 1)
    (h_compact : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s))
    (gforce : timeL2 (tensorHs (I := I) (M := M) g r s a) T)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    (fun t => ((maxRegDuhamelMap (I := I) (M := M) a hT hT1
          (0 : tensorHs (I := I) (M := M) g r s (a + 2)) gforce).toFun t).coeff i)
        =ᵐ[timeMeasure T]
      fun t => perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
        (fun s => (timeModeCoeff (I := I) (M := M) gforce i) s) t := by
  set lam := TensorEigenIdx.lambda (I := I) (M := M) i with hlam_def
  have hlam_nonneg : 0 ≤ lam := tensor_lambda_nonneg (I := I) (M := M) i
  have hcarr := maxRegDuhamelMap_zero_eq_recentredCarrier (I := I) (M := M)
    (a := a) (T := T) hT hT1 gforce
  have hsolint := solModeCoeff_eq_integral (I := I) (M := M) (a := a) hT.le gforce i
  have hconv := perModeConvL2_coeFn lam hlam_nonneg hT.le
    (timeModeCoeff (I := I) (M := M) gforce i)
  have hsoldef : solModeCoeff (I := I) (M := M) (a := a) hT.le gforce i =
      perModeConvL2 lam hlam_nonneg hT.le
        (timeModeCoeff (I := I) (M := M) gforce i) := rfl
  have hderiv := maxRegDuhamelMap_deriv_coeff_ae (I := I) (M := M)
    (h_compact := h_compact) (a := a) hT hT1
    (0 : tensorHs (I := I) (M := M) g r s (a + 2)) gforce i
  have hhd0 := homDerivModeCoeff_zero (I := I) (M := M) (a := a) (T := T) hT.le i
  have hhd0coe : ⇑(homDerivModeCoeff (I := I) (M := M) (a := a) (T := T)
        (0 : tensorHs (I := I) (M := M) g r s (a + 2)) i) =ᵐ[timeMeasure T]
      fun _ => (0 : ℝ) := by
    rw [hhd0]
    filter_upwards [Lp.coeFn_zero (E := ℝ) (p := 2) (μ := timeMeasure T)] with τ hτ
    rw [hτ]; rfl
  filter_upwards [hsolint, hconv, ae_restrict_mem (μ := volume) measurableSet_Icc]
    with t htsol htconv htmem
  have htmem' : t ∈ Set.Icc (0 : ℝ) T := htmem
  have h0mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨le_rfl, le_trans htmem.1 htmem.2⟩
  have hLHS : ((maxRegDuhamelMap (I := I) (M := M) a hT hT1
        (0 : tensorHs (I := I) (M := M) g r s (a + 2)) gforce).toFun t).coeff i =
      ∫ τ in (0 : ℝ)..t,
        ((maxRegDuhamelMap (I := I) (M := M) a hT hT1
          (0 : tensorHs (I := I) (M := M) g r s (a + 2)) gforce).deriv τ).coeff i := by
    rw [hcarr]
    exact recentredCarrier_toFun_coeff (I := I) (M := M) hT hT1
      (0 : tensorHs (I := I) (M := M) g r s (a + 2)) gforce i htmem'
  have hint_eq : (∫ τ in (0 : ℝ)..t,
        ((maxRegDuhamelMap (I := I) (M := M) a hT hT1
          (0 : tensorHs (I := I) (M := M) g r s (a + 2)) gforce).deriv τ).coeff i) =
      ∫ τ in (0 : ℝ)..t, (derivModeCoeff (I := I) (M := M) (a := a) hT.le gforce i) τ := by
    refine intervalIntegral.integral_congr_ae ?_
    have hsub : Set.uIoc (0 : ℝ) t ⊆ Set.Icc (0 : ℝ) T :=
      (Set.uIoc_subset_uIcc).trans (uIcc_subset_Icc h0mem htmem')
    have haeD := ae_restrict_of_ae_restrict_of_subset (μ := volume) hsub hderiv
    have haeH := ae_restrict_of_ae_restrict_of_subset (μ := volume) hsub hhd0coe
    rw [ae_restrict_iff' measurableSet_uIoc] at haeD haeH
    filter_upwards [haeD, haeH] with τ hτD hτH hτmem
    rw [hτD hτmem, hτH hτmem, zero_add]
  rw [hLHS, hint_eq, ← htsol, hsoldef, htconv]

/-- **The every-time carrier coordinate identity** (with a globally-continuous
forcing coordinate).  For every `t ∈ [0,T]`, the `i`-th coordinate of the carrier
value `u.toFun t` equals `perModeConv λᵢ φᵢ t`, where `φᵢ` is the `Set.IccExtend` of
the `i`-th forcing coordinate of a time-continuous representative `F`. -/
private theorem carrier_toFun_coeff_eq_perModeConv_IccExtend (hT : 0 < T) (hT1 : T ≤ 1)
    (h_compact : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s))
    (gforce : timeL2 (tensorHs (I := I) (M := M) g r s a) T)
    {F : ℝ → tensorHs (I := I) (M := M) g r s a}
    (hcoord : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
      ContinuousOn (fun t => (F t).coeff i) (Set.Icc (0 : ℝ) T))
    (hF_rep : ⇑gforce =ᵐ[timeMeasure T] F)
    (i : TensorEigenIdx (I := I) (M := M) g r s) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    ((maxRegDuhamelMap (I := I) (M := M) a hT hT1
          (0 : tensorHs (I := I) (M := M) g r s (a + 2)) gforce).toFun t).coeff i =
      perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
        (Set.IccExtend hT.le (fun p : ↑(Set.Icc (0 : ℝ) T) => (F p.1).coeff i)) t := by
  set lam := TensorEigenIdx.lambda (I := I) (M := M) i with hlam_def
  set u := maxRegDuhamelMap (I := I) (M := M) a hT hT1
    (0 : tensorHs (I := I) (M := M) g r s (a + 2)) gforce with hu_def
  set φi : ℝ → ℝ :=
    Set.IccExtend hT.le (fun p : ↑(Set.Icc (0 : ℝ) T) => (F p.1).coeff i) with hφi_def
  have hφi_cont : Continuous φi := by
    refine Continuous.Icc_extend' ?_
    exact (hcoord i).restrict
  have hφi_mem : ∀ {x : ℝ}, x ∈ Set.Icc (0 : ℝ) T → φi x = (F x).coeff i := by
    intro x hx
    rw [hφi_def, Set.IccExtend_of_mem hT.le _ hx]
  have hLHS_cont : ContinuousOn (fun t => (u.toFun t).coeff i) (Set.Icc (0 : ℝ) T) := by
    have hcomp : ContinuousOn
        (fun t => (coeffCLM (I := I) (M := M) (g := g) (r := r) (s := s) (σ := a) i)
          (u.toFun t)) (Set.Icc (0 : ℝ) T) :=
      (coeffCLM (I := I) (M := M) (g := g) (r := r) (s := s) (σ := a) i).continuous.comp_continuousOn
        u.continuousOn_toFun
    simpa only [coeffCLM_apply] using hcomp
  have hRHS_cont : ContinuousOn (fun t => perModeConv lam φi t) (Set.Icc (0 : ℝ) T) :=
    (continuous_perModeConv lam hφi_cont).continuousOn
  have hae_base := carrier_coeff_ae_perModeConv (I := I) (M := M)
    (h_compact := h_compact) (a := a) hT hT1 gforce i
  have htmc := timeModeCoeff_coeFn (I := I) (M := M) gforce i
  have hae_forcing : (fun s => (timeModeCoeff (I := I) (M := M) gforce i) s)
      =ᵐ[timeMeasure T] fun s => (F s).coeff i := by
    filter_upwards [htmc, hF_rep] with s hs hsF
    rw [hs, hsF]
  have hconv_eq : ∀ {x : ℝ}, x ∈ Set.Icc (0 : ℝ) T →
      perModeConv lam (fun s => (timeModeCoeff (I := I) (M := M) gforce i) s) x =
        perModeConv lam φi x := by
    intro x hx
    have h0mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨le_rfl, le_trans hx.1 hx.2⟩
    simp only [perModeConv]
    refine intervalIntegral.integral_congr_ae ?_
    have hsub : Set.uIoc (0 : ℝ) x ⊆ Set.Icc (0 : ℝ) T :=
      (Set.uIoc_subset_uIcc).trans (uIcc_subset_Icc h0mem hx)
    have haeF := ae_restrict_of_ae_restrict_of_subset (μ := volume) hsub hae_forcing
    rw [ae_restrict_iff' measurableSet_uIoc] at haeF
    filter_upwards [haeF] with s hsF hsmem
    have hsmem' : s ∈ Set.Icc (0 : ℝ) T := hsub hsmem
    rw [hsF hsmem, ← hφi_mem hsmem']
  have hae_full : (fun t => (u.toFun t).coeff i) =ᵐ[timeMeasure T]
      fun t => perModeConv lam φi t := by
    filter_upwards [hae_base, ae_restrict_mem (μ := volume) measurableSet_Icc]
      with x hx hxmem
    rw [hx]
    exact hconv_eq hxmem
  have hsub_clo : Set.Icc (0 : ℝ) T ⊆ closure (interior (Set.Icc (0 : ℝ) T)) := by
    rw [interior_Icc, closure_Ioo (ne_of_lt hT)]
  have heqOn : Set.EqOn (fun t => (u.toFun t).coeff i)
      (fun t => perModeConv lam φi t) (Set.Icc (0 : ℝ) T) :=
    MeasureTheory.Measure.eqOn_of_ae_eq hae_full hLHS_cont hRHS_cont hsub_clo
  exact heqOn ht

theorem carrier_toFun_coeff_eq_perModeConv_IccExtend_restrict (hT : 0 < T) (hT1 : T ≤ 1)
    {d₂ : ℝ} (hd₂_pos : 0 < d₂) (hd₂_le : d₂ ≤ T)
    (h_compact : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s))
    (gforce : timeL2 (tensorHs (I := I) (M := M) g r s a) T)
    {F : ℝ → tensorHs (I := I) (M := M) g r s a}
    (hcoord : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
      ContinuousOn (fun t => (F t).coeff i) (Set.Icc (0 : ℝ) d₂))
    (hF_rep : ⇑gforce =ᵐ[volume.restrict (Set.Icc (0 : ℝ) d₂)] F)
    (i : TensorEigenIdx (I := I) (M := M) g r s) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) d₂) :
    ((maxRegDuhamelMap (I := I) (M := M) a hT hT1
          (0 : tensorHs (I := I) (M := M) g r s (a + 2)) gforce).toFun t).coeff i =
      perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
        (Set.IccExtend hd₂_pos.le (fun p : ↑(Set.Icc (0 : ℝ) d₂) => (F p.1).coeff i)) t := by
  set lam := TensorEigenIdx.lambda (I := I) (M := M) i with hlam_def
  set u := maxRegDuhamelMap (I := I) (M := M) a hT hT1
    (0 : tensorHs (I := I) (M := M) g r s (a + 2)) gforce with hu_def
  set φi : ℝ → ℝ :=
    Set.IccExtend hd₂_pos.le (fun p : ↑(Set.Icc (0 : ℝ) d₂) => (F p.1).coeff i) with hφi_def
  have hφi_cont : Continuous φi := by
    refine Continuous.Icc_extend' ?_
    exact (hcoord i).restrict
  have hφi_mem : ∀ {x : ℝ}, x ∈ Set.Icc (0 : ℝ) d₂ → φi x = (F x).coeff i := by
    intro x hx
    rw [hφi_def, Set.IccExtend_of_mem hd₂_pos.le _ hx]
  have hLHS_cont : ContinuousOn (fun t => (u.toFun t).coeff i) (Set.Icc (0 : ℝ) d₂) := by
    have hcomp : ContinuousOn
        (fun t => (coeffCLM (I := I) (M := M) (g := g) (r := r) (s := s) (σ := a) i)
          (u.toFun t)) (Set.Icc (0 : ℝ) d₂) :=
      (coeffCLM (I := I) (M := M) (g := g) (r := r) (s := s) (σ := a) i).continuous.comp_continuousOn
        (u.continuousOn_toFun.mono (Set.Icc_subset_Icc le_rfl hd₂_le))
    simpa only [coeffCLM_apply] using hcomp
  have hRHS_cont : ContinuousOn (fun t => perModeConv lam φi t) (Set.Icc (0 : ℝ) d₂) :=
    (continuous_perModeConv lam hφi_cont).continuousOn
  have hae_base := carrier_coeff_ae_perModeConv (I := I) (M := M)
    (h_compact := h_compact) (a := a) hT hT1 gforce i
  have hae_base' := MeasureTheory.ae_restrict_of_ae_restrict_of_subset (μ := volume)
    (Set.Icc_subset_Icc le_rfl hd₂_le) hae_base
  have htmc := timeModeCoeff_coeFn (I := I) (M := M) gforce i
  have htmc' := MeasureTheory.ae_restrict_of_ae_restrict_of_subset (μ := volume)
    (Set.Icc_subset_Icc le_rfl hd₂_le) htmc
  have hae_forcing : (fun s => (timeModeCoeff (I := I) (M := M) gforce i) s)
      =ᵐ[volume.restrict (Set.Icc (0 : ℝ) d₂)] fun s => (F s).coeff i := by
    filter_upwards [htmc', hF_rep] with s hs hsF
    rw [hs, hsF]
  have hconv_eq : ∀ {x : ℝ}, x ∈ Set.Icc (0 : ℝ) d₂ →
      perModeConv lam (fun s => (timeModeCoeff (I := I) (M := M) gforce i) s) x =
        perModeConv lam φi x := by
    intro x hx
    have h0mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) d₂ := ⟨le_rfl, le_trans hx.1 hx.2⟩
    simp only [perModeConv]
    refine intervalIntegral.integral_congr_ae ?_
    have hsub : Set.uIoc (0 : ℝ) x ⊆ Set.Icc (0 : ℝ) d₂ :=
      (Set.uIoc_subset_uIcc).trans (uIcc_subset_Icc h0mem hx)
    have haeF := ae_restrict_of_ae_restrict_of_subset (μ := volume) hsub hae_forcing
    rw [ae_restrict_iff' measurableSet_uIoc] at haeF
    filter_upwards [haeF] with s hsF hsmem
    have hsmem' : s ∈ Set.Icc (0 : ℝ) d₂ := hsub hsmem
    rw [hsF hsmem, ← hφi_mem hsmem']
  have hae_full : (fun t => (u.toFun t).coeff i)
      =ᵐ[volume.restrict (Set.Icc (0 : ℝ) d₂)] fun t => perModeConv lam φi t := by
    filter_upwards [hae_base', ae_restrict_mem (μ := volume) measurableSet_Icc]
      with x hx hxmem
    rw [hx]
    exact hconv_eq hxmem
  have hsub_clo : Set.Icc (0 : ℝ) d₂ ⊆ closure (interior (Set.Icc (0 : ℝ) d₂)) := by
    rw [interior_Icc, closure_Ioo (ne_of_lt hd₂_pos)]
  have heqOn : Set.EqOn (fun t => (u.toFun t).coeff i)
      (fun t => perModeConv lam φi t) (Set.Icc (0 : ℝ) d₂) :=
    MeasureTheory.Measure.eqOn_of_ae_eq hae_full hLHS_cont hRHS_cont hsub_clo
  exact heqOn ht

theorem maxRegDuhamel_toFun_tensorL2Coeff_eq_perModeConv_id_restrict (hT : 0 < T) (hT1 : T ≤ 1)
    (ha : 0 ≤ a) {d₂ : ℝ} (hd₂_pos : 0 < d₂) (hd₂_le : d₂ ≤ T)
    (h_compact : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s))
    (gforce : timeL2 (tensorHs (I := I) (M := M) g r s a) T)
    {F : ℝ → tensorHs (I := I) (M := M) g r s a}
    (hcoord : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
      ContinuousOn (fun t => (F t).coeff i) (Set.Icc (0 : ℝ) d₂))
    (hF_rep : ⇑gforce =ᵐ[volume.restrict (Set.Icc (0 : ℝ) d₂)] F) :
    ∃ φ : TensorEigenIdx (I := I) (M := M) g r s → ℝ → ℝ,
      (∀ i, Continuous (φ i)) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) d₂, ∀ i,
        tensorL2Coeff (I := I) (M := M) h_compact
            ((tensorHsToL2 (I := I) (M := M) h_compact ha)
              ((maxRegDuhamelMap (I := I) (M := M) a hT hT1
                (0 : tensorHs (I := I) (M := M) g r s (a + 2)) gforce).toFun t)) i =
          perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (φ i) t) := by
  refine ⟨fun i => Set.IccExtend hd₂_pos.le
      (fun p : ↑(Set.Icc (0 : ℝ) d₂) => (F p.1).coeff i), ?_, ?_⟩
  · intro i
    refine Continuous.Icc_extend' ?_
    exact (hcoord i).restrict
  · intro t ht i
    rw [tensorHsToL2_tensorL2Coeff ha]
    exact carrier_toFun_coeff_eq_perModeConv_IccExtend_restrict (I := I) (M := M)
      (h_compact := h_compact) (a := a) hT hT1 hd₂_pos hd₂_le gforce hcoord hF_rep i ht

theorem timeModeCoeff_eq_perModeConv_forcing (hT : 0 < T) (hT1 : T ≤ 1)
    (h_compact : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s))
    (gforce : timeL2 (tensorHs (I := I) (M := M) g r s a) T)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    (fun t => (maxRegDuhamelSolField (I := I) (M := M) a hT hT1
          (0 : tensorHs (I := I) (M := M) g r s (a + 2)) gforce t).coeff i)
        =ᵐ[timeMeasure T]
      fun t => perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
        (fun s => (timeModeCoeff (I := I) (M := M) gforce i) s) t := by
  have hfield := maxRegDuhamelSolField_coeff_ae (I := I) (M := M)
    (h_compact := h_compact) (a := a) hT hT1
    (0 : tensorHs (I := I) (M := M) g r s (a + 2)) gforce i
  have hcarr := carrier_coeff_ae_perModeConv (I := I) (M := M)
    (h_compact := h_compact) (a := a) hT hT1 gforce i
  have hrec := maxRegDuhamelMap_zero_eq_recentredCarrier (I := I) (M := M)
    (a := a) (T := T) hT hT1 gforce
  filter_upwards [hfield, hcarr, ae_restrict_mem (μ := volume) measurableSet_Icc]
    with t htfield htcarr htmem
  have htmem' : t ∈ Set.Icc (0 : ℝ) T := htmem
  have hcarr_int : ((maxRegDuhamelMap (I := I) (M := M) a hT hT1
        (0 : tensorHs (I := I) (M := M) g r s (a + 2)) gforce).toFun t).coeff i =
      ∫ τ in (0 : ℝ)..t,
        ((maxRegDuhamelMap (I := I) (M := M) a hT hT1
          (0 : tensorHs (I := I) (M := M) g r s (a + 2)) gforce).deriv τ).coeff i := by
    rw [hrec]
    exact recentredCarrier_toFun_coeff (I := I) (M := M) hT hT1
      (0 : tensorHs (I := I) (M := M) g r s (a + 2)) gforce i htmem'
  have hzero : (0 : tensorHs (I := I) (M := M) g r s (a + 2)).coeff i = 0 := by
    rw [tensorHs.zero_coeff]
  rw [htfield, hzero, zero_add, ← hcarr_int, htcarr]

/-- **The every-time spectral-coordinate representation of the Duhamel solution.**
Let `u = maxRegDuhamelMap a hT hT1 0 gforce` be the affine Duhamel map with zero
initial datum, and let `F : ℝ → Hᵃ` be an everywhere representative of the forcing
`gforce` (`gforce =ᵐ F`) whose per-eigenmode `L²` coordinates `t ↦ (F t).coeff i` are
continuous on `[0,T]` (`hcoord` — strictly weaker than `Hᵃ`-continuity of `F`, which
the genuinely second-order Ricci–DeTurck forcing does NOT have: its continuous
representative ceilings below `Hᵃ`) and whose forcing masses are summable at every
order (`hsum`).  Then there is a per-mode forcing-coordinate family
`φ : TensorEigenIdx → ℝ → ℝ` with

* **(continuity)** each `φ i` is continuous;
* **(all-order summability)** for every `c ≥ 0` and every `t ∈ [0,T]`,
  `i ↦ tensorSobolevWeight i c · ∫₀ᵗ (φ i s)² ds` is summable;
* **(every-time coordinate identity)** for every `t ∈ [0,T]` and every `i`,
  `tensorL2Coeff … (tensorHsToL2 … (u.toFun t)) i = perModeConv λᵢ (φ i) t`.

This is the shared spectral-coordinate foundation of the interior-regularity
conjuncts: the every-time (not merely a.e.) coordinate identity is what lets the
downstream consumers read off pointwise-in-time spectral data.  (The summability is
stated on the horizon `[0,T]`, where the convolution coordinates of the solution
live and where every consumer reads them; on `t > T` it would require all-order
summability of the forcing's boundary values, which is not part of the
maximal-regularity data.) -/
theorem maxRegDuhamel_toFun_tensorL2Coeff_eq_perModeConv (hT : 0 < T) (hT1 : T ≤ 1)
    (ha : 0 ≤ a)
    (h_compact : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s))
    (gforce : timeL2 (tensorHs (I := I) (M := M) g r s a) T)
    {F : ℝ → tensorHs (I := I) (M := M) g r s a}
    (hcoord : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
      ContinuousOn (fun t => (F t).coeff i) (Set.Icc (0 : ℝ) T))
    (hF_rep : ⇑gforce =ᵐ[timeMeasure T] F)
    (hsum : ∀ c : ℝ, 0 ≤ c → Summable (forcingMass (I := I) (M := M) gforce c)) :
    ∃ φ : TensorEigenIdx (I := I) (M := M) g r s → ℝ → ℝ,
      (∀ i, Continuous (φ i)) ∧
      (∀ c : ℝ, 0 ≤ c → ∀ t ∈ Set.Icc (0 : ℝ) T,
        Summable (fun i => tensorSobolevWeight (I := I) (M := M) i c *
          ∫ s in (0 : ℝ)..t, (φ i s) ^ 2)) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) T, ∀ i,
        tensorL2Coeff (I := I) (M := M) h_compact
            ((tensorHsToL2 (I := I) (M := M) h_compact ha)
              ((maxRegDuhamelMap (I := I) (M := M) a hT hT1
                (0 : tensorHs (I := I) (M := M) g r s (a + 2)) gforce).toFun t)) i =
          perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
            (Set.IccExtend hT.le (fun p : ↑(Set.Icc (0 : ℝ) T) => (F p.1).coeff i)) t) := by
  refine ⟨fun i => Set.IccExtend hT.le (fun p : ↑(Set.Icc (0 : ℝ) T) => (F p.1).coeff i),
    ?_, ?_, ?_⟩
  · -- continuity of each φ i
    intro i
    refine Continuous.Icc_extend' ?_
    exact (hcoord i).restrict
  · -- all-order summability by comparison with forcingMass
    intro c hc t ht
    refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) (hsum c hc)
    · -- nonneg of the weighted integral
      refine mul_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) i c) ?_
      refine intervalIntegral.integral_nonneg ht.1 ?_
      intro x _; positivity
    · -- weighted integral ≤ forcingMass
      set φi : ℝ → ℝ :=
        Set.IccExtend hT.le (fun p : ↑(Set.Icc (0 : ℝ) T) => (F p.1).coeff i) with hφi_def
      have hφi_cont : Continuous φi := by
        refine Continuous.Icc_extend' ?_
        exact (hcoord i).restrict
      have hforcing : forcingMass (I := I) (M := M) gforce c i =
          tensorSobolevWeight (I := I) (M := M) i c *
            ∫ τ in Set.Icc (0 : ℝ) T,
              ((timeModeCoeff (I := I) (M := M) gforce i) τ) ^ 2 := by
        rw [forcingMass, TimeSobolev.norm_sq_eq_integral]
        congr 1
        refine MeasureTheory.integral_congr_ae ?_
        filter_upwards [] with τ
        rw [Real.norm_eq_abs, sq_abs]
      have htmc := timeModeCoeff_coeFn (I := I) (M := M) gforce i
      have hae_forcing : (fun τ => (timeModeCoeff (I := I) (M := M) gforce i) τ)
          =ᵐ[timeMeasure T] fun τ => φi τ := by
        filter_upwards [htmc, hF_rep, ae_restrict_mem (μ := volume) measurableSet_Icc]
          with τ hτ hτF hτmem
        rw [hτ, hτF, hφi_def, Set.IccExtend_of_mem hT.le _ hτmem]
      have hIcc_eq : (∫ τ in Set.Icc (0 : ℝ) T,
            ((timeModeCoeff (I := I) (M := M) gforce i) τ) ^ 2) =
          ∫ τ in Set.Icc (0 : ℝ) T, (φi τ) ^ 2 := by
        refine MeasureTheory.setIntegral_congr_ae measurableSet_Icc ?_
        have hae' : ∀ᵐ τ ∂volume, τ ∈ Set.Icc (0 : ℝ) T →
            (timeModeCoeff (I := I) (M := M) gforce i) τ = φi τ :=
          (MeasureTheory.ae_restrict_iff' measurableSet_Icc).mp hae_forcing
        filter_upwards [hae'] with τ hτ hτmem
        rw [hτ hτmem]
      have htint : (∫ τ in (0 : ℝ)..t, (φi τ) ^ 2) ≤
          ∫ τ in Set.Icc (0 : ℝ) T, (φi τ) ^ 2 := by
        rw [intervalIntegral.integral_of_le ht.1,
          ← MeasureTheory.integral_Icc_eq_integral_Ioc]
        refine MeasureTheory.setIntegral_mono_set (hφi_cont.pow 2).integrableOn_Icc ?_ ?_
        · filter_upwards with x; positivity
        · exact HasSubset.Subset.eventuallyLE (Set.Icc_subset_Icc le_rfl ht.2)
      rw [hforcing, hIcc_eq]
      exact mul_le_mul_of_nonneg_left htint (tensorSobolevWeight_nonneg (I := I) (M := M) i c)
  · -- the every-time coordinate identity
    intro t ht i
    rw [tensorHsToL2_tensorL2Coeff ha]
    exact carrier_toFun_coeff_eq_perModeConv_IccExtend (I := I) (M := M)
      (h_compact := h_compact) (a := a) hT hT1 gforce hcoord hF_rep i ht

theorem maxRegDuhamel_toFun_tensorL2Coeff_eq_perModeConv_id (hT : 0 < T) (hT1 : T ≤ 1)
    (ha : 0 ≤ a)
    (h_compact : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s))
    (gforce : timeL2 (tensorHs (I := I) (M := M) g r s a) T)
    {F : ℝ → tensorHs (I := I) (M := M) g r s a}
    (hcoord : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
      ContinuousOn (fun t => (F t).coeff i) (Set.Icc (0 : ℝ) T))
    (hF_rep : ⇑gforce =ᵐ[timeMeasure T] F) :
    ∃ φ : TensorEigenIdx (I := I) (M := M) g r s → ℝ → ℝ,
      (∀ i, Continuous (φ i)) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) T, ∀ i,
        tensorL2Coeff (I := I) (M := M) h_compact
            ((tensorHsToL2 (I := I) (M := M) h_compact ha)
              ((maxRegDuhamelMap (I := I) (M := M) a hT hT1
                (0 : tensorHs (I := I) (M := M) g r s (a + 2)) gforce).toFun t)) i =
          perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (φ i) t) := by
  refine ⟨fun i => Set.IccExtend hT.le (fun p : ↑(Set.Icc (0 : ℝ) T) => (F p.1).coeff i),
    ?_, ?_⟩
  · intro i
    refine Continuous.Icc_extend' ?_
    exact (hcoord i).restrict
  · intro t ht i
    rw [tensorHsToL2_tensorL2Coeff ha]
    exact carrier_toFun_coeff_eq_perModeConv_IccExtend (I := I) (M := M)
      (h_compact := h_compact) (a := a) hT hT1 gforce hcoord hF_rep i ht

end QuasiLinear
end Parabolic
end Analysis
end DifferentialGeometry
