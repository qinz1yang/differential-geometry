import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.AreaEvolution
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Topology.Order.Compact

noncomputable section

open Bundle Manifold Set MeasureTheory Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Families

open CurveShortening

private def factor (rho : ℝ → ℝ) (s t : ℝ) : ℝ :=
  Real.exp (∫ w in s..t, rho w)

private def affine (rho : ℝ → ℝ) (s t z : ℝ) : ℝ :=
  (factor rho s t)⁻¹ * (z - 2 * Real.pi * ∫ v in s..t, factor rho s v)

private theorem rho_int {rho : ℝ → ℝ} {a b s t : ℝ}
    (hc : ContinuousOn rho (Icc a b)) (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    IntervalIntegrable rho volume s t :=
  (hc.mono (uIcc_subset_Icc hs ht)).intervalIntegrable

private theorem primitive_deriv {rho : ℝ → ℝ} {a b s t : ℝ}
    (hc : ContinuousOn rho (Icc a b)) (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    HasDerivWithinAt (fun v => ∫ w in s..v, rho w) (rho t) (Icc a b) t := by
  let : Fact (t ∈ Icc a b) := ⟨ht⟩
  have hm : StronglyMeasurableAtFilter rho (𝓝[Icc a b] t) volume :=
    ⟨Icc a b, self_mem_nhdsWithin, hc.aestronglyMeasurable measurableSet_Icc⟩
  exact intervalIntegral.integral_hasDerivWithinAt_right (rho_int hc hs ht) hm (hc t ht)

private theorem factor_cont {rho : ℝ → ℝ} {a b s : ℝ}
    (hc : ContinuousOn rho (Icc a b)) (hs : s ∈ Icc a b) :
    ContinuousOn (factor rho s) (Icc a b) := by
  intro t ht
  change ContinuousWithinAt (fun v => Real.exp (∫ w in s..v, rho w)) (Icc a b) t
  exact Real.continuous_exp.continuousAt.comp_continuousWithinAt
    (primitive_deriv hc hs ht).continuousWithinAt

private theorem factor_deriv {rho : ℝ → ℝ} {a b s t : ℝ}
    (hc : ContinuousOn rho (Icc a b)) (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    HasDerivWithinAt (factor rho s) (rho t * factor rho s t) (Icc a b) t := by
  change HasDerivWithinAt (fun v => Real.exp (∫ w in s..v, rho w))
    (rho t * Real.exp (∫ w in s..t, rho w)) (Icc a b) t
  simpa only [mul_comm] using (primitive_deriv hc hs ht).exp

private theorem factor_pos (rho : ℝ → ℝ) (s t : ℝ) : 0 < factor rho s t :=
  Real.exp_pos _

private theorem factor_cocycle {rho : ℝ → ℝ} {a b s u t : ℝ}
    (hc : ContinuousOn rho (Icc a b)) (hs : s ∈ Icc a b)
    (hu : u ∈ Icc a b) (ht : t ∈ Icc a b) :
    factor rho s t = factor rho s u * factor rho u t := by
  unfold factor
  rw [← intervalIntegral.integral_add_adjacent_intervals (rho_int hc hs hu) (rho_int hc hu ht),
    Real.exp_add]

private theorem factor_primitive_cocycle {rho : ℝ → ℝ} {a b s u t : ℝ}
    (hc : ContinuousOn rho (Icc a b)) (hs : s ∈ Icc a b)
    (hu : u ∈ Icc a b) (ht : t ∈ Icc a b) :
    (∫ v in s..t, factor rho s v) = (∫ v in s..u, factor rho s v) +
      factor rho s u * ∫ v in u..t, factor rho u v := by
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (rho_int (factor_cont hc hs) hs hu) (rho_int (factor_cont hc hs) hu ht)]
  congr 1
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro v hv
  exact factor_cocycle hc hs hu (uIcc_subset_Icc hu ht hv)

private theorem affine_cocycle {rho : ℝ → ℝ} {a b s u t : ℝ}
    (hc : ContinuousOn rho (Icc a b)) (hs : s ∈ Icc a b)
    (hu : u ∈ Icc a b) (ht : t ∈ Icc a b) (z : ℝ) :
    affine rho u t (affine rho s u z) = affine rho s t z := by
  unfold affine
  rw [factor_cocycle hc hs hu ht, factor_primitive_cocycle hc hs hu ht]
  field_simp [(factor_pos rho s u).ne', (factor_pos rho u t).ne']
  ring

private theorem affine_deriv {rho : ℝ → ℝ} {a b s t : ℝ}
    (hc : ContinuousOn rho (Icc a b)) (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (z : ℝ) :
    HasDerivWithinAt (fun v => affine rho s v z)
      (-2 * Real.pi - rho t * affine rho s t z) (Icc a b) t := by
  have hF := ((factor_deriv hc hs ht).inv (factor_pos rho s t).ne').mul
    ((hasDerivWithinAt_const t (Icc a b) z).sub
      ((primitive_deriv (factor_cont hc hs) hs ht).const_mul (2 * Real.pi)))
  convert! hF using 1
  simp only [affine, Pi.inv_apply, Pi.sub_apply]
  field_simp [(factor_pos rho s t).ne']
  ring

private theorem integral_abs_bound {rho : ℝ → ℝ} {a b s t M : ℝ}
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≤ t)
    (hbound : ∀ v ∈ Icc a b, |rho v| ≤ M) :
    |∫ w in s..t, rho w| ≤ M * (t - s) := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := s) (b := t)
    (f := rho) (C := M) (fun v hv => by
      rw [Real.norm_eq_abs]
      exact hbound v (uIcc_subset_Icc hs ht (uIoc_subset_uIcc hv)))
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hst)] using h

private theorem factor_bounds {rho : ℝ → ℝ} {a b s t M : ℝ}
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≤ t)
    (hbound : ∀ v ∈ Icc a b, |rho v| ≤ M) :
    Real.exp (-M * (t - s)) ≤ factor rho s t ∧
      factor rho s t ≤ Real.exp (M * (t - s)) := by
  obtain ⟨hlo, hhi⟩ := abs_le.mp (integral_abs_bound hs ht hst hbound)
  exact ⟨Real.exp_le_exp.mpr (by linarith), Real.exp_le_exp.mpr hhi⟩

private theorem affine_lipschitz {rho : ℝ → ℝ} {a b s t M : ℝ}
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≤ t)
    (hM : 0 ≤ M) (hbound : ∀ v ∈ Icc a b, |rho v| ≤ M) (z z' : ℝ) :
    |affine rho s t z' - affine rho s t z| ≤ Real.exp (M * (b - a)) * |z' - z| := by
  have hsub : affine rho s t z' - affine rho s t z = (factor rho s t)⁻¹ * (z' - z) := by
    unfold affine
    ring
  have hi : (factor rho s t)⁻¹ ≤ Real.exp (M * (b - a)) := by
    rw [factor, ← Real.exp_neg]
    apply Real.exp_le_exp.mpr
    have hlo := (abs_le.mp (integral_abs_bound hs ht hst hbound)).1
    have hlen : M * (t - s) ≤ M * (b - a) := mul_le_mul_of_nonneg_left (by linarith [hs.1, ht.2]) hM
    linarith
  rw [hsub, abs_mul, abs_of_pos (inv_pos.mpr (factor_pos rho s t))]
  exact mul_le_mul_of_nonneg_right hi (abs_nonneg _)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
    [SigmaCompactSpace Q] [hT2 : T2Space Q] [hCompact : CompactSpace Q]
    [hNonempty : Nonempty Q] [hBoundary : I.Boundaryless]


def halfScalarMinimum (G : SolutionFamily (I := I) (M := Q)) (t : ℝ) : ℝ :=
  scalarMinimum G t / 2


def scalarComparisonBound (G : SolutionFamily (I := I) (M := Q)) (a b : ℝ) : ℝ :=
  sSup ((fun t => |halfScalarMinimum G t|) '' Icc a b)


def affineComparison (G : SolutionFamily (I := I) (M := Q)) (s t z : ℝ) : ℝ :=
  (areaIntegratingFactor G s t)⁻¹ *
    (z - 2 * Real.pi * ∫ v in s..t, areaIntegratingFactor G s v)

omit [SigmaCompactSpace Q] hT2 hCompact hNonempty hBoundary in
theorem areaIntegratingFactor_pos (G : SolutionFamily (I := I) (M := Q)) (s t : ℝ) :
    0 < areaIntegratingFactor G s t := Real.exp_pos _

omit [SigmaCompactSpace Q] hT2 hCompact hNonempty hBoundary in
@[simp] theorem affineComparison_self (G : SolutionFamily (I := I) (M := Q)) (s z : ℝ) :
    affineComparison G s s z = z := by
  simp [affineComparison, areaIntegratingFactor]

omit [SigmaCompactSpace Q] hT2 hCompact hNonempty hBoundary in
theorem affineComparison_sub (G : SolutionFamily (I := I) (M := Q)) (s t z z' : ℝ) :
    affineComparison G s t z' - affineComparison G s t z =
      (areaIntegratingFactor G s t)⁻¹ * (z' - z) := by
  unfold affineComparison
  ring

omit [SigmaCompactSpace Q] hT2 hCompact hNonempty hBoundary in
theorem affineComparison_strictMono (G : SolutionFamily (I := I) (M := Q)) (s t : ℝ) :
    StrictMono (affineComparison G s t) := by
  intro z z' h
  unfold affineComparison
  exact mul_lt_mul_of_pos_left (sub_lt_sub_right h _)
    (inv_pos.mpr (areaIntegratingFactor_pos G s t))

omit [SigmaCompactSpace Q] hT2 hCompact hNonempty hBoundary in
private theorem areaIntegratingFactor_eq_factor (G : SolutionFamily (I := I) (M := Q)) (s t : ℝ) :
    areaIntegratingFactor G s t = factor (halfScalarMinimum G) s t := by
  unfold areaIntegratingFactor factor halfScalarMinimum
  rw [intervalIntegral.integral_div]
  congr 1
  ring

omit [SigmaCompactSpace Q] hT2 hCompact hNonempty hBoundary in
private theorem affineComparison_eq_affine (G : SolutionFamily (I := I) (M := Q)) (s t z : ℝ) :
    affineComparison G s t z = affine (halfScalarMinimum G) s t z := by
  unfold affineComparison affine
  simp only [← areaIntegratingFactor_eq_factor]

variable [hConnected : ConnectedSpace Q] {D : RealTimeInterval} {a b : ℝ}
include hT2 hCompact hNonempty hBoundary hConnected

omit [SigmaCompactSpace Q] hCompact hNonempty hBoundary hConnected in
private theorem scalar_window_cont (B : RicciBackground (I := I) (M := Q) D a b) :
    Continuous (fun p : Icc a b × Q => B.family.scalar p.1 p.2) := by
  have hraw : ContinuousOn (fun p : ℝ × Q => B.family.scalar p.1 p.2)
      (D.carrier ×ˢ (univ : Set Q)) := by
    simpa only [SolutionOn.scalar] using B.equation.scalarCont
  have hmap : Continuous (fun p : Icc a b × Q => ((p.1 : ℝ), p.2)) :=
    (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
  have hmem : ∀ p : Icc a b × Q, ((p.1 : ℝ), p.2) ∈ D.carrier ×ˢ (univ : Set Q) :=
    fun p => ⟨D.regular_subset (B.regular p.1.property), mem_univ p.2⟩
  exact hraw.comp_continuous (f := fun p : Icc a b × Q => ((p.1 : ℝ), p.2)) hmap hmem

omit [SigmaCompactSpace Q] hBoundary hConnected in
theorem rfs_width_flow_background
    (B : RicciBackground (I := I) (M := Q) D a b) :
    ContinuousOn (halfScalarMinimum B.family) (Icc a b) ∧
      (∀ t ∈ Icc a b, ∃ q : Q,
        B.family.scalar t q / 2 = halfScalarMinimum B.family t) ∧
      0 ≤ scalarComparisonBound B.family a b ∧
      (∀ t ∈ Icc a b,
        |halfScalarMinimum B.family t| ≤ scalarComparisonBound B.family a b) ∧
      ∃ t ∈ Icc a b,
        |halfScalarMinimum B.family t| = scalarComparisonBound B.family a b := by
  have hscalar := scalar_window_cont B
  have hmin : Continuous (fun t : Icc a b => halfScalarMinimum B.family t) := by
    have hc : Continuous (fun t : Icc a b =>
        sInf ((fun q : Q => B.family.scalar t q) '' (univ : Set Q))) :=
      (isCompact_univ : IsCompact (univ : Set Q)).continuous_sInf
        (f := fun (t : Icc a b) (q : Q) => B.family.scalar t q) hscalar
    simpa only [image_univ, halfScalarMinimum, scalarMinimum] using hc.div_const (2 : ℝ)
  have hcontinuous : ContinuousOn (halfScalarMinimum B.family) (Icc a b) :=
    continuousOn_iff_continuous_domRestrict.mpr hmin
  have hattain : ∀ t ∈ Icc a b, ∃ q : Q, B.family.scalar t q / 2 = halfScalarMinimum B.family t := by
    intro t ht
    have htcont : Continuous (B.family.scalar t) :=
      hscalar.comp (g := fun p : Icc a b × Q => B.family.scalar p.1 p.2)
        (f := fun q : Q => ((⟨t, ht⟩ : Icc a b), q))
        (continuous_const.prodMk continuous_id :
        Continuous (fun q : Q => ((⟨t, ht⟩ : Icc a b), q)))
    obtain ⟨q, _, hq⟩ := (isCompact_univ : IsCompact (univ : Set Q)).exists_sInf_image_eq
      Set.univ_nonempty htcont.continuousOn
    refine ⟨q, ?_⟩
    simpa only [image_univ, halfScalarMinimum, scalarMinimum] using congrArg (fun x : ℝ => x / 2) hq.symm
  obtain ⟨t, ht, hM, hmax⟩ := isCompact_Icc.exists_sSup_image_eq_and_ge
    (nonempty_Icc.mpr B.lt.le) hcontinuous.abs
  have hbound : ∀ v ∈ Icc a b, |halfScalarMinimum B.family v| ≤ scalarComparisonBound B.family a b := by
    intro v hv
    exact (hmax v hv).trans_eq hM.symm
  exact ⟨hcontinuous, hattain, (abs_nonneg _).trans (hbound t ht), hbound, t, ht, hM.symm⟩


omit [SigmaCompactSpace Q] hBoundary hConnected in
theorem areaIntegratingFactor_continuousOn
    (B : RicciBackground (I := I) (M := Q) D a b) {s : ℝ} (hs : s ∈ Icc a b) :
    ContinuousOn (areaIntegratingFactor B.family s) (Icc a b) := by
  have hfun : areaIntegratingFactor B.family s = factor (halfScalarMinimum B.family) s :=
    funext (areaIntegratingFactor_eq_factor B.family s)
  rw [hfun]
  exact factor_cont (rfs_width_flow_background B).1 hs

omit [SigmaCompactSpace Q] hBoundary hConnected in
theorem rfs_width_affine_comparison
    (B : RicciBackground (I := I) (M := Q) D a b) :
    (∀ s ∈ Icc a b, ∀ z t, t ∈ Icc a b →
      HasDerivWithinAt (fun v => affineComparison B.family s v z)
        (-2 * Real.pi - halfScalarMinimum B.family t * affineComparison B.family s t z)
        (Icc a b) t) ∧
    (∀ s ∈ Icc a b, ∀ u ∈ Icc s b, ∀ t ∈ Icc u b, ∀ z,
      affineComparison B.family u t (affineComparison B.family s u z) =
        affineComparison B.family s t z) ∧
    (∀ s ∈ Icc a b, ∀ t ∈ Icc s b,
      Real.exp (-scalarComparisonBound B.family a b * (t - s)) ≤
          areaIntegratingFactor B.family s t ∧
        areaIntegratingFactor B.family s t ≤
          Real.exp (scalarComparisonBound B.family a b * (t - s))) ∧
    (∀ s ∈ Icc a b, ∀ t ∈ Icc s b, ∀ z z' : ℝ,
      |affineComparison B.family s t z' - affineComparison B.family s t z| ≤
        Real.exp (scalarComparisonBound B.family a b * (b - a)) * |z' - z|) := by
  obtain ⟨hc, _, hM, hbound, _⟩ := rfs_width_flow_background B
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s hs z t ht
    simpa only [affineComparison_eq_affine] using affine_deriv hc hs ht z
  · intro s hs u hu t ht z
    have hu' : u ∈ Icc a b := ⟨hs.1.trans hu.1, hu.2⟩
    have ht' : t ∈ Icc a b := ⟨hu'.1.trans ht.1, ht.2⟩
    simpa only [affineComparison_eq_affine] using affine_cocycle hc hs hu' ht' z
  · intro s hs t ht
    have ht' : t ∈ Icc a b := ⟨hs.1.trans ht.1, ht.2⟩
    simpa only [areaIntegratingFactor_eq_factor] using factor_bounds hs ht' ht.1 hbound
  · intro s hs t ht z z'
    have ht' : t ∈ Icc a b := ⟨hs.1.trans ht.1, ht.2⟩
    simpa only [affineComparison_eq_affine] using affine_lipschitz hs ht' ht.1 hM hbound z z'

end DifferentialGeometry.PDE.RicciFlow.Extinction.Families
