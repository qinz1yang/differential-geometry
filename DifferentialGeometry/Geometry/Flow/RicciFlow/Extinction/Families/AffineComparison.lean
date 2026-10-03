import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.AreaEvolution
import DifferentialGeometry.Analysis.ODE.Comparison.IntegratingFactor
import Mathlib.Topology.Order.Compact

noncomputable section

open Bundle Manifold Set MeasureTheory Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Families

open CurveShortening

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
theorem areaIntegratingFactor_eq_integratingFactor
    (G : SolutionFamily (I := I) (M := Q)) (s t : ℝ) :
    areaIntegratingFactor G s t =
      DifferentialGeometry.Analysis.integratingFactor (halfScalarMinimum G) s t := by
  unfold areaIntegratingFactor DifferentialGeometry.Analysis.integratingFactor halfScalarMinimum
  rw [intervalIntegral.integral_div]
  congr 1
  ring

omit [SigmaCompactSpace Q] hT2 hCompact hNonempty hBoundary in
private theorem affineComparison_eq_affineComparisonSolution
    (G : SolutionFamily (I := I) (M := Q)) (s t z : ℝ) :
    affineComparison G s t z =
      DifferentialGeometry.Analysis.affineComparisonSolution
        (halfScalarMinimum G) (2 * Real.pi) s t z := by
  unfold affineComparison DifferentialGeometry.Analysis.affineComparisonSolution
  simp only [← areaIntegratingFactor_eq_integratingFactor]

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
  have hfun : areaIntegratingFactor B.family s =
      DifferentialGeometry.Analysis.integratingFactor (halfScalarMinimum B.family) s :=
    funext (areaIntegratingFactor_eq_integratingFactor B.family s)
  rw [hfun]
  have hc := (rfs_width_flow_background B).1
  simpa only [uIcc_of_le B.lt.le] using
    DifferentialGeometry.Analysis.integratingFactor_continuousOn
      (hc.intervalIntegrable_of_Icc B.lt.le)
      (by simpa only [uIcc_of_le B.lt.le] using hs)

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
    simpa only [affineComparison_eq_affineComparisonSolution, neg_mul] using
      DifferentialGeometry.Analysis.hasDerivWithinAt_affineComparisonSolution
        hc hs ht (2 * Real.pi) z
  · intro s hs u hu t ht z
    have hu' : u ∈ Icc a b := ⟨hs.1.trans hu.1, hu.2⟩
    have ht' : t ∈ Icc a b := ⟨hu'.1.trans ht.1, ht.2⟩
    have hsu : IntervalIntegrable (halfScalarMinimum B.family) volume s u :=
      (hc.mono (uIcc_subset_Icc hs hu')).intervalIntegrable
    have hut : IntervalIntegrable (halfScalarMinimum B.family) volume u t :=
      (hc.mono (uIcc_subset_Icc hu' ht')).intervalIntegrable
    simpa only [affineComparison_eq_affineComparisonSolution] using
      DifferentialGeometry.Analysis.affineComparisonSolution_cocycle hsu hut (2 * Real.pi) z
  · intro s hs t ht
    simpa only [areaIntegratingFactor_eq_integratingFactor] using
      DifferentialGeometry.Analysis.integratingFactor_bounds ht.1
        (fun v hv => hbound v (Icc_subset_Icc hs.1 ht.2 hv))
  · intro s hs t ht z z'
    have hpair := DifferentialGeometry.Analysis.affineComparisonSolution_lipschitz ht.1
      (fun v hv => hbound v (Icc_subset_Icc hs.1 ht.2 hv)) (2 * Real.pi) z z'
    have hlen : scalarComparisonBound B.family a b * (t - s) ≤
        scalarComparisonBound B.family a b * (b - a) :=
      mul_le_mul_of_nonneg_left (by linarith [hs.1, ht.2]) hM
    have hwindow := hpair.trans (mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr hlen) (abs_nonneg (z' - z)))
    simpa only [affineComparison_eq_affineComparisonSolution] using hwindow

end DifferentialGeometry.PDE.RicciFlow.Extinction.Families
