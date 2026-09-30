import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative.SpatialLp
import DifferentialGeometry.Analysis.Integration.Lp.ContinuousOn
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

theorem memLp_weighted_spatial_fderiv_of_locallyLipschitzOn
    {a b : ℝ} {Ω : Set E} (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    {u : ℝ × E → ℝ} (hu : LocallyLipschitzOn (Icc a b ×ˢ closure Ω) u)
    {c : Fin d → ℝ × E → ℝ}
    (hc : ∀ i, ContinuousOn (c i) (Icc a b ×ˢ closure Ω)) (p : ℝ≥0∞) :
    MemLp (fun q : ℝ × E => ∑ i, c i q *
      fderiv ℝ (fun x => u (q.1, x)) q.2 (EuclideanSpace.single i 1)) p
        ((volume.restrict (Icc a b)).prod (volume.restrict Ω)) := by
  apply memLp_finsetSum Finset.univ
  intro i _
  have hci : MemLp (c i) ∞
      ((volume.restrict (Icc a b)).prod (volume.restrict Ω)) := by
    rw [Measure.prod_restrict]
    exact (hc i).memLp_top_of_subset_isCompact (isCompact_Icc.prod hΩc)
      (measurableSet_Icc.prod hΩ.measurableSet) (prod_mono Subset.rfl subset_closure)
  exact hci.fun_mul (r := p) (memLp_spatial_fderiv_of_locallyLipschitzOn hΩ hΩc hu p i)

theorem integrable_weighted_fderiv_pairings_of_locallyLipschitzOn
    {a b : ℝ} {Ω : Set E} (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    {u w : ℝ × E → ℝ} {A : ℝ × E → Fin d → Fin d → ℝ}
    (hu : LocallyLipschitzOn (Icc a b ×ˢ closure Ω) u)
    (hw : ContinuousOn w (Icc a b ×ˢ closure Ω))
    (hA : ∀ i j, ContinuousOn (fun q => A q i j) (Icc a b ×ˢ closure Ω))
    {φ : ℝ × E → ℝ} (hφ : ContDiff ℝ 1 φ) :
    Integrable (fun q => w q * u q * fderiv ℝ φ q (1, 0))
      ((volume.restrict (Icc a b)).prod (volume.restrict Ω)) ∧
    ∀ j, Integrable (fun q =>
      (∑ i, w q * A q i j *
        fderiv ℝ (fun x => u (q.1, x)) q.2 (EuclideanSpace.single i 1)) *
          fderiv ℝ φ q (0, EuclideanSpace.single j 1))
      ((volume.restrict (Icc a b)).prod (volume.restrict Ω)) := by
  have htest (v : ℝ × E) : Continuous (fun q => fderiv ℝ φ q v) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  constructor
  · have hc : ContinuousOn (fun q => w q * u q * fderiv ℝ φ q (1, 0))
        (Icc a b ×ˢ closure Ω) :=
      (hw.mul hu.continuousOn).mul (htest (1, 0)).continuousOn
    rw [Measure.prod_restrict]
    exact (hc.integrableOn_compact (isCompact_Icc.prod hΩc)).mono_set
      (prod_mono Subset.rfl subset_closure)
  · intro j
    have hweighted : MemLp (fun q : ℝ × E => ∑ i, w q * A q i j *
        fderiv ℝ (fun x => u (q.1, x)) q.2 (EuclideanSpace.single i 1)) 1
        ((volume.restrict (Icc a b)).prod (volume.restrict Ω)) :=
      memLp_weighted_spatial_fderiv_of_locallyLipschitzOn hΩ hΩc hu
        (fun i => hw.mul (hA i j)) 1
    have htestMem : MemLp
        (fun q : ℝ × E => fderiv ℝ φ q (0, EuclideanSpace.single j 1)) ∞
        ((volume.restrict (Icc a b)).prod (volume.restrict Ω)) := by
      rw [Measure.prod_restrict]
      exact (htest (0, EuclideanSpace.single j 1)).continuousOn.memLp_top_of_subset_isCompact
        (isCompact_Icc.prod hΩc) (measurableSet_Icc.prod hΩ.measurableSet)
        (prod_mono Subset.rfl subset_closure)
    exact memLp_one_iff_integrable.mp (hweighted.fun_mul (r := 1) htestMem)

end DifferentialGeometry.Analysis.Sobolev.Euclidean
