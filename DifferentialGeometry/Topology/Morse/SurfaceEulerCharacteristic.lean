import DifferentialGeometry.Topology.Morse.ClosedEulerCharacteristic
import DifferentialGeometry.Topology.Morse.CriticalFinite
import DifferentialGeometry.Topology.Homology.SphereEuler
import DifferentialGeometry.Topology.Morse.CriticalExtrema
import Mathlib.Geometry.Manifold.Instances.Sphere

open Set
open scoped Manifold ContDiff
namespace DifferentialGeometry.Morse

open DifferentialGeometry.Topology.Morse

variable {E H M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] [TopologicalSpace M]
  [ChartedSpace H M] (I : ModelWithCorners ℝ E H) [IsManifold I ∞ M]
  [BoundarylessManifold I M] [T2Space M] [CompactSpace M]

theorem eulerChar_eq_card_criticalPoints_sub_two_mul_card_index_one
    (K : Type) [Field K] (hdim : Module.finrank ℝ E = 2) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hfinite : {x | IsCriticalPointAt I f x}.Finite)
    (hnd : ∀ x, IsCriticalPointAt I f x → IsNondegenerateCriticalPointAt I f x)
    (hinj : InjOn f {x | IsCriticalPointAt I f x}) :
    DifferentialGeometry.Homology.eulerChar K (TopCat.of M) =
      (hfinite.toFinset.card : ℤ) - 2 *
        (hfinite.toFinset.filter (fun p => sigNeg (chartHessianAt
          (fun y => f ((extChartAt I p).symm y)) (extChartAt I p p)) = 1)).card := by
  classical
  let : Nontrivial E := Module.nontrivial_of_finrank_pos (by omega : 0 < Module.finrank ℝ E)
  rw [(finiteHomologyType_and_eulerChar_of_finite_morse I K hf hfinite hnd hinj).2]
  have hterm (p : M) : (-1 : ℤ) ^ sigNeg (chartHessianAt
      (fun y => f ((extChartAt I p).symm y)) (extChartAt I p p)) =
      1 - if sigNeg (chartHessianAt
        (fun y => f ((extChartAt I p).symm y)) (extChartAt I p p)) = 1 then 2 else 0 := by
    let Q := chartHessianAt (fun y => f ((extChartAt I p).symm y)) (extChartAt I p p)
    have hbound : sigNeg Q ≤ 2 := by
      have h := QuadraticForm.sigPos_add_sigNeg_add_radical (Q := Q)
      rw [hdim] at h
      omega
    change (-1 : ℤ) ^ sigNeg Q = 1 - if sigNeg Q = 1 then 2 else 0
    interval_cases h : sigNeg Q <;> norm_num
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.sum_ite]
  ring

end DifferentialGeometry.Morse

namespace DifferentialGeometry.Topology.Morse

open Metric

local notation "E₃" => EuclideanSpace ℝ (Fin 3)
local notation "S₂" => sphere (0 : E₃) 1

theorem ncard_criticalPoints_sphere_two
    {f : S₂ → ℝ} (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f)
    (hnd : ∀ x, IsCriticalPointAt (𝓡 2) f x → IsNondegenerateCriticalPointAt (𝓡 2) f x)
    (hinj : InjOn f {x | IsCriticalPointAt (𝓡 2) f x}) :
    {x | IsCriticalPointAt (𝓡 2) f x}.ncard = 2 + 2 *
      {p | IsCriticalPointAt (𝓡 2) f p ∧ sigNeg (chartHessianAt
        (fun y => f ((extChartAt (𝓡 2) p).symm y)) (extChartAt (𝓡 2) p p)) = 1}.ncard := by
  classical
  have hfin := DifferentialGeometry.Morse.finite_criticalPoints_of_isCompact hf isCompact_univ
    (fun _ _ => BoundarylessManifold.isInteriorPoint) (fun _ _ => mem_univ _) hnd
  have h := DifferentialGeometry.Morse.eulerChar_eq_card_criticalPoints_sub_two_mul_card_index_one
    (𝓡 2) ℚ (by simp) hf hfin hnd hinj
  have hsphere : DifferentialGeometry.Homology.eulerChar ℚ (TopCat.of S₂) = 2 := by
    simpa using DifferentialGeometry.Homology.eulerChar_euclideanSphere ℚ 2
  rw [hsphere] at h
  let S := hfin.toFinset.filter (fun p => sigNeg (chartHessianAt
    (fun y => f ((extChartAt (𝓡 2) p).symm y)) (extChartAt (𝓡 2) p p)) = 1)
  have hS : {p | IsCriticalPointAt (𝓡 2) f p ∧ sigNeg (chartHessianAt
      (fun y => f ((extChartAt (𝓡 2) p).symm y)) (extChartAt (𝓡 2) p p)) = 1} = (S : Set S₂) := by
    ext p
    simp [S]
  rw [hS, Set.ncard_coe_finset, ncard_eq_toFinset_card _ hfin]
  change (2 : ℤ) = hfin.toFinset.card - 2 * S.card at h
  omega

theorem ncard_criticalPoints_sphere_two_of_no_saddles
    {f : S₂ → ℝ} (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f)
    (hnd : ∀ x, IsCriticalPointAt (𝓡 2) f x → IsNondegenerateCriticalPointAt (𝓡 2) f x)
    (hinj : InjOn f {x | IsCriticalPointAt (𝓡 2) f x})
    (hno : ∀ p, IsCriticalPointAt (𝓡 2) f p → sigNeg (chartHessianAt
      (fun y => f ((extChartAt (𝓡 2) p).symm y)) (extChartAt (𝓡 2) p p)) ≠ 1) :
    {x | IsCriticalPointAt (𝓡 2) f x}.ncard = 2 := by
  rw [ncard_criticalPoints_sphere_two hf hnd hinj]
  have hS : {p | IsCriticalPointAt (𝓡 2) f p ∧ sigNeg (chartHessianAt
      (fun y => f ((extChartAt (𝓡 2) p).symm y)) (extChartAt (𝓡 2) p p)) = 1} = ∅ := by
    ext p
    simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
    exact hno p
  rw [hS, ncard_empty, mul_zero, add_zero]

theorem exists_min_max_sphere_two_of_no_saddles
    {f : S₂ → ℝ} (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f)
    (hnd : ∀ x, IsCriticalPointAt (𝓡 2) f x → IsNondegenerateCriticalPointAt (𝓡 2) f x)
    (hinj : InjOn f {x | IsCriticalPointAt (𝓡 2) f x})
    (hno : ∀ p, IsCriticalPointAt (𝓡 2) f p → sigNeg (chartHessianAt
      (fun y => f ((extChartAt (𝓡 2) p).symm y)) (extChartAt (𝓡 2) p p)) ≠ 1) :
    ∃ p q : S₂, f p < f q ∧ {x | IsCriticalPointAt (𝓡 2) f x} = {p, q} ∧
      (∀ x, f p ≤ f x ∧ f x ≤ f q) ∧
      (∀ x, f x = f p ↔ x = p) ∧ (∀ x, f x = f q ↔ x = q) :=
  exists_min_max_of_ncard_criticalPoints_eq_two hf.continuous hinj
    (ncard_criticalPoints_sphere_two_of_no_saddles hf hnd hinj hno)

end DifferentialGeometry.Topology.Morse
