import DifferentialGeometry.Geometry.Metric.TangentLinearDimension
import DifferentialGeometry.Geometry.Comparison.DenseEuclideanTangents
import DifferentialGeometry.Geometry.Comparison.GlobalTangentDimension

set_option autoImplicit false

open Set Metric
open scoped ENNReal

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

theorem linearDimension_eq_dimH_of_local_comparison_and_dimH
    {X : Type*} [MetricSpace X] [CompleteSpace X]
    (hcurves : ∀ x y : X, ∀ ε : ℝ, 0 < ε →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = x ∧ c 1 = y ∧
        eVariationOn c univ < ENNReal.ofReal (dist x y + ε))
    {n : ℕ} (hdim : dimH (univ : Set X) ≤ n)
    (hlocal : ∀ p : X, ∃ Ω : Set X, IsOpen Ω ∧ fourPointComparison 1 Ω ∧ p ∈ Ω) :
    let : ∀ q : X, HasAnglesAt q := fun q => by
      obtain ⟨Ω, hΩ, hcomp, hqΩ⟩ := hlocal q
      exact hasAnglesAt_of_local_fourPointComparison
        (by norm_num : (0 : ℝ) ≤ 1) hΩ hcomp hqΩ
    linearDimension X = dimH (univ : Set X) := by
  let : ∀ q : X, HasAnglesAt q := fun q => by
    obtain ⟨Ω, hΩ, hcomp, hqΩ⟩ := hlocal q
    exact hasAnglesAt_of_local_fourPointComparison
      (by norm_num : (0 : ℝ) ≤ 1) hΩ hcomp hqΩ
  obtain ⟨m, _, hglobal, _, hT⟩ :=
    exists_global_tangent_dimH_and_directions_of_local_comparison_and_dimH hcurves hdim hlocal
  apply le_antisymm
  · apply linearDimension_le_iff.mpr
    intro p k f hf
    calc
      (k : ℝ≥0∞) = dimH (univ : Set (EuclideanSpace ℝ (Fin k))) := by
        rw [Real.dimH_univ_eq_finrank, finrank_euclideanSpace_fin]
      _ = dimH (f '' univ) := (hf.dimH_image univ).symm
      _ ≤ dimH (univ : Set (TangentCone p)) := dimH_mono (subset_univ _)
      _ = m := (hT p).1
      _ = dimH (univ : Set X) := hglobal.symm
  · rcases isEmpty_or_nonempty X with hempty | hnonempty
    · have hz : dimH (univ : Set X) = 0 :=
        Set.Subsingleton.dimH_zero (fun x _ => isEmptyElim x)
      rw [hz]
      exact zero_le
    · obtain ⟨k, _, hglobalK, _, S, _, hDS, hregular⟩ :=
        exists_dense_euclidean_tangents_of_local_comparison_and_dimH hcurves hdim hlocal
      obtain ⟨p, hp⟩ := hDS.nonempty
      obtain ⟨e, _⟩ := hregular p hp
      rw [hglobalK]
      exact le_iSup_of_le p (le_iSup_of_le k
        (le_iSup_of_le (show ∃ f : EuclideanSpace ℝ (Fin k) → TangentCone p,
          Isometry f from ⟨e.symm, e.symm.isometry⟩) le_rfl))

end DifferentialGeometry.Geometry.Comparison.Toponogov
