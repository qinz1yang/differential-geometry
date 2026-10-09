import DifferentialGeometry.Geometry.Comparison.LinearDimensionIdentity
import DifferentialGeometry.Geometry.Metric.ConeIsometryDilation

set_option autoImplicit false

open Set Metric
open scoped ENNReal NNReal

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

theorem exists_greatest_euclidean_tangent_rank_of_local_comparison_and_dimH
    {X : Type*} [MetricSpace X] [CompleteSpace X] [Nonempty X]
    (hcurves : ∀ x y : X, ∀ ε : ℝ, 0 < ε →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = x ∧ c 1 = y ∧
        eVariationOn c univ < ENNReal.ofReal (dist x y + ε))
    {n : ℕ} (hdim : dimH (univ : Set X) ≤ n)
    (hlocal : ∀ p : X, ∃ Ω : Set X, IsOpen Ω ∧ fourPointComparison 1 Ω ∧ p ∈ Ω) :
    letI : ∀ q : X, HasAnglesAt q := fun q => by
      obtain ⟨Ω, hΩ, hcomp, hqΩ⟩ := hlocal q
      exact hasAnglesAt_of_local_fourPointComparison
        (by norm_num : (0 : ℝ) ≤ 1) hΩ hcomp hqΩ
    ∃ m : ℕ, m ≤ n ∧ dimH (univ : Set X) = m ∧
      (∀ V : Set X, IsOpen V → V.Nonempty → dimH V = m) ∧
      IsGreatest {k : ℕ | ∃ q : X,
        ∃ f : EuclideanSpace ℝ (Fin k) → TangentCone q, Isometry f} m ∧
      IsGreatest {k : ℕ | ∃ q : X,
        ∃ f : EuclideanSpace ℝ (Fin k) → TangentCone q,
          Isometry f ∧ f 0 = EuclideanCone.tip ∧
            ∀ c : ℝ≥0, ∀ v, f ((c : ℝ) • v) = EuclideanCone.dilate c (f v)} m := by
  let : ∀ q : X, HasAnglesAt q := fun q => by
    obtain ⟨Ω, hΩ, hcomp, hqΩ⟩ := hlocal q
    exact hasAnglesAt_of_local_fourPointComparison
      (by norm_num : (0 : ℝ) ≤ 1) hΩ hcomp hqΩ
  obtain ⟨m, hmn, hglobal, hopen, S, _, hDS, hregular⟩ :=
    exists_dense_euclidean_tangents_of_local_comparison_and_dimH hcurves hdim hlocal
  have hlinear : linearDimension X = m :=
    (linearDimension_eq_dimH_of_local_comparison_and_dimH hcurves hdim hlocal).trans hglobal
  have hbound (q : X) (k : ℕ) (f : EuclideanSpace ℝ (Fin k) → TangentCone q)
      (hf : Isometry f) : k ≤ m := by
    have h := linearDimension_le_iff.mp hlinear.le q k f hf
    exact_mod_cast h
  obtain ⟨q, hq⟩ := hDS.nonempty
  obtain ⟨e, he⟩ := hregular q hq
  have hzero : e.symm 0 = EuclideanCone.tip := by
    apply e.injective
    rw [e.apply_symm_apply, he]
  refine ⟨m, hmn, hglobal, hopen, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · exact ⟨q, e.symm, e.symm.isometry⟩
  · rintro k ⟨p, f, hf⟩
    exact hbound p k f hf
  · exact ⟨q, e.symm, e.symm.isometry, hzero,
      EuclideanCone.symm_map_smul_of_isometryEquiv e he⟩
  · rintro k ⟨p, f, hf, _⟩
    exact hbound p k f hf

end DifferentialGeometry.Geometry.Comparison.Toponogov
