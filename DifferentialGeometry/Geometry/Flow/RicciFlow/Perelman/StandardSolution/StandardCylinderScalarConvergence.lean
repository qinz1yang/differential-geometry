import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardCylinderIdentification
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardCylinderClosedLimit

noncomputable section
open Set Filter Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow

private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev Q := cylinderReferenceCopy.Q
private local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩
private local instance : TopologicalSpace cylinderPointedReference.M := cylinderPointedReference.topology
private local instance : ChartedSpace E3 cylinderPointedReference.M := cylinderPointedReference.charted
private local instance : T2Space cylinderPointedReference.M := cylinderPointedReference.t2
private local instance : IsManifold (𝓡 3) ∞ cylinderPointedReference.M := cylinderPointedReference.smooth
private local instance : SigmaCompactSpace cylinderPointedReference.M := cylinderPointedReference.sigmaCompact

theorem exists_standard_scalar_cylinder_subsequence
    {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ < 1)
    (hlt : ENNReal.ofReal τ < uniformStandardLifetime)
    (S : ℕ → StandardSolution) (x : ℕ → E3)
    (hescape : Tendsto (fun n => (riemannianEDistOf ((S n).val.metric 0) 0 (x n)).toReal)
      atTop atTop) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      Tendsto (fun n => metricScalarAt ((S (ψ n)).val.metric τ) (x (ψ n)))
        atTop (𝓝 ((1 - τ)⁻¹)) := by
  obtain ⟨φ, hφ, Φ, hcharts, bf, co, hinit, hmono, hcharts', hzero, hpull, hcomplete,
    hjets, hgram, hpde, hsolutions, hconverge, htime⟩ :=
      exists_standard_cylinder_closed_limit τ hτ hlt S x hescape
  let hsrc := standardClosedPointedMaps_sourceSigma Φ
  let htgt := standardClosedPointedMaps_targetSigma Φ
  let q : Q := cylinderPointedReference.basepoint
  have hid := standard_cylinder_closed_limit_eq_shrinking Φ hsrc htgt hinit bf co hzero hgram hpde
    τ ⟨hτ.le, le_rfl⟩ hτ1
  obtain ⟨Λ, hΛ, _C, _L, _hC, _hL, hb⟩ := standard_closed_reference_bounds τ hτ hlt
  have hbounds := hb S x cylinderPointedReference φ Φ hsrc htgt hinit
  have hcLow : 0 < Λ⁻¹ := inv_pos.mpr (zero_lt_one.trans_le hΛ)
  have hcovTail := covTail_of_bounds Φ cylinderReferenceMetric bf hsrc htgt 0 τ (by
    intro a
    obtain ⟨Ca, hCa, hcov⟩ := hbounds.2.cov a
    exact ⟨Ca, hCa, fun j t ht y _ => hcov j t ht y⟩)
  have hconv := FlowMetricConvergenceData.scalar_convergence_at Φ cylinderReferenceMetric bf hsrc htgt
    0 τ Λ⁻¹ hcLow (fun j t ht y v => (((hbounds.1 j).1 t ht).2 y (mem_univ y) v).1)
    hcovTail co ⟨hτ.le, le_rfl⟩ q
  have hscalar : metricScalarAt (co.gInf τ) q = (1 - τ)⁻¹ := by
    have hh := congrArg (fun g => metricScalarAt g (cylinderReferenceCopy.equiv.symm q)) hid
    have hcross := metricScalar_cross (co.gInf τ) cylinderReferenceCopy.equiv (cylinderReferenceCopy.equiv.symm q)
    rw [hcross] at hh
    have he := cylinderReferenceCopy.equiv.apply_symm_apply q
    exact (congrArg (fun y : Q => metricScalarAt (co.gInf τ) y) he).symm.trans
      (hh.trans (shrinkingCylinderMetric_scalar hτ1 _))
  refine ⟨φ ∘ co.φ, hmono, ?_⟩
  rw [hscalar] at hconv
  apply hconv.congr'
  filter_upwards with n
  change metricScalarAt ((S ((φ ∘ co.φ) n)).val.metric τ) (Φ.map (co.φ n) q) = _
  have hpoint := Φ.basepoint_map (co.φ n)
  change Φ.map (co.φ n) q = x (φ (co.φ n)) at hpoint
  rw [hpoint]
  rfl

end DifferentialGeometry.PDE.RicciFlow
