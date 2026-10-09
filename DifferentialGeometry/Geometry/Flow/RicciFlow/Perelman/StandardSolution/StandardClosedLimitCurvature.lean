import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardFirstTimeJet
import DifferentialGeometry.Geometry.Curvature.RiemannRicciNorm

noncomputable section
open Set Filter Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

section Maps

variable {τ : ℝ} {hτ : 0 < τ} {hlt : ENNReal.ofReal τ < uniformStandardLifetime}
  {S : ℕ → StandardSolution} {x : ℕ → E3}
  {P : PointedRiemannianManifold (𝓡 3)} {φ : ℕ → ℕ}
  (Φ : PointedCGHMaps (standardClosedPointedFlowSequence τ hτ hlt S x) P φ)

private local instance : TopologicalSpace P.M := P.topology
private local instance : ChartedSpace E3 P.M := P.charted
private local instance : T2Space P.M := P.t2
private local instance : IsManifold (𝓡 3) ∞ P.M := P.smooth
private local instance : SigmaCompactSpace P.M := P.sigmaCompact

variable (hsrc : SourceIsSigmaCompact Φ) (htgt : TargetIsSigmaCompact Φ)

private local instance (j : ℕ) : TopologicalSpace (SourceDomain Φ j) := sourceDomTop Φ j
private local instance (j : ℕ) : ChartedSpace E3 (SourceDomain Φ j) := sourceDomCharted Φ j
private local instance (j : ℕ) : T2Space (SourceDomain Φ j) := sourceDomT2 Φ j
private local instance (j : ℕ) : IsManifold (𝓡 3) ∞ (SourceDomain Φ j) := sourceDomSmooth Φ j
private local instance (j : ℕ) : SigmaCompactSpace (SourceDomain Φ j) :=
  sourceDomSigmaOf Φ j (standardClosedPointedMaps_sourceSigma Φ j)

theorem standard_closed_limit_curvature_bound
    (hinit : ∀ j, sourceMetric Φ hsrc htgt j 0 = sourceMetricRestriction Φ P.metric j)
    (bf : BumpFamily Φ) (co : FlowMetricConvergenceData Φ P.metric bf hsrc htgt 0 τ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Icc 0 τ, ∀ q : P.M,
      normSq0S (co.gInf t) q 4 (metricRm04 (co.gInf t) q) ≤ B := by
  obtain ⟨Λ, hΛ, _C, _L, _hC, _hL, hb⟩ := standard_closed_reference_bounds τ hτ hlt
  have hbounds := hb S x P φ Φ hsrc htgt hinit
  have hcLow : 0 < Λ⁻¹ := inv_pos.mpr (zero_lt_one.trans_le hΛ)
  have hbound : ∀ j t, t ∈ Icc 0 τ → ∀ (y : SourceDomain Φ j)
      (v : TangentSpace (𝓡 3) y),
      Λ⁻¹ * P.metric.inner y.val v v ≤ (sourceMetric Φ hsrc htgt j t).inner y v v := by
    intro j t ht y v
    exact (((hbounds.1 j).1 t ht).2 y (mem_univ y) v).1
  have hcovTail := covTail_of_bounds Φ P.metric bf hsrc htgt 0 τ (by
    intro a
    obtain ⟨Ca, hCa, hcov⟩ := hbounds.2.cov a
    exact ⟨Ca, hCa, fun j t ht y _ => hcov j t ht y⟩)
  obtain ⟨hlife, K, hK, hRm⟩ := uniformStandardLifetime_slab τ hτ.le hlt
  refine ⟨(567 * K) ^ 2, sq_nonneg _, ?_⟩
  intro t ht q
  have hconv := FlowMetricConvergenceData.ricNorm_convergence_at Φ P.metric bf hsrc htgt
    0 τ Λ⁻¹ hcLow hbound hcovTail co ht q
  have hRic : normSq0S (co.gInf t) q 2 (metricRicci (co.gInf t) q) ≤ (9 * K) ^ 2 := by
    apply le_of_tendsto hconv
    filter_upwards with k
    have h := ricTower_normSq_le (S ((φ ∘ co.φ) k)).val.toSolutionOn t 0
      (Φ.map (co.φ k) q)
    have hcurv := (Real.sqrt_le_iff.mp
      (hRm (S ((φ ∘ co.φ) k)) t ht (Φ.map (co.φ k) q))).2
    change ricciNorm (S ((φ ∘ co.φ) k)).val.toSolutionOn t (Φ.map (co.φ k) q) ≤
      (Module.finrank ℝ E3 : ℝ) ^ 4 *
        normSq0S ((S ((φ ∘ co.φ) k)).val.metric t) (Φ.map (co.φ k) q) 4
          (metricRm04 ((S ((φ ∘ co.φ) k)).val.metric t) (Φ.map (co.φ k) q)) at h
    norm_num only [finrank_euclideanSpace, Fintype.card_fin, Nat.cast_ofNat] at h
    change ricciNorm (S ((φ ∘ co.φ) k)).val.toSolutionOn t (Φ.map (co.φ k) q) ≤ _
    nlinarith
  have hRicRoot : Real.sqrt (normSq0S (co.gInf t) q 2 (metricRicci (co.gInf t) q)) ≤ 9 * K :=
    Real.sqrt_le_iff.mpr ⟨by positivity, hRic⟩
  have hR := sqrt_normSq_metricRm04_le_ricci_three (co.gInf t) q (by
    change Module.finrank ℝ E3 = 3
    simp)
  have hRRoot : Real.sqrt (normSq0S (co.gInf t) q 4 (metricRm04 (co.gInf t) q)) ≤ 567 * K := by
    nlinarith
  exact (Real.sqrt_le_iff.mp hRRoot).2

end Maps
end DifferentialGeometry.PDE.RicciFlow
