import DifferentialGeometry.Geometry.Curvature.RicciNonnegativeConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardClosedReferenceBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardCurvatureOperator
import DifferentialGeometry.Geometry.Curvature.RicciRestriction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.Equation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.Convergence

set_option autoImplicit false
noncomputable section
open Set Filter Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff BigOperators Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow

open DifferentialGeometry.Geometry.Curvature
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

theorem PartialStandardSolution.ricciTensor_nonnegative
    (S : PartialStandardSolution) (t : ℝ) (ht : t ∈ S.domain)
    (q : E3) (v : TangentSpace (𝓡 3) q) :
    0 ≤ ricciTensor (S.metric t) q v v :=
  ricciTensor_nonnegative_of_curvatureOperator_nonnegative (S.metric t) q
    (S.curvatureOperator_nonnegative t ht q) v

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
private local instance (j : ℕ) : TopologicalSpace (TargetDomain Φ j) := targetDomTop Φ j
private local instance (j : ℕ) : ChartedSpace E3 (TargetDomain Φ j) := targetDomCharted Φ j
private local instance (j : ℕ) : T2Space (TargetDomain Φ j) := targetDomT2 Φ j
private local instance (j : ℕ) : IsManifold (𝓡 3) ∞ (TargetDomain Φ j) := targetDomSmooth Φ j
private local instance (j : ℕ) : SigmaCompactSpace (TargetDomain Φ j) :=
  targetDomSigmaOf Φ j (standardClosedPointedMaps_targetSigma Φ j)

private theorem standard_closed_source_ricci_nonnegative
    (j : ℕ) (t : ℝ) (ht : t ∈ Icc 0 τ)
    (q : SourceDomain Φ j) (v : TangentSpace (𝓡 3) q) :
    0 ≤ ricciTensor (sourceMetric Φ hsrc htgt j t) q v v := by
  change 0 ≤ ricciTensor
    (Diffeomorph.pullbackMetric
      (((S (φ j)).val.metric t).restrictOpen (targetOpen Φ j))
      (sourceTargetDiff Φ j)) q v v
  rw [DifferentialGeometry.CheegerGromovCompactness.ricciTensor_pullback,
    DifferentialGeometry.Geometry.Curvature.ricciTensor_restrictOpen]
  apply PartialStandardSolution.ricciTensor_nonnegative
  exact (Icc_subset_lifetimeInterval_iff (S (φ j)).val.lifetime
    (S (φ j)).val.lifetime_pos τ hτ.le).mpr
      (hlt.trans_le (uniformStandardLifetime_le_lifetime (S (φ j)))) ht

theorem standard_closed_limit_ricci_nonnegative
    (bf : BumpFamily Φ) (co : FlowMetricConvergenceData Φ P.metric bf hsrc htgt 0 τ) :
    ∀ t ∈ Icc 0 τ, ∀ (q : P.M) (v : TangentSpace (𝓡 3) q),
      0 ≤ ricciTensor (co.gInf t) q v v := by
  intro t ht q v
  apply ricciTensor_nonnegative_of_local_metric_jet_convergence
    (fun k => gSeqExt Φ P.metric bf hsrc htgt (co.φ k) t) (co.gInf t) P.metric q v
  · intro ε hε
    obtain ⟨kc, hkc⟩ := co.convergencePt {q} isCompact_singleton 2 ε hε
    exact ⟨kc, fun k hk a ha => hkc k hk t ht a ha q (mem_singleton q)⟩
  · obtain ⟨kg, hkg⟩ := bf.grow_cover {q} isCompact_singleton
    refine eventually_atTop.2 ⟨kg, ?_⟩
    intro k hk
    have hq : q ∈ bf.grow (co.φ k) :=
      hkg (co.φ k) (hk.trans (co.strictMono.id_le k)) (mem_singleton q)
    rw [gSeqExt_ricci Φ P.metric bf hsrc htgt (co.φ k) t q hq v v]
    exact standard_closed_source_ricci_nonnegative Φ hsrc htgt (co.φ k) t ht
      ⟨q, bf.grow_subset (co.φ k) hq⟩ v

end Maps
end DifferentialGeometry.PDE.RicciFlow

end
