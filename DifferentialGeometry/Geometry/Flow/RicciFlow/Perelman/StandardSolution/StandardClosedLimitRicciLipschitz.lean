import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardFirstTimeJet
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardClosedRicciLipschitz
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.Convergence

set_option autoImplicit false
noncomputable section

open Set Filter Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.CheegerGromovCompactness
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

theorem standard_closed_source_limit_ricci_lipschitz
    (hinit : ∀ j, sourceMetric Φ hsrc htgt j 0 = sourceMetricRestriction Φ P.metric j)
    (bf : BumpFamily Φ) (co : FlowMetricConvergenceData Φ P.metric bf hsrc htgt 0 τ) :
    ∃ L : ℝ, 0 ≤ L ∧
      (∀ j : ℕ, ∀ s ∈ Icc 0 τ, ∀ t ∈ Icc 0 τ,
        ∀ (q : SourceDomain Φ j) (v w : TangentSpace (𝓡 3) q),
          |ricciTensor (sourceMetric Φ hsrc htgt j s) q v w -
              ricciTensor (sourceMetric Φ hsrc htgt j t) q v w| ≤
            L * Real.sqrt (P.metric.inner q.val v v) *
              Real.sqrt (P.metric.inner q.val w w) * |s - t|) ∧
      (∀ s ∈ Icc 0 τ, ∀ t ∈ Icc 0 τ,
        ∀ (q : P.M) (v w : TangentSpace (𝓡 3) q),
          |ricciTensor (co.gInf s) q v w - ricciTensor (co.gInf t) q v w| ≤
            L * Real.sqrt (P.metric.inner q v v) *
              Real.sqrt (P.metric.inner q w w) * |s - t|) := by
  obtain ⟨L, hL, hfamily⟩ := standard_closed_source_ricci_lipschitz τ hτ hlt
  have hsource := hfamily S x P φ Φ hsrc htgt hinit
  refine ⟨L, hL, hsource, ?_⟩
  intro s hs t ht q v w
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨k, hk⟩ := standard_closed_source_ricci_converges Φ hsrc htgt hinit bf co q v w
    (ε / 2) (by positivity)
  obtain ⟨hq, herror⟩ := hk k le_rfl
  let us : ℝ := ricciTensor (sourceMetric Φ hsrc htgt (co.φ k) s) ⟨q, hq⟩ v w
  let ut : ℝ := ricciTensor (sourceMetric Φ hsrc htgt (co.φ k) t) ⟨q, hq⟩ v w
  let vs : ℝ := ricciTensor (co.gInf s) q v w
  let vt : ℝ := ricciTensor (co.gInf t) q v w
  have hsClose : |us - vs| < ε / 2 := herror s hs
  have htClose : |ut - vt| < ε / 2 := herror t ht
  have hsClose' : |vs - us| < ε / 2 := by
    rw [abs_sub_comm]
    exact hsClose
  have hLip : |us - ut| ≤ L * Real.sqrt (P.metric.inner q v v) *
      Real.sqrt (P.metric.inner q w w) * |s - t| :=
    hsource (co.φ k) s hs t ht ⟨q, hq⟩ v w
  have htri₁ := abs_sub_le vs us vt
  have htri₂ := abs_sub_le us ut vt
  change |vs - vt| ≤ L * Real.sqrt (P.metric.inner q v v) *
    Real.sqrt (P.metric.inner q w w) * |s - t| + ε
  linarith

end Maps
end DifferentialGeometry.PDE.RicciFlow

end
