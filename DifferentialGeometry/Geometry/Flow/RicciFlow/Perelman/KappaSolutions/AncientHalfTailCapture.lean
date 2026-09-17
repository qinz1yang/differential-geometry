import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientTailEstimates
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.BackwardSliceSequence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedInverseDistanceControl

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Set
open DifferentialGeometry.CheegerGromovCompactness CanonicalNeighborhood
open scoped Manifold ContDiff

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type uH} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)
  {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}

private local instance complete : CompleteSpace E := FiniteDimensional.complete ℝ E
private local instance flowTopology : TopologicalSpace F.M := F.topology
private local instance flowCharted : ChartedSpace H F.M := F.charted
private local instance flowSmooth : IsManifold I ∞ F.M := F.smooth
private local instance flowT2 : T2Space F.M := F.t2
private local instance flowSigma : SigmaCompactSpace F.M := F.sigmaCompact
private local instance limitTopology : TopologicalSpace L.M := L.topology
private local instance limitCharted : ChartedSpace H L.M := L.charted
private local instance limitSmooth : IsManifold I ∞ L.M := L.smooth
private local instance limitT2 : T2Space L.M := L.t2
private local instance limitSigma : SigmaCompactSpace L.M := L.sigmaCompact
private local instance limitTangentT2 : T2Space (TangentBundle I L.M) := L.t2TangentBundle

theorem exists_compact_inverse_capture_on_half_tail_of_ancient
    (hdim : Module.finrank ℝ E = 3)
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) (q : ℕ → F.M)
    (alpha : ℕ → ℝ → F.M) (halpha : ∀ i, ContMDiff 𝓘(ℝ, ℝ) I 1 (alpha i))
    (p : F.M) {A D : ℝ} (hD : 0 ≤ D)
    (hgeo : ∀ i, IsLRegularizedGeodesicOn F.S 0 (alpha i)
      (Ioo 0 (Real.sqrt (tau i))))
    (hcost : ∀ i, lRegularizedAction F.S 0 (alpha i) 0 (Real.sqrt (tau i)) =
      lCost F.S 0 p (alpha i (Real.sqrt (tau i))) (tau i))
    (hlength : ∀ i, redLength F.S 0 p (alpha i (Real.sqrt (tau i))) (tau i) ≤ A)
    (hendpoint : ∀ i, riemannianEDistOf
      ((backwardSliceSequence F tau htau q).obj i).metric
      (q i) (alpha i (Real.sqrt (tau i))) ≤ ENNReal.ofReal D)
    {phi : ℕ → ℕ}
    (Phi : PointedRiemannianConvergenceMaps (backwardSliceSequence F tau htau q) L phi)
    (C : MetricConvergenceData Phi)
    (hreference : ∀ k, (C.domain k).referenceMetric = (C.domain k).limitMetric)
    (hcomplete : MetricComplete L) :
    IsCompact (riemannianClosedBallOf L.metric L.basepoint
      (2 * (D + Real.sqrt (2 * Real.exp (24 * A) * A)))) ∧
    ∃ k0 : ℕ, ∀ k, k0 ≤ k →
      ∀ s ∈ Icc (Real.sqrt (tau (phi k)) / 2) (Real.sqrt (tau (phi k))),
        alpha (phi k) s ∈ (Phi.partialDiffeomorph k).target ∧
        (Phi.partialDiffeomorph k).symm (alpha (phi k) s) ∈
          riemannianClosedBallOf L.metric L.basepoint
            (2 * (D + Real.sqrt (2 * Real.exp (24 * A) * A))) ∧
        Phi.partialDiffeomorph k
          ((Phi.partialDiffeomorph k).symm (alpha (phi k) s)) = alpha (phi k) s := by
  let _ : NeZero (Module.finrank ℝ E) := ⟨by omega⟩
  have hrho : 0 ≤ D + Real.sqrt (2 * Real.exp (24 * A) * A) :=
    add_nonneg hD (Real.sqrt_nonneg _)
  obtain ⟨hcompact, k0, hk0⟩ := exists_pointed_inverse_distance_control
    C hreference hcomplete (D + Real.sqrt (2 * Real.exp (24 * A) * A)) hrho 1 zero_lt_one
  refine ⟨by simpa only [one_add_one_eq_two] using hcompact, k0, ?_⟩
  intro k hk s hs
  have htail := riemannianEDist_scaled_endpoint_le_exp_redLength_on_half_tail_of_ancient
    F hdim hF (alpha (phi k)) (halpha (phi k)) p (htau (phi k)) hs
    (hgeo (phi k)) (hcost (phi k)) (hlength (phi k))
  have hball : alpha (phi k) s ∈ riemannianClosedBallOf
      ((backwardSliceSequence F tau htau q).obj (phi k)).metric (q (phi k))
      (D + Real.sqrt (2 * Real.exp (24 * A) * A)) := by
    change riemannianEDistOf _ _ _ ≤ _
    calc
      _ ≤ riemannianEDistOf
          ((backwardSliceSequence F tau htau q).obj (phi k)).metric
          (q (phi k)) (alpha (phi k) (Real.sqrt (tau (phi k)))) +
          riemannianEDistOf
          ((backwardSliceSequence F tau htau q).obj (phi k)).metric
          (alpha (phi k) (Real.sqrt (tau (phi k)))) (alpha (phi k) s) :=
        riemannianEDistOf_triangle _ _ _ _
      _ ≤ ENNReal.ofReal D + ENNReal.ofReal (Real.sqrt (2 * Real.exp (24 * A) * A)) := by
        apply add_le_add (hendpoint (phi k))
        rw [riemannianEDistOf_comm]
        exact htail
      _ = ENNReal.ofReal (D + Real.sqrt (2 * Real.exp (24 * A) * A)) :=
        (ENNReal.ofReal_add hD (Real.sqrt_nonneg _)).symm
  obtain ⟨htarget, hinverse⟩ := (hk0 k hk).1 (alpha (phi k) s) hball
  refine ⟨htarget, ?_, (Phi.partialDiffeomorph k).right_inv' htarget⟩
  simpa only [one_add_one_eq_two] using hinverse

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
