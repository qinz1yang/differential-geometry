import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.LocalExtensionUniformTimeJets
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedUniformSpatialJets


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open DifferentialGeometry.Tensor.Coordinates
open Bundle Filter Set
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.Measure
open CanonicalNeighborhood
open scoped _root_.Manifold ContDiff _root_.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

private local instance pointedUniformTimeC1 {D : RealTimeInterval}
    (L : PointedFlowData.{u, uE, uH} (I := I) D) : IsManifold I 1 L.M :=
  IsManifold.of_le (I := I) (M := L.M) (n := ∞) (by decide)


theorem pointed_time_jets_uniform_on_closed_time
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    {L : PointedFlowData.{u, uE, uH} (I := I) X.D} {phi : ℕ → ℕ}
    (hdim : Module.finrank ℝ E = 3)
    (Phi : PointedCGHMaps (I := I) X (L.atTime (I := I) 0) phi)
    {κ : ℝ} (hsource : ∀ i, KLim (I := I) κ (X.term i))
    (hnormalized : ∀ i, (X.term i).S.scalar 0 (X.term i).basepoint = 1)
    (hcomplete : MetricComplete (I := I) (L.atTime (I := I) 0))
    (G : ℕ → ℝ → SmoothRiemannianMetric I L.M)
    (hG : ∀ K : Set L.M, IsCompact K → ∀ᶠ i in atTop,
      ∃ U : Set L.M, IsOpen U ∧ K ⊆ U ∧ U ⊆ Phi.source i ∧
      ∀ t : ℝ, ∀ x ∈ U, ∀ v w : TangentSpace I x,
        (G i t).inner x v w = ((X.term (phi i)).S.base.metric t).inner (Phi.map i x)
          (mfderiv I I (Phi.map i) x v) (mfderiv I I (Phi.map i) x w))
    (B : ℕ → ℕ → ℝ → Tensor0SField (I := I) (M := L.M) (n := ∞) 2)
    (C : ℕ → ℝ → Tensor0SField (I := I) (M := L.M) (n := ∞) 2)
    (hBzero : ∀ n s, B n 0 s = metricTensorField (G n s))
    (hCzero : ∀ s, C 0 s = metricTensorField (L.S.base.metric s))
    (hB : ∀ n q s, s ≤ 0 → ∀ x : L.M,
      HasDerivWithinAt (fun t => B n q t x) (B n (q + 1) s x) (Iic 0) s)
    (hC : ∀ q s, s ≤ 0 → ∀ x : L.M,
      HasDerivWithinAt (fun t => C q t x) (C (q + 1) s x) (Iic 0) s)
    {a : ℝ} (ha : a < 0)
    (hconv : ∀ t ∈ Icc a 0,
      ∃ D : MetricConvergenceData (I := I) (Phi.atTime (L := L) t),
        ∀ k, D.domain k = CanonicalMetricCompactness.canonicalSourceData
          (I := I) (Phi.atTime (L := L) t) k)
    (V : TopologicalSpace.Opens L.M) (hV : IsCompact (closure (V : Set L.M)))
    (p : V) (A : ℝ) (hA : 0 ≤ A)
    {U : Set E} (hU : IsOpen U) (hUt : U ⊆ (extChartAt I p).target)
    (hball : ∀ y ∈ U, (extChartAt I (p : L.M)).symm y ∈
      riemannianClosedBallOf (I := I) (L.S.base.metric 0) L.basepoint A)
    {K : Set E} (hK : IsCompact K) (hKU : K ⊆ U) (r q : ℕ)
    (slots : Fin 2 → Fin (Module.finrank ℝ E)) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ Icc a 0, ∀ y ∈ K,
      ‖iteratedFDeriv ℝ r (fun z => B n q t ((extChartAt I (p : L.M)).symm z)
          (fun j => chartBasisVecFiber (I := I) (p : L.M) (slots j)
            ((extChartAt I (p : L.M)).symm z))) y -
        iteratedFDeriv ℝ r (fun z => C q t ((extChartAt I (p : L.M)).symm z)
          (fun j => chartBasisVecFiber (I := I) (p : L.M) (slots j)
            ((extChartAt I (p : L.M)).symm z))) y‖ ≤ ε := by
  classical
  let : NeZero (Module.finrank ℝ E) := ⟨by omega⟩
  let : SigmaCompactSpace V := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen I V.isOpen)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 (hG (closure (V : Set L.M)) hV)
  let G' : ℕ → ℝ → SmoothRiemannianMetric I L.M := fun n => G (n + N₀)
  have hVsource (n : ℕ) : (V : Set L.M) ⊆ Phi.source (n + N₀) := by
    obtain ⟨W, _hW, hVW, hWs, _hpair⟩ := hN₀ (n + N₀) (by omega)
    exact subset_closure.trans (hVW.trans hWs)
  have hpair (n : ℕ) (t : ℝ) (x : L.M) (hx : x ∈ V) (v w : TangentSpace I x) :
      (G' n t).inner x v w = ((X.term (phi (n + N₀))).S.base.metric t).inner
        (Phi.map (n + N₀) x) (mfderiv I I (Phi.map (n + N₀)) x v)
        (mfderiv I I (Phi.map (n + N₀)) x w) := by
    obtain ⟨W, _hW, hVW, _hWs, hp⟩ := hN₀ (n + N₀) (by omega)
    exact hp t x (hVW (subset_closure hx)) v w
  have hflow (n : ℕ) : ∃ T : SolutionOn (I := I) (M := V) X.D,
      IsSolutionOn T ∧ ∀ t, T.base.metric t = (G' n t).restrictOpen (I := I) V :=
    @exists_local_solution_of_pullback E _ _ _ _ H _ I _
      L.M L.topology L.charted L.smooth L.t2 (X.term (phi (n + N₀))).M
      (X.term (phi (n + N₀))).topology (X.term (phi (n + N₀))).charted
      (X.term (phi (n + N₀))).smooth (X.term (phi (n + N₀))).t2
      (X.term (phi (n + N₀))).sigmaCompact X.D (X.term (phi (n + N₀))).S
      (X.term (phi (n + N₀))).isSolution (Phi.partialDiffeomorph (n + N₀)) V
      inferInstance (hVsource n) (G' n) (hpair n)
  choose T hT hmetric using hflow
  have hgram (i j : Fin (Module.finrank ℝ E)) (Q : Set E) (hQ : IsCompact Q)
      (hQU : Q ⊆ U) (m : ℕ) (ε : ℝ) (hε : 0 < ε) :
      ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ Icc a 0, ∀ y ∈ Q,
        ‖iteratedFDeriv ℝ m (chartGramOnE (I := I) (G' n t) (p : L.M) i j) y -
          iteratedFDeriv ℝ m (chartGramOnE (I := I) (L.S.base.metric t) (p : L.M) i j) y‖ ≤ ε := by
    obtain ⟨N, hN⟩ := pointed_spatial_jets_uniform_on_closed_time Phi hsource G hG hconv
      hdim hnormalized hcomplete ha A hA (p : L.M) i j hU
      (hUt.trans (extChartAt_opens_target_subset V p)) hball hQ hQU m ε hε
    exact ⟨N, fun n hn t ht y hy => hN (n + N₀) (by omega) t ht y hy⟩
  intro ε hε
  obtain ⟨N, hN⟩ := local_extensions_uniform_mixed_coordinate_jets V T hT L.S L.isSolution
    (hsource 0).carrier_eq (hsource 0).regular_eq G' hmetric
    (fun n => B (n + N₀)) C (fun n => hBzero (n + N₀)) hCzero
    (fun n => hB (n + N₀)) hC isCompact_Icc (fun _ ht => ht.2) p hU hUt hgram
    hK hKU r q slots ε hε
  refine ⟨N + N₀, fun n hn t ht y hy => ?_⟩
  have hh := hN (n - N₀) (by omega) t ht y hy
  simpa only [Nat.sub_add_cancel (by omega : N₀ ≤ n)] using hh

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
