import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.KLimSelectedFlowCompactness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.KLimSelectedLimitGeometry
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.TerminalNormalizedNeck
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SpatialNeckHighCurvature
import DifferentialGeometry.Geometry.Comparison.Soul.PositiveEuclidean

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter _root_.Manifold Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.HopfRinow
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Tensor0SBundle
open CanonicalNeighborhood
open scoped _root_.Manifold ContDiff _root_.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)

private local instance klimPositiveTopology : TopologicalSpace F.M := F.topology
private local instance klimPositiveCharted : ChartedSpace H F.M := F.charted
private local instance klimPositiveSmooth : IsManifold I ∞ F.M := F.smooth
private local instance klimPositiveC1 : IsManifold I 1 F.M :=
  IsManifold.of_le (n := ∞) (by decide)
private local instance klimPositiveT2 : T2Space F.M := F.t2
private local instance klimPositiveSigma : SigmaCompactSpace F.M := F.sigmaCompact
private local instance klimPositiveTangentT2 : T2Space (TangentBundle I F.M) :=
  F.t2TangentBundle

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

theorem KLim.three_terminal_bddAbove_of_positive
    {kappa : ℝ} (hK : KLim kappa F) (hdim : Module.finrank ℝ E = 3)
    (hsec : DifferentialGeometry.Geometry.HasPositiveSectionalCurvature (I := I)
      (F.S.base.metric 0)) : BddAbove (Set.range (F.S.scalar 0)) := by
  classical
  by_contra hunbounded
  let _ : NeZero (Module.finrank ℝ E) := ⟨by omega⟩
  let _ : ConnectedSpace F.M := hK.connected
  let _ : NoncompactSpace F.M := noncompactSpace_of_terminal_scalar_unbounded F hunbounded
  let g : SmoothRiemannianMetric I F.M := F.S.base.metric 0
  have hcomplete : RiemannianMetricComplete (I := I) g :=
    ⟨hK.complete 0 (by
      simpa only [hK.carrier_eq, Set.mem_Iic] using (le_rfl : (0 : ℝ) ≤ 0))⟩
  let _ : TopologicalSpace.MetrizableSpace F.M := Manifold.metrizableSpace I F.M
  let _ : T3Space F.M := inferInstance
  let _ : RiemannianBundle (fun z : F.M => TangentSpace I z) := ⟨g.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E (fun z : F.M => TangentSpace I z) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro z v w; rfl⟩⟩
  let _ : EMetricSpace F.M := EMetricSpace.ofRiemannianMetric I F.M
  let _ : CompleteSpace F.M := hcomplete.complete
  have hEnorm : IsMetricNorm (I := I) g := fun z v =>
    tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := I) g z v
  let _ : MetricSpace F.M := riemMetricSpace (I := I) (M := F.M)
  let _ : ProperSpace F.M := properSpace_riemMetric (I := I) hcomplete.complete g hEnorm
  let _ : IsRiemannianManifold I F.M := ⟨fun z w => by
    rw [edist_dist, riemMetric_dist_eq (I := I)]
    exact ENNReal.ofReal_toReal (Exponential.riemannianEDist_ne_top (I := I) z w)⟩
  obtain ⟨_soul, eSource, _⟩ :=
    DifferentialGeometry.Geometry.Topology.exists_diffeomorph_euclidean_three_of_positiveSectionalCurvature
      g hEnorm hsec hdim
  have hEuclidean : Nonempty (F.M ≃ₘ⟮I, 𝓡 3⟯ EuclideanSpace ℝ (Fin 3)) :=
    ⟨eSource⟩
  obtain ⟨x, r, hQ, _hr, hQescape, _hQr, hexpand, hescape, hscaled,
      _hratio, hlocal, _hbackward, _hlocalAll⟩ :=
    exists_harnack_terminal_blowup_sequence F hK hunbounded F.basepoint
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hexpand.eventually_gt_atTop (1 / 4))
  let shift : ℕ → ℕ := fun i => N + i
  have hshift : StrictMono shift := fun i j hij => Nat.add_lt_add_left hij N
  let x' : ℕ → F.M := x ∘ shift
  let r' : ℕ → ℝ := r ∘ shift
  let hQ' : ∀ i, 0 < F.S.scalar 0 (x' i) := fun i => hQ (shift i)
  have hlocal' (i : ℕ) (z : F.M)
      (hz : (riemannianEDistOf (I := I) g z (x' i)).toReal < r' i) :
      F.S.scalar 0 z ≤ 4 * F.S.scalar 0 (x' i) := hlocal (shift i) z hz
  have hexpand' : Tendsto (fun i => r' i * Real.sqrt (F.S.scalar 0 (x' i)))
      atTop atTop := hexpand.comp hshift.tendsto_atTop
  have hlarge (i : ℕ) : 1 / 4 < r' i * Real.sqrt (F.S.scalar 0 (x' i)) :=
    hN (shift i) (Nat.le_add_right N i)
  obtain ⟨L, phi, hphi, Phi, hconnected, hcompleteL, hconv⟩ :=
    exists_terminalCurvatureNormalizedFlowSeq_klim_three_ancient_limit
      F hK hdim x' r' hQ' hlocal' hexpand' hlarge
  have hcanonical : ∀ t ≤ 0,
      ∃ C : MetricConvergenceData (I := I)
          (Phi.atTime (X := terminalCurvatureNormalizedFlowSeq F hK x' hQ')
            (L := L) (phi := phi) t),
        ∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData
          (I := I) (Phi.atTime (X := terminalCurvatureNormalizedFlowSeq F hK x' hQ')
            (L := L) (phi := phi) t) k := by
    intro t ht
    obtain ⟨C, hC, _⟩ := hconv t ht
    exact ⟨C, hC⟩
  obtain ⟨hL, _hbase, _hscalar, _hRm⟩ :=
    terminalCurvatureNormalizedFlowSeq_klim_ancient_limit_geometry
      F hK hdim x' r' hQ' hlocal' hexpand' L phi hphi Phi
      hconnected hcompleteL hcanonical
  obtain ⟨C0, hC0⟩ := hcanonical 0 le_rfl
  obtain ⟨mark, _e, _hmarked, _hmetric, hnecks⟩ :=
    terminalCurvatureNormalizedFlowSeq_limit_eventually_spatialNeckWitness
      F L hK hL hdim F.basepoint x' hQ'
      (hescape.comp hshift.tendsto_atTop) (hscaled.comp hshift.tendsto_atTop)
      hphi (Phi.atTime (X := terminalCurvatureNormalizedFlowSeq F hK x' hQ')
        (L := L) (phi := phi) 0) C0 hC0 hEuclidean
  obtain ⟨k0, hk0⟩ := hnecks spatialNeckControlEpsilon spatialNeckControlEpsilon_pos
  have hwitness (j : ℕ) :
      Nonempty (SpatialNeckWitness g mark (x' (phi (k0 + j))) spatialNeckControlEpsilon) := by
    obtain ⟨W, _⟩ := hk0 (k0 + j) (Nat.le_add_right k0 j)
    exact ⟨W⟩
  let W := fun j => Classical.choice (hwitness j)
  have htail : StrictMono (fun j : ℕ => k0 + j) :=
    fun i j hij => Nat.add_lt_add_left hij k0
  have hdiverges : Tendsto (fun j => metricScalarAt (I := I) g
      (x' (phi (k0 + j)))) atTop atTop :=
    ((hQescape.comp hshift.tendsto_atTop).comp hphi.tendsto_atTop).comp htail.tendsto_atTop
  exact not_tendsto_scalar_spatialNeck_centers W hEnorm le_rfl hsec hdiverges

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
