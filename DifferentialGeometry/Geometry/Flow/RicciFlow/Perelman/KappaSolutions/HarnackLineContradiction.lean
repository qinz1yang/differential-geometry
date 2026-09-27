import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedScalarConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedSectionalCurvature
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.RiemannianLineLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SurfaceLineScalarFlat
import DifferentialGeometry.Geometry.Curvature.Metric.Scaling

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open scoped _root_.Manifold ContDiff _root_.Topology BigOperators

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

local instance harnackLineContradictionC1 {N : Type*} [TopologicalSpace N]
    [ChartedSpace H N] [IsManifold I ∞ N] : IsManifold I 1 N :=
  IsManifold.of_le (I := I) (M := N) (n := ∞) (by decide)

section ExactSequenceTransport

variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
  {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
  {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}

local instance harnackLineTransportTopology : TopologicalSpace L.M := L.topology
local instance harnackLineTransportCharted : ChartedSpace H L.M := L.charted
local instance harnackLineTransportSmooth : IsManifold I ∞ L.M := L.smooth

private theorem harnackLine_of_exact_rescaled_sequence
    [NeZero (Module.finrank ℝ E)]
    (g : SmoothRiemannianMetric I M) (hg : RiemannianMetricComplete (I := I) g)
    (hsec : ∀ y : M, metricRm04At (I := I) g y ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M))
    (p : M) (x : ℕ → M) (lam : ℕ → ℝ) (hlam : ∀ i, 0 < lam i)
    (hX : X = spatialRescaledPointedSeq g x lam hlam)
    (hescape : Tendsto (fun i => (riemannianEDistOf (I := I) g p (x i)).toReal)
      atTop atTop)
    (hscaled : Tendsto (fun i => lam i *
      (riemannianEDistOf (I := I) g p (x i)).toReal) atTop atTop)
    {psi : ℕ → ℕ} (hpsi : StrictMono psi)
    (Phi : PointedRiemannianConvergenceMaps (I := I) X L psi)
    (C : MetricConvergenceData (I := I) Phi)
    (hreference : ∀ k, (C.domain k).referenceMetric = (C.domain k).limitMetric)
    (hcomplete : MetricComplete (I := I) L) (hconnected : ConnectedSpace L.M) :
    ∃ gamma : ℝ → L.M, gamma 0 = L.basepoint ∧
      ∀ s t : ℝ, riemannianEDistOf (I := I) L.metric (gamma s) (gamma t) =
        ENNReal.ofReal |s - t| := by
  subst X
  obtain ⟨gamma, -, hbase, hline⟩ :=
    exists_riemannian_line_of_rescaled_pointed_convergence
      g hg hsec p x lam hlam hescape hscaled hpsi Phi C hreference hcomplete hconnected
  exact ⟨gamma, hbase, hline⟩

end ExactSequenceTransport

variable {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)

local instance harnackLineFlowTopology : TopologicalSpace F.M := F.topology
local instance harnackLineFlowCharted : ChartedSpace H F.M := F.charted
local instance harnackLineFlowSmooth : IsManifold I ∞ F.M := F.smooth
local instance harnackLineFlowT2 : T2Space F.M := F.t2
local instance harnackLineFlowSigmaCompact : SigmaCompactSpace F.M := F.sigmaCompact

theorem false_of_harnack_terminal_normalized_metric_compactness
    {kappa : ℝ} (hK : KLim kappa F) (hdim : Module.finrank ℝ E = 2)
    (p : F.M) (x : ℕ → F.M) (hQ : ∀ i, 0 < F.S.scalar 0 (x i))
    (hescape : Tendsto
      (fun i => (riemannianEDistOf (I := I) (F.S.base.metric 0) p (x i)).toReal)
      atTop atTop)
    (hscaled : Tendsto (fun i => Real.sqrt (F.S.scalar 0 (x i)) *
      (riemannianEDistOf (I := I) (F.S.base.metric 0) p (x i)).toReal) atTop atTop)
    (P : MetricCompactLimit (I := I)
      ((terminalCurvatureNormalizedFlowSeq F hK x hQ).atZero (I := I)))
    (hcanonical : ∀ k, P.convergence.metrics.domain k =
      CanonicalMetricCompactness.canonicalSourceData (I := I) P.maps k)
    (hreference : ∀ k : ℕ,
      let C := P.convergence.metrics.domain k
      let _ : TopologicalSpace (MetricSourceDomain (I := I) P.maps k) := C.topology
      let _ : ChartedSpace H (MetricSourceDomain (I := I) P.maps k) := C.charted
      let _ : IsManifold I ∞ (MetricSourceDomain (I := I) P.maps k) := C.smooth
      C.referenceMetric = C.limitMetric)
    (hconnected : @ConnectedSpace P.limit.M P.limit.topology) : False := by
  let _ : NeZero (Module.finrank ℝ E) := ⟨by omega⟩
  let _ : ConnectedSpace F.M := hK.connected
  let L := P.limit
  let _ : TopologicalSpace L.M := L.topology
  let _ : ChartedSpace H L.M := L.charted
  let _ : IsManifold I ∞ L.M := L.smooth
  let _ : T2Space L.M := L.t2
  let _ : SigmaCompactSpace L.M := L.sigmaCompact
  let _ : ConnectedSpace L.M := hconnected
  have hzero : (0 : ℝ) ∈ D.carrier := by
    simpa only [hK.carrier_eq, Set.mem_Iic] using (le_rfl : (0 : ℝ) ≤ 0)
  have hcompleteSource : RiemannianMetricComplete (I := I) (F.S.base.metric 0) :=
    ⟨hK.complete 0 hzero⟩
  have hsecSource : ∀ y : F.M, metricRm04At (I := I) (F.S.base.metric 0) y ∈
      tensor04SectionalNonnegativeCone (I := I) (M := F.M) := by
    intro y
    apply (metricRm04At_mem_tensor04SectionalNonnegativeCone_iff
      (I := I) (F.S.base.metric 0) y).mpr
    intro v w
    have h := hK.nonnegativeCurvatureOperator 0 hzero y 1
      (fun _ => 1) (fun _ => v) (fun _ => w)
    simpa only [Fin.sum_univ_one, one_mul, SolutionFamily.rm04,
      metricRm04_apply, metricRm04StandardAt_apply, vec4] using h
  have hsecSeq : ∀ i : ℕ, ∀ y : F.M,
      let g : SmoothRiemannianMetric I F.M :=
        (((terminalCurvatureNormalizedFlowSeq F hK x hQ).atZero (I := I)).obj i).metric
      metricRm04At (I := I) g y ∈
        tensor04SectionalNonnegativeCone (I := I) (M := F.M) := by
    intro i y
    let g : SmoothRiemannianMetric I F.M :=
      scaleMetric (F.S.scalar 0 (x i)) (hQ i)
        (F.S.base.metric (parabolicTime 0 (F.S.scalar 0 (x i)) 0))
    change metricRm04At (I := I) g y ∈
      tensor04SectionalNonnegativeCone (I := I) (M := F.M)
    apply (metricRm04At_mem_tensor04SectionalNonnegativeCone_iff (I := I) g y).mpr
    intro v w
    dsimp only [g]
    rw [parabolicTime_zero, metricRmStandard_scale]
    exact mul_nonneg (hQ i).le
      (((metricRm04At_mem_tensor04SectionalNonnegativeCone_iff
        (I := I) (F.S.base.metric 0) y).mp (hsecSource y)) v w)
  have hD : P.convergence.metrics.domain =
      CanonicalMetricCompactness.canonicalSourceData P.maps := funext hcanonical
  have hconv : ∀ K : Set L.M, IsCompact K →
      metricSourceConvergesOn (I := I) P.maps
        (CanonicalMetricCompactness.canonicalSourceData P.maps) K 2 := by
    intro K hKc
    have h := P.convergence.metrics.converges K hKc 2
    rw [hD] at h
    exact h
  have hRic : ∀ y : L.M, ∀ v : TangentSpace I y,
      0 ≤ ricciTensor (I := I) L.metric y v v := by
    apply ricci_nonnegative_of_pointed_canonical_convergence hconv
    exact Filter.Eventually.of_forall
      (fun k y _hy => hsecSeq (P.subseq k) (P.maps.map k y))
  have hscalar : metricScalarAt (I := I) L.metric L.basepoint = 1 :=
    terminalCurvatureNormalizedFlowSeq_limit_scalar_base_one
      F hK x hQ P.maps P.convergence.metrics hcanonical
  obtain ⟨gamma, -, hline⟩ := harnackLine_of_exact_rescaled_sequence
    (F.S.base.metric 0) hcompleteSource hsecSource p x
    (fun i => Real.sqrt (F.S.scalar 0 (x i))) (fun i => Real.sqrt_pos.mpr (hQ i))
    (terminalCurvatureNormalizedFlowSeq_atZero_eq F hK x hQ)
    hescape hscaled P.strictMono P.maps P.convergence.metrics hreference
    P.limit_complete hconnected
  have hcompleteLimit : RiemannianMetricComplete (I := I) L.metric :=
    ⟨MetricComplete.complete L P.limit_complete⟩
  have hpos : 0 < metricScalarAt (I := I) L.metric L.basepoint := by
    rw [hscalar]
    exact zero_lt_one
  exact not_intrinsic_line_of_surface_scalar_pos L.metric hcompleteLimit hdim hRic
    L.basepoint hpos ⟨gamma, hline⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
