import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.RegularPoleRescalings
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.BackwardSliceSequence
import DifferentialGeometry.Geometry.Metric.DerivativeScaleENorm
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Instances.ENNReal.Lemmas
import DifferentialGeometry.Geometry.Metric.Convergence.ScalingLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Limits.HalfLine


noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Filter Set
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold ContDiff _root_.Topology ENNReal

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)

private local instance backwardEndpointComplete : CompleteSpace E :=
  FiniteDimensional.complete ℝ E
private local instance backwardEndpointTopology : TopologicalSpace F.M := F.topology
private local instance backwardEndpointCharted : ChartedSpace H F.M := F.charted
private local instance backwardEndpointSmooth : IsManifold I ∞ F.M := F.smooth
private local instance backwardEndpointT2 : T2Space F.M := F.t2

variable (hcar : D.carrier = Iic 0) (hreg : D.regular = Iio 0)
  (b : ℝ) (hbmem : b ∈ D.carrier) (tau : ℕ → ℝ)
  (htau : ∀ i, 0 < tau i) (q : ℕ → F.M) (hsigma : ∀ i, 0 < tau i + b)

theorem backwardSliceSequence_metric_eq_scale_poleEndpoint
    (i : ℕ) :
    ((backwardSliceSequence F tau htau q).obj i).metric =
      scaleMetric ((tau i + b) / tau i) (div_pos (hsigma i) (htau i))
        (((poleEndpointRescaledFlowSeq F hcar hreg b hbmem
          tau q hsigma).term i).S.base.metric 0) := by
  rw [backwardSliceSequence_metric, poleEndpointRescaledFlowSeq_metric_zero]
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  change (tau i)⁻¹ * (F.S.base.metric (-tau i)).inner x v w =
    ((tau i + b) / tau i) *
      ((tau i + b)⁻¹ * (F.S.base.metric (-tau i)).inner x v w)
  field_simp [(htau i).ne', (hsigma i).ne']

theorem backwardSliceSequence_metricDerivNorm_poleEndpoint
    (i m : ℕ) (x : F.M) :
    metricDerivNorm m ((backwardSliceSequence F tau htau q).obj i).metric
        (((poleEndpointRescaledFlowSeq F hcar hreg b hbmem tau q hsigma).term i).S.base.metric 0)
        (((poleEndpointRescaledFlowSeq F hcar hreg b hbmem
          tau q hsigma).term i).S.base.metric 0) x =
      if m = 0 then |b / tau i| * Real.sqrt (Module.finrank ℝ E : ℝ) else 0 := by
  let g : SmoothRiemannianMetric I F.M :=
    ((poleEndpointRescaledFlowSeq F hcar hreg b hbmem tau q hsigma).term i).S.base.metric 0
  change metricDerivNorm (I := I) (M := F.M) m
    ((backwardSliceSequence F tau htau q).obj i).metric g g x = _
  have hmetric : (((backwardSliceSequence F tau htau q).obj i).metric :
      SmoothRiemannianMetric I F.M) =
      scaleMetric ((tau i + b) / tau i) (div_pos (hsigma i) (htau i)) g :=
    backwardSliceSequence_metric_eq_scale_poleEndpoint F hcar hreg b hbmem tau htau q hsigma i
  erw [hmetric, metricDerivNorm_scaleMetric_self]
  have hratio : (tau i + b) / tau i - 1 = b / tau i := by
    field_simp [(htau i).ne']
    ring
  rw [hratio]

theorem backwardSliceSequence_metricDerivENormSupOn_poleEndpoint
    {K : Set F.M} (hK : K.Nonempty) (i m : ℕ) :
    metricDerivENormSupOn K m ((backwardSliceSequence F tau htau q).obj i).metric
        (((poleEndpointRescaledFlowSeq F hcar hreg b hbmem tau q hsigma).term i).S.base.metric 0)
        (((poleEndpointRescaledFlowSeq F hcar hreg b hbmem tau q hsigma).term i).S.base.metric 0) =
      ENNReal.ofReal (|b / tau i| * Real.sqrt (Module.finrank ℝ E : ℝ)) := by
  let g : SmoothRiemannianMetric I F.M :=
    ((poleEndpointRescaledFlowSeq F hcar hreg b hbmem tau q hsigma).term i).S.base.metric 0
  change metricDerivENormSupOn (I := I) (M := F.M) K m
    ((backwardSliceSequence F tau htau q).obj i).metric g g = _
  have hmetric : (((backwardSliceSequence F tau htau q).obj i).metric :
      SmoothRiemannianMetric I F.M) =
      scaleMetric ((tau i + b) / tau i) (div_pos (hsigma i) (htau i)) g :=
    backwardSliceSequence_metric_eq_scale_poleEndpoint F hcar hreg b hbmem tau htau q hsigma i
  erw [hmetric, metricDerivENormSupOn_scaleMetric_self hK]
  have hratio : (tau i + b) / tau i - 1 = b / tau i := by
    field_simp [(htau i).ne']
    ring
  rw [hratio]

theorem backwardSliceSequence_metricDerivENormSupOn_poleEndpoint_tendsto_zero
    (hescape : Tendsto tau atTop atTop) (K : Set F.M) (m : ℕ) :
    Tendsto (fun i =>
      metricDerivENormSupOn K m ((backwardSliceSequence F tau htau q).obj i).metric
        (((poleEndpointRescaledFlowSeq F hcar hreg b hbmem tau q hsigma).term i).S.base.metric 0)
        (((poleEndpointRescaledFlowSeq F hcar hreg b hbmem
          tau q hsigma).term i).S.base.metric 0)) atTop (𝓝 0) := by
  rcases K.eq_empty_or_nonempty with rfl | hK
  · have hempty (i : ℕ) : metricDerivENormSupOn (I := I) (M := F.M) ∅ m
        ((backwardSliceSequence F tau htau q).obj i).metric
        (((poleEndpointRescaledFlowSeq F hcar hreg b hbmem tau q hsigma).term i).S.base.metric 0)
        (((poleEndpointRescaledFlowSeq F hcar hreg b hbmem
          tau q hsigma).term i).S.base.metric 0) = 0 := by
      simp only [metricDerivENormSupOn, Set.mem_empty_iff_false, iSup_false,
        ENNReal.bot_eq_zero, ENNReal.iSup_zero]
    simpa only [hempty] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) atTop (𝓝 0))
  · simp_rw [backwardSliceSequence_metricDerivENormSupOn_poleEndpoint F hcar hreg
      b hbmem tau htau q hsigma hK]
    have herror : Tendsto
        (fun i => |b / tau i| * Real.sqrt (Module.finrank ℝ E : ℝ)) atTop (𝓝 0) := by
      simpa only [abs_zero, zero_mul] using
        ((hescape.const_div_atTop b).abs.mul_const (Real.sqrt (Module.finrank ℝ E : ℝ)))
    simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal herror

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Filter Set
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold ContDiff _root_.Topology ENNReal

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {D : RealTimeInterval}
  {P : PointedRiemannianManifold.{u, uE, uH} (I := I)} {phi : ℕ → ℕ}

private local instance normalizedEndpointComplete : CompleteSpace E :=
  FiniteDimensional.complete ℝ E

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

theorem poleEndpoint_scaled_extension_converges
    (F : PointedFlowData.{u, uE, uH} (I := I) D)
    (hcar : D.carrier = Iic 0) (hreg : D.regular = Iio 0)
    (b : ℝ) (hbmem : b ∈ D.carrier) (tau : ℕ → ℝ)
    (htau : ∀ i, 0 < tau i) (q : ℕ → F.M) (hsigma : ∀ i, 0 < tau i + b)
    (Phi : PointedCGHMaps
      (poleEndpointRescaledFlowSeq F hcar hreg b hbmem tau q hsigma) P phi)
    (R : SmoothRiemannianMetric I P.M)
    (bf : BumpFamily Phi) (hsrc : SourceIsSigmaCompact Phi) (htgt : TargetIsSigmaCompact Phi)
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (hphi : StrictMono phi) (hescape : Tendsto tau atTop atTop) :
    MetricCInfConvergenceOnCompacts
      (fun k => scaleMetric ((tau (phi (co.φ k)) + b) / tau (phi (co.φ k)))
        (div_pos (hsigma (phi (co.φ k))) (htau (phi (co.φ k))))
        (gSeqExt Phi R bf hsrc htgt (co.φ k) 0)) (co.gInf 0) (co.gInf 0) := by
  have hconv : MetricCInfConvergenceOnCompacts (I := I) (M := P.M)
      (fun k => gSeqExt Phi R bf hsrc htgt (co.φ k) 0) (co.gInf 0) (co.gInf 0) :=
    HalfLineMetricConvergenceData.canonical_metric_convergence
      (I := I) (X := poleEndpointRescaledFlowSeq F hcar hreg b hbmem tau q hsigma)
      (P := P) (subseq := phi) Phi co (t := 0) le_rfl
  apply MetricCInfConvergenceOnCompacts.scaleMetric_of_tendsto_one
    (I := I) (M := P.M) hconv
    (fun k => div_pos (hsigma (phi (co.φ k))) (htau (phi (co.φ k))))
  have htail : Tendsto (fun k => tau (phi (co.φ k))) atTop atTop :=
    hescape.comp (hphi.tendsto_atTop.comp co.strictMono.tendsto_atTop)
  have hratio : (fun k => (tau (phi (co.φ k)) + b) / tau (phi (co.φ k))) =
      fun k => 1 + b / tau (phi (co.φ k)) := by
    funext k
    rw [add_div, div_self (htau (phi (co.φ k))).ne']
  rw [hratio]
  simpa only [add_zero] using
    (tendsto_const_nhds.add (htail.const_div_atTop b) :
      Tendsto (fun k => (1 : ℝ) + b / tau (phi (co.φ k))) atTop (𝓝 (1 + 0)))

theorem eventually_poleEndpoint_scaled_extension_eq_backwardSlice_pullback
    (F : PointedFlowData.{u, uE, uH} (I := I) D)
    (hcar : D.carrier = Iic 0) (hreg : D.regular = Iio 0)
    (b : ℝ) (hbmem : b ∈ D.carrier) (tau : ℕ → ℝ)
    (htau : ∀ i, 0 < tau i) (q : ℕ → F.M) (hsigma : ∀ i, 0 < tau i + b)
    (Phi : PointedCGHMaps
      (poleEndpointRescaledFlowSeq F hcar hreg b hbmem tau q hsigma) P phi)
    (R : SmoothRiemannianMetric I P.M)
    (bf : BumpFamily Phi) (hsrc : SourceIsSigmaCompact Phi) (htgt : TargetIsSigmaCompact Phi)
    (K : Set P.M) (hK : IsCompact K) :
    ∀ᶠ i in atTop, ∃ U : Set P.M, IsOpen U ∧ K ⊆ U ∧ U ⊆ Phi.source i ∧
      ∀ x ∈ U, ∀ v w : TangentSpace I x,
        (scaleMetric ((tau (phi i) + b) / tau (phi i))
          (div_pos (hsigma (phi i)) (htau (phi i)))
          (gSeqExt Phi R bf hsrc htgt i 0)).inner x v w =
        ((backwardSliceSequence F tau htau q).obj (phi i)).metric.inner
          (Phi.map i x) (mfderiv I I (Phi.map i) x v) (mfderiv I I (Phi.map i) x w) := by
  filter_upwards [eventually_gSeqExt_eq_pullback (I := I)
    (X := poleEndpointRescaledFlowSeq F hcar hreg b hbmem tau q hsigma) (P := P)
    (phi := phi) Phi R bf hsrc htgt K hK] with i hi
  obtain ⟨U, hU, hKU, hUsrc, hinner⟩ := hi
  refine ⟨U, hU, hKU, hUsrc, fun x hx v w => ?_⟩
  let y : F.M := Phi.map i x
  let v' : TangentSpace I y := mfderiv I I (Phi.map i) x v
  let w' : TangentSpace I y := mfderiv I I (Phi.map i) x w
  let g : SmoothRiemannianMetric I F.M :=
    ((poleEndpointRescaledFlowSeq F hcar hreg b hbmem
      tau q hsigma).term (phi i)).S.base.metric 0
  let gBack : SmoothRiemannianMetric I F.M :=
    ((backwardSliceSequence F tau htau q).obj (phi i)).metric
  have hmetric : gBack =
      scaleMetric ((tau (phi i) + b) / tau (phi i))
        (div_pos (hsigma (phi i)) (htau (phi i))) g :=
    backwardSliceSequence_metric_eq_scale_poleEndpoint F hcar hreg b hbmem
      tau htau q hsigma (phi i)
  have heval : gBack.inner y v' w' =
      ((tau (phi i) + b) / tau (phi i)) * g.inner y v' w' := by
    simpa only [scaleMetric_inner] using
      congrArg (fun metric : SmoothRiemannianMetric I F.M => metric.inner y v' w') hmetric
  have hpull : (gSeqExt Phi R bf hsrc htgt i 0).inner x v w = g.inner y v' w' :=
    hinner 0 x hx v w
  change ((tau (phi i) + b) / tau (phi i)) *
    (gSeqExt Phi R bf hsrc htgt i 0).inner x v w = gBack.inner y v' w'
  exact (congrArg (fun z : ℝ => ((tau (phi i) + b) / tau (phi i)) * z) hpull).trans
    heval.symm

theorem exists_backwardSlice_canonical_metric_convergence_of_poleEndpoint
    (F : PointedFlowData.{u, uE, uH} (I := I) D)
    (hcar : D.carrier = Iic 0) (hreg : D.regular = Iio 0)
    (b : ℝ) (hbmem : b ∈ D.carrier) (tau : ℕ → ℝ)
    (htau : ∀ i, 0 < tau i) (q : ℕ → F.M) (hsigma : ∀ i, 0 < tau i + b)
    (Phi : PointedCGHMaps
      (poleEndpointRescaledFlowSeq F hcar hreg b hbmem tau q hsigma) P phi)
    (R : SmoothRiemannianMetric I P.M)
    (bf : BumpFamily Phi) (hsrc : SourceIsSigmaCompact Phi) (htgt : TargetIsSigmaCompact Phi)
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (hphi : StrictMono phi) (hescape : Tendsto tau atTop atTop) :
    ∃ Psi : PointedRiemannianConvergenceMaps (backwardSliceSequence F tau htau q)
        ({ P with metric := co.gInf 0 } : PointedRiemannianManifold (I := I))
        (phi ∘ co.φ),
      (∀ k, Psi.partialDiffeomorph k = Phi.partialDiffeomorph (co.φ k)) ∧
      ∃ C : MetricConvergenceData (I := I)
          (X := backwardSliceSequence F tau htau q)
          (L := ({ P with metric := co.gInf 0 } : PointedRiemannianManifold (I := I)))
          (subseq := phi ∘ co.φ) Psi,
        (∀ k : ℕ, C.domain k =
          CanonicalMetricCompactness.canonicalSourceData (I := I) Psi k) ∧
        (∀ k : ℕ,
          let d : MetricSourceData (I := I)
            (X := backwardSliceSequence F tau htau q)
            (L := ({ P with metric := co.gInf 0 } : PointedRiemannianManifold (I := I)))
            (subseq := phi ∘ co.φ) Psi k := C.domain k
          letI : TopologicalSpace (MetricSourceDomain (I := I) Psi k) := d.topology
          letI : ChartedSpace H (MetricSourceDomain (I := I) Psi k) := d.charted
          letI : IsManifold I ∞ (MetricSourceDomain (I := I) Psi k) := d.smooth
          d.referenceMetric = d.limitMetric) := by
  let X₀ : PointedRiemannianSeq.{u, uE, uH} (I := I) :=
    backwardSliceSequence F tau htau q
  let Y₀ : PointedFlowSeq.{u, uE, uH} (I := I) :=
    poleEndpointRescaledFlowSeq F hcar hreg b hbmem tau q hsigma
  let Q : PointedRiemannianManifold.{u, uE, uH} (I := I) :=
    { P with metric := co.gInf 0 }
  let Phi' : PointedCGHMaps (I := I) Y₀ P (phi ∘ co.φ) :=
    PointedCGHMaps.compSubseq (I := I) (X := Y₀) (P := P) (subseq := phi)
      Phi co.φ co.strictMono
  let Psi : PointedRiemannianConvergenceMaps (I := I) X₀ Q (phi ∘ co.φ) :=
    { partialDiffeomorph := Phi'.partialDiffeomorph
      source_exhausts := Phi'.source_exhausts
      base_mem := Phi'.base_mem
      basepoint_map := Phi'.basepoint_map }
  let G : ℕ → SmoothRiemannianMetric I P.M := fun k =>
    scaleMetric ((tau (phi (co.φ k)) + b) / tau (phi (co.φ k)))
      (div_pos (hsigma (phi (co.φ k))) (htau (phi (co.φ k))))
      (gSeqExt (I := I) (X := Y₀) (P := P) (subseq := phi)
        Phi R bf hsrc htgt (co.φ k) 0)
  have hG : MetricCInfConvergenceOnCompacts (I := I) (M := P.M) G
      (co.gInf 0) (co.gInf 0) :=
    poleEndpoint_scaled_extension_converges F hcar hreg b hbmem
      tau htau q hsigma Phi R bf hsrc htgt co hphi hescape
  have hlocal : ∀ K : Set Q.M, IsCompact K → ∀ᶠ k in atTop,
      ∃ U : Set Q.M, IsOpen U ∧ K ⊆ U ∧ U ⊆ Psi.source k ∧
        ∀ x ∈ U, ∀ v w : TangentSpace I x,
          (G k).inner x v w = (X₀.obj ((phi ∘ co.φ) k)).metric.inner
            (Psi.map k x) (mfderiv I I (Psi.map k) x v)
            (mfderiv I I (Psi.map k) x w) := by
    intro K hK
    filter_upwards [co.strictMono.tendsto_atTop.eventually
      (eventually_poleEndpoint_scaled_extension_eq_backwardSlice_pullback
        F hcar hreg b hbmem tau htau q hsigma Phi R bf hsrc htgt K hK)] with k hk
    exact hk
  refine ⟨Psi, fun _ => rfl, ?_⟩
  exact exists_canonicalMetricConvergenceData_of_metric_extension
    (I := I) (X := X₀) (P := Q) (phi := phi ∘ co.φ) Psi G hG hlocal

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
