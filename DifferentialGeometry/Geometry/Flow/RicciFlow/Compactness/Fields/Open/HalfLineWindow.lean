import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.Open.Equation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.Open.Completeness

open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

open Set Function Filter Bundle Manifold
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace CheegerGromovCompactness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {X : PointedFlowSeq (I := I)}
variable {P : PointedRiemannianManifold (I := I)}
variable {subseq : Nat → Nat}
variable (Φ : PointedCGHMaps (I := I) X P subseq)

noncomputable def flowMetricConvergenceDataOfHalfLineWindow
    (R : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M)
    (bf : BumpFamily (I := I) Φ) (hsrc : SourceIsSigmaCompact Φ) (htgt : TargetIsSigmaCompact Φ)
    (φ : Nat → Nat) (hφ : StrictMono φ)
    (gInf : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      Real → SmoothRiemannianMetric I P.M)
    (n : Nat)
    (hconv : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      letI : T2Space P.M := P.t2
      letI : SigmaCompactSpace P.M := P.sigmaCompact
      ∀ K : Set P.M, IsCompact K → ∀ p : Nat, ∀ ε : Real, 0 < ε →
        ∃ k₀ : Nat, ∀ k : Nat, k₀ ≤ k → ∀ t : Real, t ∈ Set.Icc (-(n : Real)) 0 →
          metricDerivNormSupOn (I := I) K p
            (gSeqExt (I := I) Φ R bf hsrc htgt (φ k) t) (gInf t) R < ε) :
    FlowMetricConvergenceData (I := I) Φ R bf hsrc htgt (-(n : Real)) 0 where
  φ := φ
  strictMono := hφ
  gInf := gInf
  convergence := hconv
  convergencePt := by
    let : TopologicalSpace P.M := P.topology
    let : ChartedSpace H P.M := P.charted
    let : T2Space P.M := P.t2
    let : IsManifold I ∞ P.M := P.smooth
    let : SigmaCompactSpace P.M := P.sigmaCompact
    intro K hK p ε hε
    obtain ⟨k₀, hk₀⟩ := hconv K hK p ε hε
    exact ⟨k₀, fun k hk t ht a ha x hx =>
      lt_of_le_of_lt
        (derivNorm_le_sup (I := I) (a := a) (p := p) hK ha
          (gSeqExt (I := I) Φ R bf hsrc htgt (φ k) t) (gInf t) R hx)
        (hk₀ k hk t ht)⟩

theorem halfLineWindow_gInf_pde
    {R : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M}
    {bf : BumpFamily (I := I) Φ} {hsrc : SourceIsSigmaCompact Φ} {htgt : TargetIsSigmaCompact Φ}
    {β ψ : Real} (hwin : Set.Icc β ψ ⊆ X.D.regular)
    (co : FlowMetricConvergenceData (I := I) Φ R bf hsrc htgt β ψ)
    (cLow : Real) (hcLow : 0 < cLow)
    (hbound : letI : TopologicalSpace P.M := P.topology
        letI : ChartedSpace H P.M := P.charted
        letI : IsManifold I ∞ P.M := P.smooth
      ∀ (k : Nat) (t : Real), t ∈ Set.Icc β ψ →
        ∀ (y : SourceDomain (I := I) Φ k)
          (v : letI : TopologicalSpace (SourceDomain (I := I) Φ k) :=
                sourceDomTop (I := I) Φ k
            letI : ChartedSpace H (SourceDomain (I := I) Φ k) :=
                sourceDomCharted (I := I) Φ k
            TangentSpace I y),
          cLow * R.inner (y : P.M) v v ≤
            letI : TopologicalSpace (SourceDomain (I := I) Φ k) :=
              sourceDomTop (I := I) Φ k
            letI : ChartedSpace H (SourceDomain (I := I) Φ k) :=
              sourceDomCharted (I := I) Φ k
            letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) :=
              sourceDomSmooth (I := I) Φ k
            (sourceMetric (I := I) Φ hsrc htgt k t).inner y v v)
    (hcovTail : letI : TopologicalSpace P.M := P.topology
        letI : ChartedSpace H P.M := P.charted
        letI : T2Space P.M := P.t2
        letI : IsManifold I ∞ P.M := P.smooth
        letI : SigmaCompactSpace P.M := P.sigmaCompact
      ∀ q : Nat, ∃ C : Real, ∀ (k : Nat) (t : Real), t ∈ Set.Icc β ψ →
        ∀ z : P.M, z ∈ bf.grow k →
          metricCovDerivNorm (I := I) q
            (gSeqExt (I := I) Φ R bf hsrc htgt k t) R z ≤ C)
    {t : Real} (hβt : β < t) (htψ : t < ψ)
    (x : P.M) (v w : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      TangentSpace I x) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : T2Space P.M := P.t2
    letI : IsManifold I ∞ P.M := P.smooth
    letI : SigmaCompactSpace P.M := P.sigmaCompact
    HasDerivAt (fun s : Real => (co.gInf s).inner x v w)
      ((-2 : Real) * ricciTensor (I := I) (co.gInf t) x v w) t := by
  let : TopologicalSpace P.M := P.topology
  let : ChartedSpace H P.M := P.charted
  let : T2Space P.M := P.t2
  let : IsManifold I ∞ P.M := P.smooth
  let : SigmaCompactSpace P.M := P.sigmaCompact
  exact (FlowMetricConvergenceData.gInf_pde (I := I) (Φ := Φ) R bf hsrc htgt β ψ hwin
    cLow hcLow hbound hcovTail co x v w ⟨hβt.le, htψ.le⟩).hasDerivAt
      (Icc_mem_nhds hβt htψ)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem halfLineWindow_metricComplete
    {bf : BumpFamily (I := I) Φ} {hsrc : SourceIsSigmaCompact Φ} {htgt : TargetIsSigmaCompact Φ}
    {β ψ : Real} (hP : MetricComplete (I := I) P)
    (co : FlowMetricConvergenceData (I := I) Φ P.metric bf hsrc htgt β ψ)
    {c : Real} (hc : 0 < c)
    (hseq : letI : TopologicalSpace P.M := P.topology
        letI : ChartedSpace H P.M := P.charted
        letI : IsManifold I ∞ P.M := P.smooth
      ∀ (k : Nat) (t : Real), t ∈ Set.Icc β ψ →
        ∀ (x : P.M) (v : TangentSpace I x),
          c * P.metric.inner x v v ≤
            (gSeqExt (I := I) Φ P.metric bf hsrc htgt (co.φ k) t).inner x v v)
    {t : Real} (ht : t ∈ Set.Icc β ψ) :
    MetricComplete (I := I)
      ({ P with metric := co.gInf t } : PointedRiemannianManifold (I := I)) := by
  let : TopologicalSpace P.M := P.topology
  let : ChartedSpace H P.M := P.charted
  let : T2Space P.M := P.t2
  let : IsManifold I ∞ P.M := P.smooth
  let : SigmaCompactSpace P.M := P.sigmaCompact
  exact MetricComplete.complete_of_lower P hP (co.gInf t) c hc
    (FlowMetricConvergenceData.lower_of (I := I) (Φ := Φ) co hseq t ht)

end CheegerGromovCompactness
end DifferentialGeometry
