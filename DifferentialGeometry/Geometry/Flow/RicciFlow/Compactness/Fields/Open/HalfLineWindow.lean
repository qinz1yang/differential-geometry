import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.Open.Equation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.Open.Completeness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.Open.BumpFamilyChange
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Foundations.WindowRestriction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Metric.TerminalWindow
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.Open.TerminalWindowConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.PointedPullbackExtensions

section

open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

open Set Function Filter Bundle _root_.Manifold
open scoped _root_.Manifold Topology ContDiff BigOperators

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

end

end

section

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open Set Filter
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped _root_.Manifold ContDiff _root_.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

theorem _root_.DifferentialGeometry.CheegerGromovCompactness.MetricCompactLimit.exists_halfLineMetricConvergenceData_of_expanding_windows
    {X : FlowSequence.{u}} (P : MetricCompactLimit (X.atTime 0))
    (hcanonical : ∀ k, P.convergence.metrics.domain k =
      CanonicalMetricCompactness.canonicalSourceData P.maps k)
    (hconnected : ConnectedSpace P.limit.M)
    (hprecompact : ∀ i, IsCompact (closure (P.maps.source i)))
    (hsourceconn : ∀ i, IsConnected (P.maps.source i))
    (hnested : ∀ i, closure (P.maps.source i) ⊆ P.maps.source (i + 1))
    (hcapture : MetricSourceCapture P.maps)
    (hnonnegative : SecLower P.limit.metric 0 Set.univ)
    (hzero : ∀ i, 0 ∈ (X.interval i).carrier)
    (hwindow : ∀ A : ℝ, ∀ᶠ i in atTop,
      Icc (-A) 0 ⊆ (X.interval i).carrier ∧ Ioo (-A) 0 ⊆ (X.interval i).regular)
    {C : ℝ} (hcurv : ∀ᶠ i in atTop, ∀ t ∈ (X.interval i).carrier,
      ∀ y, PointedFlowData.rmNormSq (X.term i) t y ≤ C) :
    let Φ := FlowSequence.singletonTimeMaps P.maps 0 hzero
    ∃ (bf : BumpFamily Φ) (hsrc : SourceIsSigmaCompact Φ)
      (htgt : TargetIsSigmaCompact Φ),
      Nonempty (HalfLineMetricConvergenceData Φ P.limit.metric bf hsrc htgt) := by
  classical
  let Φ := FlowSequence.singletonTimeMaps P.maps 0 hzero
  have hsrc : SourceIsSigmaCompact Φ := fun i =>
    DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen I3 (Φ.source_open i)
  have htgt : TargetIsSigmaCompact Φ := fun i =>
    DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen I3 (Φ.target_open i)
  obtain ⟨bf⟩ := nonempty_bumpFamily Φ
  refine ⟨bf, hsrc, htgt, ?_⟩
  apply nonempty_halfLineMetricConvergenceData (Φ := Φ)
  intro n ρ hρ
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    ((P.strictMono.comp hρ).tendsto_atTop.eventually (hwindow ((n : ℝ) + 2)))
  let k : ℕ → ℕ := fun i => ρ (i + N)
  have hk : StrictMono k := hρ.comp (fun _ _ h => Nat.add_lt_add_right h N)
  have hcarrier : ∀ i, Icc (-((n : ℝ) + 2)) 0 ⊆
      (X.interval (P.subseq (k i))).carrier :=
    fun i => (hN (i + N) (by omega)).1
  have hregular : ∀ i, Ioo (-((n : ℝ) + 2)) 0 ⊆
      (X.interval (P.subseq (k i))).regular :=
    fun i => (hN (i + N) (by omega)).2
  let L := MetricCompactLimit.staticTerminalLimitOfWindow P hcanonical hconnected
    hprecompact hsourceconn hnested hcapture hnonnegative k hk hcarrier hregular hcurv
  have hw : 0 < (n : ℝ) + 1 := by positivity
  have hwd : (n : ℝ) + 1 < (n : ℝ) + 2 := by linarith
  obtain ⟨cg, ksrc, ktgt, σ, hσ, gInf, hconv⟩ :=
    L.exists_bumpMetricConvergence_on_window hw hwd
  let τ : ℕ → ℕ := fun i => σ i + N
  have hτ : StrictMono τ := fun _ _ h => Nat.add_lt_add_right (hσ h) N
  refine ⟨τ, hτ, gInf, ?_⟩
  have hconv' := BumpMetricConvergence.mono (Φ := _) hconv
    (Set.Icc_subset_Icc (by linarith : -((n : ℝ) + 1) ≤ -(n : ℝ)) le_rfl)
  apply BumpMetricConvergence.congr_source_metric hσ (hρ.comp hτ) hconv'
  intro i t ht x hx hy v w
  exact (KappaSolutions.pointed_srcMetric_inner_eq_pullback
    (pointedCGHMapsOfManifold (L.windowSequence (hw.le.trans hwd.le))
      L.space L.subseq L.maps) ksrc ktgt (σ i) t x hx v w).trans
    (KappaSolutions.pointed_srcMetric_inner_eq_pullback Φ hsrc htgt
      ((ρ ∘ τ) i) t x hy v w).symm

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

end

section

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open Set Filter
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped _root_.Manifold ContDiff _root_.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

theorem _root_.DifferentialGeometry.CheegerGromovCompactness.MetricCompactLimit.window_bumpMetricConvergence_of_halfLine
    {X : FlowSequence.{u}} (P : MetricCompactLimit (X.atTime 0))
    (hcanonical : ∀ k, P.convergence.metrics.domain k =
      CanonicalMetricCompactness.canonicalSourceData P.maps k)
    (hconnected : ConnectedSpace P.limit.M)
    (hprecompact : ∀ i, IsCompact (closure (P.maps.source i)))
    (hsourceconn : ∀ i, IsConnected (P.maps.source i))
    (hnested : ∀ i, closure (P.maps.source i) ⊆ P.maps.source (i + 1))
    (hcapture : MetricSourceCapture P.maps)
    (hnonnegative : SecLower P.limit.metric 0 Set.univ)
    (hzero : ∀ i, 0 ∈ (X.interval i).carrier)
    {bf : BumpFamily (FlowSequence.singletonTimeMaps P.maps 0 hzero)}
    {hsrc : SourceIsSigmaCompact (FlowSequence.singletonTimeMaps P.maps 0 hzero)}
    {htgt : TargetIsSigmaCompact (FlowSequence.singletonTimeMaps P.maps 0 hzero)}
    (co : HalfLineMetricConvergenceData (FlowSequence.singletonTimeMaps P.maps 0 hzero)
      P.limit.metric bf hsrc htgt)
    {A width C : ℝ} (hw : 0 < width) (hwd : width < A) (N : ℕ)
    (hcarrier : ∀ i, Icc (-A) 0 ⊆
      (X.interval (P.subseq (co.φ (i + N)))).carrier)
    (hregular : ∀ i, Ioo (-A) 0 ⊆
      (X.interval (P.subseq (co.φ (i + N)))).regular)
    (hcurv : ∀ᶠ i in atTop, ∀ t ∈ (X.interval i).carrier,
      ∀ y, PointedFlowData.rmNormSq (X.term i) t y ≤ C) :
    let k : ℕ → ℕ := fun i => co.φ (i + N)
    let hk : StrictMono k := co.strictMono.comp (fun _ _ h => Nat.add_lt_add_right h N)
    let L := MetricCompactLimit.staticTerminalLimitOfWindow P hcanonical hconnected
      hprecompact hsourceconn hnested hcapture hnonnegative k hk hcarrier hregular hcurv
    let Ψ := pointedCGHMapsOfManifold (L.windowSequence (hw.le.trans hwd.le))
      L.space L.subseq L.maps
    ∃ (cg : BumpFamily Ψ) (ksrc : SourceIsSigmaCompact Ψ)
      (ktgt : TargetIsSigmaCompact Ψ),
      BumpMetricConvergence Ψ L.space.metric cg ksrc ktgt id co.gInf (-width) 0 := by
  classical
  let k : ℕ → ℕ := fun i => co.φ (i + N)
  have hk : StrictMono k := co.strictMono.comp (fun _ _ h => Nat.add_lt_add_right h N)
  let L := MetricCompactLimit.staticTerminalLimitOfWindow P hcanonical hconnected
    hprecompact hsourceconn hnested hcapture hnonnegative k hk hcarrier hregular hcurv
  let Ψ := pointedCGHMapsOfManifold (L.windowSequence (hw.le.trans hwd.le))
    L.space L.subseq L.maps
  have ksrc : SourceIsSigmaCompact Ψ := fun i =>
    DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen I3 (Ψ.source_open i)
  have ktgt : TargetIsSigmaCompact Ψ := fun i =>
    DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen I3 (Ψ.target_open i)
  obtain ⟨cg⟩ := nonempty_bumpFamily Ψ
  refine ⟨cg, ksrc, ktgt, ?_⟩
  obtain ⟨n, hn⟩ := exists_nat_ge width
  have hconv := BumpMetricConvergence.mono (Φ := _) (co.convergenceOn n)
    (Set.Icc_subset_Icc (neg_le_neg hn) le_rfl)
  have hshift : StrictMono (fun i : ℕ => i + N) :=
    fun _ _ h => Nat.add_lt_add_right h N
  have htail := BumpMetricConvergence.comp (Φ := _) hconv (fun i => i + N) hshift
  apply BumpMetricConvergence.congr_source_metric (co.strictMono.comp hshift)
    strictMono_id htail
  intro i t ht x hx hy v w
  exact (KappaSolutions.pointed_srcMetric_inner_eq_pullback
    (FlowSequence.singletonTimeMaps P.maps 0 hzero) hsrc htgt
      ((co.φ ∘ fun i => i + N) i) t x hx v w).trans
    (KappaSolutions.pointed_srcMetric_inner_eq_pullback Ψ ksrc ktgt i t x hy v w).symm

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

end
