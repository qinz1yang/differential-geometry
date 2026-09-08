import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.MetricExtension
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Defs
import DifferentialGeometry.Topology.Manifold.OpenSubtype

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Bundle
open scoped Manifold ContDiff

open PDE.RicciFlow.Perelman (lVelocity)

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}

theorem SourceDomainMetricData.pullbackMetric_inner_lVelocity
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    {P : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat → Nat}
    {Phi : PointedCGHMaps (I := I) X P subseq} {k : Nat}
    (D : SourceDomainMetricData (I := I) Phi k)
    (t : Real) (alpha : Real → SourceDomain (I := I) Phi k) (s : Real)
    (hmap :
      let : TopologicalSpace (SourceDomain (I := I) Phi k) := D.topology
      let : ChartedSpace H (SourceDomain (I := I) Phi k) := D.charted
      let : IsManifold I ∞ (SourceDomain (I := I) Phi k) := D.smooth
      let : TopologicalSpace (X.term (subseq k)).M :=
        (X.term (subseq k)).topology
      let : ChartedSpace H (X.term (subseq k)).M :=
        (X.term (subseq k)).charted
      let : IsManifold I ∞ (X.term (subseq k)).M :=
        (X.term (subseq k)).smooth
      MDifferentiableAt I I
        (fun y : SourceDomain (I := I) Phi k ↦ Phi.map k (y : P.M))
        (alpha s))
    (halpha :
      let : TopologicalSpace (SourceDomain (I := I) Phi k) := D.topology
      let : ChartedSpace H (SourceDomain (I := I) Phi k) := D.charted
      let : IsManifold I ∞ (SourceDomain (I := I) Phi k) := D.smooth
      MDifferentiableAt 𝓘(Real, Real) I alpha s) :
    let : TopologicalSpace (SourceDomain (I := I) Phi k) := D.topology
    let : ChartedSpace H (SourceDomain (I := I) Phi k) := D.charted
    let : T2Space (SourceDomain (I := I) Phi k) := D.t2
    let : IsManifold I ∞ (SourceDomain (I := I) Phi k) := D.smooth
    let : SigmaCompactSpace (SourceDomain (I := I) Phi k) := D.sigmaCompact
    let : TopologicalSpace P.M := P.topology
    let : ChartedSpace H P.M := P.charted
    let : T2Space P.M := P.t2
    let : IsManifold I ∞ P.M := P.smooth
    let : SigmaCompactSpace P.M := P.sigmaCompact
    let : TopologicalSpace (X.term (subseq k)).M :=
      (X.term (subseq k)).topology
    let : ChartedSpace H (X.term (subseq k)).M :=
      (X.term (subseq k)).charted
    let : T2Space (X.term (subseq k)).M := (X.term (subseq k)).t2
    let : IsManifold I ∞ (X.term (subseq k)).M :=
      (X.term (subseq k)).smooth
    let : SigmaCompactSpace (X.term (subseq k)).M :=
      (X.term (subseq k)).sigmaCompact
    (D.pullbackMetric t).inner (alpha s)
        (lVelocity (I := I) alpha s) (lVelocity (I := I) alpha s) =
      ((X.term (subseq k)).S.family.metric t).inner
        (Phi.map k (alpha s : P.M))
        (lVelocity (I := I) (fun r ↦ Phi.map k (alpha r : P.M)) s)
        (lVelocity (I := I) (fun r ↦ Phi.map k (alpha r : P.M)) s) := by
  let : TopologicalSpace (SourceDomain (I := I) Phi k) := D.topology
  let : ChartedSpace H (SourceDomain (I := I) Phi k) := D.charted
  let : T2Space (SourceDomain (I := I) Phi k) := D.t2
  let : IsManifold I ∞ (SourceDomain (I := I) Phi k) := D.smooth
  let : SigmaCompactSpace (SourceDomain (I := I) Phi k) := D.sigmaCompact
  let : TopologicalSpace P.M := P.topology
  let : ChartedSpace H P.M := P.charted
  let : T2Space P.M := P.t2
  let : IsManifold I ∞ P.M := P.smooth
  let : IsManifold I ((∞ : WithTop ℕ∞) + 1) P.M := by
    change IsManifold I ∞ P.M
    infer_instance
  let : SigmaCompactSpace P.M := P.sigmaCompact
  let : TopologicalSpace (X.term (subseq k)).M :=
    (X.term (subseq k)).topology
  let : ChartedSpace H (X.term (subseq k)).M :=
    (X.term (subseq k)).charted
  let : T2Space (X.term (subseq k)).M := (X.term (subseq k)).t2
  let : IsManifold I ∞ (X.term (subseq k)).M :=
    (X.term (subseq k)).smooth
  let : IsManifold I ((∞ : WithTop ℕ∞) + 1) (X.term (subseq k)).M := by
    change IsManifold I ∞ (X.term (subseq k)).M
    infer_instance
  let : SigmaCompactSpace (X.term (subseq k)).M :=
    (X.term (subseq k)).sigmaCompact
  dsimp only
  rw [D.pullback_inner]
  have hvel :
      lVelocity (I := I) (fun r ↦ Phi.map k (alpha r : P.M)) s =
        mfderiv I I
          (fun y : SourceDomain (I := I) Phi k ↦ Phi.map k (y : P.M))
          (alpha s) (lVelocity (I := I) alpha s) := by
    with_unfolding_all simpa only [lVelocity, Function.comp_def] using
      (mfderiv_comp_apply (I := 𝓘(Real, Real)) (I' := I) (I'' := I)
        (x := s) (f := alpha)
        (g := fun y : SourceDomain (I := I) Phi k ↦ Phi.map k (y : P.M))
        hmap halpha (1 : Real))
  rw [hvel]


theorem PointedCGHMaps.sourceMetric_inner_lVelocity
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    {P : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat → Nat}
    (Phi : PointedCGHMaps (I := I) X P subseq)
    (hsrc : SourceIsSigmaCompact Phi) (htgt : TargetIsSigmaCompact Phi)
    (k : Nat) (t : Real) (alpha : Real → P.M) (s : Real)
    (hs : let : TopologicalSpace P.M := P.topology
      alpha s ∈ Phi.source k)
    (halpha : let : TopologicalSpace P.M := P.topology
      let : ChartedSpace H P.M := P.charted
      let : IsManifold I ∞ P.M := P.smooth
      MDifferentiableAt 𝓘(Real, Real) I alpha s) :
    let : TopologicalSpace P.M := P.topology
    let : ChartedSpace H P.M := P.charted
    let : T2Space P.M := P.t2
    let : IsManifold I ∞ P.M := P.smooth
    let : SigmaCompactSpace P.M := P.sigmaCompact
    let : TopologicalSpace (SourceDomain (I := I) Phi k) :=
      sourceDomTop (I := I) Phi k
    let : ChartedSpace H (SourceDomain (I := I) Phi k) :=
      sourceDomCharted (I := I) Phi k
    let : T2Space (SourceDomain (I := I) Phi k) := sourceDomT2 (I := I) Phi k
    let : IsManifold I ∞ (SourceDomain (I := I) Phi k) :=
      sourceDomSmooth (I := I) Phi k
    let : SigmaCompactSpace (SourceDomain (I := I) Phi k) :=
      sourceDomSigmaOf (I := I) Phi k (hsrc k)
    let : TopologicalSpace (X.term (subseq k)).M :=
      (X.term (subseq k)).topology
    let : ChartedSpace H (X.term (subseq k)).M :=
      (X.term (subseq k)).charted
    let : T2Space (X.term (subseq k)).M := (X.term (subseq k)).t2
    let : IsManifold I ∞ (X.term (subseq k)).M :=
      (X.term (subseq k)).smooth
    let : SigmaCompactSpace (X.term (subseq k)).M :=
      (X.term (subseq k)).sigmaCompact
    (sourceMetric (I := I) Phi hsrc htgt k t).inner ⟨alpha s, hs⟩
        (lVelocity (I := I) alpha s) (lVelocity (I := I) alpha s) =
      ((X.term (subseq k)).S.family.metric t).inner
        (Phi.map k (alpha s))
        (lVelocity (I := I) (fun r ↦ Phi.map k (alpha r)) s)
        (lVelocity (I := I) (fun r ↦ Phi.map k (alpha r)) s) := by
  let : TopologicalSpace P.M := P.topology
  let : ChartedSpace H P.M := P.charted
  let : T2Space P.M := P.t2
  let : IsManifold I ∞ P.M := P.smooth
  let : IsManifold I ((∞ : WithTop ℕ∞) + 1) P.M := by
    change IsManifold I ∞ P.M
    infer_instance
  let : SigmaCompactSpace P.M := P.sigmaCompact
  let : TopologicalSpace (SourceDomain (I := I) Phi k) :=
    sourceDomTop (I := I) Phi k
  let : ChartedSpace H (SourceDomain (I := I) Phi k) :=
    sourceDomCharted (I := I) Phi k
  let : T2Space (SourceDomain (I := I) Phi k) := sourceDomT2 (I := I) Phi k
  let : IsManifold I ∞ (SourceDomain (I := I) Phi k) :=
    sourceDomSmooth (I := I) Phi k
  let : SigmaCompactSpace (SourceDomain (I := I) Phi k) :=
    sourceDomSigmaOf (I := I) Phi k (hsrc k)
  let : TopologicalSpace (X.term (subseq k)).M :=
    (X.term (subseq k)).topology
  let : ChartedSpace H (X.term (subseq k)).M :=
    (X.term (subseq k)).charted
  let : T2Space (X.term (subseq k)).M := (X.term (subseq k)).t2
  let : IsManifold I ∞ (X.term (subseq k)).M :=
    (X.term (subseq k)).smooth
  let : IsManifold I ((∞ : WithTop ℕ∞) + 1) (X.term (subseq k)).M := by
    change IsManifold I ∞ (X.term (subseq k)).M
    infer_instance
  let : SigmaCompactSpace (X.term (subseq k)).M :=
    (X.term (subseq k)).sigmaCompact
  let D : SourceDomainMetricData (I := I) Phi k :=
    SourceDomainMetricData.ofRestrictPullback (I := I) (hsrc k)
      (fun _ ↦ sourceMetricRestriction (I := I) Phi P.metric k) (fun _ ↦ P.metric)
  have hmetric :
      sourceMetric (I := I) Phi hsrc htgt k t = D.pullbackMetric t := by
    simpa only [sourceMetric] using
      sourceFlow_metric_eq (I := I) Phi k (hsrc k) (htgt k)
        (fun _ ↦ sourceMetricRestriction (I := I) Phi P.metric k) (fun _ ↦ P.metric) t
  have hmap : MDifferentiableAt I I (fun x : P.M ↦ Phi.map k x) (alpha s) := by
    exact ((Phi.partialDiffeomorph k).contMDiffOn_toFun.contMDiffAt
      ((Phi.partialDiffeomorph k).open_source.mem_nhds hs)).mdifferentiableAt (by simp)
  have hinc : MDifferentiableAt I I
      (fun y : SourceDomain (I := I) Phi k ↦ (y : P.M)) ⟨alpha s, hs⟩ := by
    exact (contMDiff_subtype_val (I := I) (n := (∞ : WithTop ℕ∞))
      (U := sourceOpen (I := I) Phi k)).contMDiffAt.mdifferentiableAt (by simp)
  have hsub :
      mfderiv I I
          (fun y : SourceDomain (I := I) Phi k ↦ Phi.map k (y : P.M))
          ⟨alpha s, hs⟩ (lVelocity (I := I) alpha s) =
        mfderiv I I (fun x : P.M ↦ Phi.map k x) (alpha s)
          (lVelocity (I := I) alpha s) := by
    have hchain := mfderiv_comp_apply (I := I) (I' := I) (I'' := I)
      (x := ⟨alpha s, hs⟩)
      (f := fun y : SourceDomain (I := I) Phi k ↦ (y : P.M))
      (g := fun x : P.M ↦ Phi.map k x) hmap hinc
      (lVelocity (I := I) alpha s)
    have hval :
        mfderiv I I (fun y : SourceDomain (I := I) Phi k ↦ (y : P.M))
            ⟨alpha s, hs⟩ (lVelocity (I := I) alpha s) =
          lVelocity (I := I) alpha s := by
      simpa only using
        mfderiv_subtype_val_apply (I := I) (sourceOpen (I := I) Phi k)
          ⟨alpha s, hs⟩ (lVelocity (I := I) alpha s)
    rw [hval] at hchain
    with_unfolding_all simpa only [Function.comp_def] using hchain
  have hvel :
      lVelocity (I := I) (fun r ↦ Phi.map k (alpha r)) s =
        mfderiv I I (fun x : P.M ↦ Phi.map k x) (alpha s)
          (lVelocity (I := I) alpha s) := by
    with_unfolding_all simpa only [lVelocity, Function.comp_def] using
      (mfderiv_comp_apply (I := 𝓘(Real, Real)) (I' := I) (I'' := I)
        (x := s) (f := alpha) (g := fun x : P.M ↦ Phi.map k x)
        hmap halpha (1 : Real))
  have hpull := D.pullback_inner t ⟨alpha s, hs⟩
    (lVelocity (I := I) alpha s) (lVelocity (I := I) alpha s)
  rw [hmetric]
  calc
    _ = ((X.term (subseq k)).S.family.metric t).inner
          (Phi.map k (↑(⟨alpha s, hs⟩ : SourceDomain (I := I) Phi k) : P.M))
          (mfderiv I I
            (fun y : SourceDomain (I := I) Phi k ↦ Phi.map k (y : P.M))
            ⟨alpha s, hs⟩ (lVelocity (I := I) alpha s))
          (mfderiv I I
            (fun y : SourceDomain (I := I) Phi k ↦ Phi.map k (y : P.M))
            ⟨alpha s, hs⟩ (lVelocity (I := I) alpha s)) := hpull
    _ = _ := by rw [hsub, hvel]

end DifferentialGeometry.CheegerGromovCompactness
