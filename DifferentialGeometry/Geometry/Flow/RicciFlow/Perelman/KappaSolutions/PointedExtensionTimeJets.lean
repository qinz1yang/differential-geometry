import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.PointedPullbackExtensions
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.BumpMetricTimeJets
import DifferentialGeometry.Geometry.Metric.Construction.BumpTimeJets
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ClosedWindowMetricFields


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter Set
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff _root_.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

private local instance pointedJetTopology
    (P : PointedRiemannianManifold.{u, uE, uH} (I := I)) : TopologicalSpace P.M := P.topology
private local instance pointedJetCharted
    (P : PointedRiemannianManifold.{u, uE, uH} (I := I)) : ChartedSpace H P.M := P.charted
private local instance pointedJetSmooth
    (P : PointedRiemannianManifold.{u, uE, uH} (I := I)) : IsManifold I ∞ P.M := P.smooth
private local instance pointedJetC1
    (P : PointedRiemannianManifold.{u, uE, uH} (I := I)) : IsManifold I 1 P.M :=
  IsManifold.of_le (I := I) (M := P.M) (n := ∞) (by decide)
private local instance pointedJetT2
    (P : PointedRiemannianManifold.{u, uE, uH} (I := I)) : T2Space P.M := P.t2
private local instance pointedJetSigma
    (P : PointedRiemannianManifold.{u, uE, uH} (I := I)) : SigmaCompactSpace P.M := P.sigmaCompact

private local instance pointedJetFlowTopology {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : TopologicalSpace F.M := F.topology
private local instance pointedJetFlowCharted {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : ChartedSpace H F.M := F.charted
private local instance pointedJetFlowSmooth {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : IsManifold I ∞ F.M := F.smooth
private local instance pointedJetFlowSigma {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : SigmaCompactSpace F.M := F.sigmaCompact


theorem exists_pointed_extension_time_jets
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    {P : PointedRiemannianManifold.{u, uE, uH} (I := I)} {phi : ℕ → ℕ}
    (Phi : PointedCGHMaps (I := I) X P phi)
    {b : ℝ} (hcarrier : X.D.carrier = Iic b) (hregular : X.D.regular = Iio b) :
    ∃ G : ℕ → ℝ → SmoothRiemannianMetric I P.M,
    ∃ B : ℕ → ℕ → ℝ → Tensor0SField (I := I) (M := P.M) (n := ∞) 2,
      (∀ i t, B i 0 t = metricTensorField (G i t)) ∧
      (∀ i q t, t ≤ b → ∀ x : P.M,
        HasDerivWithinAt (fun s => B i q s x) (B i (q + 1) t x) (Iic b) t) ∧
      ∀ K : Set P.M, IsCompact K → ∀ᶠ i in atTop,
        ∃ U : Set P.M, IsOpen U ∧ K ⊆ U ∧ U ⊆ Phi.source i ∧
          ∀ t : ℝ, ∀ x ∈ U, ∀ v w : TangentSpace I x,
            (G i t).inner x v w =
              ((X.term (phi i)).S.base.metric t).inner (Phi.map i x)
                (mfderiv I I (Phi.map i) x v) (mfderiv I I (Phi.map i) x w) := by
  classical
  have hsrc : SourceIsSigmaCompact Phi := fun i =>
    DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen I (Phi.source_open i)
  have htgt : TargetIsSigmaCompact Phi := fun i =>
    DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen I (Phi.target_open i)
  obtain ⟨bf⟩ := nonempty_bumpFamily Phi
  let G : ℕ → ℝ → SmoothRiemannianMetric I P.M := gSeqExt Phi P.metric bf hsrc htgt
  have hBi (i : ℕ) :
      ∃ B : ℕ → ℝ → Tensor0SField (I := I) (M := P.M) (n := ∞) 2,
        (∀ t, B 0 t = metricTensorField (G i t)) ∧
        ∀ q t, t ≤ b → ∀ x : P.M,
          HasDerivWithinAt (fun s => B q s x) (B (q + 1) t x) (Iic b) t := by
    let : TopologicalSpace (SourceDomain Phi i) := sourceDomTop Phi i
    let : ChartedSpace H (SourceDomain Phi i) := sourceDomCharted Phi i
    let : IsManifold I ∞ (SourceDomain Phi i) := sourceDomSmooth Phi i
    let : T2Space (SourceDomain Phi i) := sourceDomT2 Phi i
    let : SigmaCompactSpace (SourceDomain Phi i) := sourceDomSigmaOf Phi i (hsrc i)
    exact exists_bump_metric_time_jets P.metric (sourceOpen Phi i)
      (sourceFlow Phi i (hsrc i) (htgt i))
      (isSolutionOn_sourceFlow Phi i (hsrc i) (htgt i)) hcarrier hregular
      (bf.chi i) (bf.chi_smooth i) (bf.chi01 i) (bf.chi_support i)
  choose B hBzero hBderiv using hBi
  refine ⟨G, B, hBzero, hBderiv, ?_⟩
  intro K hK
  obtain ⟨N, hN⟩ := bf.grow_cover K hK
  filter_upwards [Filter.eventually_ge_atTop N] with i hi
  obtain ⟨W, hW, hgrow, hchi⟩ := bf.chi_one i
  refine ⟨W ∩ Phi.source i, hW.inter (Phi.source_open i),
    fun x hx => ⟨hgrow (hN i hi hx), bf.grow_subset i (hN i hi hx)⟩,
    inter_subset_right, ?_⟩
  intro t x hx v w
  have heq := gSeqExt_inner_of_mem Phi P.metric bf hsrc htgt i t x hx.2 v w
  rw [hchi x hx.1, one_smul, sub_self, zero_smul, add_zero] at heq
  exact heq.trans (pointed_srcMetric_inner_eq_pullback Phi hsrc htgt i t x hx.2 v w)

theorem exists_pointed_extension_time_jets_on_closed_window
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    {P : PointedRiemannianManifold.{u, uE, uH} (I := I)} {phi : ℕ → ℕ}
    (Phi : PointedCGHMaps (I := I) X P phi)
    (R : SmoothRiemannianMetric I P.M)
    (bf : BumpFamily Phi) (hsrc : SourceIsSigmaCompact Phi) (htgt : TargetIsSigmaCompact Phi)
    {a c b : ℝ} (hac : a < c) (hcb : c < b)
    (hslab : Icc a b ⊆ X.D.carrier) (hreg : Ioo a b ⊆ X.D.regular) :
    ∃ B : ℕ → ℕ → ℝ → Tensor0SField (I := I) (M := P.M) (n := ∞) 2,
      (∀ i t, B i 0 t = metricTensorField (gSeqExt Phi R bf hsrc htgt i t)) ∧
      ∀ i q t, t ∈ Icc c b → ∀ x : P.M,
        HasDerivWithinAt (fun s => B i q s x) (B i (q + 1) t x) (Icc c b) t := by
  classical
  have hBi (i : ℕ) :
      ∃ B : ℕ → ℝ → Tensor0SField (I := I) (M := P.M) (n := ∞) 2,
        (∀ t, B 0 t = metricTensorField (gSeqExt Phi R bf hsrc htgt i t)) ∧
        ∀ q t, t ∈ Icc c b → ∀ x : P.M,
          HasDerivWithinAt (fun s => B q s x) (B (q + 1) t x) (Icc c b) t := by
    let : TopologicalSpace (SourceDomain Phi i) := sourceDomTop Phi i
    let : ChartedSpace H (SourceDomain Phi i) := sourceDomCharted Phi i
    let : IsManifold I ∞ (SourceDomain Phi i) := sourceDomSmooth Phi i
    let : T2Space (SourceDomain Phi i) := sourceDomT2 Phi i
    let : SigmaCompactSpace (SourceDomain Phi i) := sourceDomSigmaOf Phi i (hsrc i)
    obtain ⟨A, hA0, hA⟩ :=
      CanonicalNeighborhood.FiniteHorn.exists_closedWindow_metric_time_fields
        (sourceFlow Phi i (hsrc i) (htgt i)) (isSolutionOn_sourceFlow Phi i (hsrc i) (htgt i))
        hac hcb hslab hreg
    exact exists_bump_metric_time_jets_of_tower R (sourceOpen Phi i)
      (sourceMetric Phi hsrc htgt i) A hA0 (Icc c b) (fun q t ht x => (hA q t ht x).2)
      (bf.chi i) (bf.chi_smooth i) (bf.chi01 i) (bf.chi_support i)
  choose B hB0 hB using hBi
  exact ⟨B, hB0, hB⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
