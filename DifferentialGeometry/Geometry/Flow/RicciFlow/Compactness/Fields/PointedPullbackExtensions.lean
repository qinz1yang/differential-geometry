import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.MetricExtension


set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter Set
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

private local instance pullbackExtensionTopology
    (P : PointedRiemannianManifold.{u, uE, uH} (I := I)) : TopologicalSpace P.M := P.topology
private local instance pullbackExtensionCharted
    (P : PointedRiemannianManifold.{u, uE, uH} (I := I)) : ChartedSpace H P.M := P.charted
private local instance pullbackExtensionSmooth
    (P : PointedRiemannianManifold.{u, uE, uH} (I := I)) : IsManifold I ∞ P.M := P.smooth
private local instance pullbackExtensionT2
    (P : PointedRiemannianManifold.{u, uE, uH} (I := I)) : T2Space P.M := P.t2
private local instance pullbackExtensionSigma
    (P : PointedRiemannianManifold.{u, uE, uH} (I := I)) : SigmaCompactSpace P.M := P.sigmaCompact

private local instance pullbackExtensionFlowTopology {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : TopologicalSpace F.M := F.topology
private local instance pullbackExtensionFlowCharted {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : ChartedSpace H F.M := F.charted
private local instance pullbackExtensionFlowSmooth {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : IsManifold I ∞ F.M := F.smooth
private local instance pullbackExtensionFlowSigma {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : SigmaCompactSpace F.M := F.sigmaCompact


theorem pointed_srcMetric_inner_eq_pullback
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    {P : PointedRiemannianManifold.{u, uE, uH} (I := I)} {phi : ℕ → ℕ}
    (Phi : PointedCGHMaps (I := I) X P phi)
    (hsrc : SourceIsSigmaCompact Phi) (htgt : TargetIsSigmaCompact Phi)
    (i : ℕ) (t : ℝ) (x : P.M) (hx : x ∈ Phi.source i)
    (v w : TangentSpace I x) :
    (sourceMetric Phi hsrc htgt i t).inner ⟨x, hx⟩ v w =
      ((X.term (phi i)).S.base.metric t).inner (Phi.map i x)
        (mfderiv I I (Phi.map i) x v) (mfderiv I I (Phi.map i) x w) := by
  let : TopologicalSpace (SourceDomain Phi i) := sourceDomTop Phi i
  let : ChartedSpace H (SourceDomain Phi i) := sourceDomCharted Phi i
  let : IsManifold I ∞ (SourceDomain Phi i) := sourceDomSmooth Phi i
  let : T2Space (SourceDomain Phi i) := sourceDomT2 Phi i
  let : SigmaCompactSpace (SourceDomain Phi i) := sourceDomSigmaOf Phi i (hsrc i)
  let d := SourceDomainMetricData.ofRestrictPullback (I := I) (Φ := Phi) (k := i)
    (hsrc i) (fun _ => sourceMetricRestriction Phi P.metric i) (fun _ => P.metric)
  have hmetric : sourceMetric Phi hsrc htgt i t = d.pullbackMetric t :=
    sourceFlow_metric_eq Phi i (hsrc i) (htgt i)
      (fun _ => sourceMetricRestriction Phi P.metric i) (fun _ => P.metric) t
  have hval : MDifferentiableAt I I
      (fun y : SourceDomain Phi i => (y : P.M)) ⟨x, hx⟩ :=
    ((contMDiff_subtype_val (I := I) (U := sourceOpen Phi i)
      (n := ∞)).contMDiffAt).mdifferentiableAt (by simp)
  have hPhi : MDifferentiableAt I I (Phi.map i) x :=
    (Phi.partialDiffeomorph i).mdifferentiableAt (by simp) hx
  have hderiv (z : TangentSpace I x) :
      mfderiv I I (fun y : SourceDomain Phi i => Phi.map i (y : P.M)) ⟨x, hx⟩ z =
        mfderiv I I (Phi.map i) x z := by
    have hcomp := mfderiv_comp_apply (⟨x, hx⟩ : SourceDomain Phi i) hPhi hval z
    have hincl :
        mfderiv I I (fun y : SourceDomain Phi i => (y : P.M)) ⟨x, hx⟩ z = z :=
      mfderiv_subtype_val_apply (I := I) (sourceOpen Phi i) ⟨x, hx⟩ z
    exact hcomp.trans (congrArg (mfderiv I I (Phi.map i) x) hincl)
  rw [hmetric]
  exact (d.pullback_inner t ⟨x, hx⟩ v w).trans
    (congrArg₂ (fun v' w' => ((X.term (phi i)).S.base.metric t).inner
      (Phi.map i x) v' w') (hderiv v) (hderiv w))


theorem exists_pointed_pullback_metric_extensions
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    {P : PointedRiemannianManifold.{u, uE, uH} (I := I)} {phi : ℕ → ℕ}
    (Phi : PointedCGHMaps (I := I) X P phi) :
    ∃ G : ℕ → ℝ → SmoothRiemannianMetric I P.M,
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
  refine ⟨gSeqExt Phi P.metric bf hsrc htgt, ?_⟩
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

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
