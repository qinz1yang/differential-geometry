import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.AncientExtension
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.EntropyBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SelectedCountersequenceAdapter
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WitnessStrictStability
import DifferentialGeometry.Geometry.Curvature.DimensionThree.Reconstruction.RiemannFromRicci

set_option autoImplicit false
noncomputable section
open scoped Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff ENNReal

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
  {D : RealTimeInterval}

def StrictWitness (S : SolutionOn (I := I3) (M := M) D)
    (eps kappa : ℝ) (x : M) (t : ℝ) : Prop :=
  ∃ W : WindowedModelWitness eps kappa S x t,
    ∀ a b : ℕ, a + 2 * b ≤ modelOrder eps →
      ∀ s ∈ Set.Icc (-modelDepth eps) 0,
        ∀ y ∈ riemannianClosedBallOf (I := I3) (W.model.S.base.metric 0)
          W.model.basepoint (modelRadius eps),
          tensor02CovDerivNormWith (I := I3) a (W.comparison.jet b s)
            (W.model.S.base.metric s) (W.model.S.base.metric s) y < eps

theorem oriented_witness_mono (S : SolutionOn (I := I3) (M := M) D)
    (hS : IsSolutionOn S) (o : TangentOrientationSection M)
    {delta eps kappa : ℝ} (hde : delta ≤ eps) (he : eps < 1)
    {x : M} {t : ℝ}
    (hreg : ∀ s ∈ Set.Ioo (-modelDepth delta) 0,
      parabolicTime t (S.scalar t x) s ∈ D.regular)
    (hw : OrientedWitness S o delta kappa x t) :
    OrientedWitness S o eps kappa x t := by
  obtain ⟨W, oN, hO⟩ := hw
  exact ⟨W.mono_of_regular hS hde he hreg, oN, hO⟩

theorem strict_model_witness_open (S : SolutionOn (I := I3) (M := M) D)
    (hS : IsSolutionOn S) {eps kappa : ℝ}
    (U : Set (M × ℝ)) (hU : IsOpen U)
    (hadmissible : ∀ q ∈ U,
      Set.Icc (q.2 - (eps * S.scalar q.2 q.1)⁻¹) q.2 ⊆ D.regular) :
    IsOpen (U ∩ {q : M × ℝ | StrictWitness S eps kappa q.1 q.2}) := by
  have hbase := isOpen_setOf_regular_strict_model_witness (S := S) hS eps kappa
  have heq : U ∩ {q : M × ℝ | StrictWitness S eps kappa q.1 q.2} =
      U ∩ {q : M × ℝ |
        Set.Icc (q.2 - (eps * S.scalar q.2 q.1)⁻¹) q.2 ⊆ D.regular ∧
          ∃ W : WindowedModelWitness eps kappa S q.1 q.2,
            ∀ a b : ℕ, a + 2 * b ≤ modelOrder eps →
              ∀ s ∈ Set.Icc (-modelDepth eps) 0,
                ∀ y ∈ riemannianClosedBallOf (W.model.S.base.metric 0)
                  W.model.basepoint (modelRadius eps),
                  tensor02CovDerivNormWith (I := I3) a (W.comparison.jet b s)
                    (W.model.S.base.metric s) (W.model.S.base.metric s) y < eps} := by
    ext q
    constructor
    · rintro ⟨hq, hW⟩
      exact ⟨hq, hadmissible q hq, hW⟩
    · rintro ⟨hq, _, hW⟩
      exact ⟨hq, hW⟩
  rw [heq]
  exact hU.inter hbase


theorem selected_countersequence_of_radius_failure {eps small kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (heps : 0 < eps) (heps1 : eps < 1) (hsmall : 0 < small) (hs : small ≤ eps)
    (failure : ∀ r : ℝ, 0 < r → r ≤ Real.sqrt eps →
      ¬ ModelRadiusWorksClosed.{u} eps kappa sigma Phi r) :
    Nonempty (SelectedCountersequence.{u} small kappa sigma Phi) := by
  exact selected_countersequence_of_radius_failure' heps heps1 hsmall hs failure

theorem witness_of_ancient_extension {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (heps : 0 < eps) (heps1 : eps < 1)
    (X : NormalizedSequence.{u} eps kappa sigma Phi) (L : TerminalLimit X)
    {J : RealTimeInterval} (B : BackwardExtension L J) (A : AncientExtension B) :
    ∀ᶠ i in Filter.atTop,
      OrientedWitness (X.term (L.subseq (A.extension.subseq i))).S
        (X.orientation (L.subseq (A.extension.subseq i))) eps kappa
        (X.term (L.subseq (A.extension.subseq i))).basepoint 0 := by
  sorry

theorem no_selected_countersequence {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (hkappa : 0 < kappa) (hsigma : 0 < sigma) (hPhi : AdmissiblePinchingFunction Phi) :
    ∃ e : ℝ, 0 < e ∧ ∀ eps : ℝ, 0 < eps → eps < 1 → eps ≤ e →
      ¬ Nonempty (SelectedCountersequence.{u} eps kappa sigma Phi) := by
  obtain ⟨e1, he1, h1⟩ := bounded_curvature_at_distance.{u} hkappa hsigma hPhi
  obtain ⟨e2, he2, h2⟩ := terminal_limit_global_bound.{u} hkappa hsigma hPhi
  obtain ⟨e3, he3, h3⟩ := first_backward_slab.{u} hkappa hsigma hPhi
  obtain ⟨e4, he4, h4⟩ := ancient_extension.{u} hkappa hsigma hPhi
  refine ⟨min (min e1 e2) (min e3 e4), lt_min (lt_min he1 he2) (lt_min he3 he4), ?_⟩
  intro eps hp hp1 he ⟨X⟩
  have hleft := (le_min_iff.mp he).1
  have hright := (le_min_iff.mp he).2
  obtain ⟨hb, hd⟩ := h1 eps hp (le_min_iff.mp hleft).1 X.toNormalizedSequence
  obtain ⟨L⟩ := h2 eps hp (le_min_iff.mp hleft).2 X.toNormalizedSequence hb hd
  obtain ⟨delta, hdelta, ⟨B⟩⟩ := h3 eps hp (le_min_iff.mp hright).1 X.toNormalizedSequence L
  obtain ⟨A⟩ := h4 eps hp (le_min_iff.mp hright).2 X.toNormalizedSequence L delta hdelta B
  obtain ⟨i, hi⟩ := (witness_of_ancient_extension hp hp1 X.toNormalizedSequence L B A).exists
  exact X.bad _ hi

theorem abstract_model_theorem {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (heps : 0 < eps) (heps1 : eps < 1) (hkappa : 0 < kappa) (hsigma : 0 < sigma)
    (hPhi : AdmissiblePinchingFunction Phi) :
    ∃ r : ℝ, 0 < r ∧ r ≤ Real.sqrt eps ∧ ModelRadiusWorksClosed.{u} eps kappa sigma Phi r := by
  classical
  by_contra h
  have failure : ∀ r : ℝ, 0 < r → r ≤ Real.sqrt eps →
      ¬ ModelRadiusWorksClosed.{u} eps kappa sigma Phi r := by
    intro r hr hrs hw
    exact h ⟨r, hr, hrs, hw⟩
  obtain ⟨e, he, hno⟩ := no_selected_countersequence.{u} hkappa hsigma hPhi
  have hsmall : 0 < min eps e := lt_min heps he
  exact hno (min eps e) hsmall ((min_le_left _ _).trans_lt heps1) (min_le_right _ _)
    (selected_countersequence_of_radius_failure heps heps1 hsmall (min_le_left _ _)
      failure)

structure BlowupLimit (S : SolutionOn (I := I3) (M := M) D)
    (o : TangentOrientationSection M) (kappa : ℝ) (x : ℕ → M) (t : ℕ → ℝ) where
  model : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval
  ancient : IsAncientKappaSolution kappa model
  normalized : PointedFlowScalarAtBase model 1
  orientation : TangentOrientationSection model.M
  subseq : ℕ → ℕ
  strictMono : StrictMono subseq
  scale_pos : ∀ i, 0 < S.scalar (t (subseq i)) (x (subseq i))
  map : ℕ → PartialDiffeomorph I3 I3 model.M M ∞
  exhaustion : ExhaustsByOpen (fun i => (map i).source)
  base_mem : ∀ i, model.basepoint ∈ (map i).source
  base_eq : ∀ i, map i model.basepoint = x (subseq i)
  oriented : ∀ i y, y ∈ (map i).source →
    ∃ hf : Function.Bijective (mfderiv I3 I3 (map i) y),
      PreservesTangentOrientationAt orientation o (map i) y hf
  capture : ∀ r : ℝ, 0 < r → ∀ᶠ i in Filter.atTop,
    riemannianBallOf (I := I3)
      (rescaledMetric S (t (subseq i)) (S.scalar (t (subseq i)) (x (subseq i)))
        (scale_pos i) 0) (x (subseq i)) r ⊆ (map i) '' (map i).source
  convergence : ∀ K : Set model.M, IsCompact K → ∀ A : ℝ, 0 < A →
    ∀ order : ℕ, ∀ eta : ℝ, 0 < eta → ∀ᶠ i in Filter.atTop,
      Set.Icc (t (subseq i) - A / S.scalar (t (subseq i)) (x (subseq i))) (t (subseq i)) ⊆
        D.carrier ∧ K ⊆ (map i).source ∧
      Nonempty (MetricComparisonOn (fun s => model.S.base.metric s)
        (rescaledMetric S (t (subseq i)) (S.scalar (t (subseq i)) (x (subseq i))) (scale_pos i))
        (map i) K (Set.Icc (-A) 0) order eta)

theorem maximal_point_singularity_model [CompactSpace M] [ConnectedSpace M]
    [T2Space (TangentBundle I3 M)] {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (hS : IsSolutionOn S) (o : TangentOrientationSection M) :
    ∃ kappa : ℝ, 0 < kappa ∧ ∀ theta : ℝ, 0 < theta →
      ∀ (x : ℕ → M) (t : ℕ → ℝ), (∀ i, t i ∈ Set.Ico theta T) →
        (∀ i s, s ∈ Set.Icc 0 (t i) → ∀ y, S.scalar s y ≤ S.scalar (t i) (x i)) →
        Filter.Tendsto (fun i => S.scalar (t i) (x i)) Filter.atTop Filter.atTop →
        ∃ L : BlowupLimit S o kappa x t, PointedFlowScalarBounded L.model 1 := by
  sorry


theorem closed_flow_models [CompactSpace M] [ConnectedSpace M]
    [T2Space (TangentBundle I3 M)] {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (hS : IsSolutionOn S) (o : TangentOrientationSection M) :
    ∃ kappa : ℝ, 0 < kappa ∧ ∀ eps : ℝ, 0 < eps → eps < 1 →
      ∃ Q0 : ℝ, 0 < Q0 ∧ ∀ x t, t ∈ Set.Ico 0 T → Q0 ≤ S.scalar t x →
        OrientedWitness S o eps kappa x t := by
  sorry

theorem arbitrary_high_curvature_blowup [CompactSpace M] [ConnectedSpace M]
    [T2Space (TangentBundle I3 M)] {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (hS : IsSolutionOn S) (o : TangentOrientationSection M) :
    ∃ kappa : ℝ, 0 < kappa ∧ ∀ (x : ℕ → M) (t : ℕ → ℝ),
      (∀ i, t i ∈ Set.Ico 0 T) →
      Filter.Tendsto (fun i => S.scalar (t i) (x i)) Filter.atTop Filter.atTop →
        Nonempty (BlowupLimit S o kappa x t) := by
  sorry

theorem buffered_canonical_pullback :
    ∃ epsCan : ℝ, 0 < epsCan ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsCan →
      ∃ C1 C2 : ℝ, 1 ≤ C1 ∧ 1 ≤ C2 ∧ ∀ kappa : ℝ, 0 < kappa →
        ∃ delta : ℝ, 0 < delta ∧ delta < 1 ∧
          ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
            [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
            (D : RealTimeInterval) (S : SolutionOn (I := I3) (M := M) D)
            (o : TangentOrientationSection M) (x : M) (t : ℝ),
            OrientedWitness S o delta kappa x t → Nonempty (CanonicalWitness S eps C1 C2 x t) := by
  sorry

theorem smooth_canonical_neighborhood :
    ∃ epsCan : ℝ, 0 < epsCan ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsCan →
      ∃ C1 C2 : ℝ, 1 ≤ C1 ∧ 1 ≤ C2 ∧
        ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
          [IsManifold I3 ∞ M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
          [T2Space (TangentBundle I3 M)] (T : ℝ) (hT : 0 < T)
          (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
          (_hS : IsSolutionOn S) (_o : TangentOrientationSection M),
          ∃ Qcan : ℝ, 0 < Qcan ∧ ∀ x t, t ∈ Set.Ico 0 T → Qcan ≤ S.scalar t x →
            Nonempty (CanonicalWitness S eps C1 C2 x t) := by
  obtain ⟨epsCan, hepsCan, hpb⟩ := buffered_canonical_pullback.{u}
  refine ⟨epsCan, hepsCan, ?_⟩
  intro eps heps hsmall
  obtain ⟨C1, C2, hC1, hC2, htransfer⟩ := hpb eps heps hsmall
  refine ⟨C1, C2, hC1, hC2, ?_⟩
  intro M _ _ _ _ _ _ _ T hT S hS o
  obtain ⟨kappa, hkappa, hm⟩ := closed_flow_models hT S hS o
  obtain ⟨delta, hd, hd1, hdelta⟩ := htransfer kappa hkappa
  obtain ⟨Q, hQ, hmodel⟩ := hm delta hd hd1
  exact ⟨Q, hQ, fun x t ht hR => hdelta M _ S o x t (hmodel x t ht hR)⟩

structure MixedCurvatureJet (S : SolutionOn (I := I3) (M := M) D) where
  value : ∀ a : ℕ, ℕ → ℝ → Tensor0SField (I := I3) (M := M) (n := ∞) (a + 4)
  spatial : ∀ a t, value a 0 t = curvCovDeriv (I := I3) (S.base.metric t) a
  time : ∀ a b t, t ∈ D.carrier → ∀ x (v : Fin (a + 4) → TangentSpace I3 x),
    value a (b + 1) t x v = derivWithin (fun s => value a b s x v) (D.carrier ∩ Set.Iic t) t +
      ∑ j : Fin (a + 4), value a b t x (Function.update v j
        (ricciEndAt (S.base.metric t) (metricRicciAt (S.base.metric t) x) (v j)))


theorem mixed_curvature_jet_exists (S : SolutionOn (I := I3) (M := M) D)
    (hS : IsSolutionOn S) : Nonempty (MixedCurvatureJet S) := by
  sorry

def MixedCurvatureJet.norm {S : SolutionOn (I := I3) (M := M) D}
    (J : MixedCurvatureJet S) (a b : ℕ) (t : ℝ) (x : M) : ℝ :=
  Real.sqrt (normSq0S (I := I3) (S.base.metric t) x (a + 4) (J.value a b t x))

theorem fixed_kappa_compactness {kappa : ℝ} (hkappa : 0 < kappa)
    (X : ℕ → PointedFlowData.{u, 0, 0} I3 ancientTimeInterval)
    (hX : ∀ i, IsAncientKappaSolution kappa (X i))
    (hbase : ∀ i, PointedFlowScalarAtBase (X i) 1) :
    ∃ (L : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval)
      (f : ℕ → ℕ), StrictMono f ∧ IsAncientKappaSolution kappa L ∧
        PointedFlowScalarAtBase L 1 ∧
        ∃ F : PointedRiemannianConvergenceMaps
          (({ interval := fun _ => ancientTimeInterval, term := X } : FlowSequence).atTime 0)
          (L.atTime 0) f, MetricSourceCapture F ∧ ConvergesOn F L.S := by
  sorry

theorem kappa_universal_derivatives (a b : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ kappa : ℝ, 0 < kappa →
      ∀ P : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval,
        IsAncientKappaSolution kappa P → PointedFlowScalarAtBase P 1 →
        ∀ J : MixedCurvatureJet P.S, J.norm a b 0 P.basepoint ≤ C := by
  sorry

theorem high_curvature_derivatives (a b : ℕ) :
    ∃ C eta : ℝ, 0 < C ∧ 0 < eta ∧
      ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
        [IsManifold I3 ∞ M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
        [T2Space (TangentBundle I3 M)] (T : ℝ) (hT : 0 < T)
        (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
        (hS : IsSolutionOn S) (o : TangentOrientationSection M),
        ∃ Q0 : ℝ, 0 < Q0 ∧ ∀ J : MixedCurvatureJet S, ∀ x t,
          t ∈ Set.Ico 0 T → Q0 ≤ S.scalar t x →
          ∀ y ∈ riemannianBallOf (I := I3) (S.base.metric t) x (eta / Real.sqrt (S.scalar t x)),
            0 < S.scalar t y ∧ J.norm a b t y ≤
              C * Real.rpow (S.scalar t y) (1 + (a : ℝ) / 2 + b) := by
  sorry

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
