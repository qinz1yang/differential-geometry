import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.AncientExtensionReduction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.AncientExtensionLimitInputs
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FlowConvergenceAssembly
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalLimitFrontierInputs
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.GoodPointNeckArmReduction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.FiniteArcAncientLimit
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Bounds.InjectivityRadius

set_option autoImplicit false
noncomputable section
open scoped Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped _root_.DifferentialGeometry.Manifold ContDiff ENNReal

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

theorem iUnion_windowInterval_carrier_eq_ancientTimeInterval :
    (⋃ n : ℕ, (KappaSolutions.windowInterval n).carrier) = ancientTimeInterval.carrier := by
  rw [KappaSolutions.iUnion_windowInterval_carrier, ancientTimeInterval_carrier]

def HalfLineExtensionEstimate {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    {X : NormalizedSequence.{u} eps kappa sigma Phi} {L : TerminalLimit X}
    {J : RealTimeInterval} (B : BackwardExtension L J)
    (g : ℝ → SmoothRiemannianMetric I3 L.space.M) : Prop :=
  g 0 = L.space.metric ∧
    (∀ s ∈ J.carrier, g s = B.solution.base.metric s) ∧
    ∃ diagonal : ℕ → ℕ, ∃ _ : StrictMono diagonal,
      ∀ K : Set L.space.M, IsCompact K → ∀ a b : ℝ, a ≤ b → b ≤ 0 →
        ∀ order : ℕ, ∀ eps' : ℝ, 0 < eps' → ∀ᶠ i in Filter.atTop,
          Nonempty (MetricComparisonOn (fun s => g s)
            (fun s => (X.term (L.subseq (B.subseq (diagonal i)))).S.base.metric s)
            (L.maps.partialDiffeomorph (B.subseq (diagonal i)))
            K (Set.Icc a b) order eps')

theorem isHalfLineExtension_of_estimate {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    {X : NormalizedSequence.{u} eps kappa sigma Phi} {L : TerminalLimit X}
    {J : RealTimeInterval} {B : BackwardExtension L J}
    {g : ℝ → SmoothRiemannianMetric I3 L.space.M}
    (h : HalfLineExtensionEstimate B g) : IsHalfLineExtension B g := by
  obtain ⟨hg0, hagree, diagonal, hdiag, hcomp⟩ := h
  exact isHalfLineExtension_of_eventually_metricComparisonOn B hdiag hg0 hagree hcomp

theorem estimate_of_isHalfLineExtension {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    {X : NormalizedSequence.{u} eps kappa sigma Phi} {L : TerminalLimit X}
    {J : RealTimeInterval} {B : BackwardExtension L J}
    {g : ℝ → SmoothRiemannianMetric I3 L.space.M}
    (h : IsHalfLineExtension B g) : HalfLineExtensionEstimate B g := by
  obtain ⟨hg0, hagree, diagonal, hdiag, hconv⟩ := h
  refine ⟨hg0, hagree, diagonal, hdiag, fun K hK a b hab hb order eps' heps' => ?_⟩
  filter_upwards [hconv K hK a b hab (by
    rw [ancientTimeInterval_carrier]
    exact fun t ht => Set.mem_Iic.mpr (ht.2.trans hb)) order eps' heps'] with i hi
  exact hi.2.2

def HalfLineAncientLimitFrontierEstimate {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    {X : NormalizedSequence.{u} eps kappa sigma Phi} {L : TerminalLimit X}
    {J : RealTimeInterval} (B : BackwardExtension L J) : Prop :=
  ∃ g : ℝ → SmoothRiemannianMetric I3 L.space.M, HalfLineExtensionEstimate B g ∧
    ∃ hsol : IsSolutionOn ({ base := { metric := g } } :
        SolutionOn (I := I3) (M := L.space.M) ancientTimeInterval),
      IsAncientKappaSolution (I := I3) kappa (flowOfMetric ancientTimeInterval L.space g hsol)

theorem halfLineAncientLimitFrontier_iff_estimate {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    {X : NormalizedSequence.{u} eps kappa sigma Phi} {L : TerminalLimit X}
    {J : RealTimeInterval} (B : BackwardExtension L J) :
    HalfLineAncientLimitFrontier B ↔ HalfLineAncientLimitFrontierEstimate B := by
  constructor
  · rintro ⟨g, hlim, hrest⟩
    exact ⟨g, estimate_of_isHalfLineExtension hlim, hrest⟩
  · rintro ⟨g, hest, hrest⟩
    exact ⟨g, isHalfLineExtension_of_estimate hest, hrest⟩

def HalfLineAncientExtensionFrontierEstimate (kappa sigma : ℝ) (Phi : ℝ → ℝ) : Prop :=
  ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
    ∀ (X : NormalizedSequence.{u} eps kappa sigma Phi) (L : TerminalLimit X)
      (delta : ℝ) (hd : 0 < delta)
      (B : BackwardExtension L (RealTimeInterval.closed (-delta) 0 (by linarith))),
      HalfLineAncientLimitFrontierEstimate B

theorem halfLineAncientExtensionFrontier_iff_estimate {kappa sigma : ℝ} {Phi : ℝ → ℝ} :
    HalfLineAncientExtensionFrontier.{u} kappa sigma Phi ↔
      HalfLineAncientExtensionFrontierEstimate.{u} kappa sigma Phi := by
  constructor
  · rintro ⟨e, he, hmain⟩
    exact ⟨e, he, fun eps heps hle X L delta hd B =>
      (halfLineAncientLimitFrontier_iff_estimate B).mp (hmain eps heps hle X L delta hd B)⟩
  · rintro ⟨e, he, hmain⟩
    exact ⟨e, he, fun eps heps hle X L delta hd B =>
      (halfLineAncientLimitFrontier_iff_estimate B).mpr (hmain eps heps hle X L delta hd B)⟩

def TerminalLimitFrontier (kappa sigma : ℝ) (Phi : ℝ → ℝ) : Prop :=
  TerminalLimitCompactnessFrontier.{u} kappa sigma Phi ∧
    TerminalLimitScalarBoundFrontier.{u} kappa sigma Phi

theorem terminal_limit_global_bound_of_terminalLimitFrontier {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (hPhi : AdmissiblePinchingFunction Phi) (h : TerminalLimitFrontier.{u} kappa sigma Phi) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
        BoundedAtDistance X → TerminalDerivativeBounds X → Nonempty (TerminalLimit X) :=
  terminal_limit_global_bound_of_frontiers hPhi h.1 h.2

theorem terminalLimitCompactnessFrontier_of_terminal_compactnessInput {kappa sigma : ℝ}
    {Phi : ℝ → ℝ} (h : TerminalCompactnessInput.{u} kappa sigma Phi) :
    TerminalLimitCompactnessFrontier.{u} kappa sigma Phi := by
  obtain ⟨e, he, hmain⟩ := h
  refine ⟨e, he, fun eps heps hle X hb hd => ?_⟩
  obtain ⟨P, hcanon, hconn, hcap, hpre, hcd, hnested, hor, _hsb, hnc⟩ :=
    hmain eps heps hle X hb hd
  exact ⟨P, hcanon, hconn, hcap, hpre, hcd, hnested, hor, hnc⟩

theorem terminal_compactnessInput_of_terminalLimitFrontier {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (h : TerminalLimitFrontier.{u} kappa sigma Phi) :
    TerminalCompactnessInput.{u} kappa sigma Phi := by
  obtain ⟨hcomp, hscalar⟩ := h
  obtain ⟨e₁, he₁, hmain⟩ := hcomp
  obtain ⟨e₂, he₂, hscalar'⟩ := hscalar
  refine ⟨min e₁ e₂, lt_min he₁ he₂, fun eps heps hle X hb hd => ?_⟩
  obtain ⟨P, hcanon, hconn, hcap, hpre, hcd, hnested, hor, hnc⟩ :=
    hmain eps heps (hle.trans (min_le_left e₁ e₂)) X hb hd
  obtain ⟨C, hC⟩ := hscalar' eps heps (hle.trans (min_le_right e₁ e₂)) X hb hd P hcanon hconn
    hcap hpre hcd hnested hor hnc
  exact ⟨P, hcanon, hconn, hcap, hpre, hcd, hnested, hor, ⟨C, hC⟩, hnc⟩

theorem terminal_compactnessInput_iff_terminalLimit_nonempty {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (hkappa : 0 < kappa) (hsigma : 0 < sigma) (hPhi : AdmissiblePinchingFunction Phi) :
    TerminalCompactnessInput.{u} kappa sigma Phi ↔
      (∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
        ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
          BoundedAtDistance X → TerminalDerivativeBounds X → Nonempty (TerminalLimit X)) :=
  terminal_compactnessInput_iff_exists_terminalLimit hkappa hsigma hPhi

def TerminalLimitSourceData (kappa sigma : ℝ) (Phi : ℝ → ℝ) : Prop :=
  ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
    ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
      BoundedAtDistance X → TerminalDerivativeBounds X →
        SeqMetricComplete (I := I3) (X.toFlowSequence.atTime 0) ∧
          Nonempty (BaseInjBound (I := I3) (X.toFlowSequence.atTime 0))

def TerminalLimitSourceCompactness (kappa sigma : ℝ) (Phi : ℝ → ℝ) : Prop :=
  ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
    ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
      BoundedAtDistance X → TerminalDerivativeBounds X →
        SeqMetricComplete (I := I3) (X.toFlowSequence.atTime 0) →
          Nonempty (BaseInjBound (I := I3) (X.toFlowSequence.atTime 0)) →
            ∃ P : MetricCompactLimit.{u, 0, 0} (I := I3) (X.toFlowSequence.atTime 0),
              (∀ k, P.convergence.metrics.domain k =
                CanonicalMetricCompactness.canonicalSourceData P.maps k) ∧
              ConnectedSpace P.limit.M ∧ MetricSourceCapture P.maps ∧
              (∀ i, IsCompact (closure (P.maps.partialDiffeomorph i).source)) ∧
              (∀ i, IsConnected (P.maps.partialDiffeomorph i).source) ∧
              (∀ i, closure (P.maps.partialDiffeomorph i).source ⊆
                (P.maps.partialDiffeomorph (i + 1)).source) ∧
              (∃ o : TangentOrientationSection P.limit.M,
                ∀ i y, y ∈ (P.maps.partialDiffeomorph i).source →
                  ∃ hf : Function.Bijective (mfderiv I3 I3 (P.maps.partialDiffeomorph i) y),
                    PreservesTangentOrientationAt o (X.orientation (P.subseq i))
                      (P.maps.partialDiffeomorph i) y hf) ∧
              (∃ kappa' : ℝ, 0 < kappa' ∧ MetricNoncollapsed P.limit kappa' (Set.Ioc 0 1))

theorem terminalLimitCompactnessFrontier_of_sourceCompactness {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (hprod : TerminalLimitSourceCompactness.{u} kappa sigma Phi)
    (hsrc : TerminalLimitSourceData.{u} kappa sigma Phi) :
    TerminalLimitCompactnessFrontier.{u} kappa sigma Phi := by
  obtain ⟨e₁, he₁, hmain⟩ := hprod
  obtain ⟨e₂, he₂, hdata⟩ := hsrc
  refine ⟨min e₁ e₂, lt_min he₁ he₂, fun eps heps hle X hb hd => ?_⟩
  obtain ⟨hcomplete, hinj⟩ := hdata eps heps (hle.trans (min_le_right e₁ e₂)) X hb hd
  exact hmain eps heps (hle.trans (min_le_left e₁ e₂)) X hb hd hcomplete hinj

theorem terminal_limit_global_bound_of_sourceFrontier {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (hPhi : AdmissiblePinchingFunction Phi)
    (hprod : TerminalLimitSourceCompactness.{u} kappa sigma Phi)
    (hsrc : TerminalLimitSourceData.{u} kappa sigma Phi)
    (hscalar : TerminalLimitScalarBoundFrontier.{u} kappa sigma Phi) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
        BoundedAtDistance X → TerminalDerivativeBounds X → Nonempty (TerminalLimit X) :=
  terminal_limit_global_bound_of_frontiers hPhi
    (terminalLimitCompactnessFrontier_of_sourceCompactness hprod hsrc) hscalar

def GoodPointBufferedCanonicalFrontier (kappa alpha theta : ℝ) : Prop :=
  ∃ epsStar C Lmin Lmax : ℝ, 1 ≤ C ∧ 0 < epsStar ∧ epsStar < alpha ∧
    0 < Lmin ∧ Lmin < Lmax ∧
    GoodPointNeckArmFrontier.{u} kappa alpha theta (max C C + 1) epsStar Lmin Lmax ∧
    ∀ H : ℝ, 0 < H →
      ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
        [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
        (D : RealTimeInterval) (S : SolutionOn (I := I3) (M := M) D)
        (o : TangentOrientationSection M) (x : M) (t : ℝ),
        OrientedWitness S o epsStar kappa x t →
          ∃ W : CanonicalWitness S epsStar C C x t,
            ∀ cap : LocalCap S epsStar x t W.domain.carrier,
              (∃ hdepth : ∀ y ∈ cap.tube,
                  10000 / Real.sqrt (S.scalar t x) ≤ metricDistance (S.base.metric t) x y,
                W.alternative = CanonicalAlternative.cap cap hdepth) →
              ∃ (v : M) (neck : StrongNeck S alpha v t),
                v ∈ cap.tube ∧
                (max C C + 1)⁻¹ * S.scalar t x ≤ S.scalar t v ∧
                S.scalar t v ≤ (max C C + 1) * S.scalar t x ∧
                (∀ z ∈ neck.map '' (Set.univ ×ˢ ({0} : Set ℝ)),
                  H / Real.sqrt (S.scalar t x) ≤ metricDistance (S.base.metric t) x z) ∧
                (∀ y ∈ neck.map '' (Set.univ ×ˢ ({0} : Set ℝ)),
                  ∀ z ∈ neck.map '' (Set.univ ×ˢ ({0} : Set ℝ)),
                    metricDistance (S.base.metric t) y z ≤
                      (max C C + 1) / Real.sqrt (S.scalar t x))

theorem good_point_buffered_canonical_of_frontier {kappa alpha theta : ℝ}
    (h : GoodPointBufferedCanonicalFrontier.{u} kappa alpha theta) :
    ∃ Lmin Lmax : ℝ, 0 < Lmin ∧ Lmin < Lmax ∧ ∀ H : ℝ, 0 < H →
      ∃ epsStar C : ℝ, 0 < epsStar ∧ 1 ≤ C ∧
        ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
          [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
          (D : RealTimeInterval) (S : SolutionOn (I := I3) (M := M) D)
          (o : TangentOrientationSection M) (x : M) (t : ℝ),
          OrientedWitness S o epsStar kappa x t →
          Nonempty (BufferedCanonical S alpha C H x t) ∧
          ∀ a b : MinimizingArm (S.base.metric t) x, ∀ s v : ℝ,
            s ∈ Set.Ioc 0 a.length → v ∈ Set.Ioc 0 b.length →
            Real.sqrt (S.scalar t x) * s ∈ Set.Icc Lmin Lmax →
            Real.sqrt (S.scalar t x) * v ∈ Set.Icc Lmin Lmax →
            theta ≤ Real.arccos ((s ^ 2 + v ^ 2 -
              metricDistance (S.base.metric t) (a.point s) (b.point v) ^ 2) / (2 * s * v)) →
            ∃ (neck : StrongNeck S (2 * alpha) x t)
              (path : TransversePath (a.point a.length) (b.point b.length)
                (neck.map '' (Set.univ ×ˢ ({0} : Set ℝ)))),
              (path.intersection = 1 ∨ path.intersection = -1) ∧
              (∀ w ∈ Set.Icc s a.length,
                a.point w ∉ neck.map '' (Set.univ ×ˢ ({0} : Set ℝ))) ∧
              (∀ w ∈ Set.Icc v b.length,
                b.point w ∉ neck.map '' (Set.univ ×ˢ ({0} : Set ℝ))) ∧
              (∀ y ∈ neck.map '' (Set.univ ×ˢ Set.Icc (-10) 10),
                ∀ z ∈ neck.map '' (Set.univ ×ˢ Set.Icc (-10) 10),
                  metricDistance (S.base.metric t) y z ≤ C / Real.sqrt (S.scalar t x)) := by
  obtain ⟨epsStar, C, Lmin, Lmax, hC, heps, hepsAlpha, hLmin, hLmax, harm, hbody⟩ := h
  refine ⟨Lmin, Lmax, hLmin, hLmax, fun H hH => ⟨epsStar, max C C + 1, heps, ?_, ?_⟩⟩
  · linarith [hC, le_max_left C C]
  · intro M _ _ _ _ _ D S o x t hw
    obtain ⟨W, hcap⟩ := hbody H hH M D S o x t hw
    refine ⟨?_, ?_⟩
    · refine CanonicalWitness.exists_bufferedCanonical W hepsAlpha fun cap hc => ?_
      obtain ⟨v, neck, hv, hlo, hhi, hfar, hdiam⟩ := hcap cap hc
      exact ⟨v, neck, hv, hlo, hhi, hfar, hdiam⟩
    · exact good_point_neck_separation_of_frontier harm M D S o x t hw

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
