import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Limits.HamiltonIvey
import DifferentialGeometry.Geometry.Flow.RicciFlow.Soliton.ClassificationNonnegative

set_option autoImplicit false
noncomputable section
open Bundle Filter
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.Geometry Curvature
open DifferentialGeometry.CheegerGromovCompactness
private instance euclideanThreeFinrankFact :
    Fact (Module.finrank Real (EuclideanSpace Real (Fin 3)) = 2 + 1) := ⟨by simp⟩
private instance euclideanFourFinrankFact :
    Fact (Module.finrank Real (EuclideanSpace Real (Fin 4)) = 3 + 1) := ⟨by simp⟩
variable {E : Type} [NormedAddCommGroup E] [NormedSpace Real E] [FiniteDimensional Real E]
  {H : Type} [TopologicalSpace H] {I : ModelWithCorners Real E H}
  {M : Type} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {H' : Type} [TopologicalSpace H'] {J : ModelWithCorners Real E H'} [J.Boundaryless]
  {N : Type} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
  [T2Space N] [SigmaCompactSpace N] [ConnectedSpace N]

theorem normalizedGradientRicciSoliton_isometry_classification_of_closed_blowup_limit
    [I.Boundaryless] [CompactSpace M]
    {D : RealTimeInterval}
    {T : Real} (hT : 0 < T)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (hS : IsSolutionOn (I := I) S)
    (time scale : Nat → Real)
    (hscalePos : ∀ i, 0 < scale i)
    (htimeMem : ∀ i, time i ∈ (RealTimeInterval.closedOpen 0 T hT).carrier)
    (basepoint : Nat → M)
    {L : PointedFlowData.{0, 0, 0} (I := I) D}
    (hconverges : ∀ (a b : Real) (hab : a ≤ b)
      (hcar : Set.Icc a b ⊆ D.carrier) (hreg : Set.Ioo a b ⊆ D.regular),
      ∃ N : Nat,
      ∃ hcarrier : ∀ i,
        Set.Icc a b ⊆
          (parabolicInterval (RealTimeInterval.closedOpen 0 T hT)
            (time (i + N)) (scale (i + N)) (htimeMem (i + N))).carrier,
      ∃ hregular : ∀ i,
        Set.Ioo a b ⊆
          (parabolicInterval (RealTimeInterval.closedOpen 0 T hT)
            (time (i + N)) (scale (i + N)) (htimeMem (i + N))).regular,
      Nonempty (SmoothCGHConverges (I := I)
        (parabolicPointedFlowSeq (D := RealTimeInterval.closed a b hab) S hS
          (fun i => time (i + N)) (fun i => scale (i + N))
          (fun i => hscalePos (i + N)) (fun i => htimeMem (i + N))
          hcarrier hregular (fun i => basepoint (i + N)))
        (L.timeRestrict (RealTimeInterval.closed a b hab) hcar hreg) id))
    (hscale : Tendsto scale atTop atTop)
    (htime : Tendsto time atTop (𝓝 T))
    (hdim : Module.finrank Real E = 3)
    (hzero : 0 ∈ D.carrier)
    (h : SmoothRiemannianMetric J N) (Fpot : C^∞⟮J, N; Real⟯)
    (hsol : normalizedGradientRicciSoliton h Fpot) :
    letI : TopologicalSpace L.M := L.topology
    letI : ChartedSpace H L.M := L.charted
    letI : IsManifold I ∞ L.M := L.smooth
    letI : SigmaCompactSpace L.M := L.sigmaCompact
    letI : T2Space L.M := L.t2
    ∀ (Phi : N ≃ₘ⟮J, I⟯ L.M),
      Diffeomorph.pullbackMetricCross (L.S.family.metric 0) Phi = h →
    let gaussian := ∃ e : N ≃ₘ⟮J, 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))⟯ EuclideanSpace ℝ (Fin 3),
      Diffeomorph.pullbackMetricCross (euclideanMetric (E := EuclideanSpace ℝ (Fin 3))) e = h ∧
      Fpot = gaussianPotential.comp e.toContMDiffMap
    let sphere := ∃ G : Subgroup (Equiv.Perm (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)),
      ∃ (_ : Finite G)
        (_ : IsCancelSMul G (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1))
        (_ : ContinuousConstSMul G (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1))
        (_ : ContMDiffConstSMul (𝓡 3) ∞ G (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)),
      ∃ hmetric : ∀ gamma : G, Diffeomorph.pullbackMetric roundThreeSphereShrinkerMetric
          (MulAction.smulDiffeomorph (n := ∞) (𝓡 3) gamma) = roundThreeSphereShrinkerMetric,
      ∃ e : MulAction.orbitRel.Quotient G
          (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) ≃ₘ⟮𝓡 3, J⟯ N,
        Diffeomorph.pullbackMetricCross h e =
          solitonModelQuotientMetric roundThreeSphereShrinkerMetric hmetric ∧
        (∀ x : N, Fpot x = (3 / 2 : ℝ))
    let cylinder := ∃ cover : (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) → N,
      solitonModelCovering roundThreeCylinderShrinkerMetric roundThreeCylinderShrinkerPotential h Fpot cover ∧
      ((coveringDeckGroup cover = ⊥ ∧
      ∃ e : (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) ≃ₘ⟮
          (𝓡 2).prod 𝓘(Real, Real), J⟯ N,
        (∀ x, e x = cover x) ∧
        Diffeomorph.pullbackMetricCross h e = roundThreeCylinderShrinkerMetric ∧
        ∀ x, Fpot (e x) = 1 + x.2 ^ 2 / 4) ∨
    (coveringDeckGroup cover = cylinderAntipodalGroup ∧
      ∃ e : (RealProjectivePlane × Real) ≃ₘ⟮(𝓡 2).prod 𝓘(Real, Real), J⟯ N,
        (∀ x, e (realProjectivePlaneQuotientMap x.1, x.2) = cover x) ∧
        Diffeomorph.pullbackMetricCross h e =
          (scaleMetric 2 (by norm_num)
            (roundProjectiveMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))).prod
              (euclideanMetric (E := Real)) ∧
        ∀ x, Fpot (e x) = 1 + x.2 ^ 2 / 4) ∨
    (coveringDeckGroup cover = cylinderDiagonalGroup ∧
      ∃ e : PuncturedRealProjectiveThreeSpace ≃ₘ⟮𝓡 3, J⟯ N,
        (∀ x, e (cylinderDiagonalQuotientDiffeomorph
          (cylinderDiagonalQuotientMap x)) = cover x) ∧
        Diffeomorph.pullbackMetricCross h
          (cylinderDiagonalQuotientDiffeomorph.trans e) = cylinderDiagonalQuotientMetric ∧
        ∀ x, Fpot (e (cylinderDiagonalQuotientDiffeomorph x)) =
          cylinderDiagonalQuotientPotential x))
    (gaussian ∧ ¬ sphere ∧ ¬ cylinder) ∨
      (sphere ∧ ¬ gaussian ∧ ¬ cylinder) ∨
      (cylinder ∧ ¬ gaussian ∧ ¬ sphere) := by
  let _ : CompleteSpace E := FiniteDimensional.complete Real E
  let : TopologicalSpace L.M := L.topology
  let : ChartedSpace H L.M := L.charted
  let : IsManifold I ∞ L.M := L.smooth
  let : SigmaCompactSpace L.M := L.sigmaCompact
  let : T2Space L.M := L.t2
  let _ : T2Space (TangentBundle I M) := inferInstance
  dsimp only
  intro Phi hPhi
  have hcone := SmoothCGHConverges.curvatureOperator_nonnegative_of_closed_blowup_limit
    hT S hS time scale hscalePos htimeMem basepoint hconverges hscale htime hdim 0 hzero
  have hpull : ∀ x : N, metricAlgebraicCurvatureTensorAt h x ∈
      algebraicCurvatureOperatorNonnegativeCone (I := J) (M := N) := by
    intro x
    rw [metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff]
    intro n c v w
    rw [← hPhi]
    simp_rw [metricRm04Standard_pullbackCross]
    exact (metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff
      (L.S.family.metric 0) (Phi x)).mp (hcone (Phi x)) n c
      (fun i => mfderiv J I Phi x (v i)) (fun i => mfderiv J I Phi x (w i))
  exact normalizedGradientRicciSoliton_isometry_classification_of_nonnegative hsol hdim hpull

theorem normalizedGradientRicciSoliton_isometry_classification_of_closed_blowup_limit_of_nonflat
    [I.Boundaryless] [CompactSpace M]
    {D : RealTimeInterval}
    {T : Real} (hT : 0 < T)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (hS : IsSolutionOn (I := I) S)
    (time scale : Nat → Real)
    (hscalePos : ∀ i, 0 < scale i)
    (htimeMem : ∀ i, time i ∈ (RealTimeInterval.closedOpen 0 T hT).carrier)
    (basepoint : Nat → M)
    {L : PointedFlowData.{0, 0, 0} (I := I) D}
    (hconverges : ∀ (a b : Real) (hab : a ≤ b)
      (hcar : Set.Icc a b ⊆ D.carrier) (hreg : Set.Ioo a b ⊆ D.regular),
      ∃ N : Nat,
      ∃ hcarrier : ∀ i,
        Set.Icc a b ⊆
          (parabolicInterval (RealTimeInterval.closedOpen 0 T hT)
            (time (i + N)) (scale (i + N)) (htimeMem (i + N))).carrier,
      ∃ hregular : ∀ i,
        Set.Ioo a b ⊆
          (parabolicInterval (RealTimeInterval.closedOpen 0 T hT)
            (time (i + N)) (scale (i + N)) (htimeMem (i + N))).regular,
      Nonempty (SmoothCGHConverges (I := I)
        (parabolicPointedFlowSeq (D := RealTimeInterval.closed a b hab) S hS
          (fun i => time (i + N)) (fun i => scale (i + N))
          (fun i => hscalePos (i + N)) (fun i => htimeMem (i + N))
          hcarrier hregular (fun i => basepoint (i + N)))
        (L.timeRestrict (RealTimeInterval.closed a b hab) hcar hreg) id))
    (hscale : Tendsto scale atTop atTop)
    (htime : Tendsto time atTop (𝓝 T))
    (hdim : Module.finrank Real E = 3)
    (hzero : 0 ∈ D.carrier)
    (h : SmoothRiemannianMetric J N) (Fpot : C^∞⟮J, N; Real⟯)
    (hsol : normalizedGradientRicciSoliton h Fpot)
    (hnonflat : ∃ x : N, metricRm04At h x ≠ 0) :
    letI : TopologicalSpace L.M := L.topology
    letI : ChartedSpace H L.M := L.charted
    letI : IsManifold I ∞ L.M := L.smooth
    letI : SigmaCompactSpace L.M := L.sigmaCompact
    letI : T2Space L.M := L.t2
    ∀ (Phi : N ≃ₘ⟮J, I⟯ L.M),
      Diffeomorph.pullbackMetricCross (L.S.family.metric 0) Phi = h →
    let gaussian := ∃ e : N ≃ₘ⟮J, 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))⟯ EuclideanSpace ℝ (Fin 3),
      Diffeomorph.pullbackMetricCross (euclideanMetric (E := EuclideanSpace ℝ (Fin 3))) e = h ∧
      Fpot = gaussianPotential.comp e.toContMDiffMap
    let sphere := ∃ G : Subgroup (Equiv.Perm (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)),
      ∃ (_ : Finite G)
        (_ : IsCancelSMul G (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1))
        (_ : ContinuousConstSMul G (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1))
        (_ : ContMDiffConstSMul (𝓡 3) ∞ G (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)),
      ∃ hmetric : ∀ gamma : G, Diffeomorph.pullbackMetric roundThreeSphereShrinkerMetric
          (MulAction.smulDiffeomorph (n := ∞) (𝓡 3) gamma) = roundThreeSphereShrinkerMetric,
      ∃ e : MulAction.orbitRel.Quotient G
          (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) ≃ₘ⟮𝓡 3, J⟯ N,
        Diffeomorph.pullbackMetricCross h e =
          solitonModelQuotientMetric roundThreeSphereShrinkerMetric hmetric ∧
        (∀ x : N, Fpot x = (3 / 2 : ℝ))
    let cylinder := ∃ cover : (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) → N,
      solitonModelCovering roundThreeCylinderShrinkerMetric roundThreeCylinderShrinkerPotential h Fpot cover ∧
      ((coveringDeckGroup cover = ⊥ ∧
      ∃ e : (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) ≃ₘ⟮
          (𝓡 2).prod 𝓘(Real, Real), J⟯ N,
        (∀ x, e x = cover x) ∧
        Diffeomorph.pullbackMetricCross h e = roundThreeCylinderShrinkerMetric ∧
        ∀ x, Fpot (e x) = 1 + x.2 ^ 2 / 4) ∨
    (coveringDeckGroup cover = cylinderAntipodalGroup ∧
      ∃ e : (RealProjectivePlane × Real) ≃ₘ⟮(𝓡 2).prod 𝓘(Real, Real), J⟯ N,
        (∀ x, e (realProjectivePlaneQuotientMap x.1, x.2) = cover x) ∧
        Diffeomorph.pullbackMetricCross h e =
          (scaleMetric 2 (by norm_num)
            (roundProjectiveMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))).prod
              (euclideanMetric (E := Real)) ∧
        ∀ x, Fpot (e x) = 1 + x.2 ^ 2 / 4) ∨
    (coveringDeckGroup cover = cylinderDiagonalGroup ∧
      ∃ e : PuncturedRealProjectiveThreeSpace ≃ₘ⟮𝓡 3, J⟯ N,
        (∀ x, e (cylinderDiagonalQuotientDiffeomorph
          (cylinderDiagonalQuotientMap x)) = cover x) ∧
        Diffeomorph.pullbackMetricCross h
          (cylinderDiagonalQuotientDiffeomorph.trans e) = cylinderDiagonalQuotientMetric ∧
        ∀ x, Fpot (e (cylinderDiagonalQuotientDiffeomorph x)) =
          cylinderDiagonalQuotientPotential x))
    ¬ gaussian ∧ ((sphere ∧ ¬ cylinder) ∨ (cylinder ∧ ¬ sphere)) := by
  let _ : CompleteSpace E := FiniteDimensional.complete Real E
  let : TopologicalSpace L.M := L.topology
  let : ChartedSpace H L.M := L.charted
  let : IsManifold I ∞ L.M := L.smooth
  let : SigmaCompactSpace L.M := L.sigmaCompact
  let : T2Space L.M := L.t2
  let _ : T2Space (TangentBundle I M) := inferInstance
  dsimp only
  intro Phi hPhi
  have hcone := SmoothCGHConverges.curvatureOperator_nonnegative_of_closed_blowup_limit
    hT S hS time scale hscalePos htimeMem basepoint hconverges hscale htime hdim 0 hzero
  have hpull : ∀ x : N, metricAlgebraicCurvatureTensorAt h x ∈
      algebraicCurvatureOperatorNonnegativeCone (I := J) (M := N) := by
    intro x
    rw [metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff]
    intro n c v w
    rw [← hPhi]
    simp_rw [metricRm04Standard_pullbackCross]
    exact (metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff
      (L.S.family.metric 0) (Phi x)).mp (hcone (Phi x)) n c
      (fun i => mfderiv J I Phi x (v i)) (fun i => mfderiv J I Phi x (w i))
  exact normalizedGradientRicciSoliton_isometry_classification_of_nonnegative_of_nonflat hsol hdim hpull hnonflat


theorem normalizedGradientRicciSoliton_isometry_classification_of_closed_blowup_limit_of_exists_nonvanishing_top_form
    [I.Boundaryless] [CompactSpace M]
    {D : RealTimeInterval}
    {T : Real} (hT : 0 < T)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (hS : IsSolutionOn (I := I) S)
    (time scale : Nat → Real)
    (hscalePos : ∀ i, 0 < scale i)
    (htimeMem : ∀ i, time i ∈ (RealTimeInterval.closedOpen 0 T hT).carrier)
    (basepoint : Nat → M)
    {L : PointedFlowData.{0, 0, 0} (I := I) D}
    (hconverges : ∀ (a b : Real) (hab : a ≤ b)
      (hcar : Set.Icc a b ⊆ D.carrier) (hreg : Set.Ioo a b ⊆ D.regular),
      ∃ N : Nat,
      ∃ hcarrier : ∀ i,
        Set.Icc a b ⊆
          (parabolicInterval (RealTimeInterval.closedOpen 0 T hT)
            (time (i + N)) (scale (i + N)) (htimeMem (i + N))).carrier,
      ∃ hregular : ∀ i,
        Set.Ioo a b ⊆
          (parabolicInterval (RealTimeInterval.closedOpen 0 T hT)
            (time (i + N)) (scale (i + N)) (htimeMem (i + N))).regular,
      Nonempty (SmoothCGHConverges (I := I)
        (parabolicPointedFlowSeq (D := RealTimeInterval.closed a b hab) S hS
          (fun i => time (i + N)) (fun i => scale (i + N))
          (fun i => hscalePos (i + N)) (fun i => htimeMem (i + N))
          hcarrier hregular (fun i => basepoint (i + N)))
        (L.timeRestrict (RealTimeInterval.closed a b hab) hcar hreg) id))
    (hscale : Tendsto scale atTop atTop)
    (htime : Tendsto time atTop (𝓝 T))
    (hdim : Module.finrank Real E = 3)
    (hzero : 0 ∈ D.carrier)
    (h : SmoothRiemannianMetric J N) (Fpot : C^∞⟮J, N; Real⟯)
    (hsol : normalizedGradientRicciSoliton h Fpot)
    (hΩ : ∃ Ω : DifferentialForm J N 3, ∀ x, Ω x ≠ 0) :
    letI : TopologicalSpace L.M := L.topology
    letI : ChartedSpace H L.M := L.charted
    letI : IsManifold I ∞ L.M := L.smooth
    letI : SigmaCompactSpace L.M := L.sigmaCompact
    letI : T2Space L.M := L.t2
    ∀ (Phi : N ≃ₘ⟮J, I⟯ L.M),
      Diffeomorph.pullbackMetricCross (L.S.family.metric 0) Phi = h →
    let gaussian := ∃ e : N ≃ₘ⟮J, 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))⟯ EuclideanSpace ℝ (Fin 3),
      Diffeomorph.pullbackMetricCross (euclideanMetric (E := EuclideanSpace ℝ (Fin 3))) e = h ∧
      Fpot = gaussianPotential.comp e.toContMDiffMap
    let sphere := ∃ G : Subgroup (Equiv.Perm (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)),
      ∃ (_ : Finite G)
        (_ : IsCancelSMul G (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1))
        (_ : ContinuousConstSMul G (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1))
        (_ : ContMDiffConstSMul (𝓡 3) ∞ G (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)),
      ∃ hmetric : ∀ gamma : G, Diffeomorph.pullbackMetric roundThreeSphereShrinkerMetric
          (MulAction.smulDiffeomorph (n := ∞) (𝓡 3) gamma) = roundThreeSphereShrinkerMetric,
      ∃ e : MulAction.orbitRel.Quotient G
          (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) ≃ₘ⟮𝓡 3, J⟯ N,
        Diffeomorph.pullbackMetricCross h e =
          solitonModelQuotientMetric roundThreeSphereShrinkerMetric hmetric ∧
        (∀ x : N, Fpot x = (3 / 2 : ℝ))
    let cylinder := ∃ cover : (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) → N,
      solitonModelCovering roundThreeCylinderShrinkerMetric roundThreeCylinderShrinkerPotential h Fpot cover ∧
      ((coveringDeckGroup cover = ⊥ ∧
      ∃ e : (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) ≃ₘ⟮
          (𝓡 2).prod 𝓘(Real, Real), J⟯ N,
        (∀ x, e x = cover x) ∧
        Diffeomorph.pullbackMetricCross h e = roundThreeCylinderShrinkerMetric ∧
        ∀ x, Fpot (e x) = 1 + x.2 ^ 2 / 4) ∨
    (coveringDeckGroup cover = cylinderDiagonalGroup ∧
      ∃ e : PuncturedRealProjectiveThreeSpace ≃ₘ⟮𝓡 3, J⟯ N,
        (∀ x, e (cylinderDiagonalQuotientDiffeomorph
          (cylinderDiagonalQuotientMap x)) = cover x) ∧
        Diffeomorph.pullbackMetricCross h
          (cylinderDiagonalQuotientDiffeomorph.trans e) = cylinderDiagonalQuotientMetric ∧
        ∀ x, Fpot (e (cylinderDiagonalQuotientDiffeomorph x)) =
          cylinderDiagonalQuotientPotential x))
    (gaussian ∧ ¬ sphere ∧ ¬ cylinder) ∨
      (sphere ∧ ¬ gaussian ∧ ¬ cylinder) ∨
      (cylinder ∧ ¬ gaussian ∧ ¬ sphere) := by
  let _ : CompleteSpace E := FiniteDimensional.complete Real E
  let : TopologicalSpace L.M := L.topology
  let : ChartedSpace H L.M := L.charted
  let : IsManifold I ∞ L.M := L.smooth
  let : SigmaCompactSpace L.M := L.sigmaCompact
  let : T2Space L.M := L.t2
  let _ : T2Space (TangentBundle I M) := inferInstance
  dsimp only
  intro Phi hPhi
  have hcone := SmoothCGHConverges.curvatureOperator_nonnegative_of_closed_blowup_limit
    hT S hS time scale hscalePos htimeMem basepoint hconverges hscale htime hdim 0 hzero
  have hpull : ∀ x : N, metricAlgebraicCurvatureTensorAt h x ∈
      algebraicCurvatureOperatorNonnegativeCone (I := J) (M := N) := by
    intro x
    rw [metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff]
    intro n c v w
    rw [← hPhi]
    simp_rw [metricRm04Standard_pullbackCross]
    exact (metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff
      (L.S.family.metric 0) (Phi x)).mp (hcone (Phi x)) n c
      (fun i => mfderiv J I Phi x (v i)) (fun i => mfderiv J I Phi x (w i))
  exact normalizedGradientRicciSoliton_isometry_classification_of_nonnegative_of_exists_nonvanishing_top_form hsol hdim hpull hΩ


end DifferentialGeometry.PDE.RicciFlow.Perelman
