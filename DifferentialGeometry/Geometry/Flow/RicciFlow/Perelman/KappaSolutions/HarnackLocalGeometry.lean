import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.HarnackPointSelection
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WitnessBallCapture
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Foundations.NoncollapseInjectivity

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood
open scoped Manifold ContDiff _root_.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)

local instance harnackLocalTopology : TopologicalSpace F.M := F.topology
local instance harnackLocalCharted : ChartedSpace H F.M := F.charted
local instance harnackLocalSmooth : IsManifold I ∞ F.M := F.smooth
local instance harnackLocalC1 : IsManifold I 1 F.M :=
  IsManifold.of_le (I := I) (M := F.M) (n := ∞) (by decide)
local instance harnackLocalSigmaCompact : SigmaCompactSpace F.M := F.sigmaCompact
local instance harnackLocalT2 : T2Space F.M := F.t2
local instance harnackLocalTangentT2 : T2Space (TangentBundle I F.M) := F.t2TangentBundle

variable {kappa : ℝ}

namespace KLim

variable {F}

theorem metric_inner_le (hK : KLim kappa F) {s t : ℝ} (hst : s ≤ t) (ht : t ≤ 0)
    (x : F.M) (v : TangentSpace I x) :
    (F.S.base.metric t).inner x v v ≤ (F.S.base.metric s).inner x v v := by
  have hRic : ∀ q ∈ Set.Ioo s t, ∀ y : F.M, ∀ w : TangentSpace I y,
      0 ≤ F.S.ricciAt q y (vec2 w w) := by
    intro q hq y w
    have hqmem : q ∈ D.carrier := by
      simpa only [hK.carrier_eq, Set.mem_Iic] using hq.2.le.trans ht
    change 0 ≤ metricRicciAt (I := I) (M := F.M) (F.S.base.metric q) y (vec2 w w)
    apply metricRicciAt_nonnegative_of_curvatureOperator_nonnegative
      (I := I) (M := F.M)
    apply (metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff
      (I := I) (F.S.base.metric q) y).mpr
    intro n c a b
    simpa only [SolutionFamily.rm04, metricRm04StandardAt_apply, metricRm04_apply] using
      hK.nonnegativeCurvatureOperator q hqmem y n c a b
  have hanti := metric_inner_antitoneOn_of_ricci_nonnegative_interior F.S F.isSolution
    (a := s) (b := t)
    (fun q hq => by simpa only [hK.carrier_eq, Set.mem_Iic] using hq.2.trans ht)
    (fun q hq => by simpa only [hK.regular_eq, Set.mem_Iio] using hq.2.trans_le ht)
    hRic x v
  exact hanti ⟨le_rfl, hst⟩ ⟨hst, le_rfl⟩ hst

theorem edist_le (hK : KLim kappa F) {s t : ℝ} (hst : s ≤ t) (ht : t ≤ 0)
    (x y : F.M) :
    riemannianEDistOf (I := I) (F.S.base.metric t) x y ≤
      riemannianEDistOf (I := I) (F.S.base.metric s) x y :=
  edistOf_mono (F.S.base.metric t) (F.S.base.metric s)
    (hK.metric_inner_le hst ht) x y

end KLim

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem harnackLocal_edist_comm (g : SmoothRiemannianMetric I F.M) (x y : F.M) :
    riemannianEDistOf (I := I) g x y = riemannianEDistOf (I := I) g y x := by
  let _ : RiemannianBundle (fun q : F.M => TangentSpace I q) := ⟨g.toRiemannianMetric⟩
  change Manifold.riemannianEDist I x y = Manifold.riemannianEDist I y x
  exact Manifold.riemannianEDist_comm (I := I) (x := x) (y := y)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem harnackLocal_edist_triangle
    (g : SmoothRiemannianMetric I F.M) (x y z : F.M) :
    riemannianEDistOf (I := I) g x z ≤
      riemannianEDistOf (I := I) g x y + riemannianEDistOf (I := I) g y z := by
  let _ : RiemannianBundle (fun q : F.M => TangentSpace I q) := ⟨g.toRiemannianMetric⟩
  change Manifold.riemannianEDist I x z ≤
    Manifold.riemannianEDist I x y + Manifold.riemannianEDist I y z
  exact Manifold.riemannianEDist_triangle (I := I) (x := x) (y := y) (z := z)


theorem terminalCurvatureNormalizedFlowSeq_edist_zero_le (hK : KLim kappa F)
    (x : ℕ → F.M) (hQ : ∀ i, 0 < F.S.scalar 0 (x i)) (i : ℕ)
    {s : ℝ} (hs : s ≤ 0) (y z : F.M) :
    @riemannianEDistOf E _ _ H _ I F.M F.topology F.charted F.smooth
      (((terminalCurvatureNormalizedFlowSeq F hK x hQ).term i).S.base.metric 0) y z ≤
    @riemannianEDistOf E _ _ H _ I F.M F.topology F.charted F.smooth
      (((terminalCurvatureNormalizedFlowSeq F hK x hQ).term i).S.base.metric s) y z := by
  change @riemannianEDistOf E _ _ H _ I F.M F.topology F.charted F.smooth
    ((curvatureNormalizedSolution F.S 0 (F.S.scalar 0 (x i)) (hQ i) _).base.metric 0) y z ≤
    @riemannianEDistOf E _ _ H _ I F.M F.topology F.charted F.smooth
    ((curvatureNormalizedSolution F.S 0 (F.S.scalar 0 (x i)) (hQ i) _).base.metric s) y z
  rw [curvatureNormalizedSolution_edist, curvatureNormalizedSolution_edist, parabolicTime_zero]
  exact mul_le_mul_right
    (hK.edist_le (parabolicTime_nonpos le_rfl (hQ i) hs) le_rfl y z) _

theorem terminalCurvatureNormalizedFlowSeq_ball_subset (hK : KLim kappa F)
    (x : ℕ → F.M) (hQ : ∀ i, 0 < F.S.scalar 0 (x i)) (i : ℕ)
    {s : ℝ} (hs : s ≤ 0) (p : F.M) (R : ℝ) :
    {z : F.M | @riemannianEDistOf E _ _ H _ I F.M F.topology F.charted F.smooth
      (((terminalCurvatureNormalizedFlowSeq F hK x hQ).term i).S.base.metric s) p z <
        ENNReal.ofReal R} ⊆
    {z : F.M | @riemannianEDistOf E _ _ H _ I F.M F.topology F.charted F.smooth
      (((terminalCurvatureNormalizedFlowSeq F hK x hQ).term i).S.base.metric 0) p z <
        ENNReal.ofReal R} := by
  intro z hz
  exact (terminalCurvatureNormalizedFlowSeq_edist_zero_le F hK x hQ i hs p z).trans_lt hz

theorem terminalCurvatureNormalizedFlowSeq_buffered_ball_subset (hK : KLim kappa F)
    (x : ℕ → F.M) (hQ : ∀ i, 0 < F.S.scalar 0 (x i)) (i : ℕ)
    {a A rho : ℝ} (ha : a ≤ 0) (hA : 0 ≤ A) (hrho : 0 ≤ rho) (y z : F.M)
    (hy : @riemannianEDistOf E _ _ H _ I F.M F.topology F.charted F.smooth
      (((terminalCurvatureNormalizedFlowSeq F hK x hQ).term i).S.base.metric 0)
      (x i) y ≤ ENNReal.ofReal A)
    (hz : @riemannianEDistOf E _ _ H _ I F.M F.topology F.charted F.smooth
      (((terminalCurvatureNormalizedFlowSeq F hK x hQ).term i).S.base.metric a)
      y z ≤ ENNReal.ofReal rho) :
    @riemannianEDistOf E _ _ H _ I F.M F.topology F.charted F.smooth
      (((terminalCurvatureNormalizedFlowSeq F hK x hQ).term i).S.base.metric 0)
      (x i) z ≤ ENNReal.ofReal (A + rho) := by
  have hz0 := (terminalCurvatureNormalizedFlowSeq_edist_zero_le
    F hK x hQ i ha y z).trans hz
  calc
    @riemannianEDistOf E _ _ H _ I F.M F.topology F.charted F.smooth
        (((terminalCurvatureNormalizedFlowSeq F hK x hQ).term i).S.base.metric 0)
        (x i) z ≤
      @riemannianEDistOf E _ _ H _ I F.M F.topology F.charted F.smooth
        (((terminalCurvatureNormalizedFlowSeq F hK x hQ).term i).S.base.metric 0)
        (x i) y + @riemannianEDistOf E _ _ H _ I F.M F.topology F.charted F.smooth
        (((terminalCurvatureNormalizedFlowSeq F hK x hQ).term i).S.base.metric 0) y z :=
      harnackLocal_edist_triangle F _ (x i) y z
    _ ≤ ENNReal.ofReal A + ENNReal.ofReal rho := add_le_add hy hz0
    _ = ENNReal.ofReal (A + rho) := (ENNReal.ofReal_add hA hrho).symm

theorem terminalCurvatureNormalizedFlowSeq_buffered_rmNormSq_bound (hK : KLim kappa F)
    (hdim : Module.finrank ℝ E = 2)
    (x : ℕ → F.M) (hQ : ∀ i, 0 < F.S.scalar 0 (x i)) (i : ℕ) (r : ℝ)
    (hlocal : ∀ z : F.M,
      (riemannianEDistOf (I := I) (F.S.base.metric 0) z (x i)).toReal < r →
        F.S.scalar 0 z ≤ 4 * F.S.scalar 0 (x i))
    {a s A rho : ℝ} (ha : a ≤ 0) (hs : s ≤ 0) (hA : 0 ≤ A) (hrho : 0 ≤ rho)
    (hmargin : A + rho < r * Real.sqrt (F.S.scalar 0 (x i))) (y z : F.M)
    (hy : @riemannianEDistOf E _ _ H _ I F.M F.topology F.charted F.smooth
      (((terminalCurvatureNormalizedFlowSeq F hK x hQ).term i).S.base.metric 0)
      (x i) y ≤ ENNReal.ofReal A)
    (hz : @riemannianEDistOf E _ _ H _ I F.M F.topology F.charted F.smooth
      (((terminalCurvatureNormalizedFlowSeq F hK x hQ).term i).S.base.metric a)
      y z ≤ ENNReal.ofReal rho) :
    ((terminalCurvatureNormalizedFlowSeq F hK x hQ).term i).rmNormSq (I := I) s z ≤ 16 := by
  have hz0 := terminalCurvatureNormalizedFlowSeq_buffered_ball_subset
    F hK x hQ i ha hA hrho y z hy hz
  have hzlt := hz0.trans_lt ((ENNReal.ofReal_lt_ofReal_iff
    (lt_of_le_of_lt (add_nonneg hA hrho) hmargin)).mpr hmargin)
  have hzreal : (@riemannianEDistOf E _ _ H _ I F.M F.topology F.charted F.smooth
      (((terminalCurvatureNormalizedFlowSeq F hK x hQ).term i).S.base.metric 0)
      z (x i)).toReal < r * Real.sqrt (F.S.scalar 0 (x i)) := by
    let g : SmoothRiemannianMetric I F.M :=
      scaleMetric (F.S.scalar 0 (x i)) (hQ i)
        (F.S.base.metric (parabolicTime 0 (F.S.scalar 0 (x i)) 0))
    change (riemannianEDistOf (I := I) g z (x i)).toReal <
      r * Real.sqrt (F.S.scalar 0 (x i))
    change riemannianEDistOf (I := I) g (x i) z <
      ENNReal.ofReal (r * Real.sqrt (F.S.scalar 0 (x i))) at hzlt
    exact (congrArg ENNReal.toReal (harnackLocal_edist_comm F g z (x i))).trans_lt
      (ENNReal.toReal_lt_of_lt_ofReal hzlt)
  exact terminalCurvatureNormalizedFlowSeq_rmNormSq_bound
    F hK hdim x hQ i r hlocal hs z hzreal

theorem terminalCurvatureNormalizedFlowSeq_scalar_unbounded (hK : KLim kappa F)
    (hunbounded : ¬ BddAbove (Set.range (F.S.scalar 0)))
    (x : ℕ → F.M) (hQ : ∀ i, 0 < F.S.scalar 0 (x i)) (i : ℕ) :
    ¬ BddAbove (Set.range
      (((terminalCurvatureNormalizedFlowSeq F hK x hQ).term i).S.scalar 0)) := by
  rintro ⟨C, hC⟩
  apply hunbounded
  refine ⟨F.S.scalar 0 (x i) * C, ?_⟩
  rintro b ⟨z, rfl⟩
  have hz : ((terminalCurvatureNormalizedFlowSeq F hK x hQ).term i).S.scalar 0 z ≤ C :=
    hC (Set.mem_range_self z)
  rw [terminalCurvatureNormalizedFlowSeq_scalar, zero_div] at hz
  have hmul := mul_le_mul_of_nonneg_left hz (hQ i).le
  simpa only [← mul_assoc, mul_inv_cancel₀ (hQ i).ne', one_mul] using hmul

theorem terminalCurvatureNormalizedFlowSeq_not_boundedGeometry (hK : KLim kappa F)
    (hdim : Module.finrank ℝ E = 2)
    (hunbounded : ¬ BddAbove (Set.range (F.S.scalar 0)))
    (x : ℕ → F.M) (hQ : ∀ i, 0 < F.S.scalar 0 (x i)) :
    ¬ Nonempty (SeqBoundedGeometry (I := I)
      ((terminalCurvatureNormalizedFlowSeq F hK x hQ).atZero (I := I))) := by
  rintro ⟨hgeom⟩
  apply terminalCurvatureNormalizedFlowSeq_scalar_unbounded F hK hunbounded x hQ 0
  refine ⟨hgeom.C 0, ?_⟩
  rintro b ⟨z, rfl⟩
  change F.M at z
  have hz := hgeom.bound 0 0 z
  let g : SmoothRiemannianMetric I F.M :=
    scaleMetric (F.S.scalar 0 (x 0)) (hQ 0)
      (F.S.base.metric (parabolicTime 0 (F.S.scalar 0 (x 0)) 0))
  change curvDerivNorm (I := I) 0 g z ≤ hgeom.C 0 at hz
  change Real.sqrt (DifferentialGeometry.Tensor0SBundle.normSq0S (I := I)
    g z 4 (metricRm04 (I := I) g z)) ≤ hgeom.C 0 at hz
  rw [metricRm04_apply, metricRm_normSq_eq_scalar_sq_of_finrank_two
    (I := I) (M := F.M) _ hdim,
    Real.sqrt_sq_eq_abs] at hz
  change metricScalarAt (I := I) g z ≤ hgeom.C 0
  exact (le_abs_self _).trans hz

variable [NeZero (Module.finrank ℝ E)] [I.Boundaryless]

theorem terminalCurvatureNormalizedFlowSeq_closedBall_isCompact (hK : KLim kappa F)
    (x : ℕ → F.M) (hQ : ∀ i, 0 < F.S.scalar 0 (x i)) (i : ℕ)
    {s : ℝ} (hs : s ≤ 0) (p : F.M) (R : ℝ) :
    IsCompact {z : F.M | @riemannianEDistOf E _ _ H _ I F.M F.topology F.charted F.smooth
      (((terminalCurvatureNormalizedFlowSeq F hK x hQ).term i).S.base.metric s) p z ≤
        ENNReal.ofReal R} := by
  let g : SmoothRiemannianMetric I F.M :=
    scaleMetric (F.S.scalar 0 (x i)) (hQ i)
      (F.S.base.metric (parabolicTime 0 (F.S.scalar 0 (x i)) s))
  have hcomplete : RiemannianMetricComplete (I := I) g :=
    ⟨(terminalCurvatureNormalizedFlowSeq_complete F hK x hQ).complete_on i s hs⟩
  exact hcomplete.closedEBall_isCompact p R


def terminalHalfScaleVolData (hK : KLim kappa F)
    (x : ℕ → F.M) (hQ : ∀ i, 0 < F.S.scalar 0 (x i)) :
    FlowNoncollapsingScale (I := I) (terminalCurvatureNormalizedFlowSeq F hK x hQ) where
  zero_mem := by change (0 : ℝ) ≤ 0; exact le_rfl
  kappa := kappa
  kappa_pos := hK.kappa_pos
  radius := 1 / 2
  radius_pos := by norm_num

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem terminalHalfScaleVolData_curvature (hK : KLim kappa F)
    (hdim : Module.finrank ℝ E = 2)
    (x : ℕ → F.M) (hQ : ∀ i, 0 < F.S.scalar 0 (x i)) (i : ℕ) (r : ℝ)
    (hlocal : ∀ z : F.M,
      (riemannianEDistOf (I := I) (F.S.base.metric 0) z (x i)).toReal < r →
        F.S.scalar 0 z ≤ 4 * F.S.scalar 0 (x i))
    (hlarge : 1 / 2 < r * Real.sqrt (F.S.scalar 0 (x i))) :
    (PointedFlowData.baseFlowBall (I := I)
      ((terminalCurvatureNormalizedFlowSeq F hK x hQ).term i)
      (terminalHalfScaleVolData F hK x hQ).zero_mem (1 / 2) (by norm_num)).IsRmControlled := by
  constructor
  · intro s hs
    exact hs.2
  · intro s hs z hz
    change F.M at z
    have hz0 : @riemannianEDistOf E _ _ H _ I F.M F.topology F.charted F.smooth
        (((terminalCurvatureNormalizedFlowSeq F hK x hQ).term i).S.base.metric 0)
        (x i) z < ENNReal.ofReal (1 / 2) :=
      (terminalCurvatureNormalizedFlowSeq_edist_zero_le F hK x hQ i hs.2 (x i) z).trans_lt hz
    have hzreal : (@riemannianEDistOf E _ _ H _ I F.M F.topology F.charted F.smooth
        (((terminalCurvatureNormalizedFlowSeq F hK x hQ).term i).S.base.metric 0)
        z (x i)).toReal < r * Real.sqrt (F.S.scalar 0 (x i)) := by
      let g : SmoothRiemannianMetric I F.M :=
        scaleMetric (F.S.scalar 0 (x i)) (hQ i)
          (F.S.base.metric (parabolicTime 0 (F.S.scalar 0 (x i)) 0))
      change (riemannianEDistOf (I := I) g z (x i)).toReal <
        r * Real.sqrt (F.S.scalar 0 (x i))
      change riemannianEDistOf (I := I) g (x i) z < ENNReal.ofReal (1 / 2) at hz0
      exact (congrArg ENNReal.toReal (harnackLocal_edist_comm F g z (x i))).trans_lt
        ((ENNReal.toReal_lt_of_lt_ofReal hz0).trans hlarge)
    have hRm := terminalCurvatureNormalizedFlowSeq_rmNormSq_bound
      F hK hdim x hQ i r hlocal hs.2 z hzreal
    change (1 / 2 : ℝ) ^ 4 *
      ((terminalCurvatureNormalizedFlowSeq F hK x hQ).term i).rmNormSq (I := I) s z ≤ 1
    nlinarith

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem terminalHalfScaleVolData_bound (hK : KLim kappa F)
    (hdim : Module.finrank ℝ E = 2)
    (x : ℕ → F.M) (r : ℕ → ℝ) (hQ : ∀ i, 0 < F.S.scalar 0 (x i))
    (hlocal : ∀ i z,
      (riemannianEDistOf (I := I) (F.S.base.metric 0) z (x i)).toReal < r i →
        F.S.scalar 0 z ≤ 4 * F.S.scalar 0 (x i))
    (hlarge : ∀ i, 1 / 2 < r i * Real.sqrt (F.S.scalar 0 (x i))) :
    IsFlowNoncollapsingScaleBound (I := I) (terminalHalfScaleVolData F hK x hQ) := by
  constructor
  · intro i
    exact terminalHalfScaleVolData_curvature F hK hdim x hQ i (r i) (hlocal i) (hlarge i)
  · intro i
    apply terminalCurvatureNormalizedFlowSeq_noncollapsed F hK x hQ i
    exact FlowMetricBall.isSpatiallyRmControlled_of_isRmControlled _
      (terminalHalfScaleVolData_curvature F hK hdim x hQ i (r i) (hlocal i) (hlarge i))

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem exists_terminalHalfScaleVolData_bound_tail (hK : KLim kappa F)
    (hdim : Module.finrank ℝ E = 2)
    (x : ℕ → F.M) (r : ℕ → ℝ) (hQ : ∀ i, 0 < F.S.scalar 0 (x i))
    (hlocal : ∀ i z,
      (riemannianEDistOf (I := I) (F.S.base.metric 0) z (x i)).toReal < r i →
        F.S.scalar 0 z ≤ 4 * F.S.scalar 0 (x i))
    (hexpand : Tendsto (fun i => r i * Real.sqrt (F.S.scalar 0 (x i))) atTop atTop) :
    ∃ N : ℕ, IsFlowNoncollapsingScaleBound (I := I)
      (terminalHalfScaleVolData F hK (fun i => x (N + i)) (fun i => hQ (N + i))) := by
  have hevent : ∀ᶠ i in atTop, 1 / 2 < r i * Real.sqrt (F.S.scalar 0 (x i)) :=
    hexpand (eventually_gt_atTop (1 / 2))
  obtain ⟨N, hN⟩ := eventually_atTop.mp hevent
  refine ⟨N, terminalHalfScaleVolData_bound F hK hdim (fun i => x (N + i))
    (fun i => r (N + i)) (fun i => hQ (N + i)) (fun i => hlocal (N + i)) ?_⟩
  intro i
  exact hN (N + i) (Nat.le_add_right N i)

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
