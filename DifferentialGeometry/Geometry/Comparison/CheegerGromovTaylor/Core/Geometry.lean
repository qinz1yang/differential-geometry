import DifferentialGeometry.Geometry.Comparison.CheegerGromovTaylor.Pullback.Metric
import DifferentialGeometry.Geometry.Comparison.CheegerGromovTaylor.Paths.Radial
import DifferentialGeometry.Geometry.Exponential.NormalCoordinates.PullbackDistance
import DifferentialGeometry.Geometry.Comparison.HalfSquaredDistance.Basic
import DifferentialGeometry.Geometry.Comparison.Variation.Jacobi.EndpointPositivity
import DifferentialGeometry.Geometry.Metric.Comparison.DistanceScaling

set_option autoImplicit false

noncomputable section

open Metric Set
open scoped ContDiff Manifold

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace CheegerGromovTaylor

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]

def intrinsicCore (R a : Real) : Set (intrinsicPullBall (E := E) R) :=
  {z | ‖(z : E)‖ ≤ a}

omit [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)] in
@[simp] theorem mem_intrCore
    {R a : Real} {z : intrinsicPullBall (E := E) R} :
    z ∈ intrinsicCore (E := E) R a ↔ ‖(z : E)‖ ≤ a :=
  Iff.rfl

omit [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)] in
theorem intrinsicCore_mono
    {R a b : Real} (hab : a ≤ b) :
    intrinsicCore (E := E) R a ⊆ intrinsicCore (E := E) R b := by
  intro z hz
  exact hz.trans hab

omit [NeZero (Module.finrank Real E)] in
theorem intrinsicCore_compact
    {R a : Real} (haR : a < R) :
    IsCompact (intrinsicCore (E := E) R a) := by
  let : ProperSpace E := FiniteDimensional.proper Real E
  rw [Subtype.isCompact_iff]
  have himage :
      ((fun z : intrinsicPullBall (E := E) R => (z : E)) ''
          intrinsicCore (E := E) R a) =
        Metric.closedBall (0 : E) a := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      change ‖(w : E)‖ ≤ a at hw
      rw [Metric.mem_closedBall, dist_zero_right]
      exact hw
    · intro hz
      have hza : ‖z‖ ≤ a := by
        simpa only [Metric.mem_closedBall, dist_zero_right] using hz
      have hzR : ‖z‖ < R := hza.trans_lt haR
      refine ⟨⟨z, ?_⟩, hza, rfl⟩
      change z ∈ Metric.ball (0 : E) R
      simpa only [Metric.mem_ball, dist_zero_right] using hzR
  rw [himage]
  exact isCompact_closedBall (0 : E) a

def intrinsicZero {R : Real} (hR : 0 < R) : intrinsicPullBall (E := E) R :=
  ⟨0, by
    change (0 : E) ∈ Metric.ball 0 R
    simpa only [Metric.mem_ball, dist_self] using hR⟩

omit [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)] in
theorem intrinsicZero_mem
    {R a : Real} (hR : 0 < R) (ha : 0 ≤ a) :
    intrinsicZero (E := E) hR ∈ intrinsicCore (E := E) R a := by
  simpa only [mem_intrCore, intrinsicZero, norm_zero] using ha

noncomputable def intrinsicRadial
    {R : Real} (z : intrinsicPullBall (E := E) R) (t : Real) :
    intrinsicPullBall (E := E) R := by
  refine ⟨Real.smoothTransition t • (z : E), ?_⟩
  change Real.smoothTransition t • (z : E) ∈ Metric.ball 0 R
  have hzR : ‖(z : E)‖ < R := by
    have hzmem : (z : E) ∈ Metric.ball (0 : E) R := z.property
    simpa only [Metric.mem_ball, dist_zero_right] using hzmem
  have hnonneg : 0 ≤ Real.smoothTransition t :=
    Real.smoothTransition.nonneg t
  have hle : Real.smoothTransition t ≤ 1 :=
    Real.smoothTransition.le_one t
  rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg hnonneg]
  exact (mul_le_of_le_one_left (norm_nonneg _) hle).trans_lt hzR

omit [FiniteDimensional Real E] [NeZero (Module.finrank Real E)] in
@[simp] theorem intrinsicRadial_zero
    {R : Real} (hR : 0 < R) (z : intrinsicPullBall (E := E) R) :
    intrinsicRadial (E := E) z 0 = intrinsicZero (E := E) hR := by
  apply Subtype.ext
  simp only [intrinsicRadial, intrinsicZero,
    Real.smoothTransition.zero_of_nonpos le_rfl, zero_smul]

omit [FiniteDimensional Real E] [NeZero (Module.finrank Real E)] in
@[simp] theorem intrinsicRadial_one
    {R : Real} (z : intrinsicPullBall (E := E) R) :
    intrinsicRadial (E := E) z 1 = z := by
  apply Subtype.ext
  simp only [intrinsicRadial, Real.smoothTransition.one_of_one_le le_rfl,
    one_smul]

omit [FiniteDimensional Real E] [NeZero (Module.finrank Real E)] in
theorem intrinsicRadial_smooth
    {R : Real} (z : intrinsicPullBall (E := E) R) :
    ContMDiff 𝓘(Real, Real) 𝓘(Real, E) ∞
      (intrinsicRadial (E := E) z) := by
  intro t
  have hbase :
      ContMDiffAt 𝓘(Real, Real) 𝓘(Real, E) ∞
        (fun s : Real => Real.smoothTransition s • (z : E)) t := by
    rw [contMDiffAt_iff_contDiffAt]
    exact Real.smoothTransition.contDiff.contDiffAt.smul contDiffAt_const
  have hmem :
      ∀ s : Real,
        Real.smoothTransition s • (z : E) ∈
          intrinsicPullBall (E := E) R :=
    fun s => (intrinsicRadial (E := E) z s).property
  exact codRestr_contMDiffAt (V := intrinsicPullBall (E := E) R) hmem hbase

section PullbackDistance

open Bundle Function Manifold
open Exponential NormalCoordinates Variation
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Geodesic

variable {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
variable [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

noncomputable local instance {R : Real} :
    SigmaCompactSpace (intrinsicPullBall (E := E) R) :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen
      𝓘(Real, E) (intrinsicPullBall (E := E) R).isOpen)

theorem intrinsicRadial_len
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)))
    (p : M) {R : Real}
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    (z : intrinsicPullBall (E := E) R) :
    letI : SigmaCompactSpace (intrinsicPullBall (E := E) R) :=
      isSigmaCompact_iff_sigmaCompactSpace.mp
        (Geometry.isSigmaCompact_of_isOpen
          𝓘(Real, E) (intrinsicPullBall (E := E) R).isOpen)
    letI : RiemannianBundle
        (fun y : intrinsicPullBall (E := E) R ↦
          TangentSpace 𝓘(Real, E) y) :=
      ⟨(intrinsicPullMetric (I := I) g hEnorm p hloc).toRiemannianMetric⟩
    Manifold.pathELength 𝓘(Real, E)
        (intrinsicRadial (E := E) z) 0 1 =
      ENNReal.ofReal ‖(z : E)‖ := by
  let : SigmaCompactSpace (intrinsicPullBall (E := E) R) :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen
        𝓘(Real, E) (intrinsicPullBall (E := E) R).isOpen)
  let : RiemannianBundle
      (fun y : intrinsicPullBall (E := E) R ↦
        TangentSpace 𝓘(Real, E) y) :=
    ⟨(intrinsicPullMetric (I := I) g hEnorm p hloc).toRiemannianMetric⟩
  have hradC1 :
      ContMDiffOn 𝓘(Real, Real) 𝓘(Real, E) 1
        (intrinsicRadial (E := E) z) (Set.Icc 0 1) :=
    ((intrinsicRadial_smooth (E := E) z).of_le (by norm_num)).contMDiffOn
  have hlocal :=
    intrinsicPull_pathLen (I := I) g hEnorm p hloc
      (a := 0) (b := 1) hradC1
  rw [← hlocal]
  let v : TangentSpace I p := normalFrame (I := I) g p (z : E)
  let γ : Real → M :=
    fun t => intrinsicFramedExp (I := I) g hEnorm p (t • (z : E))
  have hγ :
      γ = intrinsicGeodesic (I := I) g hEnorm p v := by
    funext t
    dsimp only [γ, v]
    calc
      intrinsicFramedExp (I := I) g hEnorm p (t • (z : E)) =
          expMapIntrinsic (I := I) g hEnorm p
            (normalFrame (I := I) g p (t • (z : E))) :=
        intrinsicFrame_apply (I := I) g hEnorm p (t • (z : E))
      _ = expMapIntrinsic (I := I) g hEnorm p
            (t • normalFrame (I := I) g p (z : E)) :=
        congrArg (expMapIntrinsic (I := I) g hEnorm p)
          ((normalFrame (I := I) g p).map_smul t (z : E))
      _ = intrinsicGeodesic (I := I) g hEnorm p
            (t • normalFrame (I := I) g p (z : E)) 1 := rfl
      _ = intrinsicGeodesic (I := I) g hEnorm p
            (normalFrame (I := I) g p (z : E)) t :=
        intrinsicGeodesic_smul (I := I) g hEnorm p
          (normalFrame (I := I) g p (z : E)) t
  have hγC1 :
      ContMDiffOn 𝓘(Real, Real) I 1 γ (Set.Icc 0 1) := by
    rw [hγ]
    exact
      (intrinsicGeodesic_contMDiffOn (I := I) g hEnorm p v).mono
        (Set.subset_univ _)
  have hbase :
      Manifold.pathELength I γ 0 1 = ENNReal.ofReal ‖(z : E)‖ := by
    have hv :
        Real.sqrt (g.inner p v v) = ‖(z : E)‖ := by
      dsimp only [v]
      exact normalFrame_sqrt (I := I) g p (z : E)
    rw [Geodesic.pathELength_eq_arcLength_riemannianBundle (I := I) g zero_le_one
      (Geodesic.speedSqrt_integrableOn_Icc_of_C1
        (I := I) g zero_le_one hγC1)
      (fun t _ => hEnorm (γ t)
        (mfderiv 𝓘(Real, Real) I γ t (1 : Real))),
      hγ, arcLength_radial (I := I) g hEnorm p v 0 1, hv]
    norm_num
  change
    Manifold.pathELength I
        (γ ∘ Real.smoothTransition) 0 1 =
      ENNReal.ofReal ‖(z : E)‖
  rw [Manifold.pathELength_comp_of_monotoneOn
    (I := I) (γ := γ) (f := Real.smoothTransition)
    (a := 0) (b := 1) zero_le_one
    (Real.smoothTransition.monotone.monotoneOn (Set.Icc 0 1))
    ((Real.smoothTransition.contDiff (n := 1)).differentiable
      one_ne_zero).differentiableOn
    (by
      simpa only [Real.smoothTransition.zero_of_nonpos le_rfl,
        Real.smoothTransition.one_of_one_le le_rfl] using
          hγC1.mdifferentiableOn one_ne_zero)]
  simpa only [Real.smoothTransition.zero_of_nonpos le_rfl,
    Real.smoothTransition.one_of_one_le le_rfl] using hbase

theorem intrinsicPull_dist_zero
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)))
    (p : M) {R : Real} (hR : 0 < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    (z : intrinsicPullBall (E := E) R) :
    riemannianEDistOf (I := 𝓘(Real, E))
        (intrinsicPullMetric (I := I) g hEnorm p hloc)
        (intrinsicZero (E := E) hR) z =
      ENNReal.ofReal ‖(z : E)‖ := by
  have hagree : framedExpMap (I := I) g p = intrinsicFramedExp (I := I) g hEnorm p := by
    funext w
    rw [framedExpMap_apply, intrinsicFrame_apply, expMap_eq_expMapIntrinsic g hEnorm p]
  have hdom : MapsTo (normalFrame g p) (intrinsicPullBall (E := E) R) (expDomain g p) := by
    intro w _
    rw [expDomain_eq_univ_of_completeSpace g hEnorm p]
    exact mem_univ _
  have hloc' : IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
      (framedExpMap g p) (intrinsicPullBall (E := E) R) := by
    rw [hagree]
    exact hloc
  have h := riemannianEDistOf_pullback_zero g p (intrinsicPullBall (E := E) R)
    ((convex_ball (0 : E) R).starConvex (Metric.mem_ball_self hR)) hloc' hdom z
  have hf : intrinsicExpOn g hEnorm p R =
      fun w : intrinsicPullBall (E := E) R => framedExpMap g p w := by
    funext w
    exact (congrFun hagree (w : E)).symm
  change riemannianEDistOf (localPullMetric g (intrinsicExpOn g hEnorm p R)
    (intrinsicExpOn_local g hEnorm p hloc))
    (intrinsicZero hR) z = _
  simp only [hf]
  exact h

theorem intrinsicPull_pair_pos
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)))
    (p : M) {R K L : Real}
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    (hKL : K * L ^ 2 < (Real.pi / 2) ^ 2)
    (γ : Real → intrinsicPullBall (E := E) R)
    (J : ∀ t : Real, TangentSpace 𝓘(Real, E) (γ t))
    (hRm : ∀ t ∈ Set.Icc (0 : Real) 1,
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
        (intrinsicFramedExp (I := I) g hEnorm p
          ((γ t : intrinsicPullBall (E := E) R) : E)) 4
        (Geometry.Curvature.metricRm04At
          (I := I) (M := M) g
          (intrinsicFramedExp (I := I) g hEnorm p
            ((γ t : intrinsicPullBall (E := E) R) : E)))) ≤ K)
    (hγ : ContMDiff 𝓘(Real, Real) 𝓘(Real, E) ∞ γ)
    (hJdiff : ∀ t, DifferentiableAt Real
      (chartRepAt (I := 𝓘(Real, E)) γ J t) t)
    (hDJdiff : ∀ t, DifferentiableAt Real
      (chartRepAt (I := 𝓘(Real, E)) γ
        (fun s => covDerivAlong (I := 𝓘(Real, E))
          (intrinsicPullMetric (I := I) g hEnorm p hloc) γ J s) t) t)
    (hJacobian : ∀ t ∈ Set.Icc (0 : Real) 1,
      IsJacobiAt (I := 𝓘(Real, E))
        (intrinsicPullMetric (I := I) g hEnorm p hloc) γ J t)
    (hJ0 : J 0 = 0) (hJ1 : J 1 ≠ 0)
    (hspeed : ∀ t ∈ Set.Icc (0 : Real) 1,
      (intrinsicPullMetric (I := I) g hEnorm p hloc).inner (γ t)
          (curveVelocity (I := 𝓘(Real, E)) γ t)
          (curveVelocity (I := 𝓘(Real, E)) γ t) =
        L ^ 2) :
    0 <
      (intrinsicPullMetric (I := I) g hEnorm p hloc).inner (γ 1)
        (covDerivAlong (I := 𝓘(Real, E))
          (intrinsicPullMetric (I := I) g hEnorm p hloc) γ J 1)
        (J 1) := by
  let gPull := intrinsicPullMetric (I := I) g hEnorm p hloc
  apply Variation.jacobi_pair_pos
    (I := 𝓘(Real, E)) gPull γ J zero_le_one isOpen_univ (subset_univ _)
    (hγ.of_le (by decide : (2 : WithTop ℕ∞) ≤ ∞)).contMDiffOn
    (fun t _ => hJdiff t) (fun t _ => hDJdiff t) hJacobian hJ0
    (fun hz => hJ1 (hz 1 (right_mem_Icc.mpr zero_le_one)))
    (by simpa only [sub_zero, one_pow, mul_one] using hKL)
  intro t ht
  have hquad :=
    intrinsicPull_quad_le (I := I) g hEnorm p hloc (γ t)
      (hRm t (Ioo_subset_Icc_self ht))
      (tangentSpaceModelContinuousLinearEquiv (I := 𝓘(Real, E)) (γ t) (J t))
      (tangentSpaceModelContinuousLinearEquiv (I := 𝓘(Real, E)) (γ t)
        (curveVelocity (I := 𝓘(Real, E)) γ t))
  dsimp only at hquad
  simp only [ContinuousLinearEquiv.symm_apply_apply] at hquad
  rw [hspeed t (Ioo_subset_Icc_self ht)] at hquad
  simpa only [mul_assoc, mul_left_comm, mul_comm] using hquad

theorem intrinsicCore_edist_lt
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)))
    (p : M) {R a : Real} (hR : 0 < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    {x q : intrinsicPullBall (E := E) R}
    (hx : ‖(x : E)‖ < a)
    (hq : q ∈ intrinsicCore (E := E) R a) :
    riemannianEDistOf (I := 𝓘(Real, E))
        (intrinsicPullMetric (I := I) g hEnorm p hloc) x q <
      ENNReal.ofReal (2 * a) := by
  let : SigmaCompactSpace (intrinsicPullBall (E := E) R) :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen
        𝓘(Real, E) (intrinsicPullBall (E := E) R).isOpen)
  let : RiemannianBundle
      (fun y : intrinsicPullBall (E := E) R ↦
        TangentSpace 𝓘(Real, E) y) :=
    ⟨(intrinsicPullMetric (I := I) g hEnorm p hloc).toRiemannianMetric⟩
  have ha : 0 < a := (norm_nonneg (x : E)).trans_lt hx
  have hx0 :=
    intrinsicPull_dist_zero (I := I) g hEnorm p hR hloc x
  have hq0 :=
    intrinsicPull_dist_zero (I := I) g hEnorm p hR hloc q
  change
    Manifold.riemannianEDist 𝓘(Real, E) x q <
      ENNReal.ofReal (2 * a)
  change
    Manifold.riemannianEDist 𝓘(Real, E)
        (intrinsicZero (E := E) hR) x =
      ENNReal.ofReal ‖(x : E)‖ at hx0
  change
    Manifold.riemannianEDist 𝓘(Real, E)
        (intrinsicZero (E := E) hR) q =
      ENNReal.ofReal ‖(q : E)‖ at hq0
  calc
    Manifold.riemannianEDist 𝓘(Real, E) x q
        ≤ Manifold.riemannianEDist 𝓘(Real, E)
            x (intrinsicZero (E := E) hR) +
          Manifold.riemannianEDist 𝓘(Real, E)
            (intrinsicZero (E := E) hR) q :=
      Manifold.riemannianEDist_triangle
    _ = ENNReal.ofReal ‖(x : E)‖ +
          ENNReal.ofReal ‖(q : E)‖ := by
      rw [Manifold.riemannianEDist_comm, hx0, hq0]
    _ < ENNReal.ofReal a + ENNReal.ofReal a :=
      ENNReal.add_lt_add_of_lt_of_le
        ENNReal.ofReal_ne_top
        ((ENNReal.ofReal_lt_ofReal_iff ha).2 hx)
        (ENNReal.ofReal_le_ofReal hq)
    _ = ENNReal.ofReal (2 * a) := by
      rw [← ENNReal.ofReal_add ha.le ha.le]
      congr 1
      ring

end PullbackDistance

end CheegerGromovTaylor
end Riemannian
end Geometry
end DifferentialGeometry
