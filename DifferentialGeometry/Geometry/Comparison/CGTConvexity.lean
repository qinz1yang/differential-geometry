import DifferentialGeometry.Geometry.Comparison.CGTPullbackMetric
import DifferentialGeometry.Geometry.Comparison.CGTRadialPath
import DifferentialGeometry.Geometry.Comparison.Variation.EndpointPositive
import DifferentialGeometry.Geometry.Metric.DistanceScaling

set_option autoImplicit false

noncomputable section

open Metric Set
open scoped ContDiff Manifold

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace CGT

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]

def intrCore (R a : Real) : Set (intrPullBall (E := E) R) :=
  {z | ‖(z : E)‖ ≤ a}

omit [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)] in
@[simp] theorem mem_intrCore
    {R a : Real} {z : intrPullBall (E := E) R} :
    z ∈ intrCore (E := E) R a ↔ ‖(z : E)‖ ≤ a :=
  Iff.rfl

omit [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)] in
theorem intrCore_mono
    {R a b : Real} (hab : a ≤ b) :
    intrCore (E := E) R a ⊆ intrCore (E := E) R b := by
  intro z hz
  exact hz.trans hab

omit [NeZero (Module.finrank Real E)] in
theorem intrCore_compact
    {R a : Real} (haR : a < R) :
    IsCompact (intrCore (E := E) R a) := by
  letI : ProperSpace E := FiniteDimensional.proper Real E
  rw [Subtype.isCompact_iff]
  have himage :
      ((fun z : intrPullBall (E := E) R => (z : E)) ''
          intrCore (E := E) R a) =
        Metric.closedBall (0 : E) a := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      simpa only [Metric.mem_closedBall, dist_zero_right] using hw
    · intro hz
      have hza : ‖z‖ ≤ a := by
        simpa only [Metric.mem_closedBall, dist_zero_right] using hz
      have hzR : ‖z‖ < R := hza.trans_lt haR
      refine ⟨⟨z, ?_⟩, hza, rfl⟩
      change z ∈ Metric.ball (0 : E) R
      simpa only [Metric.mem_ball, dist_zero_right] using hzR
  rw [himage]
  exact isCompact_closedBall (0 : E) a

def intrZero {R : Real} (hR : 0 < R) : intrPullBall (E := E) R :=
  ⟨0, by
    change (0 : E) ∈ Metric.ball 0 R
    simpa only [Metric.mem_ball, dist_self] using hR⟩

omit [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)] in
theorem intrZero_mem
    {R a : Real} (hR : 0 < R) (ha : 0 ≤ a) :
    intrZero (E := E) hR ∈ intrCore (E := E) R a := by
  simpa only [mem_intrCore, intrZero, norm_zero] using ha

noncomputable def intrRadial
    {R : Real} (z : intrPullBall (E := E) R) (t : Real) :
    intrPullBall (E := E) R := by
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
@[simp] theorem intrRadial_zero
    {R : Real} (hR : 0 < R) (z : intrPullBall (E := E) R) :
    intrRadial (E := E) z 0 = intrZero (E := E) hR := by
  apply Subtype.ext
  simp only [intrRadial, intrZero,
    Real.smoothTransition.zero_of_nonpos le_rfl, zero_smul]

omit [FiniteDimensional Real E] [NeZero (Module.finrank Real E)] in
@[simp] theorem intrRadial_one
    {R : Real} (z : intrPullBall (E := E) R) :
    intrRadial (E := E) z 1 = z := by
  apply Subtype.ext
  simp only [intrRadial, Real.smoothTransition.one_of_one_le le_rfl,
    one_smul]

omit [FiniteDimensional Real E] [NeZero (Module.finrank Real E)] in
theorem intrRadial_smooth
    {R : Real} (z : intrPullBall (E := E) R) :
    ContMDiff 𝓘(Real, Real) 𝓘(Real, E) ∞
      (intrRadial (E := E) z) := by
  intro t
  have hbase :
      ContMDiffAt 𝓘(Real, Real) 𝓘(Real, E) ∞
        (fun s : Real => Real.smoothTransition s • (z : E)) t := by
    rw [contMDiffAt_iff_contDiffAt]
    exact Real.smoothTransition.contDiff.contDiffAt.smul contDiffAt_const
  have hmem :
      ∀ s : Real,
        Real.smoothTransition s • (z : E) ∈
          intrPullBall (E := E) R :=
    fun s => (intrRadial (E := E) z s).property
  exact codRestr_contMDiffAt (V := intrPullBall (E := E) R) hmem hbase

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

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
variable [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

noncomputable local instance {R : Real} :
    SigmaCompactSpace (intrPullBall (E := E) R) :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen
      𝓘(Real, E) (intrPullBall (E := E) R).isOpen)

theorem intrRadial_len
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)))
    (p : M) {R : Real}
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    (z : intrPullBall (E := E) R) :
    letI : SigmaCompactSpace (intrPullBall (E := E) R) :=
      isSigmaCompact_iff_sigmaCompactSpace.mp
        (Geometry.isSigmaCompact_of_isOpen
          𝓘(Real, E) (intrPullBall (E := E) R).isOpen)
    letI : RiemannianBundle
        (fun y : intrPullBall (E := E) R ↦
          TangentSpace 𝓘(Real, E) y) :=
      ⟨(intrPullMetric (I := I) g hEnorm p hloc).toRiemannianMetric⟩
    Manifold.pathELength 𝓘(Real, E)
        (intrRadial (E := E) z) 0 1 =
      ENNReal.ofReal ‖(z : E)‖ := by
  letI : SigmaCompactSpace (intrPullBall (E := E) R) :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen
        𝓘(Real, E) (intrPullBall (E := E) R).isOpen)
  letI : RiemannianBundle
      (fun y : intrPullBall (E := E) R ↦
        TangentSpace 𝓘(Real, E) y) :=
    ⟨(intrPullMetric (I := I) g hEnorm p hloc).toRiemannianMetric⟩
  have hradC1 :
      ContMDiffOn 𝓘(Real, Real) 𝓘(Real, E) 1
        (intrRadial (E := E) z) (Set.Icc 0 1) :=
    ((intrRadial_smooth (E := E) z).of_le (by norm_num)).contMDiffOn
  have hlocal :=
    intrPull_pathLen (I := I) g hEnorm p hloc
      (a := 0) (b := 1) hradC1
  rw [← hlocal]
  let v : TangentSpace I p := normalFrame (I := I) g p (z : E)
  let γ : Real → M :=
    fun t => intrinsicFramedExp (I := I) g hEnorm p (t • (z : E))
  have hγ :
      γ = intrinsicGeodesic (I := I) g hEnorm p v := by
    funext t
    dsimp only [γ, v]
    rw [intrFrame_apply, map_smul, expMapIntrinsic_def,
      intrinsicGeodesic_smul]
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

theorem intrPull_dist_zero
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)))
    (p : M) {R : Real} (hR : 0 < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    (z : intrPullBall (E := E) R) :
    riemannianEDistOf (I := 𝓘(Real, E))
        (intrPullMetric (I := I) g hEnorm p hloc)
        (intrZero (E := E) hR) z =
      ENNReal.ofReal ‖(z : E)‖ := by
  letI : SigmaCompactSpace (intrPullBall (E := E) R) :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen
        𝓘(Real, E) (intrPullBall (E := E) R).isOpen)
  letI : RiemannianBundle
      (fun y : intrPullBall (E := E) R ↦
        TangentSpace 𝓘(Real, E) y) :=
    ⟨(intrPullMetric (I := I) g hEnorm p hloc).toRiemannianMetric⟩
  change
    Manifold.riemannianEDist 𝓘(Real, E)
        (intrZero (E := E) hR) z =
      ENNReal.ofReal ‖(z : E)‖
  apply le_antisymm
  · have hradC1 :
        ContMDiffOn 𝓘(Real, Real) 𝓘(Real, E) 1
          (intrRadial (E := E) z) (Set.Icc 0 1) :=
      ((intrRadial_smooth (E := E) z).of_le
        (by norm_num)).contMDiffOn
    have hdist :=
      Manifold.riemannianEDist_le_pathELength
        (I := 𝓘(Real, E)) (x := intrZero (E := E) hR) (y := z)
        hradC1 (intrRadial_zero (E := E) hR z)
        (intrRadial_one (E := E) z) zero_le_one
    rw [intrRadial_len (I := I) g hEnorm p hloc z] at hdist
    exact hdist
  · by_contra hnot
    have hlt :
        Manifold.riemannianEDist 𝓘(Real, E)
            (intrZero (E := E) hR) z <
          ENNReal.ofReal ‖(z : E)‖ :=
      lt_of_not_ge hnot
    obtain ⟨γ, hγ0, hγ1, hγC1, hγlen⟩ :=
      Manifold.exists_lt_of_riemannianEDist_lt hlt
    let η : Real → E := fun t => (γ t : E)
    have hηm :
        ContMDiffOn 𝓘(Real, Real) 𝓘(Real, E) 1 η (Set.Icc 0 1) := by
      exact
        ((contMDiff_subtype_val (n := (⊤ : WithTop ℕ∞))
          (I := 𝓘(Real, E))
          (U := intrPullBall (E := E) R)).of_le
            (show (1 : WithTop ℕ∞) ≤ (⊤ : WithTop ℕ∞) from le_top)
          ).comp_contMDiffOn hγC1
    have hη : ContDiffOn Real 1 η (Set.Icc 0 1) :=
      contMDiffOn_iff_contDiffOn.mp hηm
    have hη0 : η 0 = 0 := by
      simp only [η, hγ0, intrZero]
    have hη1 : η 1 = (z : E) := by
      simp only [η, hγ1]
    have hlift :=
      intrLift_norm_le (J := I) g hEnorm p zero_le_one hη0 hη
    have hlen :
        Manifold.pathELength I
            ((intrinsicFramedExp (I := I) g hEnorm p) ∘ η) 0 1 =
          Manifold.pathELength 𝓘(Real, E) γ 0 1 := by
      simpa only [η, intrExpOn, Function.comp_apply] using
        (intrPull_pathLen (I := I) g hEnorm p hloc hγC1)
    have hnorm_le :
        ENNReal.ofReal ‖(z : E)‖ ≤
          Manifold.pathELength 𝓘(Real, E) γ 0 1 := by
      rw [← hη1, ← hlen]
      exact hlift
    exact (not_lt_of_ge hnorm_le) hγlen

theorem intrPull_pair_pos
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)))
    (p : M) {R K L : Real}
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    (hK : 0 ≤ K) (hL : 0 < L)
    (hKL : K * L ^ 2 < (Real.pi / 2) ^ 2)
    (γ : Real → intrPullBall (E := E) R)
    (J : ∀ t : Real, TangentSpace 𝓘(Real, E) (γ t))
    (hRm : ∀ t ∈ Set.Icc (0 : Real) 1,
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
        (intrinsicFramedExp (I := I) g hEnorm p
          ((γ t : intrPullBall (E := E) R) : E)) 4
        (Geometry.Curvature.metricRm04At
          (I := I) (M := M) g
          (intrinsicFramedExp (I := I) g hEnorm p
            ((γ t : intrPullBall (E := E) R) : E)))) ≤ K)
    (hγ : ContMDiff 𝓘(Real, Real) 𝓘(Real, E) ∞ γ)
    (hgeo :
      IsGeodesicOn (I := 𝓘(Real, E))
        (intrPullMetric (I := I) g hEnorm p hloc) γ
        (Set.Icc (0 : Real) 1))
    (hJdiff : ∀ t, DifferentiableAt Real
      (chartRepAt (I := 𝓘(Real, E)) γ J t) t)
    (hDJdiff : ∀ t, DifferentiableAt Real
      (chartRepAt (I := 𝓘(Real, E)) γ
        (fun s => covDerivAlong (I := 𝓘(Real, E))
          (intrPullMetric (I := I) g hEnorm p hloc) γ J s) t) t)
    (hJac : ∀ t ∈ Set.Icc (0 : Real) 1,
      IsJacobiAt (I := 𝓘(Real, E))
        (intrPullMetric (I := I) g hEnorm p hloc) γ J t)
    (hJ0 : J 0 = 0) (hJ1 : J 1 ≠ 0)
    (hspeed : ∀ t ∈ Set.Icc (0 : Real) 1,
      (intrPullMetric (I := I) g hEnorm p hloc).inner (γ t)
          (curveVelocity (I := 𝓘(Real, E)) γ t)
          (curveVelocity (I := 𝓘(Real, E)) γ t) =
        L ^ 2)
    (hJperp : ∀ t ∈ Set.Icc (0 : Real) 1,
      (intrPullMetric (I := I) g hEnorm p hloc).inner (γ t) (J t)
          (curveVelocity (I := 𝓘(Real, E)) γ t) = 0) :
    0 <
      (intrPullMetric (I := I) g hEnorm p hloc).inner (γ 1)
        (covDerivAlong (I := 𝓘(Real, E))
          (intrPullMetric (I := I) g hEnorm p hloc) γ J 1)
        (J 1) := by
  letI : SigmaCompactSpace (intrPullBall (E := E) R) :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen
        𝓘(Real, E) (intrPullBall (E := E) R).isOpen)
  let gPull := intrPullMetric (I := I) g hEnorm p hloc
  letI : RiemannianBundle
      (fun y : intrPullBall (E := E) R ↦
        TangentSpace 𝓘(Real, E) y) :=
    ⟨gPull.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E
      (fun y : intrPullBall (E := E) R ↦
        TangentSpace 𝓘(Real, E) y) :=
    ⟨gPull.inner, gPull.contMDiff.continuous, by intro z v w; rfl⟩
  letI : PseudoEMetricSpace (intrPullBall (E := E) R) :=
    PseudoEMetricSpace.ofRiemannianMetric 𝓘(Real, E)
      (intrPullBall (E := E) R)
  letI : IsRiemannianManifold 𝓘(Real, E)
      (intrPullBall (E := E) R) :=
    ⟨fun _ _ => rfl⟩
  apply Variation.jacobi_pair_pos
    (I := 𝓘(Real, E)) gPull γ J hγ hgeo hJdiff hDJdiff hJac hJ0 hJ1
  · intro t ht
    rw [hspeed t ht]
    positivity
  · exact hJperp
  · exact mul_nonneg hK (sq_nonneg L)
  · exact hKL
  · intro t ht
    have hquad :=
      intrPull_quad_le (I := I) g hEnorm p hloc (γ t)
        (hRm t ht) (J t) (curveVelocity (I := 𝓘(Real, E)) γ t)
    dsimp only at hquad
    rw [hspeed t ht] at hquad
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hquad

theorem intrCore_edist_lt
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)))
    (p : M) {R a : Real} (hR : 0 < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    {x q : intrPullBall (E := E) R}
    (hx : ‖(x : E)‖ < a)
    (hq : q ∈ intrCore (E := E) R a) :
    riemannianEDistOf (I := 𝓘(Real, E))
        (intrPullMetric (I := I) g hEnorm p hloc) x q <
      ENNReal.ofReal (2 * a) := by
  letI : SigmaCompactSpace (intrPullBall (E := E) R) :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen
        𝓘(Real, E) (intrPullBall (E := E) R).isOpen)
  letI : RiemannianBundle
      (fun y : intrPullBall (E := E) R ↦
        TangentSpace 𝓘(Real, E) y) :=
    ⟨(intrPullMetric (I := I) g hEnorm p hloc).toRiemannianMetric⟩
  have ha : 0 < a := (norm_nonneg (x : E)).trans_lt hx
  have hx0 :=
    intrPull_dist_zero (I := I) g hEnorm p hR hloc x
  have hq0 :=
    intrPull_dist_zero (I := I) g hEnorm p hR hloc q
  change
    Manifold.riemannianEDist 𝓘(Real, E) x q <
      ENNReal.ofReal (2 * a)
  change
    Manifold.riemannianEDist 𝓘(Real, E)
        (intrZero (E := E) hR) x =
      ENNReal.ofReal ‖(x : E)‖ at hx0
  change
    Manifold.riemannianEDist 𝓘(Real, E)
        (intrZero (E := E) hR) q =
      ENNReal.ofReal ‖(q : E)‖ at hq0
  calc
    Manifold.riemannianEDist 𝓘(Real, E) x q
        ≤ Manifold.riemannianEDist 𝓘(Real, E)
            x (intrZero (E := E) hR) +
          Manifold.riemannianEDist 𝓘(Real, E)
            (intrZero (E := E) hR) q :=
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

end CGT
end Riemannian
end Geometry
end DifferentialGeometry
