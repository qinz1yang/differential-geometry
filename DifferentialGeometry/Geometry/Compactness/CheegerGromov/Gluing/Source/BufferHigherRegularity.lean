import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.ChartFamily
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Gluing.Source.Buffer



import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Gluing.StageComparison.Basic
import DifferentialGeometry.Topology.FirstExit

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Set Bundle Manifold
open scoped ContDiff Manifold Topology

open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}

omit [CompleteSpace E] in
private theorem NormalBallChart.MetricEquivOn.inv_join_le
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (hcomplete : MetricComplete (I := I) Y)
    (hconn :
      letI : TopologicalSpace Y.M := Y.topology
      ConnectedSpace Y.M)
    (hEnorm :
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : RiemannianBundle (fun x : Y.M ↦ TangentSpace I x) :=
        Y.riemBundle (I := I)
      ∀ (x : Y.M) (v : TangentSpace I x),
        ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (Y.metric.inner x v v)))
    {p : Y.M} (c : NormalChartAt (I := I) Y p) {U : Set E}
    (h :
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      c.MetricEquivOn Y.metric U)
    {x y : Y.M} {t : Real} (ht : t ∈ Set.Icc (0 : Real) 1)
    (hjoin :
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : IsManifold I 1 Y.M := IsManifold.of_le
        (I := I) (M := Y.M) (n := ∞) (by decide)
      letI : SigmaCompactSpace Y.M := Y.sigmaCompact
      letI : T2Space Y.M := Y.t2
      letI : ConnectedSpace Y.M := hconn
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      letI : TopologicalSpace.MetrizableSpace Y.M :=
        Manifold.metrizableSpace I Y.M
      letI : T3Space Y.M := inferInstance
      letI : RiemannianBundle (fun z : Y.M ↦ TangentSpace I z) :=
        Y.riemBundle (I := I)
      letI : (z : Y.M) → InnerProductSpace Real (TangentSpace I z) :=
        Y.riemInner (I := I)
      letI : IsContinuousRiemannianBundle E
          (fun z : Y.M ↦ TangentSpace I z) := Y.riemBundle_cont (I := I)
      letI : EMetricSpace Y.M := Y.emetricSpace (I := I)
      letI : CompleteSpace Y.M :=
        MetricComplete.complete (I := I) Y hcomplete
      Set.MapsTo (minJoin (I := I) Y.metric hEnorm x y)
        (Set.Icc (0 : Real) t)
        (c.hom.target ∩ c.inv ⁻¹' U)) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : IsManifold I 1 Y.M := IsManifold.of_le
      (I := I) (M := Y.M) (n := ∞) (by decide)
    letI : SigmaCompactSpace Y.M := Y.sigmaCompact
    letI : T2Space Y.M := Y.t2
    letI : ConnectedSpace Y.M := hconn
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    letI : TopologicalSpace.MetrizableSpace Y.M :=
      Manifold.metrizableSpace I Y.M
    letI : T3Space Y.M := inferInstance
    letI : RiemannianBundle (fun z : Y.M ↦ TangentSpace I z) :=
      Y.riemBundle (I := I)
    letI : (z : Y.M) → InnerProductSpace Real (TangentSpace I z) :=
      Y.riemInner (I := I)
    letI : IsContinuousRiemannianBundle E
        (fun z : Y.M ↦ TangentSpace I z) := Y.riemBundle_cont (I := I)
    letI : EMetricSpace Y.M := Y.emetricSpace (I := I)
    letI : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
    dist (c.inv x)
        (c.inv (minJoin (I := I) Y.metric hEnorm x y t)) ≤
      Real.sqrt 2 * (riemannianEDist I x y).toReal * t := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : IsManifold I 1 Y.M := IsManifold.of_le
    (I := I) (M := Y.M) (n := ∞) (by decide)
  let : SigmaCompactSpace Y.M := Y.sigmaCompact
  let : T2Space Y.M := Y.t2
  let : ConnectedSpace Y.M := hconn
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  let : TopologicalSpace.MetrizableSpace Y.M :=
    Manifold.metrizableSpace I Y.M
  let : T3Space Y.M := inferInstance
  let : RiemannianBundle (fun z : Y.M ↦ TangentSpace I z) :=
    Y.riemBundle (I := I)
  let : (z : Y.M) → InnerProductSpace Real (TangentSpace I z) :=
    Y.riemInner (I := I)
  let : IsContinuousRiemannianBundle E
      (fun z : Y.M ↦ TangentSpace I z) := Y.riemBundle_cont (I := I)
  let : EMetricSpace Y.M := Y.emetricSpace (I := I)
  let : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
  let w : TangentSpace I x := minimizingVec (I := I) Y.metric hEnorm x y
  let gamma : Real → Y.M := minJoin (I := I) Y.metric hEnorm x y
  let eta : Real → E := c.inv ∘ gamma
  let d : Real := (riemannianEDist I x y).toReal
  have hd : 0 ≤ d := ENNReal.toReal_nonneg
  have hgammaCont : Continuous gamma := by
    simpa only [gamma] using minJoin_cont (I := I) Y.metric hEnorm x y
  have hdiff : ∀ s ∈ Set.Icc (0 : Real) t,
      DifferentiableAt Real eta s := by
    intro s hs
    have hgammaDiff : MDifferentiableAt 𝓘(Real, Real) I gamma s := by
      have hsmooth := intrinsicGeodesic_contMDiffOn
        (I := I) Y.metric hEnorm x w
      have hm := hsmooth.mdifferentiableOn one_ne_zero s (Set.mem_univ s)
      with_unfolding_all
        exact hm.mdifferentiableAt (isOpen_univ.mem_nhds (Set.mem_univ s))
    have hinvDiff : MDifferentiableAt I 𝓘(Real, E) c.inv (gamma s) :=
      (c.hom.symm.contMDiffOn_toFun.mdifferentiableOn one_ne_zero _
        (hjoin hs).1).mdifferentiableAt
          (c.hom.open_target.mem_nhds (hjoin hs).1)
    exact mdifferentiableAt_iff_differentiableAt.mp
      (by simpa only [eta] using hinvDiff.comp s hgammaDiff)
  have hbound : ∀ s ∈ Set.Icc (0 : Real) t,
      ‖deriv eta s‖ ≤ Real.sqrt 2 * d := by
    intro s hs
    have hgammaDiff : MDifferentiableAt 𝓘(Real, Real) I gamma s := by
      have hsmooth := intrinsicGeodesic_contMDiffOn
        (I := I) Y.metric hEnorm x w
      have hm := hsmooth.mdifferentiableOn one_ne_zero s (Set.mem_univ s)
      with_unfolding_all
        exact hm.mdifferentiableAt (isOpen_univ.mem_nhds (Set.mem_univ s))
    have hinvDiff : MDifferentiableAt I 𝓘(Real, E) c.inv (gamma s) :=
      (c.hom.symm.contMDiffOn_toFun.mdifferentiableOn one_ne_zero _
        (hjoin hs).1).mdifferentiableAt
          (c.hom.open_target.mem_nhds (hjoin hs).1)
    have hetaDiff : MDifferentiableAt 𝓘(Real, Real) 𝓘(Real, E) eta s := by
      simpa only [eta] using hinvDiff.comp s hgammaDiff
    have hetaSrc : eta s ∈ c.hom.source :=
      c.hom.map_target (hjoin hs).1
    have hhomDiff : MDifferentiableAt 𝓘(Real, E) I c.hom (eta s) :=
      (c.hom.contMDiffOn_toFun.mdifferentiableOn one_ne_zero _ hetaSrc)
        |>.mdifferentiableAt (c.hom.open_source.mem_nhds hetaSrc)
    have hnear : ∀ᶠ q in nhds s, gamma q ∈ c.hom.target :=
      hgammaCont.continuousAt.eventually
        (c.hom.open_target.mem_nhds (hjoin hs).1)
    have heq : c.hom ∘ eta =ᶠ[nhds s] gamma := by
      filter_upwards [hnear] with q hq
      change c.hom (c.hom.symm (gamma q)) = gamma q
      exact c.hom.right_inv hq
    have hcomp :
        (mfderiv 𝓘(Real, E) I c.hom (eta s)).comp
            (mfderiv 𝓘(Real, Real) 𝓘(Real, E) eta s) =
          mfderiv 𝓘(Real, Real) I gamma s := by
      have hderiv := Filter.EventuallyEq.mfderiv_eq
        (I := 𝓘(Real, Real)) (I' := I) heq
      rw [mfderiv_comp s hhomDiff hetaDiff] at hderiv
      simpa only using hderiv
    have hetaVel : mfderiv 𝓘(Real, Real) 𝓘(Real, E) eta s 1 =
        deriv eta s := by
      rw [mfderiv_eq_fderiv]
      exact fderiv_apply_one_eq_deriv
    have hvel : mfderiv 𝓘(Real, E) I c.hom (eta s) (deriv eta s) =
        mfderiv 𝓘(Real, Real) I gamma s 1 := by
      have hv := DFunLike.congr_fun hcomp (1 : Real)
      change (mfderiv 𝓘(Real, E) I c.hom (eta s))
          (mfderiv 𝓘(Real, Real) 𝓘(Real, E) eta s 1) =
        mfderiv 𝓘(Real, Real) I gamma s 1 at hv
      rw [hetaVel] at hv
      exact hv
    have hlaunch : Y.metric.inner x w w = d ^ 2 := by
      have hnonneg : 0 ≤ Y.metric.inner x w w :=
        gInner_self_nonneg (I := I) Y.metric x w
      calc
        Y.metric.inner x w w =
            (Real.sqrt (Y.metric.inner x w w)) ^ 2 :=
          (Real.sq_sqrt hnonneg).symm
        _ = d ^ 2 := by
          rw [minimizingVec_len (I := I) Y.metric hEnorm x y]
    have hspeed : Y.metric.inner (gamma s)
          (mfderiv 𝓘(Real, Real) I gamma s 1)
          (mfderiv 𝓘(Real, Real) I gamma s 1) = d ^ 2 := by
      calc
        _ = Y.metric.inner x w w := by
          with_unfolding_all
            exact intrinsicGeodesic_speedSq_eq (I := I) Y.metric hEnorm x w s
        _ = d ^ 2 := hlaunch
    have hbase : c.hom (eta s) = gamma s := heq.self_of_nhds
    have hmetric : c.metric Y.metric (eta s)
          (deriv eta s) (deriv eta s) = d ^ 2 := by
      rw [c.metric_apply, hbase]
      exact (congrArg
        (fun v => Y.metric.inner (gamma s) v v) hvel).trans hspeed
    have hlower := (h (eta s) (hjoin hs).2 (deriv eta s)).1
    rw [hmetric] at hlower
    have hsq : ‖deriv eta s‖ ^ 2 ≤ (Real.sqrt 2 * d) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : Real) ≤ 2)]
      nlinarith
    exact le_of_sq_le_sq hsq (mul_nonneg (Real.sqrt_nonneg 2) hd)
  have hmean := Convex.norm_image_sub_le_of_norm_deriv_le
    (f := eta) hdiff hbound (convex_Icc (0 : Real) t)
    (left_mem_Icc.mpr ht.1) (right_mem_Icc.mpr ht.1)
  have hend : dist (c.inv x) (c.inv (gamma t)) =
      ‖eta t - eta 0‖ := by
    rw [dist_eq_norm]
    dsimp only [eta, Function.comp_apply]
    have hgammaZero : gamma 0 = x := by
      dsimp only [gamma]
      exact minJoin_zero (I := I) Y.metric hEnorm x y
    rw [hgammaZero]
    exact norm_sub_rev _ _
  rw [hend]
  have ht_abs : |t| = t := abs_of_nonneg ht.1
  simpa only [Real.norm_eq_abs, sub_zero, ht_abs, d, mul_assoc] using hmean

omit [CompleteSpace E] in
theorem NormalBallChart.MetricEquivOn.core_dist
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (hcomplete : MetricComplete (I := I) Y)
    (hconn :
      letI : TopologicalSpace Y.M := Y.topology
      ConnectedSpace Y.M)
    (hEnorm :
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : RiemannianBundle (fun x : Y.M ↦ TangentSpace I x) :=
        Y.riemBundle (I := I)
      ∀ (x : Y.M) (v : TangentSpace I x),
        ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (Y.metric.inner x v v)))
    {p : Y.M} (c : NormalChartAt (I := I) Y p) {U C : Set E}
    (h :
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      c.MetricEquivOn Y.metric U)
    (hCU : C ⊆ U)
    (hUsrc :
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      U ⊆ c.hom.source)
    {z : E} {eta rho : Real} (heta : 0 < eta)
    (hclosed : Metric.closedBall z eta ⊆ interior C)
    (hrhoeta : Real.sqrt 2 * rho < eta) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : IsManifold I 1 Y.M := IsManifold.of_le
      (I := I) (M := Y.M) (n := ∞) (by decide)
    letI : SigmaCompactSpace Y.M := Y.sigmaCompact
    letI : T2Space Y.M := Y.t2
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    letI : RiemannianBundle (fun x : Y.M ↦ TangentSpace I x) :=
      Y.riemBundle (I := I)
    {x | (riemannianEDist I (c.hom z) x).toReal < rho} ⊆
      {x | x ∈ c.hom '' interior C ∧
        dist (c.inv x) z ≤
          Real.sqrt 2 * (riemannianEDist I (c.hom z) x).toReal} := by
  classical
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : IsManifold I 1 Y.M := IsManifold.of_le
    (I := I) (M := Y.M) (n := ∞) (by decide)
  let : SigmaCompactSpace Y.M := Y.sigmaCompact
  let : T2Space Y.M := Y.t2
  let : ConnectedSpace Y.M := hconn
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  let : TopologicalSpace.MetrizableSpace Y.M :=
    Manifold.metrizableSpace I Y.M
  let : T3Space Y.M := inferInstance
  let : RiemannianBundle (fun x : Y.M ↦ TangentSpace I x) :=
    Y.riemBundle (I := I)
  let : (x : Y.M) → InnerProductSpace Real (TangentSpace I x) :=
    Y.riemInner (I := I)
  let : IsContinuousRiemannianBundle E
      (fun x : Y.M ↦ TangentSpace I x) := Y.riemBundle_cont (I := I)
  let : EMetricSpace Y.M := Y.emetricSpace (I := I)
  let : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
  let : MetricSpace Y.M := HopfRinow.riemMetricSpace (I := I) (M := Y.M)
  let B := Metric.closedBall z eta
  let K : Set Y.M := c.hom '' B
  have hBC : B ⊆ interior C := hclosed
  have hBU : B ⊆ U := hBC.trans (interior_subset.trans hCU)
  have hBsrc : B ⊆ c.hom.source := hBU.trans hUsrc
  have hBcompact : IsCompact B := isCompact_closedBall z eta
  have hhomCont : ContinuousOn c.hom c.hom.source :=
    c.hom.contMDiffOn_toFun.continuousOn
  have hKcompact : IsCompact K :=
    hBcompact.image_of_continuousOn (hhomCont.mono hBsrc)
  have hKclosed : IsClosed K := hKcompact.isClosed
  have hballB : Metric.ball z eta ⊆ B := Metric.ball_subset_closedBall
  have hballSrc : Metric.ball z eta ⊆ c.hom.source :=
    hballB.trans hBsrc
  let O : Set Y.M := c.hom '' Metric.ball z eta
  have hOopen : IsOpen O :=
    c.hom.toOpenPartialHomeomorph.isOpen_image_of_subset_source
      Metric.isOpen_ball hballSrc
  have hzball : z ∈ Metric.ball z eta := Metric.mem_ball_self heta
  have hyO : c.hom z ∈ O := ⟨z, hzball, rfl⟩
  have hOK : O ⊆ K := Set.image_mono hballB
  have hyInt : c.hom z ∈ interior K :=
    (interior_maximal hOK hOopen) hyO
  intro x hx
  let gamma : Real → Y.M :=
    minJoin (I := I) Y.metric hEnorm (c.hom z) x
  have hgammaCont : Continuous gamma := by
    simpa only [gamma] using
      minJoin_cont (I := I) Y.metric hEnorm (c.hom z) x
  have hgammaZero : gamma 0 = c.hom z := by
    dsimp only [gamma]
    exact minJoin_zero (I := I) Y.metric hEnorm (c.hom z) x
  have hgammaOne : gamma 1 = x := by
    dsimp only [gamma]
    exact minJoin_one (I := I) Y.metric hEnorm (c.hom z) x
  have hzSrc : z ∈ c.hom.source :=
    hBsrc (Metric.mem_closedBall_self heta.le)
  have hInvZ : c.inv (c.hom z) = z := c.hom.left_inv hzSrc
  have hgammaK : Set.MapsTo gamma (Set.Icc (0 : Real) 1) K := by
    intro q hq
    by_contra hqK
    have hqne : q ≠ 0 := by
      intro hqzero
      apply hqK
      simpa only [hqzero, hgammaZero] using interior_subset hyInt
    have hqpos : 0 < q := lt_of_le_of_ne hq.1 (Ne.symm hqne)
    obtain ⟨t, ht, hstay, hfront⟩ := exists_first_exit_frontier hKclosed hqpos
      (hgammaCont.continuousOn.mono (show
        Set.Icc (0 : Real) q ⊆ Set.Icc 0 1 from by
          intro s hs
          exact ⟨hs.1, hs.2.trans hq.2⟩))
      (by simpa only [hgammaZero] using hyInt) hqK
    have hfront' : gamma t ∈ K ∧ gamma t ∉ interior K := by
      rw [frontier, hKclosed.closure_eq] at hfront
      exact hfront
    obtain ⟨w, hwB, hwgamma⟩ := hfront'.1
    have hwSrc : w ∈ c.hom.source := hBsrc hwB
    have hInvGamma : c.inv (gamma t) = w := by
      rw [← hwgamma]
      exact c.hom.left_inv hwSrc
    have hwNotBall : w ∉ Metric.ball z eta := by
      intro hwball
      apply hfront'.2
      exact (interior_maximal hOK hOopen) ⟨w, hwball, hwgamma⟩
    have hwDist : dist z w = eta := by
      have hwle : dist w z ≤ eta := Metric.mem_closedBall.mp hwB
      have hwnlt : ¬ dist w z < eta := by
        simpa only [Metric.mem_ball, dist_comm] using hwNotBall
      rw [dist_comm]
      exact le_antisymm hwle (not_lt.mp hwnlt)
    have hjoin : Set.MapsTo gamma (Set.Icc (0 : Real) t)
        (c.hom.target ∩ c.inv ⁻¹' U) := by
      intro s hs
      obtain ⟨v, hvB, hvgamma⟩ := hstay s hs
      have hvSrc : v ∈ c.hom.source := hBsrc hvB
      have htgt : gamma s ∈ c.hom.target := by
        rw [← hvgamma]
        exact c.hom.map_source hvSrc
      have hinv : c.inv (gamma s) = v := by
        rw [← hvgamma]
        exact c.hom.left_inv hvSrc
      refine ⟨htgt, ?_⟩
      change c.inv (gamma s) ∈ U
      rw [hinv]
      exact hBU hvB
    have htunit : t ∈ Set.Icc (0 : Real) 1 :=
      ⟨ht.1.le, ht.2.trans hq.2⟩
    have hprefix := NormalBallChart.MetricEquivOn.inv_join_le
      Y hcomplete hconn hEnorm c h htunit hjoin
    have hcoord : eta ≤
        Real.sqrt 2 * (riemannianEDist I (c.hom z) x).toReal * t := by
      have heq :
          dist (c.inv (c.hom z)) (c.inv (gamma t)) = eta := by
        rw [hInvZ, hInvGamma, hwDist]
      calc
        eta = dist (c.inv (c.hom z)) (c.inv (gamma t)) := heq.symm
        _ ≤ Real.sqrt 2 *
            (riemannianEDist I (c.hom z) x).toReal * t := by
          simpa only [gamma] using hprefix
    have hsqrt : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    have hdnonneg : 0 ≤ (riemannianEDist I (c.hom z) x).toReal :=
      ENNReal.toReal_nonneg
    have hsmall : Real.sqrt 2 *
        (riemannianEDist I (c.hom z) x).toReal * t <
          Real.sqrt 2 * rho := by
      have hfirst : Real.sqrt 2 *
          (riemannianEDist I (c.hom z) x).toReal < Real.sqrt 2 * rho :=
        mul_lt_mul_of_pos_left hx (Real.sqrt_pos.2 (by norm_num))
      calc
        Real.sqrt 2 * (riemannianEDist I (c.hom z) x).toReal * t ≤
            Real.sqrt 2 * (riemannianEDist I (c.hom z) x).toReal * 1 :=
          mul_le_mul_of_nonneg_left htunit.2 (mul_nonneg hsqrt hdnonneg)
        _ < Real.sqrt 2 * rho := by simpa only [mul_one] using hfirst
    linarith
  have hxK : x ∈ K := by
    have hxK' := hgammaK (by simp : (1 : Real) ∈ Set.Icc 0 1)
    simpa only [hgammaOne] using hxK'
  obtain ⟨w, hwB, hwx⟩ := hxK
  have hxcore : x ∈ c.hom '' interior C := ⟨w, hBC hwB, hwx⟩
  have hjoin : Set.MapsTo gamma (Set.Icc (0 : Real) 1)
      (c.hom.target ∩ c.inv ⁻¹' U) := by
    intro q hq
    obtain ⟨v, hvB, hvgamma⟩ := hgammaK hq
    have hvSrc : v ∈ c.hom.source := hBsrc hvB
    have htgt : gamma q ∈ c.hom.target := by
      rw [← hvgamma]
      exact c.hom.map_source hvSrc
    have hinv : c.inv (gamma q) = v := by
      rw [← hvgamma]
      exact c.hom.left_inv hvSrc
    refine ⟨htgt, ?_⟩
    change c.inv (gamma q) ∈ U
    rw [hinv]
    exact hBU hvB
  have hfull := NormalBallChart.MetricEquivOn.inv_join_le
    Y hcomplete hconn hEnorm c h
      (by simp : (1 : Real) ∈ Set.Icc 0 1) hjoin
  have hcoord : dist (c.inv x) z ≤
      Real.sqrt 2 * (riemannianEDist I (c.hom z) x).toReal := by
    have hfull' : dist (c.inv (c.hom z)) (c.inv x) ≤
        Real.sqrt 2 * (riemannianEDist I (c.hom z) x).toReal := by
      rw [minJoin_one (I := I) Y.metric hEnorm (c.hom z) x] at hfull
      simpa only [mul_one] using hfull
    calc
      dist (c.inv x) z =
          dist (c.inv (c.hom z)) (c.inv x) := by
        rw [hInvZ, dist_comm]
      _ ≤ Real.sqrt 2 *
          (riemannianEDist I (c.hom z) x).toReal := hfull'
  exact ⟨hxcore, hcoord⟩

omit [CompleteSpace E] in
theorem BoundedGeometryNormalChartData.metric_buffer
    (inp : MetricCompactCore (I := I) X)
    (d : BoundedGeometryNormalChartData (I := I) X inp.decay)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P)
    (r : Real) (hr : 0 ≤ r)
    {phi : Nat → Nat} {hphi : StrictMono phi}
    (U C0 C1 : LiveSlot L inp.pack r → Set E)
    (aInf : (alpha : LiveSlot L inp.pack r) →
      Fin (inp.pack.A r) → E → Real)
    (Jinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E)
    (Jbarinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E)
    (h : HasSuppConvDataOn (I := I) inp P L r hr phi hphi d.chart
      U C0 C1 aInf Jinf Jbarinf)
    (hcomplete : ∀ j, MetricComplete (I := I) (X.obj j))
    (hconn : ∀ j,
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      ConnectedSpace (X.obj j).M) :
    let Lphi := L.subseq hphi
    ∃ rho : Real, 0 < rho ∧ ∀ k,
      let Y := X.obj (Lphi.φ k)
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : T2Space Y.M := Y.t2
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      letI : MetricSpace Y.M := (P (Lphi.φ k)).ms
      ∀ y ∈ Lphi.hatSourceBall inp.decay P r k,
        ∃ (alpha : LiveSlot L inp.pack r) (z : E),
          (d.chart (Lphi.φ k)
            (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))).hom z = y ∧
          Metric.ball y rho ⊆
            (d.chart (Lphi.φ k)
              (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))).hom ''
                interior (C0 alpha) ∧
          ∀ x ∈ Metric.ball y rho,
            dist
                ((d.chart (Lphi.φ k)
                  (seqCenterD inp.decay P Lphi k
                    (alpha.1 : Nat))).inv x) z ≤
              Real.sqrt 2 * inp.decay.dist (Lphi.φ k) x y := by
  classical
  let Lphi := L.subseq hphi
  have hraw := h
  dsimp only [HasSuppConvDataOn] at hraw
  rcases hraw with
    ⟨_hU, _hU8, _hC0, _hC1, _hC01, _hC1U, _hconvex, _hzero,
      hbuffer, _hcore, _hgeom, _hlim, _hweight, _htrans, _hsmooth⟩
  obtain ⟨eta, heta, hbuffer⟩ := hbuffer
  let Yzero := X.obj (Lphi.φ 0)
  let : TopologicalSpace Yzero.M := Yzero.topology
  let : ChartedSpace H Yzero.M := Yzero.charted
  let : IsManifold I ∞ Yzero.M := Yzero.smooth
  let : T2Space Yzero.M := Yzero.t2
  let : T2Space (TangentBundle I Yzero.M) := Yzero.t2TangentBundle
  let : MetricSpace Yzero.M := (P (Lphi.φ 0)).ms
  have hbase : Yzero.basepoint ∈
      Lphi.hatSourceBall inp.decay P r 0 := by
    rw [NetLimitData.hatSourceBall, Metric.mem_closedBall, dist_self]
    exact hr
  obtain ⟨alphaZero, _zZero, _hzZero, _hclosedZero⟩ :=
    hbuffer 0 Yzero.basepoint hbase
  let : Nonempty (LiveSlot L inp.pack r) := ⟨alphaZero⟩
  let etaMin : Real := Finset.univ.inf' Finset.univ_nonempty eta
  have hetaMin : 0 < etaMin := by
    dsimp only [etaMin]
    rw [Finset.lt_inf'_iff]
    intro alpha _halpha
    exact heta alpha
  let rho : Real := etaMin / 4
  have hrho : 0 < rho := div_pos hetaMin (by norm_num)
  refine ⟨rho, hrho, ?_⟩
  intro k
  dsimp only
  let Y := X.obj (Lphi.φ k)
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : T2Space Y.M := Y.t2
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  let : MetricSpace Y.M := (P (Lphi.φ k)).ms
  intro y hy
  obtain ⟨alpha, z, hzy, hzclosed⟩ := hbuffer k y hy
  have hetaMinLe : etaMin ≤ eta alpha := by
    dsimp only [etaMin]
    exact Finset.inf'_le (s := Finset.univ) (f := eta) (by simp)
  have hsqrtTwo : Real.sqrt 2 < 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : Real) ≤ 2)]
  have hrhoeta : Real.sqrt 2 * rho < eta alpha := by
    have hhalf : Real.sqrt 2 * rho < etaMin := by
      dsimp only [rho]
      have hsqrtNonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
      nlinarith
    exact hhalf.trans_le hetaMinLe
  obtain ⟨_hUopen, _hC0compact, _hC1compact, hC01, hC1U⟩ :=
    h.core_on inp P L r hr d.chart U C0 C1 aInf Jinf Jbarinf alpha
  have hC0U : C0 alpha ⊆ U alpha :=
    (hC01.trans interior_subset).trans hC1U
  obtain ⟨hRad, _hmap⟩ :=
    h.geom_on inp P L r hr d.chart U C0 C1 aInf Jinf Jbarinf k alpha
  let c : Y.M := seqCenterD inp.decay P Lphi k (alpha.1 : Nat)
  let chi := d.chart (Lphi.φ k) c
  have hequiv : chi.MetricEquivOn Y.metric (U alpha) := by
    intro w hw v
    exact d.metric_equiv (Lphi.φ k) c w (hRad hw) v
  have hUsrc : U alpha ⊆ chi.hom.source := by
    intro w hw
    exact chi.ball_subset (hRad hw)
  let : RiemannianBundle (fun q : Y.M ↦ TangentSpace I q) :=
    Y.riemBundle (I := I)
  have hcore := NormalBallChart.MetricEquivOn.core_dist Y
    (hcomplete (Lphi.φ k)) (hconn (Lphi.φ k))
      (normal_enorm (I := I) Y) chi hequiv hC0U hUsrc
        (heta alpha) hzclosed hrhoeta
  have hcenter : chi.hom z = y := by
    with_unfolding_all
      exact hzy
  have hpoint (x : Y.M) (hx : x ∈ Metric.ball y rho) :
      x ∈ chi.hom '' interior (C0 alpha) ∧
        dist (chi.inv x) z ≤
          Real.sqrt 2 * inp.decay.dist (Lphi.φ k) x y := by
    have hxP : dist x y < rho := by
      simpa only [Metric.mem_ball] using hx
    have hdecay : inp.decay.dist (Lphi.φ k) x y < rho := by
      rw [← ProperMetricOn.dist_eq inp.decay inp.realizes P (Lphi.φ k) x y]
      exact hxP
    have hed : riemannianEDist I x y =
        ENNReal.ofReal (inp.decay.dist (Lphi.φ k) x y) := by
      have hrealize := inp.realizes.edist_eq (Lphi.φ k) x y
      change riemannianEDist I x y = _ at hrealize
      exact hrealize
    have hriem : (riemannianEDist I (chi.hom z) x).toReal < rho := by
      rw [hcenter, riemannianEDist_comm, hed, ENNReal.toReal_ofReal
        (inp.realizes.dist_nonneg (Lphi.φ k) x y)]
      exact hdecay
    have hp := hcore hriem
    refine ⟨hp.1, ?_⟩
    have hcoord := hp.2
    rw [hcenter, riemannianEDist_comm, hed, ENNReal.toReal_ofReal
      (inp.realizes.dist_nonneg (Lphi.φ k) x y)] at hcoord
    simpa only [chi, c] using hcoord
  refine ⟨alpha, z, hcenter, ?_, ?_⟩
  · intro x hx
    exact (hpoint x hx).1
  · intro x hx
    exact (hpoint x hx).2

end HCGCompactness
end DifferentialGeometry
