import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.Noncollapsing.Defs

import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Foundations.InjectivityRadius
import DifferentialGeometry.Geometry.Comparison.CheegerGromovTaylor.InjectivityRadius
import DifferentialGeometry.Geometry.Comparison.Volume.Segment.Polar
import DifferentialGeometry.Geometry.Comparison.Volume.Segment.BallEuclideanUpper
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.BoundedGeometry.NormalCoordinates.IntrinsicGeometry
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Covering.VolumeOverlap

open DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Bundle Manifold MeasureTheory Metric Set
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.BonnetMyers
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Perelman

variable {E : Type uE} [NormedAddCommGroup E]
variable [InnerProductSpace Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]

namespace PointedFlowData

def baseFlowBall
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D)
    (hzero : 0 ∈ D.carrier) (r : Real) (hr : 0 < r) :
    letI : TopologicalSpace F.M := F.topology
    letI : ChartedSpace H F.M := F.charted
    letI : IsManifold I ∞ F.M := F.smooth
    letI : IsManifold I 1 F.M :=
      IsManifold.of_le (I := I) (M := F.M) (n := ∞)
        (by decide : (1 : WithTop ℕ∞) ≤ ∞)
    letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) F.M := by
      change IsManifold I ∞ F.M
      infer_instance
    letI : SigmaCompactSpace F.M := F.sigmaCompact
    letI : T2Space F.M := F.t2
    DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall
      F.S ⟨0, hzero⟩ := by
  letI : TopologicalSpace F.M := F.topology
  letI : ChartedSpace H F.M := F.charted
  letI : IsManifold I ∞ F.M := F.smooth
  letI : IsManifold I 1 F.M :=
    IsManifold.of_le (I := I) (M := F.M) (n := ∞)
      (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) F.M := by
    change IsManifold I ∞ F.M
    infer_instance
  letI : SigmaCompactSpace F.M := F.sigmaCompact
  letI : T2Space F.M := F.t2
  exact { center := F.basepoint, radius := r, radius_pos := hr }

end PointedFlowData

structure FlowerScaleVolData
    (X : PointedFlowSeq.{u, uE, uH} (I := I)) where
  zero_mem : 0 ∈ X.D.carrier
  kappa : Real
  kappa_pos : 0 < kappa
  radius : Real
  radius_pos : 0 < radius

structure IsFlowerScaleVolBound
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    (V : FlowerScaleVolData (I := I) X) : Prop where
  curvature : ∀ i : Nat,
    letI : TopologicalSpace (X.term i).M := (X.term i).topology
    letI : ChartedSpace H (X.term i).M := (X.term i).charted
    letI : IsManifold I ∞ (X.term i).M := (X.term i).smooth
    letI : IsManifold I 1 (X.term i).M :=
      IsManifold.of_le (I := I) (M := (X.term i).M) (n := ∞)
        (by decide : (1 : WithTop ℕ∞) ≤ ∞)
    letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) (X.term i).M := by
      change IsManifold I ∞ (X.term i).M
      infer_instance
    letI : SigmaCompactSpace (X.term i).M := (X.term i).sigmaCompact
    letI : T2Space (X.term i).M := (X.term i).t2
    (PointedFlowData.baseFlowBall (I := I) (X.term i)
      V.zero_mem V.radius V.radius_pos).IsRmControlled
  noncollapsed : ∀ i : Nat,
    letI : TopologicalSpace (X.term i).M := (X.term i).topology
    letI : ChartedSpace H (X.term i).M := (X.term i).charted
    letI : IsManifold I ∞ (X.term i).M := (X.term i).smooth
    letI : IsManifold I 1 (X.term i).M :=
      IsManifold.of_le (I := I) (M := (X.term i).M) (n := ∞)
        (by decide : (1 : WithTop ℕ∞) ≤ ∞)
    letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) (X.term i).M := by
      change IsManifold I ∞ (X.term i).M
      infer_instance
    letI : SigmaCompactSpace (X.term i).M := (X.term i).sigmaCompact
    letI : T2Space (X.term i).M := (X.term i).t2
    (PointedFlowData.baseFlowBall (I := I) (X.term i)
      V.zero_mem V.radius V.radius_pos).IsKappaNoncollapsed V.kappa

private lemma ofReal_add_mul {a b c : Real}
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ENNReal.ofReal a * ENNReal.ofReal c +
        ENNReal.ofReal b * ENNReal.ofReal c =
      ENNReal.ofReal ((a + b) * c) := by
  rw [← add_mul, ← ENNReal.ofReal_add ha hb,
    ← ENNReal.ofReal_mul (add_nonneg ha hb)]

private lemma cgt_fit {s : Real} (hs : 0 < s) :
    s + 2 * s < 5 * s := by
  nlinarith

private lemma cgt_quarter {s : Real} (hs : 0 < s) :
    s < (5 * s) / 4 := by
  nlinarith

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
noncomputable def flowInjOfVol
    (X : PointedFlowSeq.{u, uE, uH} (I := I))
    (hcomplete : SeqMetricComplete (I := I) (X.atZero (I := I)))
    (hconn : ∀ i : Nat,
      letI : TopologicalSpace ((X.atZero (I := I)).obj i).M :=
        ((X.atZero (I := I)).obj i).topology
      ConnectedSpace ((X.atZero (I := I)).obj i).M)
    (hgeom : SeqBoundedGeometry (I := I) (X.atZero (I := I)))
    (V : FlowerScaleVolData (I := I) X)
    (hvol : IsFlowerScaleVolBound (I := I) V) :
    FlowerScaleInjBound (I := I) X := by
  classical
  letI : MeasurableSpace E := borel E
  letI : BorelSpace E := ⟨rfl⟩
  let Y : PointedRiemannianSeq.{u, uE, uH} (I := I) :=
    X.atZero (I := I)
  let hctrl := exists_intr_control (I := I) Y hcomplete hconn hgeom
  let rCtrl : Real := hctrl.choose
  have hrCtrl : 0 < rCtrl := hctrl.choose_spec.1
  have hcontrol := hctrl.choose_spec.2
  let n : Nat := Module.finrank Real E
  let d : Nat := n - 1
  let K : Real := hgeom.C 0 + 1
  let q : Real := (n : Real) * Real.sqrt K
  let s : Real :=
    min (rCtrl / 10)
      (min (Real.pi / (10 * Real.sqrt K)) (V.radius / 2))
  let sphereB : Real :=
    (((volume : Measure
      (EuclideanSpace Real (Fin n))).toSphere Set.univ)).toReal
  let sphereP : Real :=
    (((volume : Measure E).toSphere Set.univ)).toReal
  let modelTwo : Real := hypRadVol q d (2 * s)
  let den : Real := (sphereB + sphereP) * modelTwo
  let modelSmall : Real := hypRadVol q d s
  let modelLarge : Real := hypRadVol q d V.radius
  let low : Real :=
    V.kappa * V.radius ^ n * modelSmall / modelLarge
  let ρ : Real := (s / 2) * low / den
  have hn : 0 < n :=
    Nat.pos_of_ne_zero (NeZero.ne (Module.finrank Real E))
  have hC0 : 0 ≤ hgeom.C 0 := hgeom.nonneg 0
  have hK : 0 < K := by
    dsimp only [K]
    linarith
  have hsqrtK : 0 < Real.sqrt K := Real.sqrt_pos.mpr hK
  have hs : 0 < s := by
    dsimp only [s]
    apply lt_min
    · positivity
    · apply lt_min
      · exact div_pos Real.pi_pos (mul_pos (by norm_num) hsqrtK)
      · exact div_pos V.radius_pos (by norm_num)
  have hq : 0 ≤ q :=
    mul_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _)
  have hmodelTwo : 0 < modelTwo := by
    dsimp only [modelTwo]
    exact hypRadVol_pos hq (by positivity)
  have hmodelSmall : 0 < modelSmall := by
    dsimp only [modelSmall]
    exact hypRadVol_pos hq hs
  have hmodelLarge : 0 < modelLarge := by
    dsimp only [modelLarge]
    exact hypRadVol_pos hq V.radius_pos
  have hlow : 0 < low := by
    dsimp only [low]
    exact div_pos
      (mul_pos (mul_pos V.kappa_pos (pow_pos V.radius_pos _)) hmodelSmall)
      hmodelLarge
  letI : Nontrivial E :=
    Module.nontrivial_of_finrank_pos hn
  have hfinEucl :
      0 < Module.finrank Real
        (EuclideanSpace Real (Fin n)) := by
    simpa only [finrank_euclideanSpace, Fintype.card_fin] using hn
  letI : Nontrivial (EuclideanSpace Real (Fin n)) :=
    Module.nontrivial_of_finrank_pos hfinEucl
  have hsphereB : 0 < sphereB := by
    dsimp only [sphereB]
    exact ENNReal.toReal_pos
      (Measure.measure_univ_pos.mpr
        (Measure.toSphere_ne_zero
          (volume : Measure (EuclideanSpace Real (Fin n))))).ne'
      (measure_lt_top _ _).ne
  have hsphereP : 0 ≤ sphereP := ENNReal.toReal_nonneg
  have hspheres : 0 < sphereB + sphereP :=
    add_pos_of_pos_of_nonneg hsphereB hsphereP
  have hden : 0 < den := by
    dsimp only [den]
    exact mul_pos hspheres hmodelTwo
  have hρ : 0 < ρ := by
    dsimp only [ρ]
    exact div_pos (mul_pos (by positivity) hlow) hden
  refine
    { ρ := ρ
      pos := hρ
      bound := ?_ }
  intro i
  refine ⟨hρ, ?_⟩
  intro hcomplete'
  let : TopologicalSpace (Y.obj i).M := (Y.obj i).topology
  let : ChartedSpace H (Y.obj i).M := (Y.obj i).charted
  let : IsManifold I ∞ (Y.obj i).M := (Y.obj i).smooth
  let : IsManifold I 1 (Y.obj i).M :=
    IsManifold.of_le (I := I) (M := (Y.obj i).M) (n := ∞) (by decide)
  let : T2Space (Y.obj i).M := (Y.obj i).t2
  let : SigmaCompactSpace (Y.obj i).M := (Y.obj i).sigmaCompact
  let : T2Space (TangentBundle I (Y.obj i).M) :=
    (Y.obj i).t2TangentBundle
  let : RiemannianBundle
      (fun y : (Y.obj i).M => TangentSpace I y) :=
    (Y.obj i).riemBundle (I := I)
  let : (y : (Y.obj i).M) →
      InnerProductSpace Real (TangentSpace I y) :=
    (Y.obj i).riemInner (I := I)
  let : IsContinuousRiemannianBundle E
      (fun y : (Y.obj i).M => TangentSpace I y) :=
    (Y.obj i).riemBundle_cont (I := I)
  let : EMetricSpace (Y.obj i).M :=
    (Y.obj i).emetricSpace (I := I)
  have : IsRiemannianManifold I (Y.obj i).M := ⟨fun _ _ => rfl⟩
  let : CompleteSpace (Y.obj i).M :=
    MetricComplete.complete (I := I) (Y.obj i) hcomplete'
  let : ConnectedSpace (Y.obj i).M := hconn i
  let hEnorm : ∀ (y : (Y.obj i).M) (w : TangentSpace I y),
      ‖w‖ₑ =
        ENNReal.ofReal (Real.sqrt ((Y.obj i).metric.inner y w w)) := by
    intro y w
    with_unfolding_all
      exact tensor0SBundle_enorm_eq_riemannianBundle_enorm
        (I := I) (Y.obj i).metric y w
  have hsCtrl : s < rCtrl := by
    have hsle : s ≤ rCtrl / 10 := min_le_left _ _
    nlinarith
  have hfiveCtrl : 5 * s < rCtrl := by
    have hsle : s ≤ rCtrl / 10 := min_le_left _ _
    nlinarith
  have hsPi : s ≤ Real.pi / (10 * Real.sqrt K) :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hfivePi : 5 * s ≤ Real.pi / Real.sqrt K := by
    calc
      5 * s ≤ 5 * (Real.pi / (10 * Real.sqrt K)) := by
        gcongr
      _ = Real.pi / (2 * Real.sqrt K) := by
        field_simp
        ring
      _ ≤ Real.pi / Real.sqrt K := by
        have hpos : 0 < Real.pi / Real.sqrt K :=
          div_pos Real.pi_pos hsqrtK
        have heq :
            Real.pi / (2 * Real.sqrt K) =
              (1 / 2 : Real) * (Real.pi / Real.sqrt K) := by
          field_simp
        rw [heq]
        nlinarith
  have hsLarge : s ≤ V.radius := by
    have hsle : s ≤ V.radius / 2 :=
      (min_le_right _ _).trans (min_le_right _ _)
    linarith
  have hmetricCtrl :
      ∀ z ∈ Metric.ball (0 : E) rCtrl, ∀ v : E,
        (1 / 2 : Real) * ‖v‖ ^ 2 ≤
            intrFrameMetric (I := I) (Y.obj i).metric hEnorm
              (Y.obj i).basepoint z v v ∧
          intrFrameMetric (I := I) (Y.obj i).metric hEnorm
              (Y.obj i).basepoint z v v ≤
            2 * ‖v‖ ^ 2 :=
    (hcontrol i (Y.obj i).basepoint).1
  have hlocalFive :
      IsLocalDiffeomorphOn (modelWithCornersSelf Real E) I ∞
        (intrinsicFramedExp (I := I) (Y.obj i).metric hEnorm
          (Y.obj i).basepoint)
        (Metric.ball (0 : E) (5 * s)) := by
    intro z
    exact (hcontrol i (Y.obj i).basepoint).2
      ⟨z.1, Metric.ball_subset_ball hfiveCtrl.le z.2⟩
  have hRm :
      Rm04GlobalBound (I := I) (M := (Y.obj i).M)
        (Y.obj i).metric K := by
    intro y
    exact (rm04Bound_of_seq (I := I) hgeom i y).trans (by
      dsimp only [K]
      linarith)
  have hRic :
      RicciBoundedBelow (I := I) (Y.obj i).metric
        (-(((n - 1 : Nat) : Real) * q ^ 2)) := by
    by_cases hn1 : n = 1
    · have hzero : ((n - 1 : Nat) : Real) * q ^ 2 = 0 := by
        rw [hn1]
        norm_num
      rw [hzero, neg_zero]
      exact ricci_dim1_bddBelow (by simpa only [n] using hn1)
        (Y.obj i).metric
    · have hn2 : 2 ≤ n := by omega
      have hsrc :
          RicciBoundedBelow (I := I) (Y.obj i).metric
            (-((n : Real) ^ 2 * hgeom.C 0)) :=
        ricciLower_of_rm (I := I) (Y.obj i).metric
          (by
            simpa only [n,
              Geometry.Riemannian.VolumeComparison.Rm04GlobalBound] using
              rm04Bound_of_seq (I := I) hgeom i)
      have hq2 : q ^ 2 = (n : Real) ^ 2 * K := by
        dsimp only [q]
        rw [mul_pow, Real.sq_sqrt hK.le]
      intro y v
      have hinner :
          0 ≤ (Y.obj i).metric.inner y v v := by
        rcases eq_or_ne v 0 with hv | hv
        · subst hv
          simp
        · exact ((Y.obj i).metric.pos y v hv).le
      have hkappa :
          -(((n - 1 : Nat) : Real) * q ^ 2) ≤
            -((n : Real) ^ 2 * hgeom.C 0) := by
        rw [neg_le_neg_iff, hq2]
        have hone : (1 : Real) ≤ ((n - 1 : Nat) : Real) := by
          have : 1 ≤ n - 1 := by omega
          exact_mod_cast this
        dsimp only [K]
        nlinarith [sq_nonneg (n : Real)]
      exact
        (mul_le_mul_of_nonneg_right hkappa hinner).trans (hsrc y v)
  have htwoCtrl : 2 * s < rCtrl := by
    nlinarith
  have hno :
      ∀ z, z ∈ Metric.ball (0 : E) (2 * s) → z ≠ 0 →
        ∀ t, t ∈ Ioo (0 : Real) 1 →
          ¬ IsConjVec (I := I) (Y.obj i).metric hEnorm
            (Y.obj i).basepoint
            ((t • normalFrame (I := I) (Y.obj i).metric
              (Y.obj i).basepoint z :
              TangentSpace I (Y.obj i).basepoint) : E) := by
    intro z hz hz0 t ht
    have htz : t • z ∈ Metric.ball (0 : E) rCtrl := by
      rw [Metric.mem_ball, dist_zero_right] at hz ⊢
      rw [norm_smul, Real.norm_of_nonneg ht.1.le]
      calc
        t * ‖z‖ < 1 * ‖z‖ :=
          mul_lt_mul_of_pos_right ht.2 (norm_pos_iff.mpr hz0)
        _ = ‖z‖ := one_mul _
        _ < 2 * s := hz
        _ < rCtrl := htwoCtrl
    have hraw :=
      intrFrame_not_conj (I := I) (Y.obj i).metric hEnorm
        (Y.obj i).basepoint (t • z) (c := (1 / 2 : Real)) (by norm_num)
        (fun v => (hmetricCtrl (t • z) htz v).1)
    simpa only [map_smul] using hraw
  let Vx : ENNReal :=
    riemannianVolumeMeasure (I := I) (M := (Y.obj i).M)
      (Y.obj i).metric
      {y : (Y.obj i).M |
        riemannianEDist I (Y.obj i).basepoint y <
          ENNReal.ofReal s}
  let P : ENNReal :=
    intrPullVol (I := I) (Y.obj i).metric hEnorm
      (Y.obj i).basepoint (2 * s)
  have hVxRaw :
      Vx ≤
        (volume : Measure
          (EuclideanSpace Real (Fin n))).toSphere Set.univ *
            ENNReal.ofReal modelTwo := by
    calc
      Vx ≤
          riemannianVolumeMeasure (I := I) (M := (Y.obj i).M)
            (Y.obj i).metric
            {y : (Y.obj i).M |
              riemannianEDist I (Y.obj i).basepoint y <
                ENNReal.ofReal (2 * s)} := by
        exact measure_mono
          (edistBall_mono (I := I) (Y.obj i).basepoint
            (by linarith : s ≤ 2 * s))
      _ ≤
          (volume : Measure
            (EuclideanSpace Real (Fin n))).toSphere Set.univ *
              ENNReal.ofReal modelTwo := by
        simpa only [modelTwo, d, n] using
          (segBall_vol_le_euclidean (I := I) (Y.obj i).metric hEnorm
            (Y.obj i).basepoint hq (by positivity : 0 < 2 * s) hRic)
  have hPraw :
      P ≤ (volume : Measure E).toSphere Set.univ *
        ENNReal.ofReal modelTwo := by
    simpa only [P, modelTwo, d, n] using
      (intrPullVol_le_hyp (I := I) (Y.obj i).metric hEnorm
        (Y.obj i).basepoint hq (by positivity : 0 < 2 * s) hno hRic)
  have hsphereBEq :
      (volume : Measure
        (EuclideanSpace Real (Fin n))).toSphere Set.univ =
          ENNReal.ofReal sphereB :=
    (ENNReal.ofReal_toReal (measure_lt_top _ _).ne).symm
  have hspherePEq :
      (volume : Measure E).toSphere Set.univ =
        ENNReal.ofReal sphereP :=
    (ENNReal.ofReal_toReal (measure_lt_top _ _).ne).symm
  have hVxUpper :
      Vx ≤ ENNReal.ofReal sphereB * ENNReal.ofReal modelTwo := by
    simpa only [hsphereBEq] using hVxRaw
  have hPUpper :
      P ≤ ENNReal.ofReal sphereP * ENNReal.ofReal modelTwo := by
    simpa only [hspherePEq] using hPraw
  have hDen : Vx + P ≤ ENNReal.ofReal den := by
    calc
      Vx + P ≤
          ENNReal.ofReal sphereB * ENNReal.ofReal modelTwo +
            ENNReal.ofReal sphereP * ENNReal.ofReal modelTwo :=
        add_le_add hVxUpper hPUpper
      _ = ENNReal.ofReal ((sphereB + sphereP) * modelTwo) :=
        ofReal_add_mul hsphereB.le hsphereP
      _ = ENNReal.ofReal den := rfl
  have hVxFin : Vx ≠ ⊤ :=
    ne_top_of_le_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
      hVxUpper
  let Vlarge : ENNReal :=
    riemannianVolumeMeasure (I := I) (M := (Y.obj i).M)
      (Y.obj i).metric
      {y : (Y.obj i).M |
        riemannianEDist I (Y.obj i).basepoint y <
          ENNReal.ofReal V.radius}
  have hrel :
      Vlarge * ENNReal.ofReal modelSmall ≤
        ENNReal.ofReal modelLarge * Vx := by
    simpa only [Vlarge, Vx, modelSmall, modelLarge, d, n] using
      (segBall_vol_rel (I := I) (Y.obj i).metric hEnorm
        (Y.obj i).basepoint hq hs hsLarge hRic)
  have hNC :
      ENNReal.ofReal V.kappa *
          ENNReal.ofReal V.radius ^ n ≤ Vlarge := by
    have hraw := (hvol.noncollapsed i).2
    convert hraw using 1 <;>
      with_unfolding_all
        rfl
  have hcomb :
      (ENNReal.ofReal V.kappa * ENNReal.ofReal V.radius ^ n) *
          ENNReal.ofReal modelSmall ≤
        ENNReal.ofReal modelLarge * Vx := by
    calc
      (ENNReal.ofReal V.kappa * ENNReal.ofReal V.radius ^ n) *
            ENNReal.ofReal modelSmall
          ≤ Vlarge * ENNReal.ofReal modelSmall := by
        gcongr
      _ ≤ ENNReal.ofReal modelLarge * Vx := hrel
  have hrightFin :
      ENNReal.ofReal modelLarge * Vx ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hVxFin
  have hreal :=
    (ENNReal.toReal_le_toReal
      (ENNReal.mul_ne_top
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
          (ENNReal.pow_ne_top ENNReal.ofReal_ne_top))
        ENNReal.ofReal_ne_top)
      hrightFin).mpr hcomb
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_pow,
    ENNReal.toReal_ofReal V.kappa_pos.le,
    ENNReal.toReal_ofReal V.radius_pos.le,
    ENNReal.toReal_ofReal hmodelSmall.le,
    ENNReal.toReal_ofReal hmodelLarge.le] at hreal
  have hlowReal : low ≤ Vx.toReal := by
    dsimp only [low]
    rw [div_le_iff₀ hmodelLarge]
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hreal
  have hVxLow : ENNReal.ofReal low ≤ Vx :=
    (ENNReal.ofReal_le_iff_le_toReal hVxFin).2 hlowReal
  have hcgt :
      ENNReal.ofReal (s / 2) * Vx / (Vx + P) ≤
        intrInjRadius (I := I) (Y.obj i).metric hEnorm
          (Y.obj i).basepoint := by
    simpa only [Vx, P, two_mul] using
      (intrInj_ge_cgt (I := I) (K := K) (R := 5 * s)
        (r₀ := s) (s := s) (Y.obj i).metric hEnorm
        (Y.obj i).basepoint hK (by positivity) hfivePi hRm hlocalFive
        hs hs (cgt_fit hs) (cgt_quarter hs))
  have hratio :
      ENNReal.ofReal ρ ≤
        ENNReal.ofReal (s / 2) * Vx / (Vx + P) := by
    dsimp only [ρ]
    rw [ENNReal.ofReal_div_of_pos hden,
      ENNReal.ofReal_mul (by positivity : 0 ≤ s / 2)]
    exact ENNReal.div_le_div
      (by
        gcongr)
      hDen
  simpa only [Y, PointedRiemannianManifold.intrInjRadius] using
    hratio.trans hcgt

end HCGCompactness
end DifferentialGeometry
