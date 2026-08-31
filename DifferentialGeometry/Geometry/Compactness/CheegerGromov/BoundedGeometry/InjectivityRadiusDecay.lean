import DifferentialGeometry.Geometry.Comparison.CheegerGromovTaylor.InjectivityRadius


import DifferentialGeometry.Geometry.Comparison.Volume.IntrinsicBallVolume
import DifferentialGeometry.Geometry.Comparison.Volume.SegmentBallEuclideanUpper
import DifferentialGeometry.Geometry.Comparison.Volume.SegmentCount
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.BoundedGeometry.NormalCoordinates
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Covering.VolumeOverlap

set_option autoImplicit false

noncomputable section

open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry
namespace HCGCompactness

open Bundle Manifold MeasureTheory Metric Set
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.BonnetMyers
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]

private lemma hyp_shift_le
    (d : Nat) {q s D : Real} (hq : 0 ≤ q) (hs : 0 < s) (hD : 0 ≤ D) :
    hypRadVol q d (D + s) ≤
      (2 ^ (d + 1) * Real.exp (q * (d : Real) * s)) *
        Real.exp ((q * (d : Real) + (d + 1 : Nat) / s) * D) *
          hypRadVol q d s := by
  have hsR : s ≤ D + s := by linarith
  have hratio := hypRadVol_ratio_le d hq hs hsR
  have hsdiv : 0 ≤ D / s := div_nonneg hD hs.le
  have hone :
      1 + D / s ≤ Real.exp (D / s) := by
    simpa only [add_comm] using Real.add_one_le_exp (D / s)
  have hfrac :
      (D + s) / (s / 2) = 2 * (1 + D / s) := by
    field_simp
    ring
  have hbase :
      0 ≤ 2 * (1 + D / s) := by positivity
  have hpow :
      ((D + s) / (s / 2)) ^ (d + 1) ≤
        (2 * Real.exp (D / s)) ^ (d + 1) := by
    rw [hfrac]
    exact pow_le_pow_left₀ hbase
      (mul_le_mul_of_nonneg_left hone (by norm_num)) _
  calc
    hypRadVol q d (D + s)
        ≤ Real.exp (q * (d : Real) * (D + s)) *
            ((D + s) / (s / 2)) ^ (d + 1) *
              hypRadVol q d s := hratio
    _ ≤ Real.exp (q * (d : Real) * (D + s)) *
            (2 * Real.exp (D / s)) ^ (d + 1) *
              hypRadVol q d s := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hpow (Real.exp_pos _).le)
            ((pow_nonneg (by positivity : 0 ≤ s / 2) _).trans
              (hypRadVol_ge d hq hs))
    _ = (2 ^ (d + 1) * Real.exp (q * (d : Real) * s)) *
          Real.exp ((q * (d : Real) + (d + 1 : Nat) / s) * D) *
            hypRadVol q d s := by
          rw [mul_pow, ← Real.exp_nat_mul (D / s) (d + 1)]
          calc
            Real.exp (q * (d : Real) * (D + s)) *
                  (2 ^ (d + 1) *
                    Real.exp ((d + 1 : Nat) * (D / s))) *
                  hypRadVol q d s =
                2 ^ (d + 1) *
                  (Real.exp (q * (d : Real) * (D + s)) *
                    Real.exp ((d + 1 : Nat) * (D / s))) *
                  hypRadVol q d s := by ring
            _ = 2 ^ (d + 1) *
                  Real.exp
                    (q * (d : Real) * (D + s) +
                      (d + 1 : Nat) * (D / s)) *
                  hypRadVol q d s := by
                rw [Real.exp_add]
            _ = 2 ^ (d + 1) *
                  Real.exp
                    (q * (d : Real) * s +
                      (q * (d : Real) + (d + 1 : Nat) / s) * D) *
                  hypRadVol q d s := by
                congr 3
                ring
            _ = (2 ^ (d + 1) * Real.exp (q * (d : Real) * s)) *
                  Real.exp
                    ((q * (d : Real) + (d + 1 : Nat) / s) * D) *
                  hypRadVol q d s := by
                rw [Real.exp_add]
                ring

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

private lemma shift_exp_mul_decay
    {shift lower s C D : Real} (hshift : shift ≠ 0) :
    (shift * Real.exp (C * D)) *
        ((lower / shift) * s * Real.exp (-C * D)) = lower * s := by
  field_simp
  calc
    Real.exp (C * D) * lower * s * Real.exp (-(C * D)) =
        lower * s * (Real.exp (C * D) * Real.exp (-(C * D))) := by ring
    _ = lower * s := by
      rw [← Real.exp_add]
      ring_nf
      norm_num

private lemma decay_ratio_eq
    {lower tau b shift spheres upper e : Real} (n : Nat)
    (hshift : shift ≠ 0) (hspheres : spheres ≠ 0)
    (hupper : upper ≠ 0) (htau : tau ≠ 0) (hb : b ≠ 0) :
    ((tau * b) / 2) *
          ((lower / shift) * (tau * b) ^ n * e) /
        (spheres * (upper * (tau * b) ^ n)) =
      (lower * tau / (2 * shift * spheres * upper)) * b * e := by
  field_simp

noncomputable def riemSeqDist
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I)) :
    PointedSeqDistance (I := I) X :=
  fun k x y =>
    letI : EMetricSpace (X.obj k).M := (X.obj k).emetricSpace (I := I)
    (edist x y).toReal

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
def injDecayOfBg
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k : Nat,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M)
    (bg : SeqBoundedGeometry (I := I) X)
    (base : BaseInjBound (I := I) X) :
    InjRadiusDecayInput (I := I) X := by
  classical
  letI : MeasurableSpace E := borel E
  letI : BorelSpace E := ⟨rfl⟩
  let hctrl :=
    exists_intr_control (I := I) X hcomplete hconn bg
  let rCtrl : Real := hctrl.choose
  have hrCtrl : 0 < rCtrl := hctrl.choose_spec.1
  have hcontrol := hctrl.choose_spec.2
  let n : Nat := Module.finrank Real E
  let d : Nat := n - 1
  let b : Real := min base.ρ 1
  let K : Real := bg.C 0 + 1
  let q : Real := (n : Real) * Real.sqrt (bg.C 0)
  let tau : Real :=
    min (rCtrl / 10)
      (min (Real.pi / (10 * Real.sqrt K)) (1 / 2))
  let s : Real := tau * b
  let dens : Real :=
    Real.sqrt
      (((1 / 2 : Real) * modelCoeffMin (E := E) ^ 2) ^ n)
  let unitVol : Real :=
    ((modelHaar (E := E)) (Metric.ball (0 : E) 1)).toReal
  let lowerC : Real := dens * unitVol
  let shiftC : Real :=
    2 ^ n * Real.exp (q * (d : Real) * s)
  let sphereB : Real :=
    (((volume : Measure
      (EuclideanSpace Real (Fin n))).toSphere Set.univ)).toReal
  let sphereP : Real :=
    (((volume : Measure E).toSphere Set.univ)).toReal
  let upperC : Real :=
    2 ^ n * Real.exp (q * (d : Real) * (2 * s))
  let a : Real :=
    lowerC * tau /
      (2 * shiftC * (sphereB + sphereP) * upperC)
  let C : Real := q * (d : Real) + (n : Real) / s
  have hn : 0 < n := by
    exact Nat.pos_of_ne_zero (NeZero.ne (Module.finrank Real E))
  have hb : 0 < b := lt_min base.pos one_pos
  have hb1 : b ≤ 1 := min_le_right _ _
  have hC0 : 0 ≤ bg.C 0 := bg.nonneg 0
  have hK : 0 < K := by
    dsimp only [K]
    linarith
  have hsqrtK : 0 < Real.sqrt K := Real.sqrt_pos.mpr hK
  have htau : 0 < tau := by
    dsimp only [tau]
    apply lt_min
    · positivity
    · apply lt_min
      · exact div_pos Real.pi_pos (mul_pos (by norm_num) hsqrtK)
      · norm_num
  have hs : 0 < s := mul_pos htau hb
  have hq : 0 ≤ q := by
    exact mul_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _)
  have hdens : 0 < dens := by
    dsimp only [dens]
    apply Real.sqrt_pos.mpr
    apply pow_pos
    exact mul_pos (by norm_num) (sq_pos_of_pos (modelCoeffMin_pos (E := E)))
  have hunit : 0 < unitVol := by
    dsimp only [unitVol]
    exact ENNReal.toReal_pos
      (Metric.measure_ball_pos (modelHaar (E := E)) (0 : E) one_pos).ne'
      measure_ball_lt_top.ne
  have hlower : 0 < lowerC := by
    exact mul_pos hdens hunit
  have hshift : 0 < shiftC := by
    exact mul_pos (pow_pos (by norm_num) _) (Real.exp_pos _)
  letI : Nontrivial E :=
    Module.nontrivial_of_finrank_pos
      (Nat.pos_of_ne_zero (NeZero.ne (Module.finrank Real E)))
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
          (volume : Measure
            (EuclideanSpace Real (Fin n))))).ne'
      (measure_lt_top _ _).ne
  have hsphereP : 0 ≤ sphereP := by
    exact ENNReal.toReal_nonneg
  have hspheres : 0 < sphereB + sphereP :=
    add_pos_of_pos_of_nonneg hsphereB hsphereP
  have hupper : 0 < upperC := by
    exact mul_pos (pow_pos (by norm_num) _) (Real.exp_pos _)
  have ha : 0 < a := by
    dsimp only [a]
    positivity
  have hC : 0 ≤ C := by
    dsimp only [C]
    exact add_nonneg (mul_nonneg hq (Nat.cast_nonneg _))
      (div_nonneg (Nat.cast_nonneg _) hs.le)
  refine
    { baseInj := base
      dist := riemSeqDist (I := I) X
      a := a
      C := C
      a_pos := ha
      C_nonneg := hC
      decay := ?_ }
  intro k x
  let Y := X.obj k
  have hprofile :
      0 < a * b ^ n *
        Real.exp (-C * riemSeqDist (I := I) X k x Y.basepoint) :=
    mul_pos (mul_pos ha (pow_pos hb _)) (Real.exp_pos _)
  refine ⟨by simpa only [n, b] using hprofile, ?_⟩
  intro hcomplete'
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : IsManifold I 1 Y.M :=
    IsManifold.of_le (I := I) (M := Y.M) (n := ∞) (by decide)
  let : SigmaCompactSpace Y.M := Y.sigmaCompact
  let : T2Space Y.M := Y.t2
  let : T2Space (TangentBundle I Y.M) :=
    Y.t2TangentBundle
  let : TopologicalSpace.MetrizableSpace Y.M :=
    Manifold.metrizableSpace I Y.M
  let : T3Space Y.M := inferInstance
  let : RiemannianBundle
      (fun y : Y.M => TangentSpace I y) :=
    Y.riemBundle (I := I)
  let : (y : Y.M) →
      InnerProductSpace Real (TangentSpace I y) :=
    Y.riemInner (I := I)
  let : IsContinuousRiemannianBundle E
      (fun y : Y.M => TangentSpace I y) :=
    Y.riemBundle_cont (I := I)
  let : EMetricSpace Y.M :=
    Y.emetricSpace (I := I)
  have : IsRiemannianManifold I Y.M :=
    ⟨fun _ _ => rfl⟩
  let : CompleteSpace Y.M :=
    MetricComplete.complete (I := I) Y hcomplete'
  let : ConnectedSpace Y.M := hconn k
  let hEnorm : ∀ (y : Y.M) (w : TangentSpace I y),
      ‖w‖ₑ =
        ENNReal.ofReal (Real.sqrt (Y.metric.inner y w w)) := by
    intro y w
    with_unfolding_all
      exact tensor0SBundle_enorm_eq_riemannianBundle_enorm
        (I := I) Y.metric y w
  have htauCtrl : tau ≤ rCtrl / 10 := by
    exact min_le_left _ _
  have htauPi :
      tau ≤ Real.pi / (10 * Real.sqrt K) := by
    exact (min_le_right _ _).trans (min_le_left _ _)
  have htauHalf : tau ≤ 1 / 2 := by
    exact (min_le_right _ _).trans (min_le_right _ _)
  have hsTau : s ≤ tau := by
    dsimp only [s]
    simpa only [mul_one] using
      (mul_le_mul_of_nonneg_left hb1 htau.le)
  have hsRho : s < base.ρ := by
    have hsb : s ≤ (1 / 2 : Real) * b := by
      dsimp only [s]
      exact mul_le_mul_of_nonneg_right htauHalf hb.le
    have hbRho : b ≤ base.ρ := min_le_left _ _
    linarith
  have hfiveCtrl : 5 * s < rCtrl := by
    have hfiveTau : 5 * tau ≤ rCtrl / 2 := by
      calc
        5 * tau ≤ 5 * (rCtrl / 10) :=
          mul_le_mul_of_nonneg_left htauCtrl (by norm_num)
        _ = rCtrl / 2 := by ring
    linarith
  have hsCtrl : s < rCtrl := by
    linarith
  have hpiHalf :
      Real.pi / (2 * Real.sqrt K) ≤
        Real.pi / Real.sqrt K := by
    have hpiDiv : 0 < Real.pi / Real.sqrt K :=
      div_pos Real.pi_pos hsqrtK
    have heq :
        Real.pi / (2 * Real.sqrt K) =
          (1 / 2 : Real) * (Real.pi / Real.sqrt K) := by
      field_simp
    rw [heq]
    exact mul_le_of_le_one_left hpiDiv.le (by norm_num)
  have hfivePi :
      5 * s ≤ Real.pi / Real.sqrt K := by
    calc
      5 * s ≤ 5 * tau :=
        mul_le_mul_of_nonneg_left hsTau (by norm_num)
      _ ≤ Real.pi / (2 * Real.sqrt K) := by
        calc
          5 * tau ≤ 5 * (Real.pi / (10 * Real.sqrt K)) :=
            mul_le_mul_of_nonneg_left htauPi (by norm_num)
          _ = Real.pi / (2 * Real.sqrt K) := by
            field_simp
            ring
      _ ≤ Real.pi / Real.sqrt K := hpiHalf
  have hmetricCtrl :
      ∀ z ∈ Metric.ball (0 : E) rCtrl, ∀ v : E,
        (1 / 2 : Real) * ‖v‖ ^ 2 ≤
            intrFrameMetric (I := I) Y.metric hEnorm x z v v ∧
          intrFrameMetric (I := I) Y.metric hEnorm x z v v ≤
            2 * ‖v‖ ^ 2 := by
    exact (hcontrol k x).1
  have hlocalCtrl :
      IsLocalDiffeomorphOn (modelWithCornersSelf Real E) I ∞
        (intrinsicFramedExp (I := I) Y.metric hEnorm x)
        (Metric.ball (0 : E) rCtrl) := by
    exact (hcontrol k x).2
  have hlocalS :
      IsLocalDiffeomorphOn (modelWithCornersSelf Real E) I ∞
        (intrinsicFramedExp (I := I) Y.metric hEnorm
          Y.basepoint)
        (Metric.ball (0 : E) s) := by
    intro z
    exact (hcontrol k Y.basepoint).2
      ⟨z.1, Metric.ball_subset_ball hsCtrl.le z.2⟩
  have hinjS :
      InjOn
        (intrinsicFramedExp (I := I) Y.metric hEnorm
          Y.basepoint)
        (Metric.ball (0 : E) s) := by
    exact (base.bound k).injOn_ball hcomplete' hsRho
  obtain ⟨baseChart⟩ :=
    exists_intrinsic_ball_chart (I := I) Y.metric hEnorm
      Y.basepoint hlocalS hinjS
  have hmetricS :
      ∀ z ∈ Metric.ball (0 : E) s, ∀ v : E,
        (1 / 2 : Real) * ‖v‖ ^ 2 ≤
            intrFrameMetric (I := I) Y.metric hEnorm
              Y.basepoint z v v ∧
          intrFrameMetric (I := I) Y.metric hEnorm
              Y.basepoint z v v ≤
            2 * ‖v‖ ^ 2 := by
    intro z hz v
    apply (hcontrol k Y.basepoint).1 z
    exact Metric.ball_subset_ball hsCtrl.le hz
  let V0 : ENNReal :=
    riemannianVolumeMeasure (I := I) (M := Y.M)
      Y.metric
      {y : Y.M |
        riemannianEDist I Y.basepoint y <
          ENNReal.ofReal s}
  have hV0raw :
      ENNReal.ofReal dens *
          (modelHaar (E := E)) (Metric.ball (0 : E) s) ≤ V0 := by
    simpa only [dens, V0, smallNormalBall] using
      (intrBall_vol_ge (I := I) Y.metric hEnorm
        Y.basepoint hs baseChart hmetricS)
  have hunitEq :
      (modelHaar (E := E)) (Metric.ball (0 : E) 1) =
        ENNReal.ofReal unitVol := by
    exact (ENNReal.ofReal_toReal measure_ball_lt_top.ne).symm
  have hspow : 0 ≤ s ^ n := pow_nonneg hs.le _
  have hV0 :
      ENNReal.ofReal (lowerC * s ^ n) ≤ V0 := by
    calc
      ENNReal.ofReal (lowerC * s ^ n) =
          (ENNReal.ofReal dens * ENNReal.ofReal unitVol) *
            ENNReal.ofReal (s ^ n) := by
        rw [ENNReal.ofReal_mul hlower.le,
          ENNReal.ofReal_mul hdens.le]
      _ = ENNReal.ofReal dens *
          (ENNReal.ofReal (s ^ n) *
            (modelHaar (E := E)) (Metric.ball (0 : E) 1)) := by
        rw [hunitEq]
        ac_rfl
      _ = ENNReal.ofReal dens *
          (modelHaar (E := E)) (Metric.ball (0 : E) s) := by
        rw [modelHaar_ball (E := E) hs]
      _ ≤ V0 := hV0raw
  let D : Real :=
    riemSeqDist (I := I) X k x Y.basepoint
  have hD : 0 ≤ D := by
    exact ENNReal.toReal_nonneg
  have hedistTop :
      edist x Y.basepoint ≠ (⊤ : ENNReal) := by
    rw [IsRiemannianManifold.out (I := I)]
    exact riemannianEDist_ne_top (I := I) x Y.basepoint
  have hdist :
      riemannianEDist I Y.basepoint x =
        ENNReal.ofReal D := by
    rw [← IsRiemannianManifold.out (I := I)]
    dsimp only [D, riemSeqDist]
    rw [edist_comm]
    exact (ENNReal.ofReal_toReal hedistTop).symm
  let Vx : ENNReal :=
    riemannianVolumeMeasure (I := I) (M := Y.M)
      Y.metric
      {y : Y.M |
        riemannianEDist I x y < ENNReal.ofReal s}
  let VxR : ENNReal :=
    riemannianVolumeMeasure (I := I) (M := Y.M)
      Y.metric
      {y : Y.M |
        riemannianEDist I x y < ENNReal.ofReal (D + s)}
  have hV0shift : V0 ≤ VxR := by
    exact measure_mono
      (edistBall_shift (I := I) (a := Y.basepoint) (b := x)
        (t := D) (ρ := s) hdist.le hD hs.le)
  have hRic :
      RicciBoundedBelow (I := I) Y.metric
        (-(((n - 1 : Nat) : Real) * q ^ 2)) := by
    by_cases hn1 : n = 1
    · have hzero : ((n - 1 : Nat) : Real) * q ^ 2 = 0 := by
        rw [hn1]
        norm_num
      rw [hzero, neg_zero]
      exact ricci_dim1_bddBelow (by simpa only [n] using hn1)
        Y.metric
    · have hn2 : 2 ≤ n := by
        omega
      have hsrc :
          RicciBoundedBelow (I := I) Y.metric
            (-((n : Real) ^ 2 * bg.C 0)) :=
        ricciLower_of_rm (I := I) Y.metric
          (by
            simpa only [n,
              Geometry.Riemannian.VolumeComparison.Rm04GlobalBound] using
              rm04Bound_of_seq (I := I) bg k)
      have hq2 : q ^ 2 = (n : Real) ^ 2 * bg.C 0 := by
        dsimp only [q]
        rw [mul_pow, Real.sq_sqrt hC0]
      intro y v
      have hinner :
          0 ≤ Y.metric.inner y v v := by
        rcases eq_or_ne v 0 with hv | hv
        · subst hv
          simp
        · exact (Y.metric.pos y v hv).le
      have hkappa :
          -(((n - 1 : Nat) : Real) * q ^ 2) ≤
            -((n : Real) ^ 2 * bg.C 0) := by
        rw [neg_le_neg_iff, hq2]
        have hone : (1 : Real) ≤ ((n - 1 : Nat) : Real) := by
          have : 1 ≤ n - 1 := by omega
          exact_mod_cast this
        have hbase : 0 ≤ (n : Real) ^ 2 * bg.C 0 :=
          mul_nonneg (sq_nonneg _) hC0
        calc
          (n : Real) ^ 2 * bg.C 0 = 1 * ((n : Real) ^ 2 * bg.C 0) := by
            rw [one_mul]
          _ ≤ ((n - 1 : Nat) : Real) * ((n : Real) ^ 2 * bg.C 0) :=
            mul_le_mul_of_nonneg_right hone hbase
      calc
        -(((n - 1 : Nat) : Real) * q ^ 2) *
              Y.metric.inner y v v
            ≤ -((n : Real) ^ 2 * bg.C 0) *
                Y.metric.inner y v v :=
          mul_le_mul_of_nonneg_right hkappa hinner
        _ ≤ ricciTensor (I := I) Y.metric y v v := hsrc y v
  have hdSucc : d + 1 = n := by
    dsimp only [d]
    omega
  have hrel :
      VxR * ENNReal.ofReal (hypRadVol q d s) ≤
        ENNReal.ofReal (hypRadVol q d (D + s)) * Vx := by
    simpa only [VxR, Vx, d, n] using
      (segBall_vol_rel (I := I) Y.metric hEnorm x hq hs
        (by linarith : s ≤ D + s) hRic)
  have hmodelShift :
      hypRadVol q d (D + s) ≤
        (shiftC * Real.exp (C * D)) * hypRadVol q d s := by
    simpa only [shiftC, C, hdSucc, mul_assoc] using
      (hyp_shift_le d hq hs hD)
  have hcoeffNonneg :
      0 ≤ shiftC * Real.exp (C * D) :=
    mul_nonneg hshift.le (Real.exp_pos _).le
  have hmodelShiftE :
      ENNReal.ofReal (hypRadVol q d (D + s)) ≤
        ENNReal.ofReal (shiftC * Real.exp (C * D)) *
          ENNReal.ofReal (hypRadVol q d s) := by
    calc
      ENNReal.ofReal (hypRadVol q d (D + s))
          ≤ ENNReal.ofReal
              ((shiftC * Real.exp (C * D)) * hypRadVol q d s) :=
        ENNReal.ofReal_le_ofReal hmodelShift
      _ = ENNReal.ofReal (shiftC * Real.exp (C * D)) *
            ENNReal.ofReal (hypRadVol q d s) := by
        rw [ENNReal.ofReal_mul hcoeffNonneg]
  have hmodelSPos : 0 < hypRadVol q d s :=
    hypRadVol_pos hq hs
  have hmodelS0 :
      ENNReal.ofReal (hypRadVol q d s) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr hmodelSPos
  have hVxRel :
      VxR ≤ ENNReal.ofReal (shiftC * Real.exp (C * D)) * Vx := by
    apply
      (ENNReal.mul_le_mul_iff_left hmodelS0 ENNReal.ofReal_ne_top).mp
    calc
      VxR * ENNReal.ofReal (hypRadVol q d s)
          ≤ ENNReal.ofReal (hypRadVol q d (D + s)) * Vx := hrel
      _ ≤ (ENNReal.ofReal (shiftC * Real.exp (C * D)) *
              ENNReal.ofReal (hypRadVol q d s)) * Vx := by
        gcongr
      _ = (ENNReal.ofReal (shiftC * Real.exp (C * D)) * Vx) *
            ENNReal.ofReal (hypRadVol q d s) := by
        ac_rfl
  let low : Real :=
    (lowerC / shiftC) * s ^ n * Real.exp (-C * D)
  have hlow : 0 < low := by
    dsimp only [low]
    exact mul_pos
      (mul_pos (div_pos hlower hshift) (pow_pos hs _))
      (Real.exp_pos _)
  have hlowMul :
      (shiftC * Real.exp (C * D)) * low =
        lowerC * s ^ n := by
    dsimp only [low]
    exact shift_exp_mul_decay hshift.ne'
  have hVxLow : ENNReal.ofReal low ≤ Vx := by
    apply
      (ENNReal.mul_le_mul_iff_right
        (ENNReal.ofReal_ne_zero_iff.mpr
          (mul_pos hshift (Real.exp_pos _)))
        ENNReal.ofReal_ne_top).mp
    rw [← ENNReal.ofReal_mul hcoeffNonneg, hlowMul]
    exact hV0.trans (hV0shift.trans hVxRel)
  have hRm :
      Rm04GlobalBound (I := I) (M := Y.M)
        Y.metric K := by
    intro y
    exact (rm04Bound_of_seq (I := I) bg k y).trans (by
      dsimp only [K]
      linarith)
  have hlocalFive :
      IsLocalDiffeomorphOn (modelWithCornersSelf Real E) I ∞
        (intrinsicFramedExp (I := I) Y.metric hEnorm x)
        (Metric.ball (0 : E) (5 * s)) := by
    intro z
    exact hlocalCtrl
      ⟨z.1, Metric.ball_subset_ball hfiveCtrl.le z.2⟩
  have htwoCtrl : 2 * s < rCtrl := by
    exact
      (mul_lt_mul_of_pos_right (by norm_num : (2 : Real) < 5) hs).trans
        hfiveCtrl
  have hno :
      ∀ z, z ∈ Metric.ball (0 : E) (2 * s) → z ≠ 0 →
        ∀ t, t ∈ Ioo (0 : Real) 1 →
          ¬ IsConjVec (I := I) Y.metric hEnorm x
            ((t • normalFrame (I := I) Y.metric x z :
              TangentSpace I x) : E) := by
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
      intrFrame_not_conj (I := I) Y.metric hEnorm x
        (t • z) (c := (1 / 2 : Real)) (by norm_num)
        (fun v => (hmetricCtrl (t • z) htz v).1)
    simpa only [map_smul] using hraw
  let P : ENNReal :=
    intrPullVol (I := I) Y.metric hEnorm x (2 * s)
  have hPraw :
      P ≤ (volume : Measure E).toSphere Set.univ *
        ENNReal.ofReal (hypRadVol q d (2 * s)) := by
    simpa only [P, d, n] using
      (intrPullVol_le_hyp (I := I) Y.metric hEnorm x hq
        (by positivity : 0 < 2 * s) hno hRic)
  have hVxRaw :
      Vx ≤
        (volume : Measure
          (EuclideanSpace Real (Fin n))).toSphere Set.univ *
            ENNReal.ofReal (hypRadVol q d (2 * s)) := by
    calc
      Vx ≤
          riemannianVolumeMeasure (I := I) (M := Y.M)
            Y.metric
            {y : Y.M |
              riemannianEDist I x y < ENNReal.ofReal (2 * s)} := by
        exact measure_mono
          (edistBall_mono (I := I) x (by linarith : s ≤ 2 * s))
      _ ≤
          (volume : Measure
            (EuclideanSpace Real (Fin n))).toSphere Set.univ *
              ENNReal.ofReal (hypRadVol q d (2 * s)) := by
        simpa only [d, n] using
          (segBall_vol_le_euclidean (I := I) Y.metric hEnorm x hq
            (by positivity : 0 < 2 * s) hRic)
  have hmodelTwo :
      hypRadVol q d (2 * s) ≤ upperC * s ^ n := by
    calc
      hypRadVol q d (2 * s)
          ≤ (2 * s) ^ (d + 1) *
              Real.exp (q * (d : Real) * (2 * s)) :=
        hypRadVol_le d hq (by positivity)
      _ = upperC * s ^ n := by
        dsimp only [upperC]
        rw [hdSucc, mul_pow]
        ring
  have hmodelTwoE :
      ENNReal.ofReal (hypRadVol q d (2 * s)) ≤
        ENNReal.ofReal (upperC * s ^ n) :=
    ENNReal.ofReal_le_ofReal hmodelTwo
  have hsphereBEq :
      (volume : Measure
        (EuclideanSpace Real (Fin n))).toSphere Set.univ =
          ENNReal.ofReal sphereB := by
    exact (ENNReal.ofReal_toReal (measure_lt_top _ _).ne).symm
  have hspherePEq :
      (volume : Measure E).toSphere Set.univ =
        ENNReal.ofReal sphereP := by
    exact (ENNReal.ofReal_toReal (measure_lt_top _ _).ne).symm
  let T : Real := upperC * s ^ n
  have hT : 0 < T := mul_pos hupper (pow_pos hs _)
  have hVxUpper :
      Vx ≤ ENNReal.ofReal sphereB * ENNReal.ofReal T := by
    calc
      Vx ≤
          (volume : Measure
            (EuclideanSpace Real (Fin n))).toSphere Set.univ *
              ENNReal.ofReal (hypRadVol q d (2 * s)) := hVxRaw
      _ = ENNReal.ofReal sphereB *
            ENNReal.ofReal (hypRadVol q d (2 * s)) := by
        rw [hsphereBEq]
      _ ≤ ENNReal.ofReal sphereB *
            ENNReal.ofReal (upperC * s ^ n) := by
        gcongr
      _ = ENNReal.ofReal sphereB * ENNReal.ofReal T := by
        rfl
  have hPUpper :
      P ≤ ENNReal.ofReal sphereP * ENNReal.ofReal T := by
    calc
      P ≤ (volume : Measure E).toSphere Set.univ *
            ENNReal.ofReal (hypRadVol q d (2 * s)) := hPraw
      _ = ENNReal.ofReal sphereP *
            ENNReal.ofReal (hypRadVol q d (2 * s)) := by
        rw [hspherePEq]
      _ ≤ ENNReal.ofReal sphereP *
            ENNReal.ofReal (upperC * s ^ n) := by
        gcongr
      _ = ENNReal.ofReal sphereP * ENNReal.ofReal T := by
        rfl
  let den : Real := (sphereB + sphereP) * T
  have hden : 0 < den := mul_pos hspheres hT
  have hDen : Vx + P ≤ ENNReal.ofReal den := by
    calc
      Vx + P ≤
          ENNReal.ofReal sphereB * ENNReal.ofReal T +
            ENNReal.ofReal sphereP * ENNReal.ofReal T :=
        add_le_add hVxUpper hPUpper
      _ = ENNReal.ofReal ((sphereB + sphereP) * T) :=
        ofReal_add_mul hsphereB.le hsphereP
      _ = ENNReal.ofReal den := rfl
  have hfivePos : 0 < 5 * s :=
    mul_pos (by norm_num) hs
  have hfit : s + 2 * s < 5 * s := cgt_fit hs
  have hquarter : s < (5 * s) / 4 := cgt_quarter hs
  have hcgt :
      ENNReal.ofReal (s / 2) * Vx / (Vx + P) ≤
        intrInjRadius (I := I) Y.metric hEnorm x := by
    simpa only [Vx, P, two_mul] using
      (intrInj_ge_cgt (I := I) (K := K) (R := 5 * s)
        (r₀ := s) (s := s) Y.metric hEnorm x
        hK hfivePos hfivePi hRm hlocalFive hs hs hfit hquarter)
  have hratio :
      ENNReal.ofReal ((s / 2) * low / den) ≤
        ENNReal.ofReal (s / 2) * Vx / (Vx + P) := by
    rw [ENNReal.ofReal_div_of_pos hden,
      ENNReal.ofReal_mul (by positivity : 0 ≤ s / 2)]
    exact ENNReal.div_le_div
      (by
        gcongr)
      hDen
  have hbpow : b ^ n ≤ b :=
    pow_le_of_le_one hb.le hb1 (Nat.ne_of_gt hn)
  have hratioEq :
      (s / 2) * low / den =
        a * b * Real.exp (-C * D) := by
    dsimp only [low, den, T, a]
    rw [show s = tau * b from rfl]
    exact decay_ratio_eq n hshift.ne' hspheres.ne' hupper.ne'
      htau.ne' hb.ne'
  have hprofileRatio :
      a * b ^ n * Real.exp (-C * D) ≤
        (s / 2) * low / den := by
    rw [hratioEq]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hbpow ha.le)
      (Real.exp_pos _).le
  have hfinal :
      ENNReal.ofReal
          (a * b ^ n * Real.exp (-C * D)) ≤
        intrInjRadius (I := I) Y.metric hEnorm x := by
    exact (ENNReal.ofReal_le_ofReal hprofileRatio).trans
      (hratio.trans hcgt)
  simpa only [n, b, C, D, PointedRiemannianManifold.intrInjRadius] using
    hfinal

@[simp] theorem injDecay_dist
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k : Nat,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M)
    (bg : SeqBoundedGeometry (I := I) X)
    (base : BaseInjBound (I := I) X) :
    (injDecayOfBg (I := I) X hcomplete hconn bg base).dist =
      riemSeqDist (I := I) X := by
  rfl

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem injDecay_realizes
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k : Nat,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M)
    (bg : SeqBoundedGeometry (I := I) X)
    (base : BaseInjBound (I := I) X) :
    (injDecayOfBg (I := I) X hcomplete hconn bg base).RealizesEdist := by
  refine ⟨?_, ?_⟩
  · intro k x y
    rw [injDecay_dist]
    exact ENNReal.toReal_nonneg
  · intro k x y
    rw [injDecay_dist]
    let : TopologicalSpace (X.obj k).M := (X.obj k).topology
    let : ChartedSpace H (X.obj k).M := (X.obj k).charted
    let : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    let : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
    let : T2Space (X.obj k).M := (X.obj k).t2
    let : T2Space (TangentBundle I (X.obj k).M) :=
      (X.obj k).t2TangentBundle
    let : RiemannianBundle
        (fun z : (X.obj k).M => TangentSpace I z) :=
      (X.obj k).riemBundle (I := I)
    let : (z : (X.obj k).M) →
        InnerProductSpace Real (TangentSpace I z) :=
      (X.obj k).riemInner (I := I)
    let : IsContinuousRiemannianBundle E
        (fun z : (X.obj k).M => TangentSpace I z) :=
      (X.obj k).riemBundle_cont (I := I)
    let : EMetricSpace (X.obj k).M :=
      (X.obj k).emetricSpace (I := I)
    have : IsRiemannianManifold I (X.obj k).M :=
      ⟨fun _ _ => rfl⟩
    let : ConnectedSpace (X.obj k).M := hconn k
    dsimp only [riemSeqDist]
    exact
      (ENNReal.ofReal_toReal (by
        rw [IsRiemannianManifold.out (I := I)]
        exact riemannianEDist_ne_top (I := I) x y)).symm

theorem exists_injDecay
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k : Nat,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M)
    (bg : SeqBoundedGeometry (I := I) X)
    (base : BaseInjBound (I := I) X) :
    ∃ hd : InjRadiusDecayInput (I := I) X, hd.RealizesEdist :=
  ⟨injDecayOfBg (I := I) X hcomplete hconn bg base,
    injDecay_realizes (I := I) X hcomplete hconn bg base⟩

end HCGCompactness
end DifferentialGeometry
