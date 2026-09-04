import DifferentialGeometry.Geometry.Compactness.CheegerGromov.BoundedGeometry.NormalCoordinates.RadiusProfile
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Covering.VolumeComparison

open DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Filter
open scoped Manifold ContDiff Topology

variable {E : Type uE} [NormedAddCommGroup E]
variable [InnerProductSpace Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable [I.Boundaryless]

structure MetricCompactCore
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I)) where

  decay : InjectivityRadiusDecay (I := I) X

  packAll : ∀ D : Real, 0 < D → decay.PackingBound D

  D : Real
  hD : 0 < D

  pack : decay.PackingBound D

  volume : BallMultiplicityBound (I := I) X

  dist_eq : volume.dist = decay.dist

  covering_scale_le_volume_radius :
    max 4 (50 * Real.exp (decay.C * (20 * decay.lambda D 0))) *
      decay.lambda D 0 ≤ volume.r0

  realizes : decay.RealizesDistance

structure MetricCompactSeed
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I)) where
  decay : InjectivityRadiusDecay (I := I) X
  packAll : ∀ D : Real, 0 < D → decay.PackingBound D
  volume : BallMultiplicityBound (I := I) X
  dist_eq : volume.dist = decay.dist
  realizes : decay.RealizesDistance

namespace MetricCompactSeed

def withDivisor
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (s : MetricCompactSeed (I := I) X) (D : Real) (hD : 0 < D)
    (hcap :
      max 4 (50 * Real.exp (s.decay.C * (20 * s.decay.lambda D 0))) *
        s.decay.lambda D 0 ≤ s.volume.r0) :
    MetricCompactCore (I := I) X where
  decay := s.decay
  packAll := s.packAll
  D := D
  hD := hD
  pack := s.packAll D hD
  volume := s.volume
  dist_eq := s.dist_eq
  covering_scale_le_volume_radius := hcap
  realizes := s.realizes


theorem exists_core
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (s : MetricCompactSeed (I := I) X) (c : Real) :
    ∃ D : Real, 0 < D ∧
      max 4 (50 * Real.exp (s.decay.C * (20 * s.decay.lambda D 0))) *
          s.decay.lambda D 0 ≤ s.volume.r0 ∧
        1 < D ∧ s.decay.mu 0 ≤ D ∧ c < D := by
  let q : Real :=
    s.decay.a * (min s.decay.baseInj.ρ 1) ^ (Module.finrank Real E)
  let K : Real := max 4 (50 * Real.exp (s.decay.C * 20))
  let B : Real := max 1 (max q (max (K * q / s.volume.r0) c))
  let D : Real := B + 1
  have hB_lt : B < D := by
    dsimp only [D]
    linarith
  have honeB : (1 : Real) ≤ B := by
    dsimp only [B]
    exact le_max_left _ _
  have hqB : q ≤ B := by
    dsimp only [B]
    exact (le_max_left q _).trans (le_max_right 1 _)
  have hcapB : K * q / s.volume.r0 ≤ B := by
    dsimp only [B]
    exact ((le_max_left (K * q / s.volume.r0) _).trans
      (le_max_right q _)).trans (le_max_right 1 _)
  have hcB : c ≤ B := by
    dsimp only [B]
    exact (le_max_right (K * q / s.volume.r0) c).trans
      ((le_max_right q _).trans (le_max_right 1 _))
  have hD_one : (1 : Real) < D := honeB.trans_lt hB_lt
  have hD : 0 < D := zero_lt_one.trans hD_one
  have hqD : q ≤ D := hqB.trans hB_lt.le
  have hmuD : s.decay.mu 0 ≤ D := by
    simpa only [InjectivityRadiusDecay.mu, q, mul_zero, Real.exp_zero, mul_one]
      using hqD
  have hlam_le : s.decay.lambda D 0 ≤ 1 :=
    s.decay.lambda_le_one_at_zero (by simpa only [q] using hqD)
  have hlam_nonneg : 0 ≤ s.decay.lambda D 0 :=
    (s.decay.lambda_pos hD 0).le
  have harg :
      s.decay.C * (20 * s.decay.lambda D 0) ≤ s.decay.C * 20 := by
    have h20 : 20 * s.decay.lambda D 0 ≤ (20 : Real) := by
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hlam_le (by norm_num : (0 : Real) ≤ 20)
    exact mul_le_mul_of_nonneg_left h20 s.decay.C_nonneg
  have hfac :
      max 4 (50 * Real.exp
        (s.decay.C * (20 * s.decay.lambda D 0))) ≤ K := by
    dsimp only [K]
    exact max_le_max le_rfl (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr harg) (by norm_num))
  have hKq : K * q < D * s.volume.r0 :=
    (div_lt_iff₀ s.volume.r0_pos).1 (hcapB.trans_lt hB_lt)
  have hKlam : K * s.decay.lambda D 0 < s.volume.r0 := by
    calc
      K * s.decay.lambda D 0 = K * q / D := by
        dsimp only [InjectivityRadiusDecay.lambda, InjectivityRadiusDecay.mu, q]
        simp only [mul_zero, Real.exp_zero, mul_one]
        ring
      _ < s.volume.r0 := (div_lt_iff₀ hD).2 (by
        simpa only [mul_comm] using hKq)
  have hcap :
      max 4 (50 * Real.exp
          (s.decay.C * (20 * s.decay.lambda D 0))) *
        s.decay.lambda D 0 ≤ s.volume.r0 :=
    (mul_le_mul_of_nonneg_right hfac hlam_nonneg).trans hKlam.le
  exact ⟨D, hD, hcap, hD_one, hmuD, hcB.trans_lt hB_lt⟩

end MetricCompactSeed

namespace MetricCompactCore

theorem exists_stable_net
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (inp : MetricCompactCore (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k)) :
    ∃ L : NetLimitData inp.decay inp.D P,
      ∀ α β : Nat,
        (∀ᶠ k in atTop,
          BInter inp.decay inp.D P L.lamInf α β (L.φ k)) ∨
        (∀ᶠ k in atTop,
          ¬ BInter inp.decay inp.D P L.lamInf α β (L.φ k)) :=
  exists_stableNetData inp.decay inp.hD P

end MetricCompactCore

noncomputable def properMetricsOfCompleteConnected
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k : Nat,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M) :
    ∀ k : Nat, ProperMetricOn (I := I) (X.obj k) :=
  fun k => properMetricOn (I := I) (X.obj k)
    (hcomplete.complete k) (hconn k)

structure MetricCompactBase
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I)) where
  decay : InjectivityRadiusDecay (I := I) X
  pack : ∀ D : Real, 0 < D → decay.PackingBound D
  volume : BallMultiplicityBound (I := I) X
  dist_eq : volume.dist = decay.dist
  realizes : decay.RealizesDistance
  normalBounds : NormalCoordMetricBounds (I := I) X
  normalRadius : NormalRadiusProfile decay normalBounds

namespace MetricCompactBase

def toSeed
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (b : MetricCompactBase (I := I) X) :
    MetricCompactSeed (I := I) X where
  decay := b.decay
  packAll := b.pack
  volume := b.volume
  dist_eq := b.dist_eq
  realizes := b.realizes

instance
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)} :
    Coe (MetricCompactBase (I := I) X) (MetricCompactSeed (I := I) X) :=
  ⟨toSeed⟩

theorem exists_large_divisor
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (b : MetricCompactBase (I := I) X) (c : Real) :
    ∃ D : Real, 1 < D ∧
      b.decay.mu 0 ≤ D ∧
      c < b.normalRadius.metricCoerciveRatio * D ∧
      max 4 (50 * Real.exp (b.decay.C * (20 * b.decay.lambda D 0))) *
        b.decay.lambda D 0 ≤ b.volume.r0 := by
  let q : Real :=
    b.decay.a * (min b.decay.baseInj.ρ 1) ^ (Module.finrank Real E)
  let K : Real := max 4 (50 * Real.exp (b.decay.C * 20))
  let B : Real := max 1
    (max q (max (K * q / b.volume.r0) (c / b.normalRadius.metricCoerciveRatio)))
  let D : Real := B + 1
  have hB_lt : B < D := by
    dsimp only [D]
    linarith
  have honeB : (1 : Real) ≤ B := by
    dsimp only [B]
    exact le_max_left _ _
  have hqB : q ≤ B := by
    dsimp only [B]
    exact (le_max_left q _).trans (le_max_right 1 _)
  have hcapB : K * q / b.volume.r0 ≤ B := by
    dsimp only [B]
    exact ((le_max_left (K * q / b.volume.r0) _).trans
      (le_max_right q _)).trans (le_max_right 1 _)
  have hcB : c / b.normalRadius.metricCoerciveRatio ≤ B := by
    dsimp only [B]
    exact ((le_max_right (K * q / b.volume.r0) _).trans
      (le_max_right q _)).trans (le_max_right 1 _)
  have hD_one : (1 : Real) < D := honeB.trans_lt hB_lt
  have hD : 0 < D := zero_lt_one.trans hD_one
  have hqD : q ≤ D := hqB.trans hB_lt.le
  have hmuD : b.decay.mu 0 ≤ D := by
    simpa only [InjectivityRadiusDecay.mu, q, mul_zero, Real.exp_zero, mul_one]
      using hqD
  have hlam_le : b.decay.lambda D 0 ≤ 1 :=
    b.decay.lambda_le_one_at_zero (by simpa only [q] using hqD)
  have hlam_nonneg : 0 ≤ b.decay.lambda D 0 :=
    (b.decay.lambda_pos hD 0).le
  have harg :
      b.decay.C * (20 * b.decay.lambda D 0) ≤ b.decay.C * 20 := by
    have h20 : 20 * b.decay.lambda D 0 ≤ (20 : Real) := by
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hlam_le (by norm_num : (0 : Real) ≤ 20)
    exact mul_le_mul_of_nonneg_left h20 b.decay.C_nonneg
  have hfac :
      max 4 (50 * Real.exp (b.decay.C * (20 * b.decay.lambda D 0))) ≤ K := by
    dsimp only [K]
    exact max_le_max le_rfl (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr harg) (by norm_num))
  have hKq : K * q < D * b.volume.r0 :=
    (div_lt_iff₀ b.volume.r0_pos).1 (hcapB.trans_lt hB_lt)
  have hKlam : K * b.decay.lambda D 0 < b.volume.r0 := by
    calc
      K * b.decay.lambda D 0 = K * q / D := by
        dsimp only [InjectivityRadiusDecay.lambda, InjectivityRadiusDecay.mu, q]
        simp only [mul_zero, Real.exp_zero, mul_one]
        ring
      _ < b.volume.r0 := (div_lt_iff₀ hD).2 (by
        simpa only [mul_comm] using hKq)
  have hc : c < b.normalRadius.metricCoerciveRatio * D := by
    simpa only [mul_comm] using
      (div_lt_iff₀ b.normalRadius.metricCoerciveRatio_pos).1 (hcB.trans_lt hB_lt)
  refine ⟨D, hD_one, hmuD, hc, ?_⟩
  exact (mul_le_mul_of_nonneg_right hfac hlam_nonneg).trans hKlam.le

theorem exists_large_divisor_for_exponential_scales
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (b : MetricCompactBase (I := I) X) (c₀ : Real) :
    ∃ D : Real, 1 < D ∧
      b.decay.mu 0 ≤ D ∧
      c₀ < b.normalRadius.metricCoerciveRatio * D ∧
      (8 : Real) < b.normalRadius.metricCoerciveRatio * D ∧
      (16 : Real) < b.normalRadius.ratio * D ∧
      2 * exponentialBallRadiusFactor b.decay D < D ∧
      2 * exponentialBallRadiusFactor b.decay D < b.normalRadius.ratio * D ∧
      max 4 (50 * Real.exp (b.decay.C * (20 * b.decay.lambda D 0))) *
        b.decay.lambda D 0 ≤ b.volume.r0 := by
  let Q : Real := 410 * Real.exp (b.decay.C * 20)
  let c : Real := max c₀ (max 8
    (max Q (Q * b.normalRadius.metricCoerciveRatio)))
  obtain ⟨D, hD_one, hmuD, hc, hcap⟩ := b.exists_large_divisor c
  have hD : 0 < D := zero_lt_one.trans hD_one
  have hc₀c : c₀ ≤ c := by
    dsimp only [c]
    exact le_max_left _ _
  have h8c : (8 : Real) ≤ c := by
    dsimp only [c]
    exact (le_max_left (8 : Real) _).trans (le_max_right c₀ _)
  have hQc : Q ≤ c := by
    dsimp only [c]
    exact ((le_max_left Q _).trans (le_max_right 8 _)).trans
      (le_max_right c₀ _)
  have hQgc : Q * b.normalRadius.metricCoerciveRatio ≤ c := by
    dsimp only [c]
    exact ((le_max_right Q _).trans (le_max_right 8 _)).trans
      (le_max_right c₀ _)
  have hc₀ : c₀ < b.normalRadius.metricCoerciveRatio * D := hc₀c.trans_lt hc
  have h8 : (8 : Real) < b.normalRadius.metricCoerciveRatio * D := h8c.trans_lt hc
  have hQgp : Q < b.normalRadius.metricCoerciveRatio * D := hQc.trans_lt hc
  have hQg : Q * b.normalRadius.metricCoerciveRatio <
      b.normalRadius.metricCoerciveRatio * D := hQgc.trans_lt hc
  have hQD : Q < D := by
    exact lt_of_mul_lt_mul_right (by simpa only [mul_comm] using hQg)
      b.normalRadius.metricCoerciveRatio_pos.le
  have hQratio : Q < b.normalRadius.ratio * D := by
    exact hQgp.trans_le (mul_le_mul_of_nonneg_right
      b.normalRadius.metricCoerciveRatio_le_ratio hD.le)
  have h16Q : (16 : Real) ≤ Q := by
    dsimp only [Q]
    have hexp : (1 : Real) ≤ Real.exp (b.decay.C * 20) :=
      Real.one_le_exp (mul_nonneg b.decay.C_nonneg (by norm_num))
    calc
      (16 : Real) ≤ 410 * 1 := by norm_num
      _ ≤ 410 * Real.exp (b.decay.C * 20) :=
        mul_le_mul_of_nonneg_left hexp (by norm_num)
  have h16 : (16 : Real) < b.normalRadius.ratio * D :=
    h16Q.trans_lt hQratio
  have hqD :
      b.decay.a * (min b.decay.baseInj.ρ 1) ^ (Module.finrank Real E) ≤ D := by
    simpa only [InjectivityRadiusDecay.mu, mul_zero, Real.exp_zero, mul_one]
      using hmuD
  have hlam_le : b.decay.lambda D 0 ≤ 1 :=
    b.decay.lambda_le_one_at_zero hqD
  have harg :
      b.decay.C * (20 * b.decay.lambda D 0) ≤ b.decay.C * 20 := by
    have h20 : 20 * b.decay.lambda D 0 ≤ (20 : Real) := by
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hlam_le (by norm_num : (0 : Real) ≤ 20)
    exact mul_le_mul_of_nonneg_left h20 b.decay.C_nonneg
  have hfac : 2 * exponentialBallRadiusFactor b.decay D ≤ Q := by
    dsimp only [exponentialBallRadiusFactor, Q]
    calc
      2 * (205 * Real.exp (b.decay.C * (20 * b.decay.lambda D 0))) =
          410 * Real.exp (b.decay.C * (20 * b.decay.lambda D 0)) := by ring
      _ ≤ 410 * Real.exp (b.decay.C * 20) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr harg) (by norm_num)
  exact ⟨D, hD_one, hmuD, hc₀, h8, h16, hfac.trans_lt hQD,
    hfac.trans_lt hQratio, hcap⟩

end MetricCompactBase

structure MetricCompactnessInputs
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I)) where
  decay : InjectivityRadiusDecay (I := I) X

  packAll : ∀ D : Real, 0 < D → decay.PackingBound D

  D : Real
  hD : 0 < D
  pack : decay.PackingBound D
  volume : BallMultiplicityBound (I := I) X
  dist_eq : volume.dist = decay.dist

  covering_scale_le_volume_radius :
    max 4 (50 * Real.exp (decay.C * (20 * decay.lambda D 0))) *
      decay.lambda D 0 <= volume.r0
  realizes : decay.RealizesDistance
  normalBounds : NormalCoordMetricBounds (I := I) X

  normalRadius : NormalRadiusProfile decay normalBounds

namespace MetricCompactnessInputs

def toCore
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (inp : MetricCompactnessInputs (I := I) X) :
    MetricCompactCore (I := I) X where
  decay := inp.decay
  packAll := inp.packAll
  D := inp.D
  hD := inp.hD
  pack := inp.pack
  volume := inp.volume
  dist_eq := inp.dist_eq
  covering_scale_le_volume_radius := inp.covering_scale_le_volume_radius
  realizes := inp.realizes

instance
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)} :
    Coe (MetricCompactnessInputs (I := I) X)
      (MetricCompactCore (I := I) X) :=
  ⟨toCore⟩

def toBase
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (inp : MetricCompactnessInputs (I := I) X) :
    MetricCompactBase (I := I) X where
  decay := inp.decay
  pack := inp.packAll
  volume := inp.volume
  dist_eq := inp.dist_eq
  realizes := inp.realizes
  normalBounds := inp.normalBounds
  normalRadius := inp.normalRadius

def ofBase
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (b : MetricCompactBase (I := I) X) (D : Real) (hD : 0 < D)
    (hcap :
      max 4 (50 * Real.exp (b.decay.C * (20 * b.decay.lambda D 0))) *
        b.decay.lambda D 0 ≤ b.volume.r0) :
    MetricCompactnessInputs (I := I) X where
  decay := b.decay
  packAll := b.pack
  D := D
  hD := hD
  pack := b.pack D hD
  volume := b.volume
  dist_eq := b.dist_eq
  covering_scale_le_volume_radius := hcap
  realizes := b.realizes
  normalBounds := b.normalBounds
  normalRadius := b.normalRadius

theorem exists_of_base
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (b : MetricCompactBase (I := I) X) (c : Real) :
    ∃ inp : MetricCompactnessInputs (I := I) X,
      1 < inp.D ∧ inp.decay.mu 0 ≤ inp.D ∧
        c < inp.normalRadius.metricCoerciveRatio * inp.D := by
  obtain ⟨D, hD_one, hmuD, hc, hcap⟩ := b.exists_large_divisor c
  have hD : 0 < D := zero_lt_one.trans hD_one
  refine ⟨ofBase b D hD hcap, ?_, ?_, ?_⟩
  · exact hD_one
  · exact hmuD
  · exact hc

theorem exists_of_base_with_exponential_scale_bounds
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (b : MetricCompactBase (I := I) X) (c₀ : Real) :
    ∃ inp : MetricCompactnessInputs (I := I) X,
      1 < inp.D ∧ inp.decay.mu 0 ≤ inp.D ∧
      c₀ < inp.normalRadius.metricCoerciveRatio * inp.D ∧
      (8 : Real) < inp.normalRadius.metricCoerciveRatio * inp.D ∧
      (16 : Real) < inp.normalRadius.ratio * inp.D ∧
      2 * exponentialBallRadiusFactor inp.decay inp.D < inp.D ∧
      2 * exponentialBallRadiusFactor inp.decay inp.D <
        inp.normalRadius.ratio * inp.D := by
  obtain ⟨D, hD_one, hmuD, hc₀, h8, h16, hradD, hradRatio, hcap⟩ :=
    b.exists_large_divisor_for_exponential_scales c₀
  have hD : 0 < D := zero_lt_one.trans hD_one
  refine ⟨ofBase b D hD hcap, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hD_one
  · exact hmuD
  · exact hc₀
  · exact h8
  · exact h16
  · exact hradD
  · exact hradRatio

theorem physScale_of_extra
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (inp : MetricCompactnessInputs (I := I) X) {aMin : Real}
    (haMin : 0 < aMin)
    (hextra :
      (8 * Real.exp inp.decay.C / aMin) * inp.normalRadius.metricCoerciveRatio <
        inp.normalRadius.metricCoerciveRatio * inp.D) :
    8 * Real.exp inp.decay.C < aMin * inp.D := by
  have hD : 8 * Real.exp inp.decay.C / aMin < inp.D := by
    exact lt_of_mul_lt_mul_right
      (by simpa only [mul_comm] using hextra) inp.normalRadius.metricCoerciveRatio_pos.le
  simpa only [mul_comm] using (div_lt_iff₀ haMin).1 hD

theorem exponential_scale_tails
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (inp : MetricCompactnessInputs (I := I) X)
    (h8 : (8 : Real) < inp.normalRadius.metricCoerciveRatio * inp.D)
    (hradRatio : 2 * exponentialBallRadiusFactor inp.decay inp.D <
      inp.normalRadius.ratio * inp.D)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData (I := I) inp.decay inp.D P) (r : Real) :
    ExponentialRadiusScaleTail (I := I) inp.decay inp.D P L inp.pack r ∧
      ExponentialBallRadiusTail (I := I) inp.decay inp.D P L inp.pack r
        (exponentialBallRadiusFactor inp.decay inp.D) := by
  exact ⟨inp.normalRadius.metricCoerciveRatio_scale_tail inp.hD h8 P inp.realizes L inp.pack r,
    inp.normalRadius.radius_scale_tail inp.hD
      (exponential_ball_radius_factor_pos inp.decay inp.D) hradRatio
      P inp.realizes L inp.pack r⟩

def ofUniformVolume
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (decay : InjectivityRadiusDecay (I := I) X)
    (packAll : ∀ D : Real, 0 < D → decay.PackingBound D)
    (D : Real) (hD : 0 < D)
    (vol : UniformBallVolumeBounds (I := I) X)
    (dist_eq : vol.dist = decay.dist)
    (covering_scale_le_volume_radius :
      max 4 (50 * Real.exp (decay.C * (20 * decay.lambda D 0))) *
        decay.lambda D 0 ≤ vol.r0)
    (realizes : decay.RealizesDistance)
    (normalBounds : NormalCoordMetricBounds (I := I) X)
    (normalRadius : NormalRadiusProfile decay normalBounds) :
    MetricCompactnessInputs (I := I) X where
  decay := decay
  packAll := packAll
  D := D
  hD := hD
  pack := packAll D hD
  volume := vol.toBallMultiplicityBound
  dist_eq := by
    change vol.dist = decay.dist
    exact dist_eq
  covering_scale_le_volume_radius := by
    change max 4 (50 * Real.exp (decay.C * (20 * decay.lambda D 0))) *
      decay.lambda D 0 ≤ vol.r0
    exact covering_scale_le_volume_radius
  realizes := realizes
  normalBounds := normalBounds
  normalRadius := normalRadius

def subseq
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (inp : MetricCompactnessInputs (I := I) X) (f : Nat -> Nat) :
    MetricCompactnessInputs (I := I) (X.subseq f) where
  decay := inp.decay.subseq f
  packAll := fun D hD => (inp.packAll D hD).subseq f
  D := inp.D
  hD := inp.hD
  pack := inp.pack.subseq f
  volume := inp.volume.subseq f
  dist_eq := by
    funext k x y
    change inp.volume.dist (f k) x y = inp.decay.dist (f k) x y
    rw [inp.dist_eq]
  covering_scale_le_volume_radius := by
    change max 4 (50 * Real.exp (inp.decay.C * (20 * inp.decay.lambda inp.D 0))) *
      inp.decay.lambda inp.D 0 ≤ inp.volume.r0
    exact inp.covering_scale_le_volume_radius
  realizes := inp.realizes.subseq f
  normalBounds := inp.normalBounds.subseq f
  normalRadius := inp.normalRadius.subseq f

end MetricCompactnessInputs


end HCGCompactness
end DifferentialGeometry
