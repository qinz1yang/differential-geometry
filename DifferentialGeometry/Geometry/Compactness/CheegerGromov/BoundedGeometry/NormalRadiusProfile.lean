import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Covering.ExponentialBallCovering
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.MetricBounds

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

structure NormalRadiusProfile
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hd : InjectivityRadiusDecay (I := I) X)
    (hb : NormalCoordMetricBounds (I := I) X) where
  ratio : Real
  ratio_pos : 0 < ratio
  le_radius : ∀ k x,
    ratio * hd.mu (hd.dist k x (X.obj k).basepoint) ≤ hb.radius k x
  le_exp_radius : ∀ k x,
    letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
    letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
    letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    letI : T2Space (TangentBundle I (X.obj k).M) := (X.obj k).t2TangentBundle
    ratio * hd.mu (hd.dist k x (X.obj k).basepoint) ≤
      Geometry.Riemannian.expMapC2Radius (I := I) (X.obj k).metric x

namespace NormalRadiusProfile

def subseq
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    {hb : NormalCoordMetricBounds (I := I) X}
    (h : NormalRadiusProfile hd hb) (f : Nat → Nat) :
    NormalRadiusProfile (hd.subseq f) (hb.subseq f) where
  ratio := h.ratio
  ratio_pos := h.ratio_pos
  le_radius := by
    intro k x
    change h.ratio * hd.mu (hd.dist (f k) x (X.obj (f k)).basepoint) ≤
      hb.radius (f k) x
    exact h.le_radius (f k) x
  le_exp_radius := by
    intro k x
    let : TopologicalSpace (X.obj (f k)).M := (X.obj (f k)).topology
    let : ChartedSpace H (X.obj (f k)).M := (X.obj (f k)).charted
    let : IsManifold I ∞ (X.obj (f k)).M := (X.obj (f k)).smooth
    let : T2Space (TangentBundle I (X.obj (f k)).M) :=
      (X.obj (f k)).t2TangentBundle
    change h.ratio * hd.mu (hd.dist (f k) x (X.obj (f k)).basepoint) ≤
      Geometry.Riemannian.expMapC2Radius (I := I) (X.obj (f k)).metric x
    exact h.le_exp_radius (f k) x

def gpRatio
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    {hb : NormalCoordMetricBounds (I := I) X}
    (h : NormalRadiusProfile hd hb) : Real :=
  Real.sqrt (1 / 2 : Real) * h.ratio

theorem gp_ratio_pos
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    {hb : NormalCoordMetricBounds (I := I) X}
    (h : NormalRadiusProfile hd hb) : 0 < h.gpRatio := by
  rw [gpRatio]
  exact mul_pos (Real.sqrt_pos.mpr (by norm_num)) h.ratio_pos

theorem gp_ratio_le_ratio
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    {hb : NormalCoordMetricBounds (I := I) X}
    (h : NormalRadiusProfile hd hb) : h.gpRatio ≤ h.ratio := by
  rw [gpRatio]
  have hsqrt : Real.sqrt (1 / 2 : Real) ≤ 1 :=
    Real.sqrt_le_one.mpr (by norm_num)
  simpa only [one_mul] using
    mul_le_mul_of_nonneg_right hsqrt h.ratio_pos.le

theorem floor_pos
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    {hb : NormalCoordMetricBounds (I := I) X}
    (h : NormalRadiusProfile hd hb) (R : Real) :
    0 < h.ratio * hd.mu R :=
  mul_pos h.ratio_pos (hd.mu_pos R)

theorem floor_le_radius
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    {hb : NormalCoordMetricBounds (I := I) X}
    (h : NormalRadiusProfile hd hb) {k : Nat} {x : (X.obj k).M} {R : Real}
    (hx : hd.dist k x (X.obj k).basepoint ≤ R) :
    h.ratio * hd.mu R ≤ hb.radius k x := by
  calc
    h.ratio * hd.mu R ≤
        h.ratio * hd.mu (hd.dist k x (X.obj k).basepoint) :=
      mul_le_mul_of_nonneg_left (hd.mu_antitone hx) h.ratio_pos.le
    _ ≤ hb.radius k x := h.le_radius k x

theorem floor_le_exp
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    {hb : NormalCoordMetricBounds (I := I) X}
    (h : NormalRadiusProfile hd hb) {k : Nat} {x : (X.obj k).M} {R : Real}
    (hx : hd.dist k x (X.obj k).basepoint ≤ R) :
    letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
    letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
    letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    letI : T2Space (TangentBundle I (X.obj k).M) := (X.obj k).t2TangentBundle
    h.ratio * hd.mu R ≤
      Geometry.Riemannian.expMapC2Radius (I := I) (X.obj k).metric x := by
  let : TopologicalSpace (X.obj k).M := (X.obj k).topology
  let : ChartedSpace H (X.obj k).M := (X.obj k).charted
  let : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  let : T2Space (TangentBundle I (X.obj k).M) := (X.obj k).t2TangentBundle
  calc
    h.ratio * hd.mu R ≤
        h.ratio * hd.mu (hd.dist k x (X.obj k).basepoint) :=
      mul_le_mul_of_nonneg_left (hd.mu_antitone hx) h.ratio_pos.le
    _ ≤ Geometry.Riemannian.expMapC2Radius (I := I) (X.obj k).metric x :=
      h.le_exp_radius k x

theorem floor_le_exp_gp
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    {hb : NormalCoordMetricBounds (I := I) X}
    (h : NormalRadiusProfile hd hb) {k : Nat} {x : (X.obj k).M} {R : Real}
    (hx : hd.dist k x (X.obj k).basepoint ≤ R) :
    letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
    letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
    letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    letI : T2Space (TangentBundle I (X.obj k).M) := (X.obj k).t2TangentBundle
    h.gpRatio * hd.mu R ≤
      Geometry.Riemannian.expRadiusGp (I := I) (X.obj k).metric x := by
  let : TopologicalSpace (X.obj k).M := (X.obj k).topology
  let : ChartedSpace H (X.obj k).M := (X.obj k).charted
  let : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  let : T2Space (TangentBundle I (X.obj k).M) := (X.obj k).t2TangentBundle
  rw [gpRatio, Geometry.Riemannian.expRadiusGp]
  calc
    Real.sqrt (1 / 2 : Real) * h.ratio * hd.mu R =
        Real.sqrt (1 / 2 : Real) * (h.ratio * hd.mu R) := by ring
    _ ≤ Real.sqrt (Geometry.Riemannian.gpCoerciveConst
          (I := I) (X.obj k).metric x) * (h.ratio * hd.mu R) :=
      mul_le_mul_of_nonneg_right
        (Real.sqrt_le_sqrt (hb.half_le_gp_const k x)) (h.floor_pos R).le
    _ ≤ Real.sqrt (Geometry.Riemannian.gpCoerciveConst
          (I := I) (X.obj k).metric x) *
          Geometry.Riemannian.expMapC2Radius (I := I) (X.obj k).metric x :=
      mul_le_mul_of_nonneg_left (h.floor_le_exp hx) (Real.sqrt_nonneg _)

theorem mul_lambda_lt_floor
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    {hb : NormalCoordMetricBounds (I := I) X}
    (h : NormalRadiusProfile hd hb) {D c R : Real}
    (hD : 0 < D) (hc : c < h.ratio * D) :
    c * hd.lambda D R < h.ratio * hd.mu R := by
  rw [InjectivityRadiusDecay.lambda]
  calc
    c * (hd.mu R / D) = (c / D) * hd.mu R := by ring
    _ < h.ratio * hd.mu R :=
      mul_lt_mul_of_pos_right ((div_lt_iff₀ hD).2 hc) (hd.mu_pos R)

theorem mul_lambda_lt_radius
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    {hb : NormalCoordMetricBounds (I := I) X}
    (h : NormalRadiusProfile hd hb) {D c R : Real}
    (hD : 0 < D) (hc : c < h.ratio * D)
    {k : Nat} {x : (X.obj k).M}
    (hx : hd.dist k x (X.obj k).basepoint ≤ R) :
    c * hd.lambda D R < hb.radius k x :=
  (h.mul_lambda_lt_floor hD hc).trans_le (h.floor_le_radius hx)

theorem mul_lambda_lt_exp
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    {hb : NormalCoordMetricBounds (I := I) X}
    (h : NormalRadiusProfile hd hb) {D c R : Real}
    (hD : 0 < D) (hc : c < h.ratio * D)
    {k : Nat} {x : (X.obj k).M}
    (hx : hd.dist k x (X.obj k).basepoint ≤ R) :
    letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
    letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
    letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    letI : T2Space (TangentBundle I (X.obj k).M) := (X.obj k).t2TangentBundle
    c * hd.lambda D R <
      Geometry.Riemannian.expMapC2Radius (I := I) (X.obj k).metric x := by
  let : TopologicalSpace (X.obj k).M := (X.obj k).topology
  let : ChartedSpace H (X.obj k).M := (X.obj k).charted
  let : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  let : T2Space (TangentBundle I (X.obj k).M) := (X.obj k).t2TangentBundle
  exact (h.mul_lambda_lt_floor hD hc).trans_le (h.floor_le_exp hx)

theorem mul_lambda_lt_exp_gp
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    {hb : NormalCoordMetricBounds (I := I) X}
    (h : NormalRadiusProfile hd hb) {D c R : Real}
    (hD : 0 < D) (hc : c < h.gpRatio * D)
    {k : Nat} {x : (X.obj k).M}
    (hx : hd.dist k x (X.obj k).basepoint ≤ R) :
    letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
    letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
    letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    letI : T2Space (TangentBundle I (X.obj k).M) := (X.obj k).t2TangentBundle
    c * hd.lambda D R <
      Geometry.Riemannian.expRadiusGp (I := I) (X.obj k).metric x := by
  let : TopologicalSpace (X.obj k).M := (X.obj k).topology
  let : ChartedSpace H (X.obj k).M := (X.obj k).charted
  let : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  let : T2Space (TangentBundle I (X.obj k).M) := (X.obj k).t2TangentBundle
  have hfloor : c * hd.lambda D R < h.gpRatio * hd.mu R := by
    rw [InjectivityRadiusDecay.lambda]
    calc
      c * (hd.mu R / D) = (c / D) * hd.mu R := by ring
      _ < h.gpRatio * hd.mu R :=
        mul_lt_mul_of_pos_right ((div_lt_iff₀ hD).2 hc) (hd.mu_pos R)
  exact hfloor.trans_le (h.floor_le_exp_gp hx)

theorem gp_scale_tail
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    {hb : NormalCoordMetricBounds (I := I) X}
    (h : NormalRadiusProfile hd hb) {D : Real} (hD : 0 < D)
    (h8 : (8 : Real) < h.gpRatio * D)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (hre : hd.RealizesDistance) (L : NetLimitData (I := I) hd D P)
    (pb : hd.PackingBound D) (r : Real) :
    ExponentialRadiusScaleTail (I := I) hd D P L pb r := by
  have hwin : ∀ᶠ n in atTop, ∀ γ ∈ Finset.range (pb.A r),
      L.lamInf γ / 2 ≤ hd.lambda D (seqRadius hd D P (L.φ n) γ) :=
    (Filter.eventually_all_finset _).mpr fun γ _ =>
      (L.lambda_window hd hD P γ).mono fun _ hγ => by
        simpa only [NetLimitData.lamInf] using hγ.1
  filter_upwards [hwin] with n hn
  intro γ c hc
  let : MetricSpace (X.obj (L.φ n)).M := (P (L.φ n)).ms
  have : ProperSpace (X.obj (L.φ n)).M := (P (L.φ n)).proper
  have hr : seqRadius hd D P (L.φ n) (γ : Nat) =
      dist c (X.obj (L.φ n)).basepoint := by
    unfold seqRadius
    exact OrderedNet.netRadius_of_center _ _ _ (γ : Nat) hc
  have hx : hd.dist (L.φ n) c (X.obj (L.φ n)).basepoint ≤
      seqRadius hd D P (L.φ n) (γ : Nat) := by
    rw [← ProperMetricOn.dist_eq hd hre P (L.φ n), ← hr]
  let : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
  let : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
  let : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
  let : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
  let : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
    (X.obj (L.φ n)).t2TangentBundle
  calc
    4 * L.lamInf (γ : Nat) = 8 * (L.lamInf (γ : Nat) / 2) := by ring
    _ ≤ 8 * hd.lambda D (seqRadius hd D P (L.φ n) (γ : Nat)) :=
      mul_le_mul_of_nonneg_left
        (hn (γ : Nat) (Finset.mem_range.mpr γ.isLt)) (by norm_num)
    _ < Geometry.Riemannian.expRadiusGp
          (I := I) (X.obj (L.φ n)).metric c :=
      h.mul_lambda_lt_exp_gp (D := D) (c := 8)
        (R := seqRadius hd D P (L.φ n) (γ : Nat)) hD h8 hx

theorem half_gp_scale_tail
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    {hb : NormalCoordMetricBounds (I := I) X}
    (h : NormalRadiusProfile hd hb) {D a : Real} (hD : 0 < D)
    (ha : 0 < a) (haRatio : 2 * a < h.ratio * D)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (hre : hd.RealizesDistance) (L : NetLimitData (I := I) hd D P)
    (pb : hd.PackingBound D) (r : Real) :
    ∀ᶠ n in atTop, ∀ γ : Fin (pb.A r), ∀ c : (X.obj (L.φ n)).M,
      seqCenter hd D P (L.φ n) (γ : Nat) = some c →
        letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
        letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
        letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
        letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
        letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
          (X.obj (L.φ n)).t2TangentBundle
        (a / 2) * L.lamInf (γ : Nat) <
          Geometry.Riemannian.expRadiusGp
            (I := I) (X.obj (L.φ n)).metric c := by
  have hsqrt : (1 / 2 : Real) < Real.sqrt (1 / 2 : Real) := by
    have hsqrtSq := Real.sq_sqrt (by norm_num : (0 : Real) ≤ 1 / 2)
    have hsqrtNonneg := Real.sqrt_nonneg (1 / 2 : Real)
    nlinarith
  have hratioD : 0 < h.ratio * D := mul_pos h.ratio_pos hD
  have haGp : a < h.gpRatio * D := by
    calc
      a < (1 / 2 : Real) * (h.ratio * D) := by nlinarith
      _ < Real.sqrt (1 / 2 : Real) * (h.ratio * D) :=
        mul_lt_mul_of_pos_right hsqrt hratioD
      _ = h.gpRatio * D := by rw [gpRatio]; ring
  have hwin : ∀ᶠ n in atTop, ∀ γ ∈ Finset.range (pb.A r),
      L.lamInf γ / 2 ≤ hd.lambda D (seqRadius hd D P (L.φ n) γ) :=
    (Filter.eventually_all_finset _).mpr fun γ _ =>
      (L.lambda_window hd hD P γ).mono fun _ hγ => by
        simpa only [NetLimitData.lamInf] using hγ.1
  filter_upwards [hwin] with n hn
  intro γ c hc
  let : MetricSpace (X.obj (L.φ n)).M := (P (L.φ n)).ms
  have : ProperSpace (X.obj (L.φ n)).M := (P (L.φ n)).proper
  have hr : seqRadius hd D P (L.φ n) (γ : Nat) =
      dist c (X.obj (L.φ n)).basepoint := by
    unfold seqRadius
    exact OrderedNet.netRadius_of_center _ _ _ (γ : Nat) hc
  have hx : hd.dist (L.φ n) c (X.obj (L.φ n)).basepoint ≤
      seqRadius hd D P (L.φ n) (γ : Nat) := by
    rw [← ProperMetricOn.dist_eq hd hre P (L.φ n), ← hr]
  let : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
  let : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
  let : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
  let : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
  let : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
    (X.obj (L.φ n)).t2TangentBundle
  calc
    (a / 2) * L.lamInf (γ : Nat) =
        a * (L.lamInf (γ : Nat) / 2) := by ring
    _ ≤ a * hd.lambda D (seqRadius hd D P (L.φ n) (γ : Nat)) :=
      mul_le_mul_of_nonneg_left
        (hn (γ : Nat) (Finset.mem_range.mpr γ.isLt)) ha.le
    _ < Geometry.Riemannian.expRadiusGp
          (I := I) (X.obj (L.φ n)).metric c :=
      h.mul_lambda_lt_exp_gp (D := D) (c := a)
        (R := seqRadius hd D P (L.φ n) (γ : Nat)) hD haGp hx

theorem metric_scale_tail
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    {hb : NormalCoordMetricBounds (I := I) X}
    (h : NormalRadiusProfile hd hb) {D a : Real} (hD : 0 < D)
    (ha : 0 < a) (haRatio : 2 * a < h.ratio * D)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (hre : hd.RealizesDistance) (L : NetLimitData (I := I) hd D P)
    (pb : hd.PackingBound D) (r : Real) :
    ∀ᶠ n in atTop, ∀ γ : Fin (pb.A r), ∀ c : (X.obj (L.φ n)).M,
      seqCenter hd D P (L.φ n) (γ : Nat) = some c →
        a * L.lamInf (γ : Nat) ≤ hb.radius (L.φ n) c := by
  have hwin : ∀ᶠ n in atTop, ∀ γ ∈ Finset.range (pb.A r),
      L.lamInf γ / 2 ≤ hd.lambda D (seqRadius hd D P (L.φ n) γ) :=
    (Filter.eventually_all_finset _).mpr fun γ _ =>
      (L.lambda_window hd hD P γ).mono fun _ hγ => by
        simpa only [NetLimitData.lamInf] using hγ.1
  filter_upwards [hwin] with n hn
  intro γ c hc
  let : MetricSpace (X.obj (L.φ n)).M := (P (L.φ n)).ms
  have : ProperSpace (X.obj (L.φ n)).M := (P (L.φ n)).proper
  have hr : seqRadius hd D P (L.φ n) (γ : Nat) =
      dist c (X.obj (L.φ n)).basepoint := by
    unfold seqRadius
    exact OrderedNet.netRadius_of_center _ _ _ (γ : Nat) hc
  have hx : hd.dist (L.φ n) c (X.obj (L.φ n)).basepoint ≤
      seqRadius hd D P (L.φ n) (γ : Nat) := by
    rw [← ProperMetricOn.dist_eq hd hre P (L.φ n), ← hr]
  calc
    a * L.lamInf (γ : Nat) =
        (2 * a) * (L.lamInf (γ : Nat) / 2) := by ring
    _ ≤ (2 * a) * hd.lambda D
        (seqRadius hd D P (L.φ n) (γ : Nat)) :=
      mul_le_mul_of_nonneg_left
        (hn (γ : Nat) (Finset.mem_range.mpr γ.isLt)) (by positivity)
    _ ≤ h.ratio * hd.mu
        (seqRadius hd D P (L.φ n) (γ : Nat)) :=
      (h.mul_lambda_lt_floor hD haRatio).le
    _ ≤ h.ratio * hd.mu
        (hd.dist (L.φ n) c (X.obj (L.φ n)).basepoint) :=
      mul_le_mul_of_nonneg_left (hd.mu_antitone hx) h.ratio_pos.le
    _ ≤ hb.radius (L.φ n) c := h.le_radius (L.φ n) c

theorem radius_scale_tail
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    {hb : NormalCoordMetricBounds (I := I) X}
    (h : NormalRadiusProfile hd hb) {D a : Real} (hD : 0 < D) (ha : 0 < a)
    (haRatio : 2 * a < h.ratio * D)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (hre : hd.RealizesDistance) (L : NetLimitData (I := I) hd D P)
    (pb : hd.PackingBound D) (r : Real) :
    ExponentialBallRadiusTail (I := I) hd D P L pb r a := by
  have hwin : ∀ᶠ n in atTop, ∀ γ ∈ Finset.range (pb.A r),
      L.lamInf γ / 2 ≤ hd.lambda D (seqRadius hd D P (L.φ n) γ) :=
    (Filter.eventually_all_finset _).mpr fun γ _ =>
      (L.lambda_window hd hD P γ).mono fun _ hγ => by
        simpa only [NetLimitData.lamInf] using hγ.1
  filter_upwards [hwin] with n hn
  intro γ c hc
  let : MetricSpace (X.obj (L.φ n)).M := (P (L.φ n)).ms
  have : ProperSpace (X.obj (L.φ n)).M := (P (L.φ n)).proper
  have hr : seqRadius hd D P (L.φ n) (γ : Nat) =
      dist c (X.obj (L.φ n)).basepoint := by
    unfold seqRadius
    exact OrderedNet.netRadius_of_center _ _ _ (γ : Nat) hc
  have hx : hd.dist (L.φ n) c (X.obj (L.φ n)).basepoint ≤
      seqRadius hd D P (L.φ n) (γ : Nat) := by
    rw [← ProperMetricOn.dist_eq hd hre P (L.φ n), ← hr]
  let : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
  let : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
  let : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
  let : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
  let : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
  let : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
    (X.obj (L.φ n)).t2TangentBundle
  have hrad_pos : 0 < a * L.lamInf (γ : Nat) :=
    mul_pos ha (hd.lambda_pos hD (L.rInf (γ : Nat)))
  have hrad_lambda : a * L.lamInf (γ : Nat) ≤
      (2 * a) * hd.lambda D (seqRadius hd D P (L.φ n) (γ : Nat)) := by
    calc
      a * L.lamInf (γ : Nat) =
          (2 * a) * (L.lamInf (γ : Nat) / 2) := by ring
      _ ≤ (2 * a) * hd.lambda D
          (seqRadius hd D P (L.φ n) (γ : Nat)) :=
        mul_le_mul_of_nonneg_left
          (hn (γ : Nat) (Finset.mem_range.mpr γ.isLt)) (by positivity)
  have hexp := h.mul_lambda_lt_exp (D := D) (c := 2 * a)
    (R := seqRadius hd D P (L.φ n) (γ : Nat)) hD haRatio hx
  exact ⟨hrad_pos, hrad_lambda.trans hexp.le⟩

end NormalRadiusProfile

end HCGCompactness
end DifferentialGeometry
