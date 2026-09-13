import DifferentialGeometry.Geometry.Compactness.CheegerGromov.BoundedGeometry.NormalCoordinates.RadiusProfile

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace CheegerGromovCompactness

open Filter
open scoped Manifold ContDiff Topology

variable {E : Type uE} [NormedAddCommGroup E]
variable [InnerProductSpace Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable [I.Boundaryless]

structure BallRadiusProfile
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hd : InjectivityRadiusDecay (I := I) X)
    (radius : forall k : Nat, (X.obj k).M -> Real) where
  ratio : Real
  ratio_pos : 0 < ratio
  le_radius : forall (k : Nat) (x : (X.obj k).M),
    ratio * hd.mu (hd.dist k x (X.obj k).basepoint) <= radius k x
  le_exp_radius : forall (k : Nat) (x : (X.obj k).M),
    (letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
     letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
     letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
     letI : T2Space (TangentBundle I (X.obj k).M) := (X.obj k).t2TangentBundle
     ratio * hd.mu (hd.dist k x (X.obj k).basepoint) <=
       Geometry.Riemannian.expMapC2Radius (I := I) (X.obj k).metric x)
  half_le_metricCoerciveConst : forall (k : Nat) (x : (X.obj k).M),
    (letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
     letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
     letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
     letI : T2Space (TangentBundle I (X.obj k).M) := (X.obj k).t2TangentBundle
     (1 / 2 : Real) <= Geometry.Riemannian.metricCoerciveConst (I := I) (X.obj k).metric x)

namespace BallRadiusProfile

def metricCoerciveRatio
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    {radius : forall k : Nat, (X.obj k).M -> Real}
    (h : BallRadiusProfile (I := I) hd radius) : Real :=
  Real.sqrt (1 / 2 : Real) * h.ratio

theorem metricCoerciveRatio_pos
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    {radius : forall k : Nat, (X.obj k).M -> Real}
    (h : BallRadiusProfile (I := I) hd radius) : 0 < h.metricCoerciveRatio := by
  rw [metricCoerciveRatio]
  exact mul_pos (Real.sqrt_pos.mpr (by norm_num)) h.ratio_pos

theorem metricCoerciveRatio_le_ratio
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    {radius : forall k : Nat, (X.obj k).M -> Real}
    (h : BallRadiusProfile (I := I) hd radius) : h.metricCoerciveRatio <= h.ratio := by
  rw [metricCoerciveRatio]
  have hsqrt : Real.sqrt (1 / 2 : Real) <= 1 :=
    Real.sqrt_le_one.mpr (by norm_num)
  simpa only [one_mul] using
    mul_le_mul_of_nonneg_right hsqrt h.ratio_pos.le

theorem floor_pos
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    {radius : forall k : Nat, (X.obj k).M -> Real}
    (h : BallRadiusProfile (I := I) hd radius) (R : Real) :
    0 < h.ratio * hd.mu R :=
  mul_pos h.ratio_pos (hd.mu_pos R)

theorem floor_le_radius
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    {radius : forall k : Nat, (X.obj k).M -> Real}
    (h : BallRadiusProfile (I := I) hd radius) {k : Nat} {x : (X.obj k).M} {R : Real}
    (hx : hd.dist k x (X.obj k).basepoint <= R) :
    h.ratio * hd.mu R <= radius k x := by
  calc
    h.ratio * hd.mu R <=
        h.ratio * hd.mu (hd.dist k x (X.obj k).basepoint) :=
      mul_le_mul_of_nonneg_left (hd.mu_antitone hx) h.ratio_pos.le
    _ <= radius k x := h.le_radius k x

theorem floor_le_exp
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    {radius : forall k : Nat, (X.obj k).M -> Real}
    (h : BallRadiusProfile (I := I) hd radius) {k : Nat} {x : (X.obj k).M} {R : Real}
    (hx : hd.dist k x (X.obj k).basepoint <= R) :
    (letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
     letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
     letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
     letI : T2Space (TangentBundle I (X.obj k).M) := (X.obj k).t2TangentBundle
     h.ratio * hd.mu R <=
       Geometry.Riemannian.expMapC2Radius (I := I) (X.obj k).metric x) := by
  let : TopologicalSpace (X.obj k).M := (X.obj k).topology
  let : ChartedSpace H (X.obj k).M := (X.obj k).charted
  let : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  let : T2Space (TangentBundle I (X.obj k).M) := (X.obj k).t2TangentBundle
  calc
    h.ratio * hd.mu R <=
        h.ratio * hd.mu (hd.dist k x (X.obj k).basepoint) :=
      mul_le_mul_of_nonneg_left (hd.mu_antitone hx) h.ratio_pos.le
    _ <= Geometry.Riemannian.expMapC2Radius (I := I) (X.obj k).metric x :=
      h.le_exp_radius k x

theorem floor_le_metricCoerciveExpRadius
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    {radius : forall k : Nat, (X.obj k).M -> Real}
    (h : BallRadiusProfile (I := I) hd radius) {k : Nat} {x : (X.obj k).M} {R : Real}
    (hx : hd.dist k x (X.obj k).basepoint <= R) :
    (letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
     letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
     letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
     letI : T2Space (TangentBundle I (X.obj k).M) := (X.obj k).t2TangentBundle
     h.metricCoerciveRatio * hd.mu R <=
       Geometry.Riemannian.metricCoerciveExpRadius (I := I) (X.obj k).metric x) := by
  let : TopologicalSpace (X.obj k).M := (X.obj k).topology
  let : ChartedSpace H (X.obj k).M := (X.obj k).charted
  let : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  let : T2Space (TangentBundle I (X.obj k).M) := (X.obj k).t2TangentBundle
  rw [metricCoerciveRatio, Geometry.Riemannian.metricCoerciveExpRadius]
  calc
    Real.sqrt (1 / 2 : Real) * h.ratio * hd.mu R =
        Real.sqrt (1 / 2 : Real) * (h.ratio * hd.mu R) := by ring
    _ <= Real.sqrt (Geometry.Riemannian.metricCoerciveConst
          (I := I) (X.obj k).metric x) * (h.ratio * hd.mu R) :=
      mul_le_mul_of_nonneg_right
        (Real.sqrt_le_sqrt (h.half_le_metricCoerciveConst k x)) (h.floor_pos R).le
    _ <= Real.sqrt (Geometry.Riemannian.metricCoerciveConst
          (I := I) (X.obj k).metric x) *
          Geometry.Riemannian.expMapC2Radius (I := I) (X.obj k).metric x :=
      mul_le_mul_of_nonneg_left (h.floor_le_exp hx) (Real.sqrt_nonneg _)

def subseq
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    {radius : forall k : Nat, (X.obj k).M -> Real}
    (h : BallRadiusProfile (I := I) hd radius) (f : Nat -> Nat) :
    BallRadiusProfile (I := I) (hd.subseq f)
      (fun k x => radius (f k) x) where
  ratio := h.ratio
  ratio_pos := h.ratio_pos
  le_radius := by
    intro k x
    change h.ratio * hd.mu (hd.dist (f k) x (X.obj (f k)).basepoint) <= radius (f k) x
    exact h.le_radius (f k) x
  le_exp_radius := by
    intro k x
    let : TopologicalSpace (X.obj (f k)).M := (X.obj (f k)).topology
    let : ChartedSpace H (X.obj (f k)).M := (X.obj (f k)).charted
    let : IsManifold I ∞ (X.obj (f k)).M := (X.obj (f k)).smooth
    let : T2Space (TangentBundle I (X.obj (f k)).M) :=
      (X.obj (f k)).t2TangentBundle
    change h.ratio * hd.mu (hd.dist (f k) x (X.obj (f k)).basepoint) <=
      Geometry.Riemannian.expMapC2Radius (I := I) (X.obj (f k)).metric x
    exact h.le_exp_radius (f k) x
  half_le_metricCoerciveConst := by
    intro k x
    let : TopologicalSpace (X.obj (f k)).M := (X.obj (f k)).topology
    let : ChartedSpace H (X.obj (f k)).M := (X.obj (f k)).charted
    let : IsManifold I ∞ (X.obj (f k)).M := (X.obj (f k)).smooth
    let : T2Space (TangentBundle I (X.obj (f k)).M) :=
      (X.obj (f k)).t2TangentBundle
    change (1 / 2 : Real) <=
      Geometry.Riemannian.metricCoerciveConst (I := I) (X.obj (f k)).metric x
    exact h.half_le_metricCoerciveConst (f k) x

def ofNormalRadiusProfile
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    {hb : NormalCoordMetricBounds (I := I) X}
    (h : NormalRadiusProfile (I := I) hd hb) :
    BallRadiusProfile (I := I) hd hb.radius where
  ratio := h.ratio
  ratio_pos := h.ratio_pos
  le_radius := h.le_radius
  le_exp_radius := h.le_exp_radius
  half_le_metricCoerciveConst := hb.half_le_metricCoerciveConst

theorem ofNormalRadiusProfile_metricCoerciveRatio
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    {hb : NormalCoordMetricBounds (I := I) X}
    (h : NormalRadiusProfile (I := I) hd hb) :
    (ofNormalRadiusProfile (I := I) h).metricCoerciveRatio = h.metricCoerciveRatio :=
  rfl

end BallRadiusProfile

end CheegerGromovCompactness
end DifferentialGeometry
