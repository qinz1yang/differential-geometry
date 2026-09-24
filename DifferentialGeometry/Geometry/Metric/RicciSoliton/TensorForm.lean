import DifferentialGeometry.Geometry.Metric.RicciSoliton.Models
import DifferentialGeometry.Geometry.Curvature.Metric.LeviCivita
import DifferentialGeometry.Geometry.Operator.Hessian.Trace.Realization
import DifferentialGeometry.Geometry.Connection.ChartBridge.Scalar.Hessian

set_option autoImplicit false

noncomputable section

open Bundle
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry

open Connection Curvature Operator
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.Coordinates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]

omit [SigmaCompactSpace M] in
theorem hessianSec_metricCov_eq_hessFun
    (g : SmoothRiemannianMetric I M) {f : M -> Real}
    (hf : ContMDiff I 𝓘(Real, Real) ∞ f) (x : M) (v w : TangentSpace I x) :
    hessianSec (I := I) (metricCov (I := I) g) (metricCov_smooth (I := I) g)
      f hf x (vec2 (I := I) v w) = hessFun (I := I) g f x v w := by
  rw [hessSec_inner_cov (I := I) (cov := metricCov (I := I) g)
      (metricCov_smooth (I := I) g) g
      (leviCivitaConnectionOfMetric_isMetricCompatible (I := I) g) f hf x v w,
    hessFun_eq_cov_grad (I := I) g hf x v w]
  rfl

omit [SigmaCompactSpace M] in
theorem metricRicciAt_add_hessianSec_eq_iff_gradientRicciSoliton
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; Real⟯) (sigma : Real) :
    (∀ x (v w : TangentSpace I x),
      metricRicciAt (I := I) g x (vec2 (I := I) v w) +
        hessianSec (I := I) (metricCov (I := I) g) (metricCov_smooth (I := I) g)
          (f : M -> Real) (f.contMDiff) x (vec2 (I := I) v w) =
        (sigma / 2) * g.inner x v w) ↔
      gradientRicciSoliton (I := I) g f sigma := by
  constructor
  · intro h x v w
    simpa only [hessianSec_metricCov_eq_hessFun (I := I) g f.contMDiff x v w,
      metricRicciAt_apply_eq_ricciTensor (I := I) g x v w] using h x v w
  · intro h x v w
    simpa only [hessianSec_metricCov_eq_hessFun (I := I) g f.contMDiff x v w,
      metricRicciAt_apply_eq_ricciTensor (I := I) g x v w] using h x v w

section Round

variable {A : Type*} [NormedAddCommGroup A] [InnerProductSpace Real A]
  [FiniteDimensional Real A]
variable {n : Nat} [Fact (Module.finrank Real A = n + 1)]

omit [FiniteDimensional Real A] in
theorem roundSphereShrinker_metricRicciAt_add_hessianSec_eq
    (hn : 2 ≤ n)
    [NeZero (Module.finrank Real (EuclideanSpace Real (Fin n)))] :
    ∀ (x : Metric.sphere (0 : A) 1) (v w : TangentSpace (𝓡 n) x),
      metricRicciAt (I := 𝓡 n) (roundSphereShrinkerMetric (A := A) hn) x
          (vec2 (I := 𝓡 n) v w) +
        hessianSec (I := 𝓡 n)
          (metricCov (I := 𝓡 n) (roundSphereShrinkerMetric (A := A) hn))
          (metricCov_smooth (I := 𝓡 n) (roundSphereShrinkerMetric (A := A) hn))
          ((roundSphereShrinkerPotential (A := A) (n := n) :
            Metric.sphere (0 : A) 1 -> Real))
          (roundSphereShrinkerPotential (A := A) (n := n)).contMDiff x
          (vec2 (I := 𝓡 n) v w) =
        (1 / 2) * (roundSphereShrinkerMetric (A := A) hn).inner x v w := by
  have h := (metricRicciAt_add_hessianSec_eq_iff_gradientRicciSoliton (I := 𝓡 n)
    (roundSphereShrinkerMetric (A := A) hn)
    (roundSphereShrinkerPotential (A := A) (n := n)) 1).mpr
    (gradientRicciSoliton_roundSphere (A := A) hn)
  intro x v w
  simpa only [one_div] using h x v w

omit [FiniteDimensional Real E] [CompleteSpace E] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [I.Boundaryless] in
private theorem vec2_apply_zero {x : M} (v w : TangentSpace I x) :
    vec2 (I := I) v w 0 = v := rfl

omit [FiniteDimensional Real E] [CompleteSpace E] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [I.Boundaryless] in
private theorem vec2_apply_one {x : M} (v w : TangentSpace I x) :
    vec2 (I := I) v w 1 = w := rfl

omit [CompleteSpace E] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless] in
theorem tensor0S_eq_zero_iff_vec2 {x : M}
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x) :
    T = 0 ↔ ∀ v w : TangentSpace I x, T (vec2 (I := I) v w) = 0 := by
  constructor
  · intro h v w
    rw [h]
    simp
  · intro h
    refine ext0S_basis (I := I) (𝕜 := Real) (s := 2) (x := x)
      (Module.finBasis Real (TangentSpace I x)) ?_
    intro slots
    have hslots :
        (fun a : Fin 2 => Module.finBasis Real (TangentSpace I x) (slots a)) =
          vec2 (I := I) (Module.finBasis Real (TangentSpace I x) (slots 0))
            (Module.finBasis Real (TangentSpace I x) (slots 1)) := by
      funext a
      fin_cases a <;> rfl
    rw [component0S_apply, hslots, h]
    simp

omit [SigmaCompactSpace M] [I.Boundaryless] in
theorem metricRicciAt_add_hessianSec_eq_smul_metricTensor0S_iff
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; Real⟯) (s : Real) :
    (∀ x : M,
      metricRicciAt (I := I) g x +
        hessianSec (I := I) (metricCov (I := I) g) (metricCov_smooth (I := I) g)
          (f : M -> Real) (f.contMDiff) x =
        (1 / (2 * s)) • metricTensor0S (I := I) g x) ↔
    ∀ x (v w : TangentSpace I x),
      metricRicciAt (I := I) g x (vec2 (I := I) v w) +
        hessianSec (I := I) (metricCov (I := I) g) (metricCov_smooth (I := I) g)
          (f : M -> Real) (f.contMDiff) x (vec2 (I := I) v w) =
        (1 / (2 * s)) * g.inner x v w := by
  constructor
  · intro h x v w
    have hv := congrArg
      (fun T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x =>
        T (vec2 (I := I) v w)) (h x)
    simpa only [Tensor0SSpace.add_apply, Tensor0SSpace.smul_apply,
      metricTensor0S_apply, vec2_apply_zero, vec2_apply_one, smul_eq_mul] using hv
  · intro h x
    refine sub_eq_zero.mp ((tensor0S_eq_zero_iff_vec2 (I := I) _).mpr ?_)
    intro v w
    rw [Tensor0SSpace.sub_apply, Tensor0SSpace.add_apply, Tensor0SSpace.smul_apply,
      metricTensor0S_apply, vec2_apply_zero, vec2_apply_one, h x v w]
    simp

omit [FiniteDimensional Real A] in
theorem roundSphereShrinker_metricRicciAt_add_hessianSec_eq_smul_metricTensor0S
    (hn : 2 ≤ n)
    [NeZero (Module.finrank Real (EuclideanSpace Real (Fin n)))] :
    ∀ (x : Metric.sphere (0 : A) 1),
      metricRicciAt (I := 𝓡 n) (roundSphereShrinkerMetric (A := A) hn) x +
        hessianSec (I := 𝓡 n)
          (metricCov (I := 𝓡 n) (roundSphereShrinkerMetric (A := A) hn))
          (metricCov_smooth (I := 𝓡 n) (roundSphereShrinkerMetric (A := A) hn))
          ((roundSphereShrinkerPotential (A := A) (n := n) :
            Metric.sphere (0 : A) 1 -> Real))
          (roundSphereShrinkerPotential (A := A) (n := n)).contMDiff x =
        (1 / (2 * (1 : Real))) • metricTensor0S (I := 𝓡 n)
          (roundSphereShrinkerMetric (A := A) hn) x :=
  (metricRicciAt_add_hessianSec_eq_smul_metricTensor0S_iff (I := 𝓡 n)
    (roundSphereShrinkerMetric (A := A) hn)
    (roundSphereShrinkerPotential (A := A) (n := n)) 1).mpr
    (by
      intro x v w
      simpa only [mul_one] using
        roundSphereShrinker_metricRicciAt_add_hessianSec_eq (A := A) (n := n) hn x v w)

end Round

section Gaussian

theorem gaussian_metricRicciAt_add_hessianSec_eq (n : Nat) [NeZero n] :
    ∀ (x : EuclideanSpace Real (Fin n))
        (v w : TangentSpace (𝓘(Real, EuclideanSpace Real (Fin n))) x),
      metricRicciAt (I := 𝓘(Real, EuclideanSpace Real (Fin n)))
          (euclideanMetric (E := EuclideanSpace Real (Fin n))) x
          (vec2 (I := 𝓘(Real, EuclideanSpace Real (Fin n))) v w) +
        hessianSec (I := 𝓘(Real, EuclideanSpace Real (Fin n)))
          (metricCov (I := 𝓘(Real, EuclideanSpace Real (Fin n)))
            (euclideanMetric (E := EuclideanSpace Real (Fin n))))
          (metricCov_smooth (I := 𝓘(Real, EuclideanSpace Real (Fin n)))
            (euclideanMetric (E := EuclideanSpace Real (Fin n))))
          ((gaussianPotential (E := EuclideanSpace Real (Fin n)) :
            EuclideanSpace Real (Fin n) -> Real))
          (gaussianPotential (E := EuclideanSpace Real (Fin n))).contMDiff x
          (vec2 (I := 𝓘(Real, EuclideanSpace Real (Fin n))) v w) =
        (1 / 2) *
          (euclideanMetric (E := EuclideanSpace Real (Fin n))).inner x v w :=
  (metricRicciAt_add_hessianSec_eq_iff_gradientRicciSoliton
    (I := 𝓘(Real, EuclideanSpace Real (Fin n)))
    (euclideanMetric (E := EuclideanSpace Real (Fin n)))
    (gaussianPotential (E := EuclideanSpace Real (Fin n))) 1).mpr
    (gradientRicciSoliton_gaussian (E := EuclideanSpace Real (Fin n)))

end Gaussian

end DifferentialGeometry.Geometry
