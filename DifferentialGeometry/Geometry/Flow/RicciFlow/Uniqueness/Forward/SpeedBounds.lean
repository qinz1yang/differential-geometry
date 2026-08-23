import DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.QuadraticTerms
import DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.Drift
import DifferentialGeometry.Tensor.RSTensor.Tensor0SRiemannian.Scaling

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle DifferentialGeometry.Tensor0SBundle
open _root_.Tensor0SBundle
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor.RSTensor
open scoped Manifold ContDiff BigOperators Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]


variable [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]

variable [NeZero (Module.finrank Real E)]

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem ricciDriftOwnSq_le (g : SmoothRiemannianMetric I M) (x : M) :
    normSq0S (I := I) g x 4 (ricciDrift04 (I := I) g x) ≤
      16 * (Module.finrank Real E : Real) ^ 6 *
        (normSq0S (I := I) g x 2 (metricRicciAt (I := I) g x) *
          normSq0S (I := I) g x 4 (metricRm04At (I := I) g x)) := by
  let L :=
    lowerTri (I := I) (metricRicciAt (I := I) g x)
      (riemannOp (metricCov (I := I) g) x)
  have hL0 := lowerTriSq_le (I := I) g
    (metricRicciAt (I := I) g x)
    (riemannOp (metricCov (I := I) g) x)
  rw [lowerRm_eq_rm04] at hL0
  have hL :
      normSq0S (I := I) g x 4 L ≤
        (Module.finrank Real E : Real) ^ 6 *
          (normSq0S (I := I) g x 2 (metricRicciAt (I := I) g x) *
            normSq0S (I := I) g x 4 (metricRm04At (I := I) g x)) := by
    simpa only [L] using hL0
  have hslots := driftSlotsSq_le (I := I) g L
  rw [ricciDrift04]
  change normSq0S (I := I) g x 4 (driftSlots (I := I) L) ≤ _
  calc
    normSq0S (I := I) g x 4 (driftSlots (I := I) L) ≤
        16 * normSq0S (I := I) g x 4 L := hslots
    _ ≤ 16 * ((Module.finrank Real E : Real) ^ 6 *
        (normSq0S (I := I) g x 2 (metricRicciAt (I := I) g x) *
          normSq0S (I := I) g x 4 (metricRm04At (I := I) g x))) :=
      mul_le_mul_of_nonneg_left hL (by norm_num)
    _ = _ := by ring

def uhlSpeed04 (g : SmoothRiemannianMetric I M)
    (R : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4)
    (x : M) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 4 x :=
  (roughLap0SField (I := I) g R x - (2 : Real) • curvatureQuadraticCombination (I := I) g R x) -
      ricciDrift04 (I := I) g x +
    (2 : Real) • lowerTri (I := I) (metricRicciAt (I := I) g x)
      (riemannOp (metricCov (I := I) g) x)

omit [NeZero (Module.finrank Real E)] in
omit [SigmaCompactSpace M] in
theorem uhlSpeed04_low {Idx : Type*} [Fintype Idx]
    (g : SmoothRiemannianMetric I M)
    (R : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4)
    (x : M) (basis : Module.Basis Idx Real (TangentSpace I x)) :
    lowOfComp (I := I) g basis
        (fun i j k l =>
          (roughLap0SField (I := I) g R x)
              (vec4 (I := I) (basis i) (basis j) (basis k) (basis l)) -
            2 * (curvatureQuadraticCombination (I := I) g R x)
              (vec4 (I := I) (basis i) (basis j) (basis k) (basis l)) -
            ricciDrift04 (I := I) g x
              (vec4 (I := I) (basis i) (basis j) (basis k) (basis l)) +
            2 * metricRicciAt (I := I) g x
              (fun q : Fin 2 =>
                if q = 0 then
                  riemannOp (metricCov (I := I) g) x
                    (basis i) (basis j) (basis k)
                else basis l)) =
      uhlSpeed04 (I := I) g R x := by
  apply lowOfComp_ext (I := I)
  intro i j k l
  rw [uhlSpeed04, Tensor0SSpace.add_apply (I := I) 4 x,
    Tensor0SSpace.sub_apply (I := I) 4 x,
    Tensor0SSpace.sub_apply (I := I) 4 x,
    Tensor0SSpace.smul_apply (I := I) 4 x,
    Tensor0SSpace.smul_apply (I := I) 4 x,
    lowerTri_apply]
  rfl

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem uhlSpeedSq_le (g : SmoothRiemannianMetric I M)
    (R : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4)
    (x : M) :
    normSq0S (I := I) g x 4 (uhlSpeed04 (I := I) g R x) ≤
      8 * (Module.finrank Real E : Real) ^ 6 *
          normSq0S (I := I) g x 6
            (metricNabla0S (I := I) g (metricNabla0S (I := I) g R) x) +
        512 * (Module.finrank Real E : Real) ^ 14 *
          normSq0S (I := I) g x 4 (R x) ^ 2 +
        72 * (Module.finrank Real E : Real) ^ 6 *
          (normSq0S (I := I) g x 2 (metricRicciAt (I := I) g x) *
            normSq0S (I := I) g x 4 (metricRm04At (I := I) g x)) := by
  let L := roughLap0SField (I := I) g R x
  let Q := curvatureQuadraticCombination (I := I) g R x
  let D := ricciDrift04 (I := I) g x
  let C :=
    lowerTri (I := I) (metricRicciAt (I := I) g x)
      (riemannOp (metricCov (I := I) g) x)
  have hL :
      normSq0S (I := I) g x 4 L ≤
        (Module.finrank Real E : Real) ^ 6 *
          normSq0S (I := I) g x 6
            (metricNabla0S (I := I) g (metricNabla0S (I := I) g R) x) := by
    simpa only [L] using roughLapSq_le (I := I) g R x
  have hQ :
      normSq0S (I := I) g x 4 Q ≤
        16 * (Module.finrank Real E : Real) ^ 14 *
          normSq0S (I := I) g x 4 (R x) ^ 2 := by
    simpa only [Q] using curvatureQuadraticCombination_norm_sq_le (I := I) g R x
  have hD :
      normSq0S (I := I) g x 4 D ≤
        16 * (Module.finrank Real E : Real) ^ 6 *
          (normSq0S (I := I) g x 2 (metricRicciAt (I := I) g x) *
            normSq0S (I := I) g x 4 (metricRm04At (I := I) g x)) := by
    simpa only [D] using ricciDriftOwnSq_le (I := I) g x
  have hC0 := lowerTriSq_le (I := I) g
    (metricRicciAt (I := I) g x)
    (riemannOp (metricCov (I := I) g) x)
  rw [lowerRm_eq_rm04] at hC0
  have hC :
      normSq0S (I := I) g x 4 C ≤
        (Module.finrank Real E : Real) ^ 6 *
          (normSq0S (I := I) g x 2 (metricRicciAt (I := I) g x) *
            normSq0S (I := I) g x 4 (metricRm04At (I := I) g x)) := by
    simpa only [C] using hC0
  have hLQ := normSq0S_sub_le (I := I) g x 4 L ((2 : Real) • Q)
  have h2Q :
      normSq0S (I := I) g x 4 ((2 : Real) • Q) =
        4 * normSq0S (I := I) g x 4 Q := by
    calc
      normSq0S (I := I) g x 4 ((2 : Real) • Q) =
          (2 : Real) ^ 2 * normSq0S (I := I) g x 4 Q :=
        Tensor0SBundle.normSq0S_smul (I := I) g (2 : Real) Q
      _ = 4 * normSq0S (I := I) g x 4 Q := by norm_num
  rw [h2Q] at hLQ
  have hLQD := normSq0S_sub_le (I := I) g x 4 (L - (2 : Real) • Q) D
  have hout := normSq0S_add_le (I := I) g x 4
    ((L - (2 : Real) • Q) - D) ((2 : Real) • C)
  have h2C :
      normSq0S (I := I) g x 4 ((2 : Real) • C) =
        4 * normSq0S (I := I) g x 4 C := by
    calc
      normSq0S (I := I) g x 4 ((2 : Real) • C) =
          (2 : Real) ^ 2 * normSq0S (I := I) g x 4 C :=
        Tensor0SBundle.normSq0S_smul (I := I) g (2 : Real) C
      _ = 4 * normSq0S (I := I) g x 4 C := by norm_num
  rw [h2C] at hout
  change normSq0S (I := I) g x 4 (((L - (2 : Real) • Q) - D) +
    (2 : Real) • C) ≤ _
  linarith

end DifferentialGeometry.PDE.RicciFlow
