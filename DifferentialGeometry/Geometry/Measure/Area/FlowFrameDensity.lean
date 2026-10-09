import DifferentialGeometry.Geometry.Measure.Area.ChangeOfFrame
import DifferentialGeometry.Geometry.Measure.Area.Pullback
import DifferentialGeometry.Geometry.Metric.Pullback.Immersion
import DifferentialGeometry.Topology.Diffeomorph.Flow
import Mathlib.Analysis.Calculus.Deriv.Mul

/- Scratch only. The original disk measure is already handled by worker07.
This is the missing prescribed-frame bridge: the frame is selected from the
central metric before any scalar test, and is constant in variation time. -/

set_option autoImplicit false
noncomputable section

open Bundle Filter Manifold Set DifferentialGeometry
open DifferentialGeometry.Geometry
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry

private theorem tangentTwoJacobian_eq_reference_mul
    {A H S : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [TopologicalSpace H] {I : ModelWithCorners ℝ A H}
    [TopologicalSpace S] [ChartedSpace H S] [IsManifold I ∞ S]
    (g₀ g₁ : SmoothRiemannianMetric I S) (z : S)
    (b : Module.Basis (Fin 2) ℝ (TangentSpace I z))
    (hb : ∀ i j, g₀.inner z (b i) (b j) = if i = j then 1 else 0)
    (v w : TangentSpace I z) :
    tangentTwoJacobian g₁ v w =
      tangentTwoJacobian g₀ v w * tangentTwoJacobian g₁ (b 0) (b 1) := by
  have hexpand (a : TangentSpace I z) :
      a = b.repr a 0 • b 0 + b.repr a 1 • b 1 := by
    simpa only [Fin.sum_univ_two] using (b.sum_repr a).symm
  let d : ℝ := |b.repr v 0 * b.repr w 1 - b.repr v 1 * b.repr w 0|
  have hfactor (g : SmoothRiemannianMetric I S) :
      tangentTwoJacobian g v w = d * tangentTwoJacobian g (b 0) (b 1) := by
    calc
      tangentTwoJacobian g v w =
          tangentTwoJacobian g
            (b.repr v 0 • b 0 + b.repr v 1 • b 1)
            (b.repr w 0 • b 0 + b.repr w 1 • b 1) :=
        congrArg₂ (tangentTwoJacobian g) (hexpand v) (hexpand w)
      _ = _ := tangentTwoJacobian_changeOfFrame g (b 0) (b 1) _ _ _ _
  have hunit : tangentTwoJacobian g₀ (b 0) (b 1) = 1 := by
    simp [tangentTwoJacobian, hb]
  have hbase : tangentTwoJacobian g₀ v w = d := by
    rw [hfactor g₀, hunit, mul_one]
  rw [hfactor g₁, hbase]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

omit [FiniteDimensional ℝ E] in
private theorem tangentTwoJacobian_induced_complex_basis
    (N : TopologicalSpace.Opens ℂ) (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (U : ℂ → M)
    (hU : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (fun q : N => U q))
    (hi : ∀ q : N, Function.Injective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun p : N => U p) q)) (z : N) :
    tangentTwoJacobian (g.pullback (fun q : N => U q) hU hi)
      (x := z) (1 : ℂ) Complex.I = riemannianAreaDensity g U z := by
  let L : ℂ →L[ℝ] E := mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun q : N => U q) z
  let P : ℂ →L[ℝ] E := mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U (z : ℂ)
  let B : E →L[ℝ] E →L[ℝ] ℝ := g.inner (U z)
  have hLP : L = P := DifferentialGeometry.mfderiv_restrict_open
    (I := 𝓘(ℝ, ℂ)) (J := 𝓘(ℝ, E)) U N z
  change Real.sqrt (B (L 1) (L 1) * B (L Complex.I) (L Complex.I) -
      B (L 1) (L Complex.I) ^ 2) =
    Real.sqrt (B (P 1) (P 1) * B (P Complex.I) (P Complex.I) -
      B (P 1) (P Complex.I) ^ 2)
  rw [hLP]

/-- The prescribed frame is orthonormal for the original induced metric and
is held fixed for every flow time. Consequently the original density and its
actual second derivative have exactly one original-density factor. This
theorem makes no frame choice and has no scalar-test or Hessian hypothesis. -/
theorem compactSupportFlow_density_eq_mul_fixed_frame [T2Space M]
    (N : TopologicalSpace.Opens ℂ) (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (U : ℂ → M)
    (hU : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (fun q : N => U q))
    (hi : ∀ q : N, Function.Injective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun p : N => U p) q))
    (z : N) (b : Module.Basis (Fin 2) ℝ (TangentSpace 𝓘(ℝ, ℂ) z))
    (hb : ∀ i j, (g.pullback (fun q : N => U q) hU hi).inner z (b i) (b j) =
      if i = j then 1 else 0)
    (X : ∀ x : M, TangentSpace 𝓘(ℝ, E) x)
    (hX : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun x : M => (⟨x, X x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hXc : HasCompactSupport X) :
    let Φ := Diffeomorph.compactSupportFlow X hX hXc
    let G := fun t => (Diffeomorph.pullbackMetric g (Φ t)).pullback
      (fun q : N => U q) hU hi
    (∀ t, riemannianAreaDensity g (Φ t ∘ U) z = riemannianAreaDensity g U z *
      tangentTwoJacobian (G t) (b 0) (b 1)) ∧
      ∀ t, deriv (deriv (fun s => riemannianAreaDensity g (Φ s ∘ U) z)) t =
        riemannianAreaDensity g U z *
          deriv (deriv (fun s => tangentTwoJacobian (G s) (b 0) (b 1))) t := by
  let Φ := Diffeomorph.compactSupportFlow X hX hXc
  let gD := g.pullback (fun q : N => U q) hU hi
  let G := fun t => (Diffeomorph.pullbackMetric g (Φ t)).pullback
    (fun q : N => U q) hU hi
  have hUd : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z :=
    DifferentialGeometry.mdifferentiableAt_subtype_iff.mp
      (hU.mdifferentiableAt (x := z) (by simp))
  have hscale (t : ℝ) : riemannianAreaDensity g (Φ t ∘ U) z =
      riemannianAreaDensity g U z * tangentTwoJacobian (G t) (b 0) (b 1) := by
    calc
      riemannianAreaDensity g (Φ t ∘ U) z =
          riemannianAreaDensity (Diffeomorph.pullbackMetric g (Φ t)) U z :=
        (riemannianAreaDensity_pullback g (Φ t) hUd).symm
      _ = tangentTwoJacobian (G t) (x := z) (1 : ℂ) Complex.I :=
        (tangentTwoJacobian_induced_complex_basis N
          (Diffeomorph.pullbackMetric g (Φ t)) U hU hi z).symm
      _ = tangentTwoJacobian gD (x := z) (1 : ℂ) Complex.I *
          tangentTwoJacobian (G t) (b 0) (b 1) :=
        tangentTwoJacobian_eq_reference_mul gD (G t) z b hb (1 : ℂ) Complex.I
      _ = _ := by rw [tangentTwoJacobian_induced_complex_basis N g U hU hi z]
  refine ⟨hscale, ?_⟩
  have hfun := funext hscale
  intro t
  rw [hfun, deriv_const_mul_field', deriv_const_mul_field]

end DifferentialGeometry.Geometry
