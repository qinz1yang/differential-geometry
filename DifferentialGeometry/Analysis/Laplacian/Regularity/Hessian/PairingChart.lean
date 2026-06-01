import DifferentialGeometry.Analysis.Laplacian.Lichnerowicz
import DifferentialGeometry.Analysis.Laplacian.Regularity.Hessian.LpClass

/-!
# Pointwise Hessian-Frobenius pairing of two smooth scalars

For smooth scalars `φ, v : C^∞(M, ℝ)` on a closed Riemannian manifold `(M, g)`,
the pointwise Hilbert-Schmidt inner product

```
b ↦ ⟨∇²φ(b), ∇²v(b)⟩_g
```

is continuous on `M` (compact). We define this pairing via the polarization
identity from `chartHessFrobeniusSq`:

```
4 ⟨A, B⟩ = ⟨A+B, A+B⟩ - ⟨A-B, A-B⟩.
```

Specifically, `4 * hessPairingSmooth g φ v b = chartHessFrobeniusSq g (φ+v) b
- chartHessFrobeniusSq g (φ-v) b`. The continuity follows from continuity of
`chartHessFrobeniusSq` (established in `Lichnerowicz.lean`).

## Main definitions

* `hessPairingChart g φ v` — the pointwise Hess Frobenius pairing of two
  smooth scalars, defined via polarization.

## Main results

* `hessPairingChart_continuous` — continuity on `M` for smooth `φ, v`.
* `hessPairingChart_memLp_two` — `Lp 2` membership on compact `M`.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace HessianPairingChart

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Connection

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-- The pointwise Hess-Frobenius pairing of two smooth scalars `φ, v` at a
point `b : M`, defined via polarization of the Frobenius norm squared. -/
noncomputable def hessPairingChart
    (g : SmoothRiemannianMetric I M) (φ v : C^∞⟮I, M; ℝ⟯) (b : M) : ℝ :=
  (chartHessFrobeniusSq (I := I) g
        (fun x : M => φ x + v x) b -
      chartHessFrobeniusSq (I := I) g
        (fun x : M => φ x - v x) b) / 4

@[simp] lemma hessPairingChart_def
    (g : SmoothRiemannianMetric I M) (φ v : C^∞⟮I, M; ℝ⟯) (b : M) :
    hessPairingChart (I := I) g φ v b =
      (chartHessFrobeniusSq (I := I) g
            (fun x : M => φ x + v x) b -
          chartHessFrobeniusSq (I := I) g
            (fun x : M => φ x - v x) b) / 4 := rfl

/-- The smoothness of `φ + v` as `M → ℝ`. -/
private lemma smoothAddOfTwoSmooth
    (φ v : C^∞⟮I, M; ℝ⟯) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x : M => φ x + v x) :=
  φ.contMDiff.add v.contMDiff

/-- The smoothness of `φ - v` as `M → ℝ`. -/
private lemma smoothSubOfTwoSmooth
    (φ v : C^∞⟮I, M; ℝ⟯) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x : M => φ x - v x) :=
  φ.contMDiff.sub v.contMDiff

/-- **Continuity of `hessPairingChart`.** For smooth `φ, v`, the pointwise
Hess pairing is continuous on `M`. -/
theorem hessPairingChart_continuous
    (g : SmoothRiemannianMetric I M) (φ v : C^∞⟮I, M; ℝ⟯) :
    Continuous (hessPairingChart (I := I) g φ v) := by
  classical
  unfold hessPairingChart
  have h1 := chartHessFrobeniusSq_continuous (I := I) g
    (smoothAddOfTwoSmooth (I := I) φ v)
  have h2 := chartHessFrobeniusSq_continuous (I := I) g
    (smoothSubOfTwoSmooth (I := I) φ v)
  exact (h1.sub h2).div_const 4

/-- `hessPairingChart` is in `Lp 2 μ_g` on the compact manifold. -/
theorem hessPairingChart_memLp_two
    (g : SmoothRiemannianMetric I M) (φ v : C^∞⟮I, M; ℝ⟯) :
    MemLp (hessPairingChart (I := I) g φ v) 2
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
  haveI : IsFiniteMeasureOnCompacts (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasureOnCompacts (I := I) (M := M) g
  exact (hessPairingChart_continuous (I := I) g φ v).memLp_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- Coerce a `SmoothScalar g` to a `C^∞⟮I, M; ℝ⟯` bundled smooth function. -/
noncomputable def smoothScalarToContMDiffMap
    {g : SmoothRiemannianMetric I M} (v : SmoothScalar g) : C^∞⟮I, M; ℝ⟯ :=
  ⟨v.toFun, v.smooth⟩

/-- The `Lp 2` class of the Hess pairing of smooth `φ : C^∞⟮I, M; ℝ⟯` and
`v : SmoothScalar g`. -/
noncomputable def hessPairingSmoothLp
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
  (hessPairingChart_memLp_two (I := I) g φ
      (smoothScalarToContMDiffMap (I := I) (g := g) v)).toLp _

@[simp] lemma hessPairingSmoothLp_def
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    hessPairingSmoothLp (I := I) (M := M) g φ v =
      (hessPairingChart_memLp_two (I := I) g φ
        (smoothScalarToContMDiffMap (I := I) (g := g) v)).toLp _ := rfl

/-- A.e. unfolding identity: `hessPairingSmoothLp g φ v` represents the
pointwise Hess pairing as an `Lp` class. -/
lemma hessPairingSmoothLp_coeFn
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    (hessPairingSmoothLp (I := I) (M := M) g φ v :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g]
      (hessPairingChart (I := I) g φ
        (smoothScalarToContMDiffMap (I := I) (g := g) v)) :=
  MemLp.coeFn_toLp _

end HessianPairingChart
end Laplacian
end Analysis
end DifferentialGeometry

end
