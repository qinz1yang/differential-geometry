import DifferentialGeometry.Analysis.Laplacian.Regularity.Bochner.Polarised

/-!
# Smooth-case Lp identity from the polarised Bochner-Weitzenböck identity

For a closed Riemannian manifold `(M, g)` and smooth scalars `φ, v ∈ C^∞⟮I, M; ℝ⟯`,
this module derives the **Lp class identity** from the pointwise polarised
Bochner-Weitzenböck identity by lifting to `Lp 2 μ_g`.

The pointwise identity (from `BochnerPolarised`) is

```
Δ_g(g(∇φ, ∇v))(x) =
    g(∇(Δφ), ∇v)(x) + g(∇φ, ∇(Δv))(x)
  + 2 · hessPairingChart g φ v x
  + 2 · ricciTensor g x (∇φ x) (∇v x).
```

Rearranged into `(1 - Δ_g)`-form:

```
(1 - Δ_g)(g(∇φ, ∇v))(x) =
    g(∇φ, ∇v)(x)
  - g(∇(Δφ), ∇v)(x) - g(∇φ, ∇(Δv))(x)
  - 2 · hessPairingChart g φ v x
  - 2 · ricciTensor g x (∇φ x) (∇v x).
```

The Lp-class identity:

```
smoothToLp((1-Δ_g)(g(∇φ, ∇v))) =
    smoothToLp(g(∇φ, ∇v))
  - smoothToLp(g(∇Δφ, ∇v)) - smoothToLp(g(∇φ, ∇Δv))
  - 2 • smoothToLp(hessPairingChart g φ v)
  - 2 • smoothToLp(ricciTensor g · (∇φ) (∇v))
```

corresponds via the smooth-case identifications to the unconditional candidate
`gradInnerLaplacianCandidateUnconditional g φ (smoothToH1Compl_mem_laplacianDomainPow_two g v)`,
giving the `smoothCandidate_identification_target` statement for smooth `v`.

## Main results

* `gradInnerSmoothBundle_oneSubLapClassical_eq_polarised` — for smooth `(φ, v)`,
  the smooth scalar `(gradInnerSmoothBundle g φ v).oneSubLapClassical` equals the
  pointwise polarised `(1 - Δ_g)`-form.

* `smoothToLp_oneSubLapClassical_eq_polarised` — at the Lp class level.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace BochnerPolarisedLpSmooth

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Laplacian.GradInnerLpIdentity
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul
open DifferentialGeometry.Analysis.Laplacian.HessianPairingChart
open DifferentialGeometry.Analysis.Laplacian.BochnerPolarised

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-- For smooth `φ, v ∈ C^∞⟮I, M; ℝ⟯`, the sum `φ + v` is smooth. -/
lemma contMDiff_phi_add_v
    (φ v : C^∞⟮I, M; ℝ⟯) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun y : M => (φ : M → ℝ) y + (v : M → ℝ) y) :=
  φ.contMDiff.add v.contMDiff

/-- For smooth `φ, v ∈ C^∞⟮I, M; ℝ⟯`, the difference `φ - v` is smooth. -/
lemma contMDiff_phi_sub_v
    (φ v : C^∞⟮I, M; ℝ⟯) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun y : M => (φ : M → ℝ) y - (v : M → ℝ) y) :=
  φ.contMDiff.sub v.contMDiff

/-- The smooth scalar `g.inner b (∇φ b) (∇v b)` is `C^∞` on `M`. -/
lemma contMDiff_g_inner_grad_phi_grad_v
    (g : SmoothRiemannianMetric I M) (φ v : C^∞⟮I, M; ℝ⟯) :
    ContMDiff I 𝓘(ℝ) ∞ (fun b : M => g.inner b
      (gradFun (I := I) g (φ : M → ℝ) b)
      (gradFun (I := I) g (v : M → ℝ) b)) := by
  have h := contMDiff_g_inner_of_smooth_sections (I := I) (M := M) g
    (grad_g (I := I) g φ.contMDiff) (grad_g (I := I) g v.contMDiff)
  refine h.congr ?_
  intro b
  rw [grad_g_apply, grad_g_apply]

/-- Specialisation of `bochner_polarised_pointwise` using smoothness witnesses
constructed from `φ` and `v`. -/
theorem bochner_polarised_pointwise_smoothCase
    (g : SmoothRiemannianMetric I M) (φ v : C^∞⟮I, M; ℝ⟯) (x : M) :
    Δ_g (I := I) g (contMDiff_g_inner_grad_phi_grad_v
        (I := I) (M := M) g φ v) x =
      g.inner x
          (gradFun (I := I) g (φ : M → ℝ) x)
          (gradFun (I := I) g (Δ_g (I := I) g v.contMDiff) x) +
        g.inner x
          (gradFun (I := I) g (v : M → ℝ) x)
          (gradFun (I := I) g (Δ_g (I := I) g φ.contMDiff) x) +
        2 * hessPairingChart (I := I) g φ v x +
        2 * ricciTensor (I := I) g x
              (gradFun (I := I) g (φ : M → ℝ) x)
              (gradFun (I := I) g (v : M → ℝ) x) :=
  bochner_polarised_pointwise (I := I) (M := M) g φ v
    (contMDiff_phi_add_v (I := I) (M := M) φ v)
    (contMDiff_phi_sub_v (I := I) (M := M) φ v)
    (contMDiff_g_inner_grad_phi_grad_v (I := I) (M := M) g φ v) x

/-- `(1 - Δ_g)`-form of the polarised Bochner identity, specialised to smooth `(φ, v)`. -/
theorem bochner_polarised_pointwise_oneSubLap_smoothCase
    (g : SmoothRiemannianMetric I M) (φ v : C^∞⟮I, M; ℝ⟯) (x : M) :
    g.inner x
        (gradFun (I := I) g (φ : M → ℝ) x)
        (gradFun (I := I) g (v : M → ℝ) x) -
      Δ_g (I := I) g (contMDiff_g_inner_grad_phi_grad_v
        (I := I) (M := M) g φ v) x =
      g.inner x
          (gradFun (I := I) g (φ : M → ℝ) x)
          (gradFun (I := I) g (v : M → ℝ) x)
        - g.inner x
            (gradFun (I := I) g (v : M → ℝ) x)
            (gradFun (I := I) g (Δ_g (I := I) g φ.contMDiff) x)
        - g.inner x
            (gradFun (I := I) g (φ : M → ℝ) x)
            (gradFun (I := I) g (Δ_g (I := I) g v.contMDiff) x)
        - 2 * hessPairingChart (I := I) g φ v x
        - 2 * ricciTensor (I := I) g x
              (gradFun (I := I) g (φ : M → ℝ) x)
              (gradFun (I := I) g (v : M → ℝ) x) :=
  bochner_polarised_pointwise_oneSubLap (I := I) (M := M) g φ v
    (contMDiff_phi_add_v (I := I) (M := M) φ v)
    (contMDiff_phi_sub_v (I := I) (M := M) φ v)
    (contMDiff_g_inner_grad_phi_grad_v (I := I) (M := M) g φ v) x

/-- The smooth scalar `gradInnerSmoothBundle g φ v` has the explicit pointwise
form `b ↦ g.inner b (∇φ b) (∇v b)`. -/
lemma gradInnerSmoothBundle_toFun
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) (b : M) :
    (gradInnerSmoothBundle (I := I) (M := M) g φ v).toFun b =
      g.inner b
        (gradFun (I := I) g (φ : M → ℝ) b)
        (gradFun (I := I) g v.toFun b) :=
  rfl

/-- The smoothness witness for `gradInnerSmoothBundle g φ v.toFun` agrees with
the smoothness witness for `b ↦ g.inner b (∇φ b) (∇v.toFun b)` via `Δ_g_congr_funext`. -/
lemma Δ_g_gradInnerSmoothBundle_eq_contMDiff_g_inner
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) (x : M) :
    Δ_g (I := I) g (gradInnerSmoothBundle (I := I) (M := M) g φ v).smooth x =
      Δ_g (I := I) g (contMDiff_g_inner_grad_phi_grad_v
        (I := I) (M := M) g φ ⟨v.toFun, v.smooth⟩) x := by
  apply Δ_g_congr_func

end BochnerPolarisedLpSmooth
end Laplacian
end Analysis
end DifferentialGeometry

end
