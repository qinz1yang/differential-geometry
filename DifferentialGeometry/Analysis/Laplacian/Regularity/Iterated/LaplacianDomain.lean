import DifferentialGeometry.Analysis.Laplacian.Regularity.LaplacianDomain.PerChartWitness
import DifferentialGeometry.Analysis.Laplacian.Spectral.Resolvent

/-!
# Iterated Laplacian domain

For a closed Riemannian manifold `(M, g)`, this file defines the iterated
Laplacian domain `laplacianDomainPow g k : Submodule ℝ (H1Compl g)`.

## Definition strategy

We define `laplacianDomainPow g k` via the iterated `Lp`-side resolvent
operator. Recall:

* `resolvent g : Lp ℝ 2 μ_g →L[ℝ] H1Compl g` — the `H¹`-side resolvent.
* `H1ComplToLp g : H1Compl g →L[ℝ] Lp ℝ 2 μ_g` — the inclusion.
* `resolventL2 g := H1ComplToLp g ∘L resolvent g : Lp →L[ℝ] Lp` —
  the `L²`-side resolvent `(1 - Δ_g)⁻¹` on `L²`.

The `k`-th iterated Laplacian domain is

  `laplacianDomainPow g k :=`
  `  LinearMap.range (resolvent g ∘L (resolventL2 g)^k)` (for `k ≥ 1`)

with `laplacianDomainPow g 0 := ⊤` (the whole `H1Compl g`).

Equivalently:

* `u_h ∈ laplacianDomainPow g 1` iff `u_h ∈ laplacianDomain g`.
* `u_h ∈ laplacianDomainPow g (k+1)` iff there is `f ∈ Lp ℝ 2 μ_g` with
  `u_h = resolvent g ((resolventL2 g)^k f)`.

## Main definitions

* `iteratedResolventL2 g k : Lp →L[ℝ] Lp` — `(resolventL2 g)^k`.
* `laplacianDomainPow g k : Submodule ℝ (H1Compl g)` — the `k`-th iterated
  Laplacian domain.

## Main results

* `laplacianDomainPow_zero`: `laplacianDomainPow g 0 = ⊤`.
* `laplacianDomainPow_one`: `laplacianDomainPow g 1 = laplacianDomain g`.
* `laplacianDomainPow_succ_subset_laplacianDomain`: for `k ≥ 1`,
  `laplacianDomainPow g k ⊆ laplacianDomain g`.
* `laplacianDomainPow_mem_iff`: characterisation of membership.

## Sign convention

We follow the geometer convention `Δ_g = div_g ∘ grad_g`. The resolvent is
`(1 - Δ_g)⁻¹`. The `k`-th iterated resolvent is `(1 - Δ_g)^{-k}`.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

/-- The `k`-th iterated `L²`-side resolvent: `(1 - Δ_g)^{-k}` acting on
`Lp ℝ 2 μ_g`. Defined as the `k`-fold composition of `resolventL2 g`. -/
noncomputable def iteratedResolventL2 (g : SmoothRiemannianMetric I M) (k : ℕ) :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) →L[ℝ]
      Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
  Nat.recAux (motive := fun _ =>
    Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) →L[ℝ]
      Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
    (ContinuousLinearMap.id ℝ _)
    (fun _ prev => (resolventL2 (I := I) (M := M) g).comp prev) k

@[simp] lemma iteratedResolventL2_zero (g : SmoothRiemannianMetric I M) :
    iteratedResolventL2 (I := I) (M := M) g 0 =
      ContinuousLinearMap.id ℝ _ := rfl

@[simp] lemma iteratedResolventL2_succ (g : SmoothRiemannianMetric I M) (k : ℕ) :
    iteratedResolventL2 (I := I) (M := M) g (k + 1) =
      (resolventL2 (I := I) (M := M) g).comp
        (iteratedResolventL2 (I := I) (M := M) g k) := rfl

lemma iteratedResolventL2_one (g : SmoothRiemannianMetric I M) :
    iteratedResolventL2 (I := I) (M := M) g 1 =
      resolventL2 (I := I) (M := M) g := by
  rw [iteratedResolventL2_succ]
  rw [iteratedResolventL2_zero]
  exact ContinuousLinearMap.comp_id _

@[simp] lemma iteratedResolventL2_zero_apply (g : SmoothRiemannianMetric I M)
    (f : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    iteratedResolventL2 (I := I) (M := M) g 0 f = f := rfl

lemma iteratedResolventL2_succ_apply (g : SmoothRiemannianMetric I M) (k : ℕ)
    (f : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    iteratedResolventL2 (I := I) (M := M) g (k + 1) f =
      resolventL2 (I := I) (M := M) g
        (iteratedResolventL2 (I := I) (M := M) g k f) := rfl

/-- The composition law `(resolventL2 g)^(j+k) = (resolventL2 g)^j ∘L (resolventL2 g)^k`. -/
lemma iteratedResolventL2_add (g : SmoothRiemannianMetric I M) (j k : ℕ) :
    iteratedResolventL2 (I := I) (M := M) g (j + k) =
      (iteratedResolventL2 (I := I) (M := M) g j).comp
        (iteratedResolventL2 (I := I) (M := M) g k) := by
  induction j with
  | zero => simp [iteratedResolventL2_zero]
  | succ j ih =>
    rw [Nat.succ_add, iteratedResolventL2_succ, iteratedResolventL2_succ, ih]
    rw [ContinuousLinearMap.comp_assoc]

/-- The `k`-th iterated Laplacian domain: the image of the composition
`resolvent g ∘ iteratedResolventL2 g (k-1)` for `k ≥ 1`, and the whole
`H1Compl g` for `k = 0`.

Equivalently, `u_h ∈ laplacianDomainPow g k` iff `(1 - Δ_g)^k u_h ∈ Lp`, with
the convention that for `k = 0` the condition is vacuous. -/
noncomputable def laplacianDomainPow (g : SmoothRiemannianMetric I M) (k : ℕ) :
    Submodule ℝ (H1Compl (I := I) (M := M) g) :=
  Nat.recAux (motive := fun _ => Submodule ℝ (H1Compl (I := I) (M := M) g))
    ⊤
    (fun k _ => LinearMap.range
      ((resolvent (I := I) (M := M) g).toLinearMap.comp
        (iteratedResolventL2 (I := I) (M := M) g k).toLinearMap)) k

@[simp] lemma laplacianDomainPow_zero (g : SmoothRiemannianMetric I M) :
    laplacianDomainPow (I := I) (M := M) g 0 = ⊤ := rfl

lemma laplacianDomainPow_succ (g : SmoothRiemannianMetric I M) (k : ℕ) :
    laplacianDomainPow (I := I) (M := M) g (k + 1) =
      LinearMap.range
        ((resolvent (I := I) (M := M) g).toLinearMap.comp
          (iteratedResolventL2 (I := I) (M := M) g k).toLinearMap) := rfl

/-- For `k = 1`, the iterated Laplacian domain equals the ordinary
Laplacian domain. -/
lemma laplacianDomainPow_one (g : SmoothRiemannianMetric I M) :
    laplacianDomainPow (I := I) (M := M) g 1 =
      laplacianDomain (I := I) (M := M) g := by
  rw [laplacianDomainPow_succ]
  unfold laplacianDomain
  rw [iteratedResolventL2_zero]
  rfl

/-- Membership characterisation for `k + 1`: `u_h ∈ laplacianDomainPow g (k+1)`
iff there is `f ∈ Lp ℝ 2 μ_g` with `u_h = resolvent g (iteratedResolventL2 g k f)`. -/
lemma laplacianDomainPow_succ_mem_iff (g : SmoothRiemannianMetric I M) (k : ℕ)
    {u : H1Compl (I := I) (M := M) g} :
    u ∈ laplacianDomainPow (I := I) (M := M) g (k + 1) ↔
      ∃ f : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g),
        u = resolvent (I := I) (M := M) g
          (iteratedResolventL2 (I := I) (M := M) g k f) := by
  rw [laplacianDomainPow_succ]
  rw [LinearMap.mem_range]
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨f, ?_⟩
    simp only [LinearMap.coe_comp, Function.comp_apply,
      ContinuousLinearMap.coe_coe] at hf
    exact hf.symm
  · rintro ⟨f, hf⟩
    refine ⟨f, ?_⟩
    simp only [LinearMap.coe_comp, Function.comp_apply,
      ContinuousLinearMap.coe_coe]
    exact hf.symm

/-- For `k ≥ 1`, `laplacianDomainPow g k ⊆ laplacianDomain g`.

This is because every element of `laplacianDomainPow g (k+1)` is the image of
some `Lp` element under the resolvent. -/
lemma laplacianDomainPow_succ_subset_laplacianDomain
    (g : SmoothRiemannianMetric I M) (k : ℕ) :
    (laplacianDomainPow (I := I) (M := M) g (k + 1) : Set (H1Compl g)) ⊆
      (laplacianDomain (I := I) (M := M) g : Set (H1Compl g)) := by
  intro u hu
  rw [SetLike.mem_coe, laplacianDomainPow_succ_mem_iff] at hu
  obtain ⟨f, hf⟩ := hu
  rw [SetLike.mem_coe]
  rw [laplacianDomain_mem_iff]
  exact ⟨iteratedResolventL2 (I := I) (M := M) g k f, hf⟩

/-- For `u ∈ laplacianDomainPow g (k+1)`, the canonical preimage
`laplacianDomain.preimage u` (which is `(1 - Δ_g) u` in `L²`) lies in the
range of `iteratedResolventL2 g k`. -/
lemma laplacianDomainPow_succ_preimage_in_range
    (g : SmoothRiemannianMetric I M) (k : ℕ)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g (k + 1)) :
    laplacianDomain.preimage (I := I) (M := M) g
        ⟨u_h, laplacianDomainPow_succ_subset_laplacianDomain
          (I := I) (M := M) g k hu_h⟩ ∈
      LinearMap.range
        (iteratedResolventL2 (I := I) (M := M) g k).toLinearMap := by
  rw [laplacianDomainPow_succ_mem_iff] at hu_h
  obtain ⟨f, hf⟩ := hu_h
  rw [LinearMap.mem_range]
  refine ⟨f, ?_⟩
  apply resolvent_injective (I := I) (M := M) g
  rw [resolvent_laplacianDomain_preimage_eq]
  exact hf.symm

example (g : SmoothRiemannianMetric I M) :
    Submodule ℝ (H1Compl (I := I) (M := M) g) :=
  laplacianDomainPow (I := I) (M := M) g 0

example (g : SmoothRiemannianMetric I M) :
    laplacianDomainPow (I := I) (M := M) g 1 =
      laplacianDomain (I := I) (M := M) g :=
  laplacianDomainPow_one (I := I) (M := M) g

end Laplacian
end Analysis
end DifferentialGeometry

end
