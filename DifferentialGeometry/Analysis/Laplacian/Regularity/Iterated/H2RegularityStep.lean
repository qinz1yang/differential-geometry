import DifferentialGeometry.Analysis.Laplacian.Regularity.Iterated.H2Regularity

/-!
# Iterated `H²` regularity step for the iterated Laplacian domain

For a closed Riemannian manifold `(M, g)`, this file establishes the
iterative `H²` regularity step at level `k = 2`:

For `u_h ∈ laplacianDomainPow g 2`, both the canonical function
representative `((H1ComplToLp u_h) : M → ℝ)` *and* the canonical function
representative of the `Lp`-side preimage (i.e. `(1-Δ_g) u_h`) lie in
`MemWkpChart g 2 2`.

## Why two-sided `H²` regularity?

`laplacianDomainPow g 2` is defined as the range of
`resolvent g ∘ resolventL2 g` on `Lp`. Explicitly, if
`u_h = resolvent g (resolventL2 g f)` for some `f ∈ Lp`, then:

* `u_h ∈ laplacianDomain g`, with `laplacianDomain.preimage u_h = resolventL2 g f`.
* `laplacianDomain.preimage u_h = H1ComplToLp g (resolvent g f)`, and
  `resolvent g f ∈ laplacianDomain g`.

So `u_h ∈ laplacianDomainPow g 2` is equivalent to: `u_h ∈ laplacianDomain g`
*and* there exists `w_h ∈ laplacianDomain g` with
`H1ComplToLp g w_h = laplacianDomain.preimage u_h`.

The single-step `C` result (`iteratedH2Regularity_one` /
`laplacianDomain_memWkpChart_two_unconditional`) applied to both `u_h` and
`w_h` therefore yields the two-sided `H²` regularity for free.

## Strategy

1. By `laplacianDomainPow_succ_mem_iff`, extract `f : Lp` with
   `u_h = resolvent g (resolventL2 g f)`.
2. Set `w_h := resolvent g f ∈ laplacianDomain g`. Then
   `H1ComplToLp g w_h = resolventL2 g f` is the canonical `Lp`-preimage
   of `u_h` under the `H1Compl`-side resolvent.
3. Apply `iteratedH2Regularity_one` to both `u_h` and `w_h`.
4. Bridge `H1ComplToLp g w_h` ↔ `laplacianDomain.preimage u_h` via
   `resolvent_injective`.

## Higher-order regularity (`H⁴`, `H^{2k}`)

A genuine bootstrap to `MemWkpChart g 4 2` would require differentiating
the chart-bilinear identity and constructing a "differentiated"
chart-bilinear data structure for each weak first partial `∂_l u_chart`,
together with a re-application of the chart-local difference-quotient
regularity. This is the standard Nirenberg–Schauder bootstrap, but
requires substantial additional chart-bilinear infrastructure (chain
rules for the bilinear identity coefficients, support handling of cutoff
derivatives, and uniform `L²` control of the lower-order corrections).
That bootstrap is deferred to a later module.

The result delivered here is the cleanest unconditional consequence of
`u_h ∈ laplacianDomainPow g 2` available from the single-step `H²`
regularity: it gives `H²` regularity at both ends of the
`(1-Δ_g)`-preimage chain.

## Main result

* `laplacianDomainPow_two_h2_plus_rhs_h2` — for
  `u_h ∈ laplacianDomainPow g 2`, both the canonical function
  representative of `u_h` and the canonical function representative of
  `laplacianDomain.preimage u_h` lie in `MemWkpChart g 2 2`, with finite
  chart-based norms.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Sobolev.Chart

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

/-- For `u_h ∈ laplacianDomainPow g 2`, the `Lp`-preimage
`laplacianDomain.preimage` of `u_h` equals `H1ComplToLp g w_h` for some
`w_h ∈ laplacianDomain g`. -/
theorem laplacianDomainPow_two_preimage_eq
    (g : SmoothRiemannianMetric I M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    ∃ w_h : H1Compl (I := I) (M := M) g,
      w_h ∈ laplacianDomain (I := I) (M := M) g ∧
      H1ComplToLp (I := I) (M := M) g w_h =
        laplacianDomain.preimage (I := I) (M := M) g
          ⟨u_h, laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1 hu_h⟩ := by
  rw [show (2 : ℕ) = 1 + 1 from rfl] at hu_h
  rw [laplacianDomainPow_succ_mem_iff] at hu_h
  obtain ⟨f, hf⟩ := hu_h
  rw [iteratedResolventL2_one] at hf
  refine ⟨resolvent (I := I) (M := M) g f, ?_, ?_⟩
  · rw [laplacianDomain_mem_iff]
    exact ⟨f, rfl⟩
  · have h_resolventL2_apply : resolventL2 (I := I) (M := M) g f =
        H1ComplToLp (I := I) (M := M) g (resolvent (I := I) (M := M) g f) := by
      rfl
    apply resolvent_injective (I := I) (M := M) g
    rw [resolvent_laplacianDomain_preimage_eq]
    rw [← h_resolventL2_apply]
    exact hf.symm

/-- **Two-sided `H²` regularity for `u_h ∈ laplacianDomainPow g 2`.**

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)`
and any `u_h ∈ laplacianDomainPow g 2`, two membership claims hold:

* The canonical function representative `((H1ComplToLp u_h) : M → ℝ)`
  lies in `MemWkpChart g 2 2`, with a finite chart-based norm.

* The canonical function representative of the `Lp` preimage
  `laplacianDomain.preimage u_h` (which represents `(1 - Δ_g) u_h` as an
  `Lp` class) lies in `MemWkpChart g 2 2`, with a finite chart-based norm.

Both claims follow by applying the single-step `H²` regularity
(`iteratedH2Regularity_one`) to the two `H¹`-side elements of the
`(1-Δ_g)`-preimage chain. -/
theorem laplacianDomainPow_two_h2_plus_rhs_h2
    (g : SmoothRiemannianMetric I M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    (DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
        (I := I) (M := M) g 2 2
        ((H1ComplToLp (I := I) (M := M) g u_h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) ∧
      DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChart
        (I := I) (M := M) g 2 2
        ((H1ComplToLp (I := I) (M := M) g u_h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) < ⊤) ∧
    (DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
        (I := I) (M := M) g 2 2
        ((laplacianDomain.preimage (I := I) (M := M) g
            ⟨u_h, laplacianDomainPow_succ_subset_laplacianDomain
              (I := I) (M := M) g 1 hu_h⟩ :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) ∧
      DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChart
        (I := I) (M := M) g 2 2
        ((laplacianDomain.preimage (I := I) (M := M) g
            ⟨u_h, laplacianDomainPow_succ_subset_laplacianDomain
              (I := I) (M := M) g 1 hu_h⟩ :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) < ⊤) := by
  have hu_h_dom : u_h ∈ laplacianDomain (I := I) (M := M) g :=
    laplacianDomainPow_succ_subset_laplacianDomain (I := I) (M := M) g 1 hu_h
  have hu_h_in_pow_one : u_h ∈ laplacianDomainPow (I := I) (M := M) g 1 := by
    rw [laplacianDomainPow_one]; exact hu_h_dom
  have h_u_h2 := iteratedH2Regularity_one (I := I) (M := M) g hu_h_in_pow_one
  obtain ⟨w_h, hw_h_dom, hw_h_eq⟩ :=
    laplacianDomainPow_two_preimage_eq (I := I) (M := M) g hu_h
  have hw_h_in_pow_one : w_h ∈ laplacianDomainPow (I := I) (M := M) g 1 := by
    rw [laplacianDomainPow_one]; exact hw_h_dom
  have h_w_h2 := iteratedH2Regularity_one (I := I) (M := M) g hw_h_in_pow_one
  refine ⟨h_u_h2, ?_⟩
  rw [show (laplacianDomain.preimage (I := I) (M := M) g
        ⟨u_h, laplacianDomainPow_succ_subset_laplacianDomain
          (I := I) (M := M) g 1 hu_h⟩) =
      H1ComplToLp (I := I) (M := M) g w_h from hw_h_eq.symm]
  exact h_w_h2

/-- Restated form. The first conjunct is the same as `iteratedH2Regularity_one`
applied to `u_h`. The second conjunct says: the canonical function
representative of the `Lp` element `(1 - Δ_g) u_h`, interpreted as
`laplacianDomain.preimage u_h`, lies in `MemWkpChart g 2 2`. -/
theorem laplacianDomainPow_two_iterated_h2
    (g : SmoothRiemannianMetric I M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) g 2 2
      ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) ∧
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) g 2 2
      ((laplacianDomain.preimage (I := I) (M := M) g
          ⟨u_h, laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1 hu_h⟩ :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) := by
  have h := laplacianDomainPow_two_h2_plus_rhs_h2 (I := I) (M := M) g hu_h
  exact ⟨h.1.1, h.2.1⟩

end Laplacian
end Analysis
end DifferentialGeometry

end
