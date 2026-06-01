import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorNonSmoothRegularity

/-!
# Arbitrary-order interior regularity of the eigenvector chart component

For a closed Riemannian manifold `(M, g)` and ranks `(r, s)`, the chart
`P₀`-component of a resolvent eigenvector of the connection Laplacian `Δ_∇` —
`tensorL2ChartComponent g r s (tensorResolventEigenbasisVec … i) α P₀` —
satisfies a *scalar* divergence-form weak-elliptic identity with principal
symbol `weightedInvGramOnEuclid g α` (`= √(det g) · gⁱʲ`), packaged in
`eigenvectorTensorChartBilinearData`, a value of
`TensorChartBilinearH1ComplData g r s α P₀`.

The companion module `EigenvectorNonSmoothRegularity` ships the **interior
second-order regularity** of that chart component: on any interior subdomain
`Ω''` (open, relatively compact closure, with a difference-quotient room
neighbourhood inside the chart target) the chart component lies in
`MemWkp 2 2 … Ω''`. This module recasts that conclusion at the arbitrary-order
shape `MemWkp (2 * k) 2 … Ω''` and exposes the structural machinery of the
elliptic bootstrap that raises the order.

## The order shape `2k`

The requested arbitrary-`k` interior-regularity statement is
`MemWkp (2 * k) 2 … Ω''`. For `k = 0` this is `MemLp` (`W^{0,2}`) and for
`k = 1` it is `MemWkp 2 2` (`W^{2,2}`); both are immediate from the order-2
result by the downward monotonicity `MemWkp.le_of_le`. This module ships the
arbitrary-`k` headline unconditionally for `k ≤ 1`
(`eigenvector_chartComponent_memWkp_two_k`).

## The elliptic bootstrap step

The standard elliptic bootstrap raises the regularity order by differentiating
the divergence-form weak identity: a first weak partial `v := ∂_l u_chart` of a
divergence-form weak solution satisfies a *differentiated* divergence-form weak
identity with the **same** principal symbol `weightedInvGramOnEuclid g α`, the
Leibniz commutator `(∂_l weightedInvGramOnEuclid) · (∂_i u_chart)` being moved
to the right-hand side. The differentiated identity is again of the
`TensorChartBilinearH1ComplData` shape; applying the order-2 interior engine
`eigenvector_chartComponent_memWkp` / `tensor_h2_chart_loc_of_uniform_bound` to
*that* datum yields one further order, and iterating gives every order.

This module exposes the *purely structural* increment of that bootstrap. The
combinatorial increment — `MemWkp (m + 1) 2` of a function from `W^{1,2}`
membership together with `MemWkp m 2` of each of its chosen weak partials — is
the elementary `MemWkp_succ` decomposition; it is packaged here as
`memWkp_succ_of_chosenWeakPartial_memWkp`. Given a *differentiated*
chart-bilinear datum `D'` whose chart component is a.e. the relevant weak
partial of `D.u_chart`, the order-2 interior engine raises the order: this is
`tensorChartComponent_memWkp_succ_of_diffData`.

The arbitrary-`k` iteration is the repeated application of
`tensorChartComponent_memWkp_succ_of_diffData`; what it consumes at each level
— the differentiated chart-bilinear datum, together with the differentiated
right-hand side — is the residual analytic content (a per-level differentiated
variational identity for `eigenvectorChartVariationalIdentity`, with the seven-
term `eigenvectorChartRHS` propagated through a coupled regularity cascade).

## Sign convention

We follow the geometer convention `Δ_∇ = -∇* ∇`, with spectrum `⊆ (-∞, 0]`. The
resolvent is `(1 - Δ_∇)⁻¹` (spectrum `⊆ (0, 1]`).
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.ChartH2NonSmooth
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Sobolev.Chart hiding chartTargetEuclid
open DifferentialGeometry.Analysis.Sobolev.Euclidean

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)] in
/-- **Structural increment of `MemWkp` order.** A function `u` lies in
`W^{m+1,2}` of an open set `Ω` precisely when it lies in `W^{1,2}(Ω)` and each
of its canonical chosen weak `i`-partials lies in `W^{m,2}(Ω)`.

This is the elementary `MemWkp_succ` decomposition. It is the *structural* step
of the elliptic bootstrap: the analytic content (that each chosen weak partial
is itself a divergence-form weak solution of one order higher regularity) is
supplied separately. -/
private lemma memWkp_succ_of_chosenWeakPartial_memWkp
    {m : ℕ} {Ω : Set EuclN} {u : EuclN → ℝ}
    (h_w1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2 u Ω)
    (h_partials : ∀ i : Fin (Module.finrank ℝ E),
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) m 2
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
          2 i u Ω) Ω) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) (m + 1) 2 u Ω := by
  rw [DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp_succ]
  exact ⟨h_w1p, h_partials⟩

/-- **Arbitrary-order interior regularity of the eigenvector chart component,
order `2k` for `k ≤ 1` — chart-locality-free twin.**

Chart-locality-free twin of `eigenvector_chartComponent_memWkp_two_k`, re-keyed
onto the intrinsic eigenbasis vector `tensorResolventEigenbasisVec
(tensorResolventL2_isCompactOperator g r s) i`.

For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, an eigenbasis index
`i`, a chart center `α : M`, a component multi-index `P₀`, an interior subdomain
`Ω''` (open, with relatively compact closure) and a difference-quotient room
radius `R₀ > 0` with `Metric.cthickening R₀ (closure Ω'') ⊆ chartTargetEuclid α`,
the chart `P₀`-component

```
tensorL2ChartComponent g r s
  (tensorResolventEigenbasisVec
    (tensorResolventL2_isCompactOperator g r s) i) α P₀
```

of the resolvent eigenvector lies in `MemWkp (2 * k) 2 … Ω''` — it has interior
`W^{2k,2}` regularity on `Ω''` — for every `k ≤ 1`, with no chart-locality
hypothesis on the atlas.

For `k = 0` the conclusion is `W^{0,2} = L²` regularity; for `k = 1` it is the
`W^{2,2}` regularity of `eigenvector_chartComponent_memWkp`. Both
are obtained from the order-2 result by the downward monotonicity
`MemWkp.le_of_le`, since `2 * k ≤ 2` for `k ≤ 1`. -/
theorem eigenvector_chartComponent_memWkp_two_k
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    {Ω'' : Set EuclN} (hΩ''_open : IsOpen Ω'')
    (hΩ''_compact_closure : IsCompact (closure Ω''))
    {R₀ : ℝ} (hR₀_pos : 0 < R₀)
    (h_room : Metric.cthickening R₀ (closure Ω'') ⊆
      chartTargetEuclid (I := I) (M := M) α)
    {k : ℕ} (hk : k ≤ 1) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) (2 * k) 2
      (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
        (tensorResolventEigenbasisVec (I := I) (M := M)
          (DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.tensorResolventL2_isCompactOperator
            (I := I) (M := M) g r s) i) α P₀ :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω'' := by
  have h_two : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 2 2
      (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
        (tensorResolventEigenbasisVec (I := I) (M := M)
          (DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.tensorResolventL2_isCompactOperator
            (I := I) (M := M) g r s) i) α P₀ :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω'' :=
    eigenvector_chartComponent_memWkp g r s i α P₀
      hΩ''_open hΩ''_compact_closure hR₀_pos h_room
  have h_le : 2 * k ≤ 2 := by omega
  exact DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.le_of_le h_le h_two

omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)] in
/-- **Elliptic-bootstrap increment for the eigenvector chart component.**

Let `u` be the eigenvector chart component on an interior subdomain `Ω''`,
known to lie in `W^{1,2}(Ω'')`. Suppose that, for each direction `l`, the
canonical chosen weak `l`-partial `chosenWeakPartial' 2 l u Ω''` of `u` agrees
a.e. on `Ω''` with the chart component `D'_l.u_chart` of a *differentiated*
chart-bilinear datum `D'_l`, and that the order-2 interior engine has been
applied to `D'_l`, giving `MemWkp (2 * m) 2` of `D'_l.u_chart` on `Ω''`.

Then `u` lies in `MemWkp (2 * m + 1) 2 … Ω''`.

This is the structural increment of the elliptic bootstrap: the analytic
content — that each chosen weak partial of `u` is itself the chart component of
a divergence-form weak solution of one order higher — is supplied through the
hypotheses `h_diff_memWkp` and `h_diff_ae`; the conclusion assembles the next
regularity order by the elementary `MemWkp_succ` decomposition together with
the ae-invariance `MemWkp_congr_ae`. Iterating this increment is the
arbitrary-`k` interior-regularity bootstrap. -/
theorem tensorChartComponent_memWkp_succ_of_diffData
    {m : ℕ} {Ω'' : Set EuclN} (hΩ''_open : IsOpen Ω'')
    {u : EuclN → ℝ}
    (h_w1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2 u Ω'')
    {v : Fin (Module.finrank ℝ E) → EuclN → ℝ}
    (h_diff_ae : ∀ l : Fin (Module.finrank ℝ E),
      DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
        2 l u Ω'' =ᵐ[(volume : Measure EuclN).restrict Ω''] v l)
    (h_diff_memWkp : ∀ l : Fin (Module.finrank ℝ E),
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) (2 * m) 2 (v l) Ω'') :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) (2 * m + 1) 2 u Ω'' := by
  refine memWkp_succ_of_chosenWeakPartial_memWkp h_w1p (fun l => ?_)
  exact (DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp_congr_ae
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ''_open (h_diff_ae l)).mpr
      (h_diff_memWkp l)

section ElaborationTests

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)
  (i : TensorEigenIdx (I := I) (M := M) g r s)

/-- The chart-locality-free arbitrary-order headline produces interior
`MemWkp (2 * k) 2` of the eigenvector chart component for every `k ≤ 1`, with no
chart-locality hypothesis. -/
example (α : M) (P₀ : TensorCompIdx (E := E) r s)
    {Ω'' : Set EuclN} (hΩ''_open : IsOpen Ω'')
    (hΩ''_compact_closure : IsCompact (closure Ω''))
    {R₀ : ℝ} (hR₀_pos : 0 < R₀)
    (h_room : Metric.cthickening R₀ (closure Ω'') ⊆
      chartTargetEuclid (I := I) (M := M) α)
    {k : ℕ} (hk : k ≤ 1) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) (2 * k) 2
      (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
        (tensorResolventEigenbasisVec (I := I) (M := M)
          (DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.tensorResolventL2_isCompactOperator
            (I := I) (M := M) g r s) i) α P₀ :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω'' :=
  eigenvector_chartComponent_memWkp_two_k g r s i α P₀
    hΩ''_open hΩ''_compact_closure hR₀_pos h_room hk

end ElaborationTests

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
