import DifferentialGeometry.Analysis.Laplacian.TensorRegularity.Bootstrap
import DifferentialGeometry.Analysis.Laplacian.TensorRegularity.BootstrapMixed
import DifferentialGeometry.Analysis.Laplacian.TensorRegularity.BootstrapStep

/-!
# All-orders interior elliptic-system regularity of connection-Laplacian tensor
# weak solutions

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)`, ranks
`(r, s)`, a chart center `α : M`, a component multi-index `P₀`, and a pair of
chart-supported smooth compactly-supported `(r, s)`-tensor sections `T` (the
solution) and `F` (the source) satisfying the global `H¹` weak equation
`∫_M ⟨∇T, ∇v⟩ dμ_g = ⟨F, v⟩_{L²}` of the connection Laplacian, this file ships
the **unconditional, all-orders** interior Sobolev regularity of the Euclidean
chart component `tensorComponentEuclid g r s T α P₀`: it lies in `MemWkp (2k+2) 2`
on every precompact interior subdomain `Ω''`, for *every* order `k : ℕ`, with no
chart-selection / uniform-atlas hypothesis (`HasLocallyConstantChartAt` or any
analog) anywhere in the file.

## The elliptic-system coupling, handled honestly

The connection Laplacian `Δ_∇` on an `(r, s)`-tensor is **not** the scalar
Laplacian applied component-by-component. In a chart, the Weitzenböck / Bochner
expansion writes `(Δ_∇ T)`'s frame components as the scalar (metric) Laplacian
of the component plus a **lower-order** coupling among all the components
(Christoffel- and curvature-weighted first- and zeroth-order terms). The chart
components therefore solve an elliptic **system** with lower-order coupling, not
a decoupled family of scalar equations.

The infrastructure that captures this coupling without any approximation is the
chain
```
  tensorComponent_isSmoothWeakSolution           (WeakSolutionHeadline.lean)
  tensorComponent_iterated_partial_isSmoothWeakSolution   (BootstrapMixed.lean)
```
The first exhibits each Euclidean chart component as a smooth weak solution of
the **principal-part** scalar elliptic form `tensorPrincipalForm g α …` against
the explicit right-hand side `tensorComponentWeakRHS …`, into which the
component-coupled lower-order Weitzenböck terms are folded. The second iterates
this: every classical mixed partial `iterClassicalPartial m idx (component)` is
itself a smooth weak solution of the *same* principal form, against the iterated
perturbed source `iteratedPerturbedSource (tensorPrincipalForm …) m … idx` —
which is again smooth, with the coupling having been transported one order down
at each differentiation step. Because the principal part is identical at every
order, the scalar interior `H²` engine `smooth_cc_h2_loc_memWkp_two` applies
verbatim to every iterated partial, and the order-by-order assembly is the
generic Sobolev arithmetic of `memWkp_of_iterClassicalPartial_memWkp_two` below.

## Main results

* `memWkp_succ_of_classicalPartial_memWkp` — generic scalar order-raiser: a
  smooth `u ∈ L²(Ω)` all of whose classical partials `∂_l u` lie in `W^{k,2}(Ω)`
  lies in `W^{k+1,2}(Ω)`.
* `memWkp_of_iterClassicalPartial_memWkp_two` — generic scalar bootstrap: a
  smooth `u ∈ W^{m,2}(Ω)` all of whose `m`-fold classical partials lie in
  `W^{2,2}(Ω)` lies in `W^{m+2,2}(Ω)`.
* `iterClassicalPartial_memWkp_two_of_weakSolution` — every iterated chart
  partial of a connection-Laplacian weak-solution component lies in `W^{2,2}`
  on a precompact interior subdomain (the scalar interior `H²` engine applied to
  the iterated weak-solution identity).
* `tensorComponent_memWkp_allOrders_interior` — the **all-orders headline**: the
  Euclidean chart component lies in `MemWkp (2k+2) 2 Ω''` for every `k : ℕ`, on
  every precompact interior subdomain, unconditionally.

## Sign convention

Geometer Laplacian `Δ_∇ = -∇*∇`, spectrum `⊆ (-∞, 0]`; the resolvent is
`(1 - Δ_∇)⁻¹`.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Bundle Manifold Set Filter MeasureTheory
open scoped Manifold Topology ContDiff BigOperators ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace TensorRegularity

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean

section GenericRaiser

variable {d : ℕ} [NeZero d]

local notation "EE" => EuclideanSpace ℝ (Fin d)

/-- **Generic scalar order-raiser.** For a smooth function `u` on an open set
`Ω ⊆ EuclideanSpace ℝ (Fin d)` that lies in `L²(Ω)` and all of whose classical
partials `∂_l u` lie in `W^{k,2}(Ω)`, `u` lies in `W^{k+1,2}(Ω)`.

The proof unfolds `MemWkp (k+1)` to its recursive characterisation `MemW1p u ∧
∀ l, chosenWeakPartial l u ∈ W^{k,2}`. For smooth `u`, the chosen weak partial
agrees a.e. with the classical partial `∂_l u`, so the hypothesis on the
classical partials transfers; the `MemW1p` part follows from the `L²` membership
of `u` (the classical partials are weak partials of the smooth `u`, lying in
`L²` since they lie in `W^{k,2} ⊆ L²`). -/
theorem memWkp_succ_of_classicalPartial_memWkp
    (k : ℕ) {Ω : Set EE} (hΩ_open : IsOpen Ω)
    {u : EE → ℝ} (hu_smooth : ContDiff ℝ (⊤ : ℕ∞) u)
    (hu_L2 : MemLp u 2 (volume.restrict Ω))
    (h_partial : ∀ l : Fin d,
      MemWkp (d := d) k 2
        (fun x => (fderiv ℝ u x) (EuclideanSpace.single l 1)) Ω) :
    MemWkp (d := d) (k + 1) 2 u Ω := by
  classical
  rw [MemWkp_succ]
  have hu_W1 : DeGiorgi.MemW1p (d := d) 2 u Ω := by
    refine ⟨hu_L2, fun i => ?_⟩
    refine ⟨fun x => (fderiv ℝ u x) (EuclideanSpace.single i 1), ?_, ?_⟩
    · exact (h_partial i).memLp
    · exact DeGiorgi.HasWeakPartialDeriv.of_contDiff hΩ_open
        (hu_smooth.of_le (by norm_cast))
  refine ⟨hu_W1, fun i => ?_⟩
  have h_ae := chosenWeakPartial_smooth_ae_eq (d := d)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open hu_smooth hu_W1 i
  exact (MemWkp_congr_ae (d := d) (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_ae).mpr
    (h_partial i)

/-- **Generic scalar all-orders bootstrap.** For a smooth function `u` on an open
set `Ω ⊆ EuclideanSpace ℝ (Fin d)` that already lies in `W^{m,2}(Ω)` and *all* of
whose `m`-fold iterated classical partials `iterClassicalPartial m idx u` lie in
`W^{2,2}(Ω)`, `u` lies in `W^{m+2,2}(Ω)`.

The proof is induction on `m`. The `m = 0` case is the hypothesis at the empty
multi-index. The step uses the order-raiser `memWkp_succ_of_classicalPartial_memWkp`:
each classical partial `∂_l u` is smooth, lies in `W^{m,2}(Ω)` (as
`u ∈ W^{m+1,2}(Ω)`), and its `m`-fold partials are the `(m+1)`-fold partials of
`u` (with `l` prepended), so the induction hypothesis gives
`∂_l u ∈ W^{m+2,2}(Ω)` for every `l`; the order-raiser, with `u ∈ L²(Ω)`, then
promotes `u` to `W^{m+3,2}(Ω)`. -/
theorem memWkp_of_iterClassicalPartial_memWkp_two
    (m : ℕ) {Ω : Set EE} (hΩ_open : IsOpen Ω)
    {u : EE → ℝ} (hu_smooth : ContDiff ℝ (⊤ : ℕ∞) u)
    (hu_Wm : MemWkp (d := d) m 2 u Ω)
    (h_top : ∀ idx : Fin m → Fin d,
      MemWkp (d := d) 2 2 (iterClassicalPartial (d := d) m idx u) Ω) :
    MemWkp (d := d) (m + 2) 2 u Ω := by
  classical
  induction m generalizing u with
  | zero =>
      simpa [iterClassicalPartial_zero] using h_top (fun i : Fin 0 => i.elim0)
  | succ m ih =>
      have hu_L2 : MemLp u 2 (volume.restrict Ω) := hu_Wm.memLp
      have h_du : ∀ l : Fin d,
          MemWkp (d := d) (m + 2) 2
            (fun x => (fderiv ℝ u x) (EuclideanSpace.single l 1)) Ω := by
        intro l
        refine ih ?_ ?_ ?_
        · exact contDiff_partial_eta (d := d) hu_smooth l
        · exact classicalPartial_memWkp_of_memWkp_succ (d := d) hΩ_open
            hu_smooth hu_Wm l
        · intro idx
          have h_eq :
              iterClassicalPartial (d := d) m idx
                  (fun x => (fderiv ℝ u x) (EuclideanSpace.single l 1)) =
                iterClassicalPartial (d := d) (m + 1)
                  (Fin.cons l idx) u := by
            rw [iterClassicalPartial_succ]
            simp only [Fin.cons_zero, Fin.cons_succ]
          rw [h_eq]
          exact h_top (Fin.cons l idx)
      have h_raised : MemWkp (d := d) ((m + 2) + 1) 2 u Ω :=
        memWkp_succ_of_classicalPartial_memWkp (d := d) (m + 2) hΩ_open
          hu_smooth hu_L2 h_du
      have h_idx : (m + 2) + 1 = (m + 1) + 2 := by ring
      rwa [h_idx] at h_raised

end GenericRaiser

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- **Each iterated chart partial of a weak-solution component lies in `W^{2,2}`
on a precompact interior subdomain.**

For a connection-Laplacian weak-solution pair `(T, F)` of chart-supported smooth
sections with the chart component supported inside `K`, the `m`-fold iterated
classical partial of the Euclidean chart component
`tensorComponentEuclid g r s T α P₀` lies in `MemWkp 2 2` on every precompact
interior subdomain `Ω''` (with `closure Ω''` compact and `Ω'' ⊆ chartTargetEuclid
α` providing the geometric room for the scalar interior `H²` engine).

The iterated partial is, by `tensorComponent_iterated_partial_isSmoothWeakSolution`,
a smooth weak solution of the *same* principal form `tensorPrincipalForm g α …`
against the smooth, compactly-supported iterated perturbed source — into which
the Weitzenböck lower-order coupling has been folded one order at a time. The
scalar interior `H²` engine `smooth_cc_h2_loc_memWkp_two` then delivers the
`W^{2,2}` membership. -/
theorem iterClassicalPartial_memWkp_two_of_weakSolution
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T F : SmoothCcTensor g r s) (α : M)
    {K : Set EuclN} (hK : IsCompact K)
    (hK_target : K ⊆ chartTargetEuclid (I := I) (M := M) α)
    (P₀ : CompIdx E r s)
    (hT_supp : tsupport T.toFun ⊆ (chartAt H α).source)
    (hF_supp : tsupport F.toFun ⊆ (chartAt H α).source)
    (hT_K : tsupport (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) ⊆ K)
    (hweak : ∀ v : SmoothCcTensor g r s,
      ∫ x, tensorCovDerivPointwiseInner (I := I) (M := M) g r s T v x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
        tensorL2Inner (I := I) (M := M) g r s F.toFun v.toFun)
    {Ω'' : Set EuclN} (hΩ''_open : IsOpen Ω'')
    (hΩ''_compact_closure : IsCompact (closure Ω''))
    (m : ℕ) (idx : Fin m → Fin (Module.finrank ℝ E)) :
    MemWkp (d := Module.finrank ℝ E) 2 2
      (iterClassicalPartial (d := Module.finrank ℝ E) m idx
        (tensorComponentEuclid (I := I) (M := M) g r s T α P₀)) Ω'' := by
  classical
  set B := tensorPrincipalForm (I := I) (M := M) g α hK hK_target with hB_def
  set u : EuclN → ℝ := tensorComponentEuclid (I := I) (M := M) g r s T α P₀
    with hu_def
  set RHS : EuclN → ℝ :=
    tensorComponentWeakRHS (I := I) (M := M) g r s T F α hK hK_target P₀
    with hRHS_def
  have h_weak_sol :
      B.IsSmoothWeakSolution
        (iterClassicalPartial (d := Module.finrank ℝ E) m idx u)
        (iteratedPerturbedSource (d := Module.finrank ℝ E) B m u RHS idx) :=
    tensorComponent_iterated_partial_isSmoothWeakSolution (I := I) (M := M)
      g r s T F α hK hK_target P₀ hT_supp hF_supp hT_K hweak m idx
  have hu_cd : ContDiff ℝ (⊤ : ℕ∞) u :=
    tensorComponentEuclid_contDiff (I := I) (M := M) g r s T α P₀ hT_supp
  have hu_cpt : HasCompactSupport u :=
    tensorComponentEuclid_hasCompactSupport (I := I) (M := M) g r s T α P₀ hT_supp
  have hRHS_cd : ContDiff ℝ (⊤ : ℕ∞) RHS :=
    tensorComponentWeakRHS_contDiff (I := I) (M := M) g r s T F α hK hK_target P₀
      hT_supp hF_supp
  have hRHS_cpt : HasCompactSupport RHS :=
    tensorComponentWeakRHS_hasCompactSupport (I := I) (M := M) g r s T F α hK
      hK_target P₀ hT_supp hF_supp hT_K hweak
  have h_w_cpt :
      HasCompactSupport (iterClassicalPartial (d := Module.finrank ℝ E) m idx u) :=
    hasCompactSupport_iterClassicalPartial (d := Module.finrank ℝ E) m idx hu_cpt
  have h_s_cd : ContDiff ℝ (⊤ : ℕ∞)
      (iteratedPerturbedSource (d := Module.finrank ℝ E) B m u RHS idx) :=
    contDiff_iteratedPerturbedSource (d := Module.finrank ℝ E) B m hu_cd hRHS_cd idx
  have h_s_cpt : HasCompactSupport
      (iteratedPerturbedSource (d := Module.finrank ℝ E) B m u RHS idx) := by
    have h_sub :
        tsupport (iteratedPerturbedSource (d := Module.finrank ℝ E) B m u RHS idx)
          ⊆ tsupport u ∪ tsupport RHS :=
      tsupport_iteratedPerturbedSource_subset (d := Module.finrank ℝ E) B m
        ((isClosed_tsupport u).union (isClosed_tsupport RHS))
        subset_union_left subset_union_right idx
    exact HasCompactSupport.of_support_subset_isCompact
      (hu_cpt.union hRHS_cpt)
      ((subset_tsupport _).trans h_sub)
  obtain ⟨C, _hC_nn, h_engine⟩ :=
    smooth_cc_h2_loc_memWkp_two (d := Module.finrank ℝ E) B hΩ''_open
      hΩ''_compact_closure
  exact (h_engine h_weak_sol h_w_cpt h_s_cd h_s_cpt).1

/-- **All-orders interior tensor elliptic-system regularity (unconditional).**

For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, a chart center
`α : M`, a component multi-index `P₀`, and a connection-Laplacian weak-solution
pair `(T, F)` of chart-supported smooth sections with the chart component
supported inside `K`, the Euclidean chart component
`tensorComponentEuclid g r s T α P₀` lies in `MemWkp (2k+2) 2` on every
precompact interior subdomain `Ω''`, for *every* order `k : ℕ`.

This is the all-orders, `HasLocallyConstantChartAt`-free tensor analog of the
scalar interior bootstrap. The Weitzenböck lower-order coupling among the chart
components is handled honestly through the iterated weak-solution identity
(`iterClassicalPartial_memWkp_two_of_weakSolution`), and the order-by-order
assembly is the generic scalar bootstrap `memWkp_of_iterClassicalPartial_memWkp_two`:
every `2k`-fold mixed partial of the chart component lies in `W^{2,2}` on `Ω''`,
hence (since the chart component lies in `W^{2k,2}` by the same chain at the
lower order, anchoring the bootstrap's `W^{m,2}` hypothesis) the chart component
lies in `W^{2k+2,2}`. -/
theorem tensorComponent_memWkp_allOrders_interior
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T F : SmoothCcTensor g r s) (α : M)
    {K : Set EuclN} (hK : IsCompact K)
    (hK_target : K ⊆ chartTargetEuclid (I := I) (M := M) α)
    (P₀ : CompIdx E r s)
    (hT_supp : tsupport T.toFun ⊆ (chartAt H α).source)
    (hF_supp : tsupport F.toFun ⊆ (chartAt H α).source)
    (hT_K : tsupport (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) ⊆ K)
    (hweak : ∀ v : SmoothCcTensor g r s,
      ∫ x, tensorCovDerivPointwiseInner (I := I) (M := M) g r s T v x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
        tensorL2Inner (I := I) (M := M) g r s F.toFun v.toFun)
    {Ω'' : Set EuclN} (hΩ''_open : IsOpen Ω'')
    (hΩ''_compact_closure : IsCompact (closure Ω''))
    (k : ℕ) :
    MemWkp (d := Module.finrank ℝ E) (2 * k + 2) 2
      (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) Ω'' := by
  classical
  set u : EuclN → ℝ := tensorComponentEuclid (I := I) (M := M) g r s T α P₀
    with hu_def
  have hu_cd : ContDiff ℝ (⊤ : ℕ∞) u :=
    tensorComponentEuclid_contDiff (I := I) (M := M) g r s T α P₀ hT_supp
  have h_even : ∀ j : ℕ,
      MemWkp (d := Module.finrank ℝ E) (2 * j) 2 u Ω'' := by
    intro j
    induction j with
    | zero =>
        rw [Nat.mul_zero, MemWkp_zero]
        have hu_cpt : HasCompactSupport u :=
          tensorComponentEuclid_hasCompactSupport (I := I) (M := M)
            g r s T α P₀ hT_supp
        exact (Continuous.memLp_of_hasCompactSupport hu_cd.continuous hu_cpt).restrict Ω''
    | succ j ih =>
        have h_step :
            MemWkp (d := Module.finrank ℝ E) (2 * j + 2) 2 u Ω'' :=
          memWkp_of_iterClassicalPartial_memWkp_two (d := Module.finrank ℝ E)
            (2 * j) hΩ''_open hu_cd ih
            (fun idx => iterClassicalPartial_memWkp_two_of_weakSolution
              (I := I) (M := M) g r s T F α hK hK_target P₀ hT_supp hF_supp
              hT_K hweak hΩ''_open hΩ''_compact_closure (2 * j) idx)
        have h_idx : 2 * j + 2 = 2 * (j + 1) := by ring
        rwa [h_idx] at h_step
  exact memWkp_of_iterClassicalPartial_memWkp_two (d := Module.finrank ℝ E)
    (2 * k) hΩ''_open hu_cd (h_even k)
    (fun idx => iterClassicalPartial_memWkp_two_of_weakSolution
      (I := I) (M := M) g r s T F α hK hK_target P₀ hT_supp hF_supp
      hT_K hweak hΩ''_open hΩ''_compact_closure (2 * k) idx)

end TensorRegularity
end Laplacian
end Analysis
end DifferentialGeometry

end
