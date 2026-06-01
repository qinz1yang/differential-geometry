import DifferentialGeometry.Analysis.Laplacian.TensorRegularity.WeakSolutionHeadline
import DifferentialGeometry.Analysis.Sobolev.Nirenberg.H2Regularity

/-!
# Interior `H²` regularity for the chart components of a tensor weak solution

For a smooth Riemannian metric `g` on a closed (compact, boundaryless) smooth
manifold `M`, a chart center `α : M`, and a component multi-index
`P₀ : CompIdx E r s`, the headline `tensorComponent_isSmoothWeakSolution`
(from `WeakSolutionHeadline.lean`) packages each Euclidean chart component
`tensorComponentEuclid g r s T α P₀` of an `(r, s)`-tensor section `T` solving
the global `H¹` weak equation of the connection Laplacian as a smooth weak
solution of the principal-part elliptic bilinear form
`tensorPrincipalForm g α hK hK_target` — a uniformly elliptic
`SmoothEllipticBilinearForm` on `Set.univ : Set EuclN`.

This file glues that packaging to the Euclidean interior `H²` regularity
theorem `h2_loc_smooth_solution` (from `Sobolev.Nirenberg.H2Regularity`). The
end product is a per-component, per-chart statement: on any precompact open
subdomain `Ω''` of `EuclN`, each chart component `tensorComponentEuclid` admits
weak second partial derivatives in `L²(Ω'')`, with a quantitative bound on
`∫_{Ω''} g²` in terms of the `H¹` data of the chart component plus the `L²`
norms of the chart component and the explicit right-hand side on a slightly
enlarged compact-closure neighborhood.

## Discharging the engine hypotheses

The Euclidean engine `h2_loc_smooth_solution` requires, beyond the
`IsSmoothWeakSolution` witness:

* an `L²`-locality property for the right-hand side — discharged here from
  `tensorComponentWeakRHS_contDiff` (the explicit right-hand side is `C^∞`) and
  `tensorComponentWeakRHS_hasCompactSupport` (it has compact support): a `C^∞`
  compactly-supported function lies in `L²` on every restricted measure;
* a geometric room condition `Metric.cthickening 2 (closure Ω'') ⊆ Ω` together
  with `closure Ω'' ⊆ Ω` — both *trivial* here, since the principal-part form
  `tensorPrincipalForm` has domain `Ω = Set.univ`.

## Setting

Closed (compact, boundaryless) smooth Riemannian manifold:
`[I.Boundaryless]`, `[T2Space M]`, `[SigmaCompactSpace M]`, `[CompactSpace M]`.
The model fibre `E` is a finite-dimensional real inner-product space with
positive dimension (`[NeZero (Module.finrank ℝ E)]`).

## Main results

* `tensor_h2_loc_chartComp` — the headline: for a chart-supported smooth
  `(r, s)`-tensor solution `T` of the global `H¹` weak equation of the
  connection Laplacian, a chart center `α`, a compact `K ⊆ chartTargetEuclid α`
  containing the chart component's support, and a precompact open
  `Ω'' ⊆ EuclN`, the chart component `tensorComponentEuclid g r s T α P₀`
  admits, for every direction pair `(i, k)`, a weak `k`-partial `g_{i,k}` of
  its classical `i`-partial on `Ω''`, with `g_{i,k} ∈ L²(Ω'')` and the
  quantitative `H¹`-data bound on `∫_{Ω''} g_{i,k}²`.

* `tensor_h2_loc_chartComp_all` — the packaged corollary quantifying the
  headline over every component multi-index `P₀ : CompIdx E r s`.
-/

noncomputable section

open Bundle Manifold Set Filter MeasureTheory Topology
open scoped Manifold Topology ContDiff BigOperators Matrix InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace TensorRegularity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean
open DifferentialGeometry.Analysis.Sobolev.NirenbergCrossBounds

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

omit [NeZero (Module.finrank ℝ E)] in
/-- A `C^∞` function with compact support on `EuclN` lies in `L²` on every
restricted measure: in particular, on `volume.restrict Ω'` for any subset
`Ω'`. -/
private lemma memLp_two_contDiff_hasCompactSupport_restrict
    {f : EuclN → ℝ} (hf_cd : ContDiff ℝ ∞ f) (hf_cs : HasCompactSupport f)
    (Ω' : Set EuclN) :
    MemLp f 2 ((volume : Measure EuclN).restrict Ω') :=
  (hf_cd.continuous.memLp_of_hasCompactSupport (μ := volume) (p := 2)
    hf_cs).restrict _

/-- **Interior `H²` regularity of the chart components of a tensor weak
solution.**

Let `g` be a smooth Riemannian metric on a closed (compact, boundaryless) smooth
manifold `M`, let `α : M` be a chart center, and let `T` (the solution) and `F`
(the source) be smooth compactly-supported `(r, s)`-tensor sections supported
inside the chart source. Let `K ⊆ chartTargetEuclid α` be compact, with the
Euclidean chart component `tensorComponentEuclid g r s T α P₀` supported inside
`K`, and `P₀ : CompIdx E r s` a component multi-index.

Assume the global `H¹` weak equation
`∫_M ⟨∇T, ∇v⟩ dμ_g = ⟨F, v⟩_{L²}` of the connection Laplacian holds for every
smooth compactly-supported test section `v`. Then, for any precompact open
subdomain `Ω'' ⊆ EuclN` and every direction pair `(i, k)`, the Euclidean chart
component `tensorComponentEuclid g r s T α P₀` admits a weak `k`-partial
derivative `g` of its classical `i`-partial on `Ω''`. The function `g` lies in
`L²(Ω'')`, and there is a slightly enlarged precompact open neighborhood `Ω'`
and a constant `C ≥ 0` with
`∫_{Ω''} g² ≤ C · (∫_{Ω'} ∑_j (∂_j u)² + ∫_{Ω'} u² + ∫_{Ω'} f²)`,
where `u := tensorComponentEuclid g r s T α P₀` is the chart component and
`f := tensorComponentWeakRHS g r s T F α hK hK_target P₀` is the explicit
right-hand side. The quantitative constant `C` is retained for downstream
bootstrap arguments. -/
theorem tensor_h2_loc_chartComp
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
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
    {Ω'' : Set EuclN} (hΩ'' : IsOpen Ω'')
    (hΩ''_compact_closure : IsCompact (closure Ω'')) :
    ∀ i k : Fin (Module.finrank ℝ E), ∃ g_ik : EuclN → ℝ,
      MemLp g_ik 2 ((volume : Measure EuclN).restrict Ω'') ∧
      DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) k g_ik
        (fun y : EuclN =>
          (fderiv ℝ (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) y)
            (EuclideanSpace.single i 1)) Ω'' ∧
      ∃ Ω' : Set EuclN, IsOpen Ω' ∧ closure Ω'' ⊆ Ω' ∧
        closure Ω' ⊆ (Set.univ : Set EuclN) ∧
        IsCompact (closure Ω') ∧
        ∃ C : ℝ, 0 ≤ C ∧
          ∫ x in Ω'', g_ik x ^ 2 ∂(volume : Measure EuclN) ≤
            C * (∫ x in Ω',
                  ∑ j : Fin (Module.finrank ℝ E),
                    ((fderiv ℝ
                      (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) x)
                        (EuclideanSpace.single j 1)) ^ 2
                ∂(volume : Measure EuclN) +
              ∫ x in Ω',
                  (tensorComponentEuclid (I := I) (M := M) g r s T α P₀ x) ^ 2
                ∂(volume : Measure EuclN) +
              ∫ x in Ω',
                  (tensorComponentWeakRHS (I := I) (M := M)
                    g r s T F α hK hK_target P₀ x) ^ 2
                ∂(volume : Measure EuclN)) := by
  classical
  have h_weak :
      (tensorPrincipalForm (I := I) (M := M) g α hK hK_target).IsSmoothWeakSolution
        (tensorComponentEuclid (I := I) (M := M) g r s T α P₀)
        (tensorComponentWeakRHS (I := I) (M := M) g r s T F α hK hK_target P₀) :=
    tensorComponent_isSmoothWeakSolution (I := I) (M := M)
      g r s T F α hK hK_target P₀ hT_supp hF_supp hT_K hweak
  have hRHS_cd : ContDiff ℝ ∞
      (tensorComponentWeakRHS (I := I) (M := M) g r s T F α hK hK_target P₀) :=
    tensorComponentWeakRHS_contDiff (I := I) (M := M)
      g r s T F α hK hK_target P₀ hT_supp hF_supp
  have hRHS_cs : HasCompactSupport
      (tensorComponentWeakRHS (I := I) (M := M) g r s T F α hK hK_target P₀) :=
    tensorComponentWeakRHS_hasCompactSupport (I := I) (M := M)
      g r s T F α hK hK_target P₀ hT_supp hF_supp hT_K hweak
  have hf_l2_loc : ∀ {Ω' : Set EuclN}, IsCompact (closure Ω') →
      MemLp (tensorComponentWeakRHS (I := I) (M := M) g r s T F α hK hK_target P₀)
        2 ((volume : Measure EuclN).restrict Ω') := by
    intro Ω' _
    exact memLp_two_contDiff_hasCompactSupport_restrict (E := E)
      hRHS_cd hRHS_cs Ω'
  have h_closure_in :
      closure Ω'' ⊆ (Set.univ : Set EuclN) := fun y _ => Set.mem_univ y
  have h_room :
      Metric.cthickening 2 (closure Ω'') ⊆ (Set.univ : Set EuclN) :=
    fun y _ => Set.mem_univ y
  obtain ⟨C, hC_nn, h_eng⟩ := h2_loc_smooth_solution
    (d := Module.finrank ℝ E)
    (tensorPrincipalForm (I := I) (M := M) g α hK hK_target)
    hΩ'' hΩ''_compact_closure h_closure_in h_room
  intro i k
  obtain ⟨g_ik, hg_memLp, hg_weak, Ω', hΩ'_open, hΩ''_in_Ω', hΩ'_in,
    hΩ'_compact, hbound⟩ := h_eng h_weak hf_l2_loc i k
  exact ⟨g_ik, hg_memLp, hg_weak, Ω', hΩ'_open, hΩ''_in_Ω', hΩ'_in,
    hΩ'_compact, C, hC_nn, hbound⟩

/-- **Interior `H²` regularity of every chart component of a tensor weak
solution.**

Quantified form of `tensor_h2_loc_chartComp` over all component multi-indices:
under the global `H¹` weak equation of the connection Laplacian, for every
component multi-index `P₀ : CompIdx E r s` whose Euclidean chart component is
supported inside the compact `K`, and every direction pair `(i, k)`, the chart
component `tensorComponentEuclid g r s T α P₀` admits a weak `k`-partial of its
classical `i`-partial on the precompact open subdomain `Ω''`, in `L²(Ω'')`,
with the quantitative `H¹`-data bound on a slightly enlarged neighborhood. -/
theorem tensor_h2_loc_chartComp_all
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T F : SmoothCcTensor g r s) (α : M)
    {K : Set EuclN} (hK : IsCompact K)
    (hK_target : K ⊆ chartTargetEuclid (I := I) (M := M) α)
    (hT_supp : tsupport T.toFun ⊆ (chartAt H α).source)
    (hF_supp : tsupport F.toFun ⊆ (chartAt H α).source)
    (hT_K : ∀ P₀ : CompIdx E r s,
      tsupport (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) ⊆ K)
    (hweak : ∀ v : SmoothCcTensor g r s,
      ∫ x, tensorCovDerivPointwiseInner (I := I) (M := M) g r s T v x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
        tensorL2Inner (I := I) (M := M) g r s F.toFun v.toFun)
    {Ω'' : Set EuclN} (hΩ'' : IsOpen Ω'')
    (hΩ''_compact_closure : IsCompact (closure Ω'')) :
    ∀ (P₀ : CompIdx E r s) (i k : Fin (Module.finrank ℝ E)),
      ∃ g_ik : EuclN → ℝ,
      MemLp g_ik 2 ((volume : Measure EuclN).restrict Ω'') ∧
      DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) k g_ik
        (fun y : EuclN =>
          (fderiv ℝ (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) y)
            (EuclideanSpace.single i 1)) Ω'' ∧
      ∃ Ω' : Set EuclN, IsOpen Ω' ∧ closure Ω'' ⊆ Ω' ∧
        closure Ω' ⊆ (Set.univ : Set EuclN) ∧
        IsCompact (closure Ω') ∧
        ∃ C : ℝ, 0 ≤ C ∧
          ∫ x in Ω'', g_ik x ^ 2 ∂(volume : Measure EuclN) ≤
            C * (∫ x in Ω',
                  ∑ j : Fin (Module.finrank ℝ E),
                    ((fderiv ℝ
                      (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) x)
                        (EuclideanSpace.single j 1)) ^ 2
                ∂(volume : Measure EuclN) +
              ∫ x in Ω',
                  (tensorComponentEuclid (I := I) (M := M) g r s T α P₀ x) ^ 2
                ∂(volume : Measure EuclN) +
              ∫ x in Ω',
                  (tensorComponentWeakRHS (I := I) (M := M)
                    g r s T F α hK hK_target P₀ x) ^ 2
                ∂(volume : Measure EuclN)) :=
  fun P₀ => tensor_h2_loc_chartComp (I := I) (M := M)
    g r s T F α hK hK_target P₀ hT_supp hF_supp (hT_K P₀) hweak hΩ'' hΩ''_compact_closure

end TensorRegularity
end Laplacian
end Analysis
end DifferentialGeometry
