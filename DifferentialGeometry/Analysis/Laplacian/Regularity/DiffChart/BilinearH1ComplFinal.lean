import DifferentialGeometry.Analysis.Laplacian.Regularity.DiffChart.BilinearH1ComplFromDomainPow
import DifferentialGeometry.Analysis.Laplacian.Regularity.DiffChart.BilinearH1ComplCanonical
import DifferentialGeometry.Analysis.Laplacian.Regularity.FChartResidual.LpDecomposition
import DifferentialGeometry.Analysis.Laplacian.Regularity.GradInner.LpIdentity
import DifferentialGeometry.Analysis.Laplacian.Regularity.GradInner.LaplacianDensityExt
import DifferentialGeometry.Analysis.Laplacian.Regularity.GradInner.VariationalIntegralForm
import DifferentialGeometry.Analysis.Sobolev.Chart.SmoothMul

/-!
# Final chain: image membership, iterated closure, and residual MemW1p discharge

For a closed Riemannian manifold `(M, g)`, chart point `α : M`, smooth
partition-of-unity weight `ρα := chartAtlasPOU I M α`, and an element
`u_h ∈ laplacianDomainPow g 2`, this module assembles the final chain that
leads up to the residual `MemW1p 2 fChartResidual chartTargetEuclid α`
regularity used by the differentiated chart-bilinear data constructor.

## The chain

The chain has four logical steps:

1. **Image-membership of `gradInnerCLM g ρα u_h`**: for
   `u_h ∈ laplacianDomainPow g 2`,
   ```
   gradInnerCLM g ρα u_h ∈ H1ComplToLp '' (laplacianDomain g).
   ```
   Delivered in two forms:
   * **Smooth case (unconditional)**: for `u_h := smoothToH1Compl v` with
     smooth `v : SmoothScalar g`, the membership holds unconditionally
     (re-export of `gradInnerCLM_smoothToH1Compl_mem_image_laplacianDomain`).
   * **General case (density-bearing)**: for arbitrary
     `u_h ∈ laplacianDomainPow g 2`, the membership holds given a smooth
     approximating sequence with `H1Compl` and Bochner-candidate `Lp`
     convergence, plus the smooth-case Bochner identification target for
     each approximator. Re-export of
     `gradInnerCLM_mem_image_laplacianDomain_via_density`.

2. **Iterated closure of `smoothMulH1Compl g ρα u_h`**: under the same
   hypotheses,
   ```
   smoothMulH1Compl g ρα u_h ∈ laplacianDomainPow g 2.
   ```
   This is the iterated closure of the Laplacian domain under smooth
   multiplication: starting from `u_h ∈ laplacianDomainPow g 2`, the
   product `ρα · u_h` (as an `H1Compl` element) remains in
   `laplacianDomainPow g 2` (so its `(1-Δ_g)`-preimage is again in
   `laplacianDomain g`, recursively). Membership follows from the
   image-membership step via the equivalence
   `smoothMulH1Compl_mem_pow_two_iff_gradInnerCLM_mem_image`.

3. **`MemWkpChart g 2 2` regularity of the Leibniz residual Lp class**:
   given the iterated closure, the Lp class `fHLeibnizResidualLp g α u_h` (≡
   `preimage⟨smoothMulH1Compl ρα u_h⟩ - smoothMulLp ρα (preimage u_h)`) has
   its function representative in `MemWkpChart g 2 2`. This follows from
   closure of `MemWkpChart g 2 2` under subtraction, together with the
   two-sided `H²` regularity `laplacianDomainPow_two_h2_plus_rhs_h2`
   applied to `smoothMulH1Compl ρα u_h ∈ laplacianDomainPow g 2` (the
   iterated closure) and to `u_h ∈ laplacianDomainPow g 2`.

4. **The constructor**: the existing `_unconditional` constructor
   `diffChartBilinearH1ComplData_of_laplacianDomainPow_two_unconditional`
   takes `MemW1p 2 fChartResidual` as a hypothesis. The discharge of this
   hypothesis from the residual regularity step requires an additional
   chart-side support bridge (the "raw chart-pull MemW1p" piece): for
   `F : M → ℝ` with `F ∈ MemWkpChart g 1 p` and `tsupport(F)` contained in
   `(chartAt H α).source`, the raw chart-pull `chartPushedRaw α F` is in
   `MemW1p p chartTargetEuclid α`. This bridge is currently a follow-up
   piece. The constructor here exposes the residual `MemW1p` hypothesis
   in the same form as the `_unconditional` constructor, packaged with
   the density hypotheses needed for the image-membership and
   iterated-closure steps.

## Main results

### Unconditional (smooth case)

* `gradInnerCLM_mem_image_smooth` — image-membership, smooth case (re-export).
* `smoothMulH1Compl_mem_pow_two_smooth` — iterated closure, smooth case (re-export).

### Density-bearing (general case)

* `gradInnerCLM_mem_image_density` — image-membership with density hypotheses.
* `smoothMulH1Compl_mem_pow_two_density` — iterated closure with density hypotheses.
* `fHLeibnizResidualLp_coeFn_memWkpChart_two_two_of_mem` — residual
  regularity given the iterated closure: the manifold-side function
  corresponding to `fHLeibnizResidualLp.coeFn` lies in `MemWkpChart g 2 2`.
* `fHLeibnizResidualLp_coeFn_memWkpChart_two_two_density` — residual
  regularity with density hypotheses (discharges the iterated closure
  internally).

### The constructor

* `diffChartBilinearH1ComplData_of_laplacianDomainPow_two_density` — the
  constructor packaged with the density hypotheses for the image-membership
  and iterated-closure steps, plus the residual `MemW1p 2 fChartResidual`
  hypothesis (matching the shape of the existing `_unconditional`
  constructor).

## Note on the chart-side support bridge

A fully unconditional `MemW1p 2 fChartResidual` discharge requires an
additional chart-side support bridge converting `MemWkpChart g 1 p`
membership with support in `(chartAt H α).source` into `MemW1p p
chartTargetEuclid α` of the raw chart-pull. The `MemWkpChart` predicate
naturally gives `MemWkp 1 p chartTargetEuclid α` of the
*partition-of-unity-weighted* chart-pull (`chartPushed POU α F`), but
converting to the raw chart-pull (without POU multiplier) requires the
support condition `tsupport(F) ⊆ (chartAt H α).source` plus a chart-local
construction. This bridge is currently a follow-up piece, not delivered
in this module.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace DiffChartBilinearH1ComplFinal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainChartData
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul
open DifferentialGeometry.Analysis.Laplacian.GradInnerLpIdentity
open DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational
open DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianDensityExtension
open DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl
open DifferentialGeometry.Analysis.Sobolev.Chart

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-- **Image-membership, smooth case (unconditional).** For smooth `v : SmoothScalar g`,
the gradient inner product `gradInnerCLM g φ (smoothToH1Compl v)` lifts to
an `H1Compl` element in `laplacianDomain g`. Re-export of
`gradInnerCLM_smoothToH1Compl_mem_image_laplacianDomain`. -/
theorem gradInnerCLM_mem_image_smooth
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    gradInnerCLM (I := I) (M := M) g φ
        (smoothToH1Compl (I := I) (M := M) g v) ∈
      Set.image (H1ComplToLp (I := I) (M := M) g)
        (laplacianDomain (I := I) (M := M) g : Set (H1Compl g)) :=
  gradInnerCLM_smoothToH1Compl_mem_image_laplacianDomain
    (I := I) (M := M) g φ v

/-- **Image-membership, general case (density-bearing).** For arbitrary
`u_h ∈ laplacianDomainPow g 2` and given a smooth approximating sequence
with `H1Compl` convergence and Bochner-candidate `Lp` convergence plus the
smooth-case identification target for each approximator,
`gradInnerCLM g φ u_h` lifts to an `H1Compl` element in `laplacianDomain g`.
Re-export of `gradInnerCLM_mem_image_laplacianDomain_via_density`. -/
theorem gradInnerCLM_mem_image_density
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (h_smooth_seq : ℕ → SmoothScalar g)
    (h_conv_H1Compl : Tendsto
      (fun n => smoothToH1Compl (I := I) (M := M) g (h_smooth_seq n))
      atTop (𝓝 u_h))
    (h_conv_candidate : Tendsto
      (fun n => gradInnerLaplacianCandidateUnconditional (I := I) (M := M) g φ
        (smoothToH1Compl_mem_laplacianDomainPow_two
          (I := I) (M := M) g (h_smooth_seq n)))
      atTop (𝓝 (gradInnerLaplacianCandidateUnconditional
        (I := I) (M := M) g φ hu_h)))
    (h_smooth_identity : ∀ n,
      smoothCandidate_identification_target (I := I) (M := M) g φ
        (h_smooth_seq n)) :
    gradInnerCLM (I := I) (M := M) g φ u_h ∈
      Set.image (H1ComplToLp (I := I) (M := M) g)
        (laplacianDomain (I := I) (M := M) g : Set (H1Compl g)) :=
  gradInnerCLM_mem_image_laplacianDomain_via_density
    (I := I) (M := M) g φ hu_h h_smooth_seq h_conv_H1Compl
    h_conv_candidate h_smooth_identity

/-- **Iterated closure, smooth case (unconditional).** For smooth `v : SmoothScalar g`,
`smoothMulH1Compl g φ (smoothToH1Compl v) ∈ laplacianDomainPow g 2`. Re-export
of `smoothMulH1Compl_smoothToH1Compl_mem_laplacianDomainPow_two`. -/
theorem smoothMulH1Compl_mem_pow_two_smooth
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    smoothMulH1Compl (I := I) (M := M) g φ
        (smoothToH1Compl (I := I) (M := M) g v) ∈
      laplacianDomainPow (I := I) (M := M) g 2 :=
  smoothMulH1Compl_smoothToH1Compl_mem_laplacianDomainPow_two
    (I := I) (M := M) g φ v

/-- **Iterated closure, general case (density-bearing).** For arbitrary
`u_h ∈ laplacianDomainPow g 2` and given density hypotheses, the
iterated closure `smoothMulH1Compl g φ u_h ∈ laplacianDomainPow g 2` holds.
Re-export of `smoothMulH1Compl_mem_pow_two_via_density`. -/
theorem smoothMulH1Compl_mem_pow_two_density
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (h_smooth_seq : ℕ → SmoothScalar g)
    (h_conv_H1Compl : Tendsto
      (fun n => smoothToH1Compl (I := I) (M := M) g (h_smooth_seq n))
      atTop (𝓝 u_h))
    (h_conv_candidate : Tendsto
      (fun n => gradInnerLaplacianCandidateUnconditional (I := I) (M := M) g φ
        (smoothToH1Compl_mem_laplacianDomainPow_two
          (I := I) (M := M) g (h_smooth_seq n)))
      atTop (𝓝 (gradInnerLaplacianCandidateUnconditional
        (I := I) (M := M) g φ hu_h)))
    (h_smooth_identity : ∀ n,
      smoothCandidate_identification_target (I := I) (M := M) g φ
        (h_smooth_seq n)) :
    smoothMulH1Compl (I := I) (M := M) g φ u_h ∈
      laplacianDomainPow (I := I) (M := M) g 2 :=
  smoothMulH1Compl_mem_pow_two_via_density
    (I := I) (M := M) g φ hu_h h_smooth_seq h_conv_H1Compl
    h_conv_candidate h_smooth_identity

/-- The function `ρα · (preimage⟨u_h⟩).coeFn` is in `MemWkpChart g 2 2`
when `u_h ∈ laplacianDomainPow g 2`. This is the smooth-times-H² closure
applied to the `Lp` preimage representative. -/
private lemma rhoAlpha_mul_preimage_coeFn_memWkpChart_two_two
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) g 2 2
      (fun x : M => (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x *
        ((laplacianDomain.preimage (I := I) (M := M) g
            ⟨u_h, laplacianDomainPow_succ_subset_laplacianDomain
              (I := I) (M := M) g 1 hu_h⟩ :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x) := by
  classical
  have h_preimage_h2 := (laplacianDomainPow_two_h2_plus_rhs_h2
    (I := I) (M := M) g hu_h).2.1
  exact DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart_smooth_mul
    (I := I) (M := M) g (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) h_preimage_h2

/-- **Residual regularity given the iterated closure (function form).** Given
`u_h ∈ laplacianDomainPow g 2` and the iterated closure
`smoothMulH1Compl ρα u_h ∈ laplacianDomainPow g 2`, the manifold-side function
`-2 g(∇ρα, ∇u_h) - Δρα · u_h` (equal a.e. to the `fHLeibnizResidualLp`
function representative) is in `MemWkpChart g 2 2`.

The statement is in *function* form rather than `Lp`-class form because
`MemWkpChart` is a predicate on `M → ℝ` rather than `Lp ℝ 2`. The function
representative differs from `(fHLeibnizResidualLp).coeFn` only by an
ae-equality; `MemWkpChart` is closed under ae-equality (via
chart-pulled-raw ae transfer). -/
theorem fHLeibnizResidualLp_coeFn_memWkpChart_two_two_of_mem
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (h_mem : smoothMulH1Compl (I := I) (M := M) g
        (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) u_h ∈
      laplacianDomainPow (I := I) (M := M) g 2) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) g 2 2
      (fun x : M =>
        ((laplacianDomain.preimage (I := I) (M := M) g
            ⟨smoothMulH1Compl (I := I) (M := M) g
                (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) u_h,
              smoothMulH1Compl_mem_laplacianDomain (I := I) (M := M) g
                (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
                (laplacianDomainPow_succ_subset_laplacianDomain
                  (I := I) (M := M) g 1 hu_h)⟩ :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x -
        (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x *
          ((laplacianDomain.preimage (I := I) (M := M) g
              ⟨u_h, laplacianDomainPow_succ_subset_laplacianDomain
                (I := I) (M := M) g 1 hu_h⟩ :
            Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x) := by
  classical
  have h_smHC_h2 := (laplacianDomainPow_two_h2_plus_rhs_h2
    (I := I) (M := M) g h_mem).2.1
  have h_smoothMul_h2 := rhoAlpha_mul_preimage_coeFn_memWkpChart_two_two
    (I := I) (M := M) g α hu_h
  have h_preimage_eq :
      laplacianDomain.preimage (I := I) (M := M) g
          ⟨smoothMulH1Compl (I := I) (M := M) g
              (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) u_h,
            smoothMulH1Compl_mem_laplacianDomain (I := I) (M := M) g
              (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
              (laplacianDomainPow_succ_subset_laplacianDomain
                (I := I) (M := M) g 1 hu_h)⟩ =
      laplacianDomain.preimage (I := I) (M := M) g
        ⟨smoothMulH1Compl (I := I) (M := M) g
            (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) u_h,
          laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1 h_mem⟩ := rfl
  rw [h_preimage_eq]
  exact DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart_sub
    (I := I) (M := M) g (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    h_smHC_h2 h_smoothMul_h2

/-- **Residual regularity in density form.** Combines the density-form
iterated closure with the `MemWkpChart g 2 2` residual regularity, giving
the conclusion in terms of the density hypotheses for arbitrary
`u_h ∈ laplacianDomainPow g 2`. -/
theorem fHLeibnizResidualLp_coeFn_memWkpChart_two_two_density
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (h_smooth_seq : ℕ → SmoothScalar g)
    (h_conv_H1Compl : Tendsto
      (fun n => smoothToH1Compl (I := I) (M := M) g (h_smooth_seq n))
      atTop (𝓝 u_h))
    (h_conv_candidate : Tendsto
      (fun n => gradInnerLaplacianCandidateUnconditional (I := I) (M := M) g
        (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
        (smoothToH1Compl_mem_laplacianDomainPow_two
          (I := I) (M := M) g (h_smooth_seq n)))
      atTop (𝓝 (gradInnerLaplacianCandidateUnconditional
        (I := I) (M := M) g
        (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) hu_h)))
    (h_smooth_identity : ∀ n,
      smoothCandidate_identification_target (I := I) (M := M) g
        (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) (h_smooth_seq n)) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) g 2 2
      (fun x : M =>
        ((laplacianDomain.preimage (I := I) (M := M) g
            ⟨smoothMulH1Compl (I := I) (M := M) g
                (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) u_h,
              smoothMulH1Compl_mem_laplacianDomain (I := I) (M := M) g
                (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
                (laplacianDomainPow_succ_subset_laplacianDomain
                  (I := I) (M := M) g 1 hu_h)⟩ :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x -
        (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x *
          ((laplacianDomain.preimage (I := I) (M := M) g
              ⟨u_h, laplacianDomainPow_succ_subset_laplacianDomain
                (I := I) (M := M) g 1 hu_h⟩ :
            Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x) := by
  classical
  have h_mem := smoothMulH1Compl_mem_pow_two_density
    (I := I) (M := M) g (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) hu_h
    h_smooth_seq h_conv_H1Compl h_conv_candidate h_smooth_identity
  exact fHLeibnizResidualLp_coeFn_memWkpChart_two_two_of_mem
    (I := I) (M := M) g α hu_h h_mem

/-- **Constructor for `DiffChartBilinearH1ComplData g α` from density
hypotheses, residual `MemW1p` hypothesis, and the differentiated
variational identity.**

This packages the density-bearing form of the image-membership and
iterated-closure steps with the residual `MemW1p 2 fChartResidual`
hypothesis and the differentiated identity.
The downstream pipeline can supply the density approximator sequence
once it is constructed; the residual `MemW1p 2 fChartResidual` is the
final remaining piece that the chart-side support bridge would discharge
fully unconditionally. -/
noncomputable def diffChartBilinearH1ComplData_of_laplacianDomainPow_two_density
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl g} (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (_h_smooth_seq : ℕ → SmoothScalar g)
    (_h_conv_H1Compl : Tendsto
      (fun n => smoothToH1Compl (I := I) (M := M) g (_h_smooth_seq n))
      atTop (𝓝 u_h))
    (_h_conv_candidate : Tendsto
      (fun n => gradInnerLaplacianCandidateUnconditional (I := I) (M := M) g
        (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
        (smoothToH1Compl_mem_laplacianDomainPow_two
          (I := I) (M := M) g (_h_smooth_seq n)))
      atTop (𝓝 (gradInnerLaplacianCandidateUnconditional
        (I := I) (M := M) g
        (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) hu_h)))
    (_h_smooth_identity : ∀ n,
      smoothCandidate_identification_target (I := I) (M := M) g
        (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) (_h_smooth_seq n))
    (direction : Fin (Module.finrank ℝ E))
    (h_residual_memW1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      (fChartResidual (I := I) (M := M) g α u_h)
      (chartTargetEuclid (I := I) (M := M) α))
    (h_identity :
      ∀ ψ : EuclN → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α →
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α i j y *
                (chosenSecondPartialChartPushedU
                  (I := I) (M := M) g α u_h i direction) y *
                (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
          ∂(volume : Measure EuclN)) +
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
              (laplacianDomainPow_succ_subset_laplacianDomain
                (I := I) (M := M) g 1 hu_h)).weak_partial direction y * ψ y
          ∂(volume : Measure EuclN)) =
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            chosenFChartDeriv (I := I) (M := M) g α hu_h direction y * ψ y
          ∂(volume : Measure EuclN)) -
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramDerivOnEuclid (I := I) g α i j direction y *
                (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
                  (laplacianDomainPow_succ_subset_laplacianDomain
                    (I := I) (M := M) g 1 hu_h)).weak_partial i y *
                (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
          ∂(volume : Measure EuclN)) -
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityDerivOnEuclid (I := I) g α direction y *
            (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
              (laplacianDomainPow_succ_subset_laplacianDomain
                (I := I) (M := M) g 1 hu_h)).u_chart y * ψ y
          ∂(volume : Measure EuclN)) +
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityDerivOnEuclid (I := I) g α direction y *
            (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
              (laplacianDomainPow_succ_subset_laplacianDomain
                (I := I) (M := M) g 1 hu_h)).f_chart y * ψ y
          ∂(volume : Measure EuclN))) :
    DiffChartBilinearH1ComplData (I := I) (M := M) g α :=
  diffChartBilinearH1ComplData_of_laplacianDomainPow_two_via_residual
    (I := I) (M := M) g α hu_h direction h_residual_memW1p h_identity

end DiffChartBilinearH1ComplFinal
end Laplacian
end Analysis
end DifferentialGeometry

end
