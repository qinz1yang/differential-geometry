import DifferentialGeometry.Analysis.Laplacian.Regularity.GradInner.LaplacianSmooth

/-!
# Density-based extension of the smooth-case gradient-inner-Laplacian regularity theorem

For a closed Riemannian manifold `(M, g)`, a smooth scalar
`φ : C^∞⟮I, M; ℝ⟯`, and an arbitrary `u_h ∈ laplacianDomainPow g 2`, this
module packages the **density-based extension** of the smooth-case
gradient-inner-Laplacian regularity theorem (delivered in
`GradInnerLaplacianSmoothFull.lean`) to the non-smooth case.

The extension strategy is:

1. **Density of smooth scalars in `laplacianDomainPow g 2`** (under a
   suitable graph norm). Given `u_h ∈ laplacianDomainPow g 2`, construct
   a sequence `v_n : SmoothScalar g` with `smoothToH1Compl v_n →
   u_h` (in `H1Compl`) and the corresponding iterated preimages converging
   in `Lp`.

2. **H¹Compl-continuity of both sides** of the regularity identity.
   The LHS `gradInnerCLM g φ u_h` is H¹Compl-continuous in `u_h` (as a
   CLM). The RHS `H1ComplToLp(resolvent g (Bochner candidate))` is
   H¹Compl-continuous via the resolvent's continuity, provided the
   candidate is `Lp`-continuous in `u_h`.

3. **Bochner candidate continuity** in `u_h`. Each summand of the
   candidate is `Lp`-continuous in `u_h`:
   - `gradInnerCLM g φ u_h` and `gradInnerCLM g (Δφ) u_h` —
     `Lp`-continuous via CLM property.
   - `gradInnerLapU g φ hu_h` — `Lp`-continuous via `preimageLift`,
     provided `preimageLift` is continuous wrt the graph norm.
   - `ricciPairingCLM g φ u_h` — `Lp`-continuous via CLM property.
   - `hessPairingLpOnLapDom g φ hu_dom` — **the key obstruction**;
     requires `H²`-graph-norm continuity, which is the subject of
     follow-up work.

4. **Smooth-case identity** (Step 2) on the dense subset.

5. **Hessian-bridge** for the smooth approximators.

## Approach

We expose the density extension in **hypothesis-bearing form**, taking as
hypotheses:

* `h_density`: an approximating sequence of smooth scalars `v_n`
  approximating `u_h` in the H¹Compl topology, with iterated preimages
  converging in Lp.
* `h_smooth`: the smooth-case regularity identity holds for each `v_n`.
* `h_candidate_conv`: the Bochner candidate evaluated at `v_n`'s
  membership in `laplacianDomainPow g 2` converges to the candidate at
  the limit point `hu_h` (in `Lp`).

Given these hypotheses, the regularity identity extends by continuity of
both sides.

## Main results

* `gradInnerCLM_eq_H1ComplToLp_resolvent_unconditional_via_density` —
  the density-extension form of the regularity theorem, with the
  approximating-sequence hypotheses exposed.

* `gradInnerCLM_mem_image_laplacianDomain_via_density` — the image
  membership form via density.

* `smoothMulH1Compl_mem_pow_two_via_density` — the iterated-closure form
  via density.

## Note on the full unconditional discharge

The full unconditional regularity theorem requires:

1. **Construction of the approximating sequence**: given
   `u_h ∈ laplacianDomainPow g 2`, construct smooth `v_n : SmoothScalar g`
   with `v_n → u_h` in the H¹Compl topology AND iterated preimages
   converging. The straightforward approach is to take a sequence of
   smooth `f_n ∈ Lp 2 μ_g` (dense by `MeasureTheory.MemLp.exists_smooth_compactSupport`
   or analogous) with `f_n → laplacianDomain.preimage ⟨preimageLift g hu_h, _⟩`
   (the iterated preimage of `u_h`); then `v_n := resolvent g (resolvent g f_n)`,
   which is in `laplacianDomainPow g 2` BUT NOT necessarily smooth.

2. **Bridging non-smooth approximators to smooth ones**: this is the
   core difficulty, requiring `H²`-regularity of `resolvent` chain (via
   `iteratedH2Regularity_one` and analogous), combined with a smoothing
   on `M` to produce smooth approximators in `SmoothScalar g`.

3. **Continuity of `hessPairingLpOnLapDom` in graph norm**: requires
   chart-side analysis and quantitative continuity bounds.

All three are substantial follow-up items and are the subject of
future work.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace GradInnerLaplacianDensityExtension

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Laplacian.GradInnerLpIdentity
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open DifferentialGeometry.Analysis.Laplacian.HessianPairingChart
open DifferentialGeometry.Analysis.Laplacian.HessianPairingLapDom
open DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianCandidate
open DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational
open DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM
open DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianFinal
open DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianSmoothFull

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-- **Density-extension regularity theorem, hypothesis-bearing**. Given
the density-extension hypotheses, the regularity identity holds for
arbitrary `u_h ∈ laplacianDomainPow g 2`. -/
theorem gradInnerCLM_eq_H1ComplToLp_resolvent_unconditional_via_density
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
    gradInnerCLM (I := I) (M := M) g φ u_h =
      H1ComplToLp (I := I) (M := M) g
        (resolvent (I := I) (M := M) g
          (gradInnerLaplacianCandidateUnconditional
            (I := I) (M := M) g φ hu_h)) := by
  classical

  have h_LHS_conv : Tendsto
      (fun n => gradInnerCLM (I := I) (M := M) g φ
        (smoothToH1Compl (I := I) (M := M) g (h_smooth_seq n)))
      atTop (𝓝 (gradInnerCLM (I := I) (M := M) g φ u_h)) := by
    exact ((gradInnerCLM (I := I) (M := M) g φ).continuous.tendsto _).comp
      h_conv_H1Compl

  have h_RHS_conv : Tendsto
      (fun n => H1ComplToLp (I := I) (M := M) g
        (resolvent (I := I) (M := M) g
          (gradInnerLaplacianCandidateUnconditional (I := I) (M := M) g φ
            (smoothToH1Compl_mem_laplacianDomainPow_two
              (I := I) (M := M) g (h_smooth_seq n)))))
      atTop (𝓝 (H1ComplToLp (I := I) (M := M) g
        (resolvent (I := I) (M := M) g
          (gradInnerLaplacianCandidateUnconditional
            (I := I) (M := M) g φ hu_h)))) := by
    have h_resolvent_cont :
        Continuous (resolvent (I := I) (M := M) g) :=
      (resolvent (I := I) (M := M) g).continuous
    have h_H1ComplToLp_cont :
        Continuous (H1ComplToLp (I := I) (M := M) g) :=
      (H1ComplToLp (I := I) (M := M) g).continuous
    have h_composition_cont :
        Continuous (fun f => H1ComplToLp (I := I) (M := M) g
          (resolvent (I := I) (M := M) g f)) :=
      h_H1ComplToLp_cont.comp h_resolvent_cont
    exact (h_composition_cont.tendsto _).comp h_conv_candidate

  have h_smooth_eq : ∀ n,
      gradInnerCLM (I := I) (M := M) g φ
        (smoothToH1Compl (I := I) (M := M) g (h_smooth_seq n)) =
      H1ComplToLp (I := I) (M := M) g
        (resolvent (I := I) (M := M) g
          (gradInnerLaplacianCandidateUnconditional (I := I) (M := M) g φ
            (smoothToH1Compl_mem_laplacianDomainPow_two
              (I := I) (M := M) g (h_smooth_seq n)))) := fun n =>
    smoothCase_via_candidate_identification
      (I := I) (M := M) g φ (h_smooth_seq n) (h_smooth_identity n)

  have h_seq_eq : (fun n => gradInnerCLM (I := I) (M := M) g φ
        (smoothToH1Compl (I := I) (M := M) g (h_smooth_seq n))) =
      (fun n => H1ComplToLp (I := I) (M := M) g
        (resolvent (I := I) (M := M) g
          (gradInnerLaplacianCandidateUnconditional (I := I) (M := M) g φ
            (smoothToH1Compl_mem_laplacianDomainPow_two
              (I := I) (M := M) g (h_smooth_seq n))))) := by
    funext n
    exact h_smooth_eq n

  rw [h_seq_eq] at h_LHS_conv
  exact tendsto_nhds_unique h_LHS_conv h_RHS_conv

/-- **Density-extension regularity theorem, image-membership form**. -/
theorem gradInnerCLM_mem_image_laplacianDomain_via_density
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
        (laplacianDomain (I := I) (M := M) g : Set (H1Compl g)) := by
  classical
  refine ⟨resolvent (I := I) (M := M) g
    (gradInnerLaplacianCandidateUnconditional (I := I) (M := M) g φ hu_h),
    ?_, ?_⟩
  · exact (laplacianDomain_mem_iff (I := I) (M := M) g).mpr
      ⟨gradInnerLaplacianCandidateUnconditional (I := I) (M := M) g φ hu_h, rfl⟩
  · exact (gradInnerCLM_eq_H1ComplToLp_resolvent_unconditional_via_density
      (I := I) (M := M) g φ hu_h h_smooth_seq h_conv_H1Compl
      h_conv_candidate h_smooth_identity).symm

/-- **Density-extension regularity theorem, iterated-closure form**. -/
theorem smoothMulH1Compl_mem_pow_two_via_density
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
      laplacianDomainPow (I := I) (M := M) g 2 := by
  classical
  rw [smoothMulH1Compl_mem_pow_two_iff_gradInnerCLM_mem_image
    (I := I) (M := M) g φ hu_h]
  exact gradInnerCLM_mem_image_laplacianDomain_via_density
    (I := I) (M := M) g φ hu_h h_smooth_seq h_conv_H1Compl
    h_conv_candidate h_smooth_identity

/-- The composition `n ↦ gradInnerCLM g φ (smoothToH1Compl (h_smooth_seq n))`
converges in `Lp` when `smoothToH1Compl (h_smooth_seq n) → u_h` in `H¹Compl`. -/
theorem gradInnerCLM_smoothSeq_conv
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (h_smooth_seq : ℕ → SmoothScalar g)
    (h_conv_H1Compl : Tendsto
      (fun n => smoothToH1Compl (I := I) (M := M) g (h_smooth_seq n))
      atTop (𝓝 u_h)) :
    Tendsto
      (fun n => gradInnerCLM (I := I) (M := M) g φ
        (smoothToH1Compl (I := I) (M := M) g (h_smooth_seq n)))
      atTop (𝓝 (gradInnerCLM (I := I) (M := M) g φ u_h)) :=
  ((gradInnerCLM (I := I) (M := M) g φ).continuous.tendsto _).comp h_conv_H1Compl

/-- The composition `n ↦ ricciPairingCLM g φ (smoothToH1Compl (h_smooth_seq n))`
converges in `Lp` when `smoothToH1Compl (h_smooth_seq n) → u_h` in `H¹Compl`. -/
theorem ricciPairingCLM_smoothSeq_conv
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (h_smooth_seq : ℕ → SmoothScalar g)
    (h_conv_H1Compl : Tendsto
      (fun n => smoothToH1Compl (I := I) (M := M) g (h_smooth_seq n))
      atTop (𝓝 u_h)) :
    Tendsto
      (fun n => ricciPairingCLM (I := I) (M := M) g φ
        (smoothToH1Compl (I := I) (M := M) g (h_smooth_seq n)))
      atTop (𝓝 (ricciPairingCLM (I := I) (M := M) g φ u_h)) :=
  ((ricciPairingCLM (I := I) (M := M) g φ).continuous.tendsto _).comp h_conv_H1Compl

end GradInnerLaplacianDensityExtension
end Laplacian
end Analysis
end DifferentialGeometry

end
