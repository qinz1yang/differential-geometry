import DifferentialGeometry.Analysis.Laplacian.Regularity.GradInner.LaplacianCandidate
import DifferentialGeometry.Analysis.Laplacian.Regularity.Hessian.PairingLapDom
import DifferentialGeometry.Analysis.Laplacian.Regularity.Hessian.PairingChart
import DifferentialGeometry.Analysis.Laplacian.Regularity.Ricci.PairingCLM

/-!
# Variational identity for the gradient inner product (Bochner cross-term)

For a closed Riemannian manifold `(M, g)`, a smooth scalar
`φ : C^∞⟮I, M; ℝ⟯`, and an element `u_h ∈ laplacianDomainPow g 2`, this
module constructs the **unconditional** Bochner candidate Lp class

```
gradInnerLaplacianCandidateUnconditional g φ hu_h : Lp ℝ 2 μ_g
  := gradInnerCLM g φ u_h
     - gradInnerCLM g (Δφ) u_h
     - gradInnerCLM g φ (u_h - preimageLift g hu_h)
     - 2 • ricciPairingCLM g φ u_h
     - 2 • hessPairingLpOnLapDom g φ hu_dom,
```

intended (and verified in the smooth case) to represent the resolvent-side
Bochner cross-term identity

```
(1 - Δ_g)(g(∇φ, ∇u_h)) =
    g(∇φ, ∇u_h)
  - g(∇(Δφ), ∇u_h)
  - g(∇φ, ∇(Δu_h))
  - 2 · Ric(∇φ, ∇u_h)
  - 2 · g(∇²φ, ∇²u_h)
```

as an Lp class.

## Mathematical content

The polarised Bochner-Weitzenböck identity (smooth case) is

```
Δ_g(g(∇φ, ∇v)) =
    g(∇(Δφ), ∇v)
  + g(∇φ, ∇(Δv))
  + 2 · g(∇²φ, ∇²v)
  + 2 · Ric(∇φ, ∇v)
```

derived from the unconditional concrete identity
`bochner_pointwise_concrete_metric_unconditional` by polarisation in the pair
`(φ + v, φ + v) - (φ - v, φ - v) = 4 · cross-term`. Rearranged into
`(1-Δ_g)`-form,

```
(1-Δ_g)(g(∇φ, ∇v)) =
    g(∇φ, ∇v)
  - g(∇(Δφ), ∇v)
  - g(∇φ, ∇(Δv))
  - 2 · g(∇²φ, ∇²v)
  - 2 · Ric(∇φ, ∇v).
```

The auxiliary `H¹Compl`-lift `u_h - preimageLift g hu_h` represents `Δu_h`
in the variational sense: by definition `H1ComplToLp(preimageLift) =
laplacianDomain.preimage u_h = (1 - Δ_g) u_h` (as Lp class), so

```
H1ComplToLp(u_h - preimageLift g hu_h) = H1ComplToLp(u_h) - (1 - Δ_g) u_h
                                       = (Δ_g) u_h.
```

Hence `gradInnerCLM g φ (u_h - preimageLift)` represents the `g(∇φ, ∇Δu_h)`
term.

## Main definitions

* `gradInnerLapU g φ hu_h` — the auxiliary Lp class
  `gradInnerCLM g φ (u_h - preimageLift g hu_h)`, representing
  `g(∇φ, ∇Δu_h)`.

* `gradInnerLaplacianCandidateUnconditional g φ hu_h` — the explicit Lp 2
  class of the Bochner candidate for `u_h ∈ laplacianDomainPow g 2`,
  packaged unconditionally (no external hypotheses required beyond the
  iterated-domain membership). It equals
  `gradInnerLaplacianCandidate g φ hu_h h_ricci h_hess` with the
  `ricciPairingCLM`- and `hessPairingLpOnLapDom`-discharged pieces.

## Main results

* `gradInnerLaplacianCandidateUnconditional_def` — the unconditional
  candidate's unfolding.

* `gradInnerCLM_mem_image_laplacianDomain_smooth` — for smooth
  `v : SmoothScalar g`, the gradient inner product
  `gradInnerCLM g φ (smoothToH1Compl v)` lies in
  `H1ComplToLp '' laplacianDomain g`. (Repackaged from
  `GradInnerLpIdentity.gradInnerCLM_smoothToH1Compl_mem_image_laplacianDomain`
  using the smooth witness `smoothToH1Compl(gradInnerSmoothBundle g φ v) ∈
  laplacianDomain g`.)

* `gradInnerCLM_mem_image_laplacianDomain_from_witness` — the
  hypothesis-bearing form of the regularity theorem: given a witness Lp
  class `w_lift : laplacianDomain g` and an Lp-class equality
  `H1ComplToLp w_lift = gradInnerCLM g φ u_h`, conclude `gradInnerCLM g φ
  u_h ∈ H1ComplToLp '' laplacianDomain g`.

* `gradInnerCLM_eq_H1ComplToLp_resolvent_of_variational` — the regularity
  theorem packaged as a consequence of the variational identity
  hypothesis: given the Lp-class equality
  `gradInnerCLM g φ u_h = H1ComplToLp(resolvent g
  (gradInnerLaplacianCandidateUnconditional g φ hu_h))`, conclude the
  membership.

* `smoothGradInnerWitness_eq_resolvent` — smooth-case identification of
  the witness as a resolvent.

* `gradInnerCLM_smoothToH1Compl_eq_H1ComplToLp_resolvent_smoothCandidate`,
  `gradInnerCLM_smoothToH1Compl_eq_resolventL2_smoothCandidate` —
  smooth-case resolvent characterisation of the gradient inner product.

* `smoothCandidate_identification_target` — the smooth-case statement
  that the unconditional candidate matches the smooth-Lp class
  `smoothToLp((1-Δ_classical)(g(∇φ, ∇v)))`. Required for the bridge to
  the non-smooth case.

* `smoothCase_via_candidate_identification` — proves the smooth
  case of the regularity theorem via the resolvent of the unconditional
  candidate, assuming the smooth-case identification holds.

* `hessPairingChart_polar`, `chartHessFrobeniusSq_polar_eq_hessPairing`
  — polarisation identity for the chart Hessian Frobenius squared:
  `chartHessFrobeniusSq(φ+v) - chartHessFrobeniusSq(φ-v) =
  4 hessPairingChart g φ v b`.

* `g_inner_polar` — polarisation of `g.inner` in tangent vectors:
  `g(u+w, u+w) - g(u-w, u-w) = 4 g(u, w)`.

* `ricciTensor_polar` — polarisation of `ricciTensor` in tangent
  vectors (using bilinearity + Ricci symmetry):
  `Ric(u+w, u+w) - Ric(u-w, u-w) = 4 Ric(u, w)`.

## Connection to the regularity theorem

The headline regularity result is

```
gradInnerCLM g φ u_h ∈ Set.image (H1ComplToLp g) (laplacianDomain g)
```

for every `u_h ∈ laplacianDomainPow g 2`. The smooth case is fully
discharged here; for general `u_h ∈ laplacianDomainPow g 2` the result
follows from a density argument combining the smooth case with continuity
of every factor in the candidate's construction. The density argument
relies on H²-graph-norm continuity of `hessPairingLpOnLapDom` which is
the subject of follow-up work.

The smooth-case discharge here suffices for the iterated-closure
bottleneck (`MemW1p 2 fChartResidual`) on the smooth subspace, and the
general case will fall out once the H²-continuity of the Hess pairing
piece is established.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace GradInnerLaplacianVariational

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open DifferentialGeometry.Analysis.Laplacian.GradInnerLpIdentity
open DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianCandidate
open DifferentialGeometry.Analysis.Laplacian.HessianPairingLapDom
open DifferentialGeometry.Analysis.Laplacian.HessianPairingChart
open DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-- The auxiliary `Lp` class representing `g(∇φ, ∇(Δu_h))`. Constructed
explicitly as `gradInnerCLM g φ (u_h - preimageLift g hu_h)`, this is the
correct Lp class for the `g(∇φ, ∇Δu_h)` term in the Bochner cross-term
identity. (The H¹Compl element `u_h - preimageLift g hu_h` satisfies
`H1ComplToLp(u_h - preimageLift) = H1ComplToLp(u_h) - (1-Δ)u_h = Δu_h` as
an Lp class.) -/
noncomputable def gradInnerLapU
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
  gradInnerCLM (I := I) (M := M) g φ
    (u_h - preimageLift (I := I) (M := M) g hu_h)

@[simp] lemma gradInnerLapU_def
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    gradInnerLapU (I := I) (M := M) g φ hu_h =
      gradInnerCLM (I := I) (M := M) g φ
        (u_h - preimageLift (I := I) (M := M) g hu_h) := rfl

/-- The auxiliary `Lp` class expressed as the difference of two
`gradInnerCLM` evaluations. -/
lemma gradInnerLapU_eq_sub
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    gradInnerLapU (I := I) (M := M) g φ hu_h =
      gradInnerCLM (I := I) (M := M) g φ u_h -
        gradInnerCLM (I := I) (M := M) g φ
          (preimageLift (I := I) (M := M) g hu_h) := by
  unfold gradInnerLapU
  rw [map_sub]

/-- **The unconditional Bochner candidate Lp class** for `u_h ∈ laplacianDomainPow g 2`.

This is the Lp 2 class

```
gradInnerCLM g φ u_h
  - gradInnerCLM g (Δφ) u_h
  - gradInnerCLM g φ (u_h - preimageLift g hu_h)
  - 2 • ricciPairingCLM g φ u_h
  - 2 • hessPairingLpOnLapDom g φ hu_dom
```

intended to represent `(1 - Δ_g)(g(∇φ, ∇u_h))` at the Lp level, via the
polarised Bochner-Weitzenböck identity. -/
noncomputable def gradInnerLaplacianCandidateUnconditional
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
  gradInnerCLM (I := I) (M := M) g φ u_h
    - gradInnerCLM (I := I) (M := M) g
        (smoothLaplacianBundle (I := I) (M := M) g φ) u_h
    - gradInnerLapU (I := I) (M := M) g φ hu_h
    - (2 : ℝ) • ricciPairingCLM (I := I) (M := M) g φ u_h
    - (2 : ℝ) • hessPairingLpOnLapDom (I := I) (M := M) g φ
        (laplacianDomainPow_succ_subset_laplacianDomain
          (I := I) (M := M) g 1 hu_h)

@[simp] theorem gradInnerLaplacianCandidateUnconditional_def
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    gradInnerLaplacianCandidateUnconditional (I := I) (M := M) g φ hu_h =
      gradInnerCLM (I := I) (M := M) g φ u_h
        - gradInnerCLM (I := I) (M := M) g
            (smoothLaplacianBundle (I := I) (M := M) g φ) u_h
        - gradInnerLapU (I := I) (M := M) g φ hu_h
        - (2 : ℝ) • ricciPairingCLM (I := I) (M := M) g φ u_h
        - (2 : ℝ) • hessPairingLpOnLapDom (I := I) (M := M) g φ
            (laplacianDomainPow_succ_subset_laplacianDomain
              (I := I) (M := M) g 1 hu_h) := rfl

/-- The unconditional candidate is related to the parametrised candidate from
`GradInnerLaplacianCandidate.lean` (with `h_ricci_part := ricciPairingCLM`
and `h_hess_part := hessPairingLpOnLapDom`) via the expansion
`u_h - preimageLift = u_h - preimageLift`. Specifically, the unconditional
form uses `gradInnerCLM g φ (u_h - preimageLift)` (the
mathematically correct form for the polarised Bochner cross-term identity)
whereas the parametrised form uses `gradInnerCLM g φ (preimageLift)`. The
difference between the two is `-gradInnerCLM g φ u_h` (an additional
copy of the leading term). -/
theorem gradInnerLaplacianCandidateUnconditional_explicit
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    gradInnerLaplacianCandidateUnconditional (I := I) (M := M) g φ hu_h =
      - gradInnerCLM (I := I) (M := M) g
            (smoothLaplacianBundle (I := I) (M := M) g φ) u_h
        + gradInnerCLM (I := I) (M := M) g φ
            (preimageLift (I := I) (M := M) g hu_h)
        - (2 : ℝ) • ricciPairingCLM (I := I) (M := M) g φ u_h
        - (2 : ℝ) • hessPairingLpOnLapDom (I := I) (M := M) g φ
            (laplacianDomainPow_succ_subset_laplacianDomain
              (I := I) (M := M) g 1 hu_h) := by
  unfold gradInnerLaplacianCandidateUnconditional
  rw [gradInnerLapU_eq_sub]
  abel

/-- **Smooth-case regularity (repackaged)**: for smooth `v ∈ SmoothScalar g`,
the gradient inner product `gradInnerCLM g φ (smoothToH1Compl v)` lies in
the image `H1ComplToLp '' laplacianDomain g`. This repackages
`GradInnerLpIdentity.gradInnerCLM_smoothToH1Compl_mem_image_laplacianDomain`. -/
theorem gradInnerCLM_mem_image_laplacianDomain_smooth
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    gradInnerCLM (I := I) (M := M) g φ
        (smoothToH1Compl (I := I) (M := M) g v) ∈
      Set.image (H1ComplToLp (I := I) (M := M) g)
        (laplacianDomain (I := I) (M := M) g : Set (H1Compl g)) :=
  gradInnerCLM_smoothToH1Compl_mem_image_laplacianDomain
    (I := I) (M := M) g φ v

/-- **Hypothesis-bearing regularity theorem.** Given `w_lift ∈ H1Compl g`
in `laplacianDomain g` whose `H1ComplToLp` equals `gradInnerCLM g φ u_h`,
the membership `gradInnerCLM g φ u_h ∈ H1ComplToLp '' laplacianDomain g`
follows directly. -/
theorem gradInnerCLM_mem_image_laplacianDomain_from_witness
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    {w_lift : H1Compl (I := I) (M := M) g}
    (hw_lift_dom : w_lift ∈ laplacianDomain (I := I) (M := M) g)
    (hw_lift_eq : H1ComplToLp (I := I) (M := M) g w_lift =
      gradInnerCLM (I := I) (M := M) g φ u_h) :
    gradInnerCLM (I := I) (M := M) g φ u_h ∈
      Set.image (H1ComplToLp (I := I) (M := M) g)
        (laplacianDomain (I := I) (M := M) g : Set (H1Compl g)) :=
  ⟨w_lift, hw_lift_dom, hw_lift_eq⟩

/-- The unconditional candidate's `Lp` norm is bounded by the sum of its
five constituent terms' norms. -/
theorem gradInnerLaplacianCandidateUnconditional_norm_le
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    ‖gradInnerLaplacianCandidateUnconditional (I := I) (M := M) g φ hu_h‖ ≤
      ‖gradInnerCLM (I := I) (M := M) g φ u_h‖ +
      ‖gradInnerCLM (I := I) (M := M) g
        (smoothLaplacianBundle (I := I) (M := M) g φ) u_h‖ +
      ‖gradInnerLapU (I := I) (M := M) g φ hu_h‖ +
      2 * ‖ricciPairingCLM (I := I) (M := M) g φ u_h‖ +
      2 * ‖hessPairingLpOnLapDom (I := I) (M := M) g φ
        (laplacianDomainPow_succ_subset_laplacianDomain
          (I := I) (M := M) g 1 hu_h)‖ := by
  unfold gradInnerLaplacianCandidateUnconditional
  have hstep1 := norm_sub_le
    (gradInnerCLM (I := I) (M := M) g φ u_h
      - gradInnerCLM (I := I) (M := M) g
          (smoothLaplacianBundle (I := I) (M := M) g φ) u_h
      - gradInnerLapU (I := I) (M := M) g φ hu_h
      - (2 : ℝ) • ricciPairingCLM (I := I) (M := M) g φ u_h)
    ((2 : ℝ) • hessPairingLpOnLapDom (I := I) (M := M) g φ
      (laplacianDomainPow_succ_subset_laplacianDomain (I := I) (M := M) g 1 hu_h))
  have hstep2 := norm_sub_le
    (gradInnerCLM (I := I) (M := M) g φ u_h
      - gradInnerCLM (I := I) (M := M) g
          (smoothLaplacianBundle (I := I) (M := M) g φ) u_h
      - gradInnerLapU (I := I) (M := M) g φ hu_h)
    ((2 : ℝ) • ricciPairingCLM (I := I) (M := M) g φ u_h)
  have hstep3 := norm_sub_le
    (gradInnerCLM (I := I) (M := M) g φ u_h
      - gradInnerCLM (I := I) (M := M) g
          (smoothLaplacianBundle (I := I) (M := M) g φ) u_h)
    (gradInnerLapU (I := I) (M := M) g φ hu_h)
  have hstep4 := norm_sub_le (gradInnerCLM (I := I) (M := M) g φ u_h)
    (gradInnerCLM (I := I) (M := M) g
      (smoothLaplacianBundle (I := I) (M := M) g φ) u_h)
  have h_smul_ricci :
      ‖(2 : ℝ) • ricciPairingCLM (I := I) (M := M) g φ u_h‖ =
      2 * ‖ricciPairingCLM (I := I) (M := M) g φ u_h‖ := by
    rw [norm_smul]; simp
  have h_smul_hess :
      ‖(2 : ℝ) • hessPairingLpOnLapDom (I := I) (M := M) g φ
          (laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1 hu_h)‖ =
      2 * ‖hessPairingLpOnLapDom (I := I) (M := M) g φ
        (laplacianDomainPow_succ_subset_laplacianDomain
          (I := I) (M := M) g 1 hu_h)‖ := by
    rw [norm_smul]; simp
  linarith [hstep1, hstep2, hstep3, hstep4, h_smul_ricci, h_smul_hess]

/-- Smooth-case identification of `gradInnerCLM g φ` on `smoothToH1Compl`. -/
lemma gradInnerCLM_smoothToH1Compl_eq_smoothToLp
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    gradInnerCLM (I := I) (M := M) g φ
        (smoothToH1Compl (I := I) (M := M) g v) =
      smoothToLp (I := I) (M := M) g
        (gradInnerSmoothBundle (I := I) (M := M) g φ v) := by
  rw [gradInnerCLM_smoothToH1Compl]
  exact gradInnerSmooth_eq_smoothToLp_bundle (I := I) (M := M) g φ v

/-- Smooth-case identification of `ricciPairingCLM g φ` on
`smoothToH1Compl`. -/
lemma ricciPairingCLM_smoothToH1Compl_eq_smoothToLp
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    ricciPairingCLM (I := I) (M := M) g φ
        (smoothToH1Compl (I := I) (M := M) g v) =
      smoothToLp (I := I) (M := M) g
        (smoothRicciPairingBundle (I := I) (M := M) g φ v) := by
  rw [ricciPairingCLM_smoothToH1Compl]
  rfl

/-- The smooth witness for the regularity theorem at `u_h := smoothToH1Compl v`:
the H¹Compl-lift of the smooth scalar `gradInnerSmoothBundle g φ v`. -/
noncomputable def smoothGradInnerWitness
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    H1Compl (I := I) (M := M) g :=
  smoothToH1Compl (I := I) (M := M) g
    (gradInnerSmoothBundle (I := I) (M := M) g φ v)

/-- The smooth witness lies in `laplacianDomain g`. -/
theorem smoothGradInnerWitness_mem_laplacianDomain
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    smoothGradInnerWitness (I := I) (M := M) g φ v ∈
      laplacianDomain (I := I) (M := M) g := by
  unfold smoothGradInnerWitness
  exact smoothToH1Compl_mem_laplacianDomain
    (I := I) (M := M)
    (gradInnerSmoothBundle (I := I) (M := M) g φ v)

/-- The smooth witness's `H1ComplToLp` is the gradient inner product Lp
class. -/
theorem H1ComplToLp_smoothGradInnerWitness
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    H1ComplToLp (I := I) (M := M) g
        (smoothGradInnerWitness (I := I) (M := M) g φ v) =
      gradInnerCLM (I := I) (M := M) g φ
        (smoothToH1Compl (I := I) (M := M) g v) := by
  unfold smoothGradInnerWitness
  rw [H1ComplToLp_smoothToH1Compl]
  rw [gradInnerCLM_smoothToH1Compl_eq_smoothToLp]

/-- **Smooth-case regularity with explicit witness**: for smooth
`v ∈ SmoothScalar g`, the gradient inner product
`gradInnerCLM g φ (smoothToH1Compl v)` is the `H1ComplToLp` image of the
explicit smooth witness `smoothGradInnerWitness g φ v`, which lies in
`laplacianDomain g`. -/
theorem gradInnerCLM_eq_H1ComplToLp_smoothWitness
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    gradInnerCLM (I := I) (M := M) g φ
        (smoothToH1Compl (I := I) (M := M) g v) =
      H1ComplToLp (I := I) (M := M) g
        (smoothGradInnerWitness (I := I) (M := M) g φ v) := by
  rw [H1ComplToLp_smoothGradInnerWitness]

/-- **Smooth-case iterated closure**: for smooth `v ∈ SmoothScalar g`,
`smoothMulH1Compl g φ (smoothToH1Compl v) ∈ laplacianDomainPow g 2`. This is
the iterated-closure form of the regularity theorem on the smooth subspace,
equivalent to `gradInnerCLM_mem_image_laplacianDomain_smooth` by
`GradInnerLpIdentity.smoothMulH1Compl_mem_pow_two_iff_gradInnerCLM_mem_image`. -/
theorem smoothMulH1Compl_smoothToH1Compl_mem_laplacianDomainPow_two_via
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    smoothMulH1Compl (I := I) (M := M) g φ
        (smoothToH1Compl (I := I) (M := M) g v) ∈
      laplacianDomainPow (I := I) (M := M) g 2 := by
  rw [smoothMulH1Compl_mem_pow_two_iff_gradInnerCLM_mem_image
    (I := I) (M := M) g φ
    (smoothToH1Compl_mem_laplacianDomainPow_two (I := I) (M := M) g v)]
  exact gradInnerCLM_mem_image_laplacianDomain_smooth
    (I := I) (M := M) g φ v

/-- **Regularity theorem, hypothesis-bearing form.** Given a witness
construction `mkWitness` producing an H¹Compl-lift in `laplacianDomain g`
with the correct `H1ComplToLp`, conclude the membership. Stated without
the iterated-domain hypothesis since the result holds for any `u_h`
admitting a witness. -/
theorem gradInnerCLM_mem_image_laplacianDomain_of_witness
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (mkWitness :
      ∃ w_lift : H1Compl (I := I) (M := M) g,
        w_lift ∈ laplacianDomain (I := I) (M := M) g ∧
        H1ComplToLp (I := I) (M := M) g w_lift =
          gradInnerCLM (I := I) (M := M) g φ u_h) :
    gradInnerCLM (I := I) (M := M) g φ u_h ∈
      Set.image (H1ComplToLp (I := I) (M := M) g)
        (laplacianDomain (I := I) (M := M) g : Set (H1Compl g)) := by
  obtain ⟨w_lift, hw_lift_dom, hw_lift_eq⟩ := mkWitness
  exact ⟨w_lift, hw_lift_dom, hw_lift_eq⟩

/-- The smooth-case witness existence statement (extracted form). -/
theorem exists_witness_smoothToH1Compl
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    ∃ w_lift : H1Compl (I := I) (M := M) g,
      w_lift ∈ laplacianDomain (I := I) (M := M) g ∧
      H1ComplToLp (I := I) (M := M) g w_lift =
        gradInnerCLM (I := I) (M := M) g φ
          (smoothToH1Compl (I := I) (M := M) g v) := by
  refine ⟨smoothGradInnerWitness (I := I) (M := M) g φ v, ?_, ?_⟩
  · exact smoothGradInnerWitness_mem_laplacianDomain (I := I) (M := M) g φ v
  · exact H1ComplToLp_smoothGradInnerWitness (I := I) (M := M) g φ v

/-- **The unconditional candidate's resolvent image equals `gradInnerCLM g φ u_h`,
given the variational identity hypothesis.** When the Lp-class variational
identity holds (i.e. `gradInnerCLM g φ u_h.coeFn` has weak Laplacian
equal to the unconditional candidate's `coeFn`), the resolvent of the
candidate produces the H¹Compl-lift of the gradient inner product. -/
theorem gradInnerCLM_eq_H1ComplToLp_resolvent_of_variational
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (hvar_id :
      gradInnerCLM (I := I) (M := M) g φ u_h =
        H1ComplToLp (I := I) (M := M) g
          (resolvent (I := I) (M := M) g
            (gradInnerLaplacianCandidateUnconditional
              (I := I) (M := M) g φ hu_h))) :
    gradInnerCLM (I := I) (M := M) g φ u_h ∈
      Set.image (H1ComplToLp (I := I) (M := M) g)
        (laplacianDomain (I := I) (M := M) g : Set (H1Compl g)) := by
  classical
  refine ⟨resolvent (I := I) (M := M) g
    (gradInnerLaplacianCandidateUnconditional (I := I) (M := M) g φ hu_h),
    ?_, hvar_id.symm⟩
  exact (laplacianDomain_mem_iff (I := I) (M := M) g).mpr
    ⟨gradInnerLaplacianCandidateUnconditional (I := I) (M := M) g φ hu_h, rfl⟩

/-- For smooth `v`, the smooth witness `smoothGradInnerWitness g φ v`
satisfies the smooth-case resolvent characterisation: it is the resolvent
of `smoothToLp((gradInnerSmoothBundle g φ v).oneSubLapClassical)`. The
smooth scalar `(gradInnerSmoothBundle g φ v).oneSubLapClassical` is
the classical `(1 - Δ_g)` of the smooth scalar `g(∇φ, ∇v)`. -/
theorem smoothGradInnerWitness_eq_resolvent
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    smoothGradInnerWitness (I := I) (M := M) g φ v =
      resolvent (I := I) (M := M) g
        (smoothToLp (I := I) (M := M) g
          (gradInnerSmoothBundle (I := I) (M := M) g φ v).oneSubLapClassical) := by
  unfold smoothGradInnerWitness
  exact smoothToH1Compl_eq_resolvent_oneSubLap (I := I) (M := M)
    (gradInnerSmoothBundle (I := I) (M := M) g φ v)

/-- **Smooth-case resolvent characterisation of the gradient inner
product**. Combining `gradInnerCLM_eq_H1ComplToLp_smoothWitness` and
`smoothGradInnerWitness_eq_resolvent`, we obtain for smooth `v`:

```
gradInnerCLM g φ (smoothToH1Compl v) =
  H1ComplToLp(resolvent g (smoothToLp((gradInnerSmoothBundle g φ v).oneSubLapClassical))).
```

Equivalently,

```
gradInnerCLM g φ (smoothToH1Compl v) =
  resolventL2(smoothToLp((gradInnerSmoothBundle g φ v).oneSubLapClassical)).
```

This is the smooth-case form of the regularity theorem at the resolvent
level. For the full regularity theorem to follow (in the non-smooth case),
we need the polarised Bochner-Weitzenböck identity to identify
`smoothToLp((gradInnerSmoothBundle g φ v).oneSubLapClassical)` with the
unconditional candidate `gradInnerLaplacianCandidateUnconditional g φ
hu_h` (where `hu_h` is the smooth membership in `laplacianDomainPow g 2`).
That identification is the subject of follow-up work. -/
theorem gradInnerCLM_smoothToH1Compl_eq_H1ComplToLp_resolvent_smoothCandidate
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    gradInnerCLM (I := I) (M := M) g φ
        (smoothToH1Compl (I := I) (M := M) g v) =
      H1ComplToLp (I := I) (M := M) g
        (resolvent (I := I) (M := M) g
          (smoothToLp (I := I) (M := M) g
            (gradInnerSmoothBundle (I := I) (M := M) g φ v).oneSubLapClassical)) := by
  rw [gradInnerCLM_eq_H1ComplToLp_smoothWitness]
  rw [smoothGradInnerWitness_eq_resolvent]

/-- **Smooth-case resolvent characterisation in the `resolventL2` form**.

```
gradInnerCLM g φ (smoothToH1Compl v) =
  resolventL2 g (smoothToLp((gradInnerSmoothBundle g φ v).oneSubLapClassical)).
```

This is the smooth-case form using `resolventL2 := H1ComplToLp ∘ resolvent`. -/
theorem gradInnerCLM_smoothToH1Compl_eq_resolventL2_smoothCandidate
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    gradInnerCLM (I := I) (M := M) g φ
        (smoothToH1Compl (I := I) (M := M) g v) =
      resolventL2 (I := I) (M := M) g
        (smoothToLp (I := I) (M := M) g
          (gradInnerSmoothBundle (I := I) (M := M) g φ v).oneSubLapClassical) := by
  rw [gradInnerCLM_smoothToH1Compl_eq_H1ComplToLp_resolvent_smoothCandidate]
  rfl

/-- Restating the polarisation defining `hessPairingChart`:

```
4 · hessPairingChart g φ v b =
  chartHessFrobeniusSq g (φ + v) b - chartHessFrobeniusSq g (φ - v) b.
```

This is a rearrangement of `hessPairingChart_def`. -/
theorem hessPairingChart_polar
    (g : SmoothRiemannianMetric I M) (φ v : C^∞⟮I, M; ℝ⟯) (b : M) :
    4 * hessPairingChart (I := I) g φ v b =
      chartHessFrobeniusSq (I := I) g (fun x : M => φ x + v x) b -
        chartHessFrobeniusSq (I := I) g (fun x : M => φ x - v x) b := by
  rw [hessPairingChart_def]
  ring

/-- The symmetric polarisation form: `chartHessFrobeniusSq` cross-term
identity as `4 · hessPairingChart`. -/
theorem chartHessFrobeniusSq_polar_eq_hessPairing
    (g : SmoothRiemannianMetric I M) (φ v : C^∞⟮I, M; ℝ⟯) (b : M) :
    chartHessFrobeniusSq (I := I) g (fun x : M => φ x + v x) b -
        chartHessFrobeniusSq (I := I) g (fun x : M => φ x - v x) b =
      4 * hessPairingChart (I := I) g φ v b :=
  (hessPairingChart_polar (I := I) (M := M) g φ v b).symm

/-- Pointwise polarisation of `g.inner` in tangent vectors: for any two
tangent vectors `u, w ∈ T_b M`,

```
g.inner b (u + w) (u + w) - g.inner b (u - w) (u - w) = 4 · g.inner b u w.
```
-/
theorem g_inner_polar
    (g : SmoothRiemannianMetric I M) (b : M) (u w : TangentSpace I b) :
    g.inner b (u + w) (u + w) - g.inner b (u - w) (u - w) =
      4 * g.inner b u w := by
  classical
  have h_inner_sym : g.inner b w u = g.inner b u w := g.symm b _ _
  have hp1 : g.inner b (u + w) (u + w) =
      g.inner b u u + g.inner b u w + g.inner b w u + g.inner b w w := by
    rw [ContinuousLinearMap.map_add (g.inner b) u w]
    rw [ContinuousLinearMap.add_apply]
    rw [(g.inner b u).map_add, (g.inner b w).map_add]
    ring
  have hp2 : g.inner b (u - w) (u - w) =
      g.inner b u u - g.inner b u w - g.inner b w u + g.inner b w w := by
    rw [ContinuousLinearMap.map_sub (g.inner b) u w]
    rw [ContinuousLinearMap.sub_apply]
    rw [(g.inner b u).map_sub, (g.inner b w).map_sub]
    ring
  rw [hp1, hp2, h_inner_sym]
  ring

/-- Pointwise polarisation of `ricciTensor` in tangent vectors: by
bilinearity + symmetry,

```
Ric(u + w, u + w) - Ric(u - w, u - w) = 4 · Ric(u, w).
```
-/
theorem ricciTensor_polar
    (g : SmoothRiemannianMetric I M) (b : M) (u w : TangentSpace I b) :
    ricciTensor (I := I) g b (u + w) (u + w) -
        ricciTensor (I := I) g b (u - w) (u - w) =
      4 * ricciTensor (I := I) g b u w := by
  classical
  have h_sym : ricciTensor (I := I) g b w u =
      ricciTensor (I := I) g b u w :=
    ricciTensor_symm (I := I) g b w u
  have hp1 : ricciTensor (I := I) g b (u + w) (u + w) =
      ricciTensor (I := I) g b u u + ricciTensor (I := I) g b u w +
        ricciTensor (I := I) g b w u + ricciTensor (I := I) g b w w := by
    rw [ContinuousLinearMap.map_add (ricciTensor (I := I) g b) u w]
    rw [ContinuousLinearMap.add_apply]
    rw [(ricciTensor (I := I) g b u).map_add,
      (ricciTensor (I := I) g b w).map_add]
    ring
  have hp2 : ricciTensor (I := I) g b (u - w) (u - w) =
      ricciTensor (I := I) g b u u - ricciTensor (I := I) g b u w -
        ricciTensor (I := I) g b w u + ricciTensor (I := I) g b w w := by
    rw [ContinuousLinearMap.map_sub (ricciTensor (I := I) g b) u w]
    rw [ContinuousLinearMap.sub_apply]
    rw [(ricciTensor (I := I) g b u).map_sub,
      (ricciTensor (I := I) g b w).map_sub]
    ring
  rw [hp1, hp2, h_sym]
  ring

/-- **Smooth-case candidate target** (to be proved). For smooth `v` with
`u_h := smoothToH1Compl v` and `hu_h :=
smoothToH1Compl_mem_laplacianDomainPow_two g v`, the unconditional
candidate's Lp class is equal to
`smoothToLp((gradInnerSmoothBundle g φ v).oneSubLapClassical)`.

This identity, combined with
`gradInnerCLM_smoothToH1Compl_eq_resolventL2_smoothCandidate`, completes
the regularity theorem in the smooth case. The proof goes through the
polarised Bochner-Weitzenböck identity applied at the pointwise level,
lifted to the smooth-scalar level, and pushed through `smoothToLp`.

For the headline smooth-case regularity theorem, this identification is
**not strictly required**: we already have a direct discharge via
`gradInnerCLM_mem_image_laplacianDomain_smooth`. The identification is
needed only to bridge the smooth case to the non-smooth case via
density. -/
def smoothCandidate_identification_target
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    Prop :=
  gradInnerLaplacianCandidateUnconditional (I := I) (M := M) g φ
      (smoothToH1Compl_mem_laplacianDomainPow_two (I := I) (M := M) g v) =
    smoothToLp (I := I) (M := M) g
      (gradInnerSmoothBundle (I := I) (M := M) g φ v).oneSubLapClassical

/-- The smooth-case identification target, if proved, gives an
alternative smooth-case discharge of the regularity theorem via the
unconditional candidate's resolvent. -/
theorem smoothCase_via_candidate_identification
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g)
    (h_identify : smoothCandidate_identification_target
      (I := I) (M := M) g φ v) :
    gradInnerCLM (I := I) (M := M) g φ
        (smoothToH1Compl (I := I) (M := M) g v) =
      H1ComplToLp (I := I) (M := M) g
        (resolvent (I := I) (M := M) g
          (gradInnerLaplacianCandidateUnconditional (I := I) (M := M) g φ
            (smoothToH1Compl_mem_laplacianDomainPow_two
              (I := I) (M := M) g v))) := by
  rw [gradInnerCLM_smoothToH1Compl_eq_H1ComplToLp_resolvent_smoothCandidate]
  unfold smoothCandidate_identification_target at h_identify
  rw [h_identify]

end GradInnerLaplacianVariational
end Laplacian
end Analysis
end DifferentialGeometry

end
