import DifferentialGeometry.Analysis.Laplacian.Regularity.LaplacianDomain.SmoothMulH1Compl
import DifferentialGeometry.Analysis.Laplacian.Regularity.Iterated.LaplacianDomain
import DifferentialGeometry.Analysis.Laplacian.Regularity.Iterated.H2RegularityStep

/-!
# Manifold-side `Lp`-class identity for `gradInnerCLM g φ u_h`

For a closed Riemannian manifold `(M, g)` and an arbitrary smooth scalar
`φ : C^∞⟮I, M; ℝ⟯`, this module derives an explicit `Lp`-class identity for
twice the gradient inner product `2 · gradInnerCLM g φ u_h` valid for every
`u_h ∈ laplacianDomain g`.

The identity follows from the `(1-Δ)`-preimage formula
`laplacianDomain.preimage⟨smoothMulH1Compl g φ u_h⟩ = fHLeibnizGeneral g φ u_h hu_h`
combined with the definitional unfolding of `fHLeibnizGeneral` and
`fHLeibnizGeneralResidualCLM`.

## Main results

* `gradInnerCLM_eq_two_inv_preimageDiff` — for `u_h ∈ laplacianDomain g`:

  ```
  2 • gradInnerCLM g φ u_h
    = smoothMulLp g φ (preimage⟨u_h⟩)
      − preimage⟨smoothMulH1Compl g φ u_h⟩
      − smoothMulLp g (Δφ) (H1ComplToLp u_h).
  ```

  This rearranges the existing preimage decomposition; for
  `φ := chartAtlasPOU I M α` it specialises to (and is mathematically
  equivalent to) `ResidualLpDecomposition.fHLeibnizGeneralResidualCLM_eq_preimageDiff`.

* `gradInnerCLM_mem_H1ComplToLp_laplacianDomain_iff` — the equivalence

  ```
  gradInnerCLM g φ u_h ∈ H1ComplToLp '' (laplacianDomain g)
    ↔ smoothMulH1Compl g φ u_h ∈ laplacianDomainPow g 2,
  ```

  proved for `u_h ∈ laplacianDomainPow g 2`. The forward direction is the
  iterated regularity closure for `smoothMulH1Compl`; the reverse is the
  rearrangement of the Lp identity above using that the other two summands
  always lie in the image of the resolvent.

* `gradInnerCLM_mem_image_implies_smoothMulH1Compl_mem_pow_two` — direct
  implication form of the equivalence, packaged for downstream use.

## Connection to the iterated regularity bottleneck

For `u_h ∈ laplacianDomainPow g 2`, the membership
`smoothMulH1Compl g φ u_h ∈ laplacianDomainPow g 2` is the iterated closure of
the Laplacian domain under smooth multiplication. By the equivalence above,
this is precisely the question whether `gradInnerCLM g φ u_h` lifts to an
H¹Compl element in `laplacianDomain g`.

Equivalently: whether `g(∇φ, ∇u_h)` is H¹ chart-wise, which is true
mathematically (each chart-side ∂_j of `u_h` is H¹ for `u_h ∈ laplacianDomain g`,
and smooth-bounded `g_inv^{ij} · ∂_i φ ∘ symm` times H¹ is H¹). The chart-side
non-smooth formalisation requires a "raw" chart-pushed weak-partial Lp class
without partition-of-unity weight, which is a separate substantial
infrastructure item.

This file does NOT attempt that chart-side construction. It exposes the
equivalence cleanly so that the bottleneck localizes to a single, sharp
mathematical statement.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace GradInnerLpIdentity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul
open DifferentialGeometry.Analysis.Laplacian.MetricExtension

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-- Algebraic rearrangement in an additive commutative group:
`a = b - c - d ↔ c = b - a - d`. -/
private lemma sub_rearrange_three {α : Type*} [AddCommGroup α] {a b c d : α}
    (h : a = b - c - d) : c = b - a - d := by
  have hcomp : c = b - (b - c - d) - d := by abel
  rw [← h] at hcomp
  exact hcomp

/-- Algebraic rearrangement in an additive commutative group:
`a + b = c - d ↔ a = c - b - d`. (We don't actually need this; see
`sub_rearrange_three` instead.) -/
private lemma add_sub_rearrange {α : Type*} [AddCommGroup α] {a b c d : α}
    (h : a + b = c - d) : a = c - b - d := by
  have : a = c - d - b := by
    rw [← h]; abel
  rw [this]; abel

/-- **The general manifold-side `Lp`-class identity for `2 • gradInnerCLM g φ u_h`.**

For an arbitrary smooth scalar `φ : C^∞⟮I, M; ℝ⟯` and `u_h ∈ laplacianDomain g`,
twice the gradient inner product splits as the difference of two
`(1-Δ_g)`-preimages plus the smooth-multiplication of `u_h` by `Δφ`:

```
2 • gradInnerCLM g φ u_h
  = smoothMulLp g φ (preimage⟨u_h⟩)
    − preimage⟨smoothMulH1Compl g φ u_h⟩
    − smoothMulLp g (Δφ) (H1ComplToLp u_h).
```

This generalises `ResidualLpDecomposition.fHLeibnizGeneralResidualCLM_eq_preimageDiff`
from `φ := chartAtlasPOU I M α` to arbitrary smooth `φ`. -/
theorem gradInnerCLM_eq_two_inv_preimageDiff
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_dom : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    (2 : ℝ) • gradInnerCLM (I := I) (M := M) g φ u_h =
      smoothMulLp (I := I) (M := M) g φ
          (laplacianDomain.preimage (I := I) (M := M) g ⟨u_h, hu_dom⟩) -
        laplacianDomain.preimage (I := I) (M := M) g
          ⟨smoothMulH1Compl (I := I) (M := M) g φ u_h,
            smoothMulH1Compl_mem_laplacianDomain (I := I) (M := M) g φ hu_dom⟩ -
        smoothMulLp (I := I) (M := M) g
          (smoothLaplacianBundle (I := I) (M := M) g φ)
          (H1ComplToLp (I := I) (M := M) g u_h) := by
  classical
  have h_preimage :=
    laplacianDomain_preimage_smoothMulH1Compl (I := I) (M := M) g φ hu_dom
  unfold fHLeibnizGeneral at h_preimage
  have h_diff_eq :
      H1ComplToLp (I := I) (M := M) g u_h -
        laplacianOp (I := I) (M := M) g ⟨u_h, hu_dom⟩ =
      laplacianDomain.preimage (I := I) (M := M) g ⟨u_h, hu_dom⟩ := by
    rw [laplacianOp_apply]
    abel
  rw [h_diff_eq] at h_preimage
  have h_residual_apply := fHLeibnizGeneralResidualCLM_apply
    (I := I) (M := M) g φ u_h
  rw [h_residual_apply] at h_preimage
  have h_rearrange :
      smoothMulLp (I := I) (M := M) g φ
          (laplacianDomain.preimage (I := I) (M := M) g ⟨u_h, hu_dom⟩) +
        (-((2 : ℝ) • gradInnerCLM (I := I) (M := M) g φ u_h) -
          smoothMulLp (I := I) (M := M) g
            (smoothLaplacianBundle (I := I) (M := M) g φ)
            (H1ComplToLp (I := I) (M := M) g u_h)) =
      laplacianDomain.preimage (I := I) (M := M) g
        ⟨smoothMulH1Compl (I := I) (M := M) g φ u_h,
          smoothMulH1Compl_mem_laplacianDomain (I := I) (M := M) g φ hu_dom⟩ :=
    h_preimage.symm
  rw [← h_rearrange]
  abel

/-- The auxiliary lift of `preimage⟨u_h⟩ ∈ Lp` to an `H1Compl` element in
`laplacianDomain g`, available for `u_h ∈ laplacianDomainPow g 2`. -/
noncomputable def preimageLift
    (g : SmoothRiemannianMetric I M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    H1Compl (I := I) (M := M) g :=
  Classical.choose (laplacianDomainPow_two_preimage_eq (I := I) (M := M) g hu_h)

lemma preimageLift_mem_laplacianDomain
    (g : SmoothRiemannianMetric I M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    preimageLift (I := I) (M := M) g hu_h ∈
      laplacianDomain (I := I) (M := M) g :=
  (Classical.choose_spec (laplacianDomainPow_two_preimage_eq
    (I := I) (M := M) g hu_h)).1

lemma H1ComplToLp_preimageLift
    (g : SmoothRiemannianMetric I M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    H1ComplToLp (I := I) (M := M) g
        (preimageLift (I := I) (M := M) g hu_h) =
      laplacianDomain.preimage (I := I) (M := M) g
        ⟨u_h, laplacianDomainPow_succ_subset_laplacianDomain
          (I := I) (M := M) g 1 hu_h⟩ :=
  (Classical.choose_spec (laplacianDomainPow_two_preimage_eq
    (I := I) (M := M) g hu_h)).2

/-- For `u_h ∈ laplacianDomainPow g 2`, the `Lp`-class
`smoothMulLp g φ (preimage⟨u_h⟩)` lifts to `H1Compl`: it is the L²-image
of `smoothMulH1Compl g φ (preimageLift g hu_h) ∈ laplacianDomain g`. -/
theorem smoothMulLp_preimage_in_image_laplacianDomain
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    smoothMulLp (I := I) (M := M) g φ
        (laplacianDomain.preimage (I := I) (M := M) g
          ⟨u_h, laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1 hu_h⟩) ∈
      Set.image (H1ComplToLp (I := I) (M := M) g)
        (laplacianDomain (I := I) (M := M) g : Set (H1Compl g)) := by
  classical
  have hvH_mem := preimageLift_mem_laplacianDomain (I := I) (M := M) g hu_h
  have h_sM_mem := smoothMulH1Compl_mem_laplacianDomain
    (I := I) (M := M) g φ hvH_mem
  refine ⟨smoothMulH1Compl (I := I) (M := M) g φ
    (preimageLift (I := I) (M := M) g hu_h), ?_, ?_⟩
  · exact h_sM_mem
  · rw [H1ComplToLp_smoothMulH1Compl]
    rw [H1ComplToLp_preimageLift]

/-- For any `u_h ∈ H1Compl g`, the `Lp`-class
`smoothMulLp g (Δφ) (H1ComplToLp u_h)` lifts to `H1Compl` when
`u_h ∈ laplacianDomain g`: it equals `H1ComplToLp(smoothMulH1Compl g (Δφ) u_h)`
with `smoothMulH1Compl g (Δφ) u_h ∈ laplacianDomain g`. -/
theorem smoothMulLp_DeltaPhi_in_image_laplacianDomain
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_dom : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    smoothMulLp (I := I) (M := M) g
        (smoothLaplacianBundle (I := I) (M := M) g φ)
        (H1ComplToLp (I := I) (M := M) g u_h) ∈
      Set.image (H1ComplToLp (I := I) (M := M) g)
        (laplacianDomain (I := I) (M := M) g : Set (H1Compl g)) := by
  classical
  have h_sM_mem := smoothMulH1Compl_mem_laplacianDomain (I := I) (M := M) g
    (smoothLaplacianBundle (I := I) (M := M) g φ) hu_dom
  refine ⟨smoothMulH1Compl (I := I) (M := M) g
    (smoothLaplacianBundle (I := I) (M := M) g φ) u_h, ?_, ?_⟩
  · exact h_sM_mem
  · rw [H1ComplToLp_smoothMulH1Compl]

/-- **Reverse implication (gradInnerCLM image ⊆ iterated closure)**.

For `u_h ∈ laplacianDomainPow g 2`, if `gradInnerCLM g φ u_h` lifts to an
`H1Compl` element in `laplacianDomain g`, then so does
`preimage⟨smoothMulH1Compl g φ u_h⟩` (the `Lp` class `(1-Δ_g)(φ · u_h)`).
This is precisely the iterated closure
`smoothMulH1Compl g φ u_h ∈ laplacianDomainPow g 2`. -/
theorem smoothMulH1Compl_mem_pow_two_of_gradInnerCLM_mem_image
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (h_grad : gradInnerCLM (I := I) (M := M) g φ u_h ∈
      Set.image (H1ComplToLp (I := I) (M := M) g)
        (laplacianDomain (I := I) (M := M) g : Set (H1Compl g))) :
    smoothMulH1Compl (I := I) (M := M) g φ u_h ∈
      laplacianDomainPow (I := I) (M := M) g 2 := by
  classical
  have hu_dom := laplacianDomainPow_succ_subset_laplacianDomain
    (I := I) (M := M) g 1 hu_h
  have h_lp_identity :
      laplacianDomain.preimage (I := I) (M := M) g
          ⟨smoothMulH1Compl (I := I) (M := M) g φ u_h,
            smoothMulH1Compl_mem_laplacianDomain (I := I) (M := M) g φ hu_dom⟩ =
        smoothMulLp (I := I) (M := M) g φ
            (laplacianDomain.preimage (I := I) (M := M) g ⟨u_h, hu_dom⟩) -
          (2 : ℝ) • gradInnerCLM (I := I) (M := M) g φ u_h -
          smoothMulLp (I := I) (M := M) g
            (smoothLaplacianBundle (I := I) (M := M) g φ)
            (H1ComplToLp (I := I) (M := M) g u_h) := by
    have h := gradInnerCLM_eq_two_inv_preimageDiff
      (I := I) (M := M) g φ hu_dom
    exact sub_rearrange_three h
  have h1 := smoothMulLp_preimage_in_image_laplacianDomain
    (I := I) (M := M) g φ hu_h
  obtain ⟨w1, hw1_dom, hw1_eq⟩ := h1
  obtain ⟨w2, hw2_dom, hw2_eq⟩ := h_grad
  have h3 := smoothMulLp_DeltaPhi_in_image_laplacianDomain
    (I := I) (M := M) g φ hu_dom
  obtain ⟨w3, hw3_dom, hw3_eq⟩ := h3
  have h_in_image :
      laplacianDomain.preimage (I := I) (M := M) g
          ⟨smoothMulH1Compl (I := I) (M := M) g φ u_h,
            smoothMulH1Compl_mem_laplacianDomain (I := I) (M := M) g φ hu_dom⟩ ∈
        Set.image (H1ComplToLp (I := I) (M := M) g)
          (laplacianDomain (I := I) (M := M) g : Set (H1Compl g)) := by
    refine ⟨w1 - (2 : ℝ) • w2 - w3, ?_, ?_⟩
    · refine sub_mem (sub_mem hw1_dom ?_) hw3_dom
      exact (laplacianDomain (I := I) (M := M) g).smul_mem (2 : ℝ) hw2_dom
    · rw [map_sub, map_sub, map_smul]
      rw [hw1_eq, hw2_eq, hw3_eq]
      exact h_lp_identity.symm
  obtain ⟨w, hw_dom, hw_eq⟩ := h_in_image
  obtain ⟨f, hf⟩ := (laplacianDomain_mem_iff (I := I) (M := M) g).mp hw_dom
  rw [show (2 : ℕ) = 1 + 1 from rfl]
  rw [laplacianDomainPow_succ_mem_iff]
  refine ⟨f, ?_⟩
  rw [iteratedResolventL2_one]
  have h1 : (smoothMulH1Compl (I := I) (M := M) g φ u_h : H1Compl g) =
      resolvent (I := I) (M := M) g
        (laplacianDomain.preimage (I := I) (M := M) g
          ⟨smoothMulH1Compl (I := I) (M := M) g φ u_h,
            smoothMulH1Compl_mem_laplacianDomain (I := I) (M := M) g φ hu_dom⟩) := by
    rw [resolvent_laplacianDomain_preimage_eq]
  rw [h1]
  congr 1
  rw [← hw_eq]
  rw [hf]
  rfl

/-- **Forward implication (iterated closure → gradInnerCLM image)**.

For `u_h ∈ laplacianDomainPow g 2`, if `smoothMulH1Compl g φ u_h ∈
laplacianDomainPow g 2`, then `gradInnerCLM g φ u_h` lifts to an
`H1Compl` element in `laplacianDomain g`. -/
theorem gradInnerCLM_mem_image_of_smoothMulH1Compl_mem_pow_two
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (h_sM : smoothMulH1Compl (I := I) (M := M) g φ u_h ∈
      laplacianDomainPow (I := I) (M := M) g 2) :
    gradInnerCLM (I := I) (M := M) g φ u_h ∈
      Set.image (H1ComplToLp (I := I) (M := M) g)
        (laplacianDomain (I := I) (M := M) g : Set (H1Compl g)) := by
  classical
  have hu_dom := laplacianDomainPow_succ_subset_laplacianDomain
    (I := I) (M := M) g 1 hu_h
  have h_sM_dom := laplacianDomainPow_succ_subset_laplacianDomain
    (I := I) (M := M) g 1 h_sM
  have h_preimage_unique :
      laplacianDomain.preimage (I := I) (M := M) g
          ⟨smoothMulH1Compl (I := I) (M := M) g φ u_h,
            smoothMulH1Compl_mem_laplacianDomain (I := I) (M := M) g φ hu_dom⟩ =
        laplacianDomain.preimage (I := I) (M := M) g
          ⟨smoothMulH1Compl (I := I) (M := M) g φ u_h, h_sM_dom⟩ := by
    rfl
  have h_identity := gradInnerCLM_eq_two_inv_preimageDiff
    (I := I) (M := M) g φ hu_dom
  have h1 := smoothMulLp_preimage_in_image_laplacianDomain
    (I := I) (M := M) g φ hu_h
  obtain ⟨w1, hw1_dom, hw1_eq⟩ := h1
  have w2_eq := H1ComplToLp_preimageLift (I := I) (M := M) g h_sM
  have w2_dom := preimageLift_mem_laplacianDomain (I := I) (M := M) g h_sM
  have h3 := smoothMulLp_DeltaPhi_in_image_laplacianDomain
    (I := I) (M := M) g φ hu_dom
  obtain ⟨w3, hw3_dom, hw3_eq⟩ := h3
  refine ⟨(1/2 : ℝ) • (w1 - preimageLift (I := I) (M := M) g h_sM - w3), ?_, ?_⟩
  · refine (laplacianDomain (I := I) (M := M) g).smul_mem (1/2 : ℝ) ?_
    refine sub_mem (sub_mem hw1_dom w2_dom) hw3_dom
  · rw [map_smul, map_sub, map_sub]
    rw [hw1_eq, w2_eq, hw3_eq]
    rw [h_preimage_unique.symm]
    rw [← h_identity]
    rw [smul_smul]
    norm_num

/-- **Equivalence theorem**: for `u_h ∈ laplacianDomainPow g 2`,

```
smoothMulH1Compl g φ u_h ∈ laplacianDomainPow g 2
  ↔ gradInnerCLM g φ u_h ∈ H1ComplToLp '' laplacianDomain g.
```

This localizes the iterated-closure question to a single sharp statement:
whether the gradient-inner-product Lp class is in the image of
`H1ComplToLp` restricted to `laplacianDomain g`. Equivalently, whether
`g(∇φ, ∇u_h)` is H¹ chart-wise (the "H²-of-product" question for `φ · u_h`).

The forward direction is `gradInnerCLM_mem_image_of_smoothMulH1Compl_mem_pow_two`;
the reverse is `smoothMulH1Compl_mem_pow_two_of_gradInnerCLM_mem_image`. -/
theorem smoothMulH1Compl_mem_pow_two_iff_gradInnerCLM_mem_image
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    smoothMulH1Compl (I := I) (M := M) g φ u_h ∈
      laplacianDomainPow (I := I) (M := M) g 2 ↔
    gradInnerCLM (I := I) (M := M) g φ u_h ∈
      Set.image (H1ComplToLp (I := I) (M := M) g)
        (laplacianDomain (I := I) (M := M) g : Set (H1Compl g)) := by
  refine ⟨gradInnerCLM_mem_image_of_smoothMulH1Compl_mem_pow_two
    (I := I) (M := M) g φ hu_h, ?_⟩
  exact smoothMulH1Compl_mem_pow_two_of_gradInnerCLM_mem_image
    (I := I) (M := M) g φ hu_h

/-- The smooth scalar representing the pointwise gradient inner product
`x ↦ g.inner x (∇φ x) (∇v x)` for smooth `φ, v`. -/
noncomputable def gradInnerSmoothBundle
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    SmoothScalar g where
  toFun := fun x => g.inner x (gradFun (I := I) g (φ : C^∞⟮I, M; ℝ⟯) x)
    (gradFun (I := I) g v.toFun x)
  smooth := by
    have h := contMDiff_g_inner_of_smooth_sections (I := I) (M := M) g
      (grad_g (I := I) g φ.contMDiff) (grad_g (I := I) g v.smooth)
    refine h.congr ?_
    intro x
    change g.inner x ((grad_g (I := I) g φ.contMDiff :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
          ((grad_g (I := I) g v.smooth :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) =
        g.inner x (gradFun (I := I) g φ x) (gradFun (I := I) g v.toFun x)
    rw [grad_g_apply, grad_g_apply]

@[simp] lemma gradInnerSmoothBundle_apply
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    (v : SmoothScalar g) (x : M) :
    (gradInnerSmoothBundle (I := I) (M := M) g φ v).toFun x =
      g.inner x (gradFun (I := I) g φ x) (gradFun (I := I) g v.toFun x) := rfl

/-- For smooth `v`, `gradInnerSmooth g φ v` (the Lp class) equals
`smoothToLp g (gradInnerSmoothBundle g φ v)`. -/
theorem gradInnerSmooth_eq_smoothToLp_bundle
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    gradInnerSmooth (I := I) (M := M) g φ v =
      smoothToLp (I := I) (M := M) g
        (gradInnerSmoothBundle (I := I) (M := M) g φ v) := by
  apply MeasureTheory.Lp.ext
  refine (gradInnerSmooth_coeFn (I := I) (M := M) g φ v).trans ?_
  refine (MemLp.coeFn_toLp (gradInnerSmoothBundle (I := I) (M := M) g φ v).memLp_two).symm.trans ?_
  refine Filter.Eventually.of_forall ?_
  intro x; rfl

/-- **Smooth-case discharge**: for smooth `v`, the gradient inner product
`gradInnerCLM g φ (smoothToH1Compl v)` lies in `H1ComplToLp '' laplacianDomain g`.

The discharge is direct: the smooth scalar
`gradInnerSmoothBundle g φ v` has its `smoothToH1Compl` lift in
`laplacianDomain g`, and the `H1ComplToLp` of that lift equals
`gradInnerCLM g φ (smoothToH1Compl v) = gradInnerSmooth g φ v`. -/
theorem gradInnerCLM_smoothToH1Compl_mem_image_laplacianDomain
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    gradInnerCLM (I := I) (M := M) g φ
        (smoothToH1Compl (I := I) (M := M) g v) ∈
      Set.image (H1ComplToLp (I := I) (M := M) g)
        (laplacianDomain (I := I) (M := M) g : Set (H1Compl g)) := by
  classical
  refine ⟨smoothToH1Compl (I := I) (M := M) g
    (gradInnerSmoothBundle (I := I) (M := M) g φ v), ?_, ?_⟩
  · exact smoothToH1Compl_mem_laplacianDomain
      (I := I) (M := M) (gradInnerSmoothBundle (I := I) (M := M) g φ v)
  · rw [H1ComplToLp_smoothToH1Compl]
    rw [gradInnerCLM_smoothToH1Compl]
    rw [gradInnerSmooth_eq_smoothToLp_bundle]

/-- Specialised form: for smooth `v`, the bottleneck statement (`gradInnerCLM
g φ u_h ∈ H1ComplToLp '' laplacianDomain g`) holds. Hence by the equivalence
`smoothMulH1Compl_mem_pow_two_iff_gradInnerCLM_mem_image`, the iterated closure
`smoothMulH1Compl g φ (smoothToH1Compl v) ∈ laplacianDomainPow g 2` follows once
`smoothToH1Compl v ∈ laplacianDomainPow g 2`. The latter is automatic since
the variational Laplacian on smooth scalars agrees with the classical
Laplacian, which iterates within smooth scalars. -/
theorem smoothToH1Compl_mem_laplacianDomainPow_two
    (g : SmoothRiemannianMetric I M) (v : SmoothScalar g) :
    smoothToH1Compl (I := I) (M := M) g v ∈
      laplacianDomainPow (I := I) (M := M) g 2 := by
  classical
  rw [show (2 : ℕ) = 1 + 1 from rfl]
  rw [laplacianDomainPow_succ_mem_iff]
  refine ⟨smoothToLp (I := I) (M := M) g
    v.oneSubLapClassical.oneSubLapClassical, ?_⟩
  rw [iteratedResolventL2_one]
  rw [smoothToH1Compl_eq_resolvent_oneSubLap (I := I) (M := M) v]
  congr 1
  rw [show resolventL2 (I := I) (M := M) g
        (smoothToLp (I := I) (M := M) g v.oneSubLapClassical.oneSubLapClassical) =
      H1ComplToLp (I := I) (M := M) g
        (resolvent (I := I) (M := M) g
          (smoothToLp (I := I) (M := M) g v.oneSubLapClassical.oneSubLapClassical)) from rfl]
  rw [← smoothToH1Compl_eq_resolvent_oneSubLap (I := I) (M := M)
    v.oneSubLapClassical]
  rw [H1ComplToLp_smoothToH1Compl]

/-- **Smooth-case full discharge**: for smooth `v`,
`smoothMulH1Compl g φ (smoothToH1Compl v) ∈ laplacianDomainPow g 2`.

This is the smooth case of the iterated closure bottleneck. It follows from
`gradInnerCLM_smoothToH1Compl_mem_image_laplacianDomain` (the smooth-case
discharge of `gradInnerCLM`) combined with the equivalence theorem
`smoothMulH1Compl_mem_pow_two_iff_gradInnerCLM_mem_image`. -/
theorem smoothMulH1Compl_smoothToH1Compl_mem_laplacianDomainPow_two
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    smoothMulH1Compl (I := I) (M := M) g φ
        (smoothToH1Compl (I := I) (M := M) g v) ∈
      laplacianDomainPow (I := I) (M := M) g 2 := by
  rw [smoothMulH1Compl_mem_pow_two_iff_gradInnerCLM_mem_image
    (I := I) (M := M) g φ
    (smoothToH1Compl_mem_laplacianDomainPow_two (I := I) (M := M) g v)]
  exact gradInnerCLM_smoothToH1Compl_mem_image_laplacianDomain
    (I := I) (M := M) g φ v

end GradInnerLpIdentity
end Laplacian
end Analysis
end DifferentialGeometry

end
