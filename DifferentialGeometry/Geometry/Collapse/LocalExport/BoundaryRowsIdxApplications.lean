import DifferentialGeometry.Geometry.Collapse.BoundaryScale.BoundaryRowBindingsIdx
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryUniformWitnessesIdx

/-!
# Consumers: the index-shifted BSA04 / BSA05 / BSA06 / H / P3b statements on BBR03's sequence

Lane BDRY-IDX3. The accepted sequence forms `H_envelope_eventually`, `H_bsa05_eventually`,
`bsa04_row_counterexample`, `bsa06_row_eventually`, `eventually_strict_scale_boundary_BDRY4` and
`lpa02_witnesses_at_scale_boundary_BDRY3` quantify over sequences at `δ_n` for ALL `n`, an EMPTY
hypothesis (`isEmpty_boundarySequence_ratio_IDX`, lane BDRY-IDX). Their restatements (`…_IDX`,
modules `BoundaryScale.BoundaryRowBindingsIdx` and `LocalExport.BoundaryUniformWitnessesIdx`) take
sequences at `δ_{n+1}`. Non-vacuity, in the form in which BBR03's contradiction (B:10624–10644)
consumes the rows: each restated statement APPLIED to BBR03's counterexample sequence
(`exists_boundary_counterexample_sequence_of_no_threshold`, StaticCounterexamples.lean): same
prefix; for every certificate `Good` WITHOUT a nonempty-boundary threshold, the BBR03 sequence
(members at `δ_{n+1}`, none with `Good`) carries the full conclusion. No adapter between the shapes.

* `H_envelope_eventually_bbr03_IDX3`, `H_bsa05_eventually_bbr03_IDX3`,
  `bsa04_row_counterexample_bbr03_IDX3`, `bsa06_row_eventually_bbr03_IDX3`,
  `eventually_strict_scale_boundary_bbr03_IDX3`;
* `lpa02_witnesses_at_scale_boundary_bbr03_IDX3`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open scoped Manifold ContDiff ENNReal NNReal Topology

namespace DifferentialGeometry.Geometry.Collapse

universe u

/-- **H applied to BBR03's sequence (non-vacuity of `H_envelope_eventually_IDX`).** With `δStar` of
`H_envelope_eventually_IDX`, for `0 < δ₀ ≤ δStar`, `K ≥ 2` and every certificate `Good` without a
nonempty-boundary threshold, the BBR03 counterexample sequence (members at `δ_{n+1}`, none with
`Good`) satisfies the envelope `r_p(w) - (Λ/2) d(p, q) ≤ r_q(w')` at all pairs on one tail. -/
theorem H_envelope_eventually_bbr03_IDX3 :
    ∃ δStar > 0, ∀ {δ₀ : ℝ}, 0 < δ₀ → δ₀ ≤ δStar → ∀ (K : ℕ), 2 ≤ K → ∀ (A : ℝ → ℝ)
      (Good : ∀ (W : CompactCarrier.{u}) (g : SmoothRiemannianMetric W.model W.Carrier) (w : ℝ),
        NearlyCuspidalBoundary W g K w → Prop),
      (¬ ∃ w₀ : ℝ, 0 < w₀ ∧ w₀ < euclideanThreeUnitBallVolume ∧
        ∀ (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
          (g : SmoothRiemannianMetric W.model W.Carrier) (B : NearlyCuspidalBoundary W g K w₀),
          boundaryVolumeCollapsed W g w₀ → curvatureDerivativesControlled g K A w₀ →
            Good W g w₀ B) →
      ∃ (W : ℕ → CompactCarrier.{u}) (_ : ∀ n, ConnectedSpace (W n).Carrier)
        (g : ∀ n, SmoothRiemannianMetric (W n).model (W n).Carrier)
        (B : ∀ n, NearlyCuspidalBoundary (W n) (g n) K (boundaryCounterexampleRatio δ₀ (n + 1))),
        (∀ n, ¬ Good (W n) (g n) (boundaryCounterexampleRatio δ₀ (n + 1)) (B n)) ∧
        ∀ {Λ w : ℝ}, 0 < Λ → 0 < w → w < euclideanThreeUnitBallVolume / 4 →
          ∀ᶠ n : ℕ in atTop, ∀ p q : (W n).Carrier,
            firstVolumeScale (g n) p w - Λ / 2 * (riemannianEDistOf (g n) p q).toReal ≤
              firstVolumeScale (g n) q (w / (2 * (1 + 2 / Λ) ^ 3)) := by
  obtain ⟨δS, hδS, hP⟩ := H_envelope_eventually_IDX.{u}
  refine ⟨δS, hδS, ?_⟩
  intro δ₀ hδ₀ hδ₀S K hK A Good hno
  obtain ⟨W, hW, g, B, hseq⟩ :=
    exists_boundary_counterexample_sequence_of_no_threshold K A hδ₀ Good hno
  exact ⟨W, hW, g, B, fun n => (hseq n).2.2, hP hδ₀ hδ₀S K hK W g B (fun n => (hseq n).1)⟩

/-- **BSA05 applied to BBR03's sequence (non-vacuity of `H_bsa05_eventually_IDX`).** For
`0 < δ₀ ≤ δStar`, `K ≥ 2` and every certificate `Good` without a nonempty-boundary threshold, the
BBR03 counterexample sequence (members at `δ_{n+1}`, none with `Good`) carries one smooth scale
`ρ_n` per member with BSA05.a on one tail and the collar smallness on every `ε`-tail. -/
theorem H_bsa05_eventually_bbr03_IDX3 :
    ∃ δStar > 0, ∀ {δ₀ : ℝ}, 0 < δ₀ → δ₀ ≤ δStar → ∀ (K : ℕ), 2 ≤ K → ∀ (A : ℝ → ℝ)
      (Good : ∀ (W : CompactCarrier.{u}) (g : SmoothRiemannianMetric W.model W.Carrier) (w : ℝ),
        NearlyCuspidalBoundary W g K w → Prop),
      (¬ ∃ w₀ : ℝ, 0 < w₀ ∧ w₀ < euclideanThreeUnitBallVolume ∧
        ∀ (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
          (g : SmoothRiemannianMetric W.model W.Carrier) (B : NearlyCuspidalBoundary W g K w₀),
          boundaryVolumeCollapsed W g w₀ → curvatureDerivativesControlled g K A w₀ →
            Good W g w₀ B) →
      ∃ (W : ℕ → CompactCarrier.{u}) (_ : ∀ n, ConnectedSpace (W n).Carrier)
        (g : ∀ n, SmoothRiemannianMetric (W n).model (W n).Carrier)
        (B : ∀ n, NearlyCuspidalBoundary (W n) (g n) K (boundaryCounterexampleRatio δ₀ (n + 1))),
        (∀ n, ¬ Good (W n) (g n) (boundaryCounterexampleRatio δ₀ (n + 1)) (B n)) ∧
        ∀ {Λ w : ℝ}, 0 < Λ → 0 < w → w < euclideanThreeUnitBallVolume / 4 →
          ∃ ρ : ∀ n, (W n).Carrier → ℝ,
            (∀ᶠ n in atTop, ContMDiff (W n).model 𝓘(ℝ, ℝ) ∞ (ρ n) ∧ (∀ p, 0 < ρ n p) ∧
              (∀ p, firstVolumeScale (g n) p w / 2 ≤ ρ n p ∧
                ρ n p ≤ 2 * firstVolumeScale (g n) p (w / (2 * (1 + 2 / Λ) ^ 3))) ∧
              ∀ x y, ENNReal.ofReal |ρ n x - ρ n y| ≤
                ENNReal.ofReal Λ * riemannianEDistOf (g n) x y) ∧
            ∀ ε > 0, ∀ᶠ n in atTop, ∀ (i : Fin (B n).count) (p : CuspHalfSpace),
              p.2.val 0 ≤ 96 → ρ n (((B n).collar i).toFun p) < ε := by
  obtain ⟨δS, hδS, hP⟩ := H_bsa05_eventually_IDX.{u}
  refine ⟨δS, hδS, ?_⟩
  intro δ₀ hδ₀ hδ₀S K hK A Good hno
  obtain ⟨W, hW, g, B, hseq⟩ :=
    exists_boundary_counterexample_sequence_of_no_threshold K A hδ₀ Good hno
  exact ⟨W, hW, g, B, fun n => (hseq n).2.2, hP hδ₀ hδ₀S K hK W g B (fun n => (hseq n).1)⟩

/-- **BSA04 applied to BBR03's sequence (non-vacuity of `bsa04_row_counterexample_IDX`).** For
`0 < δ₀ ≤ δStar`, `K ≥ 2` and every certificate `Good` without a nonempty-boundary threshold, the
BBR03 counterexample sequence (members at `δ_{n+1}`, none with `Good`) satisfies (BSA04.a) and
(BSA04.c) at every point of every member `n ≥ 3`, with `α = n`. -/
theorem bsa04_row_counterexample_bbr03_IDX3 :
    ∃ δStar > 0, ∀ {δ₀ : ℝ}, 0 < δ₀ → δ₀ ≤ δStar → ∀ (K : ℕ), 2 ≤ K → ∀ (A : ℝ → ℝ)
      (Good : ∀ (W : CompactCarrier.{u}) (g : SmoothRiemannianMetric W.model W.Carrier) (w : ℝ),
        NearlyCuspidalBoundary W g K w → Prop),
      (¬ ∃ w₀ : ℝ, 0 < w₀ ∧ w₀ < euclideanThreeUnitBallVolume ∧
        ∀ (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
          (g : SmoothRiemannianMetric W.model W.Carrier) (B : NearlyCuspidalBoundary W g K w₀),
          boundaryVolumeCollapsed W g w₀ → curvatureDerivativesControlled g K A w₀ →
            Good W g w₀ B) →
      ∃ (W : ℕ → CompactCarrier.{u}) (_ : ∀ n, ConnectedSpace (W n).Carrier)
        (g : ∀ n, SmoothRiemannianMetric (W n).model (W n).Carrier)
        (B : ∀ n, NearlyCuspidalBoundary (W n) (g n) K (boundaryCounterexampleRatio δ₀ (n + 1))),
        (∀ n, ¬ Good (W n) (g n) (boundaryCounterexampleRatio δ₀ (n + 1)) (B n)) ∧
        ∀ n : ℕ, 3 ≤ n → ∀ p : (W n).Carrier,
          ENNReal.ofReal (2 * n * firstVolumeScale (g n) p (n : ℝ)⁻¹) < curvatureRadius (g n) p ∧
          ∀ {C w : ℝ}, C < n → (n : ℝ)⁻¹ ≤ w → w < euclideanThreeUnitBallVolume →
            ∀ k ≤ K, ∀ q ∈ riemannianBallOf (g n) p (C * firstVolumeScale (g n) p w),
              curvatureDerivativeNorm (g n) k q ≤
                boundaryDerivativeConstant A K C w * (firstVolumeScale (g n) p w ^ (k + 2))⁻¹ := by
  obtain ⟨δS, hδS, hP⟩ := bsa04_row_counterexample_IDX.{u}
  refine ⟨δS, hδS, ?_⟩
  intro δ₀ hδ₀ hδ₀S K hK A Good hno
  obtain ⟨W, hW, g, B, hseq⟩ :=
    exists_boundary_counterexample_sequence_of_no_threshold K A hδ₀ Good hno
  exact ⟨W, hW, g, B, fun n => (hseq n).2.2,
    hP hδ₀ hδ₀S K hK A W g B (fun n => (hseq n).1) (fun n => (hseq n).2.1)⟩

/-- **BSA06 applied to BBR03's sequence (non-vacuity of `bsa06_row_eventually_IDX`).** For
`0 < δ₀ ≤ δStar`, `K ≥ 2`, `A > 0` and every certificate `Good` without a nonempty-boundary
threshold, the BBR03 counterexample sequence (members at `δ_{n+1}`, none with `Good`) has scales
`ρ_n` with, on one tail, BSA05.a and all BSA06 / BCP04.a clauses at every point (`α = n`), and the
collar smallness on every `ε`-tail. -/
theorem bsa06_row_eventually_bbr03_IDX3 :
    ∃ δStar > 0, ∀ {δ₀ : ℝ}, 0 < δ₀ → δ₀ ≤ δStar → ∀ (K : ℕ), 2 ≤ K → ∀ (A : ℝ → ℝ),
      (∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w) →
      ∀ (Good : ∀ (W : CompactCarrier.{u}) (g : SmoothRiemannianMetric W.model W.Carrier) (w : ℝ),
        NearlyCuspidalBoundary W g K w → Prop),
      (¬ ∃ w₀ : ℝ, 0 < w₀ ∧ w₀ < euclideanThreeUnitBallVolume ∧
        ∀ (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
          (g : SmoothRiemannianMetric W.model W.Carrier) (B : NearlyCuspidalBoundary W g K w₀),
          boundaryVolumeCollapsed W g w₀ → curvatureDerivativesControlled g K A w₀ →
            Good W g w₀ B) →
      ∃ (W : ℕ → CompactCarrier.{u}) (_ : ∀ n, ConnectedSpace (W n).Carrier)
        (g : ∀ n, SmoothRiemannianMetric (W n).model (W n).Carrier)
        (B : ∀ n, NearlyCuspidalBoundary (W n) (g n) K (boundaryCounterexampleRatio δ₀ (n + 1))),
        (∀ n, ¬ Good (W n) (g n) (boundaryCounterexampleRatio δ₀ (n + 1)) (B n)) ∧
        ∀ {Λ w : ℝ}, 0 < Λ → 0 < w → w < euclideanThreeUnitBallVolume / 4 →
          ∃ ρ : ∀ n, (W n).Carrier → ℝ,
            (∀ᶠ n : ℕ in atTop, ∃ hρ : ∀ p, 0 < ρ n p,
              ContMDiff (W n).model 𝓘(ℝ, ℝ) ∞ (ρ n) ∧
              (∀ p, firstVolumeScale (g n) p w / 2 ≤ ρ n p ∧
                ρ n p ≤ 2 * firstVolumeScale (g n) p (w / (2 * (1 + 2 / Λ) ^ 3))) ∧
              (∀ x y, ENNReal.ofReal |ρ n x - ρ n y| ≤
                ENNReal.ofReal Λ * riemannianEDistOf (g n) x y) ∧
              ∀ p : (W n).Carrier,
                w / (2 * (1 + 2 / Λ) ^ 3) / (24 * ∫ t in (0 : ℝ)..1, Real.sinh t ^ 2) ≤
                    (ballVolume (g n) p (ρ n p)).toReal / ρ n p ^ 3 ∧
                (∀ y ∈ riemannianBallOf (normalizedCenterMetric (g n) (ρ n p) (hρ p)) p
                    ((n : ℝ) / 4),
                  SectionalBoundedBelowAt (normalizedCenterMetric (g n) (ρ n p) (hρ p)) y
                    (-(((n : ℝ) / 4) ^ 2)⁻¹)) ∧
                (∀ R : ℝ, 0 < R → 2 * R + 2 < n → ∀ k ≤ K,
                  ∀ y ∈ riemannianBallOf (normalizedCenterMetric (g n) (ρ n p) (hρ p)) p R,
                    curvatureDerivativeNorm (normalizedCenterMetric (g n) (ρ n p) (hρ p)) k y ≤
                      (2 : ℝ) ^ (K + 2) * boundaryDerivativeConstant A K (2 * R + 2)
                        (w / (2 * (1 + 2 / Λ) ^ 3))) ∧
                (0 < distanceToBoundary (W n) (g n) p →
                  n * (distanceToBoundary (W n) (g n) p).toReal /
                      ((distanceToBoundary (W n) (g n) p).toReal + 3) <
                    (distanceToBoundary (W n) (g n) p).toReal / ρ n p) ∧
                (ENNReal.ofReal 10 < distanceToBoundary (W n) (g n) p →
                  (n : ℝ) / 2 < (distanceToBoundary (W n) (g n) p).toReal / ρ n p ∧
                  ∀ b : ℝ, b ≤ (n : ℝ) / 2 →
                    riemannianBallOf (g n) p (b * ρ n p) ⊆
                      (W n).model.interior (W n).Carrier)) ∧
            ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ (i : Fin (B n).count) (p : CuspHalfSpace),
              p.2.val 0 ≤ 96 → ρ n (((B n).collar i).toFun p) < ε := by
  obtain ⟨δS, hδS, hP⟩ := bsa06_row_eventually_IDX.{u}
  refine ⟨δS, hδS, ?_⟩
  intro δ₀ hδ₀ hδ₀S K hK A hA Good hno
  obtain ⟨W, hW, g, B, hseq⟩ :=
    exists_boundary_counterexample_sequence_of_no_threshold K A hδ₀ Good hno
  exact ⟨W, hW, g, B, fun n => (hseq n).2.2,
    hP hδ₀ hδ₀S K hK A hA W g B (fun n => (hseq n).1) (fun n => (hseq n).2.1)⟩

/-- **T2 clause (i) applied to BBR03's sequence (non-vacuity of
`eventually_strict_scale_boundary_BDRY4_IDX`).** For `0 < δ₀ ≤ δStar`, `K ≥ 2` and every
certificate `Good` without a nonempty-boundary threshold, the BBR03 counterexample sequence (members
at `δ_{n+1}`, none with `Good`) carries one scale `ρ_n` with T2's clause (i) on one tail (strict
LC02 bounds written with `2 * Λ⁻¹`) and `ρ_n ≤ ε` on the collars on every `ε`-tail. -/
theorem eventually_strict_scale_boundary_bbr03_IDX3 :
    ∃ δStar > 0, ∀ {δ₀ : ℝ}, 0 < δ₀ → δ₀ ≤ δStar → ∀ (K : ℕ), 2 ≤ K → ∀ (A : ℝ → ℝ)
      (Good : ∀ (W : CompactCarrier.{u}) (g : SmoothRiemannianMetric W.model W.Carrier) (w : ℝ),
        NearlyCuspidalBoundary W g K w → Prop),
      (¬ ∃ w₀ : ℝ, 0 < w₀ ∧ w₀ < euclideanThreeUnitBallVolume ∧
        ∀ (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
          (g : SmoothRiemannianMetric W.model W.Carrier) (B : NearlyCuspidalBoundary W g K w₀),
          boundaryVolumeCollapsed W g w₀ → curvatureDerivativesControlled g K A w₀ →
            Good W g w₀ B) →
      ∃ (W : ℕ → CompactCarrier.{u}) (_ : ∀ n, ConnectedSpace (W n).Carrier)
        (g : ∀ n, SmoothRiemannianMetric (W n).model (W n).Carrier)
        (B : ∀ n, NearlyCuspidalBoundary (W n) (g n) K (boundaryCounterexampleRatio δ₀ (n + 1))),
        (∀ n, ¬ Good (W n) (g n) (boundaryCounterexampleRatio δ₀ (n + 1)) (B n)) ∧
        ∀ {Λ w : ℝ}, 0 < Λ → 0 < w → w < euclideanThreeUnitBallVolume / 4 →
          ∃ ρ : ∀ n, (W n).Carrier → ℝ,
            (∀ᶠ n in atTop, (∀ p, 0 < ρ n p) ∧
              ContMDiff (W n).model 𝓘(ℝ, ℝ) ∞ (ρ n) ∧
              (∀ x y, ENNReal.ofReal |ρ n x - ρ n y| ≤
                ENNReal.ofReal Λ * riemannianEDistOf (g n) x y) ∧
              ∀ p, firstVolumeScale (g n) p w / 2 < ρ n p ∧
                ρ n p < 2 * firstVolumeScale (g n) p (w / (2 * (1 + 2 * Λ⁻¹) ^ 3))) ∧
            ∀ ε > 0, ∀ᶠ n in atTop, ∀ (i : Fin (B n).count) (q : CuspHalfSpace),
              q.2.val 0 ≤ 96 → ρ n (((B n).collar i).toFun q) ≤ ε := by
  obtain ⟨δS, hδS, hP⟩ := eventually_strict_scale_boundary_BDRY4_IDX.{u}
  refine ⟨δS, hδS, ?_⟩
  intro δ₀ hδ₀ hδ₀S K hK A Good hno
  obtain ⟨W, hW, g, B, hseq⟩ :=
    exists_boundary_counterexample_sequence_of_no_threshold K A hδ₀ Good hno
  exact ⟨W, hW, g, B, fun n => (hseq n).2.2, hP hδ₀ hδ₀S K hK W g B (fun n => (hseq n).1)⟩

section Completion

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Calculus
open DifferentialGeometry.Geometry.Comparison.Toponogov
open GC.MetricGeometry

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

/-- **P3b's scale-function consumer applied to BBR03's sequence (non-vacuity of
`lpa02_witnesses_at_scale_boundary_BDRY3_IDX`).** The prefix of the restated statement; then for
`0 < δ₀ ≤ δStar` and every certificate `Good` without a nonempty-boundary threshold, the BBR03
counterexample sequence (members at `δ_{n+1}`, none with `Good`) has, for every choice of complete
completions `ĝ_n` agreeing with `g_n` on `{D ≥ 4}`, the witnesses at every scale function below
`2 r_p(w')` on one tail. -/
theorem lpa02_witnesses_at_scale_boundary_bbr03_IDX3 :
    ∃ δStar > 0, ∀ (K : ℕ), 10 ≤ K → ∀ (A : ℝ → ℝ),
      (∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w) →
      ∀ {Λ w : ℝ}, 0 < Λ → 0 < w → w < 4 * Real.pi / 3 →
      ∀ {δ' T : ℝ}, 0 < δ' →
      ∀ {δ₀ : ℝ}, 0 < δ₀ → δ₀ ≤ δStar →
      ∀ (Good : ∀ (W : CompactCarrier.{0}) (g : SmoothRiemannianMetric W.model W.Carrier) (w : ℝ),
        NearlyCuspidalBoundary W g K w → Prop),
      (¬ ∃ w₀ : ℝ, 0 < w₀ ∧ w₀ < euclideanThreeUnitBallVolume ∧
        ∀ (W : CompactCarrier.{0}) [ConnectedSpace W.Carrier]
          (g : SmoothRiemannianMetric W.model W.Carrier) (B : NearlyCuspidalBoundary W g K w₀),
          boundaryVolumeCollapsed W g w₀ → curvatureDerivativesControlled g K A w₀ →
            Good W g w₀ B) →
      ∃ (W : ℕ → CompactCarrier.{0}) (_ : ∀ n, ConnectedSpace (W n).Carrier)
        (g : ∀ n, SmoothRiemannianMetric (W n).model (W n).Carrier)
        (B : ∀ n, NearlyCuspidalBoundary (W n) (g n) K (boundaryCounterexampleRatio δ₀ (n + 1))),
        (∀ n, ¬ Good (W n) (g n) (boundaryCounterexampleRatio δ₀ (n + 1)) (B n)) ∧
      ∀ (ĝ : ∀ n, SmoothRiemannianMetric (𝓡 3) ((W n).pieceInterior ⊤)),
        (∀ n, RiemannianMetricComplete (I := 𝓡 3) (ĝ n)) →
        (∀ n (x : (W n).pieceInterior ⊤), ENNReal.ofReal 4 ≤ distanceToBoundary (W n) (g n) x →
          (ĝ n).inner x = (pieceInteriorMetric (W n) (g n) ⊤).inner x) →
      ∃ V : ℝ, T ≤ V ∧ ∃ δ : ℝ, 0 < δ ∧ δ < δ' ∧ ∀ᶠ n in atTop,
        letI := inducedMetricSpace (ĝ n)
        ∀ (ρ : (W n).Carrier → ℝ) (hρ : ∀ p, 0 < ρ p),
        (∀ p, ρ p < 2 * firstVolumeScale (g n) p (w / (2 * (1 + 2 * Λ⁻¹) ^ 3))) →
        ∀ (p : (W n).pieceInterior ⊤), ENNReal.ofReal 5 < distanceToBoundary (W n) (g n) p →
        ∃ s ∈ Icc T V, ∃ hs : 0 < s,
          (∀ y ∈ Metric.ball p (400 * (s * ρ p)),
            SectionalBoundedBelowAt (ĝ n) y (-((1 / 60) ^ 2 * (s * ρ p)⁻¹ ^ 2))) ∧
          ∃ (C : Type) (mC : MetricSpace C) (o : C), Nonempty (RadialConeData o) ∧
            Nonempty (@KleinerLottApprox ((W n).pieceInterior ⊤) C
              ((inducedMetricSpace (ĝ n)).rescale (s * ρ p)⁻¹ (inv_pos.mpr (mul_pos hs (hρ p))))
              mC p o δ) := by
  obtain ⟨δS, hδS, hP⟩ := lpa02_witnesses_at_scale_boundary_BDRY3_IDX
  refine ⟨δS, hδS, ?_⟩
  intro K hK A hA Λ w hΛ hw hwc δ' T hδ' δ₀ hδ₀ hδ₀S Good hno
  obtain ⟨W, hW, g, B, hseq⟩ :=
    exists_boundary_counterexample_sequence_of_no_threshold K A hδ₀ Good hno
  exact ⟨W, hW, g, B, fun n => (hseq n).2.2, fun ĝ hcomp heq =>
    hP K hK A hA hΛ hw hwc hδ' hδ₀ hδ₀S W g B (fun n => (hseq n).1) (fun n => (hseq n).2.1) ĝ
      hcomp heq⟩

end Completion

end DifferentialGeometry.Geometry.Collapse
