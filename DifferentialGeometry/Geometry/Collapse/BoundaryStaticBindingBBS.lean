import DifferentialGeometry.Geometry.Collapse.BoundarySequenceAssignmentBSTD1
import DifferentialGeometry.Geometry.Collapse.BoundaryScale.BoundaryRowBindingsIdx
import DifferentialGeometry.Geometry.Collapse.StaticCounterexamples
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Presentation

/-!
# BBR02 binding and BBR03 reduction on the per-sequence boundary assignment (lane B-BBR-BSA)

Blueprint 207B, BBR02 (B:10567–10590) and BBR03 (B:10592–10654); task 61, D61-11 and draft §7.5
("BBR02 only binds; BBR03 takes ONE tail member of the IDX2 sequence; no new E").

* `BoundaryStandingSequence_BSTD1.mono_BBS`: a standing sequence below `δ₁` is one below every
  `δ₂ ≥ δ₁` (the restriction of prospective thresholds below `δ*`, B:10620).
* `bbr02_standing_tail_BBS` (BBR02, binding part): for the fixed `K, A` there is `0 < δ₁ ≤ δStar`
  (the exported boundary threshold, lowered to BSA04's) such that for EVERY early choice `E` and
  EVERY standing sequence below `δ₁` (BSA04's boundary counterexample construction at the ratios
  `δ_{n+1}`) there are ONE zero scale `V`, ONE register `R` over `(E, V)` and ONE tail `n₀` on
  which every member carries the member output of the assignment (T3B-BFRZ's per-member conclusion
  on its SAME carrier, its original labelled boundary `P.cusp = B`, all points and components; the
  product-or-separated alternative of BCP03; the premise at `r_∂`) together with BSA04's standing
  data (BSA04.a `R_p > 2n r_p(1/n)` at EVERY point and the whole-ball derivative bounds with the ONE
  function `A'`, at `α = n`).
* `bbr03_reduction_BBS` (BBR03, reduction): for every certificate `Good` of a member, EITHER a
  positive threshold `w₀ < ω₃` for `Good` exists (BBR03's conclusion form), OR there is a standing
  sequence below `δ₁` (at `δ₀ = δ₁`) all of whose members fail `Good` and whose members from one
  tail on carry, for every early choice, the output of `bbr02_standing_tail_BBS`. No hypothesis.
* `bbr03_reduction_graph_BBS`: the same with `Good` = BBR03's labelled finite graph presentation
  (A2's conclusion: a raw graph presentation whose external tori are the boundary components).
* `bbr03_one_tail_member_BBS`: in the second case every early choice has ONE member that is a
  nongraph counterexample AND carries the full output (draft §7.5).

The step still missing for BBR02/BBR03 as rows: member output ⇒ labelled graph presentation (the
augmented chain BCG03–BCF04 grows `BoundaryMemberOutput`, draft §7.5, and the FC42 consumer).
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian GC.GraphManifold
open scoped Manifold ContDiff ENNReal NNReal Topology

namespace DifferentialGeometry.Geometry.Collapse

attribute [local instance] BoundaryStandingSequence_BSTD1.conn

/-- A standing sequence below `δ₁` is a standing sequence below every `δ₂ ≥ δ₁` (same members). -/
def BoundaryStandingSequence_BSTD1.mono_BBS {K : ℕ} {A : ℝ → ℝ} {δ₁ δ₂ : ℝ}
    (S : BoundaryStandingSequence_BSTD1 K A δ₁) (h : δ₁ ≤ δ₂) :
    BoundaryStandingSequence_BSTD1 K A δ₂ :=
  { S with δ₀_le := S.δ₀_le.trans h }

/-- **BBR02, binding part** (B:10567–10590; D61-11, draft §7.5): there is `0 < δ₁ ≤ δStar` such
that for every early choice `E` and every standing sequence `S` below `δ₁` (BSA04's boundary
counterexample construction at `δ_{n+1}`) ONE zero scale `V`, ONE register `R` over `(E, V)` and ONE
tail `n₀` work for all members: every member `n ≥ n₀` carries the assignment's member output (all
points and components, its own labelled boundary) and BSA04's standing data at `α = n`. -/
theorem bbr02_standing_tail_BBS (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ)
    (hA : ∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w) :
    ∃ δ₁ : ℝ, 0 < δ₁ ∧ ∃ hδ₁ : δ₁ ≤ (bdryThresholds_BSTD1 K hK A hA).δStar,
      ∀ (E : BoundaryEarlyChoices_BSTD1 K hK A hA) (S : BoundaryStandingSequence_BSTD1 K A δ₁),
      ∃ V : ℝ, ∃ R : BoundaryRegisterOver_BSTD1 E V, ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
        Nonempty (BoundaryMemberOutput_BSTD1 (S.mono_BBS hδ₁) n R) ∧
        ∀ p : (S.W n).Carrier,
          ENNReal.ofReal (2 * n * firstVolumeScale (S.g n) p (n : ℝ)⁻¹) <
              curvatureRadius (S.g n) p ∧
          ∀ {C w : ℝ}, C < n → (n : ℝ)⁻¹ ≤ w → w < euclideanThreeUnitBallVolume →
            ∀ k ≤ K, ∀ q ∈ riemannianBallOf (S.g n) p (C * firstVolumeScale (S.g n) p w),
              curvatureDerivativeNorm (S.g n) k q ≤
                boundaryDerivativeConstant A K C w *
                  (firstVolumeScale (S.g n) p w ^ (k + 2))⁻¹ := by
  obtain ⟨δS, hδS, h4⟩ := bsa04_row_counterexample_IDX.{0}
  have hΘ := (bdryThresholds_BSTD1 K hK A hA).δStar_pos
  refine ⟨min (bdryThresholds_BSTD1 K hK A hA).δStar δS, lt_min hΘ hδS, min_le_left _ _,
    fun E S => ?_⟩
  obtain ⟨V, R, n₀, hR⟩ := exists_boundarySequenceAssignment_BSTD1 E (S.mono_BBS (min_le_left _ _))
  have hstd := h4 S.δ₀_pos (S.δ₀_le.trans (min_le_right _ _)) K (by omega) A S.W S.g S.B S.coll
    S.der
  refine ⟨V, R, max n₀ 3, fun n hn => ⟨hR n (le_of_max_le_left hn), fun p => ?_⟩⟩
  exact hstd n (le_of_max_le_right hn) p

/-- **BBR03, reduction** (B:10592–10654; draft §7.5): for every certificate `Good`, EITHER a
positive threshold `w₀ < ω₃` for `Good` exists, OR there is a standing sequence below `δ₁` (at
`δ₀ = δ₁`) all of whose members fail `Good` and whose members from one tail on carry, for every
early choice, the output of `bbr02_standing_tail_BBS` (the assignment's member output and BSA04's
standing data). No hypothesis: the second case is what BBR02's graph clause refutes. -/
theorem bbr03_reduction_BBS (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ)
    (hA : ∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w)
    (Good : ∀ (W : CompactCarrier.{0}) (g : SmoothRiemannianMetric W.model W.Carrier) (w : ℝ),
      NearlyCuspidalBoundary W g K w → Prop) :
    (∃ w₀ : ℝ, 0 < w₀ ∧ w₀ < euclideanThreeUnitBallVolume ∧
      ∀ (W : CompactCarrier.{0}) [ConnectedSpace W.Carrier]
        (g : SmoothRiemannianMetric W.model W.Carrier) (B : NearlyCuspidalBoundary W g K w₀),
        boundaryVolumeCollapsed W g w₀ → curvatureDerivativesControlled g K A w₀ →
          Good W g w₀ B) ∨
    ∃ δ₁ : ℝ, 0 < δ₁ ∧ ∃ hδ₁ : δ₁ ≤ (bdryThresholds_BSTD1 K hK A hA).δStar,
      ∃ S : BoundaryStandingSequence_BSTD1 K A δ₁, S.δ₀ = δ₁ ∧
        (∀ n, ¬ Good (S.W n) (S.g n) (boundaryCounterexampleRatio S.δ₀ (n + 1)) (S.B n)) ∧
        ∀ E : BoundaryEarlyChoices_BSTD1 K hK A hA,
        ∃ V : ℝ, ∃ R : BoundaryRegisterOver_BSTD1 E V, ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
          Nonempty (BoundaryMemberOutput_BSTD1 (S.mono_BBS hδ₁) n R) ∧
          ∀ p : (S.W n).Carrier,
            ENNReal.ofReal (2 * n * firstVolumeScale (S.g n) p (n : ℝ)⁻¹) <
                curvatureRadius (S.g n) p ∧
            ∀ {C w : ℝ}, C < n → (n : ℝ)⁻¹ ≤ w → w < euclideanThreeUnitBallVolume →
              ∀ k ≤ K, ∀ q ∈ riemannianBallOf (S.g n) p (C * firstVolumeScale (S.g n) p w),
                curvatureDerivativeNorm (S.g n) k q ≤
                  boundaryDerivativeConstant A K C w *
                    (firstVolumeScale (S.g n) p w ^ (k + 2))⁻¹ := by
  by_cases hthr : ∃ w₀ : ℝ, 0 < w₀ ∧ w₀ < euclideanThreeUnitBallVolume ∧
      ∀ (W : CompactCarrier.{0}) [ConnectedSpace W.Carrier]
        (g : SmoothRiemannianMetric W.model W.Carrier) (B : NearlyCuspidalBoundary W g K w₀),
        boundaryVolumeCollapsed W g w₀ → curvatureDerivativesControlled g K A w₀ →
          Good W g w₀ B
  · exact Or.inl hthr
  · right
    obtain ⟨δ₁, hδ₁, hδ₁Θ, hbind⟩ := bbr02_standing_tail_BBS K hK A hA
    obtain ⟨W, hW, g, B, hseq⟩ :=
      exists_boundary_counterexample_sequence_of_no_threshold.{0} K A hδ₁ Good hthr
    let S : BoundaryStandingSequence_BSTD1 K A δ₁ :=
      ⟨δ₁, hδ₁, le_rfl, W, hW, g, B, fun n => (hseq n).1, fun n => (hseq n).2.1⟩
    exact ⟨δ₁, hδ₁, hδ₁Θ, S, rfl, fun n => (hseq n).2.2, fun E => hbind E S⟩

/-- **BBR03, reduction at the labelled graph presentation** (A2's conclusion): EITHER the BBR03
threshold exists (every member at `w₀` has a raw graph presentation whose external tori are its
boundary components, with their labels), OR a standing sequence of NONGRAPH counterexamples below
`δ₁` whose late members carry, for every early choice, the full output of BBR02's binding. -/
theorem bbr03_reduction_graph_BBS (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ)
    (hA : ∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w) :
    (∃ w₀ : ℝ, 0 < w₀ ∧ w₀ < euclideanThreeUnitBallVolume ∧
      ∀ (W : CompactCarrier.{0}) [ConnectedSpace W.Carrier]
        (g : SmoothRiemannianMetric W.model W.Carrier) (B : NearlyCuspidalBoundary W g K w₀),
        boundaryVolumeCollapsed W g w₀ → curvatureDerivativesControlled g K A w₀ →
          ∃ G : RawGraphPresentation W, ∃ e : Fin B.count ≃ Fin G.externalCount,
            ∀ i, Set.range (G.external.torusMap (e i)) = B.component i) ∨
    ∃ δ₁ : ℝ, 0 < δ₁ ∧ ∃ hδ₁ : δ₁ ≤ (bdryThresholds_BSTD1 K hK A hA).δStar,
      ∃ S : BoundaryStandingSequence_BSTD1 K A δ₁, S.δ₀ = δ₁ ∧
        (∀ n, ¬ ∃ G : RawGraphPresentation (S.W n), ∃ e : Fin (S.B n).count ≃ Fin G.externalCount,
          ∀ i, Set.range (G.external.torusMap (e i)) = (S.B n).component i) ∧
        ∀ E : BoundaryEarlyChoices_BSTD1 K hK A hA,
        ∃ V : ℝ, ∃ R : BoundaryRegisterOver_BSTD1 E V, ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
          Nonempty (BoundaryMemberOutput_BSTD1 (S.mono_BBS hδ₁) n R) ∧
          ∀ p : (S.W n).Carrier,
            ENNReal.ofReal (2 * n * firstVolumeScale (S.g n) p (n : ℝ)⁻¹) <
                curvatureRadius (S.g n) p ∧
            ∀ {C w : ℝ}, C < n → (n : ℝ)⁻¹ ≤ w → w < euclideanThreeUnitBallVolume →
              ∀ k ≤ K, ∀ q ∈ riemannianBallOf (S.g n) p (C * firstVolumeScale (S.g n) p w),
                curvatureDerivativeNorm (S.g n) k q ≤
                  boundaryDerivativeConstant A K C w *
                    (firstVolumeScale (S.g n) p w ^ (k + 2))⁻¹ :=
  bbr03_reduction_BBS K hK A hA fun W _ _ B =>
    ∃ G : RawGraphPresentation W, ∃ e : Fin B.count ≃ Fin G.externalCount,
      ∀ i, Set.range (G.external.torusMap (e i)) = B.component i

/-- **BBR03 takes ONE tail member** (draft §7.5): EITHER the BBR03 threshold exists, OR there is a
standing sequence below `δ₁` such that every early choice `E` has a register `R` and ONE member
which is a nongraph counterexample AND carries the assignment's full member output. -/
theorem bbr03_one_tail_member_BBS (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ)
    (hA : ∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w) :
    (∃ w₀ : ℝ, 0 < w₀ ∧ w₀ < euclideanThreeUnitBallVolume ∧
      ∀ (W : CompactCarrier.{0}) [ConnectedSpace W.Carrier]
        (g : SmoothRiemannianMetric W.model W.Carrier) (B : NearlyCuspidalBoundary W g K w₀),
        boundaryVolumeCollapsed W g w₀ → curvatureDerivativesControlled g K A w₀ →
          ∃ G : RawGraphPresentation W, ∃ e : Fin B.count ≃ Fin G.externalCount,
            ∀ i, Set.range (G.external.torusMap (e i)) = B.component i) ∨
    ∃ δ₁ : ℝ, ∃ hδ₁ : δ₁ ≤ (bdryThresholds_BSTD1 K hK A hA).δStar,
      ∃ S : BoundaryStandingSequence_BSTD1 K A δ₁,
        ∀ E : BoundaryEarlyChoices_BSTD1 K hK A hA,
        ∃ V : ℝ, ∃ R : BoundaryRegisterOver_BSTD1 E V, ∃ n : ℕ,
          (¬ ∃ G : RawGraphPresentation (S.W n), ∃ e : Fin (S.B n).count ≃ Fin G.externalCount,
            ∀ i, Set.range (G.external.torusMap (e i)) = (S.B n).component i) ∧
          Nonempty (BoundaryMemberOutput_BSTD1 (S.mono_BBS hδ₁) n R) := by
  rcases bbr03_reduction_graph_BBS K hK A hA with h | ⟨δ₁, -, hδ₁, S, -, hng, hS⟩
  · exact Or.inl h
  · refine Or.inr ⟨δ₁, hδ₁, S, fun E => ?_⟩
    obtain ⟨V, R, n₀, hn⟩ := hS E
    exact ⟨V, R, n₀, hng n₀, (hn n₀ le_rfl).1⟩

end DifferentialGeometry.Geometry.Collapse
