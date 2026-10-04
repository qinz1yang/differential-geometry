import DifferentialGeometry.Geometry.Collapse.GraphManifold
import DifferentialGeometry.Geometry.Collapse.BoundaryScale.StandingSequence
import DifferentialGeometry.Geometry.Collapse.BoundaryRegister

/-!
# Counterexample sequences for the static thresholds (PBR02/PBR03 and BBR02/BBR03 framework)

Blueprint 207B: the failure reduction of PBR03 (B:10293–10333) and of BBR03 (B:10621–10645).
If no positive threshold exists, one chooses for every index `n` a counterexample at the ratio
`w_n = min{ω₃/4, 1/(16n⁴)}` (closed, B:10296) or `δ_n = min{δ_*, ω₃/8, 1/(16n⁴)}` (nonempty
boundary, B:10623). On such a closed member the volume collapse gives `R_p > 2n r_p(1/n)` at every
point and the whole-ball trigger gives the (Reduce) bounds with ONE function
`A'(C, w) = boundaryDerivativeConstant A K C w` (B:10302; W4-BSA's BSA04 kernels).

The certificate the PBR02/BBR02 producers must supply is a parameter `Good` of these statements:
the raw presentation, or the literal DI disjunction of the merged LFR50 design, or the labelled
boundary presentation. Nothing here assumes a producer; the two admitted threshold theorems of
`GraphManifold` are not used.
-/

set_option autoImplicit false

noncomputable section

open Filter Set
open DifferentialGeometry GC.Endpoint GC.GraphManifold DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff ENNReal Topology

namespace DifferentialGeometry.Geometry.Collapse

universe u

theorem euclideanThreeUnitBallVolume_pos : 0 < euclideanThreeUnitBallVolume := by
  unfold euclideanThreeUnitBallVolume
  positivity

/-- PBR03's counterexample ratio `w_n = min{ω₃/4, 1/(16n⁴)}` (B:10296). -/
def closedCounterexampleRatio (n : ℕ) : ℝ :=
  min (euclideanThreeUnitBallVolume / 4) (1 / (16 * (n : ℝ) ^ 4))

theorem closedCounterexampleRatio_pos {n : ℕ} (hn : 1 ≤ n) : 0 < closedCounterexampleRatio n := by
  have : (0 : ℝ) < n := by exact_mod_cast hn
  exact lt_min (by have := euclideanThreeUnitBallVolume_pos; positivity) (by positivity)

theorem closedCounterexampleRatio_lt_volume (n : ℕ) :
    closedCounterexampleRatio n < euclideanThreeUnitBallVolume := by
  have := euclideanThreeUnitBallVolume_pos
  exact (min_le_left _ _).trans_lt (by linarith)

theorem closedCounterexampleRatio_mul_le {n : ℕ} (hn : 1 ≤ n) :
    closedCounterexampleRatio n * (16 * (n : ℝ) ^ 4) ≤ 1 := by
  have : (0 : ℝ) < n := by exact_mod_cast hn
  have hle : closedCounterexampleRatio n ≤ 1 / (16 * (n : ℝ) ^ 4) := min_le_right _ _
  calc closedCounterexampleRatio n * (16 * (n : ℝ) ^ 4)
      ≤ 1 / (16 * (n : ℝ) ^ 4) * (16 * (n : ℝ) ^ 4) :=
        mul_le_mul_of_nonneg_right hle (by positivity)
    _ = 1 := by field_simp

/-- BBR03's counterexample ratio `δ_n = min{δ_*, ω₃/8, 1/(16n⁴)}` (B:10623). -/
def boundaryCounterexampleRatio (δStar : ℝ) (n : ℕ) : ℝ :=
  min δStar (min (euclideanThreeUnitBallVolume / 8) (1 / (16 * (n : ℝ) ^ 4)))

theorem boundaryCounterexampleRatio_pos {δStar : ℝ} (hδ : 0 < δStar) {n : ℕ} (hn : 1 ≤ n) :
    0 < boundaryCounterexampleRatio δStar n := by
  have : (0 : ℝ) < n := by exact_mod_cast hn
  exact lt_min hδ (lt_min (by have := euclideanThreeUnitBallVolume_pos; positivity)
    (by positivity))

theorem boundaryCounterexampleRatio_le (δStar : ℝ) (n : ℕ) :
    boundaryCounterexampleRatio δStar n ≤ δStar :=
  min_le_left _ _

theorem boundaryCounterexampleRatio_lt_cap (δStar : ℝ) (n : ℕ) :
    boundaryCounterexampleRatio δStar n < boundaryVolumeCap := by
  have := euclideanThreeUnitBallVolume_pos
  unfold boundaryVolumeCap
  exact ((min_le_right _ _).trans (min_le_left _ _)).trans_lt (by linarith)

theorem boundaryCounterexampleRatio_lt_volume (δStar : ℝ) (n : ℕ) :
    boundaryCounterexampleRatio δStar n < euclideanThreeUnitBallVolume :=
  (boundaryCounterexampleRatio_lt_cap δStar n).trans boundaryVolumeCap_lt

theorem boundaryCounterexampleRatio_mul_le (δStar : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    boundaryCounterexampleRatio δStar n * (16 * (n : ℝ) ^ 4) ≤ 1 := by
  have : (0 : ℝ) < n := by exact_mod_cast hn
  have hle : boundaryCounterexampleRatio δStar n ≤ 1 / (16 * (n : ℝ) ^ 4) :=
    (min_le_right _ _).trans (min_le_right _ _)
  calc boundaryCounterexampleRatio δStar n * (16 * (n : ℝ) ^ 4)
      ≤ 1 / (16 * (n : ℝ) ^ 4) * (16 * (n : ℝ) ^ 4) :=
        mul_le_mul_of_nonneg_right hle (by positivity)
    _ = 1 := by field_simp

/-! ### From "no threshold" to counterexamples -/

/-- PBR03's failure step (B:10293–10297): if no closed finite-scale threshold exists for the
certificate `Good`, every index `n ≥ 1` has a closed counterexample at the ratio `w_n`. -/
theorem exists_closed_counterexample_of_no_threshold (K : ℕ) (A : ℝ → ℝ)
    (Good : CompactCarrier.{u} → Prop)
    (h : ¬ ∃ w₀ : ℝ, 0 < w₀ ∧ w₀ < euclideanThreeUnitBallVolume ∧
      ∀ (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
        (g : SmoothRiemannianMetric W.model W.Carrier),
        (∀ p, curvatureRadius g p ≠ ⊤) → closedCollapseHypotheses W g K A w₀ → Good W)
    {n : ℕ} (hn : 1 ≤ n) :
    ∃ (W : CompactCarrier.{u}) (_ : ConnectedSpace W.Carrier)
      (g : SmoothRiemannianMetric W.model W.Carrier),
      (∀ p, curvatureRadius g p ≠ ⊤) ∧
        closedCollapseHypotheses W g K A (closedCounterexampleRatio n) ∧ ¬ Good W := by
  by_contra hno
  apply h
  refine ⟨closedCounterexampleRatio n, closedCounterexampleRatio_pos hn,
    closedCounterexampleRatio_lt_volume n, ?_⟩
  intro W hW g hfin hcol
  by_contra hgood
  exact hno ⟨W, hW, g, hfin, hcol, hgood⟩

/-- BBR03's failure step (B:10621–10625): if no nonempty-boundary threshold exists for the
certificate `Good` (which may read the boundary data, e.g. its labels), every index `n ≥ 1` has a
boundary counterexample at the ratio `δ_n`. -/
theorem exists_boundary_counterexample_of_no_threshold (K : ℕ) (A : ℝ → ℝ) {δStar : ℝ}
    (hδ : 0 < δStar)
    (Good : ∀ (W : CompactCarrier.{u}) (g : SmoothRiemannianMetric W.model W.Carrier) (w : ℝ),
      NearlyCuspidalBoundary W g K w → Prop)
    (h : ¬ ∃ w₀ : ℝ, 0 < w₀ ∧ w₀ < euclideanThreeUnitBallVolume ∧
      ∀ (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
        (g : SmoothRiemannianMetric W.model W.Carrier) (B : NearlyCuspidalBoundary W g K w₀),
        boundaryVolumeCollapsed W g w₀ → curvatureDerivativesControlled g K A w₀ → Good W g w₀ B)
    {n : ℕ} (hn : 1 ≤ n) :
    ∃ (W : CompactCarrier.{u}) (_ : ConnectedSpace W.Carrier)
      (g : SmoothRiemannianMetric W.model W.Carrier)
      (B : NearlyCuspidalBoundary W g K (boundaryCounterexampleRatio δStar n)),
      boundaryVolumeCollapsed W g (boundaryCounterexampleRatio δStar n) ∧
        curvatureDerivativesControlled g K A (boundaryCounterexampleRatio δStar n) ∧
          ¬ Good W g (boundaryCounterexampleRatio δStar n) B := by
  by_contra hno
  apply h
  refine ⟨boundaryCounterexampleRatio δStar n, boundaryCounterexampleRatio_pos hδ hn,
    boundaryCounterexampleRatio_lt_volume δStar n, ?_⟩
  intro W hW g B hvol hder
  by_contra hgood
  exact hno ⟨W, hW, g, B, hvol, hder, hgood⟩

/-! ### Standing data on one closed member -/

/-- PBR03 (B:10298–10304): on a closed member at the ratio `w_n`, `R_p > 2n r_p(1/n)` at every
point (BSA04.a kernel of W4-BSA; also when `R_p = ∞`). -/
theorem closed_standing_of_closedCollapseHypotheses {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {A : ℝ → ℝ} {n : ℕ} (hn : 1 ≤ n)
    (h : closedCollapseHypotheses W g K A (closedCounterexampleRatio n)) (p : W.Carrier) :
    ENNReal.ofReal (2 * (n : ℝ) * firstVolumeScale g p (n : ℝ)⁻¹) < curvatureRadius g p :=
  ofReal_two_mul_firstVolumeScale_lt_of_collapsed g p (by exact_mod_cast hn)
    (closedCounterexampleRatio_mul_le hn) (h.2.1 p)

/-- PBR03 (B:10305–10328): on a closed member at the ratio `w_n`, `n ≥ 2`, the whole-ball trigger
gives, for `0 < C < n` (any real `C < n`) and `1/n ≤ w < ω₃`, every order `k ≤ K` of the bound
`|∇^k Rm| ≤ A'(C, w) r_p(w)^{-(k+2)}` on `B(p, C r_p(w))`, with the ONE function (Reduce). -/
theorem closed_reduce_of_closedCollapseHypotheses {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {A : ℝ → ℝ} {n : ℕ} (hn : 2 ≤ n)
    (h : closedCollapseHypotheses W g K A (closedCounterexampleRatio n)) (p : W.Carrier)
    {C w : ℝ} (hCn : C < n) (hwn : (n : ℝ)⁻¹ ≤ w) (hwc : w < euclideanThreeUnitBallVolume) :
    ∀ k ≤ K, ∀ q ∈ riemannianBallOf g p (C * firstVolumeScale g p w),
      curvatureDerivativeNorm g k q ≤
        boundaryDerivativeConstant A K C w * (firstVolumeScale g p w ^ (k + 2))⁻¹ := by
  have hn1 : 1 ≤ n := le_trans (by norm_num) hn
  have hnR : (1 : ℝ) < n := by exact_mod_cast hn
  have hδ : closedCounterexampleRatio n * (n : ℝ) ^ 4 ≤ 1 := by
    have h16 := closedCounterexampleRatio_mul_le hn1
    have hpos := closedCounterexampleRatio_pos hn1
    have : (0 : ℝ) ≤ n ^ 4 := by positivity
    nlinarith
  exact curvatureDerivativeNorm_le_on_firstVolumeScale_ball g h.2.2 hnR hδ
    (closed_standing_of_closedCollapseHypotheses hn1 h p) hCn hwn hwc

/-- The exact standing input of LC09 (`exists_kl618_metric_model_tail`) with `α = n`:
`n r_p(1/n) ≤ R_p` at every point. -/
theorem closed_lc09_standing_of_closedCollapseHypotheses {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {A : ℝ → ℝ} {n : ℕ} (hn : 1 ≤ n)
    (h : closedCollapseHypotheses W g K A (closedCounterexampleRatio n)) (p : W.Carrier) :
    ENNReal.ofReal ((n : ℝ) * firstVolumeScale g p (n : ℝ)⁻¹) ≤ curvatureRadius g p := by
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) (closed_standing_of_closedCollapseHypotheses hn h p).le
  have := firstVolumeScale_nonneg g p (n : ℝ)⁻¹
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith

/-! ### The closed standing sequence -/

/-- PBR02/PBR03 framework (B:10293–10333): if no closed finite-scale threshold exists for the
certificate `Good`, there is a sequence of closed connected counterexamples `(W_n, g_n)` at the
ratios `w_{n+2}`, each with finite curvature scales, without `Good`, with
`R_p > 2(n+2) r_p(1/(n+2))` at every point and the (Reduce) bounds for `C < n+2`,
`1/(n+2) ≤ w < ω₃`. The PBR02 producer must supply `Good` on a tail of exactly such members. -/
theorem exists_closed_standing_sequence_of_no_threshold (K : ℕ) (A : ℝ → ℝ)
    (Good : CompactCarrier.{u} → Prop)
    (h : ¬ ∃ w₀ : ℝ, 0 < w₀ ∧ w₀ < euclideanThreeUnitBallVolume ∧
      ∀ (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
        (g : SmoothRiemannianMetric W.model W.Carrier),
        (∀ p, curvatureRadius g p ≠ ⊤) → closedCollapseHypotheses W g K A w₀ → Good W) :
    ∃ (W : ℕ → CompactCarrier.{u}) (_ : ∀ n, ConnectedSpace (W n).Carrier)
      (g : ∀ n, SmoothRiemannianMetric (W n).model (W n).Carrier),
      ∀ n, (∀ p, curvatureRadius (g n) p ≠ ⊤) ∧
        closedCollapseHypotheses (W n) (g n) K A (closedCounterexampleRatio (n + 2)) ∧
        ¬ Good (W n) ∧
        (∀ p, ENNReal.ofReal (2 * ((n + 2 : ℕ) : ℝ) * firstVolumeScale (g n) p ((n + 2 : ℕ) : ℝ)⁻¹)
          < curvatureRadius (g n) p) ∧
        ∀ p (C w : ℝ), C < ((n + 2 : ℕ) : ℝ) → ((n + 2 : ℕ) : ℝ)⁻¹ ≤ w →
          w < euclideanThreeUnitBallVolume →
          ∀ k ≤ K, ∀ q ∈ riemannianBallOf (g n) p (C * firstVolumeScale (g n) p w),
            curvatureDerivativeNorm (g n) k q ≤
              boundaryDerivativeConstant A K C w * (firstVolumeScale (g n) p w ^ (k + 2))⁻¹ := by
  have hmem : ∀ n : ℕ, ∃ (W : CompactCarrier.{u}) (_ : ConnectedSpace W.Carrier)
      (g : SmoothRiemannianMetric W.model W.Carrier),
      (∀ p, curvatureRadius g p ≠ ⊤) ∧
        closedCollapseHypotheses W g K A (closedCounterexampleRatio (n + 2)) ∧ ¬ Good W :=
    fun n => exists_closed_counterexample_of_no_threshold K A Good h (by omega)
  choose W hW g hg using hmem
  refine ⟨W, hW, g, fun n => ⟨(hg n).1, (hg n).2.1, (hg n).2.2, fun p => ?_, ?_⟩⟩
  · exact closed_standing_of_closedCollapseHypotheses (by omega) (hg n).2.1 p
  · intro p C w hCn hwn hwc
    exact closed_reduce_of_closedCollapseHypotheses (by omega) (hg n).2.1 p hCn hwn hwc

/-- BBR02/BBR03 framework (B:10621–10645): if no nonempty-boundary threshold exists for the
certificate `Good`, there is a sequence of connected boundary counterexamples at the ratios
`δ_{n+1}`, each with its nearly cuspidal boundary data, without `Good`. The per-member standing
data are BSA04's (W4-BSA, from BSA01's near-boundary output); the BBR02 producer must supply
`Good` on a tail of exactly such members. -/
theorem exists_boundary_counterexample_sequence_of_no_threshold (K : ℕ) (A : ℝ → ℝ)
    {δStar : ℝ} (hδ : 0 < δStar)
    (Good : ∀ (W : CompactCarrier.{u}) (g : SmoothRiemannianMetric W.model W.Carrier) (w : ℝ),
      NearlyCuspidalBoundary W g K w → Prop)
    (h : ¬ ∃ w₀ : ℝ, 0 < w₀ ∧ w₀ < euclideanThreeUnitBallVolume ∧
      ∀ (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
        (g : SmoothRiemannianMetric W.model W.Carrier) (B : NearlyCuspidalBoundary W g K w₀),
        boundaryVolumeCollapsed W g w₀ → curvatureDerivativesControlled g K A w₀ → Good W g w₀ B) :
    ∃ (W : ℕ → CompactCarrier.{u}) (_ : ∀ n, ConnectedSpace (W n).Carrier)
      (g : ∀ n, SmoothRiemannianMetric (W n).model (W n).Carrier)
      (B : ∀ n, NearlyCuspidalBoundary (W n) (g n) K (boundaryCounterexampleRatio δStar (n + 1))),
      ∀ n, boundaryVolumeCollapsed (W n) (g n) (boundaryCounterexampleRatio δStar (n + 1)) ∧
        curvatureDerivativesControlled (g n) K A (boundaryCounterexampleRatio δStar (n + 1)) ∧
        ¬ Good (W n) (g n) (boundaryCounterexampleRatio δStar (n + 1)) (B n) := by
  have hmem := fun n : ℕ =>
    exists_boundary_counterexample_of_no_threshold K A hδ Good h (n := n + 1) (by omega)
  choose W hW g B hg using hmem
  exact ⟨W, hW, g, B, hg⟩

end DifferentialGeometry.Geometry.Collapse
