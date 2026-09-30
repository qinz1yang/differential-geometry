# Full AC65 independent source/proof and original-input review

Two public theorems in two leaves add two owned declarations. The316-module
gate checks1400 declarations in3151 jobs. All transitive closures contain only
propext, Classical.choice and Quot.sound. Source-copy unusedArguments/simpNF/
synTaut lint is silent. The accepted-import review compiles silently apart from
eight requested standard axiom reports, including both public theorems.
Declaration kinds were inspected; defLemma is unavailable. Earlier mathematical
leaves are unchanged. The inherited AreaUpperBarrier warning is outside these
closures. Static audit passes. No full migrated root, fresh PDF/Overleaf build,
or human approval is claimed.

One agent implemented the supplied-lines engine, a second the original-input
wrapper, and a third independently source/proof-reviewed both. The engine author
also independently inspected the full wrapper. Root read both full proofs and
ran combined acceptance. The original source ball remains OPEN radius sigma
inverse, curvature remains -sigma, and the supplied radial paths, signed Q,
approximation maps, target lines and composed subsequence remain the same at
every step. No larger source ball or boundary compactness is assumed. The
independent review reopened KL Def3.6/equation3.7 and rendered Lemma4.15(2)'s
statement to confirm the normalization against the archived source and blueprint.
The retained KL correction sheet has no relevant entry. No remote freshness is
claimed. The crossing-line-to-germ dependency path was inspected explicitly:
it uses LineDistance/FourPoint/convex-affine identities, not LineSplitting.

The original-input positive test uses COMPLETE real sources and their actual
constant pointed convergence. It proves arbitrary short affine curves, actual
local four-point comparison, ambientdim<=1 and opposite endpoint identities at
L_i=i+1, sigma_i=1/(i+1). Actual opposite model angles are pi. The rank-one
application retains the ENTIRE target geometry, original radial-family equations,
actual excess limits, psi/R/epsilon/f/Q/gamma, exact segment alignment,
calibrations, same-map uniform convergence and orthogonality package. The Fin0
case retains the same full output and independent approximation radius control.
Cross-pair assertions are intentionally vacuous in these boundary-rank cases;
they are not presented as a full positive two-axis source example.

A substantial independent negative control proves for EVERY positive sigma_i->0
that the curvature-negative-sigma comparison angle with equal arms1/sigma and
side sqrt(2)/sigma tends to0. It derives the exact sinh-ratio formula, its
exponential limit, and the angle limit from the accepted half-angle identity.
Consequently the required pi/2-sigma lower bound fails eventually. The test also
proves actual translated downward/rightward Euclidean endpoints have precisely
that distance and Euclidean comparison angle pi/2, then applies the failure
result to those actual points. This rejects an invalid flat-plane long-strainer
instantiation while preserving the original KL hypothesis. No full two-axis
hyperbolic source example is claimed formalized. Earlier concrete buffered and
fixed-target two-axis tests and same-map cross-angle transfer tests remain valid
on their respective, separately stated hypotheses.

AC65 is complete via the written ALG08 L/1024 route. The full coordinate and
oriented-product assembly AC66/AC54 remains the next separate milestone; AC55
and compatibility also remain. The historical sharp8r theorem is not claimed.
Blueprint207 and migration interfaces are unchanged; Chapters3-4 remain unfinished.

```lean
import DifferentialGeometry.Topology.MetricSpace.SegmentCurves
import Mathlib.Tactic
import DifferentialGeometry.Topology.MetricSpace.BoundaryRadialSegment
import DifferentialGeometry.Geometry.Comparison.OppositeAngleExcess
import DifferentialGeometry.Geometry.Metric.Approximation.GrowingRegionGeometry
import DifferentialGeometry.Geometry.Metric.Approximation.ComparisonLimit
import DifferentialGeometry.Geometry.Metric.Approximation.MidpointTransfer
import DifferentialGeometry.Geometry.Metric.Approximation.PointedConvergence
import DifferentialGeometry.Topology.MetricSpace.SignedPrefix
import DifferentialGeometry.Geometry.Metric.Approximation.PrefixLineLimit
import DifferentialGeometry.Geometry.Comparison.BufferedAngleShortening
import DifferentialGeometry.Geometry.Comparison.OppositeCrossAngles
import DifferentialGeometry.Analysis.Asymptotics.ReciprocalShortening
import DifferentialGeometry.Geometry.Metric.Approximation.PointedBallApproximation
import DifferentialGeometry.Geometry.Comparison.ModelAngle
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.InnerProductSpace.PiL2
import DifferentialGeometry.Geometry.Metric.Approximation.RadialPrefixOrthogonality
import DifferentialGeometry.Geometry.Metric.Approximation.OriginalOrthogonalLines

open Set Filter Metric
open scoped Topology

namespace GCOriginalOrthogonalLinesReview

open DifferentialGeometry.Geometry.Comparison.Toponogov GC.MetricGeometry

private def radius (i : ℕ) : ℝ := (i : ℝ) + 1
private theorem radius_one (i : ℕ) : 1 ≤ radius i := by dsimp [radius]; linarith [Nat.cast_nonneg (α := ℝ) i]
private theorem radius_pos (i : ℕ) : 0 < radius i := lt_of_lt_of_le (by norm_num) (radius_one i)
private theorem radius_top : Tendsto radius atTop atTop :=
  tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop
private theorem same_side_zero {κ : ℝ} (hκ : 0 ≤ κ) (x a b : ℝ) (ha : a ≠ x) (hb : b ≠ x)
    (hs : (x ≤ a ∧ x ≤ b) ∨ (a ≤ x ∧ b ≤ x)) :
    comparisonAngleNegCurvature κ (dist x a) (dist x b) (dist a b) = 0 := by
  have heq : dist a b = |dist x a - dist x b| := by
    rcases hs with ⟨ha', hb'⟩ | ⟨ha', hb'⟩
    · rw [Real.dist_eq a b, Real.dist_eq x a, Real.dist_eq x b,
        abs_of_nonpos (sub_nonpos.mpr ha'), abs_of_nonpos (sub_nonpos.mpr hb')]
      have h : -(x - a) - -(x - b) = a - b := by ring
      rw [h]
    · rw [Real.dist_eq a b, Real.dist_eq x a, Real.dist_eq x b,
        abs_of_nonneg (sub_nonneg.mpr ha'), abs_of_nonneg (sub_nonneg.mpr hb')]
      have h : (x - a) - (x - b) = b - a := by ring
      rw [h, abs_sub_comm]
  rw [heq]
  exact comparisonAngleNegCurvature_abs_sub hκ (dist_pos.mpr ha.symm) (dist_pos.mpr hb.symm)

private theorem real_comparison {κ : ℝ} (hκ : 0 ≤ κ) : fourPointComparison κ (univ : Set ℝ) := by
  intro x _ a _ b _ c _ ha hb hc
  have hab := (comparisonAngleNegCurvature_mem_Icc κ (dist x a) (dist x b) (dist a b)).2
  have hbc := (comparisonAngleNegCurvature_mem_Icc κ (dist x b) (dist x c) (dist b c)).2
  have hca := (comparisonAngleNegCurvature_mem_Icc κ (dist x c) (dist x a) (dist c a)).2
  rcases le_total x a with hxa | hax <;> rcases le_total x b with hxb | hbx <;>
    rcases le_total x c with hxc | hcx
  all_goals first
    | have hz := same_side_zero hκ x a b ha hb (Or.inl ⟨hxa, hxb⟩); linarith
    | have hz := same_side_zero hκ x a b ha hb (Or.inr ⟨hax, hbx⟩); linarith
    | have hz := same_side_zero hκ x b c hb hc (Or.inl ⟨hxb, hxc⟩); linarith
    | have hz := same_side_zero hκ x b c hb hc (Or.inr ⟨hbx, hcx⟩); linarith
    | have hz := same_side_zero hκ x c a hc ha (Or.inl ⟨hxc, hxa⟩); linarith
    | have hz := same_side_zero hκ x c a hc ha (Or.inr ⟨hcx, hax⟩); linarith


private theorem real_segments (x y : ℝ) :
    ∃ f : unitInterval → ℝ, Continuous f ∧ f 0 = x ∧ f 1 = y ∧
      ∀ s t, dist (f s) (f t) = dist x y * dist s t := by
  let f : unitInterval → ℝ := fun t => (1 - (t : ℝ)) * x + (t : ℝ) * y
  refine ⟨f, by fun_prop, by simp [f], by simp [f], ?_⟩
  intro s t
  change |(1 - (s : ℝ)) * x + (s : ℝ) * y - ((1 - (t : ℝ)) * x + (t : ℝ) * y)| =
    |x - y| * |(s : ℝ) - t|
  rw [show (1 - (s : ℝ)) * x + (s : ℝ) * y - ((1 - (t : ℝ)) * x + (t : ℝ) * y) =
    (y - x) * ((s : ℝ) - t) by ring, abs_mul, abs_sub_comm y x]

private noncomputable def sig (i : ℕ) : ℝ := 1 / radius i
private theorem sig_pos (i : ℕ) : 0 < sig i := div_pos (by norm_num) (radius_pos i)
private theorem sig_zero : Tendsto sig atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
private theorem sig_inv (i : ℕ) : (sig i)⁻¹ = radius i := by simp [sig]

private def RealRadialData (ι : Type) : Prop :=
    fourPointComparison 0 (univ : Set ℝ) ∧
    (∀ a b : ℝ, ∃ c : Icc (0 : ℝ) 1 → ℝ,
      Continuous c ∧ c ⟨0, by norm_num⟩ = a ∧ c ⟨1, by norm_num⟩ = b ∧
        ∀ s t, dist (c s) (c t) = dist a b * dist s t) ∧
    (∀ j : ι, Tendsto (fun i => 2 * (sig i)⁻¹ - dist (radius i) (-radius i)) atTop (𝓝 0)) ∧
    ∃ qPlus qMinus : ∀ i, ι → Icc (0 : ℝ) ((sig i)⁻¹) → ℝ,
      (∀ i j, Isometry (qPlus i j)) ∧ (∀ i j, Isometry (qMinus i j)) ∧
      (∀ i j, qPlus i j ⟨0, ⟨le_rfl, (inv_pos.mpr (sig_pos i)).le⟩⟩ = (0 : ℝ)) ∧
      (∀ i j, qMinus i j ⟨0, ⟨le_rfl, (inv_pos.mpr (sig_pos i)).le⟩⟩ = (0 : ℝ)) ∧
      (∀ i j, qPlus i j ⟨(sig i)⁻¹, ⟨(inv_pos.mpr (sig_pos i)).le, le_rfl⟩⟩ = radius i) ∧
      (∀ i j, qMinus i j ⟨(sig i)⁻¹, ⟨(inv_pos.mpr (sig_pos i)).le, le_rfl⟩⟩ = -radius i) ∧
    ∃ (ψ : ℕ → ℕ) (R ε : ℕ → ℝ), StrictMono ψ ∧
      PointedGHConverges (fun i => (0 : ℝ)) (0 : ℝ) ∧ Tendsto R atTop atTop ∧ Tendsto ε atTop (𝓝 0) ∧
      ∃ f : ∀ i, PointedBallApprox ((0 : ℝ)) (0 : ℝ) (R i) (ε i),
      ∃ Q : ∀ i, ι → Icc (-((sig (ψ i))⁻¹)) ((sig (ψ i))⁻¹) → ℝ,
      (∀ i j, LipschitzWith 1 (Q i j)) ∧
      (∀ i j, Q i j ⟨0, ⟨by linarith [inv_pos.mpr (sig_pos (ψ i))],
        (inv_pos.mpr (sig_pos (ψ i))).le⟩⟩ = (0 : ℝ)) ∧
      (∀ i j, ∀ t : Icc (0 : ℝ) ((sig (ψ i))⁻¹),
        Q i j ⟨t.val, ⟨by linarith [t.property.1, inv_pos.mpr (sig_pos (ψ i))], t.property.2⟩⟩ = qPlus (ψ i) j t ∧
        Q i j ⟨-t.val, ⟨by linarith [t.property.2],
          by linarith [t.property.1, inv_pos.mpr (sig_pos (ψ i))]⟩⟩ = qMinus (ψ i) j t) ∧
      (∀ i j, ∀ t : Icc (0 : ℝ) ((sig (ψ i))⁻¹),
        t.val ≤ (sig (ψ i))⁻¹ - dist
          (Q i j ⟨t.val, ⟨by linarith [t.property.1, inv_pos.mpr (sig_pos (ψ i))], t.property.2⟩⟩) (radius (ψ i)) ∧
        (sig (ψ i))⁻¹ - dist
          (Q i j ⟨t.val, ⟨by linarith [t.property.1, inv_pos.mpr (sig_pos (ψ i))], t.property.2⟩⟩) (radius (ψ i)) ≤ t.val ∧
        -t.val ≤ (sig (ψ i))⁻¹ - dist
          (Q i j ⟨-t.val, ⟨by linarith [t.property.2],
            by linarith [t.property.1, inv_pos.mpr (sig_pos (ψ i))]⟩⟩) (radius (ψ i)) ∧
        (sig (ψ i))⁻¹ - dist
          (Q i j ⟨-t.val, ⟨by linarith [t.property.2],
            by linarith [t.property.1, inv_pos.mpr (sig_pos (ψ i))]⟩⟩) (radius (ψ i)) ≤
          -t.val + (2 * (sig (ψ i))⁻¹ - dist (radius (ψ i)) (-radius (ψ i)))) ∧
      ∃ γ : ι → ℝ → ℝ,
        (∀ j, Isometry (γ j)) ∧ (∀ j, γ j 0 = (0 : ℝ)) ∧
        (∀ S ζ : ℝ, 0 < ζ → ∀ᶠ i in atTop,
          S ≤ R i ∧ ∀ j, S ≤ (sig (ψ i))⁻¹ ∧
          ∀ t : Icc (-((sig (ψ i))⁻¹)) ((sig (ψ i))⁻¹), |t.val| ≤ S →
            ∀ ht : dist (Q i j t) ((0 : ℝ)) ≤ R i,
              dist ((f i).toFun ⟨Q i j t, ht⟩) (γ j t.val) < ζ) ∧
        ∀ j k, j ≠ k → germComparisonAngle 0 (γ j) (γ k) = Real.pi / 2

private theorem real_family (ι : Type) [Finite ι] [Subsingleton ι] : RealRadialData ι := by
  exact (PointedGHConverges.const (0 : ℝ)).exists_orthogonal_calibrated_lines_of_reciprocal_local_geometry
    (n := 1) (fun _ => arbitrarily_short_curves_of_metric_segments real_segments)
    (fun i => by simpa only [Nat.cast_one] using
      (dimH_mono (subset_univ (ball (0 : ℝ) ((sig i)⁻¹)))).trans_eq Real.dimH_univ)
    (fun i z _ => ⟨univ, isOpen_univ, real_comparison (sig_pos i).le, mem_univ z⟩)
    (fun i (_ : ι) => radius i) (fun i _ => -radius i) sig_pos sig_zero
    (fun i _ => by rw [sig_inv, Real.dist_eq, zero_sub, abs_neg, abs_of_pos (radius_pos i)])
    (fun i _ => by rw [sig_inv, Real.dist_eq, zero_sub, neg_neg, abs_of_pos (radius_pos i)]) (by
      intro j
      exact Eventually.of_forall fun i => by
        have hh := comparisonAngleNegCurvature_add (sig_pos i).le (radius_pos i) (radius_pos i)
        rw [Real.dist_eq (0 : ℝ) (radius i), Real.dist_eq (0 : ℝ) (-radius i),
          Real.dist_eq (radius i) (-radius i), zero_sub, abs_neg, abs_of_pos (radius_pos i),
          zero_sub, neg_neg, abs_of_pos (radius_pos i), sub_neg_eq_add,
          abs_of_pos (show 0 < radius i + radius i by linarith [radius_pos i]), hh]
        linarith [sig_pos i])
    (fun j k hjk => (hjk (Subsingleton.elim j k)).elim)
    (fun j k hjk => (hjk (Subsingleton.elim j k)).elim)

-- Both applications retain every generated q±, subsequence, approximation, signed-prefix
-- alignment, calibration, and convergence field of the original-input theorem.
theorem real_one_axis_full_package : RealRadialData (Fin 1) := real_family (Fin 1)
theorem real_no_axes_full_package : RealRadialData (Fin 0) := real_family (Fin 0)

end GCOriginalOrthogonalLinesReview


namespace GCAC65FlatLongAnglesReview

open DifferentialGeometry.Geometry.Comparison.Toponogov

private theorem sinh_ratio {a x : ℝ} (hx : 0 < x) :
    Real.sinh (a * x) / Real.sinh x =
      (Real.exp ((a - 1) * x) - Real.exp (-(a + 1) * x)) /
        (1 - Real.exp (-2 * x)) := by
  have hden : 1 - Real.exp (-2 * x) ≠ 0 :=
    (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))).ne'
  have hsinh : Real.sinh x ≠ 0 := (Real.sinh_pos_iff.mpr hx).ne'
  have h1 : Real.exp (a * x) = Real.exp ((a - 1) * x) * Real.exp x := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h2 : Real.exp (-(a * x)) = Real.exp (-(a + 1) * x) * Real.exp x := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h3 : Real.exp (-x) = Real.exp (-2 * x) * Real.exp x := by
    rw [← Real.exp_add]
    congr 1
    ring
  apply (div_eq_div_iff hsinh hden).mpr
  rw [Real.sinh_eq, Real.sinh_eq, h1, h2, h3]
  ring

private theorem tendsto_sinh_ratio {x : ℕ → ℝ} {a : ℝ}
    (ha : -1 < a) (ha1 : a < 1) (hx : Tendsto x atTop atTop) :
    Tendsto (fun i => Real.sinh (a * x i) / Real.sinh (x i)) atTop (𝓝 0) := by
  have h1 := Real.tendsto_exp_atBot.comp (hx.const_mul_atTop_of_neg (show a - 1 < 0 by linarith))
  have h2 := Real.tendsto_exp_atBot.comp (hx.const_mul_atTop_of_neg (show -(a + 1) < 0 by linarith))
  have h3 := Real.tendsto_exp_atBot.comp (hx.const_mul_atTop_of_neg (show (-2 : ℝ) < 0 by norm_num))
  have ht := (h1.sub h2).div (tendsto_const_nhds.sub h3) (by norm_num : (1 : ℝ) - 0 ≠ 0)
  have ht' : Tendsto (fun i => (Real.exp ((a - 1) * x i) - Real.exp (-(a + 1) * x i)) /
      (1 - Real.exp (-2 * x i))) atTop (𝓝 0) := by
    convert ht using 1 <;> simp only [Function.comp_def, sub_zero, zero_div]
    funext i
    rfl
  apply ht'.congr'
  filter_upwards [hx.eventually_gt_atTop 0] with i hi
  exact (sinh_ratio hi).symm

private theorem flat_long_comparison_tends_zero {σ : ℕ → ℝ}
    (hσpos : ∀ i, 0 < σ i) (hσ : Tendsto σ atTop (𝓝 0)) :
    Tendsto (fun i => comparisonAngleNegCurvature (σ i) ((σ i)⁻¹) ((σ i)⁻¹)
      (Real.sqrt 2 * (σ i)⁻¹)) atTop (𝓝 0) := by
  have hsqrt : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hsqrt_sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsqrt2 : Real.sqrt 2 < 2 := by nlinarith
  have hx : Tendsto (fun i => Real.sqrt (σ i) * (σ i)⁻¹) atTop atTop := by
    simpa only [div_one] using
      Real.tendsto_sqrt_mul_reciprocal_div_atTop (C := 1) (by norm_num) hσpos hσ
  have hr := tendsto_sinh_ratio (a := Real.sqrt 2 / 2) (by linarith) (by linarith) hx
  have hsin (i : ℕ) : Real.sin (comparisonAngleNegCurvature (σ i) ((σ i)⁻¹) ((σ i)⁻¹)
      (Real.sqrt 2 * (σ i)⁻¹) / 2) =
      Real.sinh (Real.sqrt 2 / 2 * (Real.sqrt (σ i) * (σ i)⁻¹)) /
        Real.sinh (Real.sqrt (σ i) * (σ i)⁻¹) := by
    have hL : 0 < (σ i)⁻¹ := inv_pos.mpr (hσpos i)
    have hh := sinh_half_eq_mul_sin_comparison_half (hσpos i) hL
      (mul_nonneg hsqrt hL.le) (mul_le_mul_of_nonneg_right hsqrt2.le hL.le)
    have he : Real.sqrt (σ i) * (Real.sqrt 2 * (σ i)⁻¹) / 2 =
        Real.sqrt 2 / 2 * (Real.sqrt (σ i) * (σ i)⁻¹) := by ring
    rw [he] at hh
    apply (eq_div_iff (Real.sinh_pos_iff.mpr (mul_pos (Real.sqrt_pos.mpr (hσpos i)) hL)).ne').mpr
    rw [mul_comm]
    exact hh.symm
  have hangle (i : ℕ) : comparisonAngleNegCurvature (σ i) ((σ i)⁻¹) ((σ i)⁻¹)
      (Real.sqrt 2 * (σ i)⁻¹) =
      2 * Real.arcsin (Real.sinh (Real.sqrt 2 / 2 * (Real.sqrt (σ i) * (σ i)⁻¹)) /
        Real.sinh (Real.sqrt (σ i) * (σ i)⁻¹)) := by
    rw [← hsin i, Real.arcsin_sin]
    · ring
    · linarith [(comparisonAngleNegCurvature_mem_Icc (σ i) ((σ i)⁻¹) ((σ i)⁻¹)
        (Real.sqrt 2 * (σ i)⁻¹)).1, Real.pi_pos]
    · linarith [(comparisonAngleNegCurvature_mem_Icc (σ i) ((σ i)⁻¹) ((σ i)⁻¹)
        (Real.sqrt 2 * (σ i)⁻¹)).2]
  simpa only [hangle, Real.arcsin_zero, mul_zero] using hr.arcsin.const_mul 2

private theorem flat_long_cross_angle_premise_fails {σ : ℕ → ℝ}
    (hσpos : ∀ i, 0 < σ i) (hσ : Tendsto σ atTop (𝓝 0)) :
    ∀ᶠ i in atTop, ¬ Real.pi / 2 - σ i ≤
      comparisonAngleNegCurvature (σ i) ((σ i)⁻¹) ((σ i)⁻¹) (Real.sqrt 2 * (σ i)⁻¹) := by
  have hp : 0 < Real.pi / 4 := by linarith [Real.pi_pos]
  filter_upwards [(flat_long_comparison_tends_zero hσpos hσ).eventually (gt_mem_nhds hp),
    hσ.eventually (gt_mem_nhds hp)] with i hi hsi
  exact not_le.mpr (by linarith)

private abbrev Plane := EuclideanSpace ℝ (Fin 2)

private def down (t : ℝ) : Plane := WithLp.toLp 2 ![3, -2 - t]
private def right (t : ℝ) : Plane := WithLp.toLp 2 ![3 + t, -2]

private theorem translated_orthogonal_distance {L : ℝ} (hL : 0 ≤ L) :
    dist (down L) (right L) = Real.sqrt 2 * L := by
  apply (sq_eq_sq₀ dist_nonneg (mul_nonneg (Real.sqrt_nonneg 2) hL)).mp
  rw [EuclideanSpace.dist_sq_eq]
  simp only [Fin.sum_univ_two, Real.dist_eq, sq_abs, down, right, PiLp.toLp_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  ring

private theorem translated_orthogonal_euclidean_angle {L : ℝ} (hL : 0 < L) :
    comparisonAngle L L (dist (down L) (right L)) = Real.pi / 2 := by
  rw [translated_orthogonal_distance hL.le, comparisonAngle, mul_pow,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have he : L ^ 2 + L ^ 2 - 2 * L ^ 2 = 0 := by ring
  rw [he, zero_div, Real.arccos_zero]

private theorem translated_orthogonal_long_cross_angle_fails {σ : ℕ → ℝ}
    (hσpos : ∀ i, 0 < σ i) (hσ : Tendsto σ atTop (𝓝 0)) :
    ∀ᶠ i in atTop, ¬ Real.pi / 2 - σ i ≤
      comparisonAngleNegCurvature (σ i) ((σ i)⁻¹) ((σ i)⁻¹)
        (dist (down ((σ i)⁻¹)) (right ((σ i)⁻¹))) := by
  filter_upwards [flat_long_cross_angle_premise_fails hσpos hσ] with i hi
  rwa [translated_orthogonal_distance (inv_pos.mpr (hσpos i)).le]

#print axioms translated_orthogonal_euclidean_angle
#print axioms translated_orthogonal_long_cross_angle_fails

#print axioms flat_long_comparison_tends_zero
#print axioms flat_long_cross_angle_premise_fails

end GCAC65FlatLongAnglesReview

#print axioms GC.MetricGeometry.PointedGHConverges.exists_orthogonal_calibrated_lines_of_reciprocal_local_geometry
#print axioms GC.MetricGeometry.germComparisonAngle_eq_pi_div_two_of_converging_radial_prefixes
#print axioms GCOriginalOrthogonalLinesReview.real_one_axis_full_package
#print axioms GCOriginalOrthogonalLinesReview.real_no_axes_full_package

#lint- only unusedArguments simpNF synTaut
```
