# Independent supplied-radial extraction and angle-transfer review

Five public theorems in three leaves add six owned declarations, including one
generated declaration. The314-module gate checks1398 declarations in3149 jobs.
All transitive axiom closures contain only propext, Classical.choice and
Quot.sound. Source-copy unusedArguments/simpNF/synTaut lint is silent. The
accepted-import review compiles silently apart from12 requested standard axiom
reports, including all five new public theorems. Declaration kinds were inspected;
defLemma is unavailable. Earlier math is unchanged. The inherited
AreaUpperBarrier warning lies outside these closures. Static audit passes.
No full migrated root, new PDF/Overleaf build, or human approval is claimed.

One agent implemented the radial engine and continuity layer; another independently
inspected those proofs and tested the radial engine. The second agent implemented
the pointed wrapper, and the first independently inspected and instantiated it.
Root reviewed all five proofs and assembled the accepted-import tests. The
engine constructs Q and all original-index alignment equations BEFORE extracting
its subsequence. The wrapper's psi is exactly the composition of its approximation
diagonal and that extraction; R/epsilon/f/Q and all endpoint labels use precisely
that same composition. The target lines are unchanged. The continuity layer uses
only distortion and actual mapped-point convergence. Early IccExtend values are
identified with the original Q on the eventual common domain before limit passage.
No target line-isometry or curvature premise is hidden in this continuity step.

The concrete sources are A_i=(-3(i+1),infinity), with base0 and two pair lengths
i+1 and2(i+1). They are explicitly proved incomplete and nonproper. Supplied
radial isometries are positive/negative identity, and actual approximations are
inclusion into the real line with radius i+1 and error1/[100(i+1)]. The longer
endpoints are outside every approximation ball. The returned Q retains exact
original qPlus/qMinus alignment at EVERY original index and every time; all
eta=0 calibrations become exact positive/negative times because the excess is0.
The test retains one phi and simultaneous convergence through the same maps.
A separate empty-family test checks radius control independently of any axis.

The pointed test first proves actual PointedGHConverges from those inclusion
approximations using restriction and error enlargement. It then invokes the
pointed wrapper and retains its ENTIRE psi/R/epsilon/f/Q/gamma package, exact
original-segment alignment at psi_i, exact calibrations and same-map convergence.
Its empty-family case preserves pointed convergence and radius control as well.

Root's cross-limit regression consumes the ACTUAL Q/phi/gamma produced by the
radial engine. At signed times+2 on pair0 and-3 on pair1 it proves the target
cross-distance is5 by uniqueness of limits and eventual original-segment
alignment. It then applies the actual angle-transfer theorem with model parameter
1/(i+1), and its PUBLIC test conclusion retains the same Q/phi and convergence
of their actual source comparison angles to pi. The early indices need not contain
these times, exercising the extension's legitimate eventual-domain use.
An independent review suggested retaining this limit in the conclusion; that
strengthening was implemented and compiled before acceptance.

These are the same-witness extraction/continuity components for AC65/66. Full
original local-curvature orthogonality is the next separate assembly. Blueprint207
and migration interfaces remain unchanged; Chapters3-4 remain unfinished.

```lean
import Mathlib.Tactic
import DifferentialGeometry.Topology.MetricSpace.SignedPrefix
import DifferentialGeometry.Geometry.Metric.Approximation.PrefixLineLimit
import DifferentialGeometry.Geometry.Metric.Approximation.RadialEndpointLines
import DifferentialGeometry.Geometry.Metric.Approximation.PointedRadialEndpointLines
import DifferentialGeometry.Geometry.Metric.Approximation.PrefixCrossComparison
namespace GCRadialEndpointReview

open Set Metric Filter GC.MetricGeometry
open scoped Topology
private def radius (i : ℕ) : ℝ := (i : ℝ) + 1
private theorem radius_one (i : ℕ) : 1 ≤ radius i := by dsimp [radius]; linarith [Nat.cast_nonneg (α := ℝ) i]
private theorem radius_pos (i : ℕ) : 0 < radius i := lt_of_lt_of_le (by norm_num) (radius_one i)
private theorem radius_top : Tendsto radius atTop atTop :=
  tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop
private def lengths (i : ℕ) (j : Fin 2) : ℝ := ((j.val : ℝ) + 1) * radius i
private theorem length_pos (i : ℕ) (j : Fin 2) : 0 < lengths i j := by
  dsimp [lengths]
  exact mul_pos (by positivity) (radius_pos i)
private theorem length_lt (i : ℕ) (j : Fin 2) : lengths i j < 3 * radius i := by
  have hj : (j.val : ℝ) < 2 := by exact_mod_cast j.isLt
  dsimp [lengths]
  nlinarith [radius_pos i]
private theorem lengths_top (j : Fin 2) : Tendsto (fun i => lengths i j) atTop atTop :=
  radius_top.const_mul_atTop (by positivity)
private abbrev Source (i : ℕ) := Ioi (-(3 * radius i))
private def base (i : ℕ) : Source i := ⟨0, by change -(3 * radius i) < 0; linarith [radius_pos i]⟩
private def positiveEnd (i : ℕ) (j : Fin 2) : Source i :=
  ⟨lengths i j, by change -(3 * radius i) < lengths i j; linarith [radius_pos i, length_pos i j]⟩
private def negativeEnd (i : ℕ) (j : Fin 2) : Source i :=
  ⟨-lengths i j, by change -(3 * radius i) < -lengths i j; linarith [length_lt i j]⟩
private noncomputable def errors (i : ℕ) : ℝ := (1 / ((i : ℝ) + 1)) / 100
private theorem errors_pos (i : ℕ) : 0 < errors i := by dsimp [errors]; positivity
private theorem errors_lt (i : ℕ) : errors i < radius i := by
  have hi : 0 ≤ (i : ℝ) := Nat.cast_nonneg i
  have hh : 1 / ((i : ℝ) + 1) ≤ 1 := (div_le_iff₀ (by positivity)).mpr (by linarith)
  dsimp [errors, radius]
  linarith
private theorem errors_zero : Tendsto errors atTop (𝓝 0) := by
  change Tendsto (fun i : ℕ => (1 / ((i : ℝ) + 1)) / 100) atTop (𝓝 0)
  simpa only [zero_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).div_const 100
private def approx (i : ℕ) : PointedBallApprox (base i) (0 : ℝ) (radius i) (errors i) where
  error_pos := errors_pos i
  error_lt_radius := errors_lt i
  toFun x := x.val.val
  basepoint := rfl
  distortion x y := by simpa only [Subtype.dist_eq, sub_self, abs_zero] using errors_pos i
  coverage y hy := by
    have hyabs : |y| ≤ radius i - errors i := by simpa only [Real.dist_eq, sub_zero] using hy
    have hsrc : -(3 * radius i) < y := by linarith [(abs_le.mp hyabs).1, radius_pos i, errors_pos i]
    refine ⟨⟨⟨y, hsrc⟩, ?_⟩, ?_⟩
    · change |y - 0| ≤ radius i
      rw [sub_zero]
      linarith [errors_pos i]
    · simpa only [dist_self] using errors_pos i

private theorem source_not_complete (i : ℕ) : ¬ CompleteSpace (Source i) := by
  intro h
  let := h
  have hi : Isometry (Subtype.val : Source i → ℝ) := isometry_subtype_coe
  have hc : IsClosed (Ioi (-(3 * radius i))) := by
    simpa only [Subtype.range_val] using hi.isUniformInducing.isComplete_range.isClosed
  have hz : -(3 * radius i) ∈ closure (Ioi (-(3 * radius i))) := by
    simpa only [closure_Ioi, mem_Ici] using (le_rfl : -(3 * radius i) ≤ -(3 * radius i))
  rw [hc.closure_eq] at hz
  exact lt_irrefl (-(3 * radius i)) hz

example (i : ℕ) : ¬ ProperSpace (Source i) := by
  intro h
  let := h
  exact source_not_complete i inferInstance

example (i : ℕ) : radius i < dist (base i) (positiveEnd i 1) := by
  have hh := radius_pos i
  change radius i < |0 - lengths i 1|
  rw [zero_sub, abs_neg, abs_of_pos (length_pos i 1)]
  norm_num [lengths]
  linarith


private def qPlus (i : ℕ) (j : Fin 2) : Icc (0 : ℝ) (lengths i j) → Source i :=
  fun t => ⟨t.val, by change -(3 * radius i) < t.val; linarith [t.property.1, radius_pos i]⟩
private def qMinus (i : ℕ) (j : Fin 2) : Icc (0 : ℝ) (lengths i j) → Source i :=
  fun t => ⟨-t.val, by change -(3 * radius i) < -t.val; linarith [t.property.2, length_lt i j]⟩
private theorem qPlus_isometry (i : ℕ) (j : Fin 2) : Isometry (qPlus i j) :=
  Isometry.of_dist_eq (fun _ _ => rfl)
private theorem qMinus_isometry (i : ℕ) (j : Fin 2) : Isometry (qMinus i j) :=
  Isometry.of_dist_eq (fun s t => dist_neg_neg s.val t.val)
private theorem qPlus_zero (i : ℕ) (j : Fin 2) :
    qPlus i j ⟨0, ⟨le_rfl, (length_pos i j).le⟩⟩ = base i := rfl
private theorem qMinus_zero (i : ℕ) (j : Fin 2) :
    qMinus i j ⟨0, ⟨le_rfl, (length_pos i j).le⟩⟩ = base i := by
  apply Subtype.ext
  exact neg_zero
private theorem qPlus_end (i : ℕ) (j : Fin 2) :
    qPlus i j ⟨lengths i j, ⟨(length_pos i j).le, le_rfl⟩⟩ = positiveEnd i j := rfl
private theorem qMinus_end (i : ℕ) (j : Fin 2) :
    qMinus i j ⟨lengths i j, ⟨(length_pos i j).le, le_rfl⟩⟩ = negativeEnd i j := rfl

private theorem excess_zero (i : ℕ) (j : Fin 2) :
    2 * lengths i j - dist (positiveEnd i j) (negativeEnd i j) = 0 := by
  change 2 * lengths i j - |lengths i j - (-lengths i j)| = 0
  rw [abs_of_nonneg (by linarith [length_pos i j])]
  ring

private theorem excess_limit (j : Fin 2) :
    Tendsto (fun i => 2 * lengths i j - dist (positiveEnd i j) (negativeEnd i j)) atTop (𝓝 0) := by
  simpa only [excess_zero] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

private theorem exact_original_radial_family :
    ∃ Q : ∀ i j, Icc (-(lengths i j)) (lengths i j) → Source i,
      (∀ i j, LipschitzWith 1 (Q i j)) ∧
      (∀ i j, Q i j ⟨0, ⟨by linarith [length_pos i j], (length_pos i j).le⟩⟩ = base i) ∧
      (∀ i j, ∀ t : Icc (0 : ℝ) (lengths i j),
        Q i j ⟨t.val, ⟨by linarith [t.property.1, length_pos i j], t.property.2⟩⟩ = qPlus i j t ∧
        Q i j ⟨-t.val, ⟨by linarith [t.property.2], by linarith [t.property.1, length_pos i j]⟩⟩ = qMinus i j t) ∧
      (∀ i j, ∀ t : Icc (0 : ℝ) (lengths i j),
        lengths i j - dist (Q i j ⟨t.val, ⟨by linarith [t.property.1, length_pos i j], t.property.2⟩⟩)
          (positiveEnd i j) = t.val ∧
        lengths i j - dist (Q i j ⟨-t.val, ⟨by linarith [t.property.2], by linarith [t.property.1, length_pos i j]⟩⟩)
          (positiveEnd i j) = -t.val) ∧
      ∃ (γ : Fin 2 → ℝ → ℝ) (φ : ℕ → ℕ),
        (∀ j, Isometry (γ j)) ∧ (∀ j, γ j 0 = 0) ∧ StrictMono φ ∧
        ∀ S ζ : ℝ, 0 < ζ → ∀ᶠ i in atTop,
          S ≤ radius (φ i) ∧ ∀ j, S ≤ lengths (φ i) j ∧
          ∀ t : Icc (-(lengths (φ i) j)) (lengths (φ i) j), |t.val| ≤ S →
            ∀ ht : dist (Q (φ i) j t) (base (φ i)) ≤ radius (φ i),
              dist ((approx (φ i)).toFun ⟨Q (φ i) j t, ht⟩) (γ j t.val) < ζ := by
  obtain ⟨Q, hLip, hbase, halign, hcal, γ, φ, hγ, hγ0, hφ, hconv⟩ :=
    exists_calibrated_lines_of_opposite_radial_isometries approx radius_top errors_zero
      positiveEnd negativeEnd length_pos lengths_top qPlus qMinus qPlus_isometry qMinus_isometry
      qPlus_zero qMinus_zero qPlus_end qMinus_end excess_limit
  refine ⟨Q, hLip, hbase, halign, ?_, γ, φ, hγ, hγ0, hφ, hconv⟩
  intro i j t
  have hh := hcal i j t
  exact ⟨le_antisymm hh.2.1 hh.1,
    le_antisymm (by linarith only [hh.2.2.2, excess_zero i j]) hh.2.2.1⟩

private theorem empty_family :
    ∃ (φ : ℕ → ℕ), StrictMono φ ∧ ∀ S : ℝ, ∀ᶠ i in atTop, S ≤ radius (φ i) := by
  obtain ⟨Q, hLip, hbase, halign, hcal, γ, φ, hγ, hγ0, hφ, hconv⟩ :=
    exists_calibrated_lines_of_opposite_radial_isometries (ι := Fin 0) (L := fun _ _ => 0)
      approx radius_top errors_zero
      (fun _ j => Fin.elim0 j) (fun _ j => Fin.elim0 j)
      (fun _ j => Fin.elim0 j) (fun j => Fin.elim0 j)
      (fun _ j => Fin.elim0 j) (fun _ j => Fin.elim0 j)
      (fun _ j => Fin.elim0 j) (fun _ j => Fin.elim0 j)
      (fun _ j => Fin.elim0 j) (fun _ j => Fin.elim0 j)
      (fun _ j => Fin.elim0 j) (fun _ j => Fin.elim0 j)
      (fun j => Fin.elim0 j)
  refine ⟨φ, hφ, ?_⟩
  intro S
  filter_upwards [hconv S 1 (by norm_num)] with i hi
  exact hi.1


end GCRadialEndpointReview

namespace GCRadialEndpointReview

open Set Metric Filter GC.MetricGeometry
open scoped Topology

private theorem source_pointed_convergence : PointedGHConverges base (0 : ℝ) := by
  refine ⟨inferInstance, ?_⟩
  intro R ε hε hεR
  filter_upwards [radius_top.eventually (eventually_ge_atTop R),
    errors_zero.eventually (eventually_lt_nhds (by positivity : 0 < ε / 2))] with i hiR hie
  exact ⟨((approx i).restrict (by linarith) hiR).enlargeError (by linarith) hεR⟩

private theorem pointed_exact_original_radial_family :
    ∃ (ψ : ℕ → ℕ) (R ε : ℕ → ℝ), StrictMono ψ ∧
      PointedGHConverges (fun i => base (ψ i)) (0 : ℝ) ∧
      Tendsto R atTop atTop ∧ Tendsto ε atTop (𝓝 0) ∧
      ∃ f : ∀ i, PointedBallApprox (base (ψ i)) (0 : ℝ) (R i) (ε i),
      ∃ Q : ∀ i j, Icc (-(lengths (ψ i) j)) (lengths (ψ i) j) → Source (ψ i),
      (∀ i j, LipschitzWith 1 (Q i j)) ∧
      (∀ i j, Q i j ⟨0, ⟨by linarith [length_pos (ψ i) j], (length_pos (ψ i) j).le⟩⟩ = base (ψ i)) ∧
      (∀ i j, ∀ t : Icc (0 : ℝ) (lengths (ψ i) j),
        Q i j ⟨t.val, ⟨by linarith [t.property.1, length_pos (ψ i) j], t.property.2⟩⟩ = qPlus (ψ i) j t ∧
        Q i j ⟨-t.val, ⟨by linarith [t.property.2], by linarith [t.property.1, length_pos (ψ i) j]⟩⟩ = qMinus (ψ i) j t) ∧
      (∀ i j, ∀ t : Icc (0 : ℝ) (lengths (ψ i) j),
        lengths (ψ i) j - dist (Q i j ⟨t.val, ⟨by linarith [t.property.1, length_pos (ψ i) j], t.property.2⟩⟩)
          (positiveEnd (ψ i) j) = t.val ∧
        lengths (ψ i) j - dist (Q i j ⟨-t.val, ⟨by linarith [t.property.2], by linarith [t.property.1, length_pos (ψ i) j]⟩⟩)
          (positiveEnd (ψ i) j) = -t.val) ∧
      ∃ γ : Fin 2 → ℝ → ℝ,
        (∀ j, Isometry (γ j)) ∧ (∀ j, γ j 0 = 0) ∧
        ∀ S ζ : ℝ, 0 < ζ → ∀ᶠ i in atTop,
          S ≤ R i ∧ ∀ j, S ≤ lengths (ψ i) j ∧
          ∀ t : Icc (-(lengths (ψ i) j)) (lengths (ψ i) j), |t.val| ≤ S →
            ∀ ht : dist (Q i j t) (base (ψ i)) ≤ R i,
              dist ((f i).toFun ⟨Q i j t, ht⟩) (γ j t.val) < ζ := by
  obtain ⟨ψ, R, ε, hψ, hpointed, hR, hε, f, Q, hLip, hbase, halign, hcal, γ, hγ, hγ0, hconv⟩ :=
    source_pointed_convergence.exists_calibrated_lines_of_opposite_radial_isometries
      positiveEnd negativeEnd length_pos lengths_top qPlus qMinus qPlus_isometry qMinus_isometry
      qPlus_zero qMinus_zero qPlus_end qMinus_end excess_limit
  refine ⟨ψ, R, ε, hψ, hpointed, hR, hε, f, Q, hLip, hbase, halign, ?_, γ, hγ, hγ0, hconv⟩
  intro i j t
  have hh := hcal i j t
  exact ⟨le_antisymm hh.2.1 hh.1,
    le_antisymm (by linarith only [hh.2.2.2, excess_zero (ψ i) j]) hh.2.2.1⟩

private theorem pointed_empty_family :
    ∃ (ψ : ℕ → ℕ) (R : ℕ → ℝ), StrictMono ψ ∧
      PointedGHConverges (fun i => base (ψ i)) (0 : ℝ) ∧
      ∀ S : ℝ, ∀ᶠ i in atTop, S ≤ R i := by
  obtain ⟨ψ, R, ε, hψ, hpointed, hR, hε, f, Q, hLip, hbase, halign, hcal, γ, hγ, hγ0, hconv⟩ :=
    source_pointed_convergence.exists_calibrated_lines_of_opposite_radial_isometries
      (ι := Fin 0) (L := fun _ _ => 0)
      (fun _ j => Fin.elim0 j) (fun _ j => Fin.elim0 j)
      (fun _ j => Fin.elim0 j) (fun j => Fin.elim0 j)
      (fun _ j => Fin.elim0 j) (fun _ j => Fin.elim0 j)
      (fun _ j => Fin.elim0 j) (fun _ j => Fin.elim0 j)
      (fun _ j => Fin.elim0 j) (fun _ j => Fin.elim0 j)
      (fun _ j => Fin.elim0 j) (fun _ j => Fin.elim0 j)
      (fun j => Fin.elim0 j)
  refine ⟨ψ, R, hψ, hpointed, ?_⟩
  intro S
  filter_upwards [hconv S 1 (by norm_num)] with i hi
  exact hi.1


end GCRadialEndpointReview

namespace GCRadialEndpointReview

open Set Filter Metric GC.MetricGeometry
open scoped Topology
open DifferentialGeometry.Geometry.Comparison.Toponogov

private theorem same_extracted_family_cross_limits :
    ∃ (Q : ∀ i j, Icc (-(lengths i j)) (lengths i j) → Source i)
      (φ : ℕ → ℕ) (γ : Fin 2 → ℝ → ℝ), StrictMono φ ∧
      (∀ j, Isometry (γ j)) ∧ (∀ j, γ j 0 = 0) ∧ dist (γ 0 2) (γ 1 (-3)) = 5 ∧
      Tendsto (fun i : ℕ => comparisonAngleNegCurvature (1 / ((i : ℝ) + 1)) |(2 : ℝ)| |(-3 : ℝ)|
        (dist (IccExtend (by linarith [length_pos (φ i) 0] : -(lengths (φ i) 0) ≤ lengths (φ i) 0) (Q (φ i) 0) 2)
          (IccExtend (by linarith [length_pos (φ i) 1] : -(lengths (φ i) 1) ≤ lengths (φ i) 1) (Q (φ i) 1) (-3))))
        atTop (𝓝 Real.pi) := by
  obtain ⟨Q, hLip, hbase, halign, hcal, γ, φ, hγ, hγ0, hφ, hconv⟩ := exact_original_radial_family
  have hd := tendsto_dist_IccExtend_of_converging_signed_prefixes
    (fun i j => (length_pos (φ i) j).le) (fun i => Q (φ i))
    (fun i j => hLip (φ i) j) (fun i j => hbase (φ i) j)
    (fun i => approx (φ i)) (errors_zero.comp hφ.tendsto_atTop) γ hconv (0 : Fin 2) 1 2 (-3)
  have hevent : ∀ᶠ i in atTop,
      dist (IccExtend (by linarith [length_pos (φ i) 0] : -(lengths (φ i) 0) ≤ lengths (φ i) 0) (Q (φ i) 0) 2)
        (IccExtend (by linarith [length_pos (φ i) 1] : -(lengths (φ i) 1) ≤ lengths (φ i) 1) (Q (φ i) 1) (-3)) = 5 := by
    filter_upwards [hconv 3 1 (by norm_num)] with i hi
    have h2 : (2 : ℝ) ≤ lengths (φ i) 0 := by linarith [(hi.2 0).1]
    have h3 : (3 : ℝ) ≤ lengths (φ i) 1 := (hi.2 1).1
    rw [IccExtend_of_mem _ _ (show (2 : ℝ) ∈ Icc (-(lengths (φ i) 0)) (lengths (φ i) 0) from ⟨by linarith [length_pos (φ i) 0], h2⟩),
      IccExtend_of_mem _ _ (show (-3 : ℝ) ∈ Icc (-(lengths (φ i) 1)) (lengths (φ i) 1) from ⟨by linarith, by linarith [length_pos (φ i) 1]⟩)]
    rw [(halign (φ i) 0 ⟨2, ⟨by norm_num, h2⟩⟩).1,
      (halign (φ i) 1 ⟨3, ⟨by norm_num, h3⟩⟩).2]
    norm_num [qPlus, qMinus, Subtype.dist_eq, Real.dist_eq]
  have hconst : Tendsto (fun i => dist
      (IccExtend (by linarith [length_pos (φ i) 0] : -(lengths (φ i) 0) ≤ lengths (φ i) 0) (Q (φ i) 0) 2)
      (IccExtend (by linarith [length_pos (φ i) 1] : -(lengths (φ i) 1) ≤ lengths (φ i) 1) (Q (φ i) 1) (-3))) atTop (𝓝 5) :=
    tendsto_const_nhds.congr' (hevent.mono fun i hi => hi.symm)
  have hdist := tendsto_nhds_unique hd hconst
  have ha := tendsto_comparisonAngle_IccExtend_of_converging_signed_prefixes
    (fun i j => (length_pos (φ i) j).le) (fun i => Q (φ i))
    (fun i j => hLip (φ i) j) (fun i j => hbase (φ i) j)
    (fun i => approx (φ i)) (errors_zero.comp hφ.tendsto_atTop) γ hconv
    (κ := fun i => (1 / ((i : ℝ) + 1)))
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    (Eventually.of_forall fun i => by positivity) (0 : Fin 2) 1
    (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (-3 : ℝ) ≠ 0)
  have hangle : comparisonAngleNegCurvature 0 |(2 : ℝ)| |(-3 : ℝ)| (dist (γ 0 2) (γ 1 (-3))) = Real.pi := by
    rw [hdist]
    norm_num only [show |(2 : ℝ)| = 2 by norm_num, show |(-3 : ℝ)| = 3 by norm_num]
    simpa only [show (2 : ℝ) + 3 = 5 by norm_num] using
      comparisonAngleNegCurvature_add (κ := 0) (a := 2) (b := 3) (by norm_num) (by norm_num) (by norm_num)
  rw [hangle] at ha
  exact ⟨Q, φ, γ, hφ, hγ, hγ0, hdist, ha⟩

end GCRadialEndpointReview
namespace GCRadialEndpointReview
#print axioms exact_original_radial_family
#print axioms empty_family
#print axioms source_not_complete
#print axioms source_pointed_convergence
#print axioms pointed_exact_original_radial_family
#print axioms pointed_empty_family
#print axioms same_extracted_family_cross_limits
end GCRadialEndpointReview
#print axioms GC.MetricGeometry.exists_calibrated_lines_of_opposite_radial_isometries
#print axioms GC.MetricGeometry.PointedGHConverges.exists_calibrated_lines_of_opposite_radial_isometries
#print axioms GC.MetricGeometry.PointedBallApprox.tendsto_dist_of_tendsto_images
#print axioms GC.MetricGeometry.tendsto_dist_IccExtend_of_converging_signed_prefixes
#print axioms GC.MetricGeometry.tendsto_comparisonAngle_IccExtend_of_converging_signed_prefixes

#lint- only unusedArguments simpNF synTaut
```
