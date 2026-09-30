# Compiled self-review: one finite-family subsequence of actual isometries

One public theorem adds one owned declaration. The 281-module gate checks 1315
owned declarations (3116 jobs), with transitive axiom closures limited to propext,
Classical.choice and Quot.sound. Source-copy unusedArguments, simpNF and synTaut
linters are silent. Declaration kind was manually inspected; defLemma is unavailable.
Earlier mathematical leaves are unchanged. The inherited AreaUpperBarrier warning
is outside these closures. Static audit passes. No full migrated root, fresh
blueprint PDF/Overleaf build, human or delegated review is claimed.

The compiled driver uses both coordinate axes of the actual L2 Euclidean plane,
indexed by Fin2. Their orientations alternate with the source index. The driver
proves that each map is an isometry fixing the origin, applies the full finite-family
extraction theorem, and retains ONE strictly increasing subsequence with uniform
control of BOTH maps on every fixed real parameter ball. It separately proves
each original axis map is not onto the plane, and checks that the even/odd images
of parameter1 on the first axis are the distinct points(1,0) and(-1,0). Thus
coverage and full-sequence alignment cannot be silently substituted for the actual
conclusion. The theorem axiom report is standard and the driver compiles silently.

Statement audit checks the actual supplied maps, arbitrary finite indexing type,
fixed basepoint, eventual distortion on each fixed parameter ball, common scalar
error tending to zero, actual target-valued isometries and one ordinary strict
subsequence. Uniformity is simultaneous over all family members and all points of
each fixed ball. Map continuity, target coverage and global error control are not
assumed. The proof shares one filter, uses actual compact finite nets, then extracts
one sequence satisfying every integer-ball/reciprocal-accuracy condition. Properness
belongs to the parameter domain and target; original varying source spaces are not
part of this theorem. Their prefix-image adapter remains the next AC59 obligation.

```lean
import DifferentialGeometry.Topology.MetricSpace.FiniteFamilyIsometry
import DifferentialGeometry.Geometry.Metric.Approximation.ProductApproximation
import Mathlib.Tactic

open Set Metric Filter GC.MetricGeometry
open scoped Topology

private abbrev Plane := WithLp 2 (ℝ × ℝ)
private def origin : Plane := WithLp.toLp 2 (0, 0)
private def axis (j : Fin 2) (t : ℝ) : Plane :=
  if j = 0 then WithLp.toLp 2 (t, 0) else WithLp.toLp 2 (0, t)
private theorem axis_iso (j : Fin 2) : Isometry (axis j) := by
  change Isometry (fun t : ℝ => if j = 0 then WithLp.toLp 2 (t, (0 : ℝ)) else WithLp.toLp 2 (0, t))
  by_cases hj : j = 0
  · simpa only [ite_eq_left hj] using WithLp.isometry_prodMk_right (E := ℝ) (0 : ℝ)
  · simpa only [ite_eq_right hj] using WithLp.isometry_prodMk_left (Y := ℝ) (0 : ℝ)
private theorem axis_zero (j : Fin 2) : axis j 0 = origin := by
  by_cases hj : j = 0 <;> simp [axis, origin, hj]
private def maps (n : ℕ) (j : Fin 2) (t : ℝ) : Plane :=
  if Even n then axis j t else axis j (-t)
private theorem maps_iso (n : ℕ) (j : Fin 2) : Isometry (maps n j) := by
  by_cases hn : Even n
  · change Isometry (fun t => if Even n then axis j t else axis j (-t))
    simpa only [ite_eq_left hn] using axis_iso j
  · change Isometry (fun t => if Even n then axis j t else axis j (-t))
    simpa only [ite_eq_right hn, Function.comp_def] using (axis_iso j).comp isometry_neg
private theorem maps_zero (n : ℕ) (j : Fin 2) : maps n j 0 = origin := by
  by_cases hn : Even n <;> simp only [maps, hn, ↓reduceIte, neg_zero, axis_zero]

example : ∃ (F : Fin 2 → ℝ → Plane) (φ : ℕ → ℕ),
    (∀ j, Isometry (F j)) ∧ (∀ j, F j 0 = origin) ∧ StrictMono φ ∧
    ∀ S η : ℝ, 0 < η → ∀ᶠ i in atTop,
      ∀ j x, |x| ≤ S → dist (maps (φ i) j x) (F j x) < η := by
  have hd : ∀ S : ℝ, ∀ᶠ n in atTop, ∀ j, ∀ s t : ℝ,
      dist s 0 ≤ S → dist t 0 ≤ S → |dist (maps n j s) (maps n j t) - dist s t| ≤ (0 : ℝ) := by
    intro S
    exact Eventually.of_forall (fun n j s t _ _ => by rw [(maps_iso n j).dist_eq, sub_self, abs_zero])
  simpa only [Real.dist_eq, sub_zero] using exists_isometry_family_subsequence_of_local_distortion
    maps maps_zero (ε := fun _ => 0) tendsto_const_nhds hd

example (j : Fin 2) : ¬ Function.Surjective (axis j) := by
  intro hs
  obtain ⟨t, ht⟩ := hs (WithLp.toLp 2 (1, 1))
  by_cases hj : j = 0
  · have hh := congrArg WithLp.snd ht
    simp only [axis, ite_eq_left hj] at hh
    change (0 : ℝ) = 1 at hh
    norm_num at hh
  · have hh := congrArg WithLp.fst ht
    simp only [axis, ite_eq_right hj] at hh
    change (0 : ℝ) = 1 at hh
    norm_num at hh

example (n : ℕ) : maps (2*n) 0 1 = WithLp.toLp 2 ((1 : ℝ), 0) ∧
    maps (2*n+1) 0 1 = WithLp.toLp 2 ((-1 : ℝ), 0) := by
  have he : Even (2*n) := ⟨n, by omega⟩
  have ho : ¬ Even (2*n+1) := by rintro ⟨k, hk⟩; omega
  simp [maps, he, ho, axis]

#print axioms GC.MetricGeometry.exists_isometry_family_subsequence_of_local_distortion
```
