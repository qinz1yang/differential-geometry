# Compiled self-review: metric model endpoint and parameter rigidity

Ten public theorems and one definition in three leaves add twelve owned
declarations including a generated declaration. The 256-module gate checks
1204 owned declarations (3090 jobs), with transitive axiom closures limited
to propext, Classical.choice and Quot.sound. Source-copy unusedArguments,
simpNF and synTaut linters are silent. Declaration kinds were manually
inspected; defLemma is unavailable. Earlier mathematical leaves are unchanged.
The inherited AreaUpperBarrier warning is outside these closures. Static
audit passes. No full migrated root, fresh blueprint PDF/Overleaf build,
human or delegated review is claimed.

The independent compiled driver verifies actual boundary/interior points of
the ray and positive segment, both segment endpoints, and the zero-length
segment. It checks no endpoints on every real point and every positive-period
circle point. An actual interval reflection is constructed with its inverse
and ordinary metric; it exchanges endpoints and sends coordinate2 to3 on
[0,5]. The uniform-orientation and pointed-coordinate theorems are applied
to this reflection. An actual isometry from [-2,infinity) to [0,infinity)
is constructed; the interior point0 has height2 under EVERY onto ray chart
on that same source, using the new uniqueness theorem. Actual circle
translations test circumference invariance, and unequal circumferences4/5
and segment lengths4/5 are proved nonisometric. The driver exits zero and
prints all eleven authored declaration axiom reports.

Statement review checks that endpoint is literally the prior triangle-equality
predicate, transported in BOTH directions only by onto isometries. The ray
has exactly one endpoint; an interior height is not moved to zero. Interval
orientation is one GLOBAL choice for all points, not a pointwise disjunction.
Positive lengths are required in rigidity, while the endpoint description
also covers length0. Circle rigidity uses actual antipodal distances and
the quotient norm bound in both directions, with positive periods. No model
classification, curvature or smooth structure is assumed. Pairwise type
exclusion and its assembly with global existence remain next.

```lean
import DifferentialGeometry.Topology.MetricSpace.ModelParameterRigidity
import DifferentialGeometry.Topology.MetricSpace.CircleEndpoint
import Mathlib.Tactic

open Set Metric

example : IsEndpoint (⟨0, by norm_num⟩ : Ici (0 : ℝ)) := (isEndpoint_Ici_iff _).mpr rfl
example : ¬ IsEndpoint (⟨2, by norm_num⟩ : Ici (0 : ℝ)) := by
  rw [isEndpoint_Ici_iff]
  norm_num
example : IsEndpoint (⟨0, by norm_num⟩ : Icc (0 : ℝ) 5) :=
  (isEndpoint_Icc_iff (by norm_num) _).mpr (Or.inl rfl)
example : IsEndpoint (⟨5, by norm_num⟩ : Icc (0 : ℝ) 5) :=
  (isEndpoint_Icc_iff (by norm_num) _).mpr (Or.inr rfl)
example : ¬ IsEndpoint (⟨2, by norm_num⟩ : Icc (0 : ℝ) 5) := by
  rw [isEndpoint_Icc_iff (by norm_num)]
  norm_num
example : IsEndpoint (⟨0, by norm_num⟩ : Icc (0 : ℝ) 0) :=
  (isEndpoint_Icc_iff (by norm_num) _).mpr (Or.inl rfl)
example (p : ℝ) : ¬ IsEndpoint p := not_isEndpoint_real p
example (L : ℝ) (hL : 0 < L) (p : AddCircle L) : ¬ IsEndpoint p := not_isEndpoint_addCircle hL p

private noncomputable def reflection {L : ℝ} : Icc (0 : ℝ) L ≃ᵢ Icc (0 : ℝ) L where
  toFun t := ⟨L - t, by constructor <;> linarith [t.property.1, t.property.2]⟩
  invFun t := ⟨L - t, by constructor <;> linarith [t.property.1, t.property.2]⟩
  left_inv t := Subtype.ext (by dsimp; ring)
  right_inv t := Subtype.ext (by dsimp; ring)
  isometry_toFun := by
    apply Isometry.of_dist_eq
    intro a b
    change |L - (a : ℝ) - (L - (b : ℝ))| = |(a : ℝ) - b|
    rw [show L - (a : ℝ) - (L - (b : ℝ)) = -((a : ℝ) - b) by ring, abs_neg]

example : IsEndpoint (reflection (⟨0, by norm_num⟩ : Icc (0 : ℝ) 5)) :=
  (isEndpoint_isometryEquiv_iff reflection _).mpr ((isEndpoint_Icc_iff (by norm_num) _).mpr (Or.inl rfl))
example : ((reflection (⟨2, by norm_num⟩ : Icc (0 : ℝ) 5)) : ℝ) = 3 := by
  change (5 : ℝ) - 2 = 3
  norm_num
example : (5 : ℝ) = 5 ∧
    ((∀ t : Icc (0 : ℝ) 5, (reflection t : ℝ) = t) ∨
      (∀ t : Icc (0 : ℝ) 5, (reflection t : ℝ) = 5 - t)) :=
  reflection.Icc_length_and_coordinates (by norm_num) (by norm_num)
example : (5 : ℝ) = 5 ∧
    ((reflection (⟨2, by norm_num⟩ : Icc (0 : ℝ) 5) : ℝ) = 2 ∨
      (reflection (⟨2, by norm_num⟩ : Icc (0 : ℝ) 5) : ℝ) = 5 - 2) :=
  IsometryEquiv.Icc_pointed_coordinates (by norm_num) (by norm_num)
    (IsometryEquiv.refl _) reflection ⟨2, by norm_num⟩

private noncomputable def shiftedRay : Ici (-2 : ℝ) ≃ᵢ Ici (0 : ℝ) where
  toFun t := ⟨t + 2, by change 0 ≤ (t : ℝ) + 2; have ht : -2 ≤ (t : ℝ) := t.property; linarith⟩
  invFun t := ⟨t - 2, by change -2 ≤ (t : ℝ) - 2; have ht : 0 ≤ (t : ℝ) := t.property; linarith⟩
  left_inv t := Subtype.ext (by dsimp; ring)
  right_inv t := Subtype.ext (by dsimp; ring)
  isometry_toFun := by
    apply Isometry.of_dist_eq
    intro a b
    change |(a : ℝ) + 2 - ((b : ℝ) + 2)| = |(a : ℝ) - b|
    congr 1
    ring
example (e : Ici (0 : ℝ) ≃ᵢ Ici (0 : ℝ)) : e ⟨2, by norm_num⟩ = ⟨2, by norm_num⟩ :=
  e.apply_Ici_zero _
example (f : Ici (-2 : ℝ) ≃ᵢ Ici (0 : ℝ)) :
    (f ⟨0, by norm_num⟩ : ℝ) = 2 := by
  have h := shiftedRay.Ici_pointed_height_eq f ⟨0, by norm_num⟩
  change (0 : ℝ) + 2 = (f ⟨0, by norm_num⟩ : ℝ) at h
  linarith
example (p : AddCircle (4 : ℝ)) : (4 : ℝ) = 4 :=
  (IsometryEquiv.addRight p).addCircle_period_eq (by norm_num) (by norm_num)
example : ¬ Nonempty (AddCircle (4 : ℝ) ≃ᵢ AddCircle (5 : ℝ)) := by
  rintro ⟨e⟩
  have h := e.addCircle_period_eq (by norm_num) (by norm_num)
  norm_num at h
example : ¬ Nonempty (Icc (0 : ℝ) 4 ≃ᵢ Icc (0 : ℝ) 5) := by
  rintro ⟨e⟩
  have h := (e.Icc_length_and_coordinates (by norm_num) (by norm_num)).1
  norm_num at h

#print axioms Metric.IsEndpoint
#print axioms Metric.isEndpoint_isometryEquiv_iff
#print axioms Metric.not_isEndpoint_real
#print axioms Metric.isEndpoint_Ici_iff
#print axioms Metric.isEndpoint_Icc_iff
#print axioms Metric.not_isEndpoint_addCircle
#print axioms IsometryEquiv.apply_Ici_zero
#print axioms IsometryEquiv.Icc_length_and_coordinates
#print axioms IsometryEquiv.addCircle_period_eq
#print axioms IsometryEquiv.Ici_pointed_height_eq
#print axioms IsometryEquiv.Icc_pointed_coordinates
```
