# Full AC85–86 independent acceptance

Three public theorems in two leaves add three owned declarations. The355-module gate checks1624 declarations in3190 jobs. All new transitive closures use only propext, Classical.choice and Quot.sound. Source-copy and accepted-import regression lint is silent; nine reports cover all three production theorems and six regression assertions. Declaration kinds were inspected; defLemma is unavailable. Earlier mathematical leaves are unchanged. The inherited AreaUpperBarrier warning is outside these closures. The separate blueprint static audit passes. No migrated-root/PDF/Overleaf build or human approval is claimed.

Root and source_review independently read the full AC85 proof and domains; a separate agent also compiled it. AC86's entire original-input assembly was independently read by root and source_review. The regressions were produced independently and all bodies read by root. Final tests import the canonical leaves. Production imports are targeted.

AC85 fixes ONE ultrafilter refining atTop for all NNReal parameters and all target points. Coverage chooses actual lifts in original closed-ball domains; their images and radial/interpoint distances converge. For each parameter/point, radial images eventually lie in the original map domain and in a fixed compact target ball. Limits along the SAME ultrafilter pass zero, one and the full two-parameter distance law. No source completeness or compactness is used, and no independent rescaling isometries replace radial maps. This alternate proof route is explicitly documented against the blueprint's countable diagonal.

The actual incomplete dense union of Euclidean rays is proved incomplete through its missing vertical point(0,1). Its radial maps and inclusion PBAs with own coverage are constructed, and the original pointed convergence supplies full cone data on the SAME Euclidean plane. AC86 is tested from actual constant real-cone input centered3 with bound n2: the SAME produced target is isometric to the real line/dimension1 with actual radial points. Actual singleton input with n1 yields the SAME singleton/dimension0 target and constant maps. These demonstrate a loose dimension bound and the degenerate case; they do not claim actual sourcedimension drop.

AC86 invokes the accepted original-geometry extraction with kappa_i=0 and radii i+1, then applies85 to the SAME returned convergence. All completeness, properness, dimension, global comparison, segment, strong-side and exact-net outputs remain. Full85–86 are proved;83 convention equivalence and87 are separate. Blueprint207 and migration interfaces are unchanged.

```lean
import DifferentialGeometry.Geometry.Metric.Approximation.NonnegativeConeCompactness
import DifferentialGeometry.Geometry.Metric.Approximation.PointedIsometry
import DifferentialGeometry.Topology.MetricSpace.SegmentCurves
import DifferentialGeometry.Geometry.Comparison.OppositeAngleExcess
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

set_option autoImplicit false

namespace GCAC85Review

open GC.MetricGeometry Set Metric Filter
open scoped NNReal Topology

private abbrev Plane := EuclideanSpace ℝ (Fin 2)
private noncomputable def v (a b : ℝ) : Plane := WithLp.toLp 2 ![a, b]
private def rays : Set Plane := {x | x 0 ≠ 0 ∨ x 1 = 0}
private abbrev Source := rays
private noncomputable def apex : Source := ⟨0, Or.inr rfl⟩

private theorem vector_eta (x : Plane) : v (x 0) (x 1) = x := by
  ext i
  fin_cases i <;> rfl

private theorem horizontal_dist (a b c : ℝ) : dist (v a c) (v b c) = |a - b| := by
  apply (sq_eq_sq₀ dist_nonneg (abs_nonneg _)).mp
  simp only [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two, v,
    Real.dist_eq, sq_abs]
  simp

private noncomputable def sourceCone : RadialConeData apex where
  map t x := ⟨(t : ℝ) • x.val, by
    by_cases ht : t = 0
    · subst t
      right
      simp
    · rcases x.property with hx | hx
      · left
        change (t : ℝ) * x.val 0 ≠ 0
        exact mul_ne_zero (by exact_mod_cast ht) hx
      · right
        change (t : ℝ) * x.val 1 = 0
        rw [hx, mul_zero]⟩
  map_zero x := by apply Subtype.ext; simp [apex]
  map_one x := by apply Subtype.ext; simp
  dist_sq s t x y := by
    simp only [Subtype.dist_eq, radialConeKernel, apex, EuclideanSpace.dist_sq_eq,
      Fin.sum_univ_two, PiLp.smul_apply, PiLp.zero_apply, smul_eq_mul, Real.dist_eq, sq_abs]
    ring

private noncomputable def inclusionApprox {R ε : ℝ} (hε : 0 < ε) (hR : ε < R) :
    PointedBallApprox apex (0 : Plane) R ε where
  error_pos := hε
  error_lt_radius := hR
  toFun x := x.val.val
  basepoint := rfl
  distortion x y := by
    change |dist x.val.val y.val.val - dist x.val.val y.val.val| < ε
    simpa only [sub_self, abs_zero] using hε
  coverage y hy := by
    by_cases hy0 : y 0 = 0
    · let z : Source := ⟨v (ε / 2) (y 1), Or.inl (by change ε / 2 ≠ 0; positivity)⟩
      have hdist : dist y z.val = ε / 2 := by
        have he : y = v 0 (y 1) := by rw [← hy0]; exact (vector_eta y).symm
        rw [he]
        change dist (v 0 (y 1)) (v (ε / 2) (y 1)) = ε / 2
        rw [horizontal_dist]
        rw [zero_sub, abs_neg, abs_of_pos (by positivity : 0 < ε / 2)]
      have hz : dist z apex ≤ R := by
        have hh := dist_triangle z.val y (0 : Plane)
        rw [dist_comm z.val y, hdist] at hh
        change dist z.val (0 : Plane) ≤ R
        linarith
      exact ⟨⟨z, hz⟩, by simpa only [hdist] using (by linarith : ε / 2 < ε)⟩
    · let z : Source := ⟨y, Or.inl hy0⟩
      refine ⟨⟨z, ?_⟩, ?_⟩
      · change dist y (0 : Plane) ≤ R
        linarith
      · change dist y y < ε
        simpa only [dist_self] using hε

private theorem source_not_complete : ¬ CompleteSpace Source := by
  intro h
  let := h
  have hc : IsClosed rays := by
    simpa only [Subtype.range_val] using
      (isometry_subtype_coe (s := rays)).isUniformInducing.isComplete_range.isClosed
  have hcl : v 0 1 ∈ closure rays := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    refine ⟨v (ε / 2) 1, Or.inl (by change ε / 2 ≠ 0; positivity), ?_⟩
    rw [horizontal_dist]
    rw [zero_sub, abs_neg, abs_of_pos (by positivity : 0 < ε / 2)]
    linarith
  have hm := hc.closure_subset hcl
  change (0 : ℝ) ≠ 0 ∨ (1 : ℝ) = 0 at hm
  norm_num at hm

private theorem original_pointed_convergence :
    PointedGHConverges (fun _ : ℕ => apex) (0 : Plane) :=
  ⟨inferInstance, fun R ε hε hR => Eventually.of_forall (fun _ => ⟨inclusionApprox (R := R) (ε := ε) hε hR⟩)⟩

private theorem incomplete_cones_converge_to_same_plane_cone :
    Nonempty (RadialConeData (0 : Plane)) :=
  original_pointed_convergence.nonempty_radialConeData (fun _ => sourceCone)

private theorem same_limit_has_full_two_parameter_radial_identity :
    ∃ H : RadialConeData (0 : Plane),
      ∀ (s t : ℝ≥0) (x y : Plane),
        dist (H.map s x) (H.map t y) ^ 2 =
          (s : ℝ) ^ 2 * dist 0 x ^ 2 + (t : ℝ) ^ 2 * dist 0 y ^ 2 -
            2 * (s : ℝ) * (t : ℝ) * radialConeKernel 0 x y := by
  obtain ⟨H⟩ := incomplete_cones_converge_to_same_plane_cone
  exact ⟨H, H.dist_sq⟩

#print axioms source_not_complete
#print axioms original_pointed_convergence
#print axioms incomplete_cones_converge_to_same_plane_cone
#print axioms same_limit_has_full_two_parameter_radial_identity

end GCAC85Review

#lint- only unusedArguments simpNF synTaut

open Set Metric Filter GC.MetricGeometry
open scoped Topology NNReal
open DifferentialGeometry.Geometry.Comparison.Toponogov

namespace GCNonnegativeConeCompactnessReview

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

private noncomputable def realCone (p : ℝ) : RadialConeData p where
  map t x := p + (t : ℝ) * (x - p)
  map_zero x := by simp
  map_one x := by simp
  dist_sq s t x y := by
    simp only [radialConeKernel, Real.dist_eq, sq_abs]
    ring

theorem actual_real_cone_model_limit :
    ∃ (Y : Type) (m : MetricSpace Y), letI := m
      ∃ (q : Y) (φ : ℕ → ℕ) (H : RadialConeData q), StrictMono φ ∧
        CompleteSpace Y ∧ ProperSpace Y ∧
        PointedGHConverges (fun _ : ℕ => (3 : ℝ)) q ∧
        dimH (univ : Set Y) = 1 ∧ fourPointComparison 0 (univ : Set Y) ∧
        ∃ e : ℝ ≃ᵢ Y, e 3 = q ∧ ∀ t : ℝ≥0, dist q (H.map t (e 4)) = t := by
  obtain ⟨Y, m, q, φ, hφ, hcomplete, hproper, hconv, hcone, hdim, hcomp,
      _hsegments, _hside, _hnets⟩ := exists_pointed_cone_limit_of_nonnegative_geometry
    (fun _ : ℕ => (3 : ℝ)) (n := 2) (by norm_num)
    (fun _ => arbitrarily_short_curves_of_metric_segments real_segments)
    (fun _ => by rw [Real.dimH_univ]; norm_num)
    (fun _ => real_comparison le_rfl) (fun _ => realCone 3)
  let := m
  let := hproper
  obtain ⟨H⟩ := hcone
  obtain ⟨e, he⟩ := (PointedGHConverges.const (3 : ℝ)).exists_isometryEquiv hconv
  refine ⟨Y, m, q, φ, H, hφ, hcomplete, hproper, hconv, ?_, hcomp, e, he, ?_⟩
  · rw [← e.dimH_univ]
    exact Real.dimH_univ
  · intro t
    rw [H.dist_apex, ← he, e.dist_eq]
    norm_num [Real.dist_eq]

private abbrev Point := PUnit.{1}
private noncomputable def pointCone : RadialConeData (PUnit.unit : Point) where
  map _ _ := PUnit.unit
  map_zero _ := rfl
  map_one _ := Subsingleton.elim _ _
  dist_sq _ _ _ _ := by simp [radialConeKernel, Subsingleton.elim _ (PUnit.unit : Point)]

private theorem point_segments (x y : Point) :
    ∃ f : unitInterval → Point, Continuous f ∧ f 0 = x ∧ f 1 = y ∧
      ∀ s t, dist (f s) (f t) = dist x y * dist s t := by
  have hy : y = x := Subsingleton.elim _ _
  subst y
  refine ⟨fun _ => x, continuous_const, rfl, rfl, ?_⟩
  intro s t
  simp only [dist_self, zero_mul]

theorem actual_singleton_cone_model_limit :
    ∃ (Y : Type) (m : MetricSpace Y), letI := m
      ∃ (q : Y) (φ : ℕ → ℕ) (H : RadialConeData q), StrictMono φ ∧
        CompleteSpace Y ∧ ProperSpace Y ∧
        PointedGHConverges (fun _ : ℕ => (PUnit.unit : Point)) q ∧
        dimH (univ : Set Y) = 0 ∧ Subsingleton Y ∧
        ∀ t y, H.map t y = q := by
  have hd : dimH (univ : Set Point) = 0 :=
    dimH_subsingleton (fun _ _ _ _ => Subsingleton.elim _ _)
  have hcomp : fourPointComparison 0 (univ : Set Point) := by
    intro p _ a _ b _ c _ ha _ _
    exact (ha (Subsingleton.elim _ _)).elim
  obtain ⟨Y, m, q, φ, hφ, hcomplete, hproper, hconv, hcone, _hdim, _hcomp,
      _hsegments, _hside, _hnets⟩ := exists_pointed_cone_limit_of_nonnegative_geometry
    (fun _ : ℕ => (PUnit.unit : Point)) (n := 1) (by norm_num)
    (fun _ => arbitrarily_short_curves_of_metric_segments point_segments)
    (fun _ => by rw [hd]; positivity) (fun _ => hcomp) (fun _ => pointCone)
  let := m
  let := hproper
  obtain ⟨H⟩ := hcone
  obtain ⟨e, _he⟩ := (PointedGHConverges.const (PUnit.unit : Point)).exists_isometryEquiv hconv
  have hsub : Subsingleton Y := ⟨fun a b => e.symm.injective (Subsingleton.elim _ _)⟩
  let := hsub
  exact ⟨Y, m, q, φ, H, hφ, hcomplete, hproper, hconv,
    dimH_subsingleton (fun _ _ _ _ => Subsingleton.elim _ _), hsub,
    fun _ _ => Subsingleton.elim _ _⟩

end GCNonnegativeConeCompactnessReview

#print axioms GC.MetricGeometry.nonempty_radialConeData_of_pointed_approximations
#print axioms GC.MetricGeometry.PointedGHConverges.nonempty_radialConeData
#print axioms GC.MetricGeometry.exists_pointed_cone_limit_of_nonnegative_geometry
#print axioms GCNonnegativeConeCompactnessReview.actual_real_cone_model_limit
#print axioms GCNonnegativeConeCompactnessReview.actual_singleton_cone_model_limit
#lint- only unusedArguments simpNF synTaut
```
