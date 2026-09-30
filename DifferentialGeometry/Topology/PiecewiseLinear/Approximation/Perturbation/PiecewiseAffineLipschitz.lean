import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.Analysis.Normed.Module.FiniteDimension

namespace DifferentialGeometry.Topology.Engulfing

open Set Filter Metric
open scoped _root_.Topology NNReal

theorem eventually_dist_le_of_finite_selection
    {X Y ι : Type*} [PseudoMetricSpace X] [MetricSpace Y] [Finite ι]
    {s : Set X} {f : X → Y} {A : ι → X → Y} {L : ℝ≥0}
    (hf : ContinuousOn f s) (hA : ∀ i, LipschitzOnWith L (A i) s)
    (hselect : ∀ x ∈ s, ∃ i, f x = A i x) {x : X} (hx : x ∈ s) :
    ∀ᶠ y in 𝓝[s] x, dist (f y) (f x) ≤ L * dist y x := by
  classical
  have hactive : ∀ᶠ y in 𝓝[s] x, ∀ i, f y = A i y → f x = A i x := by
    apply Filter.eventually_all.mpr
    intro i
    by_cases hi : f x = A i x
    · exact Filter.Eventually.of_forall fun _ _ => hi
    · have hne := ((hf x hx).dist ((hA i).continuousOn x hx)).eventually_ne
        (show dist (f x) (A i x) ≠ 0 from fun h => hi (dist_eq_zero.mp h))
      filter_upwards [hne] with y hy hiy
      exact False.elim (hy (by simp only [hiy, dist_self]))
  filter_upwards [hactive, self_mem_nhdsWithin] with y hy hys
  obtain ⟨i, hi⟩ := hselect y hys
  rw [hi, hy i hi]
  exact (hA i).dist_le_mul y hys x hx

theorem dist_endpoints_le_of_eventually_dist_le
    {Y : Type*} [PseudoMetricSpace Y] {f : ℝ → Y} {C : ℝ}
    (hf : ContinuousOn f (Icc 0 1))
    (hlocal : ∀ t ∈ Ico (0 : ℝ) 1,
      ∀ᶠ u in 𝓝[>] t, dist (f u) (f t) ≤ C * (u - t)) :
    dist (f 1) (f 0) ≤ C := by
  have hbound : ∀ t ∈ Ico (0 : ℝ) 1, ∀ r, C < r →
      ∃ᶠ u in 𝓝[>] t, slope (fun z => dist (f z) (f 0)) t u < r := by
    intro t ht r hr
    apply Filter.Eventually.frequently
    filter_upwards [hlocal t ht, self_mem_nhdsWithin] with u hu hut
    have hpos : 0 < u - t := sub_pos.mpr hut
    apply lt_of_le_of_lt _ hr
    rw [slope_def_field]
    apply (div_le_iff₀ hpos).mpr
    calc
      dist (f u) (f 0) - dist (f t) (f 0) ≤ dist (f u) (f t) := by
        linarith [dist_triangle (f u) (f t) (f 0)]
      _ ≤ C * (u - t) := hu
  have hderiv (t : ℝ) : HasDerivWithinAt (fun z : ℝ => C * z) C (Ici t) t := by
    simpa using ((hasDerivAt_id t).const_mul C).hasDerivWithinAt
  have h := image_le_of_liminf_slope_right_le_deriv_boundary
    (fun t ht => (hf t ht).dist tendsto_const_nhds)
    (show dist (f 0) (f 0) ≤ C * (0 : ℝ) by simp)
    (show ContinuousOn (fun z : ℝ => C * z) (Icc 0 1) by fun_prop)
    (fun t _ => hderiv t) hbound (show (1 : ℝ) ∈ Icc 0 1 by constructor <;> norm_num)
  simpa only [mul_one] using h

variable {E Y ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MetricSpace Y] [Finite ι]

theorem lipschitzOnWith_of_finite_selection
    {s : Set E} (hs : Convex ℝ s) {f : E → Y} {A : ι → E → Y} {L : ℝ≥0}
    (hf : ContinuousOn f s) (hA : ∀ i, LipschitzOnWith L (A i) s)
    (hselect : ∀ x ∈ s, ∃ i, f x = A i x) : LipschitzOnWith L f s := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  let p : ℝ → E := AffineMap.lineMap y x
  have hp : Continuous p := (lipschitzWith_lineMap y x).continuous
  have hps : MapsTo p (Icc 0 1) s := hs.mapsTo_lineMap hy hx
  have hfp : ContinuousOn (f ∘ p) (Icc 0 1) := hf.comp hp.continuousOn hps
  have hAp (i : ι) : LipschitzOnWith (L * nndist y x) ((A i) ∘ p) (Icc 0 1) :=
    (hA i).comp (lipschitzWith_lineMap y x).lipschitzOnWith hps
  have hselp (t : ℝ) (ht : t ∈ Icc 0 1) : ∃ i, (f ∘ p) t = ((A i) ∘ p) t :=
    hselect (p t) (hps ht)
  have hlocal (t : ℝ) (ht : t ∈ Ico 0 1) :
      ∀ᶠ u in 𝓝[>] t, dist ((f ∘ p) u) ((f ∘ p) t) ≤
        (L : ℝ) * dist y x * (u - t) := by
    have h := eventually_dist_le_of_finite_selection hfp hAp hselp
      (Ico_subset_Icc_self ht)
    have h' := h.filter_mono (nhdsWithin_le_of_mem (Icc_mem_nhdsGT_of_mem ht))
    filter_upwards [h', self_mem_nhdsWithin] with u hu hut
    simpa only [NNReal.coe_mul, coe_nndist, Real.dist_eq,
      abs_of_pos (sub_pos.mpr (show t < u from hut))] using hu
  have h := dist_endpoints_le_of_eventually_dist_le hfp hlocal
  simpa only [Function.comp_apply, p, AffineMap.lineMap_apply_one,
    AffineMap.lineMap_apply_zero, dist_comm y x] using h

theorem lipschitzWith_of_finite_selection
    {f : E → Y} {A : ι → E → Y} {L : ℝ≥0}
    (hf : Continuous f) (hA : ∀ i, LipschitzWith L (A i))
    (hselect : ∀ x, ∃ i, f x = A i x) : LipschitzWith L f := by
  have h := lipschitzOnWith_of_finite_selection convex_univ hf.continuousOn
    (fun i => (hA i).lipschitzOnWith) (fun x _ => hselect x)
  exact LipschitzWith.of_dist_le_mul fun x y => h.dist_le_mul x (mem_univ x) y (mem_univ y)

section Affine

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem affineMap_lipschitzWith_of_linear_bound (A : E →ᵃ[ℝ] F) {L : ℝ≥0}
    (hA : ∀ v, ‖A.linear v‖ ≤ L * ‖v‖) : LipschitzWith L A := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hxy : A.linear (x - y) = A x - A y := by
    simpa only [vsub_eq_sub] using A.linearMap_vsub x y
  rw [dist_eq_norm, dist_eq_norm, ← hxy]
  exact hA (x - y)

theorem lipschitzOnWith_of_finite_affine_selection
    {s : Set E} (hs : Convex ℝ s) {f : E → F} {A : ι → E →ᵃ[ℝ] F} {L : ℝ≥0}
    (hf : ContinuousOn f s) (hA : ∀ i v, ‖(A i).linear v‖ ≤ L * ‖v‖)
    (hselect : ∀ x ∈ s, ∃ i, f x = A i x) : LipschitzOnWith L f s :=
  lipschitzOnWith_of_finite_selection hs hf
    (fun i => (affineMap_lipschitzWith_of_linear_bound (A i) (hA i)).lipschitzOnWith) hselect

theorem lipschitzWith_of_finite_affine_selection
    {f : E → F} {A : ι → E →ᵃ[ℝ] F} {L : ℝ≥0}
    (hf : Continuous f) (hA : ∀ i v, ‖(A i).linear v‖ ≤ L * ‖v‖)
    (hselect : ∀ x, ∃ i, f x = A i x) : LipschitzWith L f :=
  lipschitzWith_of_finite_selection hf
    (fun i => affineMap_lipschitzWith_of_linear_bound (A i) (hA i)) hselect

variable [FiniteDimensional ℝ E]

theorem lipschitzOnWith_of_finite_affine_selection_of_opNorm_le
    {s : Set E} (hs : Convex ℝ s) {f : E → F} {A : ι → E →ᵃ[ℝ] F} {L : ℝ≥0}
    (hf : ContinuousOn f s) (hA : ∀ i, ‖(A i).linear.toContinuousLinearMap‖ ≤ L)
    (hselect : ∀ x ∈ s, ∃ i, f x = A i x) : LipschitzOnWith L f s := by
  apply lipschitzOnWith_of_finite_affine_selection hs hf _ hselect
  intro i v
  exact ((A i).linear.toContinuousLinearMap.le_opNorm v).trans
    (mul_le_mul_of_nonneg_right (hA i) (norm_nonneg v))

theorem lipschitzWith_of_finite_affine_selection_of_opNorm_le
    {f : E → F} {A : ι → E →ᵃ[ℝ] F} {L : ℝ≥0}
    (hf : Continuous f) (hA : ∀ i, ‖(A i).linear.toContinuousLinearMap‖ ≤ L)
    (hselect : ∀ x, ∃ i, f x = A i x) : LipschitzWith L f := by
  apply lipschitzWith_of_finite_affine_selection hf _ hselect
  intro i v
  exact ((A i).linear.toContinuousLinearMap.le_opNorm v).trans
    (mul_le_mul_of_nonneg_right (hA i) (norm_nonneg v))

theorem exists_lipschitzOnWith_of_finite_affine_selection
    {s : Set E} (hs : Convex ℝ s) {f : E → F} {A : ι → E →ᵃ[ℝ] F}
    (hf : ContinuousOn f s) (hselect : ∀ x ∈ s, ∃ i, f x = A i x) :
    ∃ L, LipschitzOnWith L f s := by
  classical
  let := Fintype.ofFinite ι
  let L : ℝ≥0 := Finset.univ.sup fun i => ‖(A i).linear.toContinuousLinearMap‖₊
  refine ⟨L, lipschitzOnWith_of_finite_affine_selection_of_opNorm_le hs hf ?_ hselect⟩
  intro i
  exact_mod_cast (Finset.le_sup (f := fun j => ‖(A j).linear.toContinuousLinearMap‖₊)
    (Finset.mem_univ i))

theorem exists_lipschitzWith_of_finite_affine_selection
    {f : E → F} {A : ι → E →ᵃ[ℝ] F}
    (hf : Continuous f) (hselect : ∀ x, ∃ i, f x = A i x) :
    ∃ L, LipschitzWith L f := by
  obtain ⟨L, hL⟩ := exists_lipschitzOnWith_of_finite_affine_selection convex_univ
    hf.continuousOn (fun x _ => hselect x)
  exact ⟨L, LipschitzWith.of_dist_le_mul fun x y =>
    hL.dist_le_mul x (mem_univ x) y (mem_univ y)⟩

end Affine

end DifferentialGeometry.Topology.Engulfing
