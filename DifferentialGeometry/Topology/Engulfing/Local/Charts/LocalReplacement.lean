import DifferentialGeometry.Topology.PiecewiseLinear.Approximation.RelativeApproximation
import Mathlib.Topology.UrysohnsLemma
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.OpenPartialHomeomorph.Defs

namespace DifferentialGeometry.Topology.Engulfing

open Set Metric _root_.Geometry
open scoped _root_.Topology ContinuousMap

section Blend

variable {X F : Type*} [TopologicalSpace X] [NormedAddCommGroup F] [NormedSpace ℝ F]

def cutoffBlend (g h : C(X, F)) (χ : C(X, ℝ)) : C(X, F) :=
  ⟨fun x => g x + χ x • (h x - g x), by fun_prop⟩

@[simp]
theorem cutoffBlend_apply (g h : C(X, F)) (χ : C(X, ℝ)) (x : X) :
    cutoffBlend g h χ x = g x + χ x • (h x - g x) := rfl

theorem cutoffBlend_eq_left (g h : C(X, F)) (χ : C(X, ℝ)) {x : X} (hx : χ x = 0) :
    cutoffBlend g h χ x = g x := by simp [hx]

theorem cutoffBlend_eq_right (g h : C(X, F)) (χ : C(X, ℝ)) {x : X} (hx : χ x = 1) :
    cutoffBlend g h χ x = h x := by simp [hx]

theorem cutoffBlend_eq_of_eq (g h : C(X, F)) (χ : C(X, ℝ)) {x : X} (hx : h x = g x) :
    cutoffBlend g h χ x = g x := by simp [hx]

theorem cutoffBlend_norm_sub_le (g h : C(X, F)) (χ : C(X, ℝ)) {x : X}
    (hx : χ x ∈ Icc (0 : ℝ) 1) : ‖cutoffBlend g h χ x - g x‖ ≤ ‖h x - g x‖ := by
  rw [cutoffBlend_apply, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hx.1]
  exact mul_le_of_le_one_left (norm_nonneg _) hx.2

theorem cutoffBlend_mem_convex (g h : C(X, F)) (χ : C(X, ℝ)) {S : Set F}
    (hS : Convex ℝ S) {x : X} (hx : χ x ∈ Icc (0 : ℝ) 1)
    (hg : g x ∈ S) (hh : h x ∈ S) : cutoffBlend g h χ x ∈ S := by
  have h := hS hg hh (sub_nonneg.mpr hx.2) hx.1 (sub_add_cancel 1 (χ x))
  convert h using 1
  simp only [cutoffBlend_apply, sub_smul, one_smul, smul_sub]
  abel

theorem exists_local_cutoff_blend [NormalSpace X] (g h : C(X, F))
    {A U : Set X} (hA : IsClosed A) (hU : IsOpen U) (hAU : A ⊆ U) :
    ∃ f : C(X, F), (∀ x ∈ A, f x = h x) ∧ (∀ x ∉ U, f x = g x) ∧
      (∀ x, h x = g x → f x = g x) ∧
      (∀ x, ‖f x - g x‖ ≤ ‖h x - g x‖) ∧
      (∀ S : Set F, Convex ℝ S → ∀ x, g x ∈ S → h x ∈ S → f x ∈ S) := by
  obtain ⟨χ, hχ0, hχ1, hχrange⟩ := exists_continuous_zero_one_of_isClosed
    hU.isClosed_compl hA (disjoint_left.mpr (fun _ hx hxa => hx (hAU hxa)))
  exact ⟨cutoffBlend g h χ, fun x hx => cutoffBlend_eq_right g h χ (hχ1 hx),
    fun x hx => cutoffBlend_eq_left g h χ (hχ0 hx),
    fun x hx => cutoffBlend_eq_of_eq g h χ hx,
    fun x => cutoffBlend_norm_sub_le g h χ (hχrange x),
    fun S hS x hg hh => cutoffBlend_mem_convex g h χ hS (hχrange x) hg hh⟩

theorem exists_local_cutoff_blend_neighborhood [NormalSpace X] (g h : C(X, F))
    {A U : Set X} (hA : IsClosed A) (hU : IsOpen U) (hAU : A ⊆ U) :
    ∃ (V : Set X) (f : C(X, F)), IsOpen V ∧ A ⊆ V ∧ closure V ⊆ U ∧
      (∀ x ∈ closure V, f x = h x) ∧ (∀ x ∉ U, f x = g x) ∧
      (∀ x, h x = g x → f x = g x) ∧ (∀ x, ‖f x - g x‖ ≤ ‖h x - g x‖) := by
  obtain ⟨V, hV, hAV, hVU⟩ := normal_exists_closure_subset hA hU hAU
  obtain ⟨f, hinner, houter, hfix, hnear, -⟩ :=
    exists_local_cutoff_blend g h isClosed_closure hU hVU
  exact ⟨V, f, hV, hAV, hVU, hinner, houter, hfix, hnear⟩

end Blend

theorem exists_subdivision_faces_near_compact
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) {A U : Set E}
    (hA : IsCompact A) (hU : IsOpen U) (hAU : A ⊆ U) :
    ∃ L : SimplicialComplex ℝ E, L.faces.Finite ∧ L.space = K.space ∧
      simplicialRefines L K ∧ ∀ s ∈ L.faces,
        (convexHull ℝ (s : Set E) ∩ A).Nonempty → convexHull ℝ (s : Set E) ⊆ U := by
  classical
  obtain ⟨δ, hδ, hδU⟩ := hA.exists_thickening_subset_open hU hAU
  obtain ⟨L, hL, heq, href, hmesh, -⟩ := exists_fine_subdivision K hK hδ
  refine ⟨L, hL, heq, href, ?_⟩
  intro s hs hmeet x hx
  obtain ⟨a, has, haA⟩ := hmeet
  apply hδU
  apply mem_thickening_iff.mpr
  refine ⟨a, haA, ?_⟩
  exact (dist_le_diam_of_mem (s.finite_toSet.isCompact_convexHull ℝ).isBounded hx has).trans_lt
    (hmesh s hs)

theorem exists_subdivision_with_cutoff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) {A U : Set E}
    (hA : IsCompact A) (hU : IsOpen U) (hAU : A ⊆ U) :
    ∃ L : SimplicialComplex ℝ E, L.faces.Finite ∧ L.space = K.space ∧
      simplicialRefines L K ∧ ∃ χ : C(E, ℝ),
        (∀ x, χ x ∈ Icc (0 : ℝ) 1) ∧ (∀ x ∉ U, χ x = 0) ∧
        ∀ s ∈ L.faces, (convexHull ℝ (s : Set E) ∩ A).Nonempty →
          ∀ x ∈ convexHull ℝ (s : Set E), χ x = 1 := by
  obtain ⟨V, hV, hAV, hVU⟩ := normal_exists_closure_subset hA.isClosed hU hAU
  obtain ⟨χ, hχ0, hχ1, hχrange⟩ := exists_continuous_zero_one_of_isClosed
    hU.isClosed_compl isClosed_closure
    (disjoint_left.mpr (fun _ hx hxV => hx (hVU hxV)))
  obtain ⟨L, hL, heq, href, hfaces⟩ := exists_subdivision_faces_near_compact K hK hA hV hAV
  exact ⟨L, hL, heq, href, χ, hχrange, fun x hx => hχ0 hx,
    fun s hs hmeet x hx => hχ1 (subset_closure (hfaces s hs hmeet hx))⟩

theorem exists_local_replacement_subdivision
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) {A U : Set E}
    (hA : IsCompact A) (hU : IsOpen U) (hAU : A ⊆ U) :
    ∃ L : SimplicialComplex ℝ E, L.faces.Finite ∧ L.space = K.space ∧
      simplicialRefines L K ∧ ∀ g h : C(L.space, F), ∃ f : C(L.space, F),
        (∀ x : L.space, x.1 ∉ U → f x = g x) ∧
        (∀ x, h x = g x → f x = g x) ∧ (∀ x, ‖f x - g x‖ ≤ ‖h x - g x‖) ∧
        (∀ s ∈ L.faces, (convexHull ℝ (s : Set E) ∩ A).Nonempty →
          ∀ x : L.space, x.1 ∈ convexHull ℝ (s : Set E) → f x = h x) := by
  obtain ⟨L, hL, heq, href, χ, hχrange, hχ0, hχ1⟩ :=
    exists_subdivision_with_cutoff K hK hA hU hAU
  refine ⟨L, hL, heq, href, ?_⟩
  intro g h
  let χL : C(L.space, ℝ) := χ.comp ⟨Subtype.val, continuous_subtype_val⟩
  refine ⟨cutoffBlend g h χL, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact cutoffBlend_eq_left g h χL (hχ0 x hx)
  · intro x hx
    exact cutoffBlend_eq_of_eq g h χL hx
  · intro x
    exact cutoffBlend_norm_sub_le g h χL (hχrange x)
  · intro s hs hmeet x hx
    exact cutoffBlend_eq_right g h χL (hχ1 s hs hmeet x hx)

section ClosedReplacement

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

theorem exists_continuous_replacement_on_closed {A : Set X} (hA : IsClosed A)
    (g : C(X, Y)) (f : C(A, Y))
    (hboundary : ∀ x : A, x.1 ∈ frontier A → f x = g x) :
    ∃ G : C(X, Y), (∀ x : A, G x = f x) ∧
      (∀ x ∉ interior A, G x = g x) := by
  classical
  let G : X → Y := fun x => if hx : x ∈ A then f ⟨x, hx⟩ else g x
  have hGeq (x : A) : G x = f x := dite_eq_left x.2
  have hGOn : ContinuousOn G A := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    exact f.continuous.congr (fun x => (hGeq x).symm)
  have hGout (x : X) (hx : x ∉ interior A) : G x = g x := by
    by_cases hxA : x ∈ A
    · exact (hGeq ⟨x, hxA⟩).trans (hboundary ⟨x, hxA⟩ ⟨subset_closure hxA, hx⟩)
    · exact dite_eq_right hxA
  have hcont : Continuous (A.piecewise G g) := continuous_piecewise
    (fun x hx => hGout x hx.2) (by simpa only [hA.closure_eq] using hGOn)
    g.continuous.continuousOn
  have heq : A.piecewise G g = G := by
    funext x
    by_cases hx : x ∈ A
    · exact piecewise_eq_of_mem _ _ _ hx
    · rw [piecewise_eq_of_notMem _ _ _ hx, hGout x (fun hi => hx (interior_subset hi))]
  exact ⟨⟨G, heq ▸ hcont⟩, hGeq, hGout⟩

variable {F : Type*} [TopologicalSpace F]

theorem exists_chart_replacement_on_closed (e : OpenPartialHomeomorph Y F)
    {A : Set X} (hA : IsClosed A) (g : C(X, Y)) (f : C(A, F))
    (hgsource : ∀ x : A, g x ∈ e.source) (hftarget : ∀ x, f x ∈ e.target)
    (hboundary : ∀ x : A, x.1 ∈ frontier A → f x = e (g x)) :
    ∃ G : C(X, Y), (∀ x : A, G x = e.symm (f x)) ∧
      (∀ x ∉ interior A, G x = g x) ∧
      (∀ x : A, G x ∈ e.source ∧ e (G x) = f x) ∧
      (∀ x : A, f x = e (g x) → G x = g x) := by
  let f' : C(A, Y) := ⟨fun x => e.symm (f x),
    e.continuousOn_symm.comp_continuous f.continuous hftarget⟩
  have hboundary' (x : A) (hx : x.1 ∈ frontier A) : f' x = g x := by
    change e.symm (f x) = g x
    rw [hboundary x hx, e.left_inv (hgsource x)]
  obtain ⟨G, hG, hGout⟩ := exists_continuous_replacement_on_closed hA g f' hboundary'
  refine ⟨G, hG, hGout, ?_, ?_⟩
  · intro x
    rw [hG x]
    exact ⟨e.map_target (hftarget x), e.right_inv (hftarget x)⟩
  · intro x hx
    rw [hG x]
    change e.symm (f x) = g x
    rw [hx, e.left_inv (hgsource x)]

end ClosedReplacement

section ChartBlend

variable {X M F : Type*} [TopologicalSpace X] [NormalSpace X] [TopologicalSpace M]
    [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem exists_local_chart_blend (e : OpenPartialHomeomorph M F)
    {A B U : Set X} (hA : IsClosed A) (hB : IsClosed B) (hU : IsOpen U)
    (hBU : B ⊆ U) (hUA : U ⊆ interior A)
    (g : C(X, M)) (f : C(A, F)) (hgsource : ∀ x : A, g x ∈ e.source)
    {S : Set F} (hS : Convex ℝ S) (hStarget : S ⊆ e.target)
    (hgrange : ∀ x : A, e (g x) ∈ S) (hfrange : ∀ x, f x ∈ S) :
    ∃ G : C(X, M),
      (∀ x : A, x.1 ∈ B → G x = e.symm (f x)) ∧
      (∀ x ∉ U, G x = g x) ∧
      (∀ x : A, f x = e (g x) → G x = g x) ∧
      (∀ x : A, G x ∈ e.source ∧
        ‖e (G x) - e (g x)‖ ≤ ‖f x - e (g x)‖) := by
  obtain ⟨χ, hχ0, hχ1, hχrange⟩ := exists_continuous_zero_one_of_isClosed
    hU.isClosed_compl hB (disjoint_left.mpr (fun _ hx hxb => hx (hBU hxb)))
  let χA : C(A, ℝ) := χ.comp ⟨Subtype.val, continuous_subtype_val⟩
  let gA : C(A, F) := ⟨fun x => e (g x), e.continuousOn.comp_continuous
    (g.continuous.comp continuous_subtype_val) hgsource⟩
  let q : C(A, F) := cutoffBlend gA f χA
  have hqtarget (x : A) : q x ∈ e.target := hStarget
    (cutoffBlend_mem_convex gA f χA hS (hχrange x) (hgrange x) (hfrange x))
  have hqboundary (x : A) (hx : x.1 ∈ frontier A) : q x = e (g x) :=
    cutoffBlend_eq_left gA f χA (hχ0 (fun hxU => hx.2 (hUA hxU)))
  obtain ⟨G, hG, hGout, hGcoord, hGfix⟩ := exists_chart_replacement_on_closed
    e hA g q hgsource hqtarget hqboundary
  refine ⟨G, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [hG x]
    exact congrArg e.symm (cutoffBlend_eq_right gA f χA (hχ1 hx))
  · intro x hxU
    by_cases hxA : x ∈ A
    · exact hGfix ⟨x, hxA⟩ (cutoffBlend_eq_left gA f χA (hχ0 hxU))
    · exact hGout x (fun hi => hxA (interior_subset hi))
  · intro x hx
    exact hGfix x (cutoffBlend_eq_of_eq gA f χA hx)
  · intro x
    refine ⟨(hGcoord x).1, ?_⟩
    rw [(hGcoord x).2]
    exact cutoffBlend_norm_sub_le gA f χA (hχrange x)

end ChartBlend

end DifferentialGeometry.Topology.Engulfing
