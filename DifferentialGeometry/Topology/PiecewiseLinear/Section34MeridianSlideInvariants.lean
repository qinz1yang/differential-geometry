import DifferentialGeometry.Topology.PiecewiseLinear.CylindricalFrontier
import DifferentialGeometry.Topology.PiecewiseLinear.Section34BoundaryBigonSlide
import DifferentialGeometry.Topology.PiecewiseLinear.Section34MeridianMotionClass
import DifferentialGeometry.Topology.PiecewiseLinear.Section34SurfaceSlideGerms

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

open Classical in
theorem IsPLHomeomorphOn.restrict_boundary_complex_of_selfmap
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {n : ℕ} (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) K)
    {H : E → E} (hH : IsPLHomeomorphOn H K.space K.space) :
    IsPLHomeomorphOn H (boundaryComplex (n + 1) K).space
      (boundaryComplex (n + 1) K).space := by
  let _ : Finite (boundaryComplex (n + 1) K).faces :=
    (boundaryComplex_faces_finite (n + 1) K).to_subtype
  have h := hH.restrict (isPolyhedron_space (boundaryComplex (n + 1) K))
    (boundaryComplex_space_subset (n + 1) K)
  rwa [← boundaryComplex_space_of_isPLHomeomorphOn K K hK hH] at h

open Classical in
theorem IsCylindricalDiagram.isPLHomeomorphOn_lateral_of_volume_selfmap
    {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (D : Geometry.SimplicialComplex ℝ E) (K : Geometry.SimplicialComplex ℝ F)
    [Finite D.faces] [Finite K.faces] (hD : IsPLBall 2 D.space)
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hdim : Module.finrank ℝ F = 3)
    {f : E × ℝ → F} (hf : IsCylindricalDiagram f D.space K.space)
    {H : F → F} (hH : IsPLHomeomorphOn H K.space K.space) :
    IsPLHomeomorphOn H (f '' ((boundaryComplex 2 D).space ×ˢ Icc (0 : ℝ) 1))
      (f '' ((boundaryComplex 2 D).space ×ˢ Icc (0 : ℝ) 1)) := by
  rw [hf.image_side_eq_boundaryComplex D K hD hK hdim]
  exact hH.restrict_boundary_complex_of_selfmap K hK

open Classical in
theorem IsCylindricalDiagram.meridian_trace_eq_rim_trace
    {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (D : Geometry.SimplicialComplex ℝ E) (K : Geometry.SimplicialComplex ℝ F)
    [Finite D.faces] [Finite K.faces] (hD : IsPLBall 2 D.space)
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hdim : Module.finrank ℝ F = 3)
    {f : E × ℝ → F} (hf : IsCylindricalDiagram f D.space K.space)
    {J : Set F} (hJB : J ⊆ (boundaryComplex 3 K).space)
    {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) :
    J ∩ f '' (D.space ×ˢ {r}) = J ∩ f '' ((boundaryComplex 2 D).space ×ˢ {r}) := by
  have hside := hf.boundary D hD.isCombinatorialManifoldWithBoundary
  have hmeet : (boundaryComplex 3 K).space ∩ f '' (D.space ×ˢ {r}) =
      f '' ((boundaryComplex 2 D).space ×ˢ {r}) := by
    rw [← hf.image_side_eq_boundaryComplex D K hD hK hdim]
    exact hf.image_subcylinder_inter_slice (boundaryComplex_space_subset 2 D)
      hside.image_top_eq_bottom hr
  ext y
  exact ⟨fun hy => ⟨hy.1, hmeet.subset ⟨hJB hy.1, hy.2⟩⟩,
    fun hy => ⟨hy.1, (hmeet.symm.subset hy.2).2⟩⟩

open Classical in
theorem IsCombinatorialManifoldWithBoundary.meridian_class_of_volume_selfmap
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) {J : Set E} (hJ : IsPLSphere 1 J)
    (hJB : J ⊆ (boundaryComplex 3 K).space)
    (hnull : (⟨inclusion (hJB.trans (boundaryComplex_space_subset 3 K)),
      continuous_inclusion _⟩ : C(J, K.space)).Nullhomotopic)
    (hess : ¬(⟨inclusion hJB, continuous_inclusion hJB⟩ :
      C(J, (boundaryComplex 3 K).space)).Nullhomotopic)
    {H : E → E} (hH : IsPLHomeomorphOn H K.space K.space) :
    ∃ hnew : H '' J ⊆ (boundaryComplex 3 K).space, IsPLSphere 1 (H '' J) ∧
      (⟨inclusion (hnew.trans (boundaryComplex_space_subset 3 K)),
        continuous_inclusion _⟩ : C(H '' J, K.space)).Nullhomotopic ∧
      ¬(⟨inclusion hnew, continuous_inclusion hnew⟩ :
        C(H '' J, (boundaryComplex 3 K).space)).Nullhomotopic := by
  have hHB := hH.restrict_boundary_complex_of_selfmap K hK
  have hnew : H '' J ⊆ (boundaryComplex 3 K).space :=
    (image_mono hJB).trans hHB.image_eq.subset
  refine ⟨hnew, hJ.of_isPLHomeomorphOn (hHB.restrict hJ.isPolyhedron hJB),
    hH.nullhomotopic_inclusion_of_image (hJB.trans (boundaryComplex_space_subset 3 K))
      (hnew.trans (boundaryComplex_space_subset 3 K)) rfl hnull, ?_⟩
  exact fun h => hess ((hHB.nullhomotopic_inclusion_iff_of_image hJB hnew rfl).mpr h)

theorem remaining_meridian_trace_finite_and_strict
    {X : Type*} {J L N : Set X} {H : X → X} {p q : X}
    (hpq : p ≠ q) (hfinite : (J ∩ L).Finite)
    (hNtrace : N ∩ (J ∩ L) = {p, q})
    (htrace : H '' J ∩ L = (J ∩ L) \ {p, q}) :
    (H '' J ∩ L).Finite ∧ (H '' J ∩ L).ncard + 2 = (J ∩ L).ncard ∧
      (H '' J ∩ L).ncard < (J ∩ L).ncard := by
  have hp : p ∈ J ∩ L := (hNtrace.symm.subset (Or.inl rfl)).2
  have hq : q ∈ J ∩ L := (hNtrace.symm.subset (Or.inr rfl)).2
  have hcount := intersection_count_of_deleted_pair hpq hp hq htrace hfinite
  exact ⟨by rw [htrace]; exact hfinite.sdiff, hcount, by omega⟩

theorem remaining_meridian_axis_charts_of_supported_slide
    {X : Type*} [TopologicalSpace X] {S N J L R : Set X} {H : X → X}
    (hJ : J ⊆ S) (hN : IsClosed N) (hHN : MapsTo H N N)
    (hfix : EqOn H id (closure (S \ N)))
    (hNR : N ∩ (J ∩ L) ⊆ R) (htrace : H '' J ∩ L = (J ∩ L) \ R)
    (haxes : ∀ x ∈ J ∩ L, ∃ (e : OpenPartialHomeomorph (ℝ × ℝ) S) (ε : ℝ),
      0 < ε ∧ (e (0, 0) : X) = x ∧ Ioo (-ε) ε ×ˢ Ioo (-ε) ε ⊆ e.source ∧
      ∀ p ∈ Ioo (-ε) ε ×ˢ Ioo (-ε) ε,
        ((e p : X) ∈ J ↔ p.1 = 0) ∧ ((e p : X) ∈ L ↔ p.2 = 0)) :
    ∀ x ∈ H '' J ∩ L, ∃ (e : OpenPartialHomeomorph (ℝ × ℝ) S) (ε : ℝ),
      0 < ε ∧ (e (0, 0) : X) = x ∧ Ioo (-ε) ε ×ˢ Ioo (-ε) ε ⊆ e.source ∧
      ∀ p ∈ Ioo (-ε) ε ×ˢ Ioo (-ε) ε,
        ((e p : X) ∈ H '' J ↔ p.1 = 0) ∧ ((e p : X) ∈ L ↔ p.2 = 0) := by
  intro x hx
  obtain ⟨e, ε, hε, he0, hes, he⟩ := haxes x (htrace.subset hx).1
  obtain ⟨η, hη, -, hηs, hηaxes⟩ :=
    OpenPartialHomeomorph.exists_remaining_axis_chart_of_supported_slide
      hJ hN hHN hfix hNR htrace e hε hes
      (fun p hp => (he p hp).1) (fun p hp => (he p hp).2) (he0.symm ▸ hx)
  exact ⟨e, η, hη, he0, hηs, hηaxes⟩

theorem IsCylindricalDiagram.height_germs_after_supported_slide
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E × ℝ → F} {P : Set E} {S B N J R : Set F} {H : F → F}
    (hf : IsCylindricalDiagram f P S) (hJB : J ⊆ B) (hN : IsClosed N)
    (hHN : MapsTo H N N) (hfix : EqOn H id (closure (B \ N)))
    {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1)
    (hNR : N ∩ (J ∩ f '' (P ×ˢ {r})) ⊆ R)
    (htrace : H '' J ∩ f '' (P ×ˢ {r}) = (J ∩ f '' (P ×ˢ {r})) \ R)
    {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1)
    (hgerms : ∀ x ∈ P, f (x, r) ∈ J →
      (x, r) ∈ closure (((P ×ˢ Icc a b) ∩ f ⁻¹' J) ∩ {y | y.2 < r}) ∧
        (x, r) ∈ closure (((P ×ˢ Icc a b) ∩ f ⁻¹' J) ∩ {y | r < y.2})) :
    ∀ x ∈ P, f (x, r) ∈ H '' J →
      (x, r) ∈ closure (((P ×ˢ Icc a b) ∩ f ⁻¹' (H '' J)) ∩ {y | y.2 < r}) ∧
        (x, r) ∈ closure (((P ×ˢ Icc a b) ∩ f ⁻¹' (H '' J)) ∩ {y | r < y.2}) := by
  intro x hxP hxJ
  have hxtrace : f (x, r) ∈ H '' J ∩ f '' (P ×ˢ {r}) :=
    ⟨hxJ, (x, r), ⟨hxP, rfl⟩, rfl⟩
  have hxold := htrace.subset hxtrace
  have hxN : f (x, r) ∉ N := fun hxN => hxold.2 (hNR ⟨hxN, hxold.1⟩)
  obtain ⟨hlo, hhi⟩ := hgerms x hxP hxold.1.1
  have hcont := hf.isPiecewiseAffineOn.continuousOn (x, r) ⟨hxP, hr⟩
  have hsub (T : Set (E × ℝ)) : (P ×ˢ Icc a b) ∩ T ⊆ P ×ˢ Icc (0 : ℝ) 1 :=
    fun _ hy => ⟨hy.1.1, ha.trans hy.1.2.1, hy.1.2.2.trans hb⟩
  constructor
  · rw [inter_right_comm]
    apply (mem_closure_inter_pullback_image_iff_of_closed_support hJB hN hHN hfix
      ((P ×ˢ Icc a b) ∩ {y | y.2 < r}) (hcont.mono (hsub _)) hxN).mpr
    simpa only [inter_right_comm] using hlo
  · rw [inter_right_comm]
    apply (mem_closure_inter_pullback_image_iff_of_closed_support hJB hN hHN hfix
      ((P ×ˢ Icc a b) ∩ {y | r < y.2}) (hcont.mono (hsub _)) hxN).mpr
    simpa only [inter_right_comm] using hhi

end DifferentialGeometry.Topology.PiecewiseLinear
