import DifferentialGeometry.Topology.PiecewiseLinear.Section34MeridianPosition
import DifferentialGeometry.Topology.PiecewiseLinear.Section34MeridianSlideInvariants
import DifferentialGeometry.Topology.PiecewiseLinear.Section34NullMeridianEmptyBigon

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

open Classical in
theorem Section34MeridianPosition.exists_strict_slide
    (D : Geometry.SimplicialComplex ℝ E) (M : Geometry.SimplicialComplex ℝ F)
    [Finite D.faces] [Finite M.faces] (hD : IsPLBall 2 D.space)
    (hM : IsCombinatorialManifoldWithBoundary 3 M)
    {f : E × ℝ → F} (hf : IsCylindricalDiagram f D.space M.space)
    (hends : ∀ x ∈ D.space, f (x, 0) = f (x, 1))
    (hdim : Module.finrank ℝ F = 3) {J : Set F} {r : ℝ}
    (hpos : Section34MeridianPosition D M f r J) (hr : r ∈ Ioo (1 / 4 : ℝ) (3 / 4))
    (hne : (J ∩ f '' (D.space ×ˢ {r})).Nonempty) :
    ∃ H : F → F, IsPLHomeomorphOn H M.space M.space ∧
      Section34MeridianPosition D M f r (H '' J) ∧
      (H '' J ∩ f '' (D.space ×ˢ {r})).ncard < (J ∩ f '' (D.space ×ˢ {r})).ncard := by
  classical
  have hr01 : r ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [hr.1, hr.2]
  let P := (boundaryComplex 2 D).space
  let L := f '' (P ×ˢ {r})
  have hPD : P ⊆ D.space := boundaryComplex_space_subset 2 D
  have hP : IsPLSphere 1 P := isPLSphere_boundaryComplex_space_of_isPLBall D hD
  have hside := hf.boundary D hD.isCombinatorialManifoldWithBoundary
  have hsideEq := hf.image_side_eq_boundaryComplex D M hD hM hdim
  have hL : IsPLSphere 1 L :=
    hP.of_isPLHomeomorphOn (hside.isPLHomeomorphOn_slice hP.isPolyhedron hr01)
  have hLB : L ⊆ (boundaryComplex 3 M).space := by
    rw [← hsideEq]
    exact image_mono (fun _ hz => ⟨hz.1, hz.2.symm ▸ hr01⟩)
  obtain ⟨d, hd⟩ := hD
  have hdBd : d '' stdSimplexBoundary 2 = P := by
    rw [show P = (boundaryComplex 2 D).space from rfl,
      boundaryComplex_space_of_isPLHomeomorphOn_stdSimplex D hd,
      simplexBoundary_stdVertices_space]
  have hJside : J ⊆ f '' ((d '' stdSimplexBoundary 2) ×ˢ Icc (0 : ℝ) 1) := by
    rw [hdBd, hsideEq]
    exact hpos.boundary
  obtain ⟨B, q, x, y, hq, hBside, hBJ, hBL, hxy, hBtrace, -⟩ :=
    hf.exists_empty_bigon_of_nullhomotopic_circle hd hends hpos.circle hJside
      (hpos.boundary.trans (boundaryComplex_space_subset 3 M)) hpos.volumeNull
      (by norm_num) (by norm_num) hr hpos.traceFinite hpos.heightSides hne
  rw [hdBd] at hBside hBL hBtrace
  have hBB : B ⊆ (boundaryComplex 3 M).space := hsideEq ▸ hBside
  let c : Fin 2 → F := ![x, y]
  have hc : Function.Injective c := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · exact (hxy hij).elim
    · exact (hxy hij.symm).elim
    · rfl
  have hcTrace : B ∩ (J ∩ L) = {c 0, c 1} := hBtrace
  have hcJL (i : Fin 2) : c i ∈ J ∩ L := by
    apply (hcTrace.symm.subset ?_).2
    fin_cases i <;> simp [c]
  choose e ε hε hcenter hsource haxes using fun i => hpos.axisCharts (c i) (hcJL i)
  obtain ⟨N, n, H, hn, -, -, hH, hfix, hHN, htrace, hNtrace, -⟩ :=
    hM.exists_boundary_raw_bigon_slide M ⟨q, hq⟩ hBB isOpen_univ (subset_univ B)
      hpos.circle hL hpos.boundary hLB hBJ hBL c hc hcTrace e ε hε hsource hcenter
      (fun i p hp => (haxes i p hp).1) (fun i p hp => (haxes i p hp).2)
  obtain ⟨hnewB, hnewJ, hnewNull, hnewEss⟩ := hM.meridian_class_of_volume_selfmap M
    hpos.circle hpos.boundary hpos.volumeNull hpos.boundaryEssential hH
  have holdTrace := hf.meridian_trace_eq_rim_trace D M ⟨d, hd⟩ hM hdim hpos.boundary hr01
  have hnewTrace := hf.meridian_trace_eq_rim_trace D M ⟨d, hd⟩ hM hdim hnewB hr01
  have hfullTrace : H '' J ∩ f '' (D.space ×ˢ {r}) =
      (J ∩ f '' (D.space ×ˢ {r})) \ {c 0, c 1} := by
    rw [holdTrace, hnewTrace]
    exact htrace
  have hNfull : N ∩ (J ∩ f '' (D.space ×ˢ {r})) = {c 0, c 1} := by
    rw [holdTrace]
    exact hNtrace
  obtain ⟨hfinite, -, hlt⟩ := remaining_meridian_trace_finite_and_strict hxy
    hpos.traceFinite hNfull hfullTrace
  have hNclosed : IsClosed N := (IsPLBall.isPolyhedron ⟨n, hn⟩).isClosed
  have hHNmap : MapsTo H N N := image_subset_iff.mp hHN.subset
  refine ⟨H, hH, ⟨hnewJ, hnewB, hnewNull, hnewEss, hfinite, ?_, ?_⟩, hlt⟩
  · exact hf.height_germs_after_supported_slide hpos.boundary hNclosed hHNmap hfix
      hr01 hNfull.subset hfullTrace (by norm_num) (by norm_num) hpos.heightSides
  · exact remaining_meridian_axis_charts_of_supported_slide hpos.boundary hNclosed
      hHNmap hfix hNtrace.subset htrace hpos.axisCharts

open Classical in
theorem Section34MeridianPosition.exists_disjoint_image
    (D : Geometry.SimplicialComplex ℝ E) (M : Geometry.SimplicialComplex ℝ F)
    [Finite D.faces] [Finite M.faces] (hD : IsPLBall 2 D.space)
    (hM : IsCombinatorialManifoldWithBoundary 3 M)
    {f : E × ℝ → F} (hf : IsCylindricalDiagram f D.space M.space)
    (hends : ∀ x ∈ D.space, f (x, 0) = f (x, 1))
    (hdim : Module.finrank ℝ F = 3) {J : Set F} {r : ℝ}
    (hpos : Section34MeridianPosition D M f r J) (hr : r ∈ Ioo (1 / 4 : ℝ) (3 / 4)) :
    ∃ H : F → F, IsPLHomeomorphOn H M.space M.space ∧
      Section34MeridianPosition D M f r (H '' J) ∧
      Disjoint (H '' J) (f '' (D.space ×ˢ {r})) := by
  classical
  suffices ∀ n : ℕ, ∀ J : Set F, Section34MeridianPosition D M f r J →
      (J ∩ f '' (D.space ×ˢ {r})).ncard = n →
      ∃ H : F → F, IsPLHomeomorphOn H M.space M.space ∧
        Section34MeridianPosition D M f r (H '' J) ∧
        Disjoint (H '' J) (f '' (D.space ×ˢ {r})) by
    exact this _ J hpos rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro K hK hn
    by_cases hne : (K ∩ f '' (D.space ×ˢ {r})).Nonempty
    · obtain ⟨H, hH, hnew, hlt⟩ := hK.exists_strict_slide D M hD hM hf hends hdim hr hne
      obtain ⟨U, hU, hfinal, hdis⟩ := ih _ (hn ▸ hlt) (H '' K) hnew rfl
      exact ⟨U ∘ H, hH.trans hU, by simpa only [image_comp] using hfinal,
        by simpa only [image_comp] using hdis⟩
    · refine ⟨id, (isPolyhedron_space M).isPLHomeomorphOn_id, ?_, ?_⟩
      · simpa only [image_id] using hK
      · rw [image_id]
        exact disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp hne)

end DifferentialGeometry.Topology.PiecewiseLinear
