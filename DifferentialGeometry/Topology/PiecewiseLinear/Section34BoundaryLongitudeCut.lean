import DifferentialGeometry.Topology.PiecewiseLinear.Section34MeridianSeam
import DifferentialGeometry.Topology.PiecewiseLinear.Section34ProperLongitudeArc

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

open Classical in
theorem IsCylindricalDiagram.exists_proper_boundary_longitude_cut
    {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (D : Geometry.SimplicialComplex ℝ E) (M : Geometry.SimplicialComplex ℝ F)
    [Finite D.faces] [Finite M.faces] (hD : IsPLBall 2 D.space)
    (hM : IsCombinatorialManifoldWithBoundary 3 M) (hdim : Module.finrank ℝ F = 3)
    {f : E × ℝ → F} (hf : IsCylindricalDiagram f D.space M.space)
    (hends : ∀ x ∈ D.space, f (x, 0) = f (x, 1)) {J : Set F}
    (hJ : IsPLSphere 1 J) (hJB : J ⊆ (boundaryComplex 3 M).space)
    (hnon : ¬ (⟨inclusion (hJB.trans (boundaryComplex_space_subset 3 M)),
      continuous_inclusion _⟩ : C(J, M.space)).Nullhomotopic) {p : F}
    (htrace : J ∩ f '' ((boundaryComplex 2 D).space ×ˢ ({0} : Set ℝ)) = {p}) :
    ∃ (a : E) (γ : ℝ → E × ℝ), a ∈ (boundaryComplex 2 D).space ∧ f (a, 0) = p ∧
      IsPLHomeomorphOn γ (Icc 0 1) ((D.space ×ˢ Icc (0 : ℝ) 1) ∩ f ⁻¹' J) ∧
      γ 0 = (a, 0) ∧ γ 1 = (a, 1) ∧
      γ '' Icc 0 1 ⊆ (boundaryComplex 2 D).space ×ˢ Icc (0 : ℝ) 1 ∧
      γ '' Ioo 0 1 = (D.space ×ˢ Ioo (0 : ℝ) 1) ∩ f ⁻¹' J ∧
      (γ '' Icc 0 1) ∩ ((boundaryComplex 2 D).space ×ˢ ({0} : Set ℝ)) = {(a, 0)} ∧
      (γ '' Icc 0 1) ∩ ((boundaryComplex 2 D).space ×ˢ ({1} : Set ℝ)) = {(a, 1)} ∧
      (f ∘ γ) '' Ioo 0 1 = J \ {p} := by
  have hDbd := boundaryComplex_space_subset 2 D
  have hfull : J ∩ f '' (D.space ×ˢ ({0} : Set ℝ)) = {p} :=
    (hf.meridian_trace_eq_rim_trace D M hD hM hdim hJB (by norm_num)).trans htrace
  have hside : (D.space ×ˢ Icc (0 : ℝ) 1) ∩ f ⁻¹' J ⊆
      (boundaryComplex 2 D).space ×ˢ Icc (0 : ℝ) 1 := by
    rintro z ⟨hz, hzJ⟩
    have hJside : J ⊆ f '' ((boundaryComplex 2 D).space ×ˢ Icc (0 : ℝ) 1) := by
      rw [hf.image_side_eq_boundaryComplex D M hD hM hdim]
      exact hJB
    obtain ⟨w, hw, heq⟩ := hJside hzJ
    have hfst := ((hf.eq_iff_fst_eq_and_circle_eq hends ⟨hDbd hw.1, hw.2⟩ hz).mp heq).1
    exact ⟨hfst ▸ hw.1, hz.2⟩
  obtain ⟨a, γ, -, hap, hγ, hγ0, hγ1, hopen, hcap, hmap⟩ :=
    hf.exists_proper_cut_arc_of_singleton_seam hD hends hJ
      (hJB.trans (boundaryComplex_space_subset 3 M)) hfull hnon
  have hγside : γ '' Icc 0 1 ⊆ (boundaryComplex 2 D).space ×ˢ Icc (0 : ℝ) 1 :=
    hγ.image_eq.subset.trans hside
  have hzero : (a, (0 : ℝ)) ∈ γ '' Icc 0 1 :=
    ⟨0, by norm_num, hγ0⟩
  have hone : (a, (1 : ℝ)) ∈ γ '' Icc 0 1 :=
    ⟨1, by norm_num, hγ1⟩
  have ha := (hγside hzero).1
  refine ⟨a, γ, ha, hap, hγ, hγ0, hγ1, hγside, hopen, ?_, ?_, hmap⟩
  · ext z
    constructor
    · rintro ⟨hz, hzbot⟩
      rcases hcap.subset ⟨hz, hDbd hzbot.1, Or.inl hzbot.2⟩ with h | h
      · exact h
      · exact (one_ne_zero ((congrArg Prod.snd h).symm.trans hzbot.2)).elim
    · rintro rfl
      exact ⟨hzero, ha, rfl⟩
  · ext z
    constructor
    · rintro ⟨hz, hztop⟩
      rcases hcap.subset ⟨hz, hDbd hztop.1, Or.inr hztop.2⟩ with h | h
      · exact (zero_ne_one ((congrArg Prod.snd h).symm.trans hztop.2)).elim
      · exact h
    · rintro rfl
      exact ⟨hone, ha, rfl⟩

end DifferentialGeometry.Topology.PiecewiseLinear
