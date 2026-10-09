import DifferentialGeometry.Topology.PiecewiseLinear.Section34CrossingCornerCoreAlignment
import DifferentialGeometry.Topology.PiecewiseLinear.Section34FillingRibbonContacts

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsCylindricalDiagram.exists_filling_corner_chart_matching_core
    {A E : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {f : (ℝ × ℝ) × ℝ → E} {C R X Y F D : Set E}
    (hf : IsCylindricalDiagram f spliceSquare C)
    (hends : ∀ p ∈ spliceSquare, f (p, 0) = f (p, 1))
    (hfirst : f '' (section34MarkedRibbon 0 ∪ section34MarkedRibbon 2) = C ∩ X)
    (hsecond : f '' (section34MarkedRibbon 1 ∪ section34MarkedRibbon 3) = C ∩ Y)
    {a b : Bool}
    (hquadrant : f '' (section34CrossingQuadrant a b ×ˢ Icc (0 : ℝ) 1) = C ∩ R)
    (hF : X ∩ R = F) (hD : Y ∩ R = D)
    {g : A × ℝ → E} {P B : Set A} {S : Set E} (hg : IsCylindricalDiagram g P S)
    (hgends : ∀ p ∈ P, g (p, 0) = g (p, 1)) {γ : ℝ → A}
    (hγ : IsPLHomeomorphOn γ (Icc 0 1) B) (hBP : B ⊆ P)
    (haxis : f '' section34MarkedAxis = g '' ({γ 0} ×ˢ Icc (0 : ℝ) 1)) :
    ∃ (ρ : (Fin 3 → ℝ) × ℝ → E) (ν : (Fin 3 → ℝ) → (Fin 3 → ℝ)) (W : Set E),
      IsPLHomeomorphOn ρ (stdSimplexBoundary 2 ×ˢ Icc (-(1 / 2) : ℝ) (1 / 2)) W ∧
      IsPLHomeomorphOn ν (stdSimplexBoundary 2) (stdSimplexBoundary 2) ∧ W ⊆ F ∪ D ∧
      (∀ s ∈ Icc (0 : ℝ) 1, ρ (stdTriangleLoop s, 0) = g (γ 0, s)) ∧
      ρ '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) (1 / 2)) ⊆ F ∧
      ρ '' (stdSimplexBoundary 2 ×ˢ Icc (-(1 / 2) : ℝ) 0) ⊆ D ∧
      (∀ s, ∀ q ∈ Icc (0 : ℝ) 1, ν (stdTriangleLoop s) = stdTriangleLoop q →
        ∀ t ∈ Icc (0 : ℝ) (1 / 2), ρ (stdTriangleLoop s, t) =
          f (t • fourSpokeModelLeaf (if a then 0 else 2), q)) ∧
      (∀ s, ∀ q ∈ Icc (0 : ℝ) 1, ν (stdTriangleLoop s) = stdTriangleLoop q →
        ∀ t ∈ Icc (-(1 / 2) : ℝ) 0, ρ (stdTriangleLoop s, t) =
          f ((-t) • fourSpokeModelLeaf (if b then 1 else 3), q)) ∧
      (∀ Q ⊆ Icc (0 : ℝ) (1 / 2), ρ '' (stdSimplexBoundary 2 ×ˢ Q) =
        f '' (((fun t : ℝ => t • fourSpokeModelLeaf (if a then 0 else 2)) '' Q) ×ˢ
          Icc (0 : ℝ) 1)) ∧
      ∀ Q ⊆ Icc (-(1 / 2) : ℝ) 0, ρ '' (stdSimplexBoundary 2 ×ˢ Q) =
        f '' (((fun t : ℝ => (-t) • fourSpokeModelLeaf (if b then 1 else 3)) '' Q) ×ˢ
          Icc (0 : ℝ) 1) := by
  let i : Fin 4 := if a then 0 else 2
  let j : Fin 4 := if b then 1 else 3
  have hij : i ≠ j := by cases a <;> cases b <;> decide
  obtain ⟨ρ, ν, hρ, hν, hcore, hpos, hneg, hposImage, hnegImage⟩ :=
    hf.exists_signed_ribbon_chart_matching_cylindrical_core hends i j hij hg hgends
      hγ hBP haxis
  obtain ⟨hFi, hDj⟩ := hf.filling_face_ribbon_contacts hends hfirst hsecond hquadrant hF hD
  have hiF : f '' section34MarkedRibbon i ⊆ F := hFi.symm.subset.trans inter_subset_right
  have hjD : f '' section34MarkedRibbon j ⊆ D := hDj.symm.subset.trans inter_subset_right
  have hp : Icc (0 : ℝ) (1 / 2) ⊆ Icc (0 : ℝ) 1 :=
    Icc_subset_Icc le_rfl (by norm_num)
  have hn : Icc (-(1 / 2) : ℝ) 0 ⊆ Icc (-1 : ℝ) 0 :=
    Icc_subset_Icc (by norm_num) le_rfl
  have hsmall : stdSimplexBoundary 2 ×ˢ Icc (-(1 / 2) : ℝ) (1 / 2) ⊆
      stdSimplexBoundary 2 ×ˢ Icc (-1 : ℝ) 1 :=
    prod_mono_right (Icc_subset_Icc (by norm_num) (by norm_num))
  have hρsmall := hρ.restrict
    (isPolyhedron_stdSimplexBoundary_two.prod isHPolytope_Icc.isPolyhedron) hsmall
  have hspoke (k : Fin 4) : (fun t : ℝ => t • fourSpokeModelLeaf k) '' Icc 0 1 =
      segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf k) := by
    simpa using (segment_eq_image ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf k)).symm
  have hnegSpoke : (fun t : ℝ => (-t) • fourSpokeModelLeaf j) '' Icc (-1 : ℝ) 0 =
      segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf j) := by
    have heq : (fun t : ℝ => -t) '' Icc (-1 : ℝ) 0 = Icc (0 : ℝ) 1 := by
      simp
    rw [show (fun t : ℝ => (-t) • fourSpokeModelLeaf j) =
      (fun t : ℝ => t • fourSpokeModelLeaf j) ∘ (fun t => -t) from rfl,
      image_comp, heq, hspoke]
  have hposAll : ρ '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ⊆ F := by
    rw [hposImage _ Subset.rfl, hspoke]
    exact hiF
  have hnegAll : ρ '' (stdSimplexBoundary 2 ×ˢ Icc (-1 : ℝ) 0) ⊆ D := by
    rw [hnegImage _ Subset.rfl, hnegSpoke]
    exact hjD
  refine ⟨ρ, ν, _, hρsmall, hν, ?_, hcore,
    (image_mono (prod_mono_right hp)).trans hposAll,
    (image_mono (prod_mono_right hn)).trans hnegAll,
    (fun s q hq heq t ht => hpos s q hq heq t (hp ht)),
    (fun s q hq heq t ht => hneg s q hq heq t (hn ht)),
    (fun Q hQ => hposImage Q (hQ.trans hp)), fun Q hQ => hnegImage Q (hQ.trans hn)⟩
  exact ((image_mono hsmall).trans hρ.image_eq.subset).trans
    (union_subset (hjD.trans subset_union_right) (hiF.trans subset_union_left))

end DifferentialGeometry.Topology.PiecewiseLinear
