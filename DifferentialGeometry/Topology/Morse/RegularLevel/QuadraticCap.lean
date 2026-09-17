import DifferentialGeometry.Topology.Morse.RegularLevel.HeightComponents
import DifferentialGeometry.Topology.LevelSet.QuadraticGraph

open Set Metric Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.Morse

theorem image_superlevel_component_level_eq_sphere_of_quadratic_cap
    {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M] [NormedAddCommGroup F]
    {I : ModelWithCorners ℝ E H} [I.Boundaryless] [IsManifold I ∞ M]
    [T2Space M] [SigmaCompactSpace M]
    {e : M → F × ℝ} (he : _root_.Topology.IsEmbedding e)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x => (e x).2))
    {a b c α r : ℝ} (hab : a ≤ b) (hb : b = c + α / 2 * r ^ 2)
    (hα : α ≠ 0) (hr : 0 ≤ r)
    (hcompact : IsCompact ((fun x => (e x).2) ⁻¹' Icc a b))
    (hregular : ∀ x, (e x).2 ∈ Icc a b → ¬ IsCriticalPointAt I (fun y => (e y).2) x)
    {p : M} (hp : b ≤ (e p).2) (A : F × ℝ → F × ℝ)
    (hA : ∀ z, (A z).2 = z.2)
    (hcap : e '' connectedComponentIn {x | b ≤ (e x).2} p =
      (fun y => A (y, c + α / 2 * ‖y‖ ^ 2)) '' closedBall 0 r)
    (Φ : ℝ → F ≃ F)
    (hΦ : ∀ x, (e x).2 = a → ContinuousOn (fun t => Φ t (e x).1) (Icc a b))
    (hΦa : EqOn (Φ a) id ((fun x => (e x).1) '' {x | (e x).2 = a}))
    (hlevels : ∀ t ∈ Icc a b,
      Φ t '' ((fun x => (e x).1) '' {x | (e x).2 = a}) =
        (fun x => (e x).1) '' {x | (e x).2 = t}) :
    ∀ t ∈ Icc a b,
      (fun x => (e x).1) ''
        (connectedComponentIn {x | t ≤ (e x).2} p ∩ {x | (e x).2 = t}) =
      (fun y => Φ t ((Φ b).symm (A (y, b)).1)) '' sphere 0 r := by
  let C := connectedComponentIn {x | b ≤ (e x).2} p
  have hcap' : (fun x : C => e x.val) '' univ =
      (fun y => A (y, c + α / 2 * ‖y‖ ^ 2)) '' closedBall 0 r := by
    rw [image_univ]
    change range (e ∘ (Subtype.val : C → M)) = _
    rw [range_comp, Subtype.range_coe]
    exact hcap
  have htop' := Function.image_level_eq_image_sphere_of_image_quadratic_graph_eq
    (fun x : C => e x.val) A hA hα hr (subset_univ _) hcap'
  rw [← hb] at htop'
  have htop : (fun x => (e x).1) ''
      (connectedComponentIn {x | b ≤ (e x).2} p ∩ {x | (e x).2 = b}) =
      (fun y => (A (y, b)).1) '' sphere 0 r := by
    rw [← htop']
    ext y
    constructor
    · rintro ⟨x, ⟨hxC, hxlevel⟩, rfl⟩
      exact ⟨⟨x, hxC⟩, hxlevel, rfl⟩
    · rintro ⟨x, hxlevel, rfl⟩
      exact ⟨x.val, ⟨x.property, hxlevel⟩, rfl⟩
  have htransport := image_superlevel_component_level_of_no_critical_values he hf hab hcompact
    hregular hp (fun t => Φ t) hΦ hΦa hlevels
  have hbase : (fun x => (e x).1) ''
      (connectedComponentIn {x | a ≤ (e x).2} p ∩ {x | (e x).2 = a}) =
      (Φ b).symm '' ((fun y => (A (y, b)).1) '' sphere 0 r) := by
    have h := congrArg (fun S : Set F => (Φ b).symm '' S)
      ((htransport b ⟨hab, le_rfl⟩).trans htop)
    exact ((Φ b).symm_image_image _).symm.trans h
  intro t ht
  rw [← htransport t ht, hbase, image_image, image_image]

end DifferentialGeometry.Topology.Morse
