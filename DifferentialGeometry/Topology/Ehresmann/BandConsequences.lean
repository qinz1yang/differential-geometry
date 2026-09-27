import DifferentialGeometry.Topology.Ehresmann.RegularBand
import Mathlib.Topology.Connected.Basic

set_option autoImplicit false
noncomputable section

open scoped ContDiff Manifold
open DifferentialGeometry.Topology.Morse

namespace DifferentialGeometry.Topology.Ehresmann

variable {m : ℕ} {H : Type} [TopologicalSpace H]
  {M : Type} [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ (MorseModel (m + 1)) H}
  [I.Boundaryless] [IsManifold I (⊤ : WithTop ℕ∞) M]
  [T2Space M] [SigmaCompactSpace M]
  (f : M → ℝ) (a b : ℝ) (hab : a < b) (hf : ContMDiff I 𝓘(ℝ) ∞ f)
  (hcompact : IsCompact (f ⁻¹' Set.Icc a b))
  (hregular : ∀ x ∈ f ⁻¹' Set.Icc a b, ¬ IsCriticalPointAt I f x)

include hab hf hcompact hregular in
theorem range_regularBandHeight [Nonempty (f ⁻¹' Set.Icc a b)] :
    Set.range (fun y : f ⁻¹' Set.Icc a b ↦ f y.1) = Set.Icc a b := by
  rcases exists_unitSpeedVectorField_on_strip I f hf a b hcompact hregular with
    ⟨v, hv, hsupp, hdfOn, hrate⟩
  let e := regularBandHomeomorph f a b hab hf v hv hsupp hdfOn hrate
  let y : f ⁻¹' Set.Icc a b := Classical.choice inferInstance
  let x : LevelSetSpace f a := (e.symm y).1
  apply Set.Subset.antisymm
  · rintro _ ⟨z, rfl⟩
    exact z.2
  · intro t ht
    exact ⟨e (x, ⟨t, ht⟩),
      regularBandHomeomorph_height f a b hab hf v hv hsupp hdfOn hrate (x, ⟨t, ht⟩)⟩

include hf hcompact hregular in
theorem connectedSpace_levelSet_iff_of_compact_regular_band
    (s t : ℝ) (hs : s ∈ Set.Icc a b) (ht : t ∈ Set.Icc a b) :
    ConnectedSpace (LevelSetSpace f s) ↔ ConnectedSpace (LevelSetSpace f t) := by
  let _ := manifoldLevelSetChartedSpace I f s hf
    (fun x hx ↦ hregular x (by simpa [hx] using hs))
  let _ := manifoldLevelSetChartedSpace I f t hf
    (fun x hx ↦ hregular x (by simpa [hx] using ht))
  rcases exists_unitSpeedVectorField_on_strip I f hf a b hcompact hregular with
    ⟨v, hv, hsupp, hdfOn, hrate⟩
  exact (regularLevelFlowDiffeomorphOnBand f a b hf v hv hsupp hdfOn hrate
    hregular s t hs ht).toHomeomorph.connectedSpace_iff

include hcompact in
theorem exists_unitCylinderDiffeomorph_of_compact_regular_band
    {ES HS : Type} [NormedAddCommGroup ES] [NormedSpace ℝ ES] [TopologicalSpace HS]
    {S : Type} [TopologicalSpace S] [ChartedSpace HS S]
    {IS : ModelWithCorners ℝ ES HS} :
    let _ : Fact (a < b) := ⟨hab⟩
    let hreg := fun x (hx : f x = a ∨ f x = b) ↦
      hregular x (show f x ∈ Set.Icc a b from by
        rcases hx with ha | hb
        · simp [ha, hab.le]
        · simp [hb, hab.le])
    let _ := manifoldLevelSetChartedSpace I f a hf (fun x hx ↦ hreg x (Or.inl hx))
    let _ := regularBandChartedSpace f a b hab hf hreg
    ∀ sphereToFiber : S ≃ₘ⟮IS, 𝓘(ℝ, MorseModel m)⟯ LevelSetSpace f a,
      ∃ d : Diffeomorph (IS.prod (𝓡∂ 1)) (morseModelWithCornersHalfSpace m)
          (S × Set.Icc (0 : ℝ) 1) (f ⁻¹' Set.Icc a b) ∞,
        (∀ p, f (d p).1 = (b - a) * p.2.1 + a) ∧
        (∀ x, (d (x, ⟨0, by norm_num⟩)).1 = (sphereToFiber x).1) := by
  dsimp only
  let _ : Fact (a < b) := ⟨hab⟩
  have hreg : ∀ x, f x = a ∨ f x = b → ¬ IsCriticalPointAt I f x := by
    intro x hx
    apply hregular x
    rcases hx with ha | hb
    · simp [ha, hab.le]
    · simp [hb, hab.le]
  let _ := manifoldLevelSetChartedSpace I f a hf (fun x hx ↦ hreg x (Or.inl hx))
  let _ := regularBandChartedSpace f a b hab hf hreg
  intro sphereToFiber
  rcases exists_regularBandDiffeomorph f a b hab hf hcompact hregular with ⟨d, hh, hl⟩
  refine ⟨unitCylinderDiffeomorphOfProduct a b sphereToFiber d, ?_, ?_⟩
  · intro p
    rw [unitCylinderDiffeomorphOfProduct_apply, hh, affineIntervalDiffeomorph_apply]
  · intro x
    rw [unitCylinderDiffeomorphOfProduct_lower]
    exact hl (sphereToFiber x)

end DifferentialGeometry.Topology.Ehresmann
