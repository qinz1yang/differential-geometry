import DifferentialGeometry.Topology.PiecewiseLinear.GeneralPosition

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem Homeomorph.image_inter_of_eqOn {M : Type*} [TopologicalSpace M]
    (ψ : M ≃ₜ M) {B O : Set M} (hfix : EqOn ψ id O) : (ψ '' B) ∩ O = B ∩ O := by
  ext x
  constructor
  · rintro ⟨⟨y, hy, hyx⟩, hx⟩
    have heq : y = x := ψ.injective (hyx.trans (hfix hx).symm)
    exact ⟨heq ▸ hy, hx⟩
  · rintro ⟨hx, hxO⟩
    exact ⟨⟨x, hx, hfix hxO⟩, hxO⟩

theorem HasPLCrossingAt.image_right_of_fixed_open {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {A B O : Set E} {y : E} (hcross : HasPLCrossingAt A B y)
    (ψ : E ≃ₜ E) (hO : IsOpen O) (hfix : EqOn ψ id O) (hyO : y ∈ O) :
    HasPLCrossingAt A (ψ '' B) y := by
  apply hcross.congr (Filter.Eventually.of_forall fun _ => Iff.rfl)
  filter_upwards [hO.mem_nhds hyO] with z hz
  have heq := Set.ext_iff.mp (Homeomorph.image_inter_of_eqOn ψ (B := B) hfix) z
  exact ⟨fun hB => (heq.mpr ⟨hB, hz⟩).1, fun hB => (heq.mp ⟨hB, hz⟩).1⟩

private theorem eventually_mem_chart_image_iff {M E : Type*}
    [TopologicalSpace M] [TopologicalSpace E] {c : OpenPartialHomeomorph M E}
    {B B' O : Set M} (hO : IsOpen O) (hBO : B ∩ O = B' ∩ O)
    {y : M} (hyO : y ∈ O) (hy : y ∈ c.source) :
    ∀ᶠ z in 𝓝 (c y), z ∈ c '' (B ∩ c.source) ↔ z ∈ c '' (B' ∩ c.source) := by
  have hkey : ∀ {X Y : Set M}, X ∩ O = Y ∩ O → ∀ a ∈ c.source ∩ O,
      c a ∈ c '' (X ∩ c.source) → c a ∈ c '' (Y ∩ c.source) := by
    intro X Y hXY a ⟨has, haO⟩ ⟨b, ⟨hbX, hbs⟩, hba⟩
    have hb : b = a := c.injOn hbs has hba
    subst hb
    exact ⟨b, ⟨((Set.ext_iff.mp hXY b).mp ⟨hbX, haO⟩).1, hbs⟩, rfl⟩
  filter_upwards [(c.isOpen_image_source_inter hO).mem_nhds ⟨y, ⟨hy, hyO⟩, rfl⟩] with z hz
  obtain ⟨a, ha, rfl⟩ := hz
  exact ⟨hkey hBO a ha, hkey hBO.symm a ha⟩

theorem HasPLCrossingAt.image_right_of_fixed_neighborhood {M : Type*} [TopologicalSpace M]
    {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {A B O : Set M} {y : M}
    (hcross : HasPLCrossingAt (c '' (A ∩ c.source)) (c '' (B ∩ c.source)) (c y))
    (ψ : M ≃ₜ M) (hO : IsOpen O) (hfix : EqOn ψ id O)
    (hyO : y ∈ O) (hy : y ∈ c.source) :
    HasPLCrossingAt (c '' (A ∩ c.source)) (c '' (ψ '' B ∩ c.source)) (c y) := by
  apply hcross.congr (Filter.Eventually.of_forall fun _ => Iff.rfl)
  exact eventually_mem_chart_image_iff hO
    (Homeomorph.image_inter_of_eqOn ψ hfix).symm hyO hy

end DifferentialGeometry.Topology.PiecewiseLinear
