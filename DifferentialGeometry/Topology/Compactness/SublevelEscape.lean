import DifferentialGeometry.Topology.Compactness.Cocompact

open Set Filter

theorem tendsto_atTop_of_isCompact_sublevel
    {X L : Type*} [TopologicalSpace X] [LinearOrder L] {f : X → L}
    (hcompact : ∀ b : L, IsCompact {x | f x ≤ b}) :
    Tendsto f (cocompact X) atTop := by
  apply tendsto_atTop.mpr
  intro b
  filter_upwards [(hcompact b).compl_mem_cocompact] with x hx
  exact le_of_not_ge hx
