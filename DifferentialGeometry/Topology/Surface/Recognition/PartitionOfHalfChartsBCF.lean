import DifferentialGeometry.Topology.Surface.Recognition.PartitionOfBaseCurveBCF

/-!
# The embedded face partition from half charts of the base curve (lane S-BCF03b; BCF03 G7 part 1)

`exists_partition_of_halfCharts_BCF`: the abstract assembly `exists_partition_of_components_BCF`
fed by `exists_components_of_halfCharts_BCF` (G22). The base curve `Γ = f₁ '' (∂M₂ ∩ R_c)` carries a
half chart `d y` at every point (own base `Bs y`), and the chart coordinate vanishes exactly at the
rim base points `f₁ '' (He ∩ {T = c})` (`hE`); then every component `Y` of `∂M₂` has an
`EmbeddedFacePartition_BCF` whose disks are `Y ∩` whole edge fibres over `f₂ '' He` and whose
pieces cover `Y ∩ R_c`.
-/

set_option autoImplicit false

open Set Function Topology

noncomputable section

namespace DifferentialGeometry.Topology.Surface

open DifferentialGeometry.Topology

local notation "E2" => EuclideanSpace ℝ (Fin 2)

variable {Wt H : Type*} [TopologicalSpace Wt] [T2Space Wt] [NormedAddCommGroup H]
  [NormedSpace ℝ H] {fib₀ fib₁ : H → Set Wt} {f₁ f₂ : Wt → H} {T : Wt → ℝ} {c : ℝ}
  {X₁ X₂ Bd Rc : Set Wt} {B₀ : Set H}

/-- **The embedded face partition of every component of `∂M₂` from half charts of the base curve
whose coordinate vanishes exactly at the rim base points.** -/
theorem exists_partition_of_halfCharts_BCF (hfib₀ : ∀ y, fib₀ y = X₁ ∩ f₁ ⁻¹' {y})
    (hfib₁ : ∀ y, fib₁ y = X₂ ∩ f₂ ⁻¹' {y}) (hBd : IsClosed Bd) (hRc : IsCompact Rc)
    (hRcX : Rc ⊆ X₁) (hf₁ : ContinuousOn f₁ X₁)
    (hsat : ∀ p ∈ Bd ∩ Rc, ∀ q ∈ X₁, f₁ q = f₁ p → q ∈ Bd ∩ Rc) (hB : f₁ '' (Bd ∩ Rc) ⊆ B₀)
    (hch : ∀ y ∈ f₁ '' (Bd ∩ Rc), ∃ (σ : E2 → H) (φ : E2 × Circle → Wt) (O : Set H) (x₀ : E2),
      σ x₀ = y ∧ IsEmbedding σ ∧ IsOpen O ∧ range σ = B₀ ∩ O ∧ Continuous φ ∧ Injective φ ∧
      range φ = X₁ ∩ f₁ ⁻¹' range σ ∧ ∀ x z, f₁ (φ (x, z)) = σ x)
    (hHe : ∀ p ∈ Bd ∩ X₂, ∀ q ∈ X₂, f₂ q = f₂ p → q ∈ Bd ∩ X₂)
    (hdisk : ∀ p ∈ Bd ∩ X₂, ∃ ed : fib₁ (f₂ p) ≃ₜ ClosedCell 2,
      Subtype.val '' (ed ⁻¹' {x : ClosedCell 2 | ‖x.1‖ = 1}) = rim_BCF fib₁ T c (f₂ p))
    (hF1 : ∀ p ∈ Bd ∩ X₂, T p = c → rim_BCF fib₁ T c (f₂ p) = fib₀ (f₁ p))
    (hcover : Bd ⊆ (Bd ∩ X₂) ∪ (Bd ∩ Rc)) (hrim : ∀ p ∈ Bd ∩ X₂, p ∈ Rc ↔ T p = c)
    (Bs : ↥(f₁ '' (Bd ∩ Rc)) → Set H) (d : ∀ y, HalfChart_BCF (Bs y) (f₁ '' (Bd ∩ Rc)))
    (hdO : ∀ y, (y : H) ∈ (d y).O)
    (hE : ∀ y : ↥(f₁ '' (Bd ∩ Rc)), (d y).L y + (d y).κ = 0 ↔
      ∃ p ∈ Bd ∩ X₂, T p = c ∧ f₁ p = y) :
    ∀ x ∈ Bd, ∃ Pt : EmbeddedFacePartition_BCF ↥(connectedComponentIn Bd x),
      (∀ i, ∃ y ∈ f₂ '' (Bd ∩ X₂),
        Subtype.val '' Pt.disk i = connectedComponentIn Bd x ∩ fib₁ y) ∧
      Subtype.val '' (⋃ j, Pt.piece j) = connectedComponentIn Bd x ∩ Rc := by
  classical
  have hS : IsClosed (Bd ∩ Rc) := hBd.inter hRc.isClosed
  have hSX : Bd ∩ Rc ⊆ X₁ := fun p hp => hRcX hp.2
  have hΓ : IsCompact (f₁ '' (Bd ∩ Rc)) :=
    (hRc.inter_left hBd).image_of_continuousOn (hf₁.mono hSX)
  obtain ⟨n, m, a, l, ha, hl, haa, hll, hal, hcov', -, -, hZa, hZl⟩ :=
    exists_components_of_halfCharts_BCF hΓ Bs d hdO
  have hcov : f₁ '' (Bd ∩ Rc) = ⋃ k, compSet_BCF a l k := by
    rw [hcov', Set.iUnion_sum]
    rfl
  have hmemΓ : ∀ k, ∀ y ∈ compSet_BCF a l k, y ∈ f₁ '' (Bd ∩ Rc) := fun k y hy =>
    hcov ▸ mem_iUnion.mpr ⟨k, hy⟩
  refine exists_partition_of_components_BCF hfib₀ hfib₁ hS hRcX hf₁ hsat hB hch hHe hdisk hF1
    hcover hrim ha hl (compSet_disjoint_BCF haa hll hal) hcov
    (Z0 := fun y => ∃ hy : y ∈ f₁ '' (Bd ∩ Rc), (d ⟨y, hy⟩).L y + (d ⟨y, hy⟩).κ = 0) ?_ ?_ ?_
  · intro k y hy
    have hyΓ : y ∈ f₁ '' (Bd ∩ Rc) := hmemΓ (.inl k) y hy
    constructor
    · rintro ⟨hy', h⟩
      exact (hZa k ⟨y, hy'⟩ hy).mp h
    · intro h
      exact ⟨hyΓ, (hZa k ⟨y, hyΓ⟩ hy).mpr h⟩
  · rintro j y hy ⟨hy', h⟩
    have := hZl j ⟨y, hy'⟩ hy
    exact absurd h this.ne'
  · intro y hy
    constructor
    · rintro ⟨hy', h⟩
      exact (hE ⟨y, hy'⟩).mp h
    · intro h
      exact ⟨hy, (hE ⟨y, hy⟩).mpr h⟩

end DifferentialGeometry.Topology.Surface
