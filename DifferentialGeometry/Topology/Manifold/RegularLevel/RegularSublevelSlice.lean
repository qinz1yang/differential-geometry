import DifferentialGeometry.Topology.Manifold.RegularLevel.HalfSpaceSliceCharts

/-!
# Regular sublevels `{Ψ = 0, 0 ≤ B}` as manifolds with boundary

For a boundaryless ambient `M`, `Ψ : M → G` and `B : M → ℝ` smooth with `dΨ` onto on
`{Ψ = 0, 0 ≤ B}` and `d(Ψ, B)` onto on `{Ψ = 0, B = 0}`, the set `{Ψ = 0, 0 ≤ B}` carries a
manifold-with-boundary structure modelled on `𝓡∂ (d + 1)` (`finrank E = d + 1 + finrank G`), with
boundary `{B = 0}`, smooth immersive inclusion, and the universal property for maps into it.
-/

set_option autoImplicit false
noncomputable section
open Set Function Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Manifold.RegularLevel

section RegularSublevel

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  {d : ℕ}

theorem regularSublevel_sliceCharts (hdim : Module.finrank ℝ E = d + 1 + Module.finrank ℝ G)
    {Ψ : M → G} (hΨ : ContMDiff I 𝓘(ℝ, G) ∞ Ψ) {B : M → ℝ} (hB : ContMDiff I 𝓘(ℝ, ℝ) ∞ B)
    (hreg : ∀ x, Ψ x = 0 → 0 ≤ B x → Surjective (mfderiv I 𝓘(ℝ, G) Ψ x))
    (hregb : ∀ x, Ψ x = 0 → B x = 0 →
      Surjective (mfderiv I 𝓘(ℝ, G × ℝ) (fun y => (Ψ y, B y)) x)) :
    ∀ x, (Ψ x = 0 ∧ 0 ≤ B x) → ∃ p : PartialDiffeomorph I ((𝓡∂ (d + 1)).prod 𝓘(ℝ, G)) M
        (EuclideanHalfSpace (d + 1) × G) ∞ × ℝ,
      0 ≤ p.2 ∧ x ∈ p.1.source ∧
      (∀ y ∈ p.1.source, (Ψ y = 0 ∧ 0 ≤ B y) ↔ ((p.1 y).2 = 0 ∧ p.2 ≤ (p.1 y).1.1 0)) ∧
      ((p.1 x).1.1 0 = p.2 ↔ B x = 0) := by
  intro x hx
  have hint : I.IsInteriorPoint x := BoundarylessManifold.isInteriorPoint
  rcases hx.2.eq_or_lt with h0 | hpos
  · obtain ⟨Φ, hxΦ, hΦ1, hΦ⟩ :=
      exists_sliceChart_of_zero hdim hΨ hB hint h0.symm (hregb x hx.1 h0.symm)
    exact ⟨(Φ, 1), zero_le_one, hxΦ, hΦ, iff_of_true hΦ1 h0.symm⟩
  · obtain ⟨Φ, hxΦ, hΦpos, hΦ⟩ := exists_sliceChart_of_pos hdim hΨ hB hint hpos (hreg x hx.1 hx.2)
    exact ⟨(Φ, 0), le_rfl, hxΦ, hΦ, iff_of_false (hΦpos x hxΦ).ne' hpos.ne'⟩

/-- The manifold-with-boundary structure on a regular sublevel `{Ψ = 0, 0 ≤ B}`. -/
@[reducible]
def regularSublevelChartedSpace (hdim : Module.finrank ℝ E = d + 1 + Module.finrank ℝ G)
    {Ψ : M → G} (hΨ : ContMDiff I 𝓘(ℝ, G) ∞ Ψ) {B : M → ℝ} (hB : ContMDiff I 𝓘(ℝ, ℝ) ∞ B)
    (hreg : ∀ x, Ψ x = 0 → 0 ≤ B x → Surjective (mfderiv I 𝓘(ℝ, G) Ψ x))
    (hregb : ∀ x, Ψ x = 0 → B x = 0 →
      Surjective (mfderiv I 𝓘(ℝ, G × ℝ) (fun y => (Ψ y, B y)) x)) :
    ChartedSpace (EuclideanHalfSpace (d + 1)) {x : M // Ψ x = 0 ∧ 0 ≤ B x} :=
  sliceChartedSpace (fun x => Ψ x = 0 ∧ 0 ≤ B x) (fun x => B x = 0)
    (regularSublevel_sliceCharts hdim hΨ hB hreg hregb)

variable (hdim : Module.finrank ℝ E = d + 1 + Module.finrank ℝ G)
  {Ψ : M → G} (hΨ : ContMDiff I 𝓘(ℝ, G) ∞ Ψ) {B : M → ℝ} (hB : ContMDiff I 𝓘(ℝ, ℝ) ∞ B)
  (hreg : ∀ x, Ψ x = 0 → 0 ≤ B x → Surjective (mfderiv I 𝓘(ℝ, G) Ψ x))
  (hregb : ∀ x, Ψ x = 0 → B x = 0 →
    Surjective (mfderiv I 𝓘(ℝ, G × ℝ) (fun y => (Ψ y, B y)) x))

theorem regularSublevel_isManifold :
    letI := regularSublevelChartedSpace hdim hΨ hB hreg hregb
    IsManifold (𝓡∂ (d + 1)) ∞ {x : M // Ψ x = 0 ∧ 0 ≤ B x} :=
  slice_isManifold _ _ (regularSublevel_sliceCharts hdim hΨ hB hreg hregb)

theorem regularSublevel_contMDiff_val :
    letI := regularSublevelChartedSpace hdim hΨ hB hreg hregb
    ContMDiff (𝓡∂ (d + 1)) I ∞ (Subtype.val : {x : M // Ψ x = 0 ∧ 0 ≤ B x} → M) :=
  slice_contMDiff_val _ _ (regularSublevel_sliceCharts hdim hΨ hB hreg hregb)

theorem regularSublevel_isBoundaryPoint_iff {x : {x : M // Ψ x = 0 ∧ 0 ≤ B x}} :
    letI := regularSublevelChartedSpace hdim hΨ hB hreg hregb
    (𝓡∂ (d + 1)).IsBoundaryPoint x ↔ B x = 0 :=
  slice_isBoundaryPoint_iff (regularSublevel_sliceCharts hdim hΨ hB hreg hregb)

theorem regularSublevel_mfderiv_val_injective (x : {x : M // Ψ x = 0 ∧ 0 ≤ B x}) :
    letI := regularSublevelChartedSpace hdim hΨ hB hreg hregb
    Injective (mfderiv (𝓡∂ (d + 1)) I (Subtype.val : {x : M // Ψ x = 0 ∧ 0 ≤ B x} → M) x) :=
  slice_mfderiv_val_injective _ _ (regularSublevel_sliceCharts hdim hΨ hB hreg hregb) x

theorem regularSublevel_contMDiff_iff {F' G' N : Type*} [NormedAddCommGroup F']
    [NormedSpace ℝ F'] [TopologicalSpace G'] {J : ModelWithCorners ℝ F' G'} [TopologicalSpace N]
    [ChartedSpace G' N] {n : ℕ∞} {g : N → {x : M // Ψ x = 0 ∧ 0 ≤ B x}} :
    letI := regularSublevelChartedSpace hdim hΨ hB hreg hregb
    ContMDiff J (𝓡∂ (d + 1)) n g ↔ ContMDiff J I n (fun z => (g z : M)) :=
  slice_contMDiff_iff (regularSublevel_sliceCharts hdim hΨ hB hreg hregb)
    (WithTop.coe_le_coe.mpr le_top)

end RegularSublevel

end DifferentialGeometry.Manifold.RegularLevel
