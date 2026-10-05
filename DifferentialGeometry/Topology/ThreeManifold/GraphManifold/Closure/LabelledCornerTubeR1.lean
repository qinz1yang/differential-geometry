import DifferentialGeometry.Geometry.Collapse.EdgeDisk.CornerTube
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0Base

/-!
# Consumer of R0 / R1: the per-endpoint fields of the rows' `LabelledCornerTubes`

Draft 74 §3.8 / D74-14: for an actual edge endpoint `e`, `LabelledCornerTubes`
(`FC39P0Junctions.lean`) asks for an open base `V_e` of the row circle bundle `R` containing the rim
base point, a corner chart `PartialDiffeomorph (𝓡 2) 𝓘(ℝ, ℝ × ℝ) R.Base (ℝ × ℝ) ∞` with source
`V_e` and centre `(0, 0)`, the whole tube `R.tube V_e` inside the edge source and the residual
buffer, the height and face identities `chart₁ = height - level`, `chart₂ = h_F`, and the three
whole-tube sides (`vertex ↔ y ≤ 0`, `edge component ↔ y ≥ 0 ∧ x ≤ 0`, `M₃ ↔ x ≥ 0 ∧ y ≥ 0`).
`labelledCornerTube_fields_EFC` produces exactly these fields (for one endpoint, on the actual
`CircleBundle` structure) from R1's inputs: a closed circle projection, descent of `(T, h_F)` over
a base patch, rank two at one point of the rim fibre, and the sign model on an ambient
neighbourhood of the whole rim fibre inside the edge source and the residual buffer.
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter Manifold
open scoped ContDiff Manifold Topology
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint

namespace GC.GraphManifold.Assembly.FC39P0

universe u

/-- **R1 ⇒ the `LabelledCornerTubes` fields at one endpoint.** For the row circle bundle `R` with a
closed projection, a function `T` equal to `height - level` on the edge source, a residual function
`h_F`, both descending over a base patch `V ∋ c₀` to smooth `T̄`, `h̄` vanishing at `c₀`, with
`d(T, h_F)` of rank two at a point of the fibre over `c₀`, and an open neighbourhood `N` of that
whole fibre inside the edge source and the residual buffer carrying the sign model: there are an
open base `V_e ∋ c₀` and a corner chart with every per-endpoint field of `LabelledCornerTubes`. -/
theorem labelledCornerTube_fields_EFC (W : CompactCarrier.{u}) (R : CircleBundle W)
    (hcl : IsClosedMap R.proj) (source : TopologicalSpace.Opens W.Carrier) (height : source → ℝ)
    (level : ℝ) (res : R.domain → ℝ) (near : Set W.Carrier) {Vtx Edg Reg : Set W.Carrier}
    (c₀ : R.Base) {T : R.domain → ℝ}
    (hT : ∀ (x : R.domain) (hx : (x : W.Carrier) ∈ source), T x = height ⟨x, hx⟩ - level)
    {V : TopologicalSpace.Opens R.Base} (hc₀ : c₀ ∈ V) {Tb hb : R.Base → ℝ}
    (hTb : ContMDiffOn (𝓡 2) 𝓘(ℝ) ∞ Tb V) (hhb : ContMDiffOn (𝓡 2) 𝓘(ℝ) ∞ hb V)
    (hdesc : ∀ x : R.domain, R.proj x ∈ V → T x = Tb (R.proj x) ∧ res x = hb (R.proj x))
    (hcen : Tb c₀ = 0 ∧ hb c₀ = 0) {x₀ : R.domain} (hx₀ : R.proj x₀ = c₀)
    (hrank : Surjective (mfderiv W.model 𝓘(ℝ, ℝ × ℝ) (fun z => (T z, res z)) x₀))
    {N : Set R.domain} (hN : IsOpen N) (hfib : R.proj ⁻¹' {c₀} ⊆ N)
    (hNs : ∀ x ∈ N, (x : W.Carrier) ∈ source ∧ (x : W.Carrier) ∈ near)
    (hsign : ∀ x ∈ N, ((x : W.Carrier) ∈ Vtx ↔ res x ≤ 0) ∧
      ((x : W.Carrier) ∈ Edg ↔ 0 ≤ res x ∧ T x ≤ 0) ∧
      ((x : W.Carrier) ∈ Reg ↔ 0 ≤ T x ∧ 0 ≤ res x)) :
    ∃ base : TopologicalSpace.Opens R.Base, c₀ ∈ base ∧
      ∃ chart : PartialDiffeomorph (𝓡 2) 𝓘(ℝ, ℝ × ℝ) R.Base (ℝ × ℝ) ∞,
        chart.source = base ∧ chart c₀ = (0, 0) ∧
        R.tube base ⊆ source ∧ R.tube base ⊆ near ∧
        (∀ x : R.domain, R.proj x ∈ base → ∃ hx : (x : W.Carrier) ∈ source,
          (chart (R.proj x)).1 = height ⟨x, hx⟩ - level) ∧
        (∀ x : R.domain, R.proj x ∈ base → (chart (R.proj x)).2 = res x) ∧
        (∀ x : R.domain, R.proj x ∈ base →
          ((x : W.Carrier) ∈ Vtx ↔ (chart (R.proj x)).2 ≤ 0)) ∧
        (∀ x : R.domain, R.proj x ∈ base →
          ((x : W.Carrier) ∈ Edg ↔ 0 ≤ (chart (R.proj x)).2 ∧ (chart (R.proj x)).1 ≤ 0)) ∧
        (∀ x : R.domain, R.proj x ∈ base →
          ((x : W.Carrier) ∈ Reg ↔ 0 ≤ (chart (R.proj x)).1 ∧ 0 ≤ (chart (R.proj x)).2)) := by
  have hEB : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2 := finrank_euclideanSpace_fin
  have hf : MDifferentiableAt W.model (𝓡 2) R.proj x₀ :=
    (R.proj_smooth x₀).mdifferentiableAt (by simp)
  obtain ⟨Φ, hc₀Φ, -, hcen', htube, hcoord, hside⟩ :=
    DifferentialGeometry.Geometry.Collapse.EdgeDisk.exists_whole_corner_tube74 hEB
      R.proj.continuous hcl hc₀ hTb hhb hdesc hcen hx₀ hf hrank hN hfib
      (Vtx := Subtype.val ⁻¹' Vtx) (Edg := Subtype.val ⁻¹' Edg) (Reg := Subtype.val ⁻¹' Reg)
      hsign
  refine ⟨⟨Φ.source, Φ.open_source⟩, hc₀Φ, Φ, rfl, hcen', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact (hNs x (htube hx)).1
  · rintro _ ⟨x, hx, rfl⟩
    exact (hNs x (htube hx)).2
  · intro x hx
    have hxs := (hNs x (htube hx)).1
    exact ⟨hxs, (hcoord x hx).1.trans (hT x hxs)⟩
  · intro x hx
    exact (hcoord x hx).2
  · intro x hx
    exact (hside x hx).1
  · intro x hx
    exact (hside x hx).2.1
  · intro x hx
    exact (hside x hx).2.2

end GC.GraphManifold.Assembly.FC39P0
