import DifferentialGeometry.Geometry.Collapse.EdgeDisk.CompactDomain
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.EdgeFibreDiskE0

/-!
# Consumer of E1: the rows' `EdgeBundle` base fields from E0's whole disks

Draft 74, D74-11 / §3.4: `EdgeBundle.cbase` = the actual `C₂`, `cbase_compact` = FDC02's compact
base, `cbase_domain` = EDP05's descended face function `b`, `db ≠ 0`, locally `C₂ = {b ≥ 0}`
(`FC39P0Base.lean`). `edgeBundle_cbase_of_wholeDisks_EFC` takes the `fibre_disk` clause in the
rows' exact form (E0's output, `fibreDisk_of_wholeDisk_trace_EFC`), the face condition, FDC02's
compactness and EDP05's descent, on a compact carrier with a one-dimensional base (model `𝓡 1`),
and returns `cbase_compact`, `cbase_domain` for `cbase = proj(M₂ ∩ {height ≤ level})` and the
identity `M₂ ∩ {height ≤ level} = proj⁻¹(cbase) ∩ {height ≤ level}` (`EdgeBundle.edgePiece`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter Manifold
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Topology GC.Endpoint

namespace DifferentialGeometry.Geometry.Collapse.EdgeDisk

open DifferentialGeometry.Topology.Handle in
attribute [local instance] closedCellChartedSpaceSucc closedCellIsManifold

universe u

/-- **E0 ⇒ E1 on the rows' interface**: on a compact carrier, a smooth projection
`proj : source → Base` to a one-dimensional base whose whole fibres below `level` are smooth disks
(`EdgeBundle.fibre_disk`), with the face condition, a compact edge piece (FDC02) and EDP05's descent
at every frontier point of `cbase = proj(M₂ ∩ {height ≤ level})`, satisfies `cbase_compact`,
`cbase_domain` and the `edgePiece` identity. -/
theorem edgeBundle_cbase_of_wholeDisks_EFC (W : CompactCarrier.{u}) {Base : Type*}
    [TopologicalSpace Base] [ChartedSpace (EuclideanSpace ℝ (Fin 1)) Base]
    (source : TopologicalSpace.Opens W.Carrier) (proj : source → Base)
    (hproj : ContMDiff W.model (𝓡 1) ∞ proj) (height : source → ℝ) (level : ℝ)
    (M₂ : Set W.Carrier)
    (hfib : ∀ c : Base, ∃ φ : ClosedCell 2 → W.Carrier,
      IsSmoothEmbedding (𝓡∂ 2) W.model ∞ φ ∧
        range φ = Subtype.val '' {x : source | proj x = c ∧ height x ≤ level})
    (hface : ∀ c, (Subtype.val '' {x : source | proj x = c ∧ height x ≤ level} ∩
      frontier M₂).Nonempty →
      Subtype.val '' {x : source | proj x = c ∧ height x ≤ level} ⊆ M₂)
    (hcpt : IsCompact (M₂ ∩ Subtype.val '' {x : source | height x ≤ level}))
    (hdesc : ∀ c₀ ∈ frontier (proj '' {x : source | (x : W.Carrier) ∈ M₂ ∧ height x ≤ level}),
      ∃ U : TopologicalSpace.Opens Base, c₀ ∈ U ∧ ∃ b : Base → ℝ,
        ContMDiffOn (𝓡 1) 𝓘(ℝ, ℝ) ∞ b U ∧
        (∀ x : source, proj x ∈ U → height x ≤ level →
          ((x : W.Carrier) ∈ M₂ ↔ 0 ≤ b (proj x))) ∧
        ∃ x : source, proj x = c₀ ∧ ∃ F : W.Carrier → ℝ,
          MDifferentiableAt W.model 𝓘(ℝ, ℝ) F x ∧ mfderiv W.model 𝓘(ℝ, ℝ) F x ≠ 0 ∧
          (fun z : source => F z) =ᶠ[𝓝 x] b ∘ proj) :
    IsCompact (proj '' {x : source | (x : W.Carrier) ∈ M₂ ∧ height x ≤ level}) ∧
      M₂ ∩ Subtype.val '' {x : source | height x ≤ level} =
        Subtype.val '' {x : source | proj x ∈
          proj '' {x : source | (x : W.Carrier) ∈ M₂ ∧ height x ≤ level} ∧ height x ≤ level} ∧
      ∀ c ∈ frontier (proj '' {x : source | (x : W.Carrier) ∈ M₂ ∧ height x ≤ level}),
        ∃ U : TopologicalSpace.Opens Base, c ∈ U ∧ ∃ φ : Base → ℝ,
          ContMDiffOn (𝓡 1) 𝓘(ℝ, ℝ) ∞ φ U ∧ φ c = 0 ∧ mfderiv (𝓡 1) 𝓘(ℝ, ℝ) φ c ≠ 0 ∧
          proj '' {x : source | (x : W.Carrier) ∈ M₂ ∧ height x ≤ level} ∩ U =
            {c' | c' ∈ U ∧ 0 ≤ φ c'} :=
  edgeCompactDomain_of_actual_faces74 source proj hproj height level M₂
    (fun c => by
      obtain ⟨φ, hφ, hr⟩ := hfib c
      exact ⟨φ, hφ.contMDiff.continuous, hr⟩) hface hcpt hdesc

end DifferentialGeometry.Geometry.Collapse.EdgeDisk
