import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyDiskSmale
import DifferentialGeometry.Topology.Manifold.ClosedDiskRimCollar.Straighten

/-!
# Chapter-14 assembly, D2S1 input (b2): collar straightening rel the rim

Frozen input (b2) of the assembly step D2S1 (`build-logs/scratch/ASM-D2S1/D2S1Inputs.lean`): a
diffeomorphism of the closed disk fixing the rim pointwise is smoothly isotopic, through
diffeomorphisms fixing the rim pointwise, to one that is the identity on an open neighbourhood of
the rim. The isotopy is jointly smooth with jointly smooth inverses, equals `μ` for `t < ε` and is
the identity near the rim for `t > 1 - ε`.

Deviation from the frozen text (decision (A) of the lead): the orientation `o` and the hypothesis
`hμ : μ.preservesOrientation o o` are dropped. A rim-fixing diffeomorphism needs no orientation
hypothesis, and keeping `hμ` unused would fail the `unusedArguments` linter. The verbatim frozen
text is kept as an `example` in `AssemblyDiskRimApplications.lean`.

Proof: the dimension-two case of
`DifferentialGeometry.Topology.Manifold.exists_closedCell_isotopy_to_identity_near_boundary_of_fix_boundary`
(`Topology/Manifold/ClosedDiskRimCollar/Straighten.lean`), with `diskRim = {x | ‖x‖ = 1}`
(`mem_diskRim_iff`) and `ε = 1/3`.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly

local instance diskChartsRim_D2S1RIM : ChartedSpace (EuclideanHalfSpace 2) (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 1

local instance diskSmoothRim_D2S1RIM : IsManifold (𝓡∂ 2) ∞ (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellIsManifold 1

/-- **(b2) Collar straightening rel the rim.** A disk diffeomorphism fixing the rim pointwise is
isotopic, rel the rim, to one that is the identity near the rim: the isotopy `K` is jointly smooth
with jointly smooth inverses, fixes the rim pointwise at every time, equals `μ` for `t < ε` and is
the identity on an open neighbourhood `N` of the rim for `t > 1 - ε`. (Frozen statement (b2)
without the redundant orientation hypothesis.) -/
theorem exists_diskIsotopy_to_identity_near_rim_of_fix_rim
    (μ : ClosedCell 2 ≃ₘ⟮𝓡∂ 2, 𝓡∂ 2⟯ ClosedCell 2)
    (hrim : ∀ x ∈ diskRim, μ x = x) :
    ∃ K : ℝ → (ClosedCell 2 ≃ₘ⟮𝓡∂ 2, 𝓡∂ 2⟯ ClosedCell 2),
      ContMDiff ((𝓡∂ 2).prod 𝓘(ℝ, ℝ)) (𝓡∂ 2) ∞ (fun x : ClosedCell 2 × ℝ => K x.2 x.1) ∧
      ContMDiff ((𝓡∂ 2).prod 𝓘(ℝ, ℝ)) (𝓡∂ 2) ∞ (fun x : ClosedCell 2 × ℝ => (K x.2).symm x.1) ∧
      (∀ t, ∀ x ∈ diskRim, K t x = x) ∧
      ∃ ε : ℝ, 0 < ε ∧ (∀ t x, t < ε → K t x = μ x) ∧
        ∃ N : Set (ClosedCell 2), IsOpen N ∧ diskRim ⊆ N ∧ ∀ t, ∀ x ∈ N, 1 - ε < t → K t x = x := by
  obtain ⟨K, hK, hKi, hfix, hlo, N, hN, hSN, hhi⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_closedCell_isotopy_to_identity_near_boundary_of_fix_boundary
      (m := 1) μ (fun x hx => hrim x (mem_diskRim_iff.mpr hx))
  refine ⟨K, hK, hKi, fun t x hx => hfix t x (mem_diskRim_iff.mp hx), 1 / 3, by norm_num,
    fun t x ht => hlo t x ht.le, N, hN, fun x hx => hSN (mem_diskRim_iff.mp hx), ?_⟩
  intro t x hx ht
  exact hhi t x hx (by linarith)

end GC.GraphManifold.Assembly
