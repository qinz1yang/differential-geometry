import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyDiskSmale

/-!
# Chapter-14 assembly, SM-D consumer: the mapping-torus form of the disk isotopy

Consumer of `AssemblyDiskSmale.lean` (lane ASM-D2S1). D2S1 descends an isotopy from the identity to
the monodromy to the mapping torus; this is the shape it needs: time reversed (identity near `0`,
`φ` near `1`), every stage fixing the whole rim, and both the family and its inverses jointly smooth.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology Manifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly

local instance diskChartsApp_ASMD2S1 : ChartedSpace (EuclideanHalfSpace 2) (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 1

local instance diskSmoothApp_ASMD2S1 : IsManifold (𝓡∂ 2) ∞ (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellIsManifold 1

/-- **SM-D, mapping-torus form.** A diffeomorphism of the closed disk that is the identity near the
rim is reached from the identity by a jointly smooth isotopy (with jointly smooth inverses) that
fixes the rim at every time, is the identity for `t < ε` and is `φ` for `t > 1 − ε`. -/
theorem exists_diskIsotopy_from_refl_fixing_rim
    (φ : ClosedCell 2 ≃ₘ⟮𝓡∂ 2, 𝓡∂ 2⟯ ClosedCell 2) (N : Set (ClosedCell 2)) (hN : IsOpen N)
    (hrim : diskRim ⊆ N) (hφ : ∀ x ∈ N, φ x = x) :
    ∃ K : ℝ → (ClosedCell 2 ≃ₘ⟮𝓡∂ 2, 𝓡∂ 2⟯ ClosedCell 2),
      ContMDiff ((𝓡∂ 2).prod 𝓘(ℝ, ℝ)) (𝓡∂ 2) ∞ (fun p : ClosedCell 2 × ℝ => K p.2 p.1) ∧
      ContMDiff ((𝓡∂ 2).prod 𝓘(ℝ, ℝ)) (𝓡∂ 2) ∞
        (fun p : ClosedCell 2 × ℝ => (K p.2).symm p.1) ∧
      (∀ t, ∀ x ∈ diskRim, K t x = x) ∧
      ∃ ε : ℝ, 0 < ε ∧ (∀ t x, t < ε → K t x = x) ∧ (∀ t x, 1 - ε < t → K t x = φ x) := by
  obtain ⟨N', -, hrim', -, J, hJ, hJi, -, -, hJfix, ε, hε, hlo, hhi⟩ :=
    exists_diskIsotopy_rel_boundary φ N hN hrim hφ
  have hrev : ContMDiff ((𝓡∂ 2).prod 𝓘(ℝ, ℝ)) ((𝓡∂ 2).prod 𝓘(ℝ, ℝ)) ∞
      (fun p : ClosedCell 2 × ℝ => (p.1, 1 - p.2)) :=
    contMDiff_fst.prodMk (contMDiff_const.sub contMDiff_snd)
  refine ⟨fun t => J (1 - t), hJ.comp hrev, hJi.comp hrev,
    fun t x hx => hJfix _ x (hrim' hx), ε, hε, ?_, ?_⟩
  · intro t x ht
    exact hhi _ x (by linarith)
  · intro t x ht
    exact hlo _ x (by linarith)

end GC.GraphManifold.Assembly
