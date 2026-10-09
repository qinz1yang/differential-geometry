import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyDiskRim
import DifferentialGeometry.Topology.Manifold.Orientation

/-!
# Chapter-14 assembly, D2S1 input (b2): consumers

* `exists_diskIsotopy_refl_rel_rim_of_fix_rim`: (b2) followed by SM-D
  (`exists_diskIsotopy_rel_boundary`). A disk diffeomorphism fixing the rim pointwise is joined to
  the identity by a jointly smooth isotopy (with jointly smooth inverses) through diffeomorphisms
  fixing the rim pointwise. The two isotopies are combined pointwise,
  `L t = K t ∘ (K 1)⁻¹ ∘ J t`, so no concatenation in time is needed.
* The verbatim frozen statement (b2) of `build-logs/scratch/ASM-D2S1/D2S1Inputs.lean`, with the
  orientation `o` and the redundant hypothesis `hμ`, as an `example`.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly

local instance diskChartsRimApp_D2S1RIM : ChartedSpace (EuclideanHalfSpace 2) (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 1

local instance diskSmoothRimApp_D2S1RIM : IsManifold (𝓡∂ 2) ∞ (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellIsManifold 1

/-- A disk diffeomorphism fixing the rim pointwise is smoothly isotopic to the identity rel the rim:
a jointly smooth isotopy `L` with jointly smooth inverses, `L 0 = μ`, `L 1 = id`, and every `L t`
fixing the rim pointwise. Consumer of (b2) together with SM-D. -/
theorem exists_diskIsotopy_refl_rel_rim_of_fix_rim
    (μ : ClosedCell 2 ≃ₘ⟮𝓡∂ 2, 𝓡∂ 2⟯ ClosedCell 2) (hrim : ∀ x ∈ diskRim, μ x = x) :
    ∃ L : ℝ → (ClosedCell 2 ≃ₘ⟮𝓡∂ 2, 𝓡∂ 2⟯ ClosedCell 2),
      ContMDiff ((𝓡∂ 2).prod 𝓘(ℝ, ℝ)) (𝓡∂ 2) ∞ (fun x : ClosedCell 2 × ℝ => L x.2 x.1) ∧
      ContMDiff ((𝓡∂ 2).prod 𝓘(ℝ, ℝ)) (𝓡∂ 2) ∞ (fun x : ClosedCell 2 × ℝ => (L x.2).symm x.1) ∧
      (∀ x, L 0 x = μ x) ∧ (∀ x, L 1 x = x) ∧ ∀ t, ∀ x ∈ diskRim, L t x = x := by
  obtain ⟨K, hK, hKi, hfix, ε, hε, hlo, N, hN, hSN, hhi⟩ :=
    exists_diskIsotopy_to_identity_near_rim_of_fix_rim μ hrim
  have hK1N : ∀ x ∈ N, K 1 x = x := fun x hx => hhi 1 x hx (by linarith)
  obtain ⟨N', -, hSN', -, J, hJ, hJi, hJ0, hJ1, hJfix, -⟩ :=
    exists_diskIsotopy_rel_boundary (K 1) N hN hSN hK1N
  have hK1s : ∀ x ∈ diskRim, (K 1).symm x = x := fun x hx => by
    have h := (K 1).symm_apply_apply x
    rwa [hfix 1 x hx] at h
  refine ⟨fun t => (J t).trans ((K 1).symm.trans (K t)), ?_, ?_, ?_, ?_, ?_⟩
  · change ContMDiff ((𝓡∂ 2).prod 𝓘(ℝ, ℝ)) (𝓡∂ 2) ∞
      (fun x : ClosedCell 2 × ℝ => K x.2 ((K 1).symm (J x.2 x.1)))
    exact hK.comp (((K 1).symm.contMDiff.comp hJ).prodMk contMDiff_snd)
  · change ContMDiff ((𝓡∂ 2).prod 𝓘(ℝ, ℝ)) (𝓡∂ 2) ∞
      (fun x : ClosedCell 2 × ℝ => (J x.2).symm (K 1 ((K x.2).symm x.1)))
    exact hJi.comp (((K 1).contMDiff.comp hKi).prodMk contMDiff_snd)
  · intro x
    change K 0 ((K 1).symm (J 0 x)) = μ x
    rw [hJ0, Diffeomorph.symm_apply_apply]
    exact hlo 0 x hε
  · intro x
    change K 1 ((K 1).symm (J 1 x)) = x
    rw [hJ1, Diffeomorph.apply_symm_apply]
  · intro t x hx
    change K t ((K 1).symm (J t x)) = x
    rw [hJfix t x (hSN' hx), hK1s x hx, hfix t x hx]

/-- The frozen statement (b2) verbatim (`build-logs/scratch/ASM-D2S1/D2S1Inputs.lean`), with the
orientation `o` and the redundant hypothesis `hμ`, which the proof discards. -/
example (o : ManifoldOrientation (𝓡∂ 2) (ClosedCell 2) 2)
    (μ : ClosedCell 2 ≃ₘ⟮𝓡∂ 2, 𝓡∂ 2⟯ ClosedCell 2) (hμ : μ.preservesOrientation o o)
    (hrim : ∀ x ∈ diskRim, μ x = x) :
    ∃ K : ℝ → (ClosedCell 2 ≃ₘ⟮𝓡∂ 2, 𝓡∂ 2⟯ ClosedCell 2),
      ContMDiff ((𝓡∂ 2).prod 𝓘(ℝ, ℝ)) (𝓡∂ 2) ∞ (fun x : ClosedCell 2 × ℝ => K x.2 x.1) ∧
      ContMDiff ((𝓡∂ 2).prod 𝓘(ℝ, ℝ)) (𝓡∂ 2) ∞ (fun x : ClosedCell 2 × ℝ => (K x.2).symm x.1) ∧
      (∀ t, ∀ x ∈ diskRim, K t x = x) ∧
      ∃ ε : ℝ, 0 < ε ∧ (∀ t x, t < ε → K t x = μ x) ∧
        ∃ N : Set (ClosedCell 2), IsOpen N ∧ diskRim ⊆ N ∧ ∀ t, ∀ x ∈ N, 1 - ε < t → K t x = x :=
  (fun _ => exists_diskIsotopy_to_identity_near_rim_of_fix_rim μ hrim) hμ

end GC.GraphManifold.Assembly
