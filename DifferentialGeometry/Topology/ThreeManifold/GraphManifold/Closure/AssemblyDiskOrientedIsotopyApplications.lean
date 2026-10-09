import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyDiskOrientedIsotopy

/-!
# Consumer of D2S1 input (b): orientation and isotopy of disk diffeomorphisms

A diffeomorphism of the closed disk preserves a given orientation if and only if it is smoothly
isotopic to the identity (constant near the ends, inverses jointly smooth): `→` is input (b); `←` is
the isotopy-orientation lemma for manifolds with boundary (`IsotopyOrientationModel.lean`).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology Manifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly

local instance diskChartsOrientedApp_D2S1C : ChartedSpace (EuclideanHalfSpace 2) (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 1

local instance diskSmoothOrientedApp_D2S1C : IsManifold (𝓡∂ 2) ∞ (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellIsManifold 1

local instance closedCellPreconnectedOrientedApp_D2S1C : PreconnectedSpace (ClosedCell 2) :=
  closedCell_two_preconnectedSpace

/-- A disk diffeomorphism preserves the orientation `o` iff it is smoothly isotopic to the identity. -/
theorem preservesOrientation_iff_exists_diskIsotopy
    (o : ManifoldOrientation (𝓡∂ 2) (ClosedCell 2) 2)
    {μ : ClosedCell 2 ≃ₘ⟮𝓡∂ 2, 𝓡∂ 2⟯ ClosedCell 2} :
    μ.preservesOrientation o o ↔
      ∃ K : ℝ → (ClosedCell 2 ≃ₘ⟮𝓡∂ 2, 𝓡∂ 2⟯ ClosedCell 2),
        ContMDiff ((𝓡∂ 2).prod 𝓘(ℝ, ℝ)) (𝓡∂ 2) ∞ (fun x : ClosedCell 2 × ℝ => K x.2 x.1) ∧
        ContMDiff ((𝓡∂ 2).prod 𝓘(ℝ, ℝ)) (𝓡∂ 2) ∞ (fun x : ClosedCell 2 × ℝ => (K x.2).symm x.1) ∧
        ∃ ε : ℝ, 0 < ε ∧ (∀ t x, t < ε → K t x = x) ∧ (∀ t x, 1 - ε < t → K t x = μ x) := by
  refine ⟨exists_diskIsotopy_from_refl_of_preservesOrientation o μ, ?_⟩
  rintro ⟨K, hK, -, ε, hε, hlo, hhi⟩
  have hK0 : K 0 = Diffeomorph.refl (𝓡∂ 2) (ClosedCell 2) ∞ :=
    Diffeomorph.ext fun x => hlo 0 x hε
  have hswap : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡∂ 2)) ((𝓡∂ 2).prod 𝓘(ℝ, ℝ)) ∞
      (fun q : ℝ × ClosedCell 2 => (q.2, q.1)) := contMDiff_snd.prodMk contMDiff_fst
  have hKc := hK.comp hswap
  have hK1 := DifferentialGeometry.Topology.Manifold.preservesOrientation_of_contMDiff_isotopy
    o K hK0 hKc 1
  have hK1eq : K 1 = μ := Diffeomorph.ext fun x => hhi 1 x (by linarith)
  rwa [hK1eq] at hK1

end GC.GraphManifold.Assembly
