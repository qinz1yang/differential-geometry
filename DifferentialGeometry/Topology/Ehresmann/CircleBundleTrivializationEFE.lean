import DifferentialGeometry.Topology.Ehresmann.LocalTriviality
import DifferentialGeometry.Topology.Manifold.OneManifold.CircleConsequences

/-!
# Circle bundles: local triviality of a proper submersion with connected one-dimensional fibres

Lane S-EDP-FDC, group G6 (FDC03 circle bundle, draft 74 D74-13), kernel. The rows' `CircleBundle`
(`FC39P0Base.lean`) asks, over a neighbourhood of every base point, a diffeomorphism
`proj⁻¹(neighbourhood) ≃ₘ neighbourhood × Circle` (models `W.model` and `(𝓡 2).prod (𝓡 1)`) whose
first coordinate is the projection. `exists_circle_trivialization_of_proper_submersion_EFE` is that
statement for an abstract smooth proper submersion `f : M → N` of boundaryless manifolds with
`dim M = dim N + 1` and connected fibres: Ehresmann's local triviality
(`ehresmann_local_triviality`, fibre `f⁻¹(y)` with its regular-fibre structure) composed with the
classification of a compact connected regular fibre of dimension one
(`nonempty_circle_diffeomorph_regularFiber`) and the swap `Circle × Q ≃ₘ Q × Circle`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Topology.Ehresmann

variable {E F H H' M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] [TopologicalSpace H']
  [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace H' N]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
  [I.Boundaryless] [J.Boundaryless] [IsManifold I ∞ M] [IsManifold J ∞ N]

/-- **Local triviality of a proper submersion with connected fibres and one-dimensional fibre
dimension, with the circle as fibre** (the actual `CircleBundle.trivialization` shape): over a
neighbourhood `Q` of every `y`, `f⁻¹(Q) ≃ₘ Q × S¹` by a diffeomorphism whose first coordinate is
`f`. -/
theorem exists_circle_trivialization_of_proper_submersion_EFE
    [T2Space M] [SigmaCompactSpace M] [T2Space N]
    (f : M → N) (hf : ContMDiff I J ∞ f) (hproper : IsProperMap f)
    (hreg : ∀ x, Function.Surjective (mfderiv I J f x))
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F + 1)
    (hconn : ∀ y, IsConnected {x | f x = y}) (y : N) :
    ∃ Q : TopologicalSpace.Opens N, y ∈ Q ∧
      ∃ Ψ : Diffeomorph I (J.prod (𝓡 1))
        (⟨f ⁻¹' Q, Q.isOpen.preimage hf.continuous⟩ : TopologicalSpace.Opens M)
        (Q × Circle) ∞, ∀ x, (Ψ x).1.1 = f x.1 := by
  obtain ⟨Q, hy, Θ, hΘf, -⟩ := ehresmann_local_triviality f hf hproper hreg y
  have hcpt : IsCompact {x | f x = y} := isCompact_fiber_of_isProperMap f hproper y
  obtain ⟨e⟩ :=
    DifferentialGeometry.Topology.Manifold.OneManifold.nonempty_circle_diffeomorph_regularFiber f
      y hf (fun x _ => hreg x) hdim hcpt (hconn y)
  refine ⟨Q, hy, ?_⟩
  let _ := DifferentialGeometry.Topology.Manifold.regularFiberChartedSpace f y hf
    (fun x _ => hreg x)
  let Φ := (e.prodCongr (Diffeomorph.refl J Q ∞)).trans Θ
  refine ⟨Φ.symm.trans (Diffeomorph.prodComm (𝓡 1) J Circle Q ∞), fun x => ?_⟩
  have hx : Φ (Φ.symm x) = x := Φ.apply_symm_apply x
  have h2 := hΘf ((e.prodCongr (Diffeomorph.refl J Q ∞)) (Φ.symm x))
  have h3 : Θ ((e.prodCongr (Diffeomorph.refl J Q ∞)) (Φ.symm x)) = x := hx
  rw [h3] at h2
  exact h2.symm

end DifferentialGeometry.Topology.Ehresmann
