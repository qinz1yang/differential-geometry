import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySeamFamilies
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.MixedCutSystem

/-!
# Consumer of the seam families: the seam fields of `MixedCutSystem`

`exists_mixedSeamFields_of_regular_levels` turns pairwise disjoint regular torus and sphere faces
into the seam data of the existing `MixedCutSystem` (`Closure/MixedCutSystem.lean:65–96`): the two
families of signed collars with the field statements `torus_seam_source`, `sphere_seam_source`,
`torus_seam_interior`, `sphere_seam_interior`, `torus_seam_disjoint`, `sphere_seam_disjoint` and
`seam_cross_disjoint`, in their exact shapes, together with avoidance of the external torus ports
(the certificate clause `external_protected` for sphere seams).
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

/-- The seam fields of `MixedCutSystem` from pairwise disjoint regular faces. -/
theorem exists_mixedSeamFields_of_regular_levels (W : CompactCarrier.{u}) {m m' : ℕ}
    (U : Fin m → TopologicalSpace.Opens W.Carrier) (hU : ∀ k, (U k : Set W.Carrier) ⊆ W.interior)
    (f : Fin m → W.Carrier → ℝ) (c : Fin m → ℝ)
    (hf : ∀ k, ContMDiffOn W.model 𝓘(ℝ, ℝ) ∞ (f k) (U k))
    (param : Fin m → Torus → W.Carrier)
    (hparam : ∀ k, IsSmoothEmbedding torusModel W.model ∞ (param k))
    (hSU : ∀ k, range (param k) ⊆ U k) (hlev : ∀ k t, f k (param k t) = c k)
    (hreg : ∀ k t, mfderiv W.model 𝓘(ℝ, ℝ) (f k) (param k t) ≠ 0)
    (hiso : ∀ k, ∃ V₀ : Set W.Carrier, IsOpen V₀ ∧ range (param k) ⊆ V₀ ∧
      ∀ x ∈ V₀ ∩ U k, f k x = c k → x ∈ range (param k))
    (U' : Fin m' → TopologicalSpace.Opens W.Carrier)
    (hU' : ∀ j, (U' j : Set W.Carrier) ⊆ W.interior)
    (f' : Fin m' → W.Carrier → ℝ) (c' : Fin m' → ℝ)
    (hf' : ∀ j, ContMDiffOn W.model 𝓘(ℝ, ℝ) ∞ (f' j) (U' j))
    (sparam : Fin m' → ClosureSphere.{u} → W.Carrier)
    (hsparam : ∀ j, IsSmoothEmbedding (𝓡 2) W.model ∞ (sparam j))
    (hSU' : ∀ j, range (sparam j) ⊆ U' j) (hlev' : ∀ j z, f' j (sparam j z) = c' j)
    (hreg' : ∀ j z, mfderiv W.model 𝓘(ℝ, ℝ) (f' j) (sparam j z) ≠ 0)
    (hdisj : Pairwise fun k l => Disjoint (range (param k)) (range (param l)))
    (hdisj' : Pairwise fun j l => Disjoint (range (sparam j)) (range (sparam l)))
    (hcross : ∀ k j, Disjoint (range (param k)) (range (sparam j)))
    {n : ℕ} (E : BoundaryTori W n)
    (hport : ∀ i k, Disjoint (closure (E.collar i).target) (range (param k)))
    (hport' : ∀ i j, Disjoint (closure (E.collar i).target) (range (sparam j))) :
    ∃ (torusSeam : Fin m → PartialDiffeomorph signedCollarModel W.model
        (Torus × ℝ) W.Carrier ∞)
      (sphereSeam : Fin m' → PartialDiffeomorph sphereSignedCollarModel W.model
        (ClosureSphere.{u} × ℝ) W.Carrier ∞),
      (∀ a, (torusSeam a).source = signedCollarSource) ∧
      (∀ a, (sphereSeam a).source = sphereSignedCollarSource) ∧
      (∀ a, (torusSeam a).target ⊆ W.interior) ∧
      (∀ a, (sphereSeam a).target ⊆ W.interior) ∧
      (Pairwise fun a b => Disjoint (torusSeam a).target (torusSeam b).target) ∧
      (Pairwise fun a b => Disjoint (sphereSeam a).target (sphereSeam b).target) ∧
      (∀ a b, Disjoint (torusSeam a).target (sphereSeam b).target) ∧
      (∀ i a, Disjoint (E.collar i).target (torusSeam a).target) ∧
      (∀ i b, Disjoint (E.collar i).target (sphereSeam b).target) ∧
      (∀ a t, torusSeam a (t, 0) = param a t) ∧ ∀ b z, sphereSeam b (z, 0) = sparam b z := by
  obtain ⟨-, -, S, -, -, S', -, -, hd, hd', hx, hp, hp', hz, hz', -, -⟩ :=
    exists_seamFamilies_of_regular_levels W U hU f c hf param hparam hSU hlev hreg hiso U' hU' f'
      c' hf' sparam hsparam hSU' hlev' hreg' hdisj hdisj' hcross E hport hport' univ isOpen_univ
      (fun _ => subset_univ _) (fun _ => subset_univ _)
  exact ⟨fun a => (S a).collar, fun b => (S' b).collar, fun a => (S a).source_eq,
    fun b => (S' b).source_eq, fun a => (S a).target_interior, fun b => (S' b).target_interior,
    hd, hd', hx, hp, hp', hz, hz'⟩

end GC.GraphManifold.Assembly
