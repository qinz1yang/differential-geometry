import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySeamCollar
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.SphereCutCarrier

/-!
# Consumers of the B2-interior seams

Two concrete consumers of `AssemblySeamCollar.lean`.

* `exists_torusSeam_sides_of_regular_level`: the negative half of the produced torus seam lies in
  the sublevel `{f ≤ c}` and the positive half in the superlevel `{c ≤ f}`; this is the shape of the
  side clauses `torusSide_neg` / `torusSide_pos` of the assembly certificate when the two sides are
  the B1-interior and B1-complement pieces of the same function.
* `exists_sphereCutCarrier_of_regular_sphere_level`: a regular sphere level that stays away from
  the closures of the external port collars is cut by the existing sphere-cut theorem
  `exists_sphereCutCarrier` (`SphereCutCarrier.lean:2512`), the cut sphere collars being the two
  halves of the produced seam.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

/-- The two halves of a B2 torus seam lie on the two sides of the level. -/
theorem exists_torusSeam_sides_of_regular_level (W : CompactCarrier.{u})
    (U : TopologicalSpace.Opens W.Carrier) (hU : (U : Set W.Carrier) ⊆ W.interior)
    (f : W.Carrier → ℝ) (c : ℝ) (hf : ContMDiffOn W.model 𝓘(ℝ, ℝ) ∞ f U)
    (param : Torus → W.Carrier) (hparam : IsSmoothEmbedding torusModel W.model ∞ param)
    (hSU : range param ⊆ U) (hlev : ∀ t, f (param t) = c)
    (hreg : ∀ t, mfderiv W.model 𝓘(ℝ, ℝ) f (param t) ≠ 0)
    (hiso : ∃ V₀ : Set W.Carrier, IsOpen V₀ ∧ range param ⊆ V₀ ∧
      ∀ x ∈ V₀ ∩ U, f x = c → x ∈ range param)
    (V : Set W.Carrier) (hV : IsOpen V) (hSV : range param ⊆ V) :
    ∃ S : TorusSeam W, S.collar.target ⊆ V ∩ U ∧ (∀ t, S.collar (t, 0) = param t) ∧
      (∀ t s, -1 < s → s ≤ 0 → f (S.collar (t, s)) ≤ c) ∧
      ∀ t s, 0 ≤ s → s < 1 → c ≤ f (S.collar (t, s)) := by
  obtain ⟨δ, hδ, S, hT, hzero, hval⟩ :=
    exists_torusSeam_of_regular_level W U hU f c hf param hparam hSU hlev hreg hiso V hV hSV
  refine ⟨S, hT, hzero, fun t s hs1 hs0 => ?_, fun t s hs0 hs1 => ?_⟩
  · rw [hval (t, s) ⟨hs1, by linarith⟩]
    nlinarith
  · rw [hval (t, s) ⟨by linarith, hs1⟩]
    nlinarith

/-- A regular sphere level away from the external port collars is cut by the existing sphere-cut
theorem; the cut sphere collars are the two halves of the B2 seam. -/
theorem exists_sphereCutCarrier_of_regular_sphere_level (W : CompactCarrier.{u})
    (U : TopologicalSpace.Opens W.Carrier) (hU : (U : Set W.Carrier) ⊆ W.interior)
    (f : W.Carrier → ℝ) (c : ℝ) (hf : ContMDiffOn W.model 𝓘(ℝ, ℝ) ∞ f U)
    (param : ClosureSphere.{u} → W.Carrier) (hparam : IsSmoothEmbedding (𝓡 2) W.model ∞ param)
    (hSU : range param ⊆ U) (hlev : ∀ z, f (param z) = c)
    (hreg : ∀ z, mfderiv W.model 𝓘(ℝ, ℝ) f (param z) ≠ 0)
    {n : ℕ} (E : BoundaryTori W n) (hE : W.model.boundary W.Carrier = E.image)
    (hport : ∀ i, Disjoint (closure (E.collar i).target) (range param)) :
    ∃ (S : SphereSeam W) (C : CompactCarrier.{u}) (B : MixedBoundaryCertificate C)
      (_ : B.torusCount = n) (h2 : B.sphereCount = 2) (fold : C.Carrier → W.Carrier),
      (∀ z, S.collar (z, 0) = param z) ∧ (∀ i, Disjoint (E.collar i).target S.collar.target) ∧
      C.kind = .withBoundary ∧ ContMDiff C.model W.model ∞ fold ∧ Surjective fold ∧
      ∀ i z s (hs0 : 0 ≤ s), s < 1 →
        fold (B.sphere (Fin.cast h2.symm i) (z, halfPoint s hs0)) =
          S.collar (z, if i.val = 0 then s else -s) := by
  let V : Set W.Carrier := ⋂ i, (closure (E.collar i).target)ᶜ
  have hV : IsOpen V := isOpen_iInter_of_finite fun i => isClosed_closure.isOpen_compl
  have hSV : range param ⊆ V :=
    fun x hx => mem_iInter.mpr fun i => fun hc => (hport i).le_bot ⟨hc, hx⟩
  obtain ⟨δ, -, S, hT, hzero, -⟩ :=
    exists_sphereSeam_of_regular_level W U hU f c hf param hparam hSU hlev hreg V hV hSV
  have havoid : ∀ i, Disjoint (E.collar i).target S.collar.target := by
    intro i
    rw [Set.disjoint_left]
    intro y hy hyS
    exact mem_iInter.mp (hT hyS).1 i (subset_closure hy)
  obtain ⟨C, B, hn, h2, fold, hkind, hsmooth, hsurj, -, -, hsphere, -⟩ :=
    exists_sphereCutCarrier W S.collar S.source_eq S.target_interior E hE havoid
  exact ⟨S, C, B, hn, h2, fold, hzero, havoid, hkind, hsmooth, hsurj, hsphere⟩

end GC.GraphManifold.Assembly
