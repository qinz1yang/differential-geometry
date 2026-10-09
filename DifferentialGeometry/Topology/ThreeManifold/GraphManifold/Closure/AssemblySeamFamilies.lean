import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySeamCollar

/-!
# Chapter-14 assembly, B2: disjoint, port-avoiding families of seams

Finitely many pairwise disjoint regular faces (tori and spheres, each with its own defining
function) get B2 seams whose collar targets are pairwise disjoint and avoid the full collars of
given external torus ports (design `docs/geometrization/chapter14/design-fc39-fc42-assembly-20261004.md`
§3 "B2-interior": "shrink finitely many disjoint faces so collars are disjoint and avoid external
ports"; §5: external ports are never shrunk, every later operation avoids their whole target).
These are corollaries of `exists_torusSeam_of_regular_level` and
`exists_sphereSeam_of_regular_level`; they are not frozen statements.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

/-- Finitely many pairwise disjoint compact sets in a Hausdorff space have pairwise disjoint open
neighbourhoods. -/
theorem exists_open_separation_of_pairwise_disjoint_compact {X : Type*} [TopologicalSpace X]
    [T2Space X] {ι : Type*} [Finite ι] (K : ι → Set X) (hK : ∀ k, IsCompact (K k))
    (hd : Pairwise fun k l => Disjoint (K k) (K l)) :
    ∃ N : ι → Set X, (∀ k, IsOpen (N k)) ∧ (∀ k, K k ⊆ N k) ∧
      Pairwise fun k l => Disjoint (N k) (N l) := by
  have hsep : ∀ k l, k ≠ l → SeparatedNhds (K k) (K l) :=
    fun k l h => SeparatedNhds.of_isCompact_isCompact (hK k) (hK l) (hd h)
  choose A B hA hB hKA hKB hAB using hsep
  let N : ι → Set X := fun k => ⋂ l, ⋂ h : k ≠ l, A k l h ∩ B l k (Ne.symm h)
  refine ⟨N, fun k => ?_, fun k => ?_, fun k l hkl => ?_⟩
  · exact isOpen_iInter_of_finite fun l => isOpen_iInter_of_finite fun h =>
      (hA k l h).inter (hB l k (Ne.symm h))
  · exact subset_iInter fun l => subset_iInter fun h =>
      subset_inter (hKA k l h) (hKB l k (Ne.symm h))
  · have h1 : N k ⊆ A k l hkl := fun x hx => (mem_iInter₂.mp hx l hkl).1
    have h2 : N l ⊆ B k l hkl := fun x hx => (mem_iInter₂.mp hx k (Ne.symm hkl)).2
    exact (hAB k l hkl).mono h1 h2

/-- The points away from the closures of the full external port collars. -/
def portAvoidingSet {W : CompactCarrier.{u}} {n : ℕ} (E : BoundaryTori W n) : Set W.Carrier :=
  ⋂ i, (closure (E.collar i).target)ᶜ

theorem isOpen_portAvoidingSet {W : CompactCarrier.{u}} {n : ℕ} (E : BoundaryTori W n) :
    IsOpen (portAvoidingSet E) :=
  isOpen_iInter_of_finite fun _ => isClosed_closure.isOpen_compl

theorem disjoint_portAvoidingSet {W : CompactCarrier.{u}} {n : ℕ} (E : BoundaryTori W n)
    (i : Fin n) : Disjoint (E.collar i).target (portAvoidingSet E) := by
  rw [Set.disjoint_left]
  intro y hy hyP
  exact mem_iInter.mp hyP i (subset_closure hy)

theorem subset_portAvoidingSet {W : CompactCarrier.{u}} {n : ℕ} (E : BoundaryTori W n)
    {A : Set W.Carrier} (hA : ∀ i, Disjoint (closure (E.collar i).target) A) :
    A ⊆ portAvoidingSet E :=
  fun _ hx => mem_iInter.mpr fun i hc => (hA i).le_bot ⟨hc, hx⟩

/-- **Disjoint, port-avoiding seam families.** Pairwise disjoint regular torus faces and sphere
faces (each with its own defining function on its own open subset of the interior) get B2 seams
inside `V` whose collar targets are pairwise disjoint (tori, spheres, and across) and disjoint from
every full external port collar. -/
theorem exists_seamFamilies_of_regular_levels (W : CompactCarrier.{u}) {m m' : ℕ}
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
    (hport' : ∀ i j, Disjoint (closure (E.collar i).target) (range (sparam j)))
    (V : Set W.Carrier) (hV : IsOpen V) (hSV : ∀ k, range (param k) ⊆ V)
    (hSV' : ∀ j, range (sparam j) ⊆ V) :
    ∃ (δ : Fin m → ℝ) (_ : ∀ k, 0 < δ k) (S : Fin m → TorusSeam W)
      (δ' : Fin m' → ℝ) (_ : ∀ j, 0 < δ' j) (S' : Fin m' → SphereSeam W),
      (∀ k, (S k).collar.target ⊆ V ∩ U k) ∧ (∀ j, (S' j).collar.target ⊆ V ∩ U' j) ∧
      (Pairwise fun k l => Disjoint (S k).collar.target (S l).collar.target) ∧
      (Pairwise fun j l => Disjoint (S' j).collar.target (S' l).collar.target) ∧
      (∀ k j, Disjoint (S k).collar.target (S' j).collar.target) ∧
      (∀ i k, Disjoint (E.collar i).target (S k).collar.target) ∧
      (∀ i j, Disjoint (E.collar i).target (S' j).collar.target) ∧
      (∀ k t, (S k).collar (t, 0) = param k t) ∧ (∀ j z, (S' j).collar (z, 0) = sparam j z) ∧
      (∀ k, ∀ p ∈ signedCollarSource, f k ((S k).collar p) = c k + δ k * p.2) ∧
      ∀ j, ∀ p ∈ sphereSignedCollarSource, f' j ((S' j).collar p) = c' j + δ' j * p.2 := by
  let K : Fin m ⊕ Fin m' → Set W.Carrier :=
    Sum.elim (fun k => range (param k)) (fun j => range (sparam j))
  have hK : ∀ a, IsCompact (K a) := by
    rintro (k | j)
    · exact isCompact_range (hparam k).contMDiff.continuous
    · exact isCompact_range (hsparam j).contMDiff.continuous
  have hKd : Pairwise fun a b => Disjoint (K a) (K b) := by
    rintro (k | j) (l | l) hab
    · exact hdisj fun h => hab (congrArg Sum.inl h)
    · exact hcross k l
    · exact (hcross l j).symm
    · exact hdisj' fun h => hab (congrArg Sum.inr h)
  obtain ⟨N, hNo, hKN, hNd⟩ := exists_open_separation_of_pairwise_disjoint_compact K hK hKd
  let P := portAvoidingSet E
  have hP := isOpen_portAvoidingSet E
  have ht : ∀ k, ∃ (δ : ℝ) (_ : 0 < δ) (S : TorusSeam W),
      S.collar.target ⊆ (V ∩ N (Sum.inl k) ∩ P) ∩ U k ∧ (∀ t, S.collar (t, 0) = param k t) ∧
      ∀ p ∈ signedCollarSource, f k (S.collar p) = c k + δ * p.2 := fun k =>
    exists_torusSeam_of_regular_level W (U k) (hU k) (f k) (c k) (hf k) (param k) (hparam k)
      (hSU k) (hlev k) (hreg k) (hiso k) _ ((hV.inter (hNo _)).inter hP)
      (subset_inter (subset_inter (hSV k) (hKN (Sum.inl k)))
        (subset_portAvoidingSet E fun i => hport i k))
  have hs : ∀ j, ∃ (δ : ℝ) (_ : 0 < δ) (S : SphereSeam W),
      S.collar.target ⊆ (V ∩ N (Sum.inr j) ∩ P) ∩ U' j ∧ (∀ z, S.collar (z, 0) = sparam j z) ∧
      ∀ p ∈ sphereSignedCollarSource, f' j (S.collar p) = c' j + δ * p.2 := fun j =>
    exists_sphereSeam_of_regular_level W (U' j) (hU' j) (f' j) (c' j) (hf' j) (sparam j)
      (hsparam j) (hSU' j) (hlev' j) (hreg' j) _ ((hV.inter (hNo _)).inter hP)
      (subset_inter (subset_inter (hSV' j) (hKN (Sum.inr j)))
        (subset_portAvoidingSet E fun i => hport' i j))
  choose δ hδ S hS hzero hval using ht
  choose δ' hδ' S' hS' hzero' hval' using hs
  refine ⟨δ, hδ, S, δ', hδ', S', fun k y hy => ⟨(hS k hy).1.1.1, (hS k hy).2⟩,
    fun j y hy => ⟨(hS' j hy).1.1.1, (hS' j hy).2⟩, ?_, ?_, ?_, ?_, ?_, hzero, hzero', hval,
    hval'⟩
  · intro k l hkl
    exact (hNd fun h => hkl (Sum.inl_injective h)).mono (fun y hy => (hS k hy).1.1.2)
      (fun y hy => (hS l hy).1.1.2)
  · intro j l hjl
    exact (hNd fun h => hjl (Sum.inr_injective h)).mono (fun y hy => (hS' j hy).1.1.2)
      (fun y hy => (hS' l hy).1.1.2)
  · intro k j
    exact (hNd Sum.inl_ne_inr).mono (fun y hy => (hS k hy).1.1.2) (fun y hy => (hS' j hy).1.1.2)
  · intro i k
    exact (disjoint_portAvoidingSet E i).mono_right fun y hy => (hS k hy).1.2
  · intro i j
    exact (disjoint_portAvoidingSet E i).mono_right fun y hy => (hS' j hy).1.2

end GC.GraphManifold.Assembly
