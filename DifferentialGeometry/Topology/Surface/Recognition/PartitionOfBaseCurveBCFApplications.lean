import DifferentialGeometry.Topology.Surface.Recognition.PartitionOfBaseCurveBCF

/-!
# Consumer of the base-curve partition assembly (lane S-BCF03b)

The torus `Bd = S¹ × S¹ ⊆ ℝ² × S¹` over the plane base `f₁ = fst`, with no horizontal disk
(`X₂ = ∅`) and the unit circle of the base as the single loop component: the assembly gives an
`EmbeddedFacePartition_BCF` of every component of `Bd`, and it has no disk.
-/

set_option autoImplicit false

open Set Function Topology Metric

noncomputable section

namespace DifferentialGeometry.Topology.Surface

open DifferentialGeometry.Topology

local notation "E2" => EuclideanSpace ℝ (Fin 2)

/-- The unit circle of the plane as a loop `S¹ → ℝ²`. -/
def unitLoop_BCF : Circle → E2 := fun z => (circleSphereHomeomorph_BCF z : E2)

theorem continuous_unitLoop_BCF : Continuous unitLoop_BCF :=
  continuous_subtype_val.comp circleSphereHomeomorph_BCF.continuous

theorem injective_unitLoop_BCF : Injective unitLoop_BCF := fun _ _ h =>
  circleSphereHomeomorph_BCF.injective (Subtype.ext h)

theorem range_unitLoop_BCF : range unitLoop_BCF = sphere (0 : E2) 1 := by
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    exact (circleSphereHomeomorph_BCF z).2
  · intro hy
    obtain ⟨z, hz⟩ := circleSphereHomeomorph_BCF.surjective ⟨y, hy⟩
    exact ⟨z, congrArg Subtype.val hz⟩

/-- **Consumer**: the torus `S¹ × S¹ ⊆ ℝ² × S¹` has an embedded face partition on each of its
components, without disk. -/
theorem torus_partition_example_BCF :
    ∀ x ∈ (sphere (0 : E2) 1 ×ˢ (univ : Set Circle) : Set (E2 × Circle)),
      ∃ Pt : EmbeddedFacePartition_BCF
        ↥(connectedComponentIn (sphere (0 : E2) 1 ×ˢ (univ : Set Circle)) x), Pt.diskCount = 0 := by
  set B : Set (E2 × Circle) := sphere (0 : E2) 1 ×ˢ (univ : Set Circle) with hB
  have hBcl : IsClosed B := isClosed_sphere.prod isClosed_univ
  have hBin : B ∩ B = B := inter_self B
  have himg : Prod.fst '' (B ∩ B) = sphere (0 : E2) 1 := by
    rw [hBin, hB, Set.fst_image_prod _ univ_nonempty]
  have hcomp : (⋃ k : Fin 0 ⊕ Fin 1, compSet_BCF (fun (_ : Fin 0) (_ : ℝ) => (0 : E2))
      (fun _ : Fin 1 => unitLoop_BCF) k) = sphere (0 : E2) 1 := by
    ext y
    simp only [mem_iUnion]
    constructor
    · rintro ⟨k | k, hk⟩
      · exact k.elim0
      · rw [← range_unitLoop_BCF]
        exact hk
    · intro hy
      rw [← range_unitLoop_BCF] at hy
      exact ⟨.inr 0, hy⟩
  have hsat : ∀ p ∈ B ∩ B, ∀ q ∈ (univ : Set (E2 × Circle)), Prod.fst q = Prod.fst p →
      q ∈ B ∩ B := by
    rintro p hp q - hq
    rw [hBin] at hp ⊢
    refine ⟨?_, mem_univ _⟩
    rw [hq]
    exact hp.1
  have hch : ∀ y ∈ Prod.fst '' (B ∩ B), ∃ (σ : E2 → E2) (φ : E2 × Circle → E2 × Circle)
      (O : Set E2) (x₀ : E2), σ x₀ = y ∧ IsEmbedding σ ∧ IsOpen O ∧
      range σ = (univ : Set E2) ∩ O ∧ Continuous φ ∧ Injective φ ∧
      range φ = (univ : Set (E2 × Circle)) ∩ Prod.fst ⁻¹' range σ ∧
      ∀ x z, Prod.fst (φ (x, z)) = σ x := by
    intro y _
    exact ⟨id, id, univ, y, rfl, Topology.IsEmbedding.id, isOpen_univ, by simp, continuous_id,
      injective_id, by simp, fun x z => rfl⟩
  have hHe : ∀ p ∈ B ∩ (∅ : Set (E2 × Circle)), ∀ q ∈ (∅ : Set (E2 × Circle)),
      Prod.fst q = Prod.fst p → q ∈ B ∩ (∅ : Set (E2 × Circle)) := fun _ _ q hq => hq.elim
  have hdisk : ∀ p ∈ B ∩ (∅ : Set (E2 × Circle)),
      ∃ ed : ((∅ : Set (E2 × Circle)) ∩ Prod.fst ⁻¹' {Prod.fst p} : Set (E2 × Circle)) ≃ₜ
        ClosedCell 2, Subtype.val '' (ed ⁻¹' {x : ClosedCell 2 | ‖x.1‖ = 1}) =
        rim_BCF (fun y => (∅ : Set (E2 × Circle)) ∩ Prod.fst ⁻¹' {y}) (fun _ => (0 : ℝ)) 0
          (Prod.fst p) := fun p hp => hp.2.elim
  have key := exists_partition_of_components_BCF (Wt := E2 × Circle) (H := E2)
    (fib₀ := fun y => (univ : Set (E2 × Circle)) ∩ Prod.fst ⁻¹' {y})
    (fib₁ := fun y => (∅ : Set (E2 × Circle)) ∩ Prod.fst ⁻¹' {y}) (f₁ := Prod.fst) (f₂ := Prod.fst)
    (T := fun _ => 0) (c := 0) (X₁ := univ) (X₂ := ∅) (Bd := B) (Rc := B) (B₀ := univ)
    (a := fun (_ : Fin 0) (_ : ℝ) => (0 : E2)) (l := fun _ : Fin 1 => unitLoop_BCF)
    (Z0 := fun _ => False) (fun _ => rfl) (fun _ => rfl) (by rw [hBin]; exact hBcl)
    (subset_univ _) continuous_fst.continuousOn hsat (subset_univ _) hch hHe hdisk
    (fun p hp => hp.2.elim) (fun p hp => Or.inr ⟨hp, hp⟩) (fun p hp => hp.2.elim)
    (fun k => k.elim0) (fun j => ⟨continuous_unitLoop_BCF, injective_unitLoop_BCF⟩)
    (compSet_disjoint_BCF (fun k => k.elim0) (fun j j' h => (h (Subsingleton.elim j j')).elim)
      (fun k => k.elim0))
    (by rw [himg, hcomp]) (fun k => k.elim0) (fun j y hy h => h)
    (fun y _ => ⟨fun h => h.elim, fun ⟨p, hp, _⟩ => hp.2.elim⟩)
  intro x hx
  obtain ⟨Pt, hd, -⟩ := key x hx
  refine ⟨Pt, ?_⟩
  have : IsEmpty (Fin Pt.diskCount) := ⟨fun i => by
    obtain ⟨y, hy, -⟩ := hd i
    obtain ⟨p, hp, -⟩ := hy
    exact hp.2⟩
  have h0 := Fintype.card_eq_zero_iff.mpr this
  rwa [Fintype.card_fin] at h0

end DifferentialGeometry.Topology.Surface
