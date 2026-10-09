import DifferentialGeometry.Topology.Surface.Recognition.DiskCollarGluing
import DifferentialGeometry.Topology.Surface.Recognition.CircleOpenMap
import DifferentialGeometry.Topology.HighDimensional.TwistedSphere

/-!
# Disk ∪ annulus ∪ disk is a two-sphere, hence not a torus (FC40b, part R2)

Let a Hausdorff space `Y` be the union of two disjoint closed disks `D₁ = h₁(D²)`, `D₂ = h₂(D²)` and an
annulus `A = e(S¹ × [0,1])`, where `D_k` meets `A` exactly in its boundary circle `∂D_k = e(S¹ × {k})`
(equalities of SETS: the boundary parametrizations need not agree).  Then `Y ≃ₜ S²`.  Proof: reparametrize
the annulus so that its `0`-end matches `∂D₁` pointwise, glue `D₁ ∪ A` radially into one disk whose
boundary is `∂D₂` (`exists_disk_of_disk_union_collar`), and apply the twisted-sphere theorem
(`twisted_sphere_homeomorph`).  With R1 (`not_isOpenMap_circle`), `Y` has no open map to the circle, so
it is not a torus.  This is the recognition statement R2 of lane W4-FCb's sheet.
-/

set_option autoImplicit false

open Set Metric Function Topology

namespace DifferentialGeometry.Topology.Surface

open DifferentialGeometry.Topology

variable {Y : Type*} [TopologicalSpace Y] [T2Space Y]

/-- The bottom point of the collar interval. -/
def collarBottom : Icc (0 : ℝ) 1 := ⟨0, left_mem_Icc.mpr zero_le_one⟩

instance compactSpace_disk (n : ℕ) : CompactSpace (Disk n) :=
  isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)

/-- Reparametrize an annulus so that its `0`-end matches the boundary of a disk pointwise. -/
theorem exists_sphere_reparam {h : Disk 2 → Y} (hh : Continuous h) (hh' : Injective h)
    {e : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 × Icc (0 : ℝ) 1 → Y} (he : Continuous e)
    (he' : Injective e) (h1e : h '' diskSphere 2 = e '' {q | (q.2 : ℝ) = 0}) :
    ∃ ψ : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 → sphere (0 : EuclideanSpace ℝ (Fin 2)) 1,
      Continuous ψ ∧ Bijective ψ ∧ ∀ θ, e (ψ θ, collarBottom) = h ⟨θ, sphere_subset_closedBall θ.2⟩ := by
  have hmem : ∀ θ : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1,
      ∃ q : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 × Icc (0 : ℝ) 1, (q.2 : ℝ) = 0 ∧
        e q = h ⟨θ, sphere_subset_closedBall θ.2⟩ := by
    intro θ
    have : h ⟨θ, sphere_subset_closedBall θ.2⟩ ∈ h '' diskSphere 2 :=
      mem_image_of_mem h (mem_diskSphere.mpr (mem_sphere_zero_iff_norm.mp θ.2))
    rw [h1e] at this
    obtain ⟨q, hq, hqe⟩ := this
    exact ⟨q, hq, hqe⟩
  choose q hq0 hqe using hmem
  have hbot : ∀ θ, (q θ).2 = collarBottom := fun θ => Subtype.ext (hq0 θ)
  have hψ : ∀ θ : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1,
      e ((q θ).1, collarBottom) = h ⟨θ, sphere_subset_closedBall θ.2⟩ := by
    intro θ
    rw [← hbot θ, ← hqe θ]
  let g₀ : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 → Y := fun θ => e (θ, collarBottom)
  have hg₀ : IsEmbedding g₀ := by
    have hc : Continuous g₀ := he.comp (continuous_id.prodMk continuous_const)
    have hi : Injective g₀ := fun a b hab => congrArg Prod.fst (he' hab)
    exact (hc.isClosedEmbedding hi).isEmbedding
  refine ⟨fun θ => (q θ).1, ?_, ⟨?_, ?_⟩, hψ⟩
  · rw [hg₀.continuous_iff]
    have : g₀ ∘ (fun θ => (q θ).1) =
        fun θ : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 => h ⟨θ, sphere_subset_closedBall θ.2⟩ :=
      funext hψ
    rw [this]
    exact hh.comp (continuous_subtype_val.subtype_mk _)
  · intro a b hab
    have h2 : h ⟨a, sphere_subset_closedBall a.2⟩ = h ⟨b, sphere_subset_closedBall b.2⟩ := by
      rw [← hψ a, ← hψ b]
      simp only at hab
      rw [hab]
    have h3 := congrArg Subtype.val (hh' h2)
    exact Subtype.ext h3
  · intro θ'
    have : g₀ θ' ∈ e '' {q | (q.2 : ℝ) = 0} := ⟨(θ', collarBottom), rfl, rfl⟩
    rw [← h1e] at this
    obtain ⟨z, hz, hzθ⟩ := this
    let θ : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 :=
      ⟨z, mem_sphere_zero_iff_norm.mpr (mem_diskSphere.mp hz)⟩
    refine ⟨θ, hg₀.injective ?_⟩
    change e ((q θ).1, collarBottom) = g₀ θ'
    rw [hψ θ, ← hzθ]

/-- **FC40b (R2), first half.** Disk ∪ annulus ∪ disk, glued along the two boundary circles, is a
two-sphere. -/
theorem nonempty_homeomorph_sphereTwo_of_disk_annulus_disk {h₁ h₂ : Disk 2 → Y}
    (hh₁ : Continuous h₁) (hh₁' : Injective h₁) (hh₂ : Continuous h₂) (hh₂' : Injective h₂)
    {e : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 × Icc (0 : ℝ) 1 → Y} (he : Continuous e)
    (he' : Injective e) (hcover : range h₁ ∪ range e ∪ range h₂ = univ)
    (h12 : Disjoint (range h₁) (range h₂))
    (h1 : range h₁ ∩ range e = h₁ '' diskSphere 2)
    (h1e : h₁ '' diskSphere 2 = e '' {q | (q.2 : ℝ) = 0})
    (h2 : range h₂ ∩ range e = h₂ '' diskSphere 2)
    (h2e : h₂ '' diskSphere 2 = e '' {q | (q.2 : ℝ) = 1}) :
    Nonempty (Y ≃ₜ SphereTwo) := by
  obtain ⟨ψ, hψc, hψb, hψ⟩ := exists_sphere_reparam hh₁ hh₁' he he' h1e
  let c : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 × Icc (0 : ℝ) 1 → Y := fun w => e (ψ w.1, w.2)
  have hc : Continuous c := he.comp ((hψc.comp continuous_fst).prodMk continuous_snd)
  have hc' : Injective c := by
    intro a b hab
    have := he' hab
    simp only [Prod.mk.injEq] at this
    exact Prod.ext (hψb.1 this.1) this.2
  have hrange : range c = range e := by
    apply Subset.antisymm
    · rintro _ ⟨w, rfl⟩
      exact ⟨_, rfl⟩
    · rintro _ ⟨⟨θ', t⟩, rfl⟩
      obtain ⟨θ, rfl⟩ := hψb.2 θ'
      exact ⟨(θ, t), rfl⟩
  have hmatch : ∀ (θ : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) (t : Icc (0 : ℝ) 1) (z : Disk 2),
      (t : ℝ) = 0 → (z : EuclideanSpace ℝ (Fin 2)) = θ → c (θ, t) = h₁ z := by
    intro θ t z ht hz
    have ht' : t = collarBottom := Subtype.ext ht
    have hz' : z = ⟨θ, sphere_subset_closedBall θ.2⟩ := Subtype.ext hz
    rw [ht', hz']
    exact hψ θ
  have hinter : ∀ z w, h₁ z = c w → (w.2 : ℝ) = 0 := by
    intro z w hzw
    have hmem : h₁ z ∈ range h₁ ∩ range e := ⟨⟨z, rfl⟩, ⟨_, hzw.symm⟩⟩
    rw [h1, h1e] at hmem
    obtain ⟨q, hq, hqe⟩ := hmem
    have h3 := congrArg (fun p => (p.2 : ℝ)) (he' (hqe.trans hzw))
    simp only at h3
    rw [← h3]
    exact hq
  obtain ⟨e₀, he₀, he₀', hr₀, hb₀⟩ := exists_disk_of_disk_union_collar hh₁ hh₁' hc hc' hmatch hinter
  have hb₀' : e₀ '' diskSphere 2 = h₂ '' diskSphere 2 := by
    rw [hb₀, h2e]
    apply Subset.antisymm
    · rintro _ ⟨w, hw, rfl⟩
      exact ⟨(ψ w.1, w.2), hw, rfl⟩
    · rintro _ ⟨⟨θ', t⟩, ht, rfl⟩
      obtain ⟨θ, rfl⟩ := hψb.2 θ'
      exact ⟨(θ, t), ht, rfl⟩
  have key := twisted_sphere_homeomorph (m := 1) (he₀.isClosedEmbedding he₀')
    (hh₂.isClosedEmbedding hh₂') ?_ ?_ hb₀'
  · exact key
  · rw [hr₀, hrange]
    exact hcover
  · rw [hr₀, hrange, union_inter_distrib_right, h12.inter_eq, empty_union, inter_comm, h2, hb₀']

/-- **FC40b (R2).** Disk ∪ annulus ∪ disk has no continuous open map to the circle. -/
theorem not_isOpenMap_circle_of_disk_annulus_disk {h₁ h₂ : Disk 2 → Y}
    (hh₁ : Continuous h₁) (hh₁' : Injective h₁) (hh₂ : Continuous h₂) (hh₂' : Injective h₂)
    {e : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 × Icc (0 : ℝ) 1 → Y} (he : Continuous e)
    (he' : Injective e) (hcover : range h₁ ∪ range e ∪ range h₂ = univ)
    (h12 : Disjoint (range h₁) (range h₂))
    (h1 : range h₁ ∩ range e = h₁ '' diskSphere 2)
    (h1e : h₁ '' diskSphere 2 = e '' {q | (q.2 : ℝ) = 0})
    (h2 : range h₂ ∩ range e = h₂ '' diskSphere 2)
    (h2e : h₂ '' diskSphere 2 = e '' {q | (q.2 : ℝ) = 1})
    {q : Y → Circle} (hq : Continuous q) : ¬ IsOpenMap q := by
  obtain ⟨φ⟩ := nonempty_homeomorph_sphereTwo_of_disk_annulus_disk hh₁ hh₁' hh₂ hh₂' he he'
    hcover h12 h1 h1e h2 h2e
  exact not_isOpenMap_circle_of_homeomorph_sphereTwo φ hq

/-- **FC40b (R2), the sheet's statement.** Disk ∪ annulus ∪ disk is not homeomorphic to the torus. -/
theorem not_nonempty_homeomorph_torus_of_disk_annulus_disk {h₁ h₂ : Disk 2 → Y}
    (hh₁ : Continuous h₁) (hh₁' : Injective h₁) (hh₂ : Continuous h₂) (hh₂' : Injective h₂)
    {e : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 × Icc (0 : ℝ) 1 → Y} (he : Continuous e)
    (he' : Injective e) (hcover : range h₁ ∪ range e ∪ range h₂ = univ)
    (h12 : Disjoint (range h₁) (range h₂))
    (h1 : range h₁ ∩ range e = h₁ '' diskSphere 2)
    (h1e : h₁ '' diskSphere 2 = e '' {q | (q.2 : ℝ) = 0})
    (h2 : range h₂ ∩ range e = h₂ '' diskSphere 2)
    (h2e : h₂ '' diskSphere 2 = e '' {q | (q.2 : ℝ) = 1}) :
    ¬ Nonempty (Y ≃ₜ Circle × Circle) := by
  rintro ⟨φ⟩
  exact not_isOpenMap_circle_of_disk_annulus_disk hh₁ hh₁' hh₂ hh₂' he he' hcover h12 h1 h1e h2
    h2e (continuous_fst.comp φ.continuous) (isOpenMap_fst.comp φ.isOpenMap)

end DifferentialGeometry.Topology.Surface
