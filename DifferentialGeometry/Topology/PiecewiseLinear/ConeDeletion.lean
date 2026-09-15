import DifferentialGeometry.Topology.PiecewiseLinear.ConeFreeFace
import DifferentialGeometry.Topology.PiecewiseLinear.TetrahedronDeletion
import DifferentialGeometry.Topology.PiecewiseLinear.TriangleDeletion

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem mem_coneComplex_eraseTriangleComplex_tetrahedron_iff [dE : DecidableEq E]
    (K : Geometry.SimplicialComplex ℝ E) {p : E} (hp : IsConeBase p K)
    (hcard : ∀ s ∈ K.faces, s.card ≤ 3) {t : Finset E} (ht : t ∈ K.faces)
    {u : Finset E} (hucard : u.card = 4) :
    u ∈ (coneComplex (hp.of_faces_subset (eraseTriangleComplex_faces_subset K t))).faces ↔
      u ∈ (coneComplex hp).faces ∧ u ≠ insert p t := by
  classical
  cases Subsingleton.elim dE (Classical.decEq E)
  have hpt : p ∉ t := hp.notMem_face ht
  constructor
  · rintro (hu | rfl | ⟨s, hs, rfl⟩)
    · have hle := hcard u (eraseTriangleComplex_faces_subset K t hu)
      omega
    · simp only [Finset.card_singleton] at hucard
      omega
    · have hsK := eraseTriangleComplex_faces_subset K t hs
      have hps : p ∉ s := hp.notMem_face hsK
      have hscard : s.card = 3 := by
        rw [Finset.card_insert_of_notMem hps] at hucard
        omega
      have hst := ((mem_eraseTriangleComplex_triangle_iff K t hcard hscard).mp hs).2
      refine ⟨Or.inr (Or.inr ⟨s, hsK, rfl⟩), ?_⟩
      intro heq
      have h := congrArg (fun r : Finset E => r.erase p) heq
      rw [Finset.erase_insert hps, Finset.erase_insert hpt] at h
      exact hst h
  · rintro ⟨hu | rfl | ⟨s, hs, rfl⟩, hut⟩
    · have hle := hcard u hu
      omega
    · simp only [Finset.card_singleton] at hucard
      omega
    · have hps : p ∉ s := hp.notMem_face hs
      have hscard : s.card = 3 := by
        rw [Finset.card_insert_of_notMem hps] at hucard
        omega
      refine Or.inr (Or.inr ⟨s, ?_, rfl⟩)
      apply (mem_eraseTriangleComplex_triangle_iff K t hcard hscard).mpr
      exact ⟨hs, fun hst => hut (congrArg (fun r : Finset E => insert p r) hst)⟩

theorem exists_isPLHomeomorphOn_frontier_coneComplex_eraseTriangleComplex
    (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))) [Finite K.faces]
    {p : EuclideanSpace ℝ (Fin 3)} (hp : IsConeBase p K) (hK : IsPLBall 2 K.space)
    {t s : Finset (EuclideanSpace ℝ (Fin 3))} (ht : t ∈ K.faces) (htcard : t.card = 3)
    (hs : s.Nonempty) (hst : s ⊆ t) (hsne : s ≠ t)
    (htrace : (@boundaryComplex _ _ _ (Classical.decEq _) 2 K).space ∩
      convexHull ℝ (t : Set (EuclideanSpace ℝ (Fin 3))) =
        ⋃ v ∈ s, convexHull ℝ ((t.erase v : Finset _) : Set (EuclideanSpace ℝ (Fin 3))))
    (hR : IsPLBall 2 (eraseTriangleComplex K t).space)
    {U : Set (EuclideanSpace ℝ (Fin 3))} (hU : IsOpen U)
    (htU : convexHull ℝ ((insert p t : Finset _) : Set (EuclideanSpace ℝ (Fin 3))) ⊆ U) :
    ∃ h : EuclideanSpace ℝ (Fin 3) ≃ₜ EuclideanSpace ℝ (Fin 3),
      IsPLHomeomorphOn h univ univ ∧
      h '' frontier (@coneComplex _ _ _ (Classical.decEq _) p K hp).space =
        frontier (@coneComplex _ _ _ (Classical.decEq _) p (eraseTriangleComplex K t)
          (hp.of_faces_subset (eraseTriangleComplex_faces_subset K t))).space ∧ EqOn h id Uᶜ := by
  classical
  let _ : DecidableEq (EuclideanSpace ℝ (Fin 3)) := Classical.decEq _
  let R := eraseTriangleComplex K t
  let hpR := hp.of_faces_subset (eraseTriangleComplex_faces_subset K t)
  have hRfin : Finite R.faces := (eraseTriangleComplex_faces_finite K t).to_subtype
  have hCfin : Finite (coneComplex hp).faces := (coneComplex_faces_finite hp (Set.toFinite K.faces)).to_subtype
  have hC'fin : Finite (coneComplex hpR).faces :=
    (coneComplex_faces_finite hpR (eraseTriangleComplex_faces_finite K t)).to_subtype
  have hsub : (coneComplex hpR).faces ⊆ (coneComplex hp).faces := by
    rintro u (hu | rfl | ⟨s, hs, rfl⟩)
    · exact Or.inl (eraseTriangleComplex_faces_subset K t hu)
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr ⟨s, eraseTriangleComplex_faces_subset K t hs, rfl⟩)
  have htop : insert p t ∈ (coneComplex hp).faces := Or.inr (Or.inr ⟨t, ht, rfl⟩)
  have htopcard : (insert p t).card = 4 := by rw [Finset.card_insert_of_notMem (hp.notMem_face ht), htcard]
  have hcard : ∀ s ∈ K.faces, s.card ≤ 3 := fun s hs => card_le_of_isPLBall K hK hs
  have hdelete : ∀ u ∈ (coneComplex hp).faces, u.card = 4 →
      (u ∈ (coneComplex hpR).faces ↔ u ≠ insert p t) := by
    intro u hu hucard
    simpa only [hu, true_and] using mem_coneComplex_eraseTriangleComplex_tetrahedron_iff K hp hcard ht hucard
  exact exists_isPLHomeomorphOn_frontier_of_delete_free_tetrahedron (coneComplex hp) (coneComplex hpR)
    (hp.isPLBall_of_isPLBall hK) (hpR.isPLBall_of_isPLBall hR) hsub htop htopcard hdelete
    (isPLBall_frontier_coneComplex_inter_convexHull_insert (n := 1) (by simp) K hp hK ht htcard
      hs hst hsne (by simpa only [Finset.coe_erase] using htrace)) hU (by simpa only [Finset.coe_insert] using htU)

end DifferentialGeometry.Topology.PiecewiseLinear
