/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34SubdivisionCarriers

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X] {U : Set X}

theorem exists_section34_graph_refinement_control
    {K T R : LocallyFinitePLPieceIn E 3 X U}
    (hT : IsSubdivision T.complex K.complex) (hTm : T.map = K.map)
    (hR : IsSubdivision R.complex T.complex) (hRm : R.map = T.map) :
    ∃ a : Section34VertexIndex K R → Section34VertexIndex K T,
      (∀ w, Section34CarrierSupport R w.1 ⊆ Section34CarrierSupport T (a w).1) ∧
      ∀ w t, t ∈ K.complex.faces → Section34Incident w.1 t →
        Section34Incident (a w).1 t := by
  classical
  have hvertex (w : Section34VertexIndex K R) :
      ∃ v : Section34VertexIndex K T,
        Section34CarrierSupport R w.1 ⊆ Section34CarrierSupport T v.1 ∧
        ∀ t ∈ K.complex.faces, Section34Incident w.1 t → Section34Incident v.1 t := by
    obtain ⟨p, hwp⟩ := Finset.card_eq_one.mp w.2.2.1
    have hpw : p ∈ w.1 := by rw [hwp]; exact Finset.mem_singleton_self p
    have hpR : p ∈ R.complex.space :=
      R.complex.convexHull_subset_space w.2.1 (subset_convexHull ℝ _ hpw)
    have hpT : p ∈ T.complex.space := hR.space_eq.subset hpR
    let s := carrierFace T.complex p
    have hs : s ∈ T.complex.faces := carrierFace_mem hpT
    have hps : p ∈ openSimplex s := mem_openSimplex_carrierFace hpT
    have hpGraph : R.map p ∈ graphSkeletonSpace K :=
      w.2.2.2 ⟨p, subset_convexHull ℝ _ hpw, rfl⟩
    obtain ⟨t, ⟨ht, hcard⟩, q, hqt, hqp⟩ := mem_iUnion₂.mp hpGraph
    have hqp' : q = p := K.bijOn.injOn (K.complex.convexHull_subset_space ht hqt)
      (hT.space_eq.subset hpT) (by simpa only [hRm, hTm] using hqp)
    have hst := hT.convexHull_subset_of_mem_openSimplex ht hs hps (hqp' ▸ hqt)
    have hsGraph : simplexBody T s ⊆ graphSkeletonSpace K := by
      rintro _ ⟨x, hx, rfl⟩
      exact mem_iUnion₂.mpr ⟨t, ⟨ht, hcard⟩, x, hst hx, (congrFun hTm x).symm⟩
    obtain ⟨v, hvs⟩ := T.complex.nonempty_of_mem_faces hs
    let v' : Section34VertexIndex K T := ⟨{v},
      T.complex.down_closed hs (Finset.singleton_subset_iff.mpr hvs)
        (Finset.singleton_nonempty v), by simp,
      (image_mono (convexHull_mono (by simpa using hvs))).trans hsGraph⟩
    refine ⟨v', ?_, ?_⟩
    · intro x hx
      obtain ⟨p', hp', hx⟩ := mem_iUnion₂.mp hx
      obtain ⟨r, hr, y, hyr, hyx⟩ := mem_iUnion₂.mp hx
      have hpp : p' = p := by simpa only [hwp, Finset.coe_singleton, mem_singleton_iff] using hp'
      subst p'
      obtain ⟨u, hu, hru⟩ := hR.exists_face_subset hr.1
      have hsu : s ⊆ u := carrierFace_subset hpT hu
        (hru (subset_convexHull ℝ _ hr.2))
      exact mem_iUnion₂.mpr ⟨v, by simp [v'], mem_iUnion₂.mpr
        ⟨u, ⟨hu, hsu hvs⟩, y, hru hyr, by rw [← hRm]; exact hyx⟩⟩
    · intro u hu hwu
      have hsu := hT.convexHull_subset_of_mem_openSimplex hu hs hps (hwu hpw)
      have hvu := hsu (subset_convexHull ℝ _ hvs)
      simpa only [v', Section34Incident, Finset.coe_singleton, singleton_subset_iff] using hvu
  choose a hs hi using hvertex
  exact ⟨a, hs, hi⟩

end DifferentialGeometry.Topology.PiecewiseLinear
