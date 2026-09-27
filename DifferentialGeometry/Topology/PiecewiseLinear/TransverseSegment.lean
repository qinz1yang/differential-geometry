import DifferentialGeometry.Topology.PiecewiseLinear.GeneralPosition
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldConnectivity

open Set Topology Metric

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem exists_transverse_segment_at_openSimplex
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] {s : Finset E} (hs : s ∈ K.faces)
    (hmax : ∀ u ∈ K.faces, s ⊆ u → u.card ≤ s.card) {x : E} (hx : x ∈ openSimplex s)
    (hdim : Module.finrank ℝ E = s.card) :
    ∃ v : E, ∃ r : ℝ, 0 < r ∧ v ∉ vectorSpan ℝ (s : Set E) ∧
      Submodule.span ℝ {v} ⊔ vectorSpan ℝ (s : Set E) = ⊤ ∧
        ∀ t ∈ Icc (-r) r, x + t • v ∈ K.space ↔ t = 0 := by
  obtain ⟨z, hz⟩ := K.nonempty_of_mem_faces hs
  let _ : Nonempty s := ⟨⟨z, hz⟩⟩
  have hrange : range ((↑) : s → E) = (s : Set E) := by ext y; simp
  have hrank : Module.finrank ℝ (vectorSpan ℝ (s : Set E)) + 1 = s.card := by
    have h := (K.indep hs).finrank_vectorSpan_add_one
    change Module.finrank ℝ (vectorSpan ℝ (range ((↑) : s → E))) + 1 = Fintype.card s at h
    rw [hrange] at h
    simpa only [Fintype.card_coe] using h
  have hproper : vectorSpan ℝ (s : Set E) ≠ ⊤ := by
    intro htop
    rw [htop, finrank_top, hdim] at hrank
    omega
  obtain ⟨v, hv⟩ := SetLike.exists_not_mem_of_ne_top (vectorSpan ℝ (s : Set E)) hproper rfl
  have hsup : Submodule.span ℝ {v} ⊔ vectorSpan ℝ (s : Set E) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [sup_comm, Submodule.finrank_sup_span_singleton hv, hrank, hdim]
  have hlocal := eventually_mem_space_iff_sub_mem_vectorSpan K hs hmax hx
  have htend : Filter.Tendsto (fun t : ℝ => x + t • v) (𝓝 0) (𝓝 x) := by
    simpa only [zero_smul, add_zero] using
      (show Continuous (fun t : ℝ => x + t • v) by fun_prop).tendsto 0
  have hline : ∀ᶠ t : ℝ in 𝓝 0, x + t • v ∈ K.space ↔ t = 0 := by
    filter_upwards [htend.eventually hlocal] with t ht
    rw [ht, add_sub_cancel_left]
    constructor
    · intro h
      by_contra ht0
      exact hv ((Submodule.smul_mem_iff _ ht0).mp h)
    · rintro rfl
      simpa only [zero_smul] using (vectorSpan ℝ (s : Set E)).zero_mem
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hline
  refine ⟨v, δ / 2, half_pos hδ, hv, hsup, fun t ht => hball ?_⟩
  rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs]
  exact (abs_le.mpr ht).trans_lt (by linarith)

open Classical in
theorem IsCombinatorialManifold.exists_transverse_segment
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold 2 K) (hdim : Module.finrank ℝ E = 3)
    (hne : K.space.Nonempty) :
    ∃ s ∈ K.faces, ∃ x ∈ openSimplex s, ∃ v : E, ∃ r : ℝ,
      s.card = 3 ∧ 0 < r ∧ v ∉ vectorSpan ℝ (s : Set E) ∧
        Submodule.span ℝ {v} ⊔ vectorSpan ℝ (s : Set E) = ⊤ ∧
          ∀ t ∈ Icc (-r) r, x + t • v ∈ K.space ↔ t = 0 := by
  obtain ⟨p, hp⟩ := hne
  obtain ⟨a, ha, _⟩ := K.mem_space_iff.mp hp
  obtain ⟨s, hs, _, hcard⟩ :=
    hK.isCombinatorialManifoldWithBoundary.exists_face_superset_card_eq ha
  have hmax : ∀ u ∈ K.faces, s ⊆ u → u.card ≤ s.card := by
    intro u hu _
    rw [hcard]
    exact hK.card_le K hu
  have hx := centroid_mem_openSimplex (K.nonempty_of_mem_faces hs)
  obtain ⟨v, r, hr, hv, hspan, hline⟩ :=
    exists_transverse_segment_at_openSimplex K hs hmax hx (hdim.trans hcard.symm)
  exact ⟨s, hs, s.centroid ℝ id, hx, v, r, hcard, hr, hv, hspan, hline⟩

end DifferentialGeometry.Topology.PiecewiseLinear
