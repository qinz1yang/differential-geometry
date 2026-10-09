/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LinkDimension
import DifferentialGeometry.Topology.PiecewiseLinear.SimplexBall
import DifferentialGeometry.Topology.PiecewiseLinear.Triangulation
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.SingularSetOfCrossing

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem card_le_two_of_locally_injOn_into_line
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (G : Geometry.SimplicialComplex ℝ E)
    (hgerm : ∀ x ∈ G.space, ∃ (g : E → F) (L : Submodule ℝ F) (S : Set E),
      Module.finrank ℝ L = 1 ∧ S ∈ 𝓝[G.space] x ∧ IsPiecewiseAffineOn g S ∧ InjOn g S ∧
        ∀ z ∈ S, z ∈ G.space → g z ∈ L)
    {s : Finset E} (hs : s ∈ G.faces) : s.card ≤ 2 := by
  classical
  by_contra hcon
  obtain ⟨x, hxopen⟩ : ∃ x, x ∈ openSimplex s :=
    ⟨_, centroid_mem_openSimplex (G.nonempty_of_mem_faces hs)⟩
  have hxhull : x ∈ convexHull ℝ (s : Set E) := openSimplex_subset_convexHull s hxopen
  have hxspace : x ∈ G.space := G.convexHull_subset_space hs hxhull
  obtain ⟨g, L, S, hLdim, hS, hgpa, hginj, hgL⟩ := hgerm x hxspace
  obtain ⟨O, hO, hxO, hOS⟩ := mem_nhdsWithin.mp hS
  obtain ⟨r, hr, hrO⟩ := Metric.isOpen_iff.mp hO x hxO
  obtain ⟨s', hs's, hs'card⟩ := Finset.exists_subset_card_eq (show 3 ≤ s.card by omega)
  have hs'ne : s'.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨v₀, hv₀⟩ := hs'ne
  have hs'faces : s' ∈ G.faces := G.down_closed hs hs's ⟨v₀, hv₀⟩
  set C : ℝ := s'.sup' ⟨v₀, hv₀⟩ (fun v => ‖v - x‖) with hCdef
  have hCle : ∀ v ∈ s', ‖v - x‖ ≤ C := by
    intro v hv
    rw [hCdef]
    exact Finset.le_sup' (fun v => ‖v - x‖) hv
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hCle v₀ hv₀)
  obtain ⟨c, hc, hcC⟩ := exists_pos_mul_lt hr C
  set ε : ℝ := min 1 c with hεdef
  have hεpos : 0 < ε := lt_min one_pos hc
  have hεle : ε ≤ 1 := min_le_left _ _
  have hεc : ε ≤ c := min_le_right _ _
  have hAv : ∀ v : E, (AffineMap.homothety x ε : E → E) v = (1 - ε) • x + ε • v := by
    intro v
    simp only [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add, smul_sub, sub_smul, one_smul]
    abel
  have hAinj : Function.Injective ((AffineMap.homothety x ε : E →ᵃ[ℝ] E) : E → E) := by
    intro p q hpq
    have hpq' : (1 - ε) • x + ε • p = (1 - ε) • x + ε • q := by
      rw [← hAv p, ← hAv q]
      exact hpq
    have h2 : ε • p = ε • q := add_left_cancel hpq'
    exact smul_right_injective E (ne_of_gt hεpos) h2
  have hAdist : ∀ v : E, dist ((AffineMap.homothety x ε : E → E) v) x = ε * ‖v - x‖ := by
    intro v
    rw [dist_eq_norm, hAv v]
    have hrw : (1 - ε) • x + ε • v - x = ε • (v - x) := by
      simp only [smul_sub, sub_smul, one_smul]
      abel
    rw [hrw, norm_smul, Real.norm_eq_abs, abs_of_pos hεpos]
  set T : Finset E := s'.image (AffineMap.homothety x ε : E → E) with hTdef
  have hTcard : T.card = 2 + 1 := by
    rw [hTdef, Finset.card_image_of_injective _ hAinj, hs'card]
  have hTind0 :
      AffineIndependent ℝ (fun v : s' => (AffineMap.homothety x ε : E → E) (v : E)) :=
    (G.indep hs'faces).map' (AffineMap.homothety x ε) hAinj
  have hTind : AffineIndependent ℝ ((↑) : ↥T → E) :=
    ((affineIndependent_image_iff s' (AffineMap.homothety x ε : E → E)).mp hTind0).2
  have hball2 : IsPLBall 2 (convexHull ℝ (T : Set E)) :=
    isPLBall_convexHull_of_affineIndependent T hTind hTcard
  have hmem : ∀ v ∈ s', (AffineMap.homothety x ε : E → E) v ∈
      convexHull ℝ (s : Set E) ∩ Metric.ball x r := by
    intro v hv
    constructor
    · rw [hAv v]
      exact (convex_convexHull ℝ (s : Set E)) hxhull
        (subset_convexHull ℝ (s : Set E) (hs's hv)) (by linarith) hεpos.le (by ring)
    · rw [Metric.mem_ball, hAdist v]
      have h1 : ‖v - x‖ ≤ C := hCle v hv
      have h2 : ε * ‖v - x‖ ≤ ε * C := by nlinarith [norm_nonneg (v - x)]
      have h3 : ε * C ≤ c * C := by nlinarith
      have h4 : c * C = C * c := mul_comm c C
      linarith
  have hTsub : convexHull ℝ (T : Set E) ⊆ convexHull ℝ (s : Set E) ∩ Metric.ball x r := by
    apply convexHull_min _ ((convex_convexHull ℝ (s : Set E)).inter (convex_ball x r))
    intro y hy
    have hy' : y ∈ s'.image (AffineMap.homothety x ε : E → E) := by
      rw [← hTdef]
      exact Finset.mem_coe.mp hy
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy'
    exact hmem v hv
  have hTG : convexHull ℝ (T : Set E) ⊆ G.space := fun y hy =>
    G.convexHull_subset_space hs (hTsub hy).1
  have hTS : convexHull ℝ (T : Set E) ⊆ S := fun y hy =>
    hOS ⟨hrO (hTsub hy).2, hTG hy⟩
  have hPL : IsPLHomeomorphOn g (convexHull ℝ (T : Set E)) (g '' convexHull ℝ (T : Set E)) :=
    isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn hball2.isPolyhedron
      (hgpa.mono_of_isPolyhedron hball2.isPolyhedron hTS) (hginj.mono hTS).bijOn_image
  have hball2' : IsPLBall 2 (g '' convexHull ℝ (T : Set E)) := hball2.of_isPLHomeomorphOn hPL
  have hsubL : g '' convexHull ℝ (T : Set E) ⊆ (L : Set F) := by
    rintro _ ⟨z, hz, rfl⟩
    exact hgL z (hTS hz) (hTG hz)
  obtain ⟨Cx, hCxfin, hCxspace⟩ := hball2'.isPolyhedron.exists_simplicialComplex
  have : Finite Cx.faces := hCxfin.to_subtype
  have hCxball : IsPLBall 2 Cx.space := by rw [hCxspace]; exact hball2'
  obtain ⟨p, hp⟩ := hball2'.nonempty
  obtain ⟨u, hu, -⟩ := Cx.mem_space_iff.mp (by rw [hCxspace]; exact hp)
  obtain ⟨t, ht, -, htcard⟩ := exists_face_superset_card_eq_of_isPLBall Cx hCxball hu
  have htL : (t : Set F) ⊆ (L : Set F) := by
    intro w hw
    apply hsubL
    rw [← hCxspace]
    exact Cx.convexHull_subset_space ht (subset_convexHull ℝ (t : Set F) hw)
  have hspan : vectorSpan ℝ (t : Set F) ≤ L := by
    rw [vectorSpan_def]
    apply Submodule.span_le.mpr
    rintro w ⟨a, ha, b, hb, rfl⟩
    exact L.sub_mem (htL ha) (htL hb)
  have hdim2 : Module.finrank ℝ (vectorSpan ℝ (t : Set F)) = 2 := by
    have h := (Cx.indep ht).finrank_vectorSpan
      (show Fintype.card t = 2 + 1 by simpa only [Fintype.card_coe] using htcard)
    have hrange : Set.range ((↑) : t → F) = (t : Set F) := by ext y; simp
    change Module.finrank ℝ (vectorSpan ℝ (Set.range ((↑) : t → F))) = 2 at h
    rwa [hrange] at h
  have hmono := Submodule.finrank_mono hspan
  rw [hdim2, hLdim] at hmono
  omega

end DifferentialGeometry.Topology.PiecewiseLinear
