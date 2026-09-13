import DifferentialGeometry.Topology.PiecewiseLinear.LinkSubdivision
import DifferentialGeometry.Topology.PiecewiseLinear.SimplexBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.Triangulation

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem closedStar_subset_space (K : Geometry.SimplicialComplex ℝ E) (x : E) :
    closedStar K x ⊆ K.space :=
  iUnion₂_subset fun _ hs => K.convexHull_subset_space hs.1

theorem closedStar_mem_nhds (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] {x : E}
    (hK : K.space ∈ 𝓝 x) : closedStar K x ∈ 𝓝 x := by
  obtain ⟨U, hU, hUK⟩ :=
    mem_nhdsWithin_iff_exists_mem_nhds_inter.mp (closedStar_mem_nhdsWithin K x)
  exact Filter.mem_of_superset (Filter.inter_mem hU hK) hUK

section Facets

variable [DecidableEq E]

theorem erase_mem_simplexBoundary_faces {T : Finset E} (hT : AffineIndependent ℝ ((↑) : T → E))
    (hcard : 2 ≤ T.card) {v : E} (hv : v ∈ T) : T.erase v ∈ (simplexBoundary T hT).faces := by
  refine ⟨Finset.erase_subset v T, ?_, ?_⟩
  · rw [← Finset.card_pos, Finset.card_erase_of_mem hv]
    omega
  · intro h
    have := Finset.notMem_erase v T
    rw [h] at this
    exact this hv

theorem affineIndependent_insert_erase {T : Finset E} (hT : AffineIndependent ℝ ((↑) : T → E))
    {p : E} (hp : p ∈ openSimplex T) {v : E} (hv : v ∈ T) :
    AffineIndependent ℝ ((↑) : {x // x ∈ (insert p (T.erase v) : Finset E)} → E) := by
  have hpT : p ∈ convexHull ℝ (T : Set E) := openSimplex_subset_convexHull T hp
  have hpos : ∀ u ∈ T, 0 < weights T p u := (mem_openSimplex_self_iff hT hpT).mp hp
  have hpv : p ∉ T.erase v := notMem_erase_of_mem_openSimplex hT hp hv
  refine affineIndependent_of_forall_eq_zero fun a ha₀ ha₁ => ?_
  rw [Finset.sum_insert hpv] at ha₀ ha₁
  let f : E → ℝ := fun u => if u = v then 0 else a u
  have hf : ∀ u ∈ T.erase v, f u = a u := fun u hu => by
    simp only [f, if_neg (Finset.ne_of_mem_erase hu)]
  have hsum_f : ∑ u ∈ T, f u = ∑ u ∈ T.erase v, a u := by
    rw [← Finset.sum_erase T (by simp [f] : f v = 0)]
    exact Finset.sum_congr rfl hf
  have hsmul_f : ∑ u ∈ T, f u • u = ∑ u ∈ T.erase v, a u • u := by
    rw [← Finset.sum_erase (f := fun u => f u • u) (a := v) T (by simp [f])]
    exact Finset.sum_congr rfl fun u hu => by rw [hf u hu]
  let b : E → ℝ := fun u => a p * weights T p u + f u
  have hb₀ : ∑ u ∈ T, b u = 0 := by
    simp only [b]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, sum_weights hpT, mul_one, hsum_f]
    exact ha₀
  have hb₁ : ∑ u ∈ T, b u • u = 0 := by
    simp only [b, add_smul, mul_smul]
    rw [Finset.sum_add_distrib, ← Finset.smul_sum, sum_weights_smul hpT, hsmul_f]
    exact ha₁
  have hzero := eq_zero_of_sum_eq_zero_of_affineIndependent hT hb₀ hb₁
  have hap : a p = 0 := by
    have h := hzero v hv
    simp only [b, f, if_true, add_zero] at h
    rcases mul_eq_zero.mp h with h | h
    · exact h
    · exact absurd h (hpos v hv).ne'
  intro u hu
  rcases Finset.mem_insert.mp hu with h | h
  · rw [h]
    exact hap
  · have h' := hzero u (Finset.mem_of_mem_erase h)
    simp only [b, hap, zero_mul, zero_add, hf u h] at h'
    exact h'

theorem exists_facet_convexHull_insert_subset [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) {T : Finset E} (hT : AffineIndependent ℝ ((↑) : T → E))
    {p : E} (hp : p ∈ openSimplex T) (hTnhds : convexHull ℝ (T : Set E) ∈ 𝓝 p)
    (hunion : ∀ v ∈ T, convexHull ℝ ((insert p (T.erase v) : Finset E) : Set E) =
      ⋃ s ∈ {s ∈ K.faces | convexHull ℝ (s : Set E) ⊆
        convexHull ℝ ((insert p (T.erase v) : Finset E) : Set E)}, convexHull ℝ (s : Set E))
    {σ : Finset E} (hins : insert p σ ∈ K.faces) :
    ∃ v ∈ T, convexHull ℝ ((insert p σ : Finset E) : Set E) ⊆
      convexHull ℝ ((insert p (T.erase v) : Finset E) : Set E) := by
  set c := (insert p σ).centroid ℝ id with hc
  have hcopen : c ∈ openSimplex (insert p σ) :=
    centroid_mem_openSimplex (Finset.insert_nonempty p σ)
  have hcconv : c ∈ convexHull ℝ ((insert p σ : Finset E) : Set E) :=
    openSimplex_subset_convexHull _ hcopen
  have hpconv : p ∈ convexHull ℝ ((insert p σ : Finset E) : Set E) :=
    subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_insert_self p σ))
  have htend : Filter.Tendsto (fun t : ℝ => p + t • (c - p)) (𝓝[>] 0) (𝓝 p) := by
    have hcont : Continuous fun t : ℝ => p + t • (c - p) :=
      continuous_const.add (continuous_id.smul continuous_const)
    have := hcont.tendsto 0
    simp only [zero_smul, add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      p + t • (c - p) ∈ convexHull ℝ (T : Set E) ∧ t ∈ Ioo (0 : ℝ) 1 := by
    filter_upwards [htend.eventually_mem hTnhds, Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with t h1 h2
      using ⟨h1, h2⟩
  obtain ⟨t, hxt, ht0, ht1⟩ := hev.exists
  have hxconv : p + t • (c - p) ∈ convexHull ℝ ((insert p σ : Finset E) : Set E) := by
    rw [add_smul_sub_eq_combo]
    exact (convex_convexHull ℝ _) hpconv hcconv (by linarith) ht0.le (by ring)
  have hxopen : p + t • (c - p) ∈ openSimplex (insert p σ) := by
    rw [mem_openSimplex_self_iff (K.indep hins) hxconv]
    intro u hu
    rw [add_smul_sub_eq_combo, weights_combo (K.indep hins) hpconv hcconv (by linarith) ht0.le
      (by ring) u hu]
    have h1 := weights_nonneg hpconv hu
    have h2 := (mem_openSimplex_self_iff (K.indep hins) hcconv).mp hcopen u hu
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - t) h1, mul_pos ht0 h2]
  obtain ⟨v, hv, hxv⟩ := exists_mem_convexHull_insert_erase hT hp hxt
  refine ⟨v, hv, ?_⟩
  rw [hunion v hv] at hxv
  obtain ⟨s, ⟨hs, hsQ⟩, hxs⟩ := mem_iUnion₂.mp hxv
  have hsub : insert p σ ⊆ s :=
    face_subset_of_mem_openSimplex_of_mem_convexHull K hins hs hxopen hxs
  exact (convexHull_mono (Finset.coe_subset.mpr hsub)).trans hsQ

end Facets

theorem isPLSphere_geometricLink_of_mem_nhds [FiniteDimensional ℝ E] [DecidableEq E] {n : ℕ}
    (hn : Module.finrank ℝ E = n + 1) (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    {p : E} (hp : {p} ∈ K.faces) (hK : K.space ∈ 𝓝 p) :
    IsPLSphere n (SimplicialComplex.geometricLink K {p}).space := by
  classical
  obtain ⟨T, hT, hcard, hpT, hTstar, hTnhds⟩ :=
    exists_affineIndependent_openSimplex_subset hn p (closedStar_mem_nhds K hK)
  have hcard2 : 2 ≤ T.card := by omega
  have hpconvT : p ∈ convexHull ℝ (T : Set E) := openSimplex_subset_convexHull T hpT
  have hconeT : ∀ v ∈ T, convexHull ℝ ((insert p (T.erase v) : Finset E) : Set E) ⊆
      convexHull ℝ (T : Set E) := by
    intro v hv
    refine convexHull_min ?_ (convex_convexHull ℝ _)
    intro u hu
    rcases Finset.mem_insert.mp (Finset.mem_coe.mp hu) with h | h
    · rw [h]
      exact hpconvT
    · exact subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_of_mem_erase h))
  let Q : T → Set E := fun v => convexHull ℝ ((insert p (T.erase v) : Finset E) : Set E)
  have hQ : ∀ v, IsPolyhedron (Q v) := fun v =>
    isPolyhedron_convexHull_of_affineIndependent _ (affineIndependent_insert_erase hT hpT v.2)
  have hQK : ∀ v, Q v ⊆ K.space := fun v =>
    (hconeT v v.2).trans (hTstar.trans (closedStar_subset_space K p))
  obtain ⟨K'', hK'', hfin'', hunion⟩ := exists_isSubdivision_subcomplexes K Q hQ hQK
  have : Finite K''.faces := hfin''.to_subtype
  have hp'' : {p} ∈ K''.faces := hK''.singleton_mem hp
  rw [← isPLSphere_geometricLink_iff_of_isSubdivision hK'' hp]
  have hray : IsRadiallyInjective p (simplexBoundary T hT).space := by
    rw [simplexBoundary_space T hT hcard2]
    exact isRadiallyInjective_boundary hT hpT
  have hadapt : ∀ σ ∈ (SimplicialComplex.geometricLink K'' {p}).faces,
      ∃ τ ∈ (simplexBoundary T hT).faces, ∀ w ∈ σ,
        ∃ s : ℝ, 0 < s ∧ p + s • (w - p) ∈ convexHull ℝ (τ : Set E) := by
    intro σ hσ
    obtain ⟨-, hpσ, hins⟩ := (SimplicialComplex.mem_geometricLink_singleton K'' p σ).mp hσ
    obtain ⟨v, hv, hsub⟩ := exists_facet_convexHull_insert_subset K'' hT hpT hTnhds
      (fun v hv => hunion ⟨v, hv⟩) hins
    refine ⟨T.erase v, erase_mem_simplexBoundary_faces hT hcard2 hv, fun w hw => ?_⟩
    have hwmem : w ∈ convexHull ℝ ((insert p (T.erase v) : Finset E) : Set E) :=
      hsub (subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_insert_of_mem hw)))
    exact exists_ray_mem_convexHull_of_mem_convexHull_insert hwmem (ne_of_mem_of_not_mem hw hpσ)
  have hsurj : ∀ x ∈ (simplexBoundary T hT).space,
      ∃ s : ℝ, 0 < s ∧ p + s • (x - p) ∈ (SimplicialComplex.geometricLink K'' {p}).space := by
    intro x hx
    rw [simplexBoundary_space T hT hcard2] at hx
    have hxp : x ≠ p := fun h => notMem_boundary_of_mem_openSimplex hT hpT (h ▸ hx)
    have hxT : x ∈ convexHull ℝ (T : Set E) := by
      obtain ⟨v, -, hxv⟩ := mem_iUnion₂.mp hx
      exact convexHull_mono (Finset.coe_subset.mpr (Finset.erase_subset v T)) hxv
    refine exists_ray_mem_geometricLink_space K'' hp'' (fun t ht0 ht1 => ?_) hxp
    rw [hK''.space_eq]
    refine (hTstar.trans (closedStar_subset_space K p)) ?_
    rw [add_smul_sub_eq_combo]
    exact (convex_convexHull ℝ _) hpconvT hxT (by linarith) ht0.le (by ring)
  obtain ⟨f, hf⟩ := exists_isPLHomeomorphOn_of_radial p (simplexBoundary T hT)
    (SimplicialComplex.geometricLink K'' {p}) hray (isConeBase_geometricLink K'') hadapt hsurj
  rw [simplexBoundary_space T hT hcard2] at hf
  exact (isPLSphere_biUnion_erase T hT hcard).of_isPLHomeomorphOn hf.symm

end DifferentialGeometry.Topology.PiecewiseLinear
