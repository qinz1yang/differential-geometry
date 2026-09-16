import DifferentialGeometry.Topology.PiecewiseLinear.SimplexAvoiding
import Mathlib.Topology.Order.IntermediateValue

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]

theorem image_radial_prod_Icc_eq_coneComplex_space
    {K : Geometry.SimplicialComplex ℝ E} {p : E} (hp : IsConeBase p K) (hK : K.space.Nonempty) :
    (fun z : E × ℝ => p + z.2 • (z.1 - p)) '' (K.space ×ˢ Icc (0 : ℝ) 1) =
      (coneComplex hp).space := by
  apply Subset.antisymm
  · rintro x ⟨z, hz, rfl⟩
    by_cases ht : z.2 = 0
    · simpa only [ht, zero_smul, add_zero] using apex_mem_coneComplex_space hp
    · exact (mem_coneComplex_space_iff hp).mpr
        (Or.inr ⟨z.1, hz.1, z.2, lt_of_le_of_ne hz.2.1 (Ne.symm ht), hz.2.2, rfl⟩)
  · intro x hx
    rcases (mem_coneComplex_space_iff hp).mp hx with rfl | ⟨z, hz, t, ht, ht1, rfl⟩
    · obtain ⟨z, hz⟩ := hK
      exact ⟨(z, 0), ⟨hz, le_rfl, zero_le_one⟩, by simp⟩
    · exact ⟨(z, t), ⟨hz, ht.le, ht1⟩, rfl⟩

theorem coneComplex_sdiff_coneComplex_eq_image
    {K L : Geometry.SimplicialComplex ℝ E} {p : E} (hp : IsConeBase p K)
    (hLK : L.faces ⊆ K.faces) :
    (coneComplex hp).space \ (coneComplex (hp.of_faces_subset hLK)).space =
      (fun z : E × ℝ => p + z.2 • (z.1 - p)) '' ((K.space \ L.space) ×ˢ Ioc (0 : ℝ) 1) := by
  apply Subset.antisymm
  · rintro x ⟨hxK, hxL⟩
    rcases (mem_coneComplex_space_iff hp).mp hxK with rfl | ⟨z, hz, t, ht, ht1, rfl⟩
    · exact (hxL (apex_mem_coneComplex_space _)).elim
    · refine ⟨(z, t), ⟨⟨hz, ?_⟩, ht, ht1⟩, rfl⟩
      intro hzL
      exact hxL ((mem_coneComplex_space_iff _).mpr (Or.inr ⟨z, hzL, t, ht, ht1, rfl⟩))
  · rintro x ⟨z, hz, rfl⟩
    refine ⟨(mem_coneComplex_space_iff hp).mpr (Or.inr ⟨z.1, hz.1.1, z.2, hz.2.1, hz.2.2, rfl⟩), ?_⟩
    intro hxL
    rcases (mem_coneComplex_space_iff (hp.of_faces_subset hLK)).mp hxL with hxp | ⟨w, hw, t, ht, -, hxt⟩
    · exact ne_of_mem_of_notMem_of_radial hz.1.1 hp.notMem_space hz.2.1 rfl hxp
    · have heq := hp.radial.eq_of_add_smul_eq hz.1.1 (space_mono_of_faces_subset hLK hw)
        hz.2.1 ht hxt
      exact hz.1.2 (heq.symm ▸ hw)

theorem IsConeBase.isConnected_sdiff_coneComplex
    {K L : Geometry.SimplicialComplex ℝ E} {p : E} (hp : IsConeBase p K)
    (hLK : L.faces ⊆ K.faces) (hconn : IsConnected (K.space \ L.space)) :
    IsConnected ((coneComplex hp).space \ (coneComplex (hp.of_faces_subset hLK)).space) := by
  rw [coneComplex_sdiff_coneComplex_eq_image hp hLK]
  exact (hconn.prod (isConnected_Ioc (by norm_num : (0 : ℝ) < 1))).image _
    ((continuous_const.add (continuous_snd.smul (continuous_fst.sub continuous_const))).continuousOn)

theorem IsConeBase.closure_sdiff_coneComplex
    {K L : Geometry.SimplicialComplex ℝ E} [Finite K.faces] {p : E} (hp : IsConeBase p K)
    (hLK : L.faces ⊆ K.faces) (hK : K.space.Nonempty)
    (hdense : closure (K.space \ L.space) = K.space) :
    closure ((coneComplex hp).space \ (coneComplex (hp.of_faces_subset hLK)).space) =
      (coneComplex hp).space := by
  have hcompact : IsCompact (coneComplex hp).space :=
    (coneComplex_faces_finite hp (Set.toFinite K.faces)).isCompact_biUnion
      (fun s _ => s.finite_toSet.isCompact_convexHull ℝ)
  apply Subset.antisymm (closure_minimal sdiff_subset hcompact.isClosed)
  have hdom : closure ((K.space \ L.space) ×ˢ Ioc (0 : ℝ) 1) = K.space ×ˢ Icc (0 : ℝ) 1 := by
    rw [closure_prod_eq, hdense, closure_Ioc zero_ne_one]
  have hcont : Continuous (fun z : E × ℝ => p + z.2 • (z.1 - p)) :=
    continuous_const.add (continuous_snd.smul (continuous_fst.sub continuous_const))
  have h := image_closure_subset_closure_image (s := (K.space \ L.space) ×ˢ Ioc (0 : ℝ) 1) hcont
  rwa [hdom, image_radial_prod_Icc_eq_coneComplex_space hp hK,
    ← coneComplex_sdiff_coneComplex_eq_image hp hLK] at h

end DifferentialGeometry.Topology.PiecewiseLinear
