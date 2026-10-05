import DifferentialGeometry.Topology.PiecewiseLinear.LinkSubspace
import DifferentialGeometry.Topology.PiecewiseLinear.PointedConvexification

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem finrank_vectorSpan_inf_ker_eq_one_of_affineIndependent_card_three
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (T : Finset E) (hT : AffineIndependent ℝ ((↑) : T → E))
    (hcard : T.card = 3) (f : E →L[ℝ] ℝ) (hfinj : InjOn f (T : Set E)) :
    Module.finrank ℝ (vectorSpan ℝ (T : Set E) ⊓ LinearMap.ker f.toLinearMap :
      Submodule ℝ E) = 1 := by
  classical
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp (by omega : 1 < T.card)
  let _ : Nonempty T := ⟨⟨u, hu⟩⟩
  let P := vectorSpan ℝ (T : Set E)
  have hP : Module.finrank ℝ P = 2 := by
    have h := hT.finrank_vectorSpan (show Fintype.card T = 2 + 1 by
      simpa only [Fintype.card_coe] using hcard)
    have hrange : Set.range ((↑) : T → E) = (T : Set E) := by ext x; simp
    change Module.finrank ℝ (vectorSpan ℝ (Set.range ((↑) : T → E))) = 2 at h
    rwa [hrange] at h
  have hdP : u - v ∈ P := by
    simpa only [P, vsub_eq_sub] using vsub_mem_vectorSpan ℝ hu hv
  have hfd : f (u - v) ≠ 0 := by
    intro hz
    apply huv
    apply hfinj hu hv
    rw [← sub_eq_zero]
    simpa only [map_sub] using hz
  have hsup : P ⊔ LinearMap.ker f.toLinearMap = ⊤ :=
    sup_ker_eq_top_of_apply_ne_zero P f.toLinearMap hdP hfd
  have hf : f.toLinearMap ≠ 0 := by
    intro hz
    have hfzero : f = 0 := by
      ext x
      exact congrArg (fun g : E →ₗ[ℝ] ℝ => g x) hz
    apply hfd
    rw [hfzero, zero_apply]
  have hker := Module.Dual.finrank_ker_add_one_of_ne_zero hf
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq P (LinearMap.ker f.toLinearMap)
  rw [hsup, finrank_top, hP] at hdim
  change Module.finrank ℝ (P ⊓ LinearMap.ker f.toLinearMap : Submodule ℝ E) = 1
  omega

theorem geometricLink_section_subsingleton_of_simplex_vertex
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [DecidableEq E] (T : Finset E) (hT : AffineIndependent ℝ ((↑) : T → E))
    (hcard : T.card = 3) {q : E} (hq : q ∈ T)
    (M : Geometry.SimplicialComplex ℝ E)
    (hspace : M.space = convexHull ℝ (T : Set E))
    (f : E →L[ℝ] ℝ) (hfinj : InjOn f (T : Set E)) :
    ((SimplicialComplex.geometricLink M {q}).space ∩ {x | f x = f q}).Subsingleton := by
  classical
  let P := vectorSpan ℝ (T : Set E)
  have hinf : Module.finrank ℝ (P ⊓ LinearMap.ker f.toLinearMap : Submodule ℝ E) = 1 :=
    finrank_vectorSpan_inf_ker_eq_one_of_affineIndependent_card_three
      T hT hcard f hfinj
  obtain ⟨m, -, hm⟩ :=
    exists_linearMap_lt_on_convexHull_sdiff_singleton T hT (by omega) hq
  rintro a ⟨haL, haf⟩ b ⟨hbL, hbf⟩
  have haM : a ∈ M.space :=
    space_mono_of_faces_subset (SimplicialComplex.geometricLink_le M {q}) haL
  have hbM : b ∈ M.space :=
    space_mono_of_faces_subset (SimplicialComplex.geometricLink_le M {q}) hbL
  have haC : a ∈ convexHull ℝ (T : Set E) := hspace ▸ haM
  have hbC : b ∈ convexHull ℝ (T : Set E) := hspace ▸ hbM
  have hqC : q ∈ convexHull ℝ (T : Set E) := subset_convexHull ℝ _ hq
  have haq : a ≠ q := ne_of_mem_of_not_mem haL (notMem_geometricLink_space M)
  have hbq : b ≠ q := ne_of_mem_of_not_mem hbL (notMem_geometricLink_space M)
  have haP : a - q ∈ P := by
    change a - q ∈ vectorSpan ℝ (T : Set E)
    have h := vsub_mem_vectorSpan_of_mem_affineSpan_of_mem_affineSpan
      (k := ℝ) (s := (T : Set E))
      (convexHull_subset_affineSpan (T : Set E) haC)
      (convexHull_subset_affineSpan (T : Set E) hqC)
    simpa only [vsub_eq_sub] using h
  have hbP : b - q ∈ P := by
    change b - q ∈ vectorSpan ℝ (T : Set E)
    have h := vsub_mem_vectorSpan_of_mem_affineSpan_of_mem_affineSpan
      (k := ℝ) (s := (T : Set E))
      (convexHull_subset_affineSpan (T : Set E) hbC)
      (convexHull_subset_affineSpan (T : Set E) hqC)
    simpa only [vsub_eq_sub] using h
  have haK : a - q ∈ LinearMap.ker f.toLinearMap := by
    have haf' : f.toLinearMap a = f.toLinearMap q := by
      simpa only [mem_ofPred_eq, ContinuousLinearMap.coe_coe] using haf
    rw [LinearMap.mem_ker, map_sub, haf', sub_self]
  have hbK : b - q ∈ LinearMap.ker f.toLinearMap := by
    have hbf' : f.toLinearMap b = f.toLinearMap q := by
      simpa only [mem_ofPred_eq, ContinuousLinearMap.coe_coe] using hbf
    rw [LinearMap.mem_ker, map_sub, hbf', sub_self]
  have haI : a - q ∈ P ⊓ LinearMap.ker f.toLinearMap := ⟨haP, haK⟩
  have hbI : b - q ∈ P ⊓ LinearMap.ker f.toLinearMap := ⟨hbP, hbK⟩
  have hspan : P ⊓ LinearMap.ker f.toLinearMap = Submodule.span ℝ ({a - q} : Set E) :=
    eq_span_singleton_of_mem_of_finrank_eq_one hinf haI (sub_ne_zero.mpr haq)
  rw [hspan] at hbI
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hbI
  have hma : 0 < m (a - q) := by
    have := hm a ⟨haC, by simpa only [mem_singleton_iff] using haq⟩
    rw [map_sub]
    linarith
  have hmb : 0 < m (b - q) := by
    have := hm b ⟨hbC, by simpa only [mem_singleton_iff] using hbq⟩
    rw [map_sub]
    linarith
  have hmc := congrArg m hc
  simp only [map_smul, smul_eq_mul] at hmc
  have hcpos : 0 < c := by nlinarith
  have hbeq : b = q + c • (a - q) := by
    rw [add_comm]
    exact sub_eq_iff_eq_add.mp hc.symm
  exact ((isRadiallyInjective_geometricLink M) a haL b hbL c hcpos hbeq).symm

end DifferentialGeometry.Topology.PiecewiseLinear
