import DifferentialGeometry.Topology.PiecewiseLinear.CirclePair
import DifferentialGeometry.Topology.PiecewiseLinear.LinkSection

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

private theorem union_halfSpace_inter {X : Type*} (S : Set X) (ℓ : X → ℝ) :
    (S ∩ {x | 0 ≤ ℓ x}) ∪ (S ∩ {x | ℓ x ≤ 0}) = S := by
  ext x
  constructor
  · exact fun h => h.elim And.left And.left
  · intro hx
    exact (le_total 0 (ℓ x)).elim (fun h => Or.inl ⟨hx, h⟩) (fun h => Or.inr ⟨hx, h⟩)

private theorem inter_halfSpace_inter {X : Type*} (S : Set X) (ℓ : X → ℝ) :
    (S ∩ {x | 0 ≤ ℓ x}) ∩ (S ∩ {x | ℓ x ≤ 0}) = S ∩ {x | ℓ x = 0} := by
  ext x
  exact ⟨fun h => ⟨h.1.1, le_antisymm h.2.2 h.1.2⟩,
    fun h => ⟨⟨h.1, h.2.ge⟩, ⟨h.1, h.2.le⟩⟩⟩

private theorem halfSpace_inter_fiber {X : Type*} {S J : Set X} (hJS : J ⊆ S) (ℓ : X → ℝ) :
    (J ∩ {x | 0 ≤ ℓ x}) ∩ (S ∩ {x | ℓ x = 0}) = J ∩ {x | ℓ x = 0} ∧
      (J ∩ {x | ℓ x ≤ 0}) ∩ (S ∩ {x | ℓ x = 0}) = J ∩ {x | ℓ x = 0} := by
  constructor
  · ext x
    exact ⟨fun h => ⟨h.1.1, h.2.2⟩, fun h => ⟨⟨h.1, h.2.ge⟩, ⟨hJS h.1, h.2⟩⟩⟩
  · ext x
    exact ⟨fun h => ⟨h.1.1, h.2.2⟩, fun h => ⟨⟨h.1, h.2.le⟩, ⟨hJS h.1, h.2⟩⟩⟩

private theorem exists_geometricLink_disk_pair
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [DecidableEq E]
    (hn : Module.finrank ℝ E = 3) (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    {p : E} (hp : {p} ∈ K.faces) (hK : K.space ∈ 𝓝 p)
    (ℓ : E →L[ℝ] ℝ) (hℓ : ℓ ≠ 0) (hpℓ : ℓ p = 0)
    (hside : ∀ s ∈ K.faces, convexHull ℝ (s : Set E) ⊆ {x | ℓ x ≤ 0} ∨
      convexHull ℝ (s : Set E) ⊆ {x | 0 ≤ ℓ x}) :
    ∃ u v : (Fin 3 → ℝ) → E,
      IsPLHomeomorphOn u (stdSimplex ℝ (Fin 3))
        ((SimplicialComplex.geometricLink K {p}).space ∩ {x | 0 ≤ ℓ x}) ∧
      IsPLHomeomorphOn v (stdSimplex ℝ (Fin 3))
        ((SimplicialComplex.geometricLink K {p}).space ∩ {x | ℓ x ≤ 0}) ∧
      u '' stdSimplexBoundary 2 = (SimplicialComplex.geometricLink K {p}).space ∩ {x | ℓ x = 0} ∧
      v '' stdSimplexBoundary 2 = (SimplicialComplex.geometricLink K {p}).space ∩ {x | ℓ x = 0} := by
  obtain ⟨u, hu, huB⟩ := exists_isPLHomeomorphOn_geometricLink_halfSpace hn K hp hK ℓ hℓ hpℓ hside
  obtain ⟨v, hv, hvB⟩ := exists_isPLHomeomorphOn_geometricLink_halfSpace hn K hp hK (-ℓ)
    (neg_ne_zero.mpr hℓ) (by simp [hpℓ]) (by
      intro s hs
      simpa only [neg_apply, neg_nonpos, neg_nonneg] using (hside s hs).symm)
  simp only [neg_apply, neg_nonneg, neg_eq_zero] at hv hvB
  exact ⟨u, v, hu, hv, huB, hvB⟩

theorem exists_isPLHomeomorphOn_geometricLink_pair
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [DecidableEq E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [DecidableEq F]
    (hn : Module.finrank ℝ E = 3) (hn' : Module.finrank ℝ F = 3)
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (K' : Geometry.SimplicialComplex ℝ F) [Finite K'.faces]
    {p : E} {p' : F} (hp : {p} ∈ K.faces) (hp' : {p'} ∈ K'.faces)
    (hK : K.space ∈ 𝓝 p) (hK' : K'.space ∈ 𝓝 p')
    (ℓ : E →L[ℝ] ℝ) (ℓ' : F →L[ℝ] ℝ) (hℓ : ℓ ≠ 0) (hℓ' : ℓ' ≠ 0)
    (hpℓ : ℓ p = 0) (hpℓ' : ℓ' p' = 0)
    (hside : ∀ s ∈ K.faces, convexHull ℝ (s : Set E) ⊆ {x | ℓ x ≤ 0} ∨
      convexHull ℝ (s : Set E) ⊆ {x | 0 ≤ ℓ x})
    (hside' : ∀ s ∈ K'.faces, convexHull ℝ (s : Set F) ⊆ {x | ℓ' x ≤ 0} ∨
      convexHull ℝ (s : Set F) ⊆ {x | 0 ≤ ℓ' x})
    {J : Set E} {J' : Set F} (hJ : IsPLSphere 1 J) (hJ' : IsPLSphere 1 J')
    (hJK : J ⊆ (SimplicialComplex.geometricLink K {p}).space)
    (hJK' : J' ⊆ (SimplicialComplex.geometricLink K' {p'}).space)
    {a b : E} {a' b' : F} (hab : a ≠ b) (hab' : a' ≠ b')
    (hzero : J ∩ {x | ℓ x = 0} = {a, b}) (hzero' : J' ∩ {x | ℓ' x = 0} = {a', b'})
    (hpos : ∃ x ∈ J, 0 < ℓ x) (hneg : ∃ x ∈ J, ℓ x < 0)
    (hpos' : ∃ x ∈ J', 0 < ℓ' x) (hneg' : ∃ x ∈ J', ℓ' x < 0) :
    ∃ f : E → F, IsPLHomeomorphOn f (SimplicialComplex.geometricLink K {p}).space
        (SimplicialComplex.geometricLink K' {p'}).space ∧
      f '' J = J' ∧
      f '' ((SimplicialComplex.geometricLink K {p}).space ∩ {x | ℓ x = 0}) =
        (SimplicialComplex.geometricLink K' {p'}).space ∩ {x | ℓ' x = 0} ∧
      f '' ((SimplicialComplex.geometricLink K {p}).space ∩ {x | 0 ≤ ℓ x}) =
        (SimplicialComplex.geometricLink K' {p'}).space ∩ {x | 0 ≤ ℓ' x} ∧
      f '' ((SimplicialComplex.geometricLink K {p}).space ∩ {x | ℓ x ≤ 0}) =
        (SimplicialComplex.geometricLink K' {p'}).space ∩ {x | ℓ' x ≤ 0} ∧
      f a = a' ∧ f b = b' := by
  obtain ⟨u, v, hu, hv, huB, hvB⟩ := exists_geometricLink_disk_pair hn K hp hK ℓ hℓ hpℓ hside
  obtain ⟨u', v', hu', hv', huB', hvB'⟩ :=
    exists_geometricLink_disk_pair hn' K' hp' hK' ℓ' hℓ' hpℓ' hside'
  obtain ⟨γ, δ, hγ, hδ, hγ0, hγ1, hδ0, hδ1⟩ :=
    exists_isPLHomeomorphOn_Icc_inter_of_fiber_pair hJ ℓ.continuous.continuousOn hzero hab hpos hneg
  obtain ⟨γ', δ', hγ', hδ', hγ'0, hγ'1, hδ'0, hδ'1⟩ :=
    exists_isPLHomeomorphOn_Icc_inter_of_fiber_pair hJ' ℓ'.continuous.continuousOn hzero' hab' hpos' hneg'
  have hPJ := (halfSpace_inter_fiber hJK ℓ).1.trans hzero
  have hQJ := (halfSpace_inter_fiber hJK ℓ).2.trans hzero
  have hPJ' := (halfSpace_inter_fiber hJK' ℓ').1.trans hzero'
  have hQJ' := (halfSpace_inter_fiber hJK' ℓ').2.trans hzero'
  obtain ⟨G, hG, hGJ, hGA, hGB, hGP, hGQ, hG0, hG1⟩ :=
    exists_isPLHomeomorphOn_disk_pair_map_crosscuts hu hv huB hvB (inter_halfSpace_inter _ ℓ)
      hu' hv' huB' hvB' (inter_halfSpace_inter _ ℓ') hγ hδ
      (inter_subset_inter_left _ hJK) (inter_subset_inter_left _ hJK)
      (by rwa [hγ0, hγ1]) (by rwa [hδ0, hδ1]) (hδ0.trans hγ0.symm) (hδ1.trans hγ1.symm)
      hγ' hδ' (inter_subset_inter_left _ hJK') (inter_subset_inter_left _ hJK')
      (by rwa [hγ'0, hγ'1]) (by rwa [hδ'0, hδ'1]) (hδ'0.trans hγ'0.symm) (hδ'1.trans hγ'1.symm)
  rw [union_halfSpace_inter, union_halfSpace_inter] at hG
  rw [hγ0, hγ'0] at hG0
  rw [hγ1, hγ'1] at hG1
  refine ⟨G, hG, ?_, hGJ, hGA, hGB, hG0, hG1⟩
  calc
    G '' J = G '' ((J ∩ {x | 0 ≤ ℓ x}) ∪ (J ∩ {x | ℓ x ≤ 0})) := by rw [union_halfSpace_inter]
    _ = (J' ∩ {x | 0 ≤ ℓ' x}) ∪ (J' ∩ {x | ℓ' x ≤ 0}) := by rw [image_union, hGP, hGQ]
    _ = J' := union_halfSpace_inter J' ℓ'

end DifferentialGeometry.Topology.PiecewiseLinear
