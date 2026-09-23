import DifferentialGeometry.Topology.PiecewiseLinear.ChartComplexPiece
import DifferentialGeometry.Topology.PiecewiseLinear.CrossingTraceCircles

open Set Topology
open scoped Manifold

namespace DifferentialGeometry.Topology.PiecewiseLinear

private theorem isPolyhedralSphere_symm_image_of_mem_maximalAtlas
    {n m : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    (hc : c ∈ (plGroupoid n).maximalAtlas M) {C : Set (EuclideanSpace ℝ (Fin n))}
    (hC : IsPLSphere m C) (hCc : C ⊆ c.target) :
    IsPolyhedralSphere (n := n) m (c.symm '' C) := by
  obtain ⟨K, hfin, hKC⟩ := hC.isPolyhedron.exists_simplicialComplex
  rw [← hKC] at hC hCc ⊢
  refine ⟨⟨n, {
    complex := K
    finite_faces := hfin
    map := c.symm
    bijOn := (injOn_symm_of_subset_target c hCc).bijOn_image
    continuousOn := c.continuousOn_symm.mono hCc
    isPiecewiseAffineOn_chart := ?_
    isPiecewiseAffineOn_chart_symm := ?_ }⟩, hC⟩
  · intro e he
    have ht := (mem_plGroupoid_iff.mp ((mem_maximalAtlas_iff.mp hc e he).1)).1
    have hdom : (c.symm ≫ₕ e).source ∩ K.space = K.space ∩ c.symm ⁻¹' e.source := by
      rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source]
      ext x
      exact ⟨fun hx => ⟨hx.2, hx.1.2⟩, fun hx => ⟨⟨hCc hx.1, hx.2⟩, hx.1⟩⟩
    have hp := ht.inter_of_isPolyhedron hC.isPolyhedron
    rw [hdom] at hp
    exact hp.congr fun _ _ => rfl
  · intro e he
    have ht := (mem_plGroupoid_iff.mp ((mem_maximalAtlas_iff.mp hc e he).2)).1
    have himg : c.symm '' K.space = c.source ∩ c ⁻¹' K.space :=
      c.symm_image_eq_source_inter_preimage hCc
    have hdom : (e.symm ≫ₕ c).source ∩ (e.symm ≫ₕ c) ⁻¹' K.space =
        e.target ∩ e.symm ⁻¹' (c.symm '' K.space) := by
      rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source, himg]
      ext x
      simp only [mem_inter_iff, mem_preimage, OpenPartialHomeomorph.trans_apply]
      tauto
    have hp := ht.inter_preimage_of_isPolyhedron hC.isPolyhedron
    rw [hdom] at hp
    refine hp.congr fun x hx => ?_
    have hxC : e.symm x ∈ c.source ∩ c ⁻¹' K.space := himg ▸ hx.2
    change Function.invFunOn c.symm K.space (e.symm x) = c (e.symm x)
    conv_lhs => rw [← c.left_inv hxC.1]
    exact (injOn_symm_of_subset_target c hCc).leftInvOn_invFunOn hxC.2

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem exists_positive_finite_crossing_circle_family {A B : Set E3}
    (hpoly : IsPolyhedron (A ∩ B))
    (hcross : ∀ x ∈ A ∩ B, HasPLCrossingAt A B x)
    (hline : ∀ x ∈ A ∩ B, ∃ (V : Set E3) (φ : E3 → ℝ × ℝ × ℝ) (ρ : ℝ),
      IsOpen V ∧ x ∈ V ∧ 0 < ρ ∧ IsPLHomeomorphOn φ V (Metric.ball 0 ρ) ∧ φ x = 0 ∧
        ∀ y ∈ V, (y ∈ A ↔ (φ y).2.2 = 0) ∧ (y ∈ B ↔ (φ y).2.1 = 0))
    (hne : (A ∩ B).Nonempty) :
    ∃ (cnt : ℕ) (Pg : ℕ → Set E3), 0 < cnt ∧ A ∩ B = ⋃ i < cnt, Pg i ∧
      (∀ i < cnt, IsPLSphere 1 (Pg i) ∧ Pg i ⊆ A ∩ B) ∧
      ∀ i < cnt, ∀ j < cnt, i ≠ j → Disjoint (Pg i) (Pg j) := by
  classical
  obtain ⟨ι, hι, C, hC, hdisj, hcover⟩ :=
    exists_iUnion_isPLSphere_one_of_forall_lineChart hpoly hcross hline
  let _ : Finite ι := hι
  let _ : Fintype ι := Fintype.ofFinite ι
  have hιne : Nonempty ι := by
    obtain ⟨x, hx⟩ := hne
    rw [hcover] at hx
    obtain ⟨i, -⟩ := mem_iUnion.mp hx
    exact ⟨i⟩
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let Pg : ℕ → Set E3 := fun i => if hi : i < Fintype.card ι then C (e ⟨i, hi⟩) else ∅
  have hPg (i : ℕ) (hi : i < Fintype.card ι) : Pg i = C (e ⟨i, hi⟩) := dif_pos hi
  refine ⟨Fintype.card ι, Pg, Fintype.card_pos_iff.mpr hιne, ?_, ?_, ?_⟩
  · rw [hcover]
    ext x
    constructor
    · intro hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      refine mem_iUnion₂.mpr ⟨(e.symm i).1, (e.symm i).2, ?_⟩
      rw [hPg _ (e.symm i).2]
      simpa using hi
    · intro hx
      obtain ⟨i, hi, hx⟩ := mem_iUnion₂.mp hx
      rw [hPg i hi] at hx
      exact mem_iUnion.mpr ⟨_, hx⟩
  · intro i hi
    rw [hPg i hi]
    exact ⟨hC _, (subset_iUnion C _).trans hcover.symm.subset⟩
  · intro i hi j hj hij
    rw [hPg i hi, hPg j hj]
    exact hdisj fun he => hij (congrArg Fin.val (e.injective he))

theorem exists_positive_finite_piercing_circle_family {M : Type*} [TopologicalSpace M]
    [ChartedSpace E3 M] {A B : Set M} (c : OpenPartialHomeomorph M E3)
    (hc : c ∈ (plGroupoid 3).maximalAtlas M) (htrace : A ∩ B ⊆ c.source)
    (hpoly : IsPolyhedron ((c '' (A ∩ c.source)) ∩ (c '' (B ∩ c.source))))
    (hcross : ∀ x ∈ (c '' (A ∩ c.source)) ∩ (c '' (B ∩ c.source)),
      HasPLCrossingAt (c '' (A ∩ c.source)) (c '' (B ∩ c.source)) x)
    (hline : ∀ x ∈ (c '' (A ∩ c.source)) ∩ (c '' (B ∩ c.source)),
      ∃ (V : Set E3) (φ : E3 → ℝ × ℝ × ℝ) (ρ : ℝ),
        IsOpen V ∧ x ∈ V ∧ 0 < ρ ∧ IsPLHomeomorphOn φ V (Metric.ball 0 ρ) ∧ φ x = 0 ∧
          ∀ y ∈ V, (y ∈ c '' (A ∩ c.source) ↔ (φ y).2.2 = 0) ∧
            (y ∈ c '' (B ∩ c.source) ↔ (φ y).2.1 = 0))
    (hne : (A ∩ B).Nonempty) :
    ∃ (cnt : ℕ) (Pg : ℕ → Set M), 0 < cnt ∧ A ∩ B = ⋃ i < cnt, Pg i ∧
      (∀ i < cnt, IsPolyhedralSphere (n := 3) 1 (Pg i) ∧ Pg i ⊆ A ∩ B) ∧
      (∀ i < cnt, ∀ j < cnt, i ≠ j → Disjoint (Pg i) (Pg j)) ∧
      ∀ y ∈ A ∩ B, ∃ c' ∈ (plGroupoid 3).maximalAtlas M, y ∈ c'.source ∧
        HasPLCrossingAt (c' '' (A ∩ c'.source)) (c' '' (B ∩ c'.source)) (c' y) := by
  have himage : c '' (A ∩ B) = (c '' (A ∩ c.source)) ∩ (c '' (B ∩ c.source)) := by
    refine Subset.antisymm ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact ⟨⟨x, ⟨hx.1, htrace hx⟩, rfl⟩, ⟨x, ⟨hx.2, htrace hx⟩, rfl⟩⟩
    · rintro y ⟨⟨x, hx, hxy⟩, z, hz, hzy⟩
      have hxz : x = z := c.injOn hx.2 hz.2 (hxy.trans hzy.symm)
      exact ⟨x, ⟨hx.1, hxz.symm ▸ hz.1⟩, hxy⟩
  have hinverse : c.symm '' ((c '' (A ∩ c.source)) ∩ (c '' (B ∩ c.source))) = A ∩ B := by
    rw [← himage]
    refine Subset.antisymm ?_ ?_
    · rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      simpa only [c.left_inv (htrace hx)] using hx
    · intro x hx
      exact ⟨c x, ⟨x, hx, rfl⟩, c.left_inv (htrace hx)⟩
  have hne' : ((c '' (A ∩ c.source)) ∩ (c '' (B ∩ c.source))).Nonempty := by
    rw [← himage]
    exact hne.image c
  obtain ⟨cnt, C, hcnt, hcover, hC, hdisj⟩ :=
    exists_positive_finite_crossing_circle_family hpoly hcross hline hne'
  have hCt : ∀ i < cnt, C i ⊆ c.target := by
    intro i hi x hx
    obtain ⟨y, hy, rfl⟩ := ((hC i hi).2 hx).1
    exact c.map_source hy.2
  refine ⟨cnt, fun i => c.symm '' C i, hcnt, ?_, ?_, ?_, ?_⟩
  · rw [← hinverse, hcover]
    simp only [image_iUnion]
  · intro i hi
    exact ⟨isPolyhedralSphere_symm_image_of_mem_maximalAtlas hc (hC i hi).1 (hCt i hi),
      (image_mono (hC i hi).2).trans hinverse.subset⟩
  · intro i hi j hj hij
    apply Set.disjoint_left.mpr
    rintro y ⟨x, hx, hxy⟩ ⟨z, hz, hzy⟩
    have hxz : x = z := c.symm.injOn (hCt i hi hx) (hCt j hj hz) (hxy.trans hzy.symm)
    exact Set.disjoint_left.mp (hdisj i hi j hj hij) hx (hxz.symm ▸ hz)
  · intro y hy
    exact ⟨c, hc, htrace hy, hcross (c y)
      ⟨⟨y, ⟨hy.1, htrace hy⟩, rfl⟩, ⟨y, ⟨hy.2, htrace hy⟩, rfl⟩⟩⟩

end DifferentialGeometry.Topology.PiecewiseLinear
