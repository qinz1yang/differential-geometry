import DifferentialGeometry.Topology.PiecewiseLinear.Section34BicollarPages

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

open Classical in
theorem exists_interior_crossing_circle_pages
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K₀ K₁ : Geometry.SimplicialComplex ℝ E) [Finite K₀.faces] [Finite K₁.faces]
    (hK₀ : IsCombinatorialManifoldWithBoundary 2 K₀)
    (hK₁ : IsCombinatorialManifoldWithBoundary 2 K₁)
    (hor₀ : IsOrientable 2 K₀) (hor₁ : IsOrientable 2 K₁)
    {J U : Set E} (hJ : IsPLSphere 1 J) (hJ₀ : J ⊆ K₀.space) (hJ₁ : J ⊆ K₁.space)
    (hBd₀ : Disjoint J (boundaryComplex 2 K₀).space)
    (hBd₁ : Disjoint J (boundaryComplex 2 K₁).space)
    (hU : IsOpen U) (hJU : J ⊆ U) (htrace : (K₀.space ∩ K₁.space) ∩ U ⊆ J) :
    ∃ (N W₀ W₁ : Set E) (ρ σ : E × ℝ → E) (P : Fin 4 → Set E),
      IsOpen N ∧ J ⊆ N ∧ N ⊆ U ∧
      W₀ ⊆ K₀.space \ (boundaryComplex 2 K₀).space ∧
      W₁ ⊆ K₁.space \ (boundaryComplex 2 K₁).space ∧
      W₀ ∪ W₁ ⊆ U ∧ W₀ ∈ 𝓝ˢ[K₀.space] J ∧ W₁ ∈ 𝓝ˢ[K₁.space] J ∧
      IsPLHomeomorphOn ρ (J ×ˢ Icc (-1 : ℝ) 1) W₀ ∧
      IsPLHomeomorphOn σ (J ×ˢ Icc (-1 : ℝ) 1) W₁ ∧
      (∀ x ∈ J, ρ (x, 0) = x) ∧ (∀ x ∈ J, σ (x, 0) = x) ∧
      P 0 = ρ '' (J ×ˢ Icc (-1 : ℝ) 0) ∧ P 2 = ρ '' (J ×ˢ Icc (0 : ℝ) 1) ∧
      P 1 = σ '' (J ×ˢ Icc (-1 : ℝ) 0) ∧ P 3 = σ '' (J ×ˢ Icc (0 : ℝ) 1) ∧
      P 0 ∪ P 2 = W₀ ∧ P 1 ∪ P 3 = W₁ ∧
      N ∩ K₀.space = N ∩ (P 0 ∪ P 2) ∧ N ∩ K₁.space = N ∩ (P 1 ∪ P 3) ∧
      (⋃ i, P i) = W₀ ∪ W₁ ∧
      (∀ i, IsPolyhedron (P i) ∧ IsConnected (P i \ J) ∧ closure (P i \ J) = P i) ∧
      (∀ i j, i ≠ j → P i ∩ P j = J) ∧
      (∀ i, ∀ x ∈ P i \ J, connectedComponentIn ((W₀ ∪ W₁) \ J) x = P i \ J) ∧
      Function.Injective (fun i => P i \ J) := by
  have hUneigh : U ∈ 𝓝ˢ J := mem_nhdsSet_iff_forall.mpr fun x hx => hU.mem_nhds (hJU hx)
  obtain ⟨W₀, ρ, -, hW₀int, hW₀U, hN₀, hρ, hρ₀⟩ :=
    hK₀.exists_bicollar_of_isPLSphere_one K₀ hor₀ hJ hJ₀ hBd₀
      (Filter.mem_inf_of_left hUneigh)
  obtain ⟨W₁, σ, -, hW₁int, hW₁U, hN₁, hσ, hσ₀⟩ :=
    hK₁.exists_bicollar_of_isPLSphere_one K₁ hor₁ hJ hJ₁ hBd₁
      (Filter.mem_inf_of_left hUneigh)
  have hW₀K := hW₀int.trans sdiff_subset
  have hW₁K := hW₁int.trans sdiff_subset
  let A := ρ '' (J ×ˢ Icc (-1 : ℝ) 0)
  let B := σ '' (J ×ˢ Icc (-1 : ℝ) 0)
  let C := ρ '' (J ×ˢ Icc (0 : ℝ) 1)
  let D := σ '' (J ×ˢ Icc (0 : ℝ) 1)
  obtain ⟨hA, hC, hAC, hACJ, -, -, hcA, hcC, hclA, hclC⟩ :=
    hρ.centered_bicollar_half_images hJ.isPolyhedron hJ.isConnected hρ₀
  obtain ⟨hB, hD, hBD, hBDJ, -, -, hcB, hcD, hclB, hclD⟩ :=
    hσ.centered_bicollar_half_images hJ.isPolyhedron hJ.isConnected hσ₀
  change A ∪ C = W₀ at hAC
  change B ∪ D = W₁ at hBD
  change A ∩ C = J at hACJ
  change B ∩ D = J at hBDJ
  have hAW : A ⊆ W₀ := hAC ▸ subset_union_left
  have hCW : C ⊆ W₀ := hAC ▸ subset_union_right
  have hBW : B ⊆ W₁ := hBD ▸ subset_union_left
  have hDW : D ⊆ W₁ := hBD ▸ subset_union_right
  have hJA : J ⊆ A := hACJ.symm.subset.trans inter_subset_left
  have hJC : J ⊆ C := hACJ.symm.subset.trans inter_subset_right
  have hJB : J ⊆ B := hBDJ.symm.subset.trans inter_subset_left
  have hJD : J ⊆ D := hBDJ.symm.subset.trans inter_subset_right
  have hcross {L R : Set E} (hL : L ⊆ W₀) (hR : R ⊆ W₁)
      (hJL : J ⊆ L) (hJR : J ⊆ R) : L ∩ R = J := by
    apply Subset.antisymm
    · exact fun _ hx => htrace ⟨⟨hW₀K (hL hx.1), hW₁K (hR hx.2)⟩, hW₀U (hL hx.1)⟩
    · exact fun _ hx => ⟨hJL hx, hJR hx⟩
  have hAB := hcross hAW hBW hJA hJB
  have hAD := hcross hAW hDW hJA hJD
  have hCB := hcross hCW hBW hJC hJB
  have hCD := hcross hCW hDW hJC hJD
  let P : Fin 4 → Set E := ![A, B, C, D]
  have hpages : ∀ i, IsPolyhedron (P i) ∧ IsConnected (P i \ J) ∧
      closure (P i \ J) = P i := by
    intro i
    fin_cases i
    · exact ⟨hA, hcA, hclA⟩
    · exact ⟨hB, hcB, hclB⟩
    · exact ⟨hC, hcC, hclC⟩
    · exact ⟨hD, hcD, hclD⟩
  have hpair : ∀ i j, i ≠ j → P i ∩ P j = J := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> try exact (hij rfl).elim
    · exact hAB
    · exact hACJ
    · exact hAD
    · exact (inter_comm _ _).trans hAB
    · exact (inter_comm _ _).trans hCB
    · exact hBDJ
    · exact (inter_comm _ _).trans hACJ
    · exact hCB
    · exact hCD
    · exact (inter_comm _ _).trans hAD
    · exact (inter_comm _ _).trans hBDJ
    · exact (inter_comm _ _).trans hCD
  have hcover : (⋃ i, P i) = W₀ ∪ W₁ := by
    apply Subset.antisymm
    · intro x hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      fin_cases i
      · exact Or.inl (hAW hi)
      · exact Or.inr (hBW hi)
      · exact Or.inl (hCW hi)
      · exact Or.inr (hDW hi)
    · intro x hx
      rcases hx with hx | hx
      · rcases hAC.symm.subset hx with hx | hx
        · exact mem_iUnion.mpr ⟨0, hx⟩
        · exact mem_iUnion.mpr ⟨2, hx⟩
      · rcases hBD.symm.subset hx with hx | hx
        · exact mem_iUnion.mpr ⟨1, hx⟩
        · exact mem_iUnion.mpr ⟨3, hx⟩
  obtain ⟨O₀, hO₀, hJO₀, hO₀W⟩ := mem_nhdsSetWithin.mp hN₀
  obtain ⟨O₁, hO₁, hJO₁, hO₁W⟩ := mem_nhdsSetWithin.mp hN₁
  let N := (U ∩ O₀) ∩ O₁
  have hN : IsOpen N := (hU.inter hO₀).inter hO₁
  have hJN : J ⊆ N := fun x hx => ⟨⟨hJU hx, hJO₀ hx⟩, hJO₁ hx⟩
  have hNK₀ : N ∩ K₀.space = N ∩ (P 0 ∪ P 2) := by
    change N ∩ K₀.space = N ∩ (A ∪ C)
    rw [hAC]
    exact Subset.antisymm (fun _ hx => ⟨hx.1, hO₀W ⟨hx.1.1.2, hx.2⟩⟩)
      (fun _ hx => ⟨hx.1, hW₀K hx.2⟩)
  have hNK₁ : N ∩ K₁.space = N ∩ (P 1 ∪ P 3) := by
    change N ∩ K₁.space = N ∩ (B ∪ D)
    rw [hBD]
    exact Subset.antisymm (fun _ hx => ⟨hx.1, hO₁W ⟨hx.1.2, hx.2⟩⟩)
      (fun _ hx => ⟨hx.1, hW₁K hx.2⟩)
  refine ⟨N, W₀, W₁, ρ, σ, P, hN, hJN, fun _ hx => hx.1.1, hW₀int, hW₁int,
    union_subset hW₀U hW₁U, hN₀, hN₁, hρ, hσ, hρ₀, hσ₀,
    rfl, rfl, rfl, rfl, hAC, hBD, hNK₀, hNK₁, hcover, hpages, hpair, ?_, ?_⟩
  · intro i x hx
    rw [← hcover]
    exact connectedComponentIn_iUnion_sdiff_eq_of_inter_eq (fun i => (hpages i).1.isClosed)
      hpair (fun i => (hpages i).2.1.isPreconnected) i hx
  · intro i j hij
    by_contra hne
    obtain ⟨x, hxi⟩ := (hpages i).2.1.nonempty
    change P i \ J = P j \ J at hij
    have hxj := hij ▸ hxi
    exact hxi.2 ((hpair i j hne).subset ⟨hxi.1, hxj.1⟩)

end DifferentialGeometry.Topology.PiecewiseLinear
