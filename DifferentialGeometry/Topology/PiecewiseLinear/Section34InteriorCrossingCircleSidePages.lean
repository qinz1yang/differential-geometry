import DifferentialGeometry.Topology.PiecewiseLinear.Section34InteriorCrossingCirclePages
import DifferentialGeometry.Topology.PiecewiseLinear.Section34LocalBicollarSides
import DifferentialGeometry.Topology.PiecewiseLinear.Section34InteriorCrossingChartsSurface

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

private theorem page_side_identities {X : Type*} [TopologicalSpace X]
    {A B J W C : Set X} (hC : IsClosed C) (hcover : A ∪ B = W)
    (hinter : A ∩ B = J) (hJC : J ⊆ frontier C)
    (hin : A \ J ⊆ interior C) (hout : B \ J ⊆ Cᶜ) :
    A = W ∩ C ∧ B = W \ interior C ∧
      A \ J = W ∩ interior C ∧ B \ J = W ∩ Cᶜ := by
  have hJA : J ⊆ A := hinter.symm.subset.trans inter_subset_left
  have hJB : J ⊆ B := hinter.symm.subset.trans inter_subset_right
  have hW (x : X) : x ∈ W ↔ x ∈ A ∨ x ∈ B := by rw [← hcover]; rfl
  have hJin {x : X} (hx : x ∈ J) : x ∈ C := hC.frontier_subset (hJC hx)
  have hJout {x : X} (hx : x ∈ J) : x ∉ interior C := (hJC hx).2
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext x
    constructor
    · intro hx
      exact ⟨(hW x).mpr (Or.inl hx), by
        by_cases hj : x ∈ J
        · exact hJin hj
        · exact interior_subset (hin ⟨hx, hj⟩)⟩
    · rintro ⟨hw, hc⟩
      rcases (hW x).mp hw with ha | hb
      · exact ha
      · by_cases hj : x ∈ J
        · exact hJA hj
        · exact (hout ⟨hb, hj⟩ hc).elim
  · ext x
    constructor
    · intro hx
      refine ⟨(hW x).mpr (Or.inr hx), ?_⟩
      by_cases hj : x ∈ J
      · exact hJout hj
      · exact fun hi => hout ⟨hx, hj⟩ (interior_subset hi)
    · rintro ⟨hw, hc⟩
      rcases (hW x).mp hw with ha | hb
      · by_cases hj : x ∈ J
        · exact hJB hj
        · exact (hc (hin ⟨ha, hj⟩)).elim
      · exact hb
  · ext x
    constructor
    · intro hx
      exact ⟨(hW x).mpr (Or.inl hx.1), hin hx⟩
    · rintro ⟨hw, hi⟩
      have hj : x ∉ J := fun hx => hJout hx hi
      refine ⟨?_, hj⟩
      rcases (hW x).mp hw with ha | hb
      · exact ha
      · exact (hout ⟨hb, hj⟩ (interior_subset hi)).elim
  · ext x
    constructor
    · intro hx
      exact ⟨(hW x).mpr (Or.inr hx.1), hout hx⟩
    · rintro ⟨hw, ho⟩
      have hj : x ∉ J := fun hx => ho (hJin hx)
      refine ⟨?_, hj⟩
      rcases (hW x).mp hw with ha | hb
      · exact (ho (interior_subset (hin ⟨ha, hj⟩))).elim
      · exact hb

open Classical in
theorem exists_interior_crossing_circle_side_pages
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K₀ K₁ : Geometry.SimplicialComplex ℝ E) [Finite K₀.faces] [Finite K₁.faces]
    (hK₀ : IsCombinatorialManifoldWithBoundary 2 K₀)
    (hK₁ : IsCombinatorialManifoldWithBoundary 2 K₁)
    (hor₀ : IsOrientable 2 K₀) (hor₁ : IsOrientable 2 K₁)
    {X Y J U : Set E} (hX : IsClosed X) (hY : IsClosed Y)
    (hregX : closure (interior X) = X) (hregY : closure (interior Y) = Y)
    (hfrontX : U ∩ K₀.space = U ∩ frontier X)
    (hfrontY : U ∩ K₁.space = U ∩ frontier Y)
    (hJ : IsPLSphere 1 J) (hJ₀ : J ⊆ K₀.space) (hJ₁ : J ⊆ K₁.space)
    (hBd₀ : Disjoint J (boundaryComplex 2 K₀).space)
    (hBd₁ : Disjoint J (boundaryComplex 2 K₁).space)
    (hU : IsOpen U) (hJU : J ⊆ U) (htrace : (K₀.space ∩ K₁.space) ∩ U ⊆ J)
    (hcross : ∀ x ∈ J, HasPLCrossingAt K₀.space K₁.space x) :
    ∃ (N W₀ W₁ : Set E) (P : Fin 4 → Set E),
      IsOpen N ∧ J ⊆ N ∧ N ⊆ U ∧
      W₀ ⊆ K₀.space \ (boundaryComplex 2 K₀).space ∧
      W₁ ⊆ K₁.space \ (boundaryComplex 2 K₁).space ∧
      W₀ ∪ W₁ ⊆ U ∧ W₀ ∈ 𝓝ˢ[K₀.space] J ∧ W₁ ∈ 𝓝ˢ[K₁.space] J ∧
      P 0 ∪ P 2 = W₀ ∧ P 1 ∪ P 3 = W₁ ∧
      N ∩ K₀.space = N ∩ W₀ ∧ N ∩ K₁.space = N ∩ W₁ ∧
      (⋃ i, P i) = W₀ ∪ W₁ ∧
      (∀ i, IsPolyhedron (P i) ∧ IsConnected (P i \ J) ∧ closure (P i \ J) = P i) ∧
      (∀ i j, i ≠ j → P i ∩ P j = J) ∧
      (∀ i, ∀ x ∈ P i \ J, connectedComponentIn ((W₀ ∪ W₁) \ J) x = P i \ J) ∧
      Function.Injective (fun i => P i \ J) ∧
      P 0 = W₀ ∩ Y ∧ P 2 = W₀ \ interior Y ∧
      P 1 = W₁ ∩ X ∧ P 3 = W₁ \ interior X ∧
      P 0 \ J = W₀ ∩ interior Y ∧ P 2 \ J = W₀ ∩ Yᶜ ∧
      P 1 \ J = W₁ ∩ interior X ∧ P 3 \ J = W₁ ∩ Xᶜ ∧
      N ∩ (P 0 \ J) = N ∩ (K₀.space ∩ interior Y) ∧
      N ∩ (P 2 \ J) = N ∩ (K₀.space ∩ Yᶜ) ∧
      N ∩ (P 1 \ J) = N ∩ (K₁.space ∩ interior X) ∧
      N ∩ (P 3 \ J) = N ∩ (K₁.space ∩ Xᶜ) := by
  obtain ⟨N, W₀, W₁, ρ, σ, P, hN, hJN, hNU, hW₀int, hW₁int, hWU, hN₀, hN₁,
    hρ, hσ, hρ₀, hσ₀, hP₀, hP₂, hP₁, hP₃, hcover₀, hcover₁, hNK₀, hNK₁,
    hcover, hpages, hpair, hcomp, hinj⟩ :=
    exists_interior_crossing_circle_pages K₀ K₁ hK₀ hK₁ hor₀ hor₁ hJ hJ₀ hJ₁
      hBd₀ hBd₁ hU hJU htrace
  have hW₀K := hW₀int.trans sdiff_subset
  have hW₁K := hW₁int.trans sdiff_subset
  have hJX : J ⊆ frontier X := fun _ hy => (hfrontX.subset ⟨hJU hy, hJ₀ hy⟩).2
  have hJY : J ⊆ frontier Y := fun _ hy => (hfrontY.subset ⟨hJU hy, hJ₁ hy⟩).2
  obtain ⟨x, hx⟩ := hJ.nonempty
  have hJW₀ : J ⊆ W₀ := fun y hy => hρ₀ y hy ▸ hρ.bijOn.mapsTo ⟨hy, by norm_num⟩
  have hJW₁ : J ⊆ W₁ := fun y hy => hσ₀ y hy ▸ hσ.bijOn.mapsTo ⟨hy, by norm_num⟩
  have ht₀ : W₀ ∩ frontier Y = J := Subset.antisymm
    (fun _ hy => htrace ⟨⟨hW₀K hy.1,
      (hfrontY.symm.subset ⟨hWU (Or.inl hy.1), hy.2⟩).2⟩, hWU (Or.inl hy.1)⟩)
    (fun _ hy => ⟨hJW₀ hy, hJY hy⟩)
  have ht₁ : W₁ ∩ frontier X = J := Subset.antisymm
    (fun _ hy => htrace ⟨⟨(hfrontX.symm.subset ⟨hWU (Or.inr hy.1), hy.2⟩).2,
      hW₁K hy.1⟩, hWU (Or.inr hy.1)⟩)
    (fun _ hy => ⟨hJW₁ hy, hJX hy⟩)
  have hs₀ : (P 0 \ J ⊆ interior Y ∧ P 2 \ J ⊆ Yᶜ) ∨
      (P 0 \ J ⊆ Yᶜ ∧ P 2 \ J ⊆ interior Y) := by
    obtain ⟨O, hO, hJO, hOW⟩ := mem_nhdsSetWithin.mp hN₀
    have hn : W₀ ∈ 𝓝[K₀.space] x := Filter.mem_of_superset
      (Filter.inter_mem (mem_nhdsWithin_of_mem_nhds (hO.mem_nhds (hJO hx)))
        self_mem_nhdsWithin) hOW
    obtain ⟨-, -, -, -, hneg, hpos, -⟩ :=
      hρ.centered_bicollar_half_images hJ.isPolyhedron hJ.isConnected hρ₀
    rw [hP₀, hP₂, hneg, hpos]
    have hc : HasPLCrossingAt K₀.space (frontier Y) x := by
      apply (hcross x hx).congr (Filter.Eventually.of_forall fun _ => Iff.rfl)
      filter_upwards [hU.mem_nhds (hJU hx)] with y hy
      exact ⟨fun hm => (hfrontY.subset ⟨hy, hm⟩).2,
        fun hm => (hfrontY.symm.subset ⟨hy, hm⟩).2⟩
    exact hc.opposite_bicollar_sides_of_local_surface
      (fun N hN => hK₀.exists_surface_ball_chart_of_notMem_boundaryComplex
        (hJ₀ hx) (fun hb => disjoint_left.mp hBd₀ hx hb) hN)
      hJ.isConnected.isPreconnected hx hρ hρ₀ hn ht₀ hY hregY
  have hs₁ : (P 1 \ J ⊆ interior X ∧ P 3 \ J ⊆ Xᶜ) ∨
      (P 1 \ J ⊆ Xᶜ ∧ P 3 \ J ⊆ interior X) := by
    obtain ⟨O, hO, hJO, hOW⟩ := mem_nhdsSetWithin.mp hN₁
    have hn : W₁ ∈ 𝓝[K₁.space] x := Filter.mem_of_superset
      (Filter.inter_mem (mem_nhdsWithin_of_mem_nhds (hO.mem_nhds (hJO hx)))
        self_mem_nhdsWithin) hOW
    obtain ⟨-, -, -, -, hneg, hpos, -⟩ :=
      hσ.centered_bicollar_half_images hJ.isPolyhedron hJ.isConnected hσ₀
    rw [hP₁, hP₃, hneg, hpos]
    have hc : HasPLCrossingAt K₁.space (frontier X) x := by
      apply (hcross x hx).symm.congr (Filter.Eventually.of_forall fun _ => Iff.rfl)
      filter_upwards [hU.mem_nhds (hJU hx)] with y hy
      exact ⟨fun hm => (hfrontX.subset ⟨hy, hm⟩).2,
        fun hm => (hfrontX.symm.subset ⟨hy, hm⟩).2⟩
    exact hc.opposite_bicollar_sides_of_local_surface
      (fun N hN => hK₁.exists_surface_ball_chart_of_notMem_boundaryComplex
        (hJ₁ hx) (fun hb => disjoint_left.mp hBd₁ hx hb) hN)
      hJ.isConnected.isPreconnected hx hσ hσ₀ hn ht₁ hX hregX
  obtain ⟨τ, ht₀, ht₁, hi₀, ho₂, hi₁, ho₃⟩ : ∃ τ : Fin 4 ≃ Fin 4,
      P (τ 0) ∪ P (τ 2) = W₀ ∧ P (τ 1) ∪ P (τ 3) = W₁ ∧
      P (τ 0) \ J ⊆ interior Y ∧ P (τ 2) \ J ⊆ Yᶜ ∧
      P (τ 1) \ J ⊆ interior X ∧ P (τ 3) \ J ⊆ Xᶜ := by
    rcases hs₀ with ⟨hi₀, ho₂⟩ | ⟨ho₀, hi₂⟩ <;>
      rcases hs₁ with ⟨hi₁, ho₃⟩ | ⟨ho₁, hi₃⟩
    · exact ⟨Equiv.refl _, hcover₀, hcover₁, hi₀, ho₂, hi₁, ho₃⟩
    · refine ⟨Equiv.swap 1 3, ?_⟩
      have hh : P 0 ∪ P 2 = W₀ ∧ P 1 ∪ P 3 = W₁ ∧
          P 0 \ J ⊆ interior Y ∧ P 2 \ J ⊆ Yᶜ ∧
          P 3 \ J ⊆ interior X ∧ P 1 \ J ⊆ Xᶜ :=
        ⟨hcover₀, hcover₁, hi₀, ho₂, hi₃, ho₁⟩
      simpa [Equiv.swap_apply_def, union_comm] using hh
    · refine ⟨Equiv.swap 0 2, ?_⟩
      have hh : P 0 ∪ P 2 = W₀ ∧ P 1 ∪ P 3 = W₁ ∧
          P 2 \ J ⊆ interior Y ∧ P 0 \ J ⊆ Yᶜ ∧
          P 1 \ J ⊆ interior X ∧ P 3 \ J ⊆ Xᶜ :=
        ⟨hcover₀, hcover₁, hi₂, ho₀, hi₁, ho₃⟩
      simpa [Equiv.swap_apply_def, union_comm] using hh
    · refine ⟨(Equiv.swap 0 2).trans (Equiv.swap 1 3), ?_⟩
      have hh : P 0 ∪ P 2 = W₀ ∧ P 1 ∪ P 3 = W₁ ∧
          P 2 \ J ⊆ interior Y ∧ P 0 \ J ⊆ Yᶜ ∧
          P 3 \ J ⊆ interior X ∧ P 1 \ J ⊆ Xᶜ :=
        ⟨hcover₀, hcover₁, hi₂, ho₀, hi₃, ho₁⟩
      simpa [Equiv.swap_apply_def, union_comm] using hh
  let Q : Fin 4 → Set E := P ∘ τ
  have hpairQ (i j : Fin 4) (hij : i ≠ j) : Q i ∩ Q j = J :=
    hpair _ _ (fun heq => hij (τ.injective heq))
  obtain ⟨hQ₀, hQ₂, hc₀, hc₂⟩ := page_side_identities hY ht₀
    (hpairQ 0 2 (by decide)) (fun _ hy => hJY hy) hi₀ ho₂
  obtain ⟨hQ₁, hQ₃, hc₁, hc₃⟩ := page_side_identities hX ht₁
    (hpairQ 1 3 (by decide)) (fun _ hy => hJX hy) hi₁ ho₃
  have hn₀ := hNK₀.trans (congrArg (N ∩ ·) hcover₀)
  have hn₁ := hNK₁.trans (congrArg (N ∩ ·) hcover₁)
  refine ⟨N, W₀, W₁, Q, hN, hJN, hNU, hW₀int, hW₁int, hWU, hN₀, hN₁,
    ht₀, ht₁, hn₀, hn₁, ?_, fun i => hpages (τ i), hpairQ,
    fun i => hcomp (τ i), hinj.comp τ.injective, hQ₀, hQ₂, hQ₁, hQ₃,
    hc₀, hc₂, hc₁, hc₃, ?_, ?_, ?_, ?_⟩
  · change (⋃ i, P (τ i)) = W₀ ∪ W₁
    rw [τ.surjective.iUnion_comp, hcover]
  · dsimp only [Q, Function.comp_apply]
    rw [hc₀, ← inter_assoc, ← hn₀, inter_assoc]
  · dsimp only [Q, Function.comp_apply]
    rw [hc₂, ← inter_assoc, ← hn₀, inter_assoc]
  · dsimp only [Q, Function.comp_apply]
    rw [hc₁, ← inter_assoc, ← hn₁, inter_assoc]
  · dsimp only [Q, Function.comp_apply]
    rw [hc₃, ← inter_assoc, ← hn₁, inter_assoc]

end DifferentialGeometry.Topology.PiecewiseLinear
