import DifferentialGeometry.Topology.Engulfing.Simplex.Columns.NewmanExceptionalColumns

namespace DifferentialGeometry.Topology.Engulfing

open Set _root_.Geometry

variable {E : Type*} [DecidableEq E] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]

omit [DecidableEq E] in
theorem exists_exceptional_column_complex_of_generalPosition_subsets
    {n p q : ℕ} {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] [Finite κ]
    (hp : p + 3 ≤ n) (hqp : q ≤ p)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (w : E → EuclideanSpace ℝ (Fin n))
    (hgp : ∀ r : Finset E, (r : Set E) ⊆ K.vertices → r.card ≤ n + 1 →
      AffineIndependent ℝ (fun v : r => w v))
    (σ : K.faces) (hσ : σ.1.card ≤ q + 2)
    (t : κ → K.faces) (ht : ∀ i, (t i).1.card ≤ p + 1)
    (S : κ → Set (EuclideanSpace ℝ (Fin n)))
    (hS : ∀ i, S i ⊆ convexHull ℝ (w '' ((t i).1 : Set E)))
    (s : SimplexSplit ι) (v : ι → EuclideanSpace ℝ (Fin n))
    (hv : AffineIndependent ℝ v)
    (hshape : convexHull ℝ (range v) = convexHull ℝ (w '' (σ.1 : Set E)))
    (hshared : ∀ i, convexHull ℝ (w '' ((σ.1 : Set E) ∩ ((t i).1 : Set E))) ∩ S i ⊆
      s.lowerRoof v) :
    ∃ C : SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)), C.faces.Finite ∧
      (∀ u ∈ C.faces, u.card ≤ q) ∧ C.space ⊆ convexHull ℝ (range v) ∧
      s.columnSaturation v hv C.space = C.space ∧
      ∀ i, convexHull ℝ (range v) ∩ S i ⊆ s.lowerRoof v ∪ C.space := by
  classical
  let : Fintype κ := Fintype.ofFinite κ
  by_cases hq : 2 ≤ q
  · obtain ⟨T, hT, hTdim, hTin, hinter⟩ :=
      exists_exceptional_complex_of_generalPosition hp hqp hq K hK w hgp σ hσ t ht
    have hTin' : T.space ⊆ convexHull ℝ (range v) := hshape.symm ▸ hTin
    have hdim : ∀ u ∈ T.faces, u.card ≤ (q - 2) + 1 := by
      intro u hu
      have := hTdim u hu
      omega
    obtain ⟨C, hC, hCspace, hCdim⟩ := s.exists_column_complex v hv T hT hTin' hdim
    refine ⟨C, hC, ?_, ?_, ?_, ?_⟩
    · intro u hu
      have := hCdim u hu
      omega
    · rw [hCspace]
      exact s.columnSaturation_subset_simplex v hv T.space
    · rw [hCspace, s.columnSaturation_idem]
    · intro i x hx
      have hxf : x ∈ convexHull ℝ (w '' (σ.1 : Set E)) ∩
          convexHull ℝ (w '' ((t i).1 : Set E)) := ⟨hshape ▸ hx.1, hS i hx.2⟩
      rcases hinter i hxf with hxroof | hxT
      · exact Or.inl (hshared i ⟨hxroof, hx.2⟩)
      · exact Or.inr (hCspace.symm ▸ s.subset_columnSaturation v hv hTin' hxT)
  · have hq' : q ≤ 1 := by omega
    refine ⟨⊥, finite_empty, fun _ hs => hs.elim, ?_, ?_, ?_⟩
    · rw [SimplicialComplex.space_bot]
      exact empty_subset _
    · simp only [SimplicialComplex.space_bot, s.columnSaturation_empty]
    · intro i x hx
      have hxf : x ∈ convexHull ℝ (w '' (σ.1 : Set E)) ∩
          convexHull ℝ (w '' ((t i).1 : Set E)) := ⟨hshape ▸ hx.1, hS i hx.2⟩
      rw [generalPosition_intersection_eq_of_low_dimension hp hqp hq'
        K hK w hgp σ (t i) hσ (ht i)] at hxf
      exact Or.inl (hshared i ⟨hxf, hx.2⟩)

end DifferentialGeometry.Topology.Engulfing
