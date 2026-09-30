import DifferentialGeometry.Topology.Engulfing.Simplex.Columns.ExceptionalIntersection
import DifferentialGeometry.Topology.Engulfing.Simplex.Columns.ColumnPolyhedron
import DifferentialGeometry.Topology.Engulfing.Simplex.SimplexEngulfingChart

namespace DifferentialGeometry.Topology.Engulfing

open Set _root_.Geometry

section Columns

variable {F ι : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem SimplexSplit.subset_columnSaturation (s : SimplexSplit ι) (v : ι → F)
    (hv : AffineIndependent ℝ v) {T : Set F} (hT : T ⊆ convexHull ℝ (range v)) :
    T ⊆ s.columnSaturation v hv T := fun x hx => ⟨hT hx, x, hx, rfl⟩

theorem SimplexSplit.columnSaturation_subset_simplex (s : SimplexSplit ι) (v : ι → F)
    (hv : AffineIndependent ℝ v) (T : Set F) :
    s.columnSaturation v hv T ⊆ convexHull ℝ (range v) := fun _ hx => hx.1

theorem SimplexSplit.columnSaturation_idem (s : SimplexSplit ι) (v : ι → F)
    (hv : AffineIndependent ℝ v) (T : Set F) :
    s.columnSaturation v hv (s.columnSaturation v hv T) = s.columnSaturation v hv T := by
  apply Subset.antisymm
  · rintro x ⟨hx, y, ⟨-, z, hz, hyz⟩, hxy⟩
    exact ⟨hx, z, hz, hxy.trans hyz⟩
  · exact s.subset_columnSaturation v hv (s.columnSaturation_subset_simplex v hv T)

theorem SimplexSplit.columnSaturation_empty (s : SimplexSplit ι) (v : ι → F)
    (hv : AffineIndependent ℝ v) : s.columnSaturation v hv ∅ = ∅ := by
  ext x
  simp [SimplexSplit.columnSaturation]

end Columns

variable {E : Type*} [DecidableEq E] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]

omit [DecidableEq E] in
theorem exists_exceptional_column_complex_of_generalPosition
    {n p q : ℕ} {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] [Finite κ]
    (hp : p + 3 ≤ n) (hqp : q ≤ p)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (w : E → EuclideanSpace ℝ (Fin n))
    (hgp : ∀ r : Finset E, (r : Set E) ⊆ K.vertices → r.card ≤ n + 1 →
      AffineIndependent ℝ (fun v : r => w v))
    (σ : K.faces) (hσ : σ.1.card ≤ q + 2)
    (t : κ → K.faces) (ht : ∀ i, (t i).1.card ≤ p + 1)
    (s : SimplexSplit ι) (v : ι → EuclideanSpace ℝ (Fin n))
    (hv : AffineIndependent ℝ v)
    (hshape : convexHull ℝ (range v) = convexHull ℝ (w '' (σ.1 : Set E)))
    (hshared : ∀ i, convexHull ℝ (w '' ((σ.1 : Set E) ∩ ((t i).1 : Set E))) ⊆
      s.lowerRoof v) :
    ∃ C : SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)), C.faces.Finite ∧
      (∀ u ∈ C.faces, u.card ≤ q) ∧ C.space ⊆ convexHull ℝ (range v) ∧
      s.columnSaturation v hv C.space = C.space ∧
      ∀ i, convexHull ℝ (range v) ∩ convexHull ℝ (w '' ((t i).1 : Set E)) ⊆
        s.lowerRoof v ∪ C.space := by
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
      rw [hshape] at hx
      rcases hinter i hx with hxroof | hxT
      · exact Or.inl (hshared i hxroof)
      · exact Or.inr (hCspace.symm ▸ s.subset_columnSaturation v hv hTin' hxT)
  · have hq' : q ≤ 1 := by omega
    refine ⟨⊥, finite_empty, fun _ hs => hs.elim, ?_, ?_, ?_⟩
    · rw [SimplicialComplex.space_bot]
      exact empty_subset _
    · simp only [SimplicialComplex.space_bot, s.columnSaturation_empty]
    · intro i x hx
      rw [hshape, generalPosition_intersection_eq_of_low_dimension hp hqp hq'
        K hK w hgp σ (t i) hσ (ht i)] at hx
      exact Or.inl (hshared i hx)

end DifferentialGeometry.Topology.Engulfing
