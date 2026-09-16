import DifferentialGeometry.Topology.PiecewiseLinear.SphereDisk
import DifferentialGeometry.Topology.PiecewiseLinear.BallInterior
import DifferentialGeometry.Topology.PiecewiseLinear.ConeIntersection
import DifferentialGeometry.Topology.Connected.ClosedCover
import DifferentialGeometry.Topology.PiecewiseLinear.ConeComplement
import DifferentialGeometry.Topology.PiecewiseLinear.ConeBase
import DifferentialGeometry.Topology.PiecewiseLinear.SubcomplexComplementLink

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [DecidableEq E]

theorem IsConeBase.exists_connectedComponentIn_pair_sdiff
    {K L : Geometry.SimplicialComplex ℝ E} [Finite K.faces] {p : E}
    (hp : IsConeBase p K) (hLK : L.faces ⊆ K.faces)
    (hK : IsPLSphere 2 K.space) (hL : IsPLSphere 1 L.space) :
    ∃ x ∈ (coneComplex hp).space \ (coneComplex (hp.of_faces_subset hLK)).space,
      ∃ y ∈ (coneComplex hp).space \ (coneComplex (hp.of_faces_subset hLK)).space,
        let C₀ := connectedComponentIn
          ((coneComplex hp).space \ (coneComplex (hp.of_faces_subset hLK)).space) x
        let C₁ := connectedComponentIn
          ((coneComplex hp).space \ (coneComplex (hp.of_faces_subset hLK)).space) y
        Disjoint C₀ C₁ ∧
        C₀ ∪ C₁ = (coneComplex hp).space \ (coneComplex (hp.of_faces_subset hLK)).space ∧
        IsPLBall 3 (closure C₀) ∧ IsPLBall 3 (closure C₁) ∧
        closure C₀ ∪ closure C₁ = (coneComplex hp).space ∧
        closure C₀ ∩ closure C₁ = (coneComplex (hp.of_faces_subset hLK)).space := by
  obtain ⟨D₀, D₁, hDunion, hDinter, f₀, f₁, hf₀, hf₁, hf₀L, hf₁L⟩ :=
    exists_disk_decomposition_of_isPLSphere_one_subset_two hK hL
      (space_mono_of_faces_subset hLK)
  have hD₀ : IsPLBall 2 D₀ := ⟨f₀, hf₀⟩
  have hD₁ : IsPLBall 2 D₁ := ⟨f₁, hf₁⟩
  let Q : Bool → Set E := fun b => if b then D₁ else D₀
  have hQ : ∀ b, IsPolyhedron (Q b) := by
    intro b
    cases b <;> simp only [Q, Bool.false_eq_true, ↓reduceIte]
    · exact hD₀.isPolyhedron
    · exact hD₁.isPolyhedron
  have hQK : ∀ b, Q b ⊆ K.space := by
    intro b
    cases b <;> simp only [Q, Bool.false_eq_true, ↓reduceIte]
    · exact subset_union_left.trans hDunion.subset
    · exact subset_union_right.trans hDunion.subset
  obtain ⟨T, hT, hTfinite, hQT⟩ := exists_isSubdivision_subcomplexes K Q hQ hQK
  let : Finite T.faces := hTfinite.to_subtype
  let A₀ := restrict T D₀
  let A₁ := restrict T D₁
  have hA₀ : A₀.space = D₀ := restrict_space_of_eq_biUnion T D₀ (hQT false)
  have hA₁ : A₁.space = D₁ := restrict_space_of_eq_biUnion T D₁ (hQT true)
  have hA₀T : A₀.faces ⊆ T.faces := restrict_faces_subset T D₀
  have hA₁T : A₁.faces ⊆ T.faces := restrict_faces_subset T D₁
  let : Finite A₀.faces := (restrict_faces_finite T D₀).to_subtype
  let : Finite A₁.faces := (restrict_faces_finite T D₁).to_subtype
  let hpT := hp.of_isSubdivision hT
  let hp₀ := hpT.of_faces_subset hA₀T
  let hp₁ := hpT.of_faces_subset hA₁T
  have hB₀ : (restrict A₀ A₁.space).space = L.space := by
    rw [restrict_space_eq_inter_of_faces_subset T A₀ A₁ hA₀T hA₁T, hA₀, hA₁, hDinter]
  have hB₁ : (restrict A₁ A₀.space).space = L.space := by
    rw [restrict_space_eq_inter_of_faces_subset T A₁ A₀ hA₁T hA₀T, hA₁, hA₀,
      inter_comm, hDinter]
  let hB₀A := restrict_faces_subset A₀ A₁.space
  let hB₁A := restrict_faces_subset A₁ A₀.space
  let C₀ := (coneComplex hp₀).space
  let C₁ := (coneComplex hp₁).space
  let J := (coneComplex (hp.of_faces_subset hLK)).space
  have hJ₀ : (coneComplex (hp₀.of_faces_subset hB₀A)).space = J := by
    ext z
    simp only [J, mem_coneComplex_space_iff, hB₀]
  have hJ₁ : (coneComplex (hp₁.of_faces_subset hB₁A)).space = J := by
    ext z
    simp only [J, mem_coneComplex_space_iff, hB₁]
  have hC₀ : IsPLBall 3 C₀ := hp₀.isPLBall_of_isPLBall (hA₀ ▸ hD₀)
  have hC₁ : IsPLBall 3 C₁ := hp₁.isPLBall_of_isPLBall (hA₁ ▸ hD₁)
  have hCunion : C₀ ∪ C₁ = (coneComplex hp).space := by
    ext z
    simp only [C₀, C₁, mem_union, mem_coneComplex_space_iff, hA₀, hA₁]
    constructor
    · rintro ((rfl | ⟨w, hw, t, ht, ht1, hzt⟩) | (rfl | ⟨w, hw, t, ht, ht1, hzt⟩))
      · exact Or.inl rfl
      · exact Or.inr ⟨w, hDunion.subset (Or.inl hw), t, ht, ht1, hzt⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨w, hDunion.subset (Or.inr hw), t, ht, ht1, hzt⟩
    · rintro (rfl | ⟨w, hw, t, ht, ht1, hzt⟩)
      · exact Or.inl (Or.inl rfl)
      · rcases hDunion.symm.subset hw with hw | hw
        · exact Or.inl (Or.inr ⟨w, hw, t, ht, ht1, hzt⟩)
        · exact Or.inr (Or.inr ⟨w, hw, t, ht, ht1, hzt⟩)
  have hCinter : C₀ ∩ C₁ = J := by
    exact (coneComplex_space_inter hpT hA₀T hA₁T hB₀A
      (restrict_space_eq_inter_of_faces_subset T A₀ A₁ hA₀T hA₁T).symm).trans hJ₀
  have hconn₀ : IsConnected (C₀ \ J) := by
    rw [← hJ₀]
    apply hp₀.isConnected_sdiff_coneComplex hB₀A
    rw [hA₀, hB₀, ← hf₀L]
    exact hf₀.isConnected_sdiff_image_stdSimplexBoundary
  have hconn₁ : IsConnected (C₁ \ J) := by
    rw [← hJ₁]
    apply hp₁.isConnected_sdiff_coneComplex hB₁A
    rw [hA₁, hB₁, ← hf₁L]
    exact hf₁.isConnected_sdiff_image_stdSimplexBoundary
  have hclosure₀ : closure (C₀ \ J) = C₀ := by
    rw [← hJ₀]
    apply hp₀.closure_sdiff_coneComplex hB₀A (hA₀ ▸ hD₀.nonempty)
    rw [hA₀, hB₀, ← hf₀L]
    exact hf₀.closure_sdiff_image_stdSimplexBoundary
  have hclosure₁ : closure (C₁ \ J) = C₁ := by
    rw [← hJ₁]
    apply hp₁.closure_sdiff_coneComplex hB₁A (hA₁ ▸ hD₁.nonempty)
    rw [hA₁, hB₁, ← hf₁L]
    exact hf₁.closure_sdiff_image_stdSimplexBoundary
  have hdiff₀ : C₀ \ J = C₀ \ C₁ := by
    rw [← hCinter]
    ext z
    simp only [mem_sdiff, mem_inter_iff]
    tauto
  have hdiff₁ : C₁ \ J = C₁ \ C₀ := by
    rw [← hCinter]
    ext z
    simp only [mem_sdiff, mem_inter_iff]
    tauto
  obtain ⟨x, hx⟩ := hconn₀.nonempty
  obtain ⟨y, hy⟩ := hconn₁.nonempty
  have hcomponent₀ : connectedComponentIn ((coneComplex hp).space \ J) x = C₀ \ J := by
    have h := Topology.connectedComponentIn_sdiff_inter_eq_sdiff hC₀.isPolyhedron.isClosed
      hC₁.isPolyhedron.isClosed (hdiff₀ ▸ hconn₀.isPreconnected) (hdiff₀ ▸ hx)
    rwa [hCunion, hCinter, ← hdiff₀] at h
  have hcomponent₁ : connectedComponentIn ((coneComplex hp).space \ J) y = C₁ \ J := by
    have h := Topology.connectedComponentIn_sdiff_inter_eq_sdiff hC₁.isPolyhedron.isClosed
      hC₀.isPolyhedron.isClosed (hdiff₁ ▸ hconn₁.isPreconnected) (hdiff₁ ▸ hy)
    rwa [union_comm C₁ C₀, inter_comm C₁ C₀, hCunion, hCinter, ← hdiff₁] at h
  refine ⟨x, ⟨hCunion.subset (Or.inl hx.1), hx.2⟩,
    y, ⟨hCunion.subset (Or.inr hy.1), hy.2⟩, ?_⟩
  dsimp only
  change Disjoint (connectedComponentIn ((coneComplex hp).space \ J) x)
    (connectedComponentIn ((coneComplex hp).space \ J) y) ∧ _
  rw [hcomponent₀, hcomponent₁]
  refine ⟨disjoint_left.mpr (fun z hz₀ hz₁ => hz₀.2 (hCinter.subset ⟨hz₀.1, hz₁.1⟩)), ?_, ?_⟩
  · rw [← union_sdiff_distrib, hCunion]
  · rw [hclosure₀, hclosure₁]
    exact ⟨hC₀, hC₁, hCunion, hCinter⟩

end DifferentialGeometry.Topology.PiecewiseLinear
