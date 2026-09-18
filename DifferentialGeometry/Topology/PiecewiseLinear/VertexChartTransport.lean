import DifferentialGeometry.Topology.PiecewiseLinear.ClosedStarNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.SimplicialPairImage
import DifferentialGeometry.Topology.PiecewiseLinear.StarComplex

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

theorem exists_simplicialComplex_pair_image_closedStar_of_isPiecewiseAffineOn
    [DecidableEq E] [DecidableEq F]
    (K M : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite M.faces]
    (hM : M.faces ⊆ K.faces) {p : E} (hp : {p} ∈ M.faces)
    {U : Set E} (hU : U ∈ 𝓝 p) {h : E → F}
    (hpl : IsPiecewiseAffineOn h U) (hinj : InjOn h U) :
    ∃ (R : Geometry.SimplicialComplex ℝ E) (K₁ M₁ : Geometry.SimplicialComplex ℝ F),
      IsSubdivision R K ∧ ({p} : Finset E) ∈ R.faces ∧ closedStar R p ⊆ U ∧
        K₁.faces.Finite ∧ M₁.faces.Finite ∧ M₁.faces ⊆ K₁.faces ∧
          ({h p} : Finset F) ∈ M₁.faces ∧
            K₁.space = h '' closedStar R p ∧
              M₁.space = h '' closedStar (restrict R M.space) p ∧
                ∀ n : ℕ, IsPLSphere n (SimplicialComplex.geometricLink M {p}).space →
                  IsPLSphere n (SimplicialComplex.geometricLink M₁ {h p}).space := by
  classical
  have hpK : p ∈ K.space :=
    K.convexHull_subset_space (hM hp) (subset_convexHull ℝ _ (by simp))
  obtain ⟨R, hRK, hRfin, hpR, hstarU⟩ :=
    exists_isSubdivision_closedStar_subset_of_mem_nhds K hpK hU
  let _ : Finite R.faces := hRfin.to_subtype
  have hM' : IsSubdivision (restrict R M.space) M := hRK.restrict M hM
  let _ : Finite (restrict R M.space).faces := (restrict_faces_finite R M.space).to_subtype
  have hM'faces : (restrict R M.space).faces ⊆ R.faces := restrict_faces_subset R M.space
  have hpM' : ({p} : Finset E) ∈ (restrict R M.space).faces := hM'.singleton_mem hp
  let _ : Finite (starComplex R p).faces := (starComplex_faces_finite R p).to_subtype
  let _ : Finite (starComplex (restrict R M.space) p).faces :=
    (starComplex_faces_finite (restrict R M.space) p).to_subtype
  have hKSspace : (starComplex R p).space = closedStar R p := starComplex_space R p hpR
  have hMSspace : (starComplex (restrict R M.space) p).space =
      closedStar (restrict R M.space) p := starComplex_space _ p hpM'
  have hMSfaces : (starComplex (restrict R M.space) p).faces ⊆ (starComplex R p).faces :=
    fun _ hs => ⟨hM'faces hs.1, hM'faces hs.2⟩
  have hpMS : ({p} : Finset E) ∈ (starComplex (restrict R M.space) p).faces :=
    singleton_mem_starComplex _ p hpM'
  have hKSU : (starComplex R p).space ⊆ U := by
    rw [hKSspace]
    exact hstarU
  obtain ⟨K₁, M₁, hK₁fin, hM₁fin, hfaces, hpM₁, hK₁space, hM₁space, -, -, hlinkMap⟩ :=
    exists_simplicialComplex_pair_image_of_isPiecewiseAffineOn (starComplex R p)
      (starComplex (restrict R M.space) p) hMSfaces hpMS
      (hpl.mono_of_isPolyhedron (isPolyhedron_space _) hKSU) (hinj.mono hKSU)
  refine ⟨R, K₁, M₁, hRK, hpR, hstarU, hK₁fin, hM₁fin, hfaces, hpM₁, ?_, ?_, ?_⟩
  · rw [hK₁space, hKSspace]
  · rw [hM₁space, hMSspace]
  · intro n hlink
    obtain ⟨g, hg⟩ := exists_isPLHomeomorphOn_geometricLink_of_isSubdivision hM' hp
    have h1 : IsPLSphere n (SimplicialComplex.geometricLink (restrict R M.space) {p}).space :=
      hlink.of_isPLHomeomorphOn hg.symm
    refine hlinkMap n ?_
    rw [geometricLink_starComplex]
    exact h1

end DifferentialGeometry.Topology.PiecewiseLinear
