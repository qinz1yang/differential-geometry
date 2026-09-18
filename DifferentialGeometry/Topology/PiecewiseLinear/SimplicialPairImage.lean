import DifferentialGeometry.Topology.PiecewiseLinear.AffineImageTransport
import DifferentialGeometry.Topology.PiecewiseLinear.FaceLink
import DifferentialGeometry.Topology.PiecewiseLinear.Gluing
import DifferentialGeometry.Topology.PiecewiseLinear.LinkSubdivision
import DifferentialGeometry.Topology.PiecewiseLinear.PLImage
import DifferentialGeometry.Topology.PiecewiseLinear.StarComplex
import DifferentialGeometry.Topology.PiecewiseLinear.Subcomplex

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

theorem exists_simplicialComplex_pair_image_of_isPiecewiseAffineOn [DecidableEq E] [DecidableEq F]
    (K M : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite M.faces]
    (hM : M.faces ⊆ K.faces) {p : E} (hp : {p} ∈ M.faces) {h : E → F}
    (hpl : IsPiecewiseAffineOn h K.space) (hinj : InjOn h K.space) :
    ∃ K₁ M₁ : Geometry.SimplicialComplex ℝ F, K₁.faces.Finite ∧ M₁.faces.Finite ∧
      M₁.faces ⊆ K₁.faces ∧ {h p} ∈ M₁.faces ∧
      K₁.space = h '' K.space ∧ M₁.space = h '' M.space ∧
      IsPLHomeomorphOn h K.space K₁.space ∧ IsPLHomeomorphOn h M.space M₁.space ∧
      ∃ g : E → F, IsPLHomeomorphOn g (SimplicialComplex.geometricLink M {p}).space
        (SimplicialComplex.geometricLink M₁ {h p}).space := by
  classical
  obtain ⟨K', hK', hK'fin, hAff⟩ := hpl.exists_isSubdivision_affineOn_faces K
  let _ : Finite K'.faces := hK'fin.to_subtype
  have hK'space : K'.space = K.space := hK'.space_eq
  have hMK : M.space ⊆ K.space := space_mono_of_faces_subset hM
  have hM' : IsSubdivision (restrict K' M.space) M := hK'.restrict M hM
  have hM'space : (restrict K' M.space).space = M.space := hM'.space_eq
  have hM'faces : (restrict K' M.space).faces ⊆ K'.faces := restrict_faces_subset K' M.space
  let _ : Finite (restrict K' M.space).faces := (restrict_faces_finite K' M.space).to_subtype
  obtain ⟨K₁, hK₁fin, hK₁space, hK₁faces, hK₁pl⟩ :=
    exists_simplicialComplex_image_of_affineOn_faces K' hAff (by rw [hK'space]; exact hinj)
  obtain ⟨M₁, ψ, hM₁fin, hM₁space, hM₁iso, hM₁pl, -, hM₁faces⟩ :=
    exists_isGlueIso_of_affineOn_faces (restrict K' M.space)
      (fun s hs => hAff s (hM'faces hs)) (by rw [hM'space]; exact hinj.mono hMK)
  have hpM' : ({p} : Finset E) ∈ (restrict K' M.space).faces := IsSubdivision.singleton_mem hM' hp
  refine ⟨K₁, M₁, hK₁fin, hM₁fin, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    obtain ⟨s, hs, rfl⟩ := (hM₁faces t).mp ht
    exact (hK₁faces _).mpr ⟨s, hM'faces hs, rfl⟩
  · refine (hM₁faces _).mpr ⟨{p}, hpM', ?_⟩
    rw [Finset.image_singleton]
  · rw [hK₁space, hK'space]
  · rw [hM₁space, hM'space]
  · rw [← hK'space]
    exact hK₁pl
  · rw [← hM'space]
    exact hM₁pl
  · obtain ⟨g, hg⟩ := exists_isPLHomeomorphOn_geometricLink_of_isSubdivision hM' hp
    let _ : Finite (SimplicialComplex.geometricLink (restrict K' M.space) {p}).faces :=
      (((restrict_faces_finite K' M.space).subset
        (geometricLink_faces_subset (restrict K' M.space) {p}))).to_subtype
    let _ : Finite (SimplicialComplex.geometricLink M₁ {h p}).faces :=
      (hM₁fin.subset (geometricLink_faces_subset M₁ {h p})).to_subtype
    exact ⟨_, hg.symm.trans (hM₁iso.geometricLink hpM').isPLHomeomorphOn⟩

end DifferentialGeometry.Topology.PiecewiseLinear
