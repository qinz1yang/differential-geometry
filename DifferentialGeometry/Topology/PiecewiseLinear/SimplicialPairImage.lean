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

theorem exists_simplicialComplex_triple_image_of_isPiecewiseAffineOn
    [DecidableEq E] [DecidableEq F]
    (K M N : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite M.faces] [Finite N.faces]
    (hM : M.faces ⊆ K.faces) (hN : N.faces ⊆ K.faces) {p : E}
    (hpM : {p} ∈ M.faces) (hpN : {p} ∈ N.faces) {h : E → F}
    (hpl : IsPiecewiseAffineOn h K.space) (hinj : InjOn h K.space) :
    ∃ K₁ M₁ N₁ : Geometry.SimplicialComplex ℝ F,
      K₁.faces.Finite ∧ M₁.faces.Finite ∧ N₁.faces.Finite ∧
      M₁.faces ⊆ K₁.faces ∧ N₁.faces ⊆ K₁.faces ∧
      {h p} ∈ M₁.faces ∧ {h p} ∈ N₁.faces ∧
      K₁.space = h '' K.space ∧ M₁.space = h '' M.space ∧ N₁.space = h '' N.space ∧
      IsPLHomeomorphOn h K.space K₁.space ∧ IsPLHomeomorphOn h M.space M₁.space ∧
      IsPLHomeomorphOn h N.space N₁.space ∧
      (∃ g : E → F, IsPLHomeomorphOn g (SimplicialComplex.geometricLink M {p}).space
        (SimplicialComplex.geometricLink M₁ {h p}).space) ∧
      (∃ g : E → F, IsPLHomeomorphOn g (SimplicialComplex.geometricLink N {p}).space
        (SimplicialComplex.geometricLink N₁ {h p}).space) := by
  classical
  obtain ⟨K', hK', hK'fin, hAff⟩ := hpl.exists_isSubdivision_affineOn_faces K
  let _ : Finite K'.faces := hK'fin.to_subtype
  have hK'space : K'.space = K.space := hK'.space_eq
  have hMK : M.space ⊆ K.space := space_mono_of_faces_subset hM
  have hNK : N.space ⊆ K.space := space_mono_of_faces_subset hN
  have hM' : IsSubdivision (restrict K' M.space) M := hK'.restrict M hM
  have hN' : IsSubdivision (restrict K' N.space) N := hK'.restrict N hN
  have hM'space : (restrict K' M.space).space = M.space := hM'.space_eq
  have hN'space : (restrict K' N.space).space = N.space := hN'.space_eq
  have hM'faces : (restrict K' M.space).faces ⊆ K'.faces := restrict_faces_subset K' M.space
  have hN'faces : (restrict K' N.space).faces ⊆ K'.faces := restrict_faces_subset K' N.space
  let _ : Finite (restrict K' M.space).faces := (restrict_faces_finite K' M.space).to_subtype
  let _ : Finite (restrict K' N.space).faces := (restrict_faces_finite K' N.space).to_subtype
  obtain ⟨K₁, hK₁fin, hK₁space, hK₁faces, hK₁pl⟩ :=
    exists_simplicialComplex_image_of_affineOn_faces K' hAff (by rw [hK'space]; exact hinj)
  obtain ⟨M₁, ψM, hM₁fin, hM₁space, hM₁iso, hM₁pl, -, hM₁faces⟩ :=
    exists_isGlueIso_of_affineOn_faces (restrict K' M.space)
      (fun s hs => hAff s (hM'faces hs)) (by rw [hM'space]; exact hinj.mono hMK)
  obtain ⟨N₁, ψN, hN₁fin, hN₁space, hN₁iso, hN₁pl, -, hN₁faces⟩ :=
    exists_isGlueIso_of_affineOn_faces (restrict K' N.space)
      (fun s hs => hAff s (hN'faces hs)) (by rw [hN'space]; exact hinj.mono hNK)
  have hpM' : ({p} : Finset E) ∈ (restrict K' M.space).faces :=
    IsSubdivision.singleton_mem hM' hpM
  have hpN' : ({p} : Finset E) ∈ (restrict K' N.space).faces :=
    IsSubdivision.singleton_mem hN' hpN
  refine ⟨K₁, M₁, N₁, hK₁fin, hM₁fin, hN₁fin, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    obtain ⟨s, hs, rfl⟩ := (hM₁faces t).mp ht
    exact (hK₁faces _).mpr ⟨s, hM'faces hs, rfl⟩
  · intro t ht
    obtain ⟨s, hs, rfl⟩ := (hN₁faces t).mp ht
    exact (hK₁faces _).mpr ⟨s, hN'faces hs, rfl⟩
  · refine (hM₁faces _).mpr ⟨{p}, hpM', ?_⟩
    rw [Finset.image_singleton]
  · refine (hN₁faces _).mpr ⟨{p}, hpN', ?_⟩
    rw [Finset.image_singleton]
  · rw [hK₁space, hK'space]
  · rw [hM₁space, hM'space]
  · rw [hN₁space, hN'space]
  · rw [← hK'space]
    exact hK₁pl
  · rw [← hM'space]
    exact hM₁pl
  · rw [← hN'space]
    exact hN₁pl
  · obtain ⟨g, hg⟩ := exists_isPLHomeomorphOn_geometricLink_of_isSubdivision hM' hpM
    let _ : Finite (SimplicialComplex.geometricLink (restrict K' M.space) {p}).faces :=
      (((restrict_faces_finite K' M.space).subset
        (geometricLink_faces_subset (restrict K' M.space) {p}))).to_subtype
    let _ : Finite (SimplicialComplex.geometricLink M₁ {h p}).faces :=
      (hM₁fin.subset (geometricLink_faces_subset M₁ {h p})).to_subtype
    exact ⟨_, hg.symm.trans (hM₁iso.geometricLink hpM').isPLHomeomorphOn⟩
  · obtain ⟨g, hg⟩ := exists_isPLHomeomorphOn_geometricLink_of_isSubdivision hN' hpN
    let _ : Finite (SimplicialComplex.geometricLink (restrict K' N.space) {p}).faces :=
      (((restrict_faces_finite K' N.space).subset
        (geometricLink_faces_subset (restrict K' N.space) {p}))).to_subtype
    let _ : Finite (SimplicialComplex.geometricLink N₁ {h p}).faces :=
      (hN₁fin.subset (geometricLink_faces_subset N₁ {h p})).to_subtype
    exact ⟨_, hg.symm.trans (hN₁iso.geometricLink hpN').isPLHomeomorphOn⟩

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
  obtain ⟨K₁, M₁, -, hK₁fin, hM₁fin, -, hfaces, -, hpM₁, -, hK₁space, hM₁space, -, hK₁pl,
    hM₁pl, -, hlink, -⟩ :=
    exists_simplicialComplex_triple_image_of_isPiecewiseAffineOn K M M hM hM hp hp hpl hinj
  exact ⟨K₁, M₁, hK₁fin, hM₁fin, hfaces, hpM₁, hK₁space, hM₁space, hK₁pl, hM₁pl, hlink⟩

end DifferentialGeometry.Topology.PiecewiseLinear
