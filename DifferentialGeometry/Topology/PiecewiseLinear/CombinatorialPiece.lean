import DifferentialGeometry.Topology.PiecewiseLinear.PieceRestrict
import DifferentialGeometry.Topology.PiecewiseLinear.VertexChart

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
noncomputable def combinatorialPLPieceIn {n : ℕ} (K : Geometry.SimplicialComplex ℝ E)
    [Finite K.faces] (hK : IsCombinatorialManifold (n + 1) K) (p : K.space) :
    letI := combinatorialChartedSpace K hK
    PLPieceIn E (n + 1) K.space univ := by
  let _ := combinatorialChartedSpace K hK
  let f : E → K.space := fun x => if hx : x ∈ K.space then ⟨x, hx⟩ else p
  have hf_eq (x : E) (hx : x ∈ K.space) : f x = (⟨x, hx⟩ : K.space) := by
    simp [f, hx]
  have hbij : BijOn f K.space univ := by
    refine ⟨fun x hx => mem_univ _, ?_, fun y _ => ⟨y.1, y.2, ?_⟩⟩
    · intro x hx y hy hxy
      have hval := congrArg Subtype.val hxy
      simpa only [hf_eq x hx, hf_eq y hy] using hval
    · exact hf_eq y.1 y.2
  refine ⟨K, Set.toFinite _, f, hbij, ?_, ?_, ?_⟩
  · have hcont : Continuous fun x : K.space => x := continuous_id
    rw [continuousOn_iff_continuous_domRestrict]
    exact hcont.congr fun x => (hf_eq x.1 x.2).symm
  · intro e he
    obtain ⟨q, hq, rfl⟩ := mem_combinatorialChartedSpace_atlas K hK he
    have hpa := isPiecewiseAffineOn_vertexChart K hq (hK.isPLSphere_link hq)
    have hdomain : K.space ∩ f ⁻¹' (vertexChart K hq (hK.isPLSphere_link hq)).source =
        Subtype.val '' (vertexChart K hq (hK.isPLSphere_link hq)).source := by
      ext x
      constructor
      · rintro ⟨hxK, hx⟩
        change f x ∈ (vertexChart K hq (hK.isPLSphere_link hq)).source at hx
        rw [hf_eq x hxK] at hx
        exact ⟨⟨x, hxK⟩, hx, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        refine ⟨x.2, ?_⟩
        change f x.1 ∈ (vertexChart K hq (hK.isPLSphere_link hq)).source
        rw [hf_eq x.1 x.2]
        exact hx
    rw [hdomain]
    exact hpa.congr fun x hx => by
      obtain ⟨y, hy, rfl⟩ := hx
      rw [Function.comp_apply, hf_eq y.1 y.2]
      change (vertexChart K hq (hK.isPLSphere_link hq)) ⟨y.1, y.2⟩ =
        if h : y.1 ∈ K.space then (vertexChart K hq (hK.isPLSphere_link hq)) ⟨y.1, h⟩ else 0
      rw [dif_pos y.2]
  · intro e he
    obtain ⟨q, hq, rfl⟩ := mem_combinatorialChartedSpace_atlas K hK he
    rw [preimage_univ, inter_univ]
    have hpa := isPiecewiseAffineOn_vertexChart_symm K hq (hK.isPLSphere_link hq)
    exact hpa.congr fun y hy => by
      change Function.invFunOn f K.space ((vertexChart K hq (hK.isPLSphere_link hq)).symm y) =
        (((vertexChart K hq (hK.isPLSphere_link hq)).symm y : K.space) : E)
      let z := (vertexChart K hq (hK.isPLSphere_link hq)).symm y
      change Function.invFunOn f K.space z = z.1
      have hz : z = f z.1 := (hf_eq z.1 z.2).symm
      calc
        Function.invFunOn f K.space z = Function.invFunOn f K.space (f z.1) :=
          congrArg (Function.invFunOn f K.space) hz
        _ = z.1 := hbij.invOn_invFunOn.1 z.2

open Classical in
noncomputable def combinatorialSubcomplexPLPieceIn {n : ℕ}
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold (n + 1) K) (p : K.space)
    (L : Geometry.SimplicialComplex ℝ E) (hL : L.faces ⊆ K.faces) :
    letI := combinatorialChartedSpace K hK
    PLPieceIn E (n + 1) K.space (Subtype.val ⁻¹' L.space) := by
  let _ := combinatorialChartedSpace K hK
  have himage : (combinatorialPLPieceIn K hK p).map '' L.space = Subtype.val ⁻¹' L.space := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hyK : y ∈ K.space := by
        obtain ⟨s, hs, hys⟩ := L.mem_space_iff.mp hy
        exact K.convexHull_subset_space (hL hs) hys
      change (((combinatorialPLPieceIn K hK p).map y : K.space) : E) ∈ L.space
      simpa only [combinatorialPLPieceIn, dif_pos hyK] using hy
    · intro hx
      refine ⟨x.1, hx, ?_⟩
      apply Subtype.ext
      simp only [combinatorialPLPieceIn, dif_pos x.2]
  rw [← himage]
  exact (combinatorialPLPieceIn K hK p).restrict L hL

end DifferentialGeometry.Topology.PiecewiseLinear
