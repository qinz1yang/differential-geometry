import DifferentialGeometry.Topology.PiecewiseLinear.Section34CurveHeightLevels
import DifferentialGeometry.Topology.PiecewiseLinear.CylinderCut
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldInvariance

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

open Classical in
theorem IsPiecewiseAffineOn.exists_graph_image
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hcard : ∀ s ∈ K.faces, s.card ≤ 2) {f : E → F}
    (hf : IsPiecewiseAffineOn f K.space) (hinj : InjOn f K.space) :
    ∃ L : Geometry.SimplicialComplex ℝ F, L.faces.Finite ∧ L.space = f '' K.space ∧
      ∀ s ∈ L.faces, s.card ≤ 2 := by
  obtain ⟨R, hR, hRfin, hAff⟩ := hf.exists_isSubdivision_affineOn_faces K
  let _ : Finite R.faces := hRfin.to_subtype
  have hRcard : ∀ s ∈ R.faces, s.card ≤ 2 := by
    intro s hs
    obtain ⟨t, ht, hst⟩ := hR.exists_face_subset hs
    exact ((R.indep hs).card_le_card_of_subset_affineSpan
      ((subset_convexHull ℝ _).trans (hst.trans (convexHull_subset_affineSpan _)))).trans
      (hcard t ht)
  obtain ⟨L, hLfin, hLspace, hfaces, -⟩ := exists_simplicialComplex_image_of_affineOn_faces R
    hAff (hR.space_eq.symm ▸ hinj)
  refine ⟨L, hLfin, by rw [hLspace, hR.space_eq], ?_⟩
  intro s hs
  obtain ⟨t, ht, rfl⟩ := (hfaces s).mp hs
  exact Finset.card_image_le.trans (hRcard t ht)

open Classical in
theorem IsPLHomeomorphOn.exists_graph_preimage_of_isPLSphere_one
    {P : Set E} {Q J : Set F} {f : E → F} (hf : IsPLHomeomorphOn f P Q)
    (hP : IsPolyhedron P) (hJ : IsPLSphere 1 J) :
    ∃ L : Geometry.SimplicialComplex ℝ E, L.faces.Finite ∧
      L.space = P ∩ f ⁻¹' J ∧ ∀ s ∈ L.faces, s.card ≤ 2 := by
  obtain ⟨K, hKfin, hKspace⟩ := hJ.isPolyhedron.exists_simplicialComplex
  let _ : Finite K.faces := hKfin.to_subtype
  have hK : IsCombinatorialManifold 1 K :=
    (hKspace.symm ▸ hJ).isCombinatorialManifold
  have hQ : IsPolyhedron Q := hf.image_eq ▸
    hP.image_of_isPiecewiseAffineOn hf.isPiecewiseAffineOn hf.bijOn.injOn
  obtain ⟨A, hAfin, hAspace⟩ := hQ.exists_simplicialComplex
  let _ : Finite A.faces := hAfin.to_subtype
  obtain ⟨R, hRfin, hRspace, hRfaces⟩ := exists_triangulation_inter K A
  let _ : Finite R.faces := hRfin.to_subtype
  have hRQ : R.space ⊆ Q := by rw [hRspace, hAspace]; exact inter_subset_right
  have hRcard : ∀ s ∈ R.faces, s.card ≤ 2 := by
    intro s hs
    obtain ⟨t, ht, u, hu, hst⟩ := hRfaces s hs
    exact ((R.indep hs).card_le_card_of_subset_affineSpan
      ((subset_convexHull ℝ _).trans
        ((hst.trans inter_subset_left).trans (convexHull_subset_affineSpan _)))).trans
      (hK.card_le K ht)
  have hτ := hf.symm
  obtain ⟨L, hLfin, hLspace, hLcard⟩ :=
    (hτ.isPiecewiseAffineOn.mono_of_isPolyhedron (isPolyhedron_space R) hRQ).exists_graph_image
      R hRcard (hτ.bijOn.injOn.mono hRQ)
  refine ⟨L, hLfin, ?_, hLcard⟩
  rw [hLspace, hRspace, hKspace, hAspace]
  ext x
  constructor
  · rintro ⟨y, ⟨hyJ, hyQ⟩, rfl⟩
    exact ⟨hτ.bijOn.mapsTo hyQ, by
      change f (Function.invFunOn f P y) ∈ J
      rw [hf.bijOn.invOn_invFunOn.2 hyQ]
      exact hyJ⟩
  · intro hx
    exact ⟨f x, ⟨hx.2, hf.bijOn.mapsTo hx.1⟩, hf.bijOn.invOn_invFunOn.1 hx.1⟩

open Classical in
theorem IsCylindricalDiagram.exists_finite_regular_slice
    {P : Set E} {S J : Set F} {f : E × ℝ → F}
    (hf : IsCylindricalDiagram f P S) (hP : IsPolyhedron P) (hJ : IsPLSphere 1 J)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) (hstrip : 0 < a ∨ b < 1) :
    ∃ (r : ℝ) (L : Geometry.SimplicialComplex ℝ (E × ℝ)),
      r ∈ Ioo a b ∧ L.faces.Finite ∧ L.space = (P ×ˢ Icc a b) ∩ f ⁻¹' J ∧
      (∀ s ∈ L.faces, s.card ≤ 2) ∧ r ∉ Prod.snd '' L.vertices ∧
      (J ∩ f '' (P ×ˢ {r})).Finite ∧
      ∀ x ∈ L.space ∩ {y | y.2 = r},
        ∃ p q : E × ℝ, p ≠ q ∧ ({p, q} : Finset (E × ℝ)) ∈ L.faces ∧ p.2 ≠ q.2 ∧
          x ∈ openSimplex ({p, q} : Finset (E × ℝ)) ∧
          ∀ᶠ y in 𝓝 x, y ∈ L.space ↔ ∃ t : ℝ, y = x + t • (q - p) := by
  obtain ⟨L, hLfin, hLspace, hLcard⟩ :=
    (hf.isPLHomeomorphOn_strip hP ha hb hstrip).exists_graph_preimage_of_isPLSphere_one
      (hP.prod isHPolytope_Icc.isPolyhedron) hJ
  let _ : Finite L.faces := hLfin.to_subtype
  obtain ⟨r, hr, hrv, hfin, hlocal⟩ :=
    exists_regular_height_of_card_le_two L hLcard (LinearMap.snd ℝ E ℝ) hab
  refine ⟨r, L, hr, hLfin, hLspace, hLcard, hrv, ?_, ?_⟩
  · apply (hfin.image f).subset
    rintro y ⟨hyJ, x, ⟨hxP, hxr⟩, rfl⟩
    refine ⟨x, ⟨?_, hxr⟩, rfl⟩
    rw [hLspace]
    exact ⟨⟨hxP, hxr.symm ▸ ⟨hr.1.le, hr.2.le⟩⟩, hyJ⟩
  · intro x hx
    obtain ⟨p, q, hpq, hpqL, hpqheight, hxs, hgerm⟩ := hlocal x hx
    refine ⟨p, q, hpq, ?_, hpqheight, ?_, hgerm⟩
    · convert hpqL using 1
      ext v
      simp
    · convert hxs using 1
      congr 1
      ext v
      simp

end DifferentialGeometry.Topology.PiecewiseLinear
