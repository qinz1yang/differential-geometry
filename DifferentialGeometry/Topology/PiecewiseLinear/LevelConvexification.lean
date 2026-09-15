import DifferentialGeometry.Topology.PiecewiseLinear.FiberCoordinates
import DifferentialGeometry.Topology.PiecewiseLinear.HeightExtension
import DifferentialGeometry.Topology.PiecewiseLinear.PlanarSchoenflies

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_isPLHomeomorphOn_convex_image_of_subset_fiber
    (hdimE : Module.finrank ℝ E = 3) (ℓ : E →ₗ[ℝ] ℝ) (hℓ : ℓ ≠ 0)
    {D : Set E} (hD : IsPLBall 2 D) {r : ℝ} (hDr : D ⊆ {x | ℓ x = r})
    {W : Set E} (hW : Convex ℝ W) (hWopen : IsOpen W) (hDW : D ⊆ W) :
    ∃ h : E ≃ₜ E, IsPLHomeomorphOn h univ univ ∧ EqOn h id Wᶜ ∧
      (∀ x, ℓ (h x) = ℓ x) ∧ Convex ℝ (h '' D) ∧
      (∀ S : Set E, heightIndex (h '' S) ℓ = heightIndex S ℓ) := by
  classical
  obtain ⟨e, π, hleft, hfixed, -⟩ := exists_affine_coordinates_of_linear_fiber hdimE ℓ hℓ r
  obtain ⟨T, hT, hTcard, hDT, hTr, hTspan⟩ :=
    exists_affineIndependent_openSimplex_superset_of_subset_fiber hdimE ℓ hℓ
      hD.isPolyhedron.isCompact.isBounded hDr
  let P : Set E := convexHull ℝ (T : Set E)
  let Q : Finset (EuclideanSpace ℝ (Fin 2)) := T.image π
  let C₀ : Set (EuclideanSpace ℝ (Fin 2)) := convexHull ℝ (Q : Set _)
  have hP : IsPolyhedron P := isPolyhedron_convexHull_of_affineIndependent T hT
  have hDP : D ⊆ P := hDT.trans (openSimplex_subset_convexHull T)
  have hπinj : InjOn π P := by
    intro x hx y hy hxy
    exact ((hfixed x).mpr (hTr hx)).symm.trans ((congrArg e hxy).trans ((hfixed y).mpr (hTr hy)))
  have hQ : AffineIndependent ℝ ((↑) : Q → EuclideanSpace ℝ (Fin 2)) :=
    affineIndependent_image_of_injOn_convexHull π.toAffineMap hT hπinj
  have hQcard : Q.card = 3 := by
    rw [Finset.card_image_of_injOn (hπinj.mono (subset_convexHull ℝ _)), hTcard]
  have hQint : interior C₀ = openSimplex Q := interior_convexHull_eq_openSimplex hQ (by
    simpa only [finrank_euclideanSpace, Fintype.card_fin] using hQcard)
  have hC₀ : IsPolyhedron C₀ := isPolyhedron_convexHull_of_affineIndependent Q hQ
  have hπP : π '' P = C₀ := by
    change π.toAffineMap '' convexHull ℝ (T : Set E) = convexHull ℝ ((T.image π : Finset _) : Set _)
    rw [AffineMap.image_convexHull, Finset.coe_image]
    rfl
  have hπpl : IsPLHomeomorphOn π P C₀ :=
    isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn hP
      ((isPiecewiseAffineOn_of_affine π.toAffineMap isOpen_univ).mono_of_isPolyhedron hP (subset_univ _))
      ⟨fun x hx => hπP ▸ mem_image_of_mem π hx, hπinj, fun y hy => hπP.symm ▸ hy⟩
  have hepl : IsPLHomeomorphOn e C₀ P := hπpl.symm.congr (by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hπpl.bijOn.surjOn hy
    exact ((hfixed x).mpr (hTr hx)).trans (hπpl.bijOn.invOn_invFunOn.1 hx).symm)
  have hπopen : π '' openSimplex T = openSimplex Q := by
    have h := image_openSimplex_affineMap π.toAffineMap T (hπinj.mono (subset_convexHull ℝ _))
    simp only [LinearMap.coe_toAffineMap] at h
    convert h using 1
    congr 1
    ext y
    simp only [Q, Finset.mem_image]
  have hDπ : IsPLBall 2 (π '' D) :=
    hD.of_isPLHomeomorphOn (hπpl.restrict hD.isPolyhedron hDP)
  let U := interior C₀ ∩ e ⁻¹' W
  have hU : IsOpen U := isOpen_interior.inter
    (hWopen.preimage e.continuous_of_finiteDimensional)
  have hDU : π '' D ⊆ U := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [hQint, ← hπopen]
      exact mem_image_of_mem π (hDT hx)
    · change e (π x) ∈ W
      rw [(hfixed x).mpr (hDr hx)]
      exact hDW hx
  obtain ⟨g, C, hC, hg, hgD, -, hgfix⟩ :=
    exists_isPLHomeomorphOn_straighten_of_isPLBall_two hDπ hU hDU
  have hgfixC : EqOn g id C₀ᶜ := hgfix.mono
    (compl_subset_compl.mpr (inter_subset_left.trans interior_subset))
  have hgCbij : BijOn g C₀ C₀ := by
    simpa only [compl_compl] using ((bijOn_id C₀ᶜ).congr hgfixC.symm).compl g.bijective
  have hgC : IsPLHomeomorphOn g C₀ C₀ := by
    have h := hg.restrict hC₀ (subset_univ _)
    rwa [hgCbij.image_eq] at h
  let f : E → E := fun x => e (g (π x))
  have hf : IsPLHomeomorphOn f P P := hπpl.trans (hgC.trans hepl)
  have hTne : T.Nonempty := Finset.card_pos.mp (by omega)
  let L := simplexComplex T hT
  let B := simplexBoundary T hT
  have hLspace : L.space = P := simplexComplex_space T hT hTne
  let _ : Finite L.faces := (simplexComplex_faces_finite T hT).to_subtype
  have hB : B.faces ⊆ L.faces := simplexBoundary_faces_subset_simplexComplex T hT
  have hBP : B.space ⊆ P := by
    intro x hx
    obtain ⟨s, hs, hxs⟩ := B.mem_space_iff.mp hx
    exact convexHull_mono (Finset.coe_subset.mpr hs.1) hxs
  have hfix : EqOn f id B.space := by
    intro x hx
    have hxP := hBP hx
    have hxU : π x ∉ U := by
      rintro ⟨hxint, -⟩
      rw [hQint, ← hπopen] at hxint
      obtain ⟨y, hy, hyx⟩ := hxint
      have heq := hπinj (openSimplex_subset_convexHull T hy) hxP hyx
      have hxopen : x ∈ openSimplex T := heq ▸ hy
      rw [openSimplex_eq_sdiff_simplexBoundary T hT] at hxopen
      exact hxopen.2 hx
    change e (g (π x)) = x
    rw [hgfix hxU, id_eq]
    exact (hfixed x).mpr (hTr hxP)
  have hfW : EqOn f id (L.space \ W) := by
    rintro x ⟨hx, hxW⟩
    have hxP : x ∈ P := hLspace ▸ hx
    have hxU : π x ∉ U := by
      rintro ⟨-, hyW⟩
      apply hxW
      change e (π x) ∈ W at hyW
      rwa [(hfixed x).mpr (hTr hxP)] at hyW
    change e (g (π x)) = x
    rw [hgfix hxU, id_eq]
    exact (hfixed x).mpr (hTr hxP)
  have hbase : ∀ x ∈ L.space, x ∉ B.space → L.space ∈ 𝓝[{y | ℓ y = r}] x := by
    intro x hx hxB
    have hxP : x ∈ P := hLspace ▸ hx
    have hxopen : x ∈ openSimplex T := by
      rw [openSimplex_eq_sdiff_simplexBoundary T hT]
      exact ⟨hxP, hxB⟩
    have hgerm := (eventually_mem_convexHull_iff_sub_mem_vectorSpan hT hxopen).filter_mono
      (nhdsWithin_le_nhds (s := {y | ℓ y = r}))
    filter_upwards [hgerm, self_mem_nhdsWithin] with y hy hyl
    rw [hLspace]
    apply hy.mpr
    rw [hTspan, LinearMap.mem_ker, map_sub]
    exact sub_eq_zero.mpr (hyl.trans (hTr hxP).symm)
  have hfL : IsPLHomeomorphOn f L.space L.space := by rwa [hLspace]
  obtain ⟨h, hh, hhf, hhfix, hhℓ, hhInd⟩ :=
    exists_isPLHomeomorphOn_extension_preserving_height_of_eqOn_compl ℓ hℓ hB
      (hLspace.trans_le hTr) hbase hfL hfix hW hWopen hfW
  refine ⟨h, hh, hhfix, hhℓ, ?_, hhInd⟩
  have himage : h '' D = e '' C := by
    rw [(hhf.mono (hDP.trans_eq hLspace.symm)).image_eq]
    change (e ∘ g ∘ π) '' D = e '' C
    rw [image_comp, image_comp, hgD]
  rw [himage]
  exact hC.convex.affine_image e

end DifferentialGeometry.Topology.PiecewiseLinear
