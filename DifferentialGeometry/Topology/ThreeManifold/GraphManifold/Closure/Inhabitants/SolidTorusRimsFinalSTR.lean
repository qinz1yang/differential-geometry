import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.SolidTorusLocalCasesSTR

/-!
# S-SOLIDTORUS4 (suffix `_STR`), G7 part 7: `local_faces` and the rim facts

`local_faces_STR` by the four cases at a frontier point of `C₁` (cusp face only, vertical face
only, ball face only, the corner of the vertical and the ball face), and
`rims_STR : JunctionRimFacts74 A D rows_STR`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace GC.GraphManifold.Assembly.FC39P0.SolidTorusSTR

open GC.GraphManifold.Assembly.FC39P0.SolidTorusSTI GC.GraphManifold.Assembly.FC39P0

local instance carrierCharts_RimsFinalSTR : ChartedSpace (EuclideanHalfSpace 3) Wc.Carrier := by
  change ChartedSpace (EuclideanHalfSpace 3) solidTorusSet.{0}
  exact inferInstance

local instance carrierSmooth_RimsFinalSTR : IsManifold (𝓡∂ 3) ∞ Wc.Carrier := by
  change IsManifold (𝓡∂ 3) ∞ solidTorusSet.{0}
  exact inferInstance

theorem norm_sq_coords_STR (c : rows_STR.circle.Base) :
    ‖vOf_STR c‖ ^ 2 = vOf_STR c 0 * vOf_STR c 0 + vOf_STR c 1 * vOf_STR c 1 := by
  rw [← real_inner_self_eq_norm_sq, inner_two_STR]

/-- The cusp trace and the ball trace never meet in `C₁`. -/
theorem cusp_ball_STR (c : rows_STR.circle.Base) (hA : phiCusp_STR c = 0)
    (hB : phiBall_STR c ≤ 0) : phiBall_STR c < 0 := by
  refine lt_of_le_of_ne hB fun h => ?_
  have hn := norm_sq_coords_STR c
  have h0 : reL_STR (vOf_STR c) = 4 / 5 := by
    simp only [phiBall_STR, gBall_STR] at h
    linarith
  rw [reL_apply_STR] at h0
  simp only [phiCusp_STR, gCusp_STR] at hA
  nlinarith [sq_nonneg (vOf_STR c 1)]

/-- **`local_faces`** of the circle base of the rows. -/
theorem local_faces_STR : ∀ c ∈ frontier rows_STR.circle.cbase,
    ∃ U : TopologicalSpace.Opens rows_STR.circle.Base, c ∈ U ∧
      ∃ (L : Finset Lab_STR) (φ : Lab_STR → rows_STR.circle.Base → ℝ),
        1 ≤ L.card ∧ L.card ≤ 2 ∧
        (∀ f ∈ L, ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ (φ f) U ∧ φ f c = 0 ∧
          {c' | c' ∈ U ∧ c' ∈ rows_STR.circle.cbase ∧ φ f c' = 0} =
            {c' | c' ∈ U ∧ c' ∈ rows_STR.circle.cbase ∧
              rows_STR.circle.fibre c' ⊆ circleFaceSet rows_STR.slimPieces rows_STR.edge f}) ∧
        (Surjective fun w : TangentSpace (𝓡 2) c =>
          fun f : L => mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (φ f) c w) ∧
        rows_STR.circle.cbase ∩ (U : Set rows_STR.circle.Base) =
          {c' | c' ∈ U ∧ ∀ f ∈ L, φ f c' ≤ 0} := by
  intro c hc
  obtain ⟨hcm, hact⟩ := frontier_active_STR c hc
  obtain ⟨h1, h2, h3⟩ := mem_cbase_L_STR.1 hcm
  have h1' : phiCusp_STR c ≤ 0 := h1
  have h2' : phiVert_STR c ≤ 0 := h2
  have h3' : phiBall_STR c ≤ 0 := h3
  have hn := norm_q_sq_STR c
  by_cases hA : phiCusp_STR c = 0
  · -- the cusp trace only
    have hV : phiVert_STR c < 0 := by
      simp only [phiVert_STR, gVert_STR]
      simp only [phiCusp_STR, gCusp_STR] at hA
      linarith
    have hB : phiBall_STR c < 0 := cusp_ball_STR c hA h3'
    refine localFaces_single_STR c labCusp_STR (negOpen_STR labVert_STR labBall_STR) ⟨hV, hB⟩
      hA (mfderiv_phiCusp_ne_STR c) ?_
    intro c' hU
    rw [mem_cbase_L_STR]
    constructor
    · rintro ⟨x, -, -⟩
      exact x
    · intro hx
      exact ⟨hx, hU.1.le, hU.2.le⟩
  · by_cases hV : phiVert_STR c = 0
    · by_cases hB : phiBall_STR c = 0
      · obtain ⟨U, hcU, L, φ, -, rest⟩ :=
          localFaces_corner_STR c hV hB (lt_of_le_of_ne h1' hA)
        exact ⟨U, hcU, L, φ, rest⟩
      · -- the vertical trace only
        refine localFaces_single_STR c labVert_STR (negOpen_STR labCusp_STR labBall_STR)
          ⟨lt_of_le_of_ne h1' hA, lt_of_le_of_ne h3' hB⟩ hV (mfderiv_phiVert_ne_STR c) ?_
        intro c' hU
        rw [mem_cbase_L_STR]
        constructor
        · rintro ⟨-, x, -⟩
          exact x
        · intro hx
          exact ⟨hU.1.le, hx, hU.2.le⟩
    · -- the ball trace only
      have hB : phiBall_STR c = 0 := by
        rcases hact with h | h | h
        · exact absurd h hA
        · exact absurd h hV
        · exact h
      refine localFaces_single_STR c labBall_STR (negOpen_STR labCusp_STR labVert_STR)
        ⟨lt_of_le_of_ne h1' hA, lt_of_le_of_ne h2' hV⟩ hB (mfderiv_phiBall_ne_STR c) ?_
      intro c' hU
      rw [mem_cbase_L_STR]
      constructor
      · rintro ⟨-, -, x⟩
        exact x
      · intro hx
        exact ⟨hU.1.le, hU.2.le, hx⟩

/-- **The rim facts of the junctions of the solid torus cut.** -/
def rims_STR : JunctionRimFacts74 (stageGeometry_STR ballZeroDomainsL_STR)
    (cutChoice_STR ballZeroDomainsL_STR) rows_STR where
  rimBase := rimBase_STR
  rimBase_smooth := rimBase_smooth_STR
  rim_fibre c _ := rim_fibre_STR c
  edge_region := edge_region_STR
  local_faces := local_faces_STR

end GC.GraphManifold.Assembly.FC39P0.SolidTorusSTR
