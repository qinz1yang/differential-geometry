import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.SolidTorusRimsFinalSTR
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.SolidTorusCornerPointsSTR

/-!
# Solid-torus rows fixture: the V32 completeness clause of the circle-base corners (lane S-BCF03d)

The v3.2 record `CircleBaseCornersV32` of the boundary route (R9, D80-8) is the production corner
model of `C₁` plus the clause "every face that contains the whole circle fibre of `y` is a label at
`y`". The boundary chain itself has no solid-torus instance (no standing sequence, no
`NearlyCuspidalBoundary` on the solid torus: the open item F77-1), so `circleBaseCornersV32_G6C`
cannot be instantiated here. On the rows-route fixture of S-SOLIDTORUS4 the same statement can be
checked for real:

* `local_faces_V32_STR_BC3d`: `local_faces_STR` (the FDC03 corner model of `C₁`) with the extra
  completeness clause, at every frontier point of `C₁` (cusp trace, vertical trace, ball trace,
  and the corner of the vertical and the ball face);
* `corner_V32_nonempty_STR_BC3d`: an actual endpoint `e` (rim base point `q±`) with the two labels
  `{labVert_STR, labBall_STR}`, `card = 2`, all clauses and completeness (the cusp face does not
  contain the fibre).
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace GC.GraphManifold.Assembly.FC39P0.SolidTorusSTR

open GC.GraphManifold.Assembly.FC39P0.SolidTorusSTI GC.GraphManifold.Assembly.FC39P0

local instance carrierCharts_V32BC3d : ChartedSpace (EuclideanHalfSpace 3) Wc.Carrier := by
  change ChartedSpace (EuclideanHalfSpace 3) solidTorusSet.{0}
  exact inferInstance

local instance carrierSmooth_V32BC3d : IsManifold (𝓡∂ 3) ∞ Wc.Carrier := by
  change IsManifold (𝓡∂ 3) ∞ solidTorusSet.{0}
  exact inferInstance

local instance decEqLab_V32BC3d : DecidableEq Lab_STR := Classical.decEq _

/-- Only the label `f` is active at `c` when every other label is strictly negative there. -/
theorem eq_of_phi_zero_BC3d {c : rows_STR.circle.Base} {f : Lab_STR}
    (h : ∀ g : Lab_STR, g ≠ f → phiL_STR g c < 0) :
    ∀ g : Lab_STR, phiL_STR g c = 0 → g = f := by
  intro g hg
  by_contra hne
  exact (h g hne).ne hg

/-- `localFaces_single_STR` with the completeness clause (and the label set `{f}`). -/
theorem localFaces_single_V32_BC3d (c : rows_STR.circle.Base) (f : Lab_STR)
    (U : TopologicalSpace.Opens rows_STR.circle.Base) (hcU : c ∈ U) (hz : phiL_STR f c = 0)
    (hreg : mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (phiL_STR f) c ≠ 0)
    (hcb : ∀ c' ∈ U, (c' ∈ rows_STR.circle.cbase ↔ phiL_STR f c' ≤ 0))
    (hother : ∀ g : Lab_STR, g ≠ f → phiL_STR g c < 0) :
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
          {c' | c' ∈ U ∧ ∀ f ∈ L, φ f c' ≤ 0} ∧
        (∀ g : Lab_STR, rows_STR.circle.fibre c ⊆
          circleFaceSet rows_STR.slimPieces rows_STR.edge g → g ∈ L) := by
  refine ⟨U, hcU, {f}, phiL_STR, by simp, by simp, ?_, ?_, ?_, ?_⟩
  · intro g hg
    have hgf : g = f := Finset.mem_singleton.mp hg
    subst hgf
    refine ⟨(contMDiff_phiL_STR g).contMDiffOn, hz, ?_⟩
    ext c'
    constructor
    · rintro ⟨hU, hcb', h0⟩
      exact ⟨hU, hcb', (fibre_iff_STR hcb').2 h0⟩
    · rintro ⟨hU, hcb', hs⟩
      exact ⟨hU, hcb', (fibre_iff_STR hcb').1 hs⟩
  · intro v
    obtain ⟨w, hw⟩ := surjective_of_ne_zero_JN74 hreg (v ⟨f, Finset.mem_singleton_self f⟩)
    refine ⟨w, funext fun k => ?_⟩
    have hk : k = ⟨f, Finset.mem_singleton_self f⟩ := Subtype.ext (Finset.mem_singleton.mp k.2)
    rw [hk]
    exact hw
  · ext c'
    constructor
    · rintro ⟨hc', hU⟩
      refine ⟨hU, fun g hg => ?_⟩
      rw [Finset.mem_singleton.mp hg]
      exact (hcb c' hU).1 hc'
    · rintro ⟨hU, hle⟩
      exact ⟨(hcb c' hU).2 (hle f (Finset.mem_singleton_self f)), hU⟩
  · intro g hg
    have hcm : c ∈ rows_STR.circle.cbase := (hcb c hcU).2 hz.le
    exact Finset.mem_singleton.2 (eq_of_phi_zero_BC3d hother g ((fibre_iff_STR hcm).1 hg))

/-- `localFaces_corner_STR` with the completeness clause (the cusp face is strictly negative, so
only the vertical and the ball face contain the fibre). -/
theorem localFaces_corner_V32_BC3d (c : rows_STR.circle.Base) (hV : phiVert_STR c = 0)
    (hB : phiBall_STR c = 0) (hA : phiCusp_STR c < 0) :
    ∃ U : TopologicalSpace.Opens rows_STR.circle.Base, c ∈ U ∧
      ∃ (L : Finset Lab_STR) (φ : Lab_STR → rows_STR.circle.Base → ℝ),
        L = {labVert_STR, labBall_STR} ∧ 1 ≤ L.card ∧ L.card ≤ 2 ∧
        (∀ f ∈ L, ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ (φ f) U ∧ φ f c = 0 ∧
          {c' | c' ∈ U ∧ c' ∈ rows_STR.circle.cbase ∧ φ f c' = 0} =
            {c' | c' ∈ U ∧ c' ∈ rows_STR.circle.cbase ∧
              rows_STR.circle.fibre c' ⊆ circleFaceSet rows_STR.slimPieces rows_STR.edge f}) ∧
        (Surjective fun w : TangentSpace (𝓡 2) c =>
          fun f : L => mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (φ f) c w) ∧
        rows_STR.circle.cbase ∩ (U : Set rows_STR.circle.Base) =
          {c' | c' ∈ U ∧ ∀ f ∈ L, φ f c' ≤ 0} ∧
        (∀ g : Lab_STR, rows_STR.circle.fibre c ⊆
          circleFaceSet rows_STR.slimPieces rows_STR.edge g → g ∈ L) := by
  obtain ⟨U, hcU, L, φ, hL, h1, h2, h3, h4, h5⟩ := localFaces_corner_STR c hV hB hA
  refine ⟨U, hcU, L, φ, hL, h1, h2, h3, h4, h5, fun g hg => ?_⟩
  have hcm : c ∈ rows_STR.circle.cbase := mem_cbase_L_STR.2 ⟨hA.le, hV.le, hB.le⟩
  have hz : phiL_STR g c = 0 := (fibre_iff_STR hcm).1 hg
  rw [hL]
  rcases lab_cases_STR g with rfl | rfl | rfl
  · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  · exact absurd hz hA.ne
  · exact Finset.mem_insert_self _ _

/-- **`local_faces` of the solid-torus rows with the V32 completeness clause**: at every frontier
point of `C₁` the labels of `local_faces_STR` contain every face that contains the whole circle
fibre. -/
theorem local_faces_V32_STR_BC3d : ∀ c ∈ frontier rows_STR.circle.cbase,
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
          {c' | c' ∈ U ∧ ∀ f ∈ L, φ f c' ≤ 0} ∧
        (∀ g : Lab_STR, rows_STR.circle.fibre c ⊆
          circleFaceSet rows_STR.slimPieces rows_STR.edge g → g ∈ L) := by
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
    refine localFaces_single_V32_BC3d c labCusp_STR (negOpen_STR labVert_STR labBall_STR)
      ⟨hV, hB⟩ hA (mfderiv_phiCusp_ne_STR c) ?_ ?_
    · intro c' hU
      rw [mem_cbase_L_STR]
      constructor
      · rintro ⟨x, -, -⟩
        exact x
      · intro hx
        exact ⟨hx, hU.1.le, hU.2.le⟩
    · intro g hg
      rcases lab_cases_STR g with rfl | rfl | rfl
      · exact hB
      · exact absurd rfl hg
      · exact hV
  · by_cases hV : phiVert_STR c = 0
    · by_cases hB : phiBall_STR c = 0
      · obtain ⟨U, hcU, L, φ, -, rest⟩ :=
          localFaces_corner_V32_BC3d c hV hB (lt_of_le_of_ne h1' hA)
        exact ⟨U, hcU, L, φ, rest⟩
      · -- the vertical trace only
        have hA' : phiCusp_STR c < 0 := lt_of_le_of_ne h1' hA
        have hB' : phiBall_STR c < 0 := lt_of_le_of_ne h3' hB
        refine localFaces_single_V32_BC3d c labVert_STR (negOpen_STR labCusp_STR labBall_STR)
          ⟨hA', hB'⟩ hV (mfderiv_phiVert_ne_STR c) ?_ ?_
        · intro c' hU
          rw [mem_cbase_L_STR]
          constructor
          · rintro ⟨-, x, -⟩
            exact x
          · intro hx
            exact ⟨hU.1.le, hx, hU.2.le⟩
        · intro g hg
          rcases lab_cases_STR g with rfl | rfl | rfl
          · exact hB'
          · exact hA'
          · exact absurd rfl hg
    · -- the ball trace only
      have hB : phiBall_STR c = 0 := by
        rcases hact with h | h | h
        · exact absurd h hA
        · exact absurd h hV
        · exact h
      have hA' : phiCusp_STR c < 0 := lt_of_le_of_ne h1' hA
      have hV' : phiVert_STR c < 0 := lt_of_le_of_ne h2' hV
      refine localFaces_single_V32_BC3d c labBall_STR (negOpen_STR labCusp_STR labVert_STR)
        ⟨hA', hV'⟩ hB (mfderiv_phiBall_ne_STR c) ?_ ?_
      · intro c' hU
        rw [mem_cbase_L_STR]
        constructor
        · rintro ⟨-, -, x⟩
          exact x
        · intro hx
          exact ⟨hU.1.le, hU.2.le, hx⟩
      · intro g hg
        rcases lab_cases_STR g with rfl | rfl | rfl
        · exact absurd rfl hg
        · exact hA'
        · exact hV'

/-- **An actual corner of the solid-torus circle base with two forced labels**: at the rim base
point `q±` of an endpoint `e`, the V32 corner data with `L = {labVert_STR, labBall_STR}`,
`L.card = 2`, independent differentials and completeness (the cusp face is not active). -/
theorem corner_V32_nonempty_STR_BC3d :
    ∃ (e : rows_STR.edge.EdgeEnd) (U : TopologicalSpace.Opens rows_STR.circle.Base),
      rimBase_STR e.1 ∈ U ∧
      ∃ (L : Finset Lab_STR) (φ : Lab_STR → rows_STR.circle.Base → ℝ),
        L.card = 2 ∧
        (∀ f ∈ L, ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ (φ f) U ∧ φ f (rimBase_STR e.1) = 0 ∧
          {c' | c' ∈ U ∧ c' ∈ rows_STR.circle.cbase ∧ φ f c' = 0} =
            {c' | c' ∈ U ∧ c' ∈ rows_STR.circle.cbase ∧
              rows_STR.circle.fibre c' ⊆ circleFaceSet rows_STR.slimPieces rows_STR.edge f}) ∧
        (Surjective fun w : TangentSpace (𝓡 2) (rimBase_STR e.1) =>
          fun f : L => mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (φ f) (rimBase_STR e.1) w) ∧
        rows_STR.circle.cbase ∩ (U : Set rows_STR.circle.Base) =
          {c' | c' ∈ U ∧ ∀ f ∈ L, φ f c' ≤ 0} ∧
        (∀ g : Lab_STR, rows_STR.circle.fibre (rimBase_STR e.1) ⊆
          circleFaceSet rows_STR.slimPieces rows_STR.edge g → g ∈ L) := by
  obtain ⟨e, -⟩ := corner_incidences_STR
  obtain ⟨hB, hV, hA, -⟩ := corner_labels_STR e
  obtain ⟨U, hcU, L, φ, hL, -, -, rest⟩ := localFaces_corner_V32_BC3d (rimBase_STR e.1) hV hB hA
  refine ⟨e, U, hcU, L, φ, ?_, rest⟩
  rw [hL]
  exact Finset.card_pair labVert_ne_labBall_STR

end GC.GraphManifold.Assembly.FC39P0.SolidTorusSTR
