import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.SolidTorusLocalFacesSTR

/-!
# S-SOLIDTORUS4 (suffix `_STR`), G7 part 6: `local_faces` of the circle base

`localFaces_single_STR` (one active face), `localFaces_corner_STR` (the two corner faces
`{labVert_STR, labBall_STR}`, independent differentials because `Im q ≠ 0`), the frontier
dichotomy `frontier_active_STR`, and `local_faces_STR` by the four cases.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace GC.GraphManifold.Assembly.FC39P0.SolidTorusSTR

open GC.GraphManifold.Assembly.FC39P0.SolidTorusSTI GC.GraphManifold.Assembly.FC39P0

local instance carrierCharts_LocalCasesSTR : ChartedSpace (EuclideanHalfSpace 3) Wc.Carrier := by
  change ChartedSpace (EuclideanHalfSpace 3) solidTorusSet.{0}
  exact inferInstance

local instance carrierSmooth_LocalCasesSTR : IsManifold (𝓡∂ 3) ∞ Wc.Carrier := by
  change IsManifold (𝓡∂ 3) ∞ solidTorusSet.{0}
  exact inferInstance

local instance decEqLab_STR : DecidableEq Lab_STR := Classical.decEq _

theorem continuous_phiL_STR (f : Lab_STR) : Continuous (phiL_STR f) :=
  (contMDiff_phiL_STR f).continuous

/-- The open set where two face functions are negative. -/
def negOpen_STR (f g : Lab_STR) : TopologicalSpace.Opens rows_STR.circle.Base :=
  ⟨{c' | phiL_STR f c' < 0 ∧ phiL_STR g c' < 0},
    (isOpen_lt (continuous_phiL_STR f) continuous_const).inter
      (isOpen_lt (continuous_phiL_STR g) continuous_const)⟩

theorem mem_cbase_L_STR {c : rows_STR.circle.Base} :
    c ∈ rows_STR.circle.cbase ↔
      phiL_STR labCusp_STR c ≤ 0 ∧ phiL_STR labVert_STR c ≤ 0 ∧ phiL_STR labBall_STR c ≤ 0 :=
  mem_cbase_STR

theorem frontier_active_STR (c : rows_STR.circle.Base) (hc : c ∈ frontier rows_STR.circle.cbase) :
    c ∈ rows_STR.circle.cbase ∧ (phiL_STR labCusp_STR c = 0 ∨ phiL_STR labVert_STR c = 0 ∨
      phiL_STR labBall_STR c = 0) := by
  have hm : c ∈ rows_STR.circle.cbase := rows_STR.circle.cbase_compact.isClosed.frontier_subset hc
  refine ⟨hm, ?_⟩
  by_contra hcon
  simp only [not_or] at hcon
  obtain ⟨h1, h2, h3⟩ := mem_cbase_L_STR.1 hm
  have hs1 := lt_of_le_of_ne h1 hcon.1
  have hs2 := lt_of_le_of_ne h2 hcon.2.1
  have hs3 := lt_of_le_of_ne h3 hcon.2.2
  have ho : IsOpen {c' : rows_STR.circle.Base | phiL_STR labCusp_STR c' < 0 ∧
      phiL_STR labVert_STR c' < 0 ∧ phiL_STR labBall_STR c' < 0} :=
    (isOpen_lt (continuous_phiL_STR _) continuous_const).inter
      ((isOpen_lt (continuous_phiL_STR _) continuous_const).inter
        (isOpen_lt (continuous_phiL_STR _) continuous_const))
  have hsub : {c' : rows_STR.circle.Base | phiL_STR labCusp_STR c' < 0 ∧
      phiL_STR labVert_STR c' < 0 ∧ phiL_STR labBall_STR c' < 0} ⊆ rows_STR.circle.cbase := by
    intro c' hc'
    exact mem_cbase_L_STR.2 ⟨hc'.1.le, hc'.2.1.le, hc'.2.2.le⟩
  exact hc.2 (interior_maximal hsub ho ⟨hs1, hs2, hs3⟩)

/-! ## One active face -/

theorem localFaces_single_STR (c : rows_STR.circle.Base) (f : Lab_STR)
    (U : TopologicalSpace.Opens rows_STR.circle.Base) (hcU : c ∈ U) (hz : phiL_STR f c = 0)
    (hreg : mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (phiL_STR f) c ≠ 0)
    (hcb : ∀ c' ∈ U, (c' ∈ rows_STR.circle.cbase ↔ phiL_STR f c' ≤ 0)) :
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
  refine ⟨U, hcU, {f}, phiL_STR, by simp, by simp, ?_, ?_, ?_⟩
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

/-! ## The corner -/

theorem labVert_ne_labBall_STR : labVert_STR ≠ labBall_STR := fun h => by
  cases h

theorem localFaces_corner_STR (c : rows_STR.circle.Base) (hV : phiVert_STR c = 0)
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
          {c' | c' ∈ U ∧ ∀ f ∈ L, φ f c' ≤ 0} := by
  let U : TopologicalSpace.Opens rows_STR.circle.Base :=
    ⟨{c' | phiL_STR labCusp_STR c' < 0},
      isOpen_lt (continuous_phiL_STR _) continuous_const⟩
  have hcard : ({labVert_STR, labBall_STR} : Finset Lab_STR).card = 2 :=
    Finset.card_pair labVert_ne_labBall_STR
  have hn := norm_q_sq_STR c
  have hr := re_q_STR c
  have hv0 : vOf_STR c 0 = 4 / 5 := by
    have h : reL_STR (vOf_STR c) = 4 / 5 := by
      simp only [phiBall_STR, gBall_STR] at hB
      linarith
    rwa [reL_apply_STR] at h
  have hnv : ‖vOf_STR c‖ ^ 2 = vOf_STR c 0 * vOf_STR c 0 + vOf_STR c 1 * vOf_STR c 1 := by
    rw [← real_inner_self_eq_norm_sq, inner_two_STR]
  have hv1 : vOf_STR c 1 ≠ 0 := by
    intro h0
    simp only [phiVert_STR, gVert_STR] at hV
    rw [hnv, hv0, h0] at hV
    norm_num at hV
  refine ⟨U, hA, {labVert_STR, labBall_STR}, phiL_STR, rfl, by omega, by omega, ?_, ?_, ?_⟩
  · intro g hg
    refine ⟨(contMDiff_phiL_STR g).contMDiffOn, ?_, ?_⟩
    · rcases Finset.mem_insert.mp hg with rfl | hg
      · exact hV
      · rw [Finset.mem_singleton.mp hg]
        exact hB
    · ext c'
      constructor
      · rintro ⟨hU, hcb', h0⟩
        exact ⟨hU, hcb', (fibre_iff_STR hcb').2 h0⟩
      · rintro ⟨hU, hcb', hs⟩
        exact ⟨hU, hcb', (fibre_iff_STR hcb').1 hs⟩
  · intro v
    let kV : ({labVert_STR, labBall_STR} : Finset Lab_STR) :=
      ⟨labVert_STR, Finset.mem_insert_self _ _⟩
    let kB : ({labVert_STR, labBall_STR} : Finset Lab_STR) :=
      ⟨labBall_STR, Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩
    obtain ⟨a, ha⟩ : ∃ a : ℝ, a = v kV := ⟨_, rfl⟩
    obtain ⟨b, hb⟩ : ∃ b : ℝ, b = v kB := ⟨_, rfl⟩
    let w : EuclideanSpace ℝ (Fin 2) :=
      b • EuclideanSpace.single (0 : Fin 2) (1 : ℝ) +
        ((a / 2 - vOf_STR c 0 * b) / vOf_STR c 1) • EuclideanSpace.single (1 : Fin 2) (1 : ℝ)
    have hw0 : w 0 = b := by simp [w]
    have hw1 : w 1 = (a / 2 - vOf_STR c 0 * b) / vOf_STR c 1 := by simp [w]
    have hdV : mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (phiL_STR labVert_STR) c w =
        2 * (vOf_STR c 0 * w 0 + vOf_STR c 1 * w 1) :=
      (DFunLike.congr_fun (mfderiv_phiVert_STR c) w).trans (eval2_STR _ _)
    have hdB : mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (phiL_STR labBall_STR) c w = w 0 :=
      (DFunLike.congr_fun (mfderiv_phiBall_STR c) w).trans (reL_apply_STR w)
    refine ⟨w, funext fun k => ?_⟩
    rcases Finset.mem_insert.mp k.2 with hk | hk
    · have hkk : k = kV := Subtype.ext hk
      rw [hkk]
      have e : 2 * (vOf_STR c 0 * w 0 + vOf_STR c 1 * w 1) = a := by
        rw [hw0, hw1]
        field_simp
        ring
      exact (hdV.trans e).trans ha
    · have hkk : k = kB := Subtype.ext (Finset.mem_singleton.mp hk)
      rw [hkk]
      exact (hdB.trans hw0).trans hb
  · ext c'
    constructor
    · rintro ⟨hc', hU⟩
      refine ⟨hU, fun g hg => ?_⟩
      obtain ⟨-, h2, h3⟩ := mem_cbase_L_STR.1 hc'
      rcases Finset.mem_insert.mp hg with rfl | hg
      · exact h2
      · rw [Finset.mem_singleton.mp hg]
        exact h3
    · rintro ⟨hU, hle⟩
      refine ⟨mem_cbase_L_STR.2 ⟨le_of_lt hU, hle _ (Finset.mem_insert_self _ _),
        hle _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))⟩, hU⟩

end GC.GraphManifold.Assembly.FC39P0.SolidTorusSTR
