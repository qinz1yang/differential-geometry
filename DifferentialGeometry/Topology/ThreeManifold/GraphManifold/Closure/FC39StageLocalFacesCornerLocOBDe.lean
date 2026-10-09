import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageLocalFacesCornerJN74
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageFaceModelOBDe

/-!
# Local-constancy `local_faces` at a corner (cusp-aware)

Lane O-BD1 (by S-BD2e), G11d (suffix `_OBDe`). The same statement as the G11c copy with the fibre
constancy of the face function required only on `residualNear Fl ∩ Ω` for an open set `Ω` around
the face (the face function of a zero domain is a function of `E` only near the face).
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly.FC39P0

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n}

namespace StageCutRows74

variable {A : SmoothStageGeometry74 W E} {D : StageCutChoice74 A} (R : StageCutRows74 A D)

/-- **`local_faces` at a corner point `c = rimBase e` (rim over an endpoint `e`).** The primitives
`(b, U, hCU, hNeq)` are the EDP05 descended face equation at `e` (`h_F = b ∘ q₁` near the rim,
`C₂ ∩ U = {b ≥ 0}`, `db(e) ≠ 0`). -/
theorem localFaces_corner_loc_OBDe (F : JunctionFaceFacts74 A D R)
    (cov : CutCoverFacts74 A D)
    (hKR : ∀ F : NeighbourFace A.zero A.cusp, neighbourSet F ∩ D.slimSet ⊆
      relInt (regionM1 A.zero A.cusp) D.slimSet)
    (rimBase : R.edge.Base → R.circle.Base)
    (hrim : ∀ c ∈ R.edge.cbase, R.edge.rim c = R.circle.fibre (rimBase c))
    (hreg : D.edgeSet ∩ D.M₃ = R.edge.vertical) (hsub : D.edgeSet ⊆ D.M₂)
    (hconstT : ∀ x y : R.circle.domain, (x : W.Carrier) ∈ R.edge.source →
      (y : W.Carrier) ∈ R.edge.source → R.circle.proj y = R.circle.proj x →
      R.cornerT x = R.cornerT y)
    (e : R.edge.EdgeEnd) (Ω : Set W.Carrier) (hΩ : IsOpen Ω)
    (hΩF : R.slimPieces.residualSet (F.horizontal e) ⊆ Ω)
    (hconstH : ∀ x y : R.circle.domain,
      (x : W.Carrier) ∈ (R.slimPieces.residualNear (F.horizontal e) : Set W.Carrier) ∩ Ω →
      (y : W.Carrier) ∈ (R.slimPieces.residualNear (F.horizontal e) : Set W.Carrier) ∩ Ω →
      R.circle.proj y = R.circle.proj x →
      R.slimPieces.residualFn (F.horizontal e) x = R.slimPieces.residualFn (F.horizontal e) y)
    (b : R.edge.Base → ℝ) (U : TopologicalSpace.Opens R.edge.Base) (heU : e.1 ∈ U)
    (hb : ContMDiffOn (𝓡 1) 𝓘(ℝ, ℝ) ∞ b U) (hbreg : mfderiv (𝓡 1) 𝓘(ℝ, ℝ) b e.1 ≠ 0)
    (hCU : R.edge.cbase ∩ U = {c | c ∈ U ∧ 0 ≤ b c})
    (hNeq : ∃ N' : Set W.Carrier, IsOpen N' ∧ R.edge.rim e.1 ⊆ N' ∧ ∀ x ∈ N',
      ∃ hx : x ∈ R.edge.source,
        R.slimPieces.residualFn (F.horizontal e) x = b (R.edge.proj ⟨x, hx⟩)) :
    ∃ U' : TopologicalSpace.Opens R.circle.Base, rimBase e.1 ∈ U' ∧
      ∃ (L : Finset (CircleFaceLabel R.slimPieces.ResidualFace R.edge.EdgeBaseComponent))
        (φ : CircleFaceLabel R.slimPieces.ResidualFace R.edge.EdgeBaseComponent →
          R.circle.Base → ℝ),
        1 ≤ L.card ∧ L.card ≤ 2 ∧
        (∀ f ∈ L, ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ (φ f) U' ∧ φ f (rimBase e.1) = 0 ∧
          {c'' | c'' ∈ U' ∧ c'' ∈ R.circle.cbase ∧ φ f c'' = 0} =
            {c'' | c'' ∈ U' ∧ c'' ∈ R.circle.cbase ∧
              R.circle.fibre c'' ⊆ circleFaceSet R.slimPieces R.edge f}) ∧
        (Surjective fun w : TangentSpace (𝓡 2) (rimBase e.1) =>
          fun f : L => mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (φ f) (rimBase e.1) w) ∧
        R.circle.cbase ∩ U' = {c'' | c'' ∈ U' ∧ ∀ f ∈ L, φ f c'' ≤ 0} := by
  classical
  have hcl : IsClosedMap R.circle.proj := isClosedMap_circleBundle74 R.circleFacts
  have hrelint := R.relInt_edgeSet_eq_JN74 hreg hsub
  have hedge : R.edge.edgePiece = D.edgeSet := D.edgePiece_edgeBundle74 R.edgeFacts
  have hec : e.1 ∈ R.edge.cbase := R.edge.frontier_cbase_subset e.2
  have hfibrim : R.circle.fibre (rimBase e.1) = R.edge.rim e.1 := (hrim _ hec).symm
  obtain ⟨N', hN'o, hrimN', hN'eq⟩ := hNeq
  have hrimsrc : ∀ x ∈ R.edge.rim e.1, ∃ hxS : x ∈ R.edge.source,
      R.edge.proj ⟨x, hxS⟩ = e.1 ∧ R.edge.height ⟨x, hxS⟩ = R.edge.level := by
    rintro x ⟨z, ⟨hz1, hz2⟩, hzx⟩
    have hxS : x ∈ R.edge.source := by
      rw [← hzx]
      exact z.2
    have hz : z = ⟨x, hxS⟩ := Subtype.ext hzx
    subst hz
    exact ⟨hxS, hz1, hz2⟩
  have hrimF : ∀ x ∈ R.edge.rim e.1, x ∈ R.slimPieces.residualSet (F.horizontal e) := by
    rintro x ⟨z, ⟨hz1, hz2⟩, hzx⟩
    exact F.horizontal_disk e ⟨z, ⟨hz1, hz2.le⟩, hzx⟩
  -- the value of `b` at the endpoint
  have hb0 : b e.1 = 0 := by
    obtain ⟨_, x, hx, rfl⟩ := R.fibre_nonempty_JN74 (rimBase e.1)
    have hxr : (x : W.Carrier) ∈ R.edge.rim e.1 := by
      rw [← hfibrim]
      exact ⟨x, hx, rfl⟩
    obtain ⟨hxS, hxe, -⟩ := hrimsrc _ hxr
    obtain ⟨hxS', hxeq⟩ := hN'eq _ (hrimN' hxr)
    have h0 := R.slimPieces.residualFn_eq_zero_JN74 (F.horizontal e) (hrimF _ hxr)
    rw [hxeq] at h0
    exact hxe ▸ h0
  obtain ⟨U', heU', hU'U, hU'comp⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_nhds_component_iff_JN74 heU hb hb0 hbreg hCU
  -- the face model along the rim fibre
  have hmodel0 : ∀ x ∈ R.slimPieces.residualSet (F.horizontal e), ∃ O : Set W.Carrier,
      IsOpen O ∧ x ∈ O ∧ O ⊆ (R.slimPieces.residualNear (F.horizontal e) : Set W.Carrier) ∧
      (∀ y ∈ O, y ∈ D.M₂ ↔ 0 ≤ R.slimPieces.residualFn (F.horizontal e) y) ∧
      ∀ y ∈ O, R.slimPieces.residualFn (F.horizontal e) y = 0 →
        y ∈ R.slimPieces.residualSet (F.horizontal e) :=
    fun x hx => exists_faceModel_OBDe R cov F hKR (F.horizontal e) hx
  have hmodel : ∀ x ∈ R.slimPieces.residualSet (F.horizontal e), ∃ O : Set W.Carrier,
      IsOpen O ∧ x ∈ O ∧
      O ⊆ (R.slimPieces.residualNear (F.horizontal e) : Set W.Carrier) ∩ Ω ∧
      (∀ y ∈ O, y ∈ D.M₂ ↔ 0 ≤ R.slimPieces.residualFn (F.horizontal e) y) ∧
      ∀ y ∈ O, R.slimPieces.residualFn (F.horizontal e) y = 0 →
        y ∈ R.slimPieces.residualSet (F.horizontal e) := by
    intro x hx
    obtain ⟨O, ho, hxo, hOn, hM, hz⟩ := hmodel0 x hx
    exact ⟨O ∩ Ω, ho.inter hΩ, ⟨hxo, hΩF hx⟩, fun y hy => ⟨hOn hy.1, hy.2⟩,
      fun y hy => hM y hy.1, fun y hy h0 => hz y hy.1 h0⟩
  let P : Set W.Carrier :=
    {z | z ∈ (R.slimPieces.residualNear (F.horizontal e) : Set W.Carrier) ∩ Ω ∧
    (z ∈ D.M₂ ↔ 0 ≤ R.slimPieces.residualFn (F.horizontal e) z) ∧
    (R.slimPieces.residualFn (F.horizontal e) z = 0 →
      z ∈ R.slimPieces.residualSet (F.horizontal e))}
  have hfibP : R.circle.fibre (rimBase e.1) ⊆ interior P := fun x hx => by
    have hxr : x ∈ R.edge.rim e.1 := by rw [← hfibrim]; exact hx
    obtain ⟨O, ho, hxo, hOn, hM, hz⟩ := hmodel x (hrimF x hxr)
    exact mem_interior.2 ⟨O, fun y hy => ⟨hOn hy, hM y hy, hz y hy⟩, ho, hxo⟩
  have hΩs : IsOpen (Subtype.val '' (R.edge.proj ⁻¹' (U' : Set R.edge.Base) :
      Set R.edge.source) : Set W.Carrier) :=
    R.edge.source.isOpen.isOpenMap_subtype_val _ (U'.isOpen.preimage R.edge.proj.continuous)
  let Ω : Set W.Carrier := interior P ∩ N' ∩
    Subtype.val '' (R.edge.proj ⁻¹' (U' : Set R.edge.Base) : Set R.edge.source)
  have hfib : R.circle.proj ⁻¹' {rimBase e.1} ⊆ (Subtype.val ⁻¹' Ω : Set R.circle.domain) := by
    intro x hx
    have hxf : (x : W.Carrier) ∈ R.circle.fibre (rimBase e.1) := ⟨x, hx, rfl⟩
    have hxr : (x : W.Carrier) ∈ R.edge.rim e.1 := by rw [← hfibrim]; exact hxf
    obtain ⟨hxS, hxe, -⟩ := hrimsrc _ hxr
    refine ⟨⟨hfibP hxf, hrimN' hxr⟩, ⟨(x : W.Carrier), hxS⟩, ?_, rfl⟩
    change R.edge.proj ⟨(x : W.Carrier), hxS⟩ ∈ U'
    rw [hxe]
    exact heU'
  obtain ⟨V, hVo, hcV, -, hVsub⟩ := Geometry.Collapse.EdgeDisk.exists_open_tube_subset_EFC hcl
    (N := (Subtype.val ⁻¹' Ω : Set R.circle.domain))
    (((isOpen_interior.inter hN'o).inter hΩs).preimage continuous_subtype_val) hfib
    (V := Set.univ) isOpen_univ trivial
  let Vo : TopologicalSpace.Opens R.circle.Base := ⟨V, hVo⟩
  have hO : ∀ x : R.circle.domain, R.circle.proj x ∈ V →
      (x : W.Carrier) ∈ P ∧ ∃ hxS : (x : W.Carrier) ∈ R.edge.source,
        R.edge.proj ⟨x, hxS⟩ ∈ U' ∧
          R.slimPieces.residualFn (F.horizontal e) x = b (R.edge.proj ⟨x, hxS⟩) := by
    intro x hx
    obtain ⟨⟨hPi, hN'x⟩, z, hzU, hzx⟩ := hVsub hx
    have hxS : (x : W.Carrier) ∈ R.edge.source := by
      rw [← hzx]
      exact z.2
    have hz : z = ⟨(x : W.Carrier), hxS⟩ := Subtype.ext hzx
    obtain ⟨hxS', hxeq⟩ := hN'eq _ hN'x
    refine ⟨interior_subset hPi, hxS, ?_, hxeq⟩
    rw [← hz]
    exact hzU
  have hsrc : ∀ x : R.circle.domain, R.circle.proj x ∈ Vo → (x : W.Carrier) ∈ R.edge.source :=
    fun x hx => (hO x hx).2.1
  have hconstT' : ∀ x y : R.circle.domain, R.circle.proj x ∈ Vo →
      R.circle.proj y = R.circle.proj x → R.cornerT x = R.cornerT y := fun x y hx hxy =>
    hconstT x y (hsrc x hx) (hsrc y (by rw [hxy]; exact hx)) hxy
  obtain ⟨Tb, hTbsm, hTbdesc⟩ := cornerT_descends_JN74 R Vo hsrc hconstT'
  have hf : ContMDiffOn W.model 𝓘(ℝ, ℝ) ∞ (R.slimPieces.residualFn (F.horizontal e))
      (R.circle.tube (Vo : Set R.circle.Base)) := by
    refine (R.slimPieces.residualFn_contMDiffOn_JN74 (F.horizontal e)).mono ?_
    rintro _ ⟨x, hx, rfl⟩
    exact (hO x hx).1.1.1
  have hconstH' : ∀ x y : R.circle.domain, R.circle.proj x ∈ Vo →
      R.circle.proj y = R.circle.proj x →
      R.slimPieces.residualFn (F.horizontal e) x.1 =
        R.slimPieces.residualFn (F.horizontal e) y.1 := fun x y hx hxy =>
    hconstH x y (hO x hx).1.1 (hO y (by rw [hxy]; exact hx)).1.1 hxy
  obtain ⟨hbb, hbbsm, hbbdesc⟩ := exists_descended_of_fibreConst_JN74 R.circle Vo
    (R.slimPieces.residualFn (F.horizontal e)) hf hconstH'
  -- the sign model of `M₃` on the tube
  have hsign : ∀ x : R.circle.domain, R.circle.proj x ∈ V →
      ((x : W.Carrier) ∈ D.M₃ ↔ 0 ≤ R.cornerT x ∧
        0 ≤ R.slimPieces.residualFn (F.horizontal e) x) := by
    intro x hx
    obtain ⟨hPx, hxS, hπU', hxeq⟩ := hO x hx
    have hT : R.cornerT x = R.edge.height ⟨x, hxS⟩ - R.edge.level := by
      simp only [StageCutRows74.cornerT, hxS, ↓reduceDIte]
    have hπC : R.edge.proj ⟨x, hxS⟩ ∈ R.edge.cbase ↔
        0 ≤ R.slimPieces.residualFn (F.horizontal e) x := by
      rw [hxeq]
      have h := Set.ext_iff.1 hCU (R.edge.proj ⟨x, hxS⟩)
      constructor
      · intro hc
        exact (h.1 ⟨hc, hU'U hπU'⟩).2
      · intro h0
        exact (h.2 ⟨hU'U hπU', h0⟩).1
    have hE : (x : W.Carrier) ∈ D.edgeSet ↔ R.edge.proj ⟨x, hxS⟩ ∈ R.edge.cbase ∧
        R.edge.height ⟨x, hxS⟩ ≤ R.edge.level := by
      rw [← hedge]
      constructor
      · rintro ⟨z, hz, hzx⟩
        have : z = ⟨(x : W.Carrier), hxS⟩ := Subtype.ext hzx
        rw [← this]
        exact hz
      · intro h
        exact ⟨⟨x, hxS⟩, h, rfl⟩
    have hVt : (x : W.Carrier) ∈ R.edge.vertical ↔ R.edge.proj ⟨x, hxS⟩ ∈ R.edge.cbase ∧
        R.edge.height ⟨x, hxS⟩ = R.edge.level := by
      constructor
      · rintro ⟨z, hz, hzx⟩
        have : z = ⟨(x : W.Carrier), hxS⟩ := Subtype.ext hzx
        rw [← this]
        exact hz
      · intro h
        exact ⟨⟨x, hxS⟩, h, rfl⟩
    change (x : W.Carrier) ∈ D.M₂ \ relInt D.M₂ D.edgeSet ↔ _
    rw [hrelint, Set.mem_sdiff, Set.mem_sdiff, hPx.2.1, hE, hVt, hπC, hT, sub_nonneg]
    constructor
    · rintro ⟨ha, hn⟩
      refine ⟨?_, ha⟩
      by_contra hlt
      have hlt' : R.edge.height ⟨x, hxS⟩ < R.edge.level := lt_of_not_ge hlt
      exact hn ⟨⟨ha, hlt'.le⟩, fun hv => hlt'.ne hv.2⟩
    · rintro ⟨ht, ha⟩
      exact ⟨ha, fun ⟨⟨_, hle⟩, hnv⟩ => hnv ⟨ha, le_antisymm hle ht⟩⟩
  have hcb : ∀ b' : R.circle.Base, b' ∈ V →
      (b' ∈ R.circle.cbase ↔ 0 ≤ Tb b' ∧ 0 ≤ hbb b') := by
    intro b' hbV
    rw [StageCutRows74.mem_cbase_iff_fibre_subset_JN74 (R := R)]
    constructor
    · intro hsubM
      obtain ⟨_, x, hx, rfl⟩ := R.fibre_nonempty_JN74 b'
      have hxb : R.circle.proj x = b' := hx
      have hxV : R.circle.proj x ∈ V := by rw [hxb]; exact hbV
      have h1 := (hsign x hxV).1 (hsubM ⟨x, hx, rfl⟩)
      rw [hTbdesc x hxV, hbbdesc x hxV, hxb] at h1
      exact h1
    · rintro ⟨h0, h0'⟩ _ hy
      obtain ⟨x, hx, rfl⟩ := hy
      have hxb : R.circle.proj x = b' := hx
      have hxV : R.circle.proj x ∈ V := by rw [hxb]; exact hbV
      exact (hsign x hxV).2 (by rw [hTbdesc x hxV, hbbdesc x hxV, hxb]; exact ⟨h0, h0'⟩)
  -- the centre
  obtain ⟨p, hpc⟩ : ∃ p : R.circle.domain, R.circle.proj p = rimBase e.1 := by
    obtain ⟨_, p, hp, rfl⟩ := R.fibre_nonempty_JN74 (rimBase e.1)
    exact ⟨p, hp⟩
  have hpV : R.circle.proj p ∈ V := by rw [hpc]; exact hcV
  have hpr : (p : W.Carrier) ∈ R.edge.rim e.1 := by
    rw [← hfibrim]
    exact ⟨p, hpc, rfl⟩
  obtain ⟨hpS, hpe, hph⟩ := hrimsrc _ hpr
  have hTc : Tb (rimBase e.1) = 0 := by
    have hT : R.cornerT p = 0 := by
      simp only [StageCutRows74.cornerT, hpS, ↓reduceDIte, hph, sub_self]
    rw [← hpc, ← hTbdesc p hpV, hT]
  have hhc : hbb (rimBase e.1) = 0 := by
    rw [← hpc, ← hbbdesc p hpV]
    exact R.slimPieces.residualFn_eq_zero_JN74 (F.horizontal e) (hrimF _ hpr)
  -- the rank at the centre
  have hrank : Surjective fun w : TangentSpace (𝓡 2) (R.circle.proj p) =>
      (mfderiv (𝓡 2) 𝓘(ℝ, ℝ) Tb (R.circle.proj p) w,
        mfderiv (𝓡 2) 𝓘(ℝ, ℝ) hbb (R.circle.proj p) w) := by
    have hrk := cornerRank_surjective_rb_JN74 (R := R) e (F.horizontal e) p hpS hpe hph b U heU hb
      hbreg (Subtype.val ⁻¹' N' : Set R.circle.domain) (hN'o.preimage continuous_subtype_val)
      (hrimN' hpr) (fun x hx => hN'eq _ hx)
    have hTd : MDifferentiableAt (𝓡 2) 𝓘(ℝ, ℝ) Tb (R.circle.proj p) :=
      (hTbsm.contMDiffAt (hVo.mem_nhds hpV)).mdifferentiableAt (by simp)
    have hhd : MDifferentiableAt (𝓡 2) 𝓘(ℝ, ℝ) hbb (R.circle.proj p) :=
      (hbbsm.contMDiffAt (hVo.mem_nhds hpV)).mdifferentiableAt (by simp)
    have hproj : MDifferentiableAt W.model (𝓡 2) R.circle.proj p :=
      (R.circle.proj_smooth p).mdifferentiableAt (by simp)
    have hev : (fun z : R.circle.domain => (R.cornerT z,
        R.slimPieces.residualFn (F.horizontal e) z)) =ᶠ[𝓝 p]
        (fun b' => (Tb b', hbb b')) ∘ R.circle.proj := by
      filter_upwards [R.circle.proj.continuous.continuousAt.preimage_mem_nhds
        (hVo.mem_nhds hpV)] with z hz
      exact Prod.ext (hTbdesc z hz) (hbbdesc z hz)
    have hQd : MDifferentiableAt (𝓡 2) 𝓘(ℝ, ℝ × ℝ) (fun b' => (Tb b', hbb b'))
        (R.circle.proj p) :=
      ((hTbsm.prodMk_space hbbsm).contMDiffAt (hVo.mem_nhds hpV)).mdifferentiableAt (by simp)
    rw [hev.mfderiv_eq, mfderiv_comp p hQd hproj] at hrk
    intro t
    obtain ⟨v, hv⟩ := hrk t
    refine ⟨mfderiv W.model (𝓡 2) R.circle.proj p v, ?_⟩
    have hv' : mfderiv (𝓡 2) 𝓘(ℝ, ℝ × ℝ) (fun b' => (Tb b', hbb b')) (R.circle.proj p)
        (mfderiv W.model (𝓡 2) R.circle.proj p v) = t := hv
    rw [← hv']
    exact (mfderiv_pair_apply_JN74 hTd hhd _).symm
  have hrankc : Surjective fun w : TangentSpace (𝓡 2) (rimBase e.1) =>
      (mfderiv (𝓡 2) 𝓘(ℝ, ℝ) Tb (rimBase e.1) w, mfderiv (𝓡 2) 𝓘(ℝ, ℝ) hbb (rimBase e.1) w) := by
    rwa [hpc] at hrank
  let K : R.edge.EdgeBaseComponent := e.component
  have hface₁ : {c'' | c'' ∈ Vo ∧ c'' ∈ R.circle.cbase ∧ (fun b' => -hbb b') c'' = 0} =
      {c'' | c'' ∈ Vo ∧ c'' ∈ R.circle.cbase ∧
        R.circle.fibre c'' ⊆ circleFaceSet R.slimPieces R.edge (.horizontal (F.horizontal e))} := by
    ext b'
    simp only [mem_ofPred_eq, neg_eq_zero]
    refine and_congr_right fun hbV => and_congr_right fun _ => ?_
    constructor
    · intro hb0'
      rintro _ ⟨x, hx, rfl⟩
      have hxb : R.circle.proj x = b' := hx
      have hxV : R.circle.proj x ∈ V := by rw [hxb]; exact hbV
      have h0 : R.slimPieces.residualFn (F.horizontal e) x = 0 := by
        rw [hbbdesc x hxV, hxb]
        exact hb0'
      exact (hO x hxV).1.2.2 h0
    · intro hsubF
      obtain ⟨_, x, hx, rfl⟩ := R.fibre_nonempty_JN74 b'
      have hxb : R.circle.proj x = b' := hx
      have hxV : R.circle.proj x ∈ V := by rw [hxb]; exact hbV
      have h0 := R.slimPieces.residualFn_eq_zero_JN74 (F.horizontal e) (hsubF ⟨x, hx, rfl⟩)
      rw [← hxb, ← hbbdesc x hxV]
      exact h0
  have hface₂ : {c'' | c'' ∈ Vo ∧ c'' ∈ R.circle.cbase ∧ (fun b' => -Tb b') c'' = 0} =
      {c'' | c'' ∈ Vo ∧ c'' ∈ R.circle.cbase ∧
        R.circle.fibre c'' ⊆ circleFaceSet R.slimPieces R.edge (.vertical K)} := by
    ext b'
    simp only [mem_ofPred_eq, neg_eq_zero]
    refine and_congr_right fun hbV => and_congr_right fun hbc => ?_
    constructor
    · intro hT0
      rintro _ ⟨x, hx, rfl⟩
      have hxb : R.circle.proj x = b' := hx
      have hxV : R.circle.proj x ∈ V := by rw [hxb]; exact hbV
      obtain ⟨-, hxS, hπU', hxeq⟩ := hO x hxV
      have hT : R.cornerT x = R.edge.height ⟨x, hxS⟩ - R.edge.level := by
        simp only [StageCutRows74.cornerT, hxS, ↓reduceDIte]
      have h0 : R.cornerT x = 0 := by
        rw [hTbdesc x hxV, hxb]
        exact hT0
      have hh : R.edge.height ⟨x, hxS⟩ = R.edge.level := by
        rw [hT] at h0
        exact sub_eq_zero.1 h0
      have hxM3 : (x : W.Carrier) ∈ D.M₃ :=
        ((StageCutRows74.mem_cbase_iff_fibre_subset_JN74 (R := R)).1 hbc) ⟨x, hx, rfl⟩
      have hh0 : 0 ≤ R.slimPieces.residualFn (F.horizontal e) x := ((hsign x hxV).1 hxM3).2
      have hbπ : 0 ≤ b (R.edge.proj ⟨x, hxS⟩) := by
        rw [← hxeq]
        exact hh0
      have hπK : R.edge.proj ⟨x, hxS⟩ ∈ K.1 := (hU'comp _ hπU').2 hbπ
      exact ⟨⟨x, hxS⟩, ⟨hπK, hh⟩, rfl⟩
    · intro hsubV
      obtain ⟨_, x, hx, rfl⟩ := R.fibre_nonempty_JN74 b'
      have hxb : R.circle.proj x = b' := hx
      have hxV : R.circle.proj x ∈ V := by rw [hxb]; exact hbV
      have hxS : (x : W.Carrier) ∈ R.edge.source := hsrc x hxV
      obtain ⟨z, ⟨-, hz2⟩, hzx⟩ := hsubV ⟨x, hx, rfl⟩
      have hz : z = ⟨(x : W.Carrier), hxS⟩ := Subtype.ext hzx
      have hh : R.edge.height ⟨x, hxS⟩ = R.edge.level := by
        rw [← hz]
        exact hz2
      have hT : R.cornerT x = 0 := by
        simp only [StageCutRows74.cornerT, hxS, ↓reduceDIte, hh, sub_self]
      rw [← hxb, ← hTbdesc x hxV, hT]
  have hsign' : R.circle.cbase ∩ Vo = {c'' | c'' ∈ Vo ∧ (fun b' => -hbb b') c'' ≤ 0 ∧
      (fun b' => -Tb b') c'' ≤ 0} := by
    ext b'
    simp only [mem_inter_iff, mem_ofPred_eq, neg_nonpos]
    constructor
    · rintro ⟨hbc, hbV⟩
      obtain ⟨h1, h2⟩ := (hcb b' hbV).1 hbc
      exact ⟨hbV, h2, h1⟩
    · rintro ⟨hbV, h2, h1⟩
      exact ⟨(hcb b' hbV).2 ⟨h1, h2⟩, hbV⟩
  refine R.localFaces_two_JN74 Vo hcV (.horizontal (F.horizontal e)) (.vertical K)
    (by intro h; cases h) (fun b' => -hbb b') (fun b' => -Tb b') hbbsm.neg hTbsm.neg
    (by simp [hhc]) (by simp [hTc]) ?_ hface₁ hface₂ hsign'
  intro t
  obtain ⟨w, hw⟩ := hrankc (-t.2, -t.1)
  refine ⟨w, ?_⟩
  have e1 : mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun b' => -hbb b') (rimBase e.1) w =
      - mfderiv (𝓡 2) 𝓘(ℝ, ℝ) hbb (rimBase e.1) w := by
    change mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (-hbb) (rimBase e.1) w = _
    rw [mfderiv_neg]
    rfl
  have e2 : mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun b' => -Tb b') (rimBase e.1) w =
      - mfderiv (𝓡 2) 𝓘(ℝ, ℝ) Tb (rimBase e.1) w := by
    change mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (-Tb) (rimBase e.1) w = _
    rw [mfderiv_neg]
    rfl
  have h1 : mfderiv (𝓡 2) 𝓘(ℝ, ℝ) Tb (rimBase e.1) w = -t.2 := congrArg Prod.fst hw
  have h2 : mfderiv (𝓡 2) 𝓘(ℝ, ℝ) hbb (rimBase e.1) w = -t.1 := congrArg Prod.snd hw
  refine Prod.ext ?_ ?_
  · change mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun b' => -hbb b') (rimBase e.1) w = t.1
    rw [e1, h2]
    exact neg_neg _
  · change mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun b' => -Tb b') (rimBase e.1) w = t.2
    rw [e2, h1]
    exact neg_neg _


end StageCutRows74

end GC.GraphManifold.Assembly.FC39P0
