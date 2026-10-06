import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageLocalFacesHorizJN74
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageFaceModelOBDe

/-!
# Cusp-aware `local_faces` at a horizontal point

Lane O-BD1 (by S-BD2e), G11c (suffix `_OBDe`). The cusp-aware copy of `localFaces_horizontal_JN74`
(the closed kit's `[IsEmpty (Fin n)]` is dropped; the face model is `exists_faceModel_OBDe` and
the removal property is stated for the neighbour faces, `hKR : neighbourSet F ∩ slimSet ⊆
relInt_{M₁} slimSet`; the cover facts `cov` give the disjointness of zero domains and cusp cores).
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

/-- **`local_faces` at a horizontal point: the fibre of `c` lies in a residual face and misses
`M^edge`.** -/
theorem localFaces_horizontal_OBDe (F : JunctionFaceFacts74 A D R)
    (cov : CutCoverFacts74 A D)
    (hKR : ∀ F : NeighbourFace A.zero A.cusp, neighbourSet F ∩ D.slimSet ⊆
      relInt (regionM1 A.zero A.cusp) D.slimSet)
    (Fl : R.slimPieces.ResidualFace)
    (hconstH : ∀ x y : R.circle.domain, (x : W.Carrier) ∈ R.slimPieces.residualNear Fl →
      (y : W.Carrier) ∈ R.slimPieces.residualNear Fl → R.circle.proj y = R.circle.proj x →
      R.slimPieces.residualFn Fl x = R.slimPieces.residualFn Fl y)
    {c : R.circle.Base} {x₀ : W.Carrier} (hx₀ : x₀ ∈ R.circle.fibre c)
    (hx₀F : x₀ ∈ R.slimPieces.residualSet Fl) (hnoE : ∀ x ∈ R.circle.fibre c, x ∉ D.edgeSet) :
    ∃ U : TopologicalSpace.Opens R.circle.Base, c ∈ U ∧
      ∃ (L : Finset (CircleFaceLabel R.slimPieces.ResidualFace R.edge.EdgeBaseComponent))
        (φ : CircleFaceLabel R.slimPieces.ResidualFace R.edge.EdgeBaseComponent →
          R.circle.Base → ℝ),
        1 ≤ L.card ∧ L.card ≤ 2 ∧
        (∀ f ∈ L, ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ (φ f) U ∧ φ f c = 0 ∧
          {c'' | c'' ∈ U ∧ c'' ∈ R.circle.cbase ∧ φ f c'' = 0} =
            {c'' | c'' ∈ U ∧ c'' ∈ R.circle.cbase ∧
              R.circle.fibre c'' ⊆ circleFaceSet R.slimPieces R.edge f}) ∧
        (Surjective fun w : TangentSpace (𝓡 2) c =>
          fun f : L => mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (φ f) c w) ∧
        R.circle.cbase ∩ U = {c'' | c'' ∈ U ∧ ∀ f ∈ L, φ f c'' ≤ 0} := by
  classical
  have hcl : IsClosedMap R.circle.proj := isClosedMap_circleBundle74 R.circleFacts
  have hmodel : ∀ x ∈ R.slimPieces.residualSet Fl, ∃ O : Set W.Carrier, IsOpen O ∧ x ∈ O ∧
      O ⊆ (R.slimPieces.residualNear Fl : Set W.Carrier) ∧
      (∀ y ∈ O, y ∈ D.M₂ ↔ 0 ≤ R.slimPieces.residualFn Fl y) ∧
      ∀ y ∈ O, R.slimPieces.residualFn Fl y = 0 → y ∈ R.slimPieces.residualSet Fl :=
    fun x hx => exists_faceModel_OBDe R cov F hKR Fl hx
  have hfibF : R.circle.fibre c ⊆ R.slimPieces.residualSet Fl :=
    R.fibre_subset_residualSet_JN74 Fl hconstH
      (fun x hx => by
        obtain ⟨O, ho, hxo, hOn, -, hz⟩ := hmodel x hx
        exact ⟨O, ho, hxo, hOn, hz⟩) hx₀ hx₀F
  let P : Set W.Carrier := {z | z ∈ (R.slimPieces.residualNear Fl : Set W.Carrier) ∧
    (z ∈ D.M₂ ↔ 0 ≤ R.slimPieces.residualFn Fl z) ∧
    (R.slimPieces.residualFn Fl z = 0 → z ∈ R.slimPieces.residualSet Fl)}
  have hfibP : R.circle.fibre c ⊆ interior P := fun x hx => by
    obtain ⟨O, ho, hxo, hOn, hM, hz⟩ := hmodel x (hfibF hx)
    exact mem_interior.2 ⟨O, fun y hy => ⟨hOn hy, hM y hy, hz y hy⟩, ho, hxo⟩
  have hEc : IsClosed D.edgeSet := by
    rw [← R.edgePiece_eq]
    exact (R.edge.proper _ R.edge.cbase_compact).isClosed
  let O₀ : Set W.Carrier := interior P ∩ (D.edgeSet)ᶜ
  have hfib : R.circle.proj ⁻¹' {c} ⊆ (Subtype.val ⁻¹' O₀ : Set R.circle.domain) := by
    intro x hx
    have hxf : (x : W.Carrier) ∈ R.circle.fibre c := ⟨x, hx, rfl⟩
    exact ⟨hfibP hxf, hnoE _ hxf⟩
  obtain ⟨V, hVo, hcV, -, hVsub⟩ := Geometry.Collapse.EdgeDisk.exists_open_tube_subset_EFC hcl
    (N := (Subtype.val ⁻¹' O₀ : Set R.circle.domain))
    ((isOpen_interior.inter hEc.isOpen_compl).preimage continuous_subtype_val) hfib
    (V := Set.univ) isOpen_univ trivial
  let Vo : TopologicalSpace.Opens R.circle.Base := ⟨V, hVo⟩
  have hO : ∀ x : R.circle.domain, R.circle.proj x ∈ V →
      (x : W.Carrier) ∈ interior P ∧ (x : W.Carrier) ∉ D.edgeSet := fun x hx => hVsub hx
  have hP : ∀ x : R.circle.domain, R.circle.proj x ∈ V → (x : W.Carrier) ∈ P := fun x hx =>
    interior_subset (hO x hx).1
  -- descent of the face function
  have hf : ContMDiffOn W.model 𝓘(ℝ, ℝ) ∞ (R.slimPieces.residualFn Fl)
      (R.circle.tube (Vo : Set R.circle.Base)) := by
    refine (R.slimPieces.residualFn_contMDiffOn_JN74 Fl).mono ?_
    rintro _ ⟨x, hx, rfl⟩
    exact (hP x hx).1
  have hconst : ∀ x y : R.circle.domain, R.circle.proj x ∈ Vo →
      R.circle.proj y = R.circle.proj x →
      R.slimPieces.residualFn Fl x.1 = R.slimPieces.residualFn Fl y.1 := fun x y hx hxy =>
    hconstH x y (hP x hx).1 (hP y (by rw [hxy]; exact hx)).1 hxy
  obtain ⟨hb, hbsm, hbdesc⟩ := exists_descended_of_fibreConst_JN74 R.circle Vo
    (R.slimPieces.residualFn Fl) hf hconst
  -- the sign model on the tube
  have hsign : ∀ x : R.circle.domain, R.circle.proj x ∈ V →
      ((x : W.Carrier) ∈ D.M₃ ↔ 0 ≤ R.slimPieces.residualFn Fl x) := by
    intro x hx
    obtain ⟨-, hnE⟩ := hO x hx
    have hrel : (x : W.Carrier) ∉ relInt D.M₂ D.edgeSet := fun h => hnE (relInt_subset_JN74 h)
    change (x : W.Carrier) ∈ D.M₂ \ relInt D.M₂ D.edgeSet ↔ _
    rw [← (hP x hx).2.1]
    exact ⟨fun h => h.1, fun h => ⟨h, hrel⟩⟩
  have hcb : ∀ b : R.circle.Base, b ∈ V → (b ∈ R.circle.cbase ↔ 0 ≤ hb b) := by
    intro b hbV
    rw [StageCutRows74.mem_cbase_iff_fibre_subset_JN74 (R := R)]
    constructor
    · intro hsubM
      obtain ⟨_, x, hx, rfl⟩ := R.fibre_nonempty_JN74 b
      have hxb : R.circle.proj x = b := hx
      have hxV : R.circle.proj x ∈ V := by rw [hxb]; exact hbV
      have h1 := (hsign x hxV).1 (hsubM ⟨x, hx, rfl⟩)
      rw [hbdesc x hxV, hxb] at h1
      exact h1
    · intro h0 _ hy
      obtain ⟨x, hx, rfl⟩ := hy
      have hxb : R.circle.proj x = b := hx
      have hxV : R.circle.proj x ∈ V := by rw [hxb]; exact hbV
      exact (hsign x hxV).2 (by rw [hbdesc x hxV, hxb]; exact h0)
  -- the value and the differential at the centre
  have hbc : hb c = 0 := by
    obtain ⟨x', hx'c, rfl⟩ := hx₀
    have hxb : R.circle.proj x' = c := hx'c
    have hxV : R.circle.proj x' ∈ V := by rw [hxb]; exact hcV
    rw [← hxb, ← hbdesc x' hxV]
    exact R.slimPieces.residualFn_eq_zero_JN74 Fl hx₀F
  have key : ∀ p : R.circle.domain, R.circle.proj p ∈ V →
      (p : W.Carrier) ∈ R.slimPieces.residualSet Fl →
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ) hb (R.circle.proj p) ≠ 0 := by
    intro p hpV hpF h0
    apply R.slimPieces.residualFn_mfderiv_ne_zero_JN74 Fl hpF
    have hbd : MDifferentiableAt (𝓡 2) 𝓘(ℝ, ℝ) hb (R.circle.proj p) :=
      (hbsm.contMDiffAt (hVo.mem_nhds hpV)).mdifferentiableAt (by simp)
    have hproj : MDifferentiableAt W.model (𝓡 2) R.circle.proj p :=
      (R.circle.proj_smooth p).mdifferentiableAt (by simp)
    have hev : (fun z : R.circle.domain => R.slimPieces.residualFn Fl z) =ᶠ[𝓝 p]
        hb ∘ R.circle.proj := by
      filter_upwards [R.circle.proj.continuous.continuousAt.preimage_mem_nhds
        (hVo.mem_nhds hpV)] with z hz
      exact hbdesc z hz
    rw [← mfderiv_restrict_open (I := W.model) (J := 𝓘(ℝ, ℝ)) (R.slimPieces.residualFn Fl)
      R.circle.domain p, hev.mfderiv_eq, mfderiv_comp p hbd hproj, h0]
    ext v
    rfl
  have hdhb : mfderiv (𝓡 2) 𝓘(ℝ, ℝ) hb c ≠ 0 := by
    obtain ⟨p, hp, hpx⟩ := hx₀
    have hpb : R.circle.proj p = c := hp
    have hpV : R.circle.proj p ∈ V := by rw [hpb]; exact hcV
    have := key p hpV (hpx ▸ hx₀F)
    rwa [hpb] at this
  -- the face clause
  have hface : {c'' | c'' ∈ Vo ∧ c'' ∈ R.circle.cbase ∧ (fun b => -hb b) c'' = 0} =
      {c'' | c'' ∈ Vo ∧ c'' ∈ R.circle.cbase ∧
        R.circle.fibre c'' ⊆ circleFaceSet R.slimPieces R.edge (.horizontal Fl)} := by
    ext b
    simp only [mem_ofPred_eq, neg_eq_zero]
    refine and_congr_right fun hbV => and_congr_right fun _ => ?_
    constructor
    · intro hb0
      rintro _ ⟨x, hx, rfl⟩
      have hxb : R.circle.proj x = b := hx
      have hxV : R.circle.proj x ∈ V := by rw [hxb]; exact hbV
      have h0 : R.slimPieces.residualFn Fl x = 0 := by rw [hbdesc x hxV, hxb]; exact hb0
      exact (hP x hxV).2.2 h0
    · intro hsubF
      obtain ⟨_, x, hx, rfl⟩ := R.fibre_nonempty_JN74 b
      have hxb : R.circle.proj x = b := hx
      have hxV : R.circle.proj x ∈ V := by rw [hxb]; exact hbV
      have h0 := R.slimPieces.residualFn_eq_zero_JN74 Fl (hsubF ⟨x, hx, rfl⟩)
      rw [← hxb, ← hbdesc x hxV]
      exact h0
  have hsign' : R.circle.cbase ∩ Vo = {c'' | c'' ∈ Vo ∧ (fun b => -hb b) c'' ≤ 0} := by
    ext b
    simp only [mem_inter_iff, mem_ofPred_eq, neg_nonpos]
    constructor
    · rintro ⟨hbc', hbV⟩
      exact ⟨hbV, (hcb b hbV).1 hbc'⟩
    · rintro ⟨hbV, hb'⟩
      exact ⟨(hcb b hbV).2 hb', hbV⟩
  refine R.localFaces_one_JN74 Vo hcV (.horizontal Fl) (fun b => -hb b) hbsm.neg
    (by simp [hbc]) ?_ hface hsign'
  change mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (-hb) c ≠ 0
  rw [mfderiv_neg]
  exact neg_ne_zero.2 hdhb

end StageCutRows74

end GC.GraphManifold.Assembly.FC39P0
