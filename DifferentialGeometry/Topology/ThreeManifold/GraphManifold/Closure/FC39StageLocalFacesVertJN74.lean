import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageLocalFacesDatumJN74

/-!
# Draft 74, `local_faces`, step 2: the vertical points

Lane S-JUNCTIONS (by S-JUNCTIONS4), G23 part 3 (suffix `_JN74`). The vertical case of
`JunctionRimFacts74.local_faces`: `c = rimBase c'` for a point `c'` of `C₂` that is NOT an endpoint
(`c' ∈ C₂ ∖ ∂C₂`). On any rows `R`, from the face facts `F` (g3, g4: the rim over a non-endpoint
does not meet `∂M₂`), the rim facts `rim_fibre`, `edge_region` and the fibre constancy of
`T = cornerT` (chain fact `cornerT_fibreConst_at_JN74`):

* a whole-fibre patch `V ∋ c` whose preimage lies in `int M₂`, in the edge source and over a
  preconnected neighbourhood of `c'` inside `C₂`;
* `T` descends to a smooth `T̄` on the patch (`cornerT_descends_JN74`), `T̄(c) = 0`, `dT̄(c) ≠ 0`;
* on the patch `C₁ = {T̄ ≥ 0}` (`M₃ = M₂ ∖ (M^edge ∖ vertical)` and `M^edge = {T ≤ 0}` there) and
  the vertical face is `{T̄ = 0}` (the whole vertical face of the component of `c'`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly.FC39P0

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n} {A : SmoothStageGeometry74 W E}
  {D : StageCutChoice74 A}

namespace StageCutRows74

variable (R : StageCutRows74 A D)

/-- **The rim over a non-endpoint of `C₂` lies in the interior of `M₂`.** -/
theorem rim_subset_interior_M₂_JN74 (F : JunctionFaceFacts74 A D R)
    (hsub : D.edgeSet ⊆ D.M₂) {c' : R.edge.Base} (hc' : c' ∈ R.edge.cbase)
    (hnf : c' ∉ frontier R.edge.cbase) : ∀ x ∈ R.edge.rim c', x ∈ interior D.M₂ := by
  have hedge : R.edge.edgePiece = D.edgeSet := D.edgePiece_edgeBundle74 R.edgeFacts
  intro x hx
  have hxE : x ∈ D.edgeSet := by
    rw [← hedge]
    obtain ⟨z, ⟨hz1, hz2⟩, rfl⟩ := hx
    exact ⟨z, ⟨hz1 ▸ hc', hz2.le⟩, rfl⟩
  by_contra hxi
  have hxfr : x ∈ frontier D.M₂ := ⟨subset_closure (hsub hxE), hxi⟩
  rw [F.frontier_M2] at hxfr
  obtain ⟨Fl, hFl⟩ := mem_iUnion.1 hxfr
  have hx2 : x ∈ ⋃ (e : R.edge.EdgeEnd) (_ : F.horizontal e = Fl), R.edge.disk e.1 := by
    rw [← F.edge_faces Fl]
    exact ⟨hxE, hFl⟩
  simp only [mem_iUnion] at hx2
  obtain ⟨e, -, z, ⟨hz1, -⟩, hzx⟩ := hx2
  obtain ⟨z', ⟨hz1', -⟩, hz'x⟩ := hx
  have hzz : z = z' := Subtype.ext (hzx.trans hz'x.symm)
  subst hzz
  exact hnf (hz1.symm.trans hz1' ▸ e.2)

/-- **`local_faces` at a vertical point `c = rimBase c'`, `c' ∈ C₂ ∖ ∂C₂`.** -/
theorem localFaces_vertical_JN74 (F : JunctionFaceFacts74 A D R)
    (rimBase : R.edge.Base → R.circle.Base)
    (hrim : ∀ c ∈ R.edge.cbase, R.edge.rim c = R.circle.fibre (rimBase c))
    (hreg : D.edgeSet ∩ D.M₃ = R.edge.vertical) (hsub : D.edgeSet ⊆ D.M₂)
    (hconstT : ∀ x y : R.circle.domain, (x : W.Carrier) ∈ R.edge.source →
      (y : W.Carrier) ∈ R.edge.source → R.circle.proj y = R.circle.proj x →
      R.cornerT x = R.cornerT y)
    {c' : R.edge.Base} (hc' : c' ∈ R.edge.cbase) (hnf : c' ∉ frontier R.edge.cbase) :
    ∃ U : TopologicalSpace.Opens R.circle.Base, rimBase c' ∈ U ∧
      ∃ (L : Finset (CircleFaceLabel R.slimPieces.ResidualFace R.edge.EdgeBaseComponent))
        (φ : CircleFaceLabel R.slimPieces.ResidualFace R.edge.EdgeBaseComponent →
          R.circle.Base → ℝ),
        1 ≤ L.card ∧ L.card ≤ 2 ∧
        (∀ f ∈ L, ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ (φ f) U ∧ φ f (rimBase c') = 0 ∧
          {c'' | c'' ∈ U ∧ c'' ∈ R.circle.cbase ∧ φ f c'' = 0} =
            {c'' | c'' ∈ U ∧ c'' ∈ R.circle.cbase ∧
              R.circle.fibre c'' ⊆ circleFaceSet R.slimPieces R.edge f}) ∧
        (Surjective fun w : TangentSpace (𝓡 2) (rimBase c') =>
          fun f : L => mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (φ f) (rimBase c') w) ∧
        R.circle.cbase ∩ U = {c'' | c'' ∈ U ∧ ∀ f ∈ L, φ f c'' ≤ 0} := by
  classical
  have hcl : IsClosedMap R.circle.proj := isClosedMap_circleBundle74 R.circleFacts
  have hrelint := R.relInt_edgeSet_eq_JN74 hreg hsub
  have hedge : R.edge.edgePiece = D.edgeSet := D.edgePiece_edgeBundle74 R.edgeFacts
  have hint : c' ∈ interior R.edge.cbase := by
    by_contra h
    exact hnf ⟨subset_closure hc', h⟩
  have : LocallyConnectedSpace R.edge.Base :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin 1)) R.edge.Base
  obtain ⟨Uc, hUco, hc'Uc, hUcpre, hUcsub⟩ := exists_open_preconnected_subset_JN74 hint
  have hUcC : Uc ⊆ R.edge.cbase := hUcsub
  let K : R.edge.EdgeBaseComponent := ActualComponent.of hc'
  have hUcK : Uc ⊆ K.1 := hUcpre.subset_connectedComponentIn hc'Uc hUcC
  have hrimc : R.circle.fibre (rimBase c') = R.edge.rim c' := (hrim c' hc').symm
  have hrimM2 := R.rim_subset_interior_M₂_JN74 F hsub hc' hnf
  -- the open set around the rim fibre
  let O₀ : Set W.Carrier :=
    interior D.M₂ ∩ Subtype.val '' (R.edge.proj ⁻¹' Uc : Set R.edge.source)
  have hO₀ : IsOpen O₀ := isOpen_interior.inter
    (R.edge.source.isOpen.isOpenMap_subtype_val _ (hUco.preimage R.edge.proj.continuous))
  have hfib : R.circle.proj ⁻¹' {rimBase c'} ⊆ (Subtype.val ⁻¹' O₀ : Set R.circle.domain) := by
    intro x hx
    have hxf : (x : W.Carrier) ∈ R.edge.rim c' := by
      rw [← hrimc]
      exact ⟨x, hx, rfl⟩
    obtain ⟨z, ⟨hz1, hz2⟩, hzx⟩ := hxf
    refine ⟨hrimM2 _ ⟨z, ⟨hz1, hz2⟩, hzx⟩, z, ?_, hzx⟩
    change R.edge.proj z ∈ Uc
    rw [hz1]
    exact hc'Uc
  obtain ⟨V, hVo, hcV, -, hVsub⟩ := Geometry.Collapse.EdgeDisk.exists_open_tube_subset_EFC hcl
    (N := (Subtype.val ⁻¹' O₀ : Set R.circle.domain)) (hO₀.preimage continuous_subtype_val) hfib
    (V := Set.univ) isOpen_univ trivial
  let Vo : TopologicalSpace.Opens R.circle.Base := ⟨V, hVo⟩
  have hO : ∀ x : R.circle.domain, R.circle.proj x ∈ V →
      (x : W.Carrier) ∈ interior D.M₂ ∧
        ∃ hxS : (x : W.Carrier) ∈ R.edge.source, R.edge.proj ⟨x, hxS⟩ ∈ Uc := by
    intro x hx
    obtain ⟨hM, z, hzU, hzx⟩ := hVsub hx
    have hxS : (x : W.Carrier) ∈ R.edge.source := by
      rw [← hzx]
      exact z.2
    refine ⟨hM, hxS, ?_⟩
    have hz : z = ⟨(x : W.Carrier), hxS⟩ := Subtype.ext hzx
    rw [← hz]
    exact hzU
  have hsrc : ∀ x : R.circle.domain, R.circle.proj x ∈ Vo → (x : W.Carrier) ∈ R.edge.source :=
    fun x hx => (hO x hx).2.1
  have hconst : ∀ x y : R.circle.domain, R.circle.proj x ∈ Vo →
      R.circle.proj y = R.circle.proj x → R.cornerT x = R.cornerT y := fun x y hx hxy =>
    hconstT x y (hsrc x hx) (hsrc y (by rw [hxy]; exact hx)) hxy
  obtain ⟨Tb, hTbsm, hTbdesc⟩ := cornerT_descends_JN74 R Vo hsrc hconst
  -- the sign model on the tube
  have hsign : ∀ x : R.circle.domain, R.circle.proj x ∈ V →
      ((x : W.Carrier) ∈ D.M₃ ↔ 0 ≤ R.cornerT x) := by
    intro x hx
    obtain ⟨hM, hxS, hxU⟩ := hO x hx
    have hT : R.cornerT x = R.edge.height ⟨x, hxS⟩ - R.edge.level := by
      simp only [StageCutRows74.cornerT, hxS, ↓reduceDIte]
    have hπ : R.edge.proj ⟨x, hxS⟩ ∈ R.edge.cbase := hUcC hxU
    have hE : (x : W.Carrier) ∈ D.edgeSet ↔ R.edge.height ⟨x, hxS⟩ ≤ R.edge.level := by
      rw [← hedge]
      constructor
      · rintro ⟨z, ⟨-, hz⟩, hzx⟩
        have : z = ⟨(x : W.Carrier), hxS⟩ := Subtype.ext hzx
        rw [← this]
        exact hz
      · intro h
        exact ⟨⟨x, hxS⟩, ⟨hπ, h⟩, rfl⟩
    have hVt : (x : W.Carrier) ∈ R.edge.vertical ↔ R.edge.height ⟨x, hxS⟩ = R.edge.level := by
      constructor
      · rintro ⟨z, ⟨-, hz⟩, hzx⟩
        have : z = ⟨(x : W.Carrier), hxS⟩ := Subtype.ext hzx
        rw [← this]
        exact hz
      · intro h
        exact ⟨⟨x, hxS⟩, ⟨hπ, h⟩, rfl⟩
    have hM2 : (x : W.Carrier) ∈ D.M₂ := interior_subset hM
    change (x : W.Carrier) ∈ D.M₂ \ relInt D.M₂ D.edgeSet ↔ _
    rw [hrelint, hT]
    simp only [Set.mem_sdiff, hE, hVt, not_and, not_not, sub_nonneg]
    constructor
    · intro h
      by_contra hlt
      have hlt' : R.edge.height ⟨x, hxS⟩ < R.edge.level := lt_of_not_ge hlt
      exact hlt'.ne (h.2 hlt'.le)
    · intro h
      exact ⟨hM2, fun hle => le_antisymm hle h⟩
  -- membership in `C₁`
  have hcb : ∀ b : R.circle.Base, b ∈ V → (b ∈ R.circle.cbase ↔ 0 ≤ Tb b) := by
    intro b hb
    rw [StageCutRows74.mem_cbase_iff_fibre_subset_JN74 (R := R)]
    constructor
    · intro hsubM
      obtain ⟨_, x, hx, rfl⟩ := R.fibre_nonempty_JN74 b
      have hxb : R.circle.proj x = b := hx
      have hxV : R.circle.proj x ∈ V := by rw [hxb]; exact hb
      have h1 := (hsign x hxV).1 (hsubM ⟨x, hx, rfl⟩)
      rw [hTbdesc x hxV, hxb] at h1
      exact h1
    · intro h0 _ hy
      obtain ⟨x, hx, rfl⟩ := hy
      have hxb : R.circle.proj x = b := hx
      have hxV : R.circle.proj x ∈ V := by rw [hxb]; exact hb
      exact (hsign x hxV).2 (by rw [hTbdesc x hxV, hxb]; exact h0)
  -- `T̄ = 0` at the centre and its differential
  have hTc : Tb (rimBase c') = 0 := by
    obtain ⟨_, x, hx, rfl⟩ := R.fibre_nonempty_JN74 (rimBase c')
    have hxb : R.circle.proj x = rimBase c' := hx
    have hxV : R.circle.proj x ∈ V := by rw [hxb]; exact hcV
    have hxr : (x : W.Carrier) ∈ R.edge.rim c' := by
      rw [← hrimc]
      exact ⟨x, hx, rfl⟩
    obtain ⟨z, ⟨-, hz2⟩, hzx⟩ := hxr
    have hxS : (x : W.Carrier) ∈ R.edge.source := hsrc x hxV
    have hz : z = ⟨(x : W.Carrier), hxS⟩ := Subtype.ext hzx
    have hh : R.edge.height ⟨x, hxS⟩ = R.edge.level := by
      rw [← hz]
      exact hz2
    have hT : R.cornerT x = 0 := by
      simp only [StageCutRows74.cornerT, hxS, ↓reduceDIte, hh, sub_self]
    rw [← hxb, ← hTbdesc x hxV, hT]
  have key : ∀ p : R.circle.domain, R.circle.proj p ∈ V → ∀ hpS : (p : W.Carrier) ∈ R.edge.source,
      R.edge.height ⟨p, hpS⟩ = R.edge.level →
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ) Tb (R.circle.proj p) ≠ 0 := by
    intro p hpV hpS hph h0
    apply R.mfderiv_cornerT_ne_zero_JN74 p hpS hph
    have hTbd : MDifferentiableAt (𝓡 2) 𝓘(ℝ, ℝ) Tb (R.circle.proj p) :=
      (hTbsm.contMDiffAt (hVo.mem_nhds hpV)).mdifferentiableAt (by simp)
    have hproj : MDifferentiableAt W.model (𝓡 2) R.circle.proj p :=
      (R.circle.proj_smooth p).mdifferentiableAt (by simp)
    have hev : R.cornerT =ᶠ[𝓝 p] Tb ∘ R.circle.proj := by
      filter_upwards [R.circle.proj.continuous.continuousAt.preimage_mem_nhds
        (hVo.mem_nhds hpV)] with z hz
      exact hTbdesc z hz
    rw [hev.mfderiv_eq, mfderiv_comp p hTbd hproj, h0]
    simp
  have hdTb : mfderiv (𝓡 2) 𝓘(ℝ, ℝ) Tb (rimBase c') ≠ 0 := by
    obtain ⟨_, p, hp, rfl⟩ := R.fibre_nonempty_JN74 (rimBase c')
    have hpb : R.circle.proj p = rimBase c' := hp
    have hpV : R.circle.proj p ∈ V := by rw [hpb]; exact hcV
    have hpr : (p : W.Carrier) ∈ R.edge.rim c' := by
      rw [← hrimc]
      exact ⟨p, hp, rfl⟩
    obtain ⟨z, ⟨-, hz2⟩, hzp⟩ := hpr
    have hpS : (p : W.Carrier) ∈ R.edge.source := hsrc p hpV
    have hz : z = ⟨(p : W.Carrier), hpS⟩ := Subtype.ext hzp
    have hph : R.edge.height ⟨p, hpS⟩ = R.edge.level := by
      rw [← hz]
      exact hz2
    have := key p hpV hpS hph
    rwa [hpb] at this
  -- the face clause
  have hface : {c'' | c'' ∈ Vo ∧ c'' ∈ R.circle.cbase ∧ (fun b => -Tb b) c'' = 0} =
      {c'' | c'' ∈ Vo ∧ c'' ∈ R.circle.cbase ∧
        R.circle.fibre c'' ⊆ circleFaceSet R.slimPieces R.edge (.vertical K)} := by
    ext b
    simp only [mem_ofPred_eq, neg_eq_zero]
    refine and_congr_right fun hbV => and_congr_right fun _ => ?_
    constructor
    · intro hT0
      rintro _ ⟨x, hx, rfl⟩
      have hxb : R.circle.proj x = b := hx
      have hxV : R.circle.proj x ∈ V := by rw [hxb]; exact hbV
      obtain ⟨-, hxS, hxU⟩ := hO x hxV
      have hT : R.cornerT x = R.edge.height ⟨x, hxS⟩ - R.edge.level := by
        simp only [StageCutRows74.cornerT, hxS, ↓reduceDIte]
      have h0 : R.cornerT x = 0 := by rw [hTbdesc x hxV, hxb]; exact hT0
      have hh : R.edge.height ⟨x, hxS⟩ = R.edge.level := by
        rw [hT] at h0
        exact sub_eq_zero.1 h0
      exact ⟨⟨x, hxS⟩, ⟨hUcK hxU, hh⟩, rfl⟩
    · intro hsubV
      obtain ⟨_, x, hx, rfl⟩ := R.fibre_nonempty_JN74 b
      have hxb : R.circle.proj x = b := hx
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
  have hsign' : R.circle.cbase ∩ Vo = {c'' | c'' ∈ Vo ∧ (fun b => -Tb b) c'' ≤ 0} := by
    ext b
    simp only [mem_inter_iff, mem_ofPred_eq, neg_nonpos]
    constructor
    · rintro ⟨hb, hbV⟩
      exact ⟨hbV, (hcb b hbV).1 hb⟩
    · rintro ⟨hbV, hb⟩
      exact ⟨(hcb b hbV).2 hb, hbV⟩
  refine R.localFaces_one_JN74 Vo hcV (.vertical K) (fun b => -Tb b) hTbsm.neg
    (by simp [hTc]) ?_ hface hsign'
  change mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (-Tb) (rimBase c') ≠ 0
  rw [mfderiv_neg]
  exact neg_ne_zero.2 hdTb

end StageCutRows74

end GC.GraphManifold.Assembly.FC39P0
