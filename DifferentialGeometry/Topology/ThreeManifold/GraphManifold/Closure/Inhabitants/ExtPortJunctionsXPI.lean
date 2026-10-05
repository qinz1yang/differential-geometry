import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.ExtPortRegionsXPI

/-!
# FC39 external-port regression instance: the junctions and the rows `extportRowsW_XPI`

**`extportRowsW_XPI : FC39RowsV2 carrierW_XPI portsE_XPI`** — the second end-to-end FC39 row tuple
of the tree, the first one with a NON-EMPTY external port family (external review 63, D63-7):

* carrier `T² × I = {1/2 ≤ |z| ≤ 3} × S¹`, two ports (the two boundary tori);
* two cusp cores (`rad ≥ 2` owning port `0`, `rad ≤ 1` owning port `1`), one slim torus interval
  (`1 ≤ rad ≤ 3/2`, end `rad = 1` shared with the inner cusp, end `rad = 3/2` new), no zero domain,
  the empty edge bundle, the circle region `3/2 ≤ rad ≤ 2` over the annulus `3/2 ≤ ‖w‖ ≤ 2`;
* `extportJunctions_XPI : JunctionsV2 …` — every field: cover, separated interiors, the shared face,
  `M₃ = R`, `frontier M₂ = ∂M₂`, `R ∩ ∂M₂ = ∂M₂`, `S ∩ M₂ =` the new end, the removed shared face,
  and the labelled local faces of `C₁` (one horizontal face at each boundary circle);
* `extportTubes_XPI` — the labelled corner tubes (there is no edge endpoint).
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0.ExtPortXPI

local notation "E2" => EuclideanSpace ℝ (Fin 2)

/-! ## The pieces cover, their interiors are separated -/

theorem cover_XPI :
    (⋃ a, allPieces extportSlim_XPI extportEdgeBundle_XPI extportCircle_XPI a) = univ := by
  refine eq_univ_of_forall fun x => mem_iUnion.mpr ?_
  have hb := rad_bounds_XPI x
  by_cases h1 : rad_XPI x ≤ 1
  · refine ⟨.inl (.inr (.inl 1)), ?_⟩
    change x ∈ range (cuspPiece_XPI 1).map
    rw [range_cuspPiece_one_XPI]
    exact h1
  by_cases h2 : rad_XPI x ≤ 3 / 2
  · refine ⟨.inl (.inr (.inr (0 : Fin 1))), ?_⟩
    change x ∈ range slimPiece_XPI.map
    rw [range_slimPiece_XPI]
    exact ⟨by linarith, h2⟩
  by_cases h3 : rad_XPI x ≤ 2
  · refine ⟨.inr false, ?_⟩
    change x ∈ extportCircle_XPI.region
    rw [extportCircle_region_XPI]
    exact ⟨by linarith, h3⟩
  · refine ⟨.inl (.inr (.inl 0)), ?_⟩
    change x ∈ range (cuspPiece_XPI 0).map
    rw [range_cuspPiece_zero_XPI]
    change 2 ≤ rad_XPI x
    linarith

/-- The open radial interval containing the interior of each piece. -/
def pieceIv_XPI : extportSlim_XPI.RowIndex ⊕ Bool → ℝ × ℝ
  | .inl (.inl _) => (7, 8)
  | .inl (.inr (.inl b)) => if b = 0 then (2, 4) else (0, 1)
  | .inl (.inr (.inr _)) => (1, 3 / 2)
  | .inr true => (5, 6)
  | .inr false => (3 / 2, 2)

theorem interior_allPieces_XPI (a : extportSlim_XPI.RowIndex ⊕ Bool) :
    interior (allPieces extportSlim_XPI extportEdgeBundle_XPI extportCircle_XPI a) ⊆
      {x | (pieceIv_XPI a).1 < rad_XPI x ∧ rad_XPI x < (pieceIv_XPI a).2} := by
  intro x hx
  have hb := rad_bounds_XPI x
  rcases a with (i | b | j) | c
  · exact i.elim0
  · rcases Fin.exists_fin_two.mp ⟨b, rfl⟩ with rfl | rfl
    · change x ∈ interior (range (cuspPiece_XPI 0).map) at hx
      rw [range_cuspPiece_zero_XPI] at hx
      have h := interior_le_rad_XPI (by norm_num) hx
      exact ⟨h, by change rad_XPI x < 4; linarith⟩
    · change x ∈ interior (range (cuspPiece_XPI 1).map) at hx
      rw [range_cuspPiece_one_XPI] at hx
      have h := interior_rad_le_XPI (by norm_num) hx
      exact ⟨by change (0 : ℝ) < rad_XPI x; linarith, h⟩
  · change x ∈ interior (range slimPiece_XPI.map) at hx
    rw [range_slimPiece_XPI,
      show {x : carrierW_XPI.Carrier | 1 ≤ rad_XPI x ∧ rad_XPI x ≤ 3 / 2} =
        {x | 1 ≤ rad_XPI x} ∩ {x | rad_XPI x ≤ 3 / 2} from rfl, interior_inter] at hx
    exact ⟨interior_le_rad_XPI (c := 1) (by norm_num) hx.1,
      interior_rad_le_XPI (c := 3 / 2) (by norm_num) hx.2⟩
  · cases c
    · change x ∈ interior extportCircle_XPI.region at hx
      rw [extportCircle_region_XPI,
        show {x : carrierW_XPI.Carrier | 3 / 2 ≤ rad_XPI x ∧ rad_XPI x ≤ 2} =
          {x | 3 / 2 ≤ rad_XPI x} ∩ {x | rad_XPI x ≤ 2} from rfl, interior_inter] at hx
      exact ⟨interior_le_rad_XPI (c := 3 / 2) (by norm_num) hx.1,
        interior_rad_le_XPI (c := 2) (by norm_num) hx.2⟩
    · change x ∈ interior extportEdgeBundle_XPI.edgePiece at hx
      rw [extportEdge_edgePiece_XPI, interior_empty] at hx
      exact hx.elim

theorem pieceIv_sep_XPI (a a' : extportSlim_XPI.RowIndex ⊕ Bool) (hne : a ≠ a') :
    (pieceIv_XPI a).2 ≤ (pieceIv_XPI a').1 ∨ (pieceIv_XPI a').2 ≤ (pieceIv_XPI a).1 := by
  rcases a with (i | b | j) | c
  · exact i.elim0
  · rcases Fin.exists_fin_two.mp ⟨b, rfl⟩ with rfl | rfl <;>
    rcases a' with (i' | b' | j') | c'
    all_goals first
      | exact i'.elim0
      | (rcases Fin.exists_fin_two.mp ⟨b', rfl⟩ with rfl | rfl <;>
          first | exact absurd rfl hne | norm_num [pieceIv_XPI])
      | (cases c' <;> norm_num [pieceIv_XPI])
      | norm_num [pieceIv_XPI]
  · rcases a' with (i' | b' | j') | c'
    · exact i'.elim0
    · rcases Fin.exists_fin_two.mp ⟨b', rfl⟩ with rfl | rfl <;> norm_num [pieceIv_XPI]
    · exact absurd (by rw [Subsingleton.elim (α := Fin 1) j j']) hne
    · cases c' <;> norm_num [pieceIv_XPI]
  · rcases a' with (i' | b' | j') | c'
    · exact i'.elim0
    · cases c <;> rcases Fin.exists_fin_two.mp ⟨b', rfl⟩ with rfl | rfl <;>
        norm_num [pieceIv_XPI]
    · cases c <;> norm_num [pieceIv_XPI]
    · cases c <;> cases c' <;> first | exact absurd rfl hne | norm_num [pieceIv_XPI]

theorem interiors_disjoint_XPI :
    Pairwise fun a a' : extportSlim_XPI.RowIndex ⊕ Bool =>
      Disjoint (interior (allPieces extportSlim_XPI extportEdgeBundle_XPI extportCircle_XPI a))
        (interior (allPieces extportSlim_XPI extportEdgeBundle_XPI extportCircle_XPI a')) := by
  intro a a' hne
  refine Set.disjoint_left.mpr fun x hx hx' => ?_
  have h1 := interior_allPieces_XPI a hx
  have h2 := interior_allPieces_XPI a' hx'
  rcases pieceIv_sep_XPI a a' hne with h | h
  · linarith [h1.2, h2.1]
  · linarith [h1.1, h2.2]

/-! ## The labelled local faces of `C₁` -/

/-- The base radial function `a + σ ‖w‖²`. -/
def baseRadialFn_XPI (a σ : ℝ) (c : circleBaseOpens_XPI) : ℝ := a + σ * ‖c.val‖ ^ 2

theorem contMDiff_baseRadialFn_XPI (a σ : ℝ) :
    ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (baseRadialFn_XPI a σ) := by
  have h : ContDiff ℝ ∞ (fun p : E2 => a + σ * ‖p‖ ^ 2) :=
    contDiff_const.add (contDiff_const.mul (contDiff_norm_sq ℝ))
  exact h.contMDiff.comp contMDiff_subtype_val

theorem hasMFDerivAt_baseRadialFn_XPI (a σ : ℝ) (c : circleBaseOpens_XPI) :
    HasMFDerivAt (𝓡 2) 𝓘(ℝ, ℝ) (baseRadialFn_XPI a σ) c
      ((σ • (2 • (innerSL ℝ c.val).comp (ContinuousLinearMap.id ℝ E2))).comp
        (ContinuousLinearMap.id ℝ E2)) := by
  have hF : HasFDerivAt (fun p : E2 => a + σ * ‖p‖ ^ 2)
      (σ • (2 • (innerSL ℝ c.val).comp (ContinuousLinearMap.id ℝ E2))) c.val :=
    ((hasFDerivAt_id c.val).norm_sq.const_mul σ).const_add a
  have hM : HasMFDerivAt (𝓡 2) 𝓘(ℝ, ℝ) (fun p : E2 => a + σ * ‖p‖ ^ 2) c.val
      (σ • (2 • (innerSL ℝ c.val).comp (ContinuousLinearMap.id ℝ E2))) :=
    hasMFDerivAt_iff_hasFDerivAt.2 hF
  exact hM.comp c (hasMFDerivAt_subtype_val (I := 𝓡 2) circleBaseOpens_XPI c)

theorem mfderiv_baseRadialFn_self_XPI (a σ : ℝ) (c : circleBaseOpens_XPI) :
    mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (baseRadialFn_XPI a σ) c c.val = σ * (2 * ‖c.val‖ ^ 2) := by
  rw [(hasMFDerivAt_baseRadialFn_XPI a σ c).mfderiv]
  change σ * ((2 : ℕ) • inner ℝ c.val c.val) = _
  rw [real_inner_self_eq_norm_sq, nsmul_eq_mul, Nat.cast_ofNat]
  rfl

/-- The defining function of a labelled face of the circle base: `‖w‖² − 4` for the cusp face,
`9/4 − ‖w‖²` for the new slim end (no vertical face: the edge bundle is empty). -/
def faceFn_XPI :
    CircleFaceLabel extportSlim_XPI.ResidualFace extportEdgeBundle_XPI.EdgeBaseComponent →
      circleBaseOpens_XPI → ℝ
  | .horizontal (.inl _) => baseRadialFn_XPI (-4) 1
  | .horizontal (.inr _) => baseRadialFn_XPI (9 / 4) (-1)
  | .vertical c => isEmptyElim c

theorem frontier_circleCbase_XPI {c : circleBaseOpens_XPI}
    (hc : c ∈ frontier circleCbase_XPI) : ‖c.val‖ = 3 / 2 ∨ ‖c.val‖ = 2 := by
  have hcC : c ∈ circleCbase_XPI := isCompact_circleCbase_XPI.isClosed.frontier_subset hc
  by_contra h
  simp only [not_or] at h
  have hopen : IsOpen {c' : circleBaseOpens_XPI | 3 / 2 < ‖c'.val‖ ∧ ‖c'.val‖ < 2} :=
    (isOpen_lt continuous_const (continuous_norm.comp continuous_subtype_val)).inter
      (isOpen_lt (continuous_norm.comp continuous_subtype_val) continuous_const)
  have hsub : {c' : circleBaseOpens_XPI | 3 / 2 < ‖c'.val‖ ∧ ‖c'.val‖ < 2} ⊆ circleCbase_XPI :=
    fun c' hc' => ⟨hc'.1.le, hc'.2.le⟩
  have hmem : c ∈ {c' : circleBaseOpens_XPI | 3 / 2 < ‖c'.val‖ ∧ ‖c'.val‖ < 2} :=
    ⟨lt_of_le_of_ne hcC.1 (Ne.symm h.1), lt_of_le_of_ne hcC.2 h.2⟩
  exact hc.2 (interior_maximal hsub hopen hmem)

theorem norm_eq_of_sq_eq_XPI {t r : ℝ} (ht : 0 ≤ t) (hr : 0 ≤ r) (h : t ^ 2 = r ^ 2) : t = r :=
  (pow_left_inj₀ ht hr two_ne_zero).mp h

/-- A fibre lies in the face of radius `ρ` iff its base point has norm `ρ`. -/
theorem fibre_subset_iff_XPI {c : circleBaseOpens_XPI} {ρ : ℝ} :
    extportCircle_XPI.fibre c ⊆ {x | rad_XPI x = ρ} ↔ ‖c.val‖ = ρ := by
  constructor
  · intro h
    have h1 := h (circlePoint_mem_fibre_XPI c 1)
    change rad_XPI (circlePoint_XPI c 1) = ρ at h1
    rwa [rad_circlePoint_XPI] at h1
  · intro h x hx
    change rad_XPI x = ρ
    rw [rad_of_mem_fibre_XPI hx, h]

/-- The local face data at a frontier point of `C₁` of norm `ρ`, with the single face `F`. -/
theorem local_face_at_XPI (c : circleBaseOpens_XPI) (F : extportSlim_XPI.ResidualFace) (ρ a σ : ℝ)
    (U : TopologicalSpace.Opens circleBaseOpens_XPI) (hc : ‖c.val‖ = ρ)
    (hρ : 0 < ρ) (hσ : σ ≠ 0) (hφ : faceFn_XPI (.horizontal F) = baseRadialFn_XPI a σ)
    (hF : extportSlim_XPI.residualSet F = {x | rad_XPI x = ρ}) (hzero : a + σ * ρ ^ 2 = 0)
    (hU : circleCbase_XPI ∩ U = {c' | c' ∈ U ∧ baseRadialFn_XPI a σ c' ≤ 0}) :
    ∃ (L : Finset (CircleFaceLabel extportSlim_XPI.ResidualFace
        extportEdgeBundle_XPI.EdgeBaseComponent))
      (φ : CircleFaceLabel extportSlim_XPI.ResidualFace extportEdgeBundle_XPI.EdgeBaseComponent →
        circleBaseOpens_XPI → ℝ),
      1 ≤ L.card ∧ L.card ≤ 2 ∧
      (∀ f ∈ L, ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ (φ f) U ∧ φ f c = 0 ∧
        {c' | c' ∈ U ∧ c' ∈ circleCbase_XPI ∧ φ f c' = 0} =
          {c' | c' ∈ U ∧ c' ∈ circleCbase_XPI ∧
            extportCircle_XPI.fibre c' ⊆ circleFaceSet extportSlim_XPI extportEdgeBundle_XPI f}) ∧
      (Surjective fun w : TangentSpace (𝓡 2) c =>
        fun f : L => mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (φ f) c w) ∧
      circleCbase_XPI ∩ U = {c' | c' ∈ U ∧ ∀ f ∈ L, φ f c' ≤ 0} := by
  have hsq : ∀ c' : circleBaseOpens_XPI, baseRadialFn_XPI a σ c' = 0 ↔ ‖c'.val‖ = ρ := by
    intro c'
    constructor
    · intro h0
      have h1 : σ * (‖c'.val‖ ^ 2 - ρ ^ 2) = 0 := by
        rw [baseRadialFn_XPI] at h0
        linarith
      exact norm_eq_of_sq_eq_XPI (norm_nonneg _) hρ.le
        (sub_eq_zero.mp ((mul_eq_zero.mp h1).resolve_left hσ))
    · intro h
      rw [baseRadialFn_XPI, h, hzero]
  refine ⟨{.horizontal F}, faceFn_XPI, by simp, by simp, ?_, ?_, ?_⟩
  · intro f hf
    rw [Finset.mem_singleton] at hf
    subst hf
    rw [hφ]
    refine ⟨(contMDiff_baseRadialFn_XPI a σ).contMDiffOn, (hsq c).mpr hc, ?_⟩
    ext c'
    simp only [Set.mem_ofPred_eq]
    change _ ↔ c' ∈ U ∧ c' ∈ circleCbase_XPI ∧
      extportCircle_XPI.fibre c' ⊆ extportSlim_XPI.residualSet F
    rw [hF, fibre_subset_iff_XPI, hsq]
  · intro g
    set f₀ : ({.horizontal F} : Finset (CircleFaceLabel extportSlim_XPI.ResidualFace
      extportEdgeBundle_XPI.EdgeBaseComponent)) := ⟨.horizontal F, Finset.mem_singleton_self _⟩
    have hD : σ * (2 * ‖c.val‖ ^ 2) ≠ 0 :=
      mul_ne_zero hσ (mul_ne_zero two_ne_zero (pow_ne_zero 2 (by rw [hc]; exact hρ.ne')))
    let r : ℝ := g f₀
    refine ⟨(r / (σ * (2 * ‖c.val‖ ^ 2))) • c.val, ?_⟩
    funext ⟨f, hf⟩
    have hf' : f = .horizontal F := Finset.mem_singleton.mp hf
    subst hf'
    change mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (faceFn_XPI (.horizontal F)) c
      ((r / (σ * (2 * ‖c.val‖ ^ 2))) • c.val) = r
    rw [hφ, (hasMFDerivAt_baseRadialFn_XPI a σ c).mfderiv]
    change σ * ((2 : ℕ) • inner ℝ c.val ((r / (σ * (2 * ‖c.val‖ ^ 2))) • c.val)) = r
    rw [inner_smul_right, real_inner_self_eq_norm_sq, nsmul_eq_mul, Nat.cast_ofNat]
    have hn : ‖c.val‖ ≠ 0 := by rw [hc]; exact hρ.ne'
    field_simp
  · rw [hU]
    ext c'
    simp only [Set.mem_ofPred_eq, Finset.mem_singleton, forall_eq, hφ]

/-- **The labelled local faces of `C₁`** (`JunctionsV2.local_faces`): at `‖w‖ = 3/2` the new slim
end, at `‖w‖ = 2` the internal face of the outer cusp. -/
theorem local_faces_XPI : ∀ c ∈ frontier extportCircle_XPI.cbase,
    ∃ U : TopologicalSpace.Opens extportCircle_XPI.Base, c ∈ U ∧
      ∃ (L : Finset (CircleFaceLabel extportSlim_XPI.ResidualFace
          extportEdgeBundle_XPI.EdgeBaseComponent))
        (φ : CircleFaceLabel extportSlim_XPI.ResidualFace extportEdgeBundle_XPI.EdgeBaseComponent →
          extportCircle_XPI.Base → ℝ),
        1 ≤ L.card ∧ L.card ≤ 2 ∧
        (∀ f ∈ L, ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ (φ f) U ∧ φ f c = 0 ∧
          {c' | c' ∈ U ∧ c' ∈ extportCircle_XPI.cbase ∧ φ f c' = 0} =
            {c' | c' ∈ U ∧ c' ∈ extportCircle_XPI.cbase ∧
              extportCircle_XPI.fibre c' ⊆
                circleFaceSet extportSlim_XPI extportEdgeBundle_XPI f}) ∧
        (Surjective fun w : TangentSpace (𝓡 2) c =>
          fun f : L => mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (φ f) c w) ∧
        extportCircle_XPI.cbase ∩ U = {c' | c' ∈ U ∧ ∀ f ∈ L, φ f c' ≤ 0} := by
  intro c hc
  have hcont : Continuous fun c' : circleBaseOpens_XPI => ‖c'.val‖ :=
    continuous_norm.comp continuous_subtype_val
  rcases frontier_circleCbase_XPI hc with h | h
  · refine ⟨⟨{c' | ‖c'.val‖ < 7 / 4}, isOpen_lt hcont continuous_const⟩,
      (show ‖c.val‖ < 7 / 4 by rw [h]; norm_num), ?_⟩
    refine local_face_at_XPI c newEndFace_XPI (3 / 2) (9 / 4) (-1) _
      h (by norm_num) (by norm_num) rfl
      residualSet_newEnd_XPI (by norm_num) ?_
    ext c'
    simp only [mem_inter_iff, Set.mem_ofPred_eq, baseRadialFn_XPI]
    change (3 / 2 ≤ ‖c'.val‖ ∧ ‖c'.val‖ ≤ 2) ∧ ‖c'.val‖ < 7 / 4 ↔
      ‖c'.val‖ < 7 / 4 ∧ 9 / 4 + -1 * ‖c'.val‖ ^ 2 ≤ 0
    have h0 := norm_nonneg c'.val
    constructor
    · rintro ⟨⟨h1, -⟩, h3⟩
      exact ⟨h3, by nlinarith⟩
    · rintro ⟨h3, h4⟩
      refine ⟨⟨?_, by linarith⟩, h3⟩
      by_contra hlt
      rw [not_le] at hlt
      nlinarith
  · refine ⟨⟨{c' | 7 / 4 < ‖c'.val‖}, isOpen_lt continuous_const hcont⟩,
      (show 7 / 4 < ‖c.val‖ by rw [h]; norm_num), ?_⟩
    refine local_face_at_XPI c cusp0Face_XPI 2 (-4) 1 _
      h (by norm_num) (by norm_num) rfl
      residualSet_cusp0_XPI (by norm_num) ?_
    ext c'
    simp only [mem_inter_iff, Set.mem_ofPred_eq, baseRadialFn_XPI]
    change (3 / 2 ≤ ‖c'.val‖ ∧ ‖c'.val‖ ≤ 2) ∧ 7 / 4 < ‖c'.val‖ ↔
      7 / 4 < ‖c'.val‖ ∧ -4 + 1 * ‖c'.val‖ ^ 2 ≤ 0
    have h0 := norm_nonneg c'.val
    constructor
    · rintro ⟨⟨-, h2⟩, h3⟩
      exact ⟨h3, by nlinarith⟩
    · rintro ⟨h3, h4⟩
      refine ⟨⟨by linarith, ?_⟩, h3⟩
      by_contra hlt
      rw [not_le] at hlt
      nlinarith

/-! ## The junctions -/

theorem extportEdge_vertical_XPI : extportEdgeBundle_XPI.vertical = ∅ := by
  refine Set.eq_empty_of_forall_notMem ?_
  rintro x ⟨y, -, -⟩
  exact not_mem_bot_XPI _ y.2

theorem shared_eq_XPI : ∀ e F, extportSlim_XPI.endKind e = some F →
    extportSlim_XPI.endSet e = neighbourSet F := by
  intro e F h
  obtain ⟨he, rfl⟩ := (slimEndKind_some_iff_XPI (e := e) (F := F)).mp h
  rw [endSet_XPI, he, bandEndRadius_slim_false_XPI, neighbourSet_shared_XPI]

theorem shared_removed_XPI : ∀ σ : ActualSharedFace extportSlim_XPI,
    extportSlim_XPI.endSet σ.1 ⊆
      relInt (regionM1 extportZeroDomains_XPI extportCuspCores_XPI) extportSlim_XPI.union := by
  intro σ
  have he : σ.1.1.2 = false := by
    obtain ⟨F, hF⟩ := Option.isSome_iff_exists.mp σ.2
    exact ((slimEndKind_some_iff_XPI (e := σ.1) (F := F)).mp hF).1
  rw [endSet_XPI, he, bandEndRadius_slim_false_XPI, relInt_M1_slim_XPI]
  intro x hx
  change rad_XPI x = 1 at hx
  exact ⟨hx.ge, by rw [hx]; norm_num⟩

theorem region_boundary_XPI :
    extportCircle_XPI.region ∩ extportSlim_XPI.boundaryM2 =
      extportSlim_XPI.boundaryM2 \
        relInt extportSlim_XPI.boundaryM2 extportEdgeBundle_XPI.horizontalDisks := by
  have hH : extportEdgeBundle_XPI.horizontalDisks = ∅ :=
    Set.iUnion_eq_empty.mpr fun e => isEmptyElim e
  rw [hH, relInt_empty_XPI, sdiff_empty, extportCircle_region_XPI, boundaryM2_XPI]
  ext x
  simp only [mem_inter_iff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨-, h⟩
    exact h
  · intro h
    refine ⟨?_, h⟩
    rcases h with h | h <;> constructor <;> linarith

theorem slim_M2_XPI :
    extportSlim_XPI.union ∩ regionM2 extportSlim_XPI =
      ⋃ e : extportSlim_XPI.NewEnd, extportSlim_XPI.endSet e.1 := by
  have hnew : ∀ e : extportSlim_XPI.NewEnd,
      extportSlim_XPI.endSet e.1 = {x | rad_XPI x = 3 / 2} := by
    intro e
    rw [endSet_XPI, (slimEndKind_none_iff_XPI (e := e.1)).mp e.2]
    rfl
  rw [slimUnion_XPI, regionM2_XPI]
  ext x
  simp only [mem_inter_iff, Set.mem_ofPred_eq, mem_iUnion]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    refine ⟨slimNewEnd_XPI, ?_⟩
    rw [hnew]
    change rad_XPI x = 3 / 2
    linarith
  · rintro ⟨e, he⟩
    rw [hnew] at he
    change rad_XPI x = 3 / 2 at he
    constructor <;> constructor <;> linarith

/-- **The junctions of the external-port instance** (§5.6–§5.7): every field. -/
def extportJunctions_XPI :
    JunctionsV2 carrierW_XPI portsE_XPI extportZeroDomains_XPI extportCuspCores_XPI
      extportSlim_XPI extportEdgeBundle_XPI extportCircle_XPI where
  cover := cover_XPI
  interiors_disjoint := interiors_disjoint_XPI
  shared_eq := shared_eq_XPI
  zero_cusp_disjoint i := i.elim0
  horizontal := isEmptyElim
  horizontal_disk e := isEmptyElim e
  edge_faces F := by
    rw [extportEdge_edgePiece_XPI, empty_inter]
    exact (Set.iUnion_eq_empty.mpr fun e => isEmptyElim e).symm
  rimBase := isEmptyElim
  rimBase_smooth x _ := isEmptyElim x
  rim_fibre c _ := isEmptyElim c
  edge_region := by rw [extportEdge_edgePiece_XPI, empty_inter, extportEdge_vertical_XPI]
  local_faces := local_faces_XPI
  region_eq := by rw [regionM3_XPI, extportCircle_region_XPI]
  frontier_M2 := frontier_M2_XPI
  region_boundary := region_boundary_XPI
  slim_M2 := slim_M2_XPI
  shared_removed := shared_removed_XPI

/-- **The labelled corner tubes of the external-port instance**: there is no edge endpoint. -/
def extportTubes_XPI : LabelledCornerTubes extportJunctions_XPI where
  base e := isEmptyElim e
  rimBase_mem e := isEmptyElim e
  chart e := isEmptyElim e
  chart_source e := isEmptyElim e
  chart_center e := isEmptyElim e
  tube_source e := isEmptyElim e
  tube_near e := isEmptyElim e
  height_eq e := isEmptyElim e
  face_eq e := isEmptyElim e
  descended e := isEmptyElim e
  descended_smooth e := isEmptyElim e
  descended_regular e := isEmptyElim e
  descended_eq e := isEmptyElim e
  vertex_side {e} := isEmptyElim e
  edge_side {e} := isEmptyElim e
  region_side {e} := isEmptyElim e

/-- **The rows of the external-port regression instance** (review 63, D63-7): `T² × I` with two
external ports, two cusp cores, one slim torus interval sharing a face with the inner cusp, the
empty edge bundle and the circle region `3/2 ≤ rad ≤ 2`. -/
def extportRowsW_XPI : FC39RowsV2 carrierW_XPI portsE_XPI where
  zero := extportZeroDomains_XPI
  cusp := extportCuspCores_XPI
  slim := extportSlim_XPI
  edge := extportEdgeBundle_XPI
  edgeModels := extportEdgeModels_XPI
  circle := extportCircle_XPI
  junctions := extportJunctions_XPI
  labelledTubes := extportTubes_XPI

end GC.GraphManifold.Assembly.FC39P0.ExtPortXPI
