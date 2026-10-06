import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageGeometryH74
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageCornerRankKernel74

/-!
# Draft 74, D74-14 layer 2 on the actual rows: `CornerRank74.rank` from `rank_two` and `db ≠ 0`

Lane S-JUNCTIONS2 (suffix `_JN74`). At an actual endpoint `e` of the rows' edge bundle let `p` be a
point of the rim fibre over `rimBase e`, `b` the descended face equation (`h_F = b ∘ q₁` on an open
neighbourhood of `p`, `db(e) ≠ 0`). The rim agreement `rim e = circle fibre (rimBase e)` puts `p` on
the rim of `e`; there `EdgeBundle.rank_two` (EDP04) says `v ↦ (dq₁ v, dT v)` is onto, so
`v ↦ d(T, h_F) v` is onto `ℝ × ℝ` (`cornerRank_surjective_JN74`, the `rank` field of
`CornerRank74`).
`exists_cornerRank_descended_JN74` builds the whole `CornerRank74` and `CornerDescended74` of an
endpoint from the LOCAL description near the rim fibre (open neighbourhoods in the buffer on which
`h_F = b ∘ q₁` and the sign model hold) — the neighbourhood of the whole fibre is the union of
these. `exists_cornerCutFacts_JN74` / `stageCutGeometry_of_corner_data74` assemble `H` from
`CornerDescent74` (D74-14 layer 1) and these per-endpoint data.
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

/-- A point of the circle fibre over the rim base point of an endpoint lies in the edge source, on
the level of the edge height, over the endpoint (the rim agreement `rim e = circle fibre`). -/
theorem rimPoint_data_JN74 {A : SmoothStageGeometry74 W E} {D : StageCutChoice74 A}
    {R : StageCutRows74 A D} {G : JunctionRimFacts74 A D R}
    (e : R.edge.EdgeEnd) (p : R.circle.domain) (hp : R.circle.proj p = G.rimBase e.1) :
    ∃ x : R.edge.source, (x : W.Carrier) = p ∧ R.edge.proj x = e.1 ∧
      R.edge.height x = R.edge.level := by
  have hfib : (p : W.Carrier) ∈ R.circle.fibre (G.rimBase e.1) := ⟨p, hp, rfl⟩
  rw [← G.rim_fibre e.1 (R.edge.frontier_cbase_subset e.2)] at hfib
  obtain ⟨x, ⟨hx1, hx2⟩, hxp⟩ := hfib
  exact ⟨x, hxp, hx1, hx2⟩

/-- **D74-14 layer 2 on the actual rows (`CornerRank74.rank`).** At a point `p` of the rim fibre
over `rimBase e`, if `h_F = b ∘ q₁` near `p` with `b` smooth near `e` and `db(e) ≠ 0`, then the
differential of `(T, h_F)` (the corner pair) is onto `ℝ × ℝ`: EDP04's rank two for `(q₁, T)` plus
the invertible descended differential. -/
theorem cornerRank_surjective_JN74 {A : SmoothStageGeometry74 W E} {D : StageCutChoice74 A}
    {R : StageCutRows74 A D} {F : JunctionFaceFacts74 A D R} {G : JunctionRimFacts74 A D R}
    (e : R.edge.EdgeEnd) (p : R.circle.domain) (hp : R.circle.proj p = G.rimBase e.1)
    (b : R.edge.Base → ℝ) (U : TopologicalSpace.Opens R.edge.Base) (heU : e.1 ∈ U)
    (hb : ContMDiffOn (𝓡 1) 𝓘(ℝ, ℝ) ∞ b U) (hbreg : mfderiv (𝓡 1) 𝓘(ℝ, ℝ) b e.1 ≠ 0)
    (N : Set R.circle.domain) (hN : IsOpen N) (hpN : p ∈ N)
    (hNeq : ∀ x ∈ N, ∃ hx : (x : W.Carrier) ∈ R.edge.source,
      R.slimPieces.residualFn (F.horizontal e) x = b (R.edge.proj ⟨x, hx⟩)) :
    Surjective (mfderiv W.model 𝓘(ℝ, ℝ × ℝ)
      (fun z : R.circle.domain =>
        (R.cornerT z, R.slimPieces.residualFn (F.horizontal e) z)) p) := by
  classical
  obtain ⟨x₀, hx₀p, hx₀e, hx₀h⟩ := rimPoint_data_JN74 (G := G) e p hp
  let T : W.Carrier → ℝ := fun z =>
    if hz : z ∈ R.edge.source then R.edge.height ⟨z, hz⟩ - R.edge.level else 0
  let q : W.Carrier → R.edge.Base := fun z =>
    if hz : z ∈ R.edge.source then R.edge.proj ⟨z, hz⟩ else R.edge.proj x₀
  have hTfun : (fun y : R.edge.source => T y) = fun y => R.edge.height y - R.edge.level := by
    funext y
    simp only [T, y.2, ↓reduceDIte]
  have hqfun : (fun y : R.edge.source => q y) = R.edge.proj := by
    funext y
    simp only [q, y.2, ↓reduceDIte]
  have hTd : MDifferentiableAt W.model 𝓘(ℝ, ℝ) T (x₀ : W.Carrier) := by
    refine (mdifferentiableAt_subtype_iff (U := R.edge.source) (f := T) (x := x₀)).mp ?_
    rw [hTfun]
    exact ((R.edge.height_smooth.sub contMDiff_const).contMDiffAt).mdifferentiableAt
      (by decide)
  have hqd : MDifferentiableAt W.model (𝓡 1) q (x₀ : W.Carrier) := by
    refine (mdifferentiableAt_subtype_iff (U := R.edge.source) (f := q) (x := x₀)).mp ?_
    rw [hqfun]
    exact (R.edge.proj_smooth.contMDiffAt).mdifferentiableAt (by decide)
  have hqx : q (x₀ : W.Carrier) = e.1 := by
    simp only [q, x₀.2, ↓reduceDIte]
    exact hx₀e
  have hbd : MDifferentiableAt (𝓡 1) 𝓘(ℝ, ℝ) b (q (x₀ : W.Carrier)) := by
    rw [hqx]
    exact (hb.contMDiffAt (U.isOpen.mem_nhds heU)).mdifferentiableAt (by decide)
  have hbne : mfderiv (𝓡 1) 𝓘(ℝ, ℝ) b (q (x₀ : W.Carrier)) ≠ 0 := by
    rw [hqx]
    exact hbreg
  have hopen : IsOpen (Subtype.val '' N : Set W.Carrier) :=
    R.circle.domain.isOpen.isOpenMap_subtype_val N hN
  have hpx : (x₀ : W.Carrier) = (p : W.Carrier) := hx₀p
  have hmem : (x₀ : W.Carrier) ∈ (Subtype.val '' N : Set W.Carrier) := ⟨p, hpN, hpx.symm⟩
  have hr : R.slimPieces.residualFn (F.horizontal e) =ᶠ[𝓝 (x₀ : W.Carrier)] b ∘ q := by
    refine Filter.eventuallyEq_of_mem (hopen.mem_nhds hmem) ?_
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨hx, hxeq⟩ := hNeq y hy
    rw [hxeq]
    simp only [Function.comp_apply, q, hx, ↓reduceDIte]
  have e1 : mfderiv W.model (𝓡 1) q (x₀ : W.Carrier) = mfderiv W.model (𝓡 1) R.edge.proj x₀ := by
    have := mfderiv_restrict_open (I := W.model) (J := 𝓡 1) q R.edge.source x₀
    rw [hqfun] at this
    exact this.symm
  have e2 : mfderiv W.model 𝓘(ℝ, ℝ) T (x₀ : W.Carrier) =
      mfderiv W.model 𝓘(ℝ, ℝ) R.edge.height x₀ := by
    have := mfderiv_restrict_open (I := W.model) (J := 𝓘(ℝ, ℝ)) T R.edge.source x₀
    rw [hTfun, mfderiv_sub_const_JN74] at this
    exact this.symm
  have hrank : Surjective fun v : TangentSpace W.model (x₀ : W.Carrier) =>
      (mfderiv W.model (𝓡 1) q (x₀ : W.Carrier) v,
        mfderiv W.model 𝓘(ℝ, ℝ) T (x₀ : W.Carrier) v) := by
    intro uc
    obtain ⟨v, hv⟩ := R.edge.rank_two x₀ hx₀h uc
    refine ⟨v, ?_⟩
    rw [← hv]
    exact Prod.ext (congrArg (fun L => L v) e1) (congrArg (fun L => L v) e2)
  have hsurj := surjective_mfderiv_pair_JN74 (I := W.model) (IB := 𝓡 1) hqd hTd hbd hbne hr hrank
  have hrest := mfderiv_restrict_open (I := W.model) (J := 𝓘(ℝ, ℝ × ℝ))
    (fun z : W.Carrier => (T z, R.slimPieces.residualFn (F.horizontal e) z))
    R.circle.domain p
  have hfun : (fun z : R.circle.domain => (R.cornerT z, R.slimPieces.residualFn (F.horizontal e) z))
      = fun z : R.circle.domain =>
        (fun z : W.Carrier => (T z, R.slimPieces.residualFn (F.horizontal e) z)) z := rfl
  rw [hfun, hrest]
  rw [hpx] at hsurj
  exact hsurj

/-- **One endpoint of `H` from the local description near the rim fibre.** Given the descended face
equation `b` (`db(e) ≠ 0`) and, at every point of the rim fibre, an open neighbourhood inside the
edge source and the residual buffer on which `h_F = b ∘ q₁` and the three-sided sign model hold,
the neighbourhood of the WHOLE fibre is the union of these, the rank is `cornerRank_surjective_JN74`
and `b` is the descended function. -/
theorem exists_cornerRank_descended_JN74 {A : SmoothStageGeometry74 W E}
    {D : StageCutChoice74 A} {R : StageCutRows74 A D} {F : JunctionFaceFacts74 A D R}
    {G : JunctionRimFacts74 A D R} (e : R.edge.EdgeEnd)
    (hfib : ∃ p : R.circle.domain, R.circle.proj p = G.rimBase e.1)
    (b : R.edge.Base → ℝ) (U : TopologicalSpace.Opens R.edge.Base) (heU : e.1 ∈ U)
    (hb : ContMDiffOn (𝓡 1) 𝓘(ℝ, ℝ) ∞ b U) (hbreg : mfderiv (𝓡 1) 𝓘(ℝ, ℝ) b e.1 ≠ 0)
    (hloc : ∀ p : R.circle.domain, R.circle.proj p = G.rimBase e.1 →
      ∃ N : Set R.circle.domain, IsOpen N ∧ p ∈ N ∧
        (∀ x ∈ N, (x : W.Carrier) ∈ R.edge.source ∧
          (x : W.Carrier) ∈ R.slimPieces.residualNear (F.horizontal e)) ∧
        (∀ x ∈ N, ∃ hx : (x : W.Carrier) ∈ R.edge.source,
          R.slimPieces.residualFn (F.horizontal e) x = b (R.edge.proj ⟨x, hx⟩)) ∧
        (∀ x ∈ N,
          ((x : W.Carrier) ∈ R.slimPieces.rowSet (R.slimPieces.residualOwner (F.horizontal e)) ↔
            R.slimPieces.residualFn (F.horizontal e) x ≤ 0) ∧
          ((x : W.Carrier) ∈ R.edge.wholeComponent e.component ↔
            0 ≤ R.slimPieces.residualFn (F.horizontal e) x ∧ R.cornerT x ≤ 0) ∧
          ((x : W.Carrier) ∈ R.circle.region ↔
            0 ≤ R.cornerT x ∧ 0 ≤ R.slimPieces.residualFn (F.horizontal e) x))) :
    ∃ K : CornerRank74 F G e, Nonempty (CornerDescended74 K) := by
  classical
  obtain ⟨p₀, hp₀⟩ := hfib
  choose N hNo hpN hNbuf hNeq hNsign using hloc
  let nb : Set R.circle.domain :=
    ⋃ (p : R.circle.domain) (hp : R.circle.proj p = G.rimBase e.1), N p hp
  have hmem : ∀ x, x ∈ nb ↔ ∃ (p : R.circle.domain) (hp : R.circle.proj p = G.rimBase e.1),
      x ∈ N p hp := fun x => by simp only [nb, mem_iUnion]
  have hnb_open : IsOpen nb :=
    isOpen_iUnion fun p => isOpen_iUnion fun hp => hNo p hp
  have hrank := cornerRank_surjective_JN74 (F := F) (G := G) e p₀ hp₀ b U heU hb hbreg
    (N p₀ hp₀) (hNo p₀ hp₀) (hpN p₀ hp₀) (hNeq p₀ hp₀)
  let K : CornerRank74 F G e :=
    { point := p₀
      point_proj := hp₀
      rank := hrank
      nbhd := nb
      nbhd_open := hnb_open
      fibre_sub := fun p hp => (hmem p).2 ⟨p, hp, hpN p hp⟩
      nbhd_buffer := fun x hx => by
        obtain ⟨p, hp, hxp⟩ := (hmem x).1 hx
        exact hNbuf p hp x hxp
      sign := fun x hx => by
        obtain ⟨p, hp, hxp⟩ := (hmem x).1 hx
        exact hNsign p hp x hxp }
  refine ⟨K, ⟨?_⟩⟩
  exact
    { descended := b
      descended_smooth := ⟨U, heU, hb⟩
      descended_regular := hbreg
      descended_eq := fun x hx => by
        obtain ⟨p, hp, hxp⟩ := (hmem x).1 hx
        exact hNeq p hp x hxp }

/-- **The corner facts of `H` from the descent layer and the per-endpoint rank data.** -/
theorem exists_cornerCutFacts_JN74 {A : SmoothStageGeometry74 W E}
    {D : StageCutChoice74 A} {R : StageCutRows74 A D} {F : JunctionFaceFacts74 A D R}
    {G : JunctionRimFacts74 A D R} (hdesc : ∀ e, CornerDescent74 F G e)
    (hrank : ∀ e, ∃ K : CornerRank74 F G e, Nonempty (CornerDescended74 K)) :
    Nonempty (CornerCutFacts74 F G) := by
  choose K hK using hrank
  exact ⟨⟨hdesc, K, fun e => (hK e).some⟩⟩

end GC.GraphManifold.Assembly.FC39P0
