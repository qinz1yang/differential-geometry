import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.SyncedMobiusPieceMap

/-!
# The flow-out collar of the Möbius circle bundle

Lane MD5b, step (3) of `exists_syncedMobiusPiece`. Pulling the flow of a lifted bicollar `L` of
`c` back along `χ₀` gives a second half collar of the boundary torus of `mobiusBundleSet`:
`flowCollar (t, s) = χ₀⁻¹ (L.flow (±s) (χ₀ (mobiusExternalCollar (t, 0))))` for `s < wd`, a
partial diffeomorphism whose inverse records the bicollar coordinate of the base point and the
point where the backward flow meets the boundary (`tc`). Near the zero section the piece lies on
the side of `c` prescribed by the collar formula (`exists_side_mobius`), which makes the inverse
well defined.
-/

set_option autoImplicit false

noncomputable section
open Set Function Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert

namespace MobiusPiece

namespace PieceData

variable {C : CompactCarrier.{u}} {U : TopologicalSpace.Opens C.Carrier}
  {F : CircleFibration C U} {M : MobiusBase.{u}} (D : PieceData F M) (L : LiftedBicollar F D.c)

def sg (s : ℝ) : ℝ := (if D.b then (1 : ℝ) else -1) * s

theorem sg_eq (s : ℝ) : D.sg s = if D.b then s else -s := by
  unfold sg
  cases D.b <;> simp

theorem sg_sg (s : ℝ) : D.sg (D.sg s) = s := by
  unfold sg
  cases D.b <;> simp

theorem abs_sg (s : ℝ) : |D.sg s| = |s| := by
  unfold sg
  cases D.b <;> simp

theorem contDiff_sg : ContDiff ℝ ∞ D.sg :=
  contDiff_const.mul contDiff_id

def rside : ℝ := Classical.choose (exists_side_mobius M D.hι D.c D.hc D.b D.σ D.hcol)

theorem rside_pos : 0 < D.rside :=
  (Classical.choose_spec (exists_side_mobius M D.hι D.c D.hc D.b D.σ D.hcol)).1

theorem side {θ : Circle} {s : ℝ} (hs : |s| < D.rside) (h : D.c (θ, s) ∈ range D.ι) :
    0 ≤ D.sg s := by
  rw [sg_eq]
  exact (Classical.choose_spec (exists_side_mobius M D.hι D.c D.hc D.b D.σ D.hcol)).2 θ s hs h

def wd : ℝ := min (min L.width 1) D.rside / 2

theorem wd_pos : 0 < D.wd L :=
  half_pos (lt_min (lt_min L.width_pos one_pos) D.rside_pos)

theorem min_pos : 0 < min (min L.width 1) D.rside :=
  lt_min (lt_min L.width_pos one_pos) D.rside_pos

theorem wd_lt_width : D.wd L < L.width := by
  have h := min_le_left (min L.width 1) D.rside
  have h2 := min_le_left L.width 1
  unfold wd
  linarith [D.min_pos L]

theorem wd_lt_one : D.wd L < 1 := by
  have h := min_le_left (min L.width 1) D.rside
  have h2 := min_le_right L.width 1
  unfold wd
  linarith [D.min_pos L]

theorem wd_lt_rside : D.wd L < D.rside := by
  have h := min_le_right (min L.width 1) D.rside
  unfold wd
  linarith [D.min_pos L]

theorem contMDiff_χ₀U : ContMDiff (𝓡∂ 3) C.model ∞ D.χ₀ := fun x =>
  (ContMDiffAt.subtypeVal_comp_iff U D.χ₀ x).mp (D.contMDiff_χ₀ x)

def bd (t : Torus) : U := D.χ₀ (mobiusExternalCollar (t, halfZero))

theorem isBoundaryPoint_externalCollar (t : Torus) :
    (𝓡∂ 3).IsBoundaryPoint (mobiusExternalCollar.{u} (t, halfZero)) :=
  (isBoundaryPoint_iff_external _).mpr ⟨t, rfl⟩

theorem exists_bd (t : Torus) : ∃ θ : Circle, F.projection (D.bd t) = D.c (θ, 0) := by
  obtain ⟨θ, hθ⟩ := (D.mem_zero_iff _).mpr (isBoundaryPoint_externalCollar t)
  exact ⟨θ, hθ.symm⟩

theorem mem_source_c {θ : Circle} {s : ℝ} (hs : |s| < 1) : (θ, s) ∈ D.c.source := by
  rw [D.hc]
  exact abs_lt.mp hs

theorem projection_flow {x : U} {θ : Circle} {s r : ℝ} (hx : F.projection x = D.c (θ, s))
    (hs : |s| < L.width) (hsr : |s + r| < L.width) :
    F.projection (L.flow r x) = D.c (θ, s + r) := by
  rw [L.projection_flow, hx, L.baseFlow_apply θ s r hs hsr]

theorem mem_range_ι_of_side {θ : Circle} {s : ℝ} (hs : 0 ≤ s) (hs1 : s < 1) :
    D.c (θ, D.sg s) ∈ range D.ι := by
  refine ⟨M.collar (D.σ.symm θ, halfPoint s hs), ?_⟩
  rw [D.hcol _ s hs hs1, Diffeomorph.apply_symm_apply, sg_eq]

theorem flow_bd_mem (t : Torus) {s : ℝ} (hs : 0 ≤ s) (hsw : s < D.wd L) :
    L.flow (D.sg s) (D.bd t) ∈ range D.χ₀ := by
  obtain ⟨θ, hθ⟩ := D.exists_bd t
  rw [D.range_χ₀]
  change F.projection (L.flow (D.sg s) (D.bd t)) ∈ range D.ι
  have hw : |D.sg s| < L.width := by
    rw [abs_sg, abs_of_nonneg hs]
    exact hsw.trans (D.wd_lt_width L)
  rw [D.projection_flow L hθ (by simpa using L.width_pos) (by simpa using hw), zero_add]
  exact D.mem_range_ι_of_side hs (hsw.trans (D.wd_lt_one L))

theorem projection_flow_bd (t : Torus) {θ : Circle} (hθ : F.projection (D.bd t) = D.c (θ, 0))
    {s : ℝ} (hs : 0 ≤ s) (hsw : s < D.wd L) :
    F.projection (L.flow (D.sg s) (D.bd t)) = D.c (θ, D.sg s) := by
  have hw : |D.sg s| < L.width := by
    rw [abs_sg, abs_of_nonneg hs]
    exact hsw.trans (D.wd_lt_width L)
  rw [D.projection_flow L hθ (by simpa using L.width_pos) (by simpa using hw), zero_add]

def sc (x : mobiusBundleSet.{u}) : ℝ := (D.c.symm (F.projection (D.χ₀ x))).2

def collarTarget : Set mobiusBundleSet.{u} :=
  (fun x => F.projection (D.χ₀ x)) ⁻¹' (D.c.target ∩ D.c.symm ⁻¹' {q | |q.2| < D.wd L})

theorem isOpen_collarTarget : IsOpen (D.collarTarget L) := by
  have h1 : IsOpen (D.c.target ∩ D.c.symm ⁻¹' {q : Circle × ℝ | |q.2| < D.wd L}) :=
    D.c.toOpenPartialHomeomorph.continuousOn_symm.isOpen_inter_preimage D.c.open_target
      (isOpen_lt (continuous_abs.comp continuous_snd) continuous_const)
  exact h1.preimage (F.projection.continuous.comp D.contMDiff_χ₀U.continuous)

theorem eq_c_sc {x : mobiusBundleSet.{u}} (hx : x ∈ D.collarTarget L) :
    F.projection (D.χ₀ x) = D.c ((D.c.symm (F.projection (D.χ₀ x))).1, D.sc x) :=
  (D.c.toOpenPartialHomeomorph.right_inv hx.1).symm

theorem abs_sc_lt {x : mobiusBundleSet.{u}} (hx : x ∈ D.collarTarget L) : |D.sc x| < D.wd L :=
  hx.2

theorem sg_sc_nonneg {x : mobiusBundleSet.{u}} (hx : x ∈ D.collarTarget L) : 0 ≤ D.sg (D.sc x) := by
  refine D.side (θ := (D.c.symm (F.projection (D.χ₀ x))).1)
    ((D.abs_sc_lt L hx).trans (D.wd_lt_rside L)) ?_
  rw [← D.eq_c_sc L hx]
  have h : D.χ₀ x ∈ F.projection ⁻¹' range D.ι := D.range_χ₀ ▸ ⟨x, rfl⟩
  exact h

theorem flow_back_mem {x : mobiusBundleSet.{u}} (hx : x ∈ D.collarTarget L) :
    L.flow (-D.sc x) (D.χ₀ x) ∈ range D.χ₀ ∧
      F.projection (L.flow (-D.sc x) (D.χ₀ x)) =
        D.c ((D.c.symm (F.projection (D.χ₀ x))).1, 0) := by
  have hw := (D.abs_sc_lt L hx).trans (D.wd_lt_width L)
  have hp : F.projection (L.flow (-D.sc x) (D.χ₀ x)) =
      D.c ((D.c.symm (F.projection (D.χ₀ x))).1, 0) := by
    rw [D.projection_flow L (D.eq_c_sc L hx) hw (by simpa using L.width_pos), add_neg_cancel]
  refine ⟨?_, hp⟩
  rw [D.range_χ₀]
  change F.projection _ ∈ range D.ι
  rw [hp]
  refine ⟨M.collar (D.σ.symm (D.c.symm (F.projection (D.χ₀ x))).1, halfZero), ?_⟩
  rw [mobius_zero_eq M D.c D.b D.σ D.hcol, Diffeomorph.apply_symm_apply]

theorem back_isBoundaryPoint {x : mobiusBundleSet.{u}} (hx : x ∈ D.collarTarget L) :
    (𝓡∂ 3).IsBoundaryPoint (D.χinv (L.flow (-D.sc x) (D.χ₀ x))) := by
  obtain ⟨hm, hp⟩ := D.flow_back_mem L hx
  rw [← D.mem_zero_iff, D.χ₀_χinv hm, hp]
  exact ⟨_, rfl⟩

def tc (x : mobiusBundleSet.{u}) : Torus :=
  (mobiusExternalCollar.{u}.symm (D.χinv (L.flow (-D.sc x) (D.χ₀ x)))).1

theorem externalCollar_tc {x : mobiusBundleSet.{u}} (hx : x ∈ D.collarTarget L) :
    mobiusExternalCollar (D.tc L x, halfZero) = D.χinv (L.flow (-D.sc x) (D.χ₀ x)) := by
  obtain ⟨t, ht⟩ := (isBoundaryPoint_iff_external _).mp (D.back_isBoundaryPoint L hx)
  have hsrc : (t, halfZero) ∈ mobiusExternalCollar.{u}.source := by
    rw [mobiusExternalCollar_source]
    exact zero_mem_halfCollarSource t
  have h1 : mobiusExternalCollar.{u}.symm (D.χinv (L.flow (-D.sc x) (D.χ₀ x))) = (t, halfZero) := by
    rw [← ht]
    exact mobiusExternalCollar.toOpenPartialHomeomorph.left_inv hsrc
  unfold tc
  rw [h1, ht]


theorem halfSpaceOneLift_coord (t : ℝ) : (Manifold.halfSpaceOneLift t).1 0 = max t 0 := rfl

theorem halfSpace_ext {a b : EuclideanHalfSpace 1} (h : a.1 0 = b.1 0) : a = b := by
  apply Subtype.ext
  ext i
  rw [Subsingleton.elim i 0]
  exact h

theorem contMDiff_externalCollar_zero :
    ContMDiff torusModel (𝓡∂ 3) ∞ (fun t : Torus => mobiusExternalCollar.{u} (t, halfZero)) := by
  intro t
  have hsrc : (t, halfZero) ∈ mobiusExternalCollar.{u}.source := by
    rw [mobiusExternalCollar_source]
    exact zero_mem_halfCollarSource t
  exact (mobiusExternalCollar.contMDiffOn_toFun.contMDiffAt
    (mobiusExternalCollar.open_source.mem_nhds hsrc)).comp t
      ((contMDiff_id.prodMk contMDiff_const) t)

theorem contMDiff_bd : ContMDiff torusModel C.model ∞ D.bd :=
  D.contMDiff_χ₀U.comp contMDiff_externalCollar_zero

theorem contMDiffOn_sc : ContMDiffOn (𝓡∂ 3) 𝓘(ℝ, ℝ) ∞ D.sc (D.collarTarget L) := by
  intro x hx
  have h1 : ContMDiffAt (𝓡∂ 3) (SurfaceModel.model F.base.kind) ∞
      (fun x => F.projection (D.χ₀ x)) x := (F.smooth.comp D.contMDiff_χ₀U) x
  have h2 : ContMDiffAt (SurfaceModel.model F.base.kind) ((𝓡 1).prod 𝓘(ℝ, ℝ)) ∞ D.c.symm
      (F.projection (D.χ₀ x)) :=
    D.c.contMDiffOn_invFun.contMDiffAt (D.c.open_target.mem_nhds hx.1)
  exact (contMDiff_snd.contMDiffAt.comp x (h2.comp x h1)).contMDiffWithinAt

theorem sc_toFun (p : Torus × EuclideanHalfSpace 1) (hp : p.2.1 0 < D.wd L) :
    D.sc (D.χinv (L.flow (D.sg (p.2.1 0)) (D.bd p.1))) = D.sg (p.2.1 0) ∧
      F.projection (D.χ₀ (D.χinv (L.flow (D.sg (p.2.1 0)) (D.bd p.1)))) ∈ D.c.target := by
  obtain ⟨θ, hθ⟩ := D.exists_bd p.1
  have hm := D.flow_bd_mem L p.1 p.2.2 hp
  have hpr := D.projection_flow_bd L p.1 hθ p.2.2 hp
  have hsrc : (θ, D.sg (p.2.1 0)) ∈ D.c.source := by
    refine D.mem_source_c ?_
    rw [abs_sg, abs_of_nonneg p.2.2]
    exact hp.trans (D.wd_lt_one L)
  refine ⟨?_, ?_⟩
  · unfold sc
    rw [D.χ₀_χinv hm, hpr, D.c.symm_apply_apply hsrc]
  · rw [D.χ₀_χinv hm, hpr]
    exact D.c.toOpenPartialHomeomorph.map_source hsrc

def flowCollar :
    PartialDiffeomorph halfCollarModel (𝓡∂ 3) (Torus × EuclideanHalfSpace 1) mobiusBundleSet.{u} ∞
    where
  toFun p := D.χinv (L.flow (D.sg (p.2.1 0)) (D.bd p.1))
  invFun x := (D.tc L x, Manifold.halfSpaceOneLift (D.sg (D.sc x)))
  source := {p | p.2.1 0 < D.wd L}
  target := D.collarTarget L
  map_source' p hp := by
    obtain ⟨h1, h2⟩ := D.sc_toFun L p hp
    refine ⟨h2, ?_⟩
    change |D.sc _| < D.wd L
    rw [h1, abs_sg, abs_of_nonneg p.2.2]
    exact hp
  map_target' x hx := by
    change max (D.sg (D.sc x)) 0 < D.wd L
    rw [max_eq_left (D.sg_sc_nonneg L hx)]
    exact (le_abs_self _).trans_lt (by rw [abs_sg]; exact D.abs_sc_lt L hx)
  left_inv' p hp := by
    have hm := D.flow_bd_mem L p.1 p.2.2 hp
    obtain ⟨h1, -⟩ := D.sc_toFun L p hp
    refine Prod.ext ?_ ?_
    · change (mobiusExternalCollar.{u}.symm (D.χinv (L.flow (-D.sc _) (D.χ₀ _)))).1 = p.1
      rw [h1, D.χ₀_χinv hm, ← L.flow_add, neg_add_cancel, L.flow_zero]
      change (mobiusExternalCollar.{u}.symm (D.χinv (D.χ₀ _))).1 = p.1
      rw [D.χinv_χ₀]
      have hsrc : (p.1, halfZero) ∈ mobiusExternalCollar.{u}.source := by
        rw [mobiusExternalCollar_source]
        exact zero_mem_halfCollarSource p.1
      rw [mobiusExternalCollar.symm_apply_apply hsrc]
    · apply halfSpace_ext
      change max (D.sg (D.sc _)) 0 = p.2.1 0
      rw [h1, sg_sg, max_eq_left p.2.2]
  right_inv' x hx := by
    have hs := D.sg_sc_nonneg L hx
    change D.χinv (L.flow (D.sg (max (D.sg (D.sc x)) 0)) (D.bd (D.tc L x))) = x
    rw [max_eq_left hs, sg_sg]
    unfold bd
    rw [D.externalCollar_tc L hx, D.χ₀_χinv (D.flow_back_mem L hx).1, ← L.flow_add,
      add_neg_cancel, L.flow_zero, D.χinv_χ₀]
  open_source := isOpen_lt
    (Manifold.contMDiff_halfSpaceOneCoordinate.continuous.comp continuous_snd) continuous_const
  open_target := D.isOpen_collarTarget L
  contMDiffOn_toFun := by
    refine D.contMDiffOn_χinv (isOpen_lt
      (Manifold.contMDiff_halfSpaceOneCoordinate.continuous.comp continuous_snd) continuous_const)
      ?_ (fun p hp => D.flow_bd_mem L p.1 p.2.2 hp)
    have hA : ContMDiff halfCollarModel 𝓘(ℝ, ℝ) ∞
        (fun p : Torus × EuclideanHalfSpace 1 => D.sg (p.2.1 0)) :=
      D.contDiff_sg.contMDiff.comp (Manifold.contMDiff_halfSpaceOneCoordinate.comp contMDiff_snd)
    have hB : ContMDiff halfCollarModel C.model ∞
        (fun p : Torus × EuclideanHalfSpace 1 => D.bd p.1) :=
      D.contMDiff_bd.comp contMDiff_fst
    exact (contMDiff_subtype_val.comp (L.smooth.comp (hA.prodMk hB))).contMDiffOn
  contMDiffOn_invFun := by
    intro x hx
    have hT := D.isOpen_collarTarget L
    have hsc := D.contMDiffOn_sc L
    have hg' : ContMDiffOn (𝓡∂ 3) C.model ∞
        (fun x => (L.flow (-D.sc x) (D.χ₀ x) : C.Carrier)) (D.collarTarget L) := by
      intro y hy
      have h1 : ContMDiffAt (𝓡∂ 3) 𝓘(ℝ, ℝ) ∞ (fun y => -D.sc y) y :=
        contDiff_neg.contMDiff.contMDiffAt.comp y (hsc.contMDiffAt (hT.mem_nhds hy))
      exact (contMDiff_subtype_val.contMDiffAt.comp y (L.smooth.contMDiffAt.comp y
        (h1.prodMk (D.contMDiff_χ₀U y)))).contMDiffWithinAt
    have hχ := D.contMDiffOn_χinv hT hg' (fun y hy => (D.flow_back_mem L hy).1)
    have hmem : D.χinv (L.flow (-D.sc x) (D.χ₀ x)) ∈ mobiusExternalCollar.{u}.target := by
      rw [← D.externalCollar_tc L hx]
      refine mobiusExternalCollar.map_source ?_
      rw [mobiusExternalCollar_source]
      exact zero_mem_halfCollarSource _
    have h1 : ContMDiffWithinAt (𝓡∂ 3) torusModel ∞ (D.tc L) (D.collarTarget L) x := by
      have h2 := (mobiusExternalCollar.{u}.contMDiffOn_invFun.contMDiffAt
        (mobiusExternalCollar.open_target.mem_nhds hmem)).comp_contMDiffWithinAt x (hχ x hx)
      exact contMDiff_fst.contMDiffAt.comp_contMDiffWithinAt x h2
    have h3 : ContMDiffWithinAt (𝓡∂ 3) (𝓡∂ 1) ∞
        (fun x => Manifold.halfSpaceOneLift (D.sg (D.sc x))) (D.collarTarget L) x := by
      have h4 : ContMDiffWithinAt (𝓡∂ 3) 𝓘(ℝ, ℝ) ∞ (fun x => D.sg (D.sc x))
          (D.collarTarget L) x :=
        D.contDiff_sg.contMDiff.contMDiffAt.comp_contMDiffWithinAt x (hsc x hx)
      exact ContMDiffWithinAt.comp (f := fun x => D.sg (D.sc x)) (t := Ici 0) x
        (Manifold.contMDiffOn_halfSpaceOneLift _ (mem_Ici.mpr (D.sg_sc_nonneg L hx))) h4
        (fun y hy => mem_Ici.mpr (D.sg_sc_nonneg L hy))
    exact h1.prodMk h3

theorem flowCollar_apply (p : Torus × EuclideanHalfSpace 1) :
    D.flowCollar L p = D.χinv (L.flow (D.sg (p.2.1 0)) (D.bd p.1)) := rfl

theorem flowCollar_source : (D.flowCollar L).source = {p | p.2.1 0 < D.wd L} := rfl

end PieceData

end MobiusPiece

end GC.Seifert
