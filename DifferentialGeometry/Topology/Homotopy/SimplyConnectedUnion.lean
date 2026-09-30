import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.UnitInterval

namespace DifferentialGeometry.Topology

open Set unitInterval
open scoped ContinuousMap

variable {X : Type*} [TopologicalSpace X]

theorem IsSimplyConnected.paths_homotopic_in_ambient {s : Set X}
    (hs : IsSimplyConnected s) {x y : X} (p q : Path x y)
    (hp : ∀ t, p t ∈ s) (hq : ∀ t, q t ∈ s) : p.Homotopic q := by
  let x' : s := ⟨x, p.source ▸ hp 0⟩
  let y' : s := ⟨y, p.target ▸ hp 1⟩
  let p' : Path x' y' :=
    { toFun := fun t => ⟨p t, hp t⟩
      continuous_toFun := p.continuous.subtype_mk _
      source' := Subtype.ext p.source
      target' := Subtype.ext p.target }
  let q' : Path x' y' :=
    { toFun := fun t => ⟨q t, hq t⟩
      continuous_toFun := q.continuous.subtype_mk _
      source' := Subtype.ext q.source
      target' := Subtype.ext q.target }
  have : SimplyConnectedSpace s := hs
  exact (SimplyConnectedSpace.paths_homotopic p' q').map ⟨Subtype.val, continuous_subtype_val⟩

private def intervalSegment (a b : I) : Path a b where
  toFun t := ⟨(1 - (t : ℝ)) * a + t * b, by
    have ha := a.property
    have hb := b.property
    have ht := t.property
    constructor <;> nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) ha.1,
      mul_nonneg ht.1 hb.1, mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr ha.2),
      mul_nonneg ht.1 (sub_nonneg.mpr hb.2)]⟩
  continuous_toFun := by fun_prop
  source' := by ext; simp
  target' := by ext; simp

private theorem intervalSegment_mem {a b : I} (hab : a ≤ b) (t : I) :
    intervalSegment a b t ∈ Icc a b := by
  have ht := t.property
  change (a : ℝ) ≤ (1 - (t : ℝ)) * a + t * b ∧
    (1 - (t : ℝ)) * a + t * b ≤ b
  have hab' : (a : ℝ) ≤ b := hab
  constructor <;> nlinarith [mul_nonneg ht.1 (sub_nonneg.mpr hab'),
    mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr hab')]

private theorem intervalSegment_self (a : I) : intervalSegment a a = Path.refl a := by
  ext t
  change (1 - (t : ℝ)) * a + t * a = a
  ring

set_option backward.isDefEq.respectTransparency false in
theorem simplyConnectedSpace_of_open_cover {U V : Set X}
    (hUo : IsOpen U) (hVo : IsOpen V) (hcover : U ∪ V = univ)
    (hU : IsSimplyConnected U) (hV : IsSimplyConnected V)
    (hUV : IsPathConnected (U ∩ V)) : SimplyConnectedSpace X := by
  classical
  obtain ⟨o, hoU, hoV⟩ := hUV.nonempty
  let α (x : X) (hx : x ∈ U) : Path o x :=
    (hU.isPathConnected.joinedIn o hoU x hx).somePath
  let β (x : X) (hx : x ∈ V) : Path o x :=
    (hV.isPathConnected.joinedIn o hoV x hx).somePath
  have hα (x : X) (hx : x ∈ U) (t : I) : α x hx t ∈ U :=
    (hU.isPathConnected.joinedIn o hoU x hx).somePath_mem t
  have hβ (x : X) (hx : x ∈ V) (t : I) : β x hx t ∈ V :=
    (hV.isPathConnected.joinedIn o hoV x hx).somePath_mem t
  have hmem (x : X) : x ∈ U ∨ x ∈ V := by rw [← mem_union, hcover]; trivial
  let δ (x : X) : Path o x := if hx : x ∈ U then α x hx else β x ((hmem x).resolve_left hx)
  have hδU (x : X) (hx : x ∈ U) : (δ x).Homotopic (α x hx) := by
    simp only [δ, dite_eq_left hx]
    exact Path.Homotopic.refl _
  have hδV (x : X) (hx : x ∈ V) : (δ x).Homotopic (β x hx) := by
    by_cases hxU : x ∈ U
    · let c := (hUV.joinedIn o ⟨hoU, hoV⟩ x ⟨hxU, hx⟩).somePath
      have hc t : c t ∈ U ∩ V :=
        (hUV.joinedIn o ⟨hoU, hoV⟩ x ⟨hxU, hx⟩).somePath_mem t
      exact (hδU x hxU).trans <|
        (IsSimplyConnected.paths_homotopic_in_ambient hU (α x hxU) c (hα x hxU) fun t => (hc t).1).trans
          (IsSimplyConnected.paths_homotopic_in_ambient hV c (β x hx) (fun t => (hc t).2) (hβ x hx))
    · simp only [δ, dite_eq_right hxU]
      exact Path.Homotopic.refl _
  have hstep {x y : X} (p : Path x y)
      (hp : (∀ t, p t ∈ U) ∨ (∀ t, p t ∈ V)) :
      ((δ x).trans p).Homotopic (δ y) := by
    rcases hp with hp | hp
    · have hx : x ∈ U := p.source ▸ hp 0
      have hy : y ∈ U := p.target ▸ hp 1
      refine ((hδU x hx).hcomp (.refl p)).trans <| ?_
      refine (IsSimplyConnected.paths_homotopic_in_ambient hU _ _ ?_ (hα y hy)).trans (hδU y hy).symm
      intro t
      have := Set.mem_range_self t (f := (α x hx).trans p)
      rw [Path.trans_range] at this
      rcases this with ⟨s, hs⟩ | ⟨s, hs⟩
      · exact hs ▸ hα x hx s
      · exact hs ▸ hp s
    · have hx : x ∈ V := p.source ▸ hp 0
      have hy : y ∈ V := p.target ▸ hp 1
      refine ((hδV x hx).hcomp (.refl p)).trans <| ?_
      refine (IsSimplyConnected.paths_homotopic_in_ambient hV _ _ ?_ (hβ y hy)).trans (hδV y hy).symm
      intro t
      have := Set.mem_range_self t (f := (β x hx).trans p)
      rw [Path.trans_range] at this
      rcases this with ⟨s, hs⟩ | ⟨s, hs⟩
      · exact hs ▸ hβ x hx s
      · exact hs ▸ hp s
  have hpath (γ : C(I, X)) :
      ((δ (γ 0)).trans ((intervalSegment 0 1).map γ.continuous)).Homotopic (δ (γ 1)) := by
    let c : Bool → Set I := fun b => γ ⁻¹' (if b then U else V)
    obtain ⟨t, ht0, hmono, ⟨N, hN⟩, ht⟩ :=
      exists_monotone_Icc_subset_open_cover_unitInterval
        (c := c) (fun b => by
          cases b
          · exact hVo.preimage γ.continuous
          · exact hUo.preimage γ.continuous)
        (by
          intro s _
          rcases hmem (γ s) with hs | hs
          · exact mem_iUnion.mpr ⟨true, hs⟩
          · exact mem_iUnion.mpr ⟨false, hs⟩)
    let seg (a b : I) : Path (γ a) (γ b) := (intervalSegment a b).map γ.continuous
    have hcomp (a b d : I) : ((seg a b).trans (seg b d)).Homotopic (seg a d) := by
      have : ContractibleSpace I := (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0, by simp⟩
      simpa only [seg, ← Path.map_trans] using
        (SimplyConnectedSpace.paths_homotopic
          ((intervalSegment a b).trans (intervalSegment b d)) (intervalSegment a d)).map γ
    have hInd (n : ℕ) : ((δ (γ 0)).trans (seg 0 (t n))).Homotopic (δ (γ (t n))) := by
      induction n with
      | zero =>
        apply (congrArg (fun s => ((δ (γ 0)).trans (seg 0 s)).Homotopic (δ (γ s))) ht0).mpr
        have hr : seg 0 0 = Path.refl (γ 0) := by
          simp only [seg, intervalSegment_self]
          rfl
        rw [hr]
        exact ⟨Path.Homotopy.transRefl _⟩
      | succ n ih =>
        have hs : ((δ (γ (t n))).trans (seg (t n) (t (n + 1)))).Homotopic
            (δ (γ (t (n + 1)))) := by
          apply hstep
          obtain ⟨b, hb⟩ := ht n
          cases b
          · exact Or.inr (fun s => hb (intervalSegment_mem (hmono n.le_succ) s))
          · exact Or.inl (fun s => hb (intervalSegment_mem (hmono n.le_succ) s))
        exact ((Path.Homotopic.refl _).hcomp (hcomp 0 (t n) (t (n + 1))).symm).trans <|
          (Path.Homotopic.symm ⟨Path.Homotopy.transAssoc _ _ _⟩).trans <|
            (ih.hcomp (.refl _)).trans hs
    exact (congrArg (fun s => ((δ (γ 0)).trans (seg 0 s)).Homotopic (δ (γ s)))
      (hN N le_rfl)).mp (hInd N)
  have hPC : PathConnectedSpace X := by
    rw [pathConnectedSpace_iff_univ]
    rw [← hcover]
    exact hU.isPathConnected.union hV.isPathConnected ⟨o, hoU, hoV⟩
  rw [simply_connected_iff_paths_homotopic']
  refine ⟨hPC, fun {x y} p q => ?_⟩
  have hcast (r : Path x y) :
      (((intervalSegment 0 1).map r.continuous).cast r.source.symm r.target.symm) = r := by
    ext t
    change r (intervalSegment 0 1 t) = r t
    congr 1
    exact Subtype.ext (by simp [intervalSegment])
  have hδcast (z w : X) (h : w = z) : (δ z).cast rfl h = δ w := by
    subst w
    rfl
  have hp' : ((δ x).trans p).Homotopic (δ y) := by
    have hh := (hpath p.toContinuousMap).pathCast rfl p.target.symm
    rw [Path.cast_trans _ _ rfl p.source.symm p.target.symm, hcast p] at hh
    have hl := hδcast _ _ p.source.symm
    have hr := hδcast _ _ p.target.symm
    exact (congrArg₂ (fun l r => (l.trans p).Homotopic r) hl hr).mp hh
  have hq' : ((δ x).trans q).Homotopic (δ y) := by
    have hh := (hpath q.toContinuousMap).pathCast rfl q.target.symm
    rw [Path.cast_trans _ _ rfl q.source.symm q.target.symm, hcast q] at hh
    have hl := hδcast _ _ q.source.symm
    have hr := hδcast _ _ q.target.symm
    exact (congrArg₂ (fun l r => (l.trans q).Homotopic r) hl hr).mp hh
  open Path.Homotopic.Quotient in
  have heq : trans ⟦δ x⟧ ⟦p⟧ = trans ⟦δ x⟧ ⟦q⟧ := Quotient.sound (hp'.trans hq'.symm)
  open Path.Homotopic.Quotient in
  exact Path.Homotopic.Quotient.exact (by
    have := congrArg (Path.Homotopic.Quotient.trans (symm ⟦δ x⟧)) heq
    simpa [← trans_assoc] using this)

theorem isSimplyConnected_union_of_isOpen {U V : Set X}
    (hUo : IsOpen U) (hVo : IsOpen V)
    (hU : IsSimplyConnected U) (hV : IsSimplyConnected V)
    (hUV : IsPathConnected (U ∩ V)) : IsSimplyConnected (U ∪ V) := by
  let f : (U ∪ V : Set X) → X := Subtype.val
  have he (s : Set X) (hs : s ⊆ U ∪ V) :
      Nonempty ((f ⁻¹' s) ≃ₜ s) :=
    ⟨_root_.Topology.IsEmbedding.subtypeVal.homeomorphOfSubsetRange (fun x hx => ⟨⟨x, hs hx⟩, rfl⟩)⟩
  have hsc (s : Set X) (hs : s ⊆ U ∪ V) (h : IsSimplyConnected s) :
      IsSimplyConnected (f ⁻¹' s) := by
    have : SimplyConnectedSpace s := h
    exact (he s hs).some.toHomotopyEquiv.simplyConnectedSpace
  apply simplyConnectedSpace_of_open_cover (U := f ⁻¹' U) (V := f ⁻¹' V)
    (hUo.preimage continuous_subtype_val) (hVo.preimage continuous_subtype_val)
  · ext x
    exact iff_true_intro x.property
  · exact hsc U subset_union_left hU
  · exact hsc V subset_union_right hV
  · rw [← preimage_inter]
    have : PathConnectedSpace (U ∩ V : Set X) :=
      isPathConnected_iff_pathConnectedSpace.mp hUV
    have := (he (U ∩ V) (inter_subset_left.trans subset_union_left)).some.symm.pathConnectedSpace
    exact isPathConnected_iff_pathConnectedSpace.mpr this

end DifferentialGeometry.Topology
