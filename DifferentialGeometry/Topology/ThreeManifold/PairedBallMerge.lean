import DifferentialGeometry.Topology.ThreeManifold.PairedBallGluing
import DifferentialGeometry.Topology.Homeomorph.QuotientDescent
import DifferentialGeometry.Topology.Homeomorph.Sigma

set_option autoImplicit false
noncomputable section

open Set Metric

namespace DifferentialGeometry.Topology.PairedBallGluing

universe u v w
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

variable {V : Type v} {E : Type w}
  (N : V → ConnectedClosedOrientedManifold.{u} 3)
  (endpoint : E → Bool → V)
  (chart : (e : E) → (b : Bool) →
    OrientedBallChart (N (endpoint e b)).toClosedOrientedManifold)
  (s : E) (a : BoundaryAttachment)

private abbrev RemainingVertex := {v // v ≠ endpoint s false ∧ v ≠ endpoint s true}

def mergeFactor : Option (RemainingVertex endpoint s) → ConnectedClosedOrientedManifold.{u} 3
  | none => (smoothConnectedSum (N (endpoint s false)) (N (endpoint s true))
      (chart s false) (chart s true) a).toConnectedClosedOrientedManifold
  | some v => N v.val

def mergeVertex (v : V) : Option (RemainingVertex endpoint s) := by
  classical
  exact if hi : v = endpoint s false then none
  else if hj : v = endpoint s true then none
  else some ⟨v, hi, hj⟩

@[simp] theorem mergeVertex_left : mergeVertex endpoint s (endpoint s false) = none := by
  simp [mergeVertex]

@[simp] theorem mergeVertex_right : mergeVertex endpoint s (endpoint s true) = none := by
  simp [mergeVertex]

@[simp] theorem mergeVertex_remaining (v : RemainingVertex endpoint s) :
    mergeVertex endpoint s v.val = some v := by
  simp [mergeVertex, v.property.1, v.property.2]

def mergeFlag
    (b : ({p : E × Bool // p.1 ≠ s ∧ endpoint p.1 p.2 = endpoint s false} ⊕
      {p : E × Bool // p.1 ≠ s ∧ endpoint p.1 p.2 = endpoint s true}) →
      OrientedBallChart (mergeFactor N endpoint chart s a none).toClosedOrientedManifold)
    (e : {e // e ≠ s}) (t : Bool) :
    Σ v, OrientedBallChart (mergeFactor N endpoint chart s a v).toClosedOrientedManifold := by
  classical
  exact if hi : endpoint e.val t = endpoint s false then
    ⟨none, b (Sum.inl ⟨(e.val, t), e.property, hi⟩)⟩
  else if hj : endpoint e.val t = endpoint s true then
    ⟨none, b (Sum.inr ⟨(e.val, t), e.property, hj⟩)⟩
  else ⟨some ⟨endpoint e.val t, hi, hj⟩, chart e.val t⟩

theorem mergeFlag_flagMap_left
    (b : ({p : E × Bool // p.1 ≠ s ∧ endpoint p.1 p.2 = endpoint s false} ⊕
      {p : E × Bool // p.1 ≠ s ∧ endpoint p.1 p.2 = endpoint s true}) →
      OrientedBallChart (mergeFactor N endpoint chart s a none).toClosedOrientedManifold)
    (e : {e // e ≠ s}) (t : Bool) (hi : endpoint e.val t = endpoint s false) (x : E3) :
    flagMap (mergeFactor N endpoint chart s a)
        (fun e t => (mergeFlag N endpoint chart s a b e t).fst)
        (fun e t => (mergeFlag N endpoint chart s a b e t).snd) (e, t) x =
      ⟨none, (b (Sum.inl ⟨(e.val, t), e.property, hi⟩)).chart x⟩ := by
  classical
  have h : mergeFlag N endpoint chart s a b e t =
      ⟨none, b (Sum.inl ⟨(e.val, t), e.property, hi⟩)⟩ := by
    unfold mergeFlag
    rw [dite_eq_left hi]
  exact congrArg (fun p : Σ v, OrientedBallChart
    (mergeFactor N endpoint chart s a v).toClosedOrientedManifold =>
      (⟨p.fst, p.snd.chart x⟩ : Σ v, (mergeFactor N endpoint chart s a v).Carrier)) h

theorem mergeFlag_flagMap_right
    (b : ({p : E × Bool // p.1 ≠ s ∧ endpoint p.1 p.2 = endpoint s false} ⊕
      {p : E × Bool // p.1 ≠ s ∧ endpoint p.1 p.2 = endpoint s true}) →
      OrientedBallChart (mergeFactor N endpoint chart s a none).toClosedOrientedManifold)
    (e : {e // e ≠ s}) (t : Bool) (hi : endpoint e.val t ≠ endpoint s false)
    (hj : endpoint e.val t = endpoint s true) (x : E3) :
    flagMap (mergeFactor N endpoint chart s a)
        (fun e t => (mergeFlag N endpoint chart s a b e t).fst)
        (fun e t => (mergeFlag N endpoint chart s a b e t).snd) (e, t) x =
      ⟨none, (b (Sum.inr ⟨(e.val, t), e.property, hj⟩)).chart x⟩ := by
  classical
  have h : mergeFlag N endpoint chart s a b e t =
      ⟨none, b (Sum.inr ⟨(e.val, t), e.property, hj⟩)⟩ := by
    unfold mergeFlag
    rw [dite_eq_right hi, dite_eq_left hj]
  exact congrArg (fun p : Σ v, OrientedBallChart
    (mergeFactor N endpoint chart s a v).toClosedOrientedManifold =>
      (⟨p.fst, p.snd.chart x⟩ : Σ v, (mergeFactor N endpoint chart s a v).Carrier)) h

theorem mergeFlag_flagMap_remaining
    (b : ({p : E × Bool // p.1 ≠ s ∧ endpoint p.1 p.2 = endpoint s false} ⊕
      {p : E × Bool // p.1 ≠ s ∧ endpoint p.1 p.2 = endpoint s true}) →
      OrientedBallChart (mergeFactor N endpoint chart s a none).toClosedOrientedManifold)
    (e : {e // e ≠ s}) (t : Bool)
    (hi : endpoint e.val t ≠ endpoint s false) (hj : endpoint e.val t ≠ endpoint s true)
    (x : E3) :
    flagMap (mergeFactor N endpoint chart s a)
        (fun e t => (mergeFlag N endpoint chart s a b e t).fst)
        (fun e t => (mergeFlag N endpoint chart s a b e t).snd) (e, t) x =
      ⟨some ⟨endpoint e.val t, hi, hj⟩, (chart e.val t).chart x⟩ := by
  classical
  have h : mergeFlag N endpoint chart s a b e t =
      ⟨some ⟨endpoint e.val t, hi, hj⟩, chart e.val t⟩ := by
    unfold mergeFlag
    rw [dite_eq_right hi, dite_eq_right hj]
  exact congrArg (fun p : Σ v, OrientedBallChart
    (mergeFactor N endpoint chart s a v).toClosedOrientedManifold =>
      (⟨p.fst, p.snd.chart x⟩ : Σ v, (mergeFactor N endpoint chart s a v).Carrier)) h

theorem mergeFlag_fst
    (b : ({p : E × Bool // p.1 ≠ s ∧ endpoint p.1 p.2 = endpoint s false} ⊕
      {p : E × Bool // p.1 ≠ s ∧ endpoint p.1 p.2 = endpoint s true}) →
      OrientedBallChart (mergeFactor N endpoint chart s a none).toClosedOrientedManifold)
    (e : {e // e ≠ s}) (t : Bool) :
    (mergeFlag N endpoint chart s a b e t).fst =
      mergeVertex endpoint s (endpoint e.val t) := by
  classical
  unfold mergeFlag mergeVertex
  split_ifs <;> rfl

theorem pairwise_disjoint_mergeFlag_image
    (b : ({p : E × Bool // p.1 ≠ s ∧ endpoint p.1 p.2 = endpoint s false} ⊕
      {p : E × Bool // p.1 ≠ s ∧ endpoint p.1 p.2 = endpoint s true}) →
      OrientedBallChart (mergeFactor N endpoint chart s a none).toClosedOrientedManifold)
    (hdisj : Pairwise fun p q =>
      Disjoint (flagMap N endpoint chart p '' closedBall (0 : E3) 2)
        (flagMap N endpoint chart q '' closedBall (0 : E3) 2))
    (hb : Pairwise fun p q => Disjoint ((b p).chart '' closedBall (0 : E3) 2)
      ((b q).chart '' closedBall (0 : E3) 2)) :
    Pairwise fun p q : {e // e ≠ s} × Bool =>
      Disjoint (flagMap (mergeFactor N endpoint chart s a)
        (fun e t => (mergeFlag N endpoint chart s a b e t).fst)
        (fun e t => (mergeFlag N endpoint chart s a b e t).snd) p '' closedBall (0 : E3) 2)
      (flagMap (mergeFactor N endpoint chart s a)
        (fun e t => (mergeFlag N endpoint chart s a b e t).fst)
        (fun e t => (mergeFlag N endpoint chart s a b e t).snd) q '' closedBall (0 : E3) 2) := by
  classical
  let O := {e // e ≠ s} × Bool
  let J := {p : E × Bool // p.1 ≠ s ∧ endpoint p.1 p.2 = endpoint s false} ⊕
    {p : E × Bool // p.1 ≠ s ∧ endpoint p.1 p.2 = endpoint s true}
  let original : O → E × Bool := fun p => (p.1.val, p.2)
  have horiginal : Function.Injective original := by
    intro p q h
    exact Prod.ext (Subtype.ext (congrArg Prod.fst h)) (congrArg (fun p : E × Bool => p.2) h)
  let oldIndex : J → E × Bool := Sum.elim Subtype.val Subtype.val
  let F := flagMap (mergeFactor N endpoint chart s a)
    (fun e t => (mergeFlag N endpoint chart s a b e t).fst)
    (fun e t => (mergeFlag N endpoint chart s a b e t).snd)
  let P : (Σ v, (mergeFactor N endpoint chart s a v).Carrier) →
      (mergeFactor N endpoint chart s a none).Carrier ⊕ (Σ v, (N v).Carrier) :=
    fun q => match q with
      | ⟨none, x⟩ => Sum.inl x
      | ⟨some v, x⟩ => Sum.inr ⟨v.val, x⟩
  have hclass (p : O) (x : E3) :
      (∃ j : J, oldIndex j = original p ∧ P (F p x) = Sum.inl ((b j).chart x)) ∨
      P (F p x) = Sum.inr (flagMap N endpoint chart (original p) x) := by
    by_cases hi : endpoint p.1.val p.2 = endpoint s false
    · refine Or.inl ⟨Sum.inl ⟨original p, p.1.property, hi⟩, rfl, ?_⟩
      rw [show F p x = _ from mergeFlag_flagMap_left N endpoint chart s a b p.1 p.2 hi x]
    · by_cases hj : endpoint p.1.val p.2 = endpoint s true
      · refine Or.inl ⟨Sum.inr ⟨original p, p.1.property, hj⟩, rfl, ?_⟩
        rw [show F p x = _ from
          mergeFlag_flagMap_right N endpoint chart s a b p.1 p.2 hi hj x]
      · refine Or.inr ?_
        rw [show F p x = _ from
          mergeFlag_flagMap_remaining N endpoint chart s a b p.1 p.2 hi hj x]
        rfl
  intro p q hpq
  rw [disjoint_left]
  rintro z ⟨x, hx, hxz⟩ ⟨y, hy, hyz⟩
  have hxy : P (F p x) = P (F q y) := congrArg P (hxz.trans hyz.symm)
  rcases hclass p x with ⟨i, hi, hix⟩ | hix <;>
    rcases hclass q y with ⟨j, hj, hjy⟩ | hjy
  · have hv : (b i).chart x = (b j).chart y := Sum.inl.inj (hix.symm.trans (hxy.trans hjy))
    have hij : i ≠ j := fun h => hpq (horiginal (hi.symm.trans ((congrArg oldIndex h).trans hj)))
    exact disjoint_left.mp (hb hij) ⟨x, hx, hv⟩ ⟨y, hy, rfl⟩
  · exact Sum.inl_ne_inr (hix.symm.trans (hxy.trans hjy))
  · exact Sum.inr_ne_inl (hix.symm.trans (hxy.trans hjy))
  · have hv := Sum.inr.inj (hix.symm.trans (hxy.trans hjy))
    exact disjoint_left.mp (hdisj (fun h => hpq (horiginal h))) ⟨x, hx, hv⟩ ⟨y, hy, rfl⟩

theorem mergeFlag_holes_none
    (b : ({p : E × Bool // p.1 ≠ s ∧ endpoint p.1 p.2 = endpoint s false} ⊕
      {p : E × Bool // p.1 ≠ s ∧ endpoint p.1 p.2 = endpoint s true}) →
      OrientedBallChart (mergeFactor N endpoint chart s a none).toClosedOrientedManifold)
    (hends : endpoint s false ≠ endpoint s true) (S : Set E3) :
    (fun x : (mergeFactor N endpoint chart s a none).Carrier =>
      (⟨none, x⟩ : Σ v, (mergeFactor N endpoint chart s a v).Carrier)) ⁻¹'
      (⋃ p, flagMap (mergeFactor N endpoint chart s a)
        (fun e t => (mergeFlag N endpoint chart s a b e t).fst)
        (fun e t => (mergeFlag N endpoint chart s a b e t).snd) p '' S) =
      ⋃ p, (b p).chart '' S := by
  classical
  let F := flagMap (mergeFactor N endpoint chart s a)
    (fun e t => (mergeFlag N endpoint chart s a b e t).fst)
    (fun e t => (mergeFlag N endpoint chart s a b e t).snd)
  have hinj : Function.Injective (fun x : (mergeFactor N endpoint chart s a none).Carrier =>
      (⟨none, x⟩ : Σ v, (mergeFactor N endpoint chart s a v).Carrier)) := by
    intro x y h
    cases h
    rfl
  ext x
  constructor
  · intro hx
    obtain ⟨⟨e, t⟩, y, hy, hyx⟩ := mem_iUnion.mp hx
    change F (e, t) y = _ at hyx
    by_cases hi : endpoint e.val t = endpoint s false
    · have hf := mergeFlag_flagMap_left N endpoint chart s a b e t hi y
      exact mem_iUnion.mpr ⟨Sum.inl ⟨(e.val, t), e.property, hi⟩, y, hy,
        hinj (hf.symm.trans hyx)⟩
    · by_cases hj : endpoint e.val t = endpoint s true
      · have hf := mergeFlag_flagMap_right N endpoint chart s a b e t hi hj y
        exact mem_iUnion.mpr ⟨Sum.inr ⟨(e.val, t), e.property, hj⟩, y, hy,
          hinj (hf.symm.trans hyx)⟩
      · have hf := mergeFlag_flagMap_remaining N endpoint chart s a b e t hi hj y
        have hh := congrArg Sigma.fst (hf.symm.trans hyx)
        exact (Option.some_ne_none _ hh).elim
  · intro hx
    obtain ⟨p, y, hy, hyx⟩ := mem_iUnion.mp hx
    rcases p with p | p
    · refine mem_iUnion.mpr ⟨(⟨p.val.1, p.property.1⟩, p.val.2), y, hy, ?_⟩
      exact (mergeFlag_flagMap_left N endpoint chart s a b
        ⟨p.val.1, p.property.1⟩ p.val.2 p.property.2 y).trans
        (congrArg (fun x : (mergeFactor N endpoint chart s a none).Carrier =>
          (⟨none, x⟩ : Σ v, (mergeFactor N endpoint chart s a v).Carrier)) hyx)
    · refine mem_iUnion.mpr ⟨(⟨p.val.1, p.property.1⟩, p.val.2), y, hy, ?_⟩
      exact (mergeFlag_flagMap_right N endpoint chart s a b
        ⟨p.val.1, p.property.1⟩ p.val.2
        (fun h => hends (h.symm.trans p.property.2)) p.property.2 y).trans
        (congrArg (fun x : (mergeFactor N endpoint chart s a none).Carrier =>
          (⟨none, x⟩ : Σ v, (mergeFactor N endpoint chart s a v).Carrier)) hyx)

private theorem sigma_some_eq_of_eq (v v' : RemainingVertex endpoint s)
    (x : (N v.val).Carrier) (y : (N v'.val).Carrier)
    (h : (⟨v.val, x⟩ : Σ v, (N v).Carrier) = ⟨v'.val, y⟩) :
    (⟨some v, x⟩ : Σ v, (mergeFactor N endpoint chart s a v).Carrier) = ⟨some v', y⟩ := by
  have hv : v = v' := Subtype.ext (congrArg Sigma.fst h)
  subst v'
  have hinj : Function.Injective (fun x : (N v.val).Carrier =>
      (⟨v.val, x⟩ : Σ v, (N v).Carrier)) := by
    intro x y h
    cases h
    rfl
  rw [hinj h]

theorem mergeFlag_holes_some
    (b : ({p : E × Bool // p.1 ≠ s ∧ endpoint p.1 p.2 = endpoint s false} ⊕
      {p : E × Bool // p.1 ≠ s ∧ endpoint p.1 p.2 = endpoint s true}) →
      OrientedBallChart (mergeFactor N endpoint chart s a none).toClosedOrientedManifold)
    (v : RemainingVertex endpoint s) (S : Set E3) :
    (fun x : (N v.val).Carrier =>
      (⟨some v, x⟩ : Σ v, (mergeFactor N endpoint chart s a v).Carrier)) ⁻¹'
      (⋃ p, flagMap (mergeFactor N endpoint chart s a)
        (fun e t => (mergeFlag N endpoint chart s a b e t).fst)
        (fun e t => (mergeFlag N endpoint chart s a b e t).snd) p '' S) =
      (fun x : (N v.val).Carrier => (⟨v.val, x⟩ : Σ v, (N v).Carrier)) ⁻¹'
        (⋃ p, flagMap N endpoint chart p '' S) := by
  classical
  let F := flagMap (mergeFactor N endpoint chart s a)
    (fun e t => (mergeFlag N endpoint chart s a b e t).fst)
    (fun e t => (mergeFlag N endpoint chart s a b e t).snd)
  let P : (Σ v, (mergeFactor N endpoint chart s a v).Carrier) →
      (mergeFactor N endpoint chart s a none).Carrier ⊕ (Σ v, (N v).Carrier) :=
    fun q => match q with
      | ⟨none, x⟩ => Sum.inl x
      | ⟨some v, x⟩ => Sum.inr ⟨v.val, x⟩
  ext x
  constructor
  · intro hx
    obtain ⟨⟨e, t⟩, y, hy, hyx⟩ := mem_iUnion.mp hx
    change F (e, t) y = _ at hyx
    by_cases hi : endpoint e.val t = endpoint s false
    · have hf := mergeFlag_flagMap_left N endpoint chart s a b e t hi y
      have hh := congrArg Sigma.fst (hf.symm.trans hyx)
      exact (Option.some_ne_none _ hh.symm).elim
    · by_cases hj : endpoint e.val t = endpoint s true
      · have hf := mergeFlag_flagMap_right N endpoint chart s a b e t hi hj y
        have hh := congrArg Sigma.fst (hf.symm.trans hyx)
        exact (Option.some_ne_none _ hh.symm).elim
      · have hf := mergeFlag_flagMap_remaining N endpoint chart s a b e t hi hj y
        have hh := congrArg P (hf.symm.trans hyx)
        exact mem_iUnion.mpr ⟨(e.val, t), y, hy, Sum.inr.inj hh⟩
  · intro hx
    obtain ⟨p, y, hy, hyx⟩ := mem_iUnion.mp hx
    have hpv : endpoint p.1 p.2 = v.val := congrArg Sigma.fst hyx
    have hi : endpoint p.1 p.2 ≠ endpoint s false := fun h => v.property.1 (hpv.symm.trans h)
    have hj : endpoint p.1 p.2 ≠ endpoint s true := fun h => v.property.2 (hpv.symm.trans h)
    have hps : p.1 ≠ s := by
      intro h
      obtain ⟨e, t⟩ := p
      dsimp at h hi hj
      subst e
      cases t
      · exact hi rfl
      · exact hj rfl
    refine mem_iUnion.mpr ⟨(⟨p.1, hps⟩, p.2), y, hy, ?_⟩
    exact (mergeFlag_flagMap_remaining N endpoint chart s a b ⟨p.1, hps⟩ p.2 hi hj y).trans
      (sigma_some_eq_of_eq N endpoint chart s a ⟨endpoint p.1 p.2, hi, hj⟩ v
        ((chart p.1 p.2).chart y) x hyx)

def mergePuncturedFactorHomeomorph
    (b : ({p : E × Bool // p.1 ≠ s ∧ endpoint p.1 p.2 = endpoint s false} ⊕
      {p : E × Bool // p.1 ≠ s ∧ endpoint p.1 p.2 = endpoint s true}) →
      OrientedBallChart (mergeFactor N endpoint chart s a none).toClosedOrientedManifold)
    (hends : endpoint s false ≠ endpoint s true) :
    (Σ v, PuncturedFactor (mergeFactor N endpoint chart s a)
      (fun e t => (mergeFlag N endpoint chart s a b e t).fst)
      (fun e t => (mergeFlag N endpoint chart s a b e t).snd) v) ≃ₜ
      {q : (mergeFactor N endpoint chart s a none).Carrier //
        q ∉ ⋃ p, (b p).chart '' ball (0 : E3) 1} ⊕
      (Σ v : RemainingVertex endpoint s, PuncturedFactor N endpoint chart v.val) := by
  let N' := mergeFactor N endpoint chart s a
  let ep' := fun e t => (mergeFlag N endpoint chart s a b e t).fst
  let ch' := fun e t => (mergeFlag N endpoint chart s a b e t).snd
  let X := PuncturedFactor N' ep' ch'
  let Y : Option (RemainingVertex endpoint s) → Type u := fun v =>
    match v with
    | none => {q : (N' none).Carrier // q ∉ ⋃ p, (b p).chart '' ball (0 : E3) 1}
    | some v => PuncturedFactor N endpoint chart v.val
  letI : ∀ v, TopologicalSpace (Y v) := fun v => by
    cases v <;> dsimp [Y] <;> infer_instance
  let h : ∀ v, X v ≃ₜ Y v := fun v => by
    cases v with
    | none =>
      apply Homeomorph.setCongr
      ext x
      exact not_congr (Set.ext_iff.mp
        (mergeFlag_holes_none N endpoint chart s a b hends (ball (0 : E3) 1)) x)
    | some v =>
      apply Homeomorph.setCongr
      ext x
      exact not_congr (Set.ext_iff.mp
        (mergeFlag_holes_some N endpoint chart s a b v (ball (0 : E3) 1)) x)
  exact (Homeomorph.sigmaCongrRight h).trans (Homeomorph.sigmaOption Y)

theorem mergePuncturedFactorHomeomorph_none
    (b : ({p : E × Bool // p.1 ≠ s ∧ endpoint p.1 p.2 = endpoint s false} ⊕
      {p : E × Bool // p.1 ≠ s ∧ endpoint p.1 p.2 = endpoint s true}) →
      OrientedBallChart (mergeFactor N endpoint chart s a none).toClosedOrientedManifold)
    (hends : endpoint s false ≠ endpoint s true)
    (x : PuncturedFactor (mergeFactor N endpoint chart s a)
      (fun e t => (mergeFlag N endpoint chart s a b e t).fst)
      (fun e t => (mergeFlag N endpoint chart s a b e t).snd) none)
    (hx : x.val ∉ ⋃ p, (b p).chart '' ball (0 : E3) 1) :
    mergePuncturedFactorHomeomorph N endpoint chart s a b hends ⟨none, x⟩ =
      Sum.inl ⟨x.val, hx⟩ := rfl

theorem mergePuncturedFactorHomeomorph_some
    (b : ({p : E × Bool // p.1 ≠ s ∧ endpoint p.1 p.2 = endpoint s false} ⊕
      {p : E × Bool // p.1 ≠ s ∧ endpoint p.1 p.2 = endpoint s true}) →
      OrientedBallChart (mergeFactor N endpoint chart s a none).toClosedOrientedManifold)
    (hends : endpoint s false ≠ endpoint s true) (v : RemainingVertex endpoint s)
    (x : PuncturedFactor (mergeFactor N endpoint chart s a)
      (fun e t => (mergeFlag N endpoint chart s a b e t).fst)
      (fun e t => (mergeFlag N endpoint chart s a b e t).snd) (some v))
    (hx : (⟨v.val, x.val⟩ : Σ v, (N v).Carrier) ∉
      ⋃ p, flagMap N endpoint chart p '' ball (0 : E3) 1) :
    mergePuncturedFactorHomeomorph N endpoint chart s a b hends ⟨some v, x⟩ =
      Sum.inr ⟨v, ⟨x.val, hx⟩⟩ := rfl


private abbrev RVertex := {v // v ≠ endpoint s false ∧ v ≠ endpoint s true}
private abbrev LFlag := {p : E × Bool // p.1 ≠ s ∧ endpoint p.1 p.2 = endpoint s false}
private abbrev RFlag := {p : E × Bool // p.1 ≠ s ∧ endpoint p.1 p.2 = endpoint s true}

private def mergeSplitVal
    (b : LFlag endpoint s ⊕ RFlag endpoint s →
      OrientedBallChart (mergeFactor N endpoint chart s a none).toClosedOrientedManifold) :
    ({x : (mergeFactor N endpoint chart s a none).Carrier //
        x ∉ ⋃ p, (b p).chart '' ball (0 : E3) 1} ⊕
      (Σ v : RVertex endpoint s, PuncturedFactor N endpoint chart v.val)) →
        (mergeFactor N endpoint chart s a none).Carrier ⊕ (Σ v, (N v).Carrier) :=
  Sum.elim (fun x => Sum.inl x.val) (fun p => Sum.inr ⟨p.fst.val, p.snd.val⟩)

private theorem mergeSplitVal_injective
    (b : LFlag endpoint s ⊕ RFlag endpoint s →
      OrientedBallChart (mergeFactor N endpoint chart s a none).toClosedOrientedManifold) :
    Function.Injective (mergeSplitVal N endpoint chart s a b) := by
  rintro (x | ⟨v, x⟩) (y | ⟨w, y⟩) h
  · exact congrArg Sum.inl (Subtype.ext (Sum.inl.inj h))
  · exact (Sum.inl_ne_inr h).elim
  · exact (Sum.inr_ne_inl h).elim
  · have hval := Sum.inr.inj h
    have hv : v = w := Subtype.ext (congrArg Sigma.fst hval)
    subst w
    have hinj : Function.Injective (fun x : (N v.val).Carrier =>
        (⟨v.val, x⟩ : Σ v, (N v).Carrier)) := by
      intro x y h
      cases h
      rfl
    have hxy : x = y := Subtype.ext (hinj hval)
    subst y
    rfl

private def mergeAmbientSplit :
    (Σ v, (mergeFactor N endpoint chart s a v).Carrier) →
      (mergeFactor N endpoint chart s a none).Carrier ⊕ (Σ v, (N v).Carrier)
  | ⟨none, x⟩ => Sum.inl x
  | ⟨some v, x⟩ => Sum.inr ⟨v.val, x⟩

private theorem mergePuncturedFactorHomeomorph_val
    (b : LFlag endpoint s ⊕ RFlag endpoint s →
      OrientedBallChart (mergeFactor N endpoint chart s a none).toClosedOrientedManifold)
    (hends : endpoint s false ≠ endpoint s true)
    (x : Σ v, PuncturedFactor (mergeFactor N endpoint chart s a)
      (fun e t => (mergeFlag N endpoint chart s a b e t).fst)
      (fun e t => (mergeFlag N endpoint chart s a b e t).snd) v) :
    mergeSplitVal N endpoint chart s a b
      (mergePuncturedFactorHomeomorph N endpoint chart s a b hends x) =
        mergeAmbientSplit N endpoint chart s a ⟨x.fst, x.snd.val⟩ := by
  obtain ⟨v, x⟩ := x
  cases v <;> rfl

theorem exists_merge_homeomorph
    (hdisj : Pairwise fun p q =>
      Disjoint (flagMap N endpoint chart p '' closedBall (0 : E3) 2)
        (flagMap N endpoint chart q '' closedBall (0 : E3) 2))
    (hends : endpoint s false ≠ endpoint s true) :
    ∃ b : LFlag endpoint s ⊕ RFlag endpoint s →
      OrientedBallChart (mergeFactor N endpoint chart s a none).toClosedOrientedManifold,
      (∀ p x, x ∈ closedBall (0 : E3) 2 →
        ∃ hx : (remainingIncidenceChart N endpoint chart s (endpoint s false) p).chart x ∉
            (chart s false).chart '' ball (0 : E3) 1,
          (b (Sum.inl p)).chart x = ConnectedSumQuotient.inl
            (chart s false).toBallChart (chart s true).toBallChart a.1.toHomeomorph
            ⟨(remainingIncidenceChart N endpoint chart s (endpoint s false) p).chart x, hx⟩) ∧
      (∀ p x, x ∈ closedBall (0 : E3) 2 →
        ∃ hx : (remainingIncidenceChart N endpoint chart s (endpoint s true) p).chart x ∉
            (chart s true).chart '' ball (0 : E3) 1,
          (b (Sum.inr p)).chart x = ConnectedSumQuotient.inr
            (chart s false).toBallChart (chart s true).toBallChart a.1.toHomeomorph
            ⟨(remainingIncidenceChart N endpoint chart s (endpoint s true) p).chart x, hx⟩) ∧
      ∃ hb : Pairwise fun p q =>
        Disjoint (flagMap (mergeFactor N endpoint chart s a)
          (fun e t => (mergeFlag N endpoint chart s a b e t).fst)
          (fun e t => (mergeFlag N endpoint chart s a b e t).snd) p '' closedBall (0 : E3) 2)
        (flagMap (mergeFactor N endpoint chart s a)
          (fun e t => (mergeFlag N endpoint chart s a b e t).fst)
          (fun e t => (mergeFlag N endpoint chart s a b e t).snd) q '' closedBall (0 : E3) 2),
        ∃ H : Quot (seamRel N endpoint chart hdisj s a) ≃ₜ
          (Σ v, PuncturedFactor (mergeFactor N endpoint chart s a)
            (fun e t => (mergeFlag N endpoint chart s a b e t).fst)
            (fun e t => (mergeFlag N endpoint chart s a b e t).snd) v),
          (∀ x : PuncturedFactor N endpoint chart (endpoint s false),
            ∃ y, mergePuncturedFactorHomeomorph N endpoint chart s a b hends
                (H (Quot.mk _ ⟨endpoint s false, x⟩)) = Sum.inl y ∧
              y.val = ConnectedSumQuotient.inl (chart s false).toBallChart
                (chart s true).toBallChart a.1.toHomeomorph
                (selectedPuncturedFactorHomeomorph N endpoint chart s false hends x).val) ∧
          (∀ x : PuncturedFactor N endpoint chart (endpoint s true),
            ∃ y, mergePuncturedFactorHomeomorph N endpoint chart s a b hends
                (H (Quot.mk _ ⟨endpoint s true, x⟩)) = Sum.inl y ∧
              y.val = ConnectedSumQuotient.inr (chart s false).toBallChart
                (chart s true).toBallChart a.1.toHomeomorph
                (selectedPuncturedFactorHomeomorph N endpoint chart s true hends x).val) ∧
          (∀ (v : {v // v ≠ endpoint s false ∧ v ≠ endpoint s true})
            (x : PuncturedFactor N endpoint chart v.val),
            mergePuncturedFactorHomeomorph N endpoint chart s a b hends
              (H (Quot.mk _ ⟨v.val, x⟩)) = Sum.inr ⟨v, x⟩) ∧
          ∀ (e : {e // e ≠ s}) (t : Bool) (z : sphere (0 : E3) 1),
            H (Quot.mk _ ⟨endpoint e.val t, boundaryPoint N endpoint chart hdisj e.val t z⟩) =
              ⟨(mergeFlag N endpoint chart s a b e t).fst,
                boundaryPoint (mergeFactor N endpoint chart s a)
                  (fun e t => (mergeFlag N endpoint chart s a b e t).fst)
                  (fun e t => (mergeFlag N endpoint chart s a b e t).snd) hb e t z⟩ := by
  classical
  obtain ⟨b, hbL, hbR, hbd, H, hfirst, hsecond, hu, hL, hR⟩ :=
    exists_seam_quotient_homeomorph N endpoint chart hdisj s a hends
  have hb := pairwise_disjoint_mergeFlag_image N endpoint chart s a b hdisj hbd
  let J := mergePuncturedFactorHomeomorph N endpoint chart s a b hends
  let H' := H.trans J.symm
  refine ⟨b, hbL, hbR, hb, H', ?_, ?_, ?_, ?_⟩
  · intro x
    obtain ⟨y, hy, hyval⟩ := hfirst x
    exact ⟨y, (J.apply_symm_apply _).trans hy, hyval⟩
  · intro x
    obtain ⟨y, hy, hyval⟩ := hsecond x
    exact ⟨y, (J.apply_symm_apply _).trans hy, hyval⟩
  · intro v x
    exact (J.apply_symm_apply _).trans (hu v x)
  intro e t z
  apply J.injective
  change J (J.symm (H (Quot.mk _
    ⟨endpoint e.val t, boundaryPoint N endpoint chart hdisj e.val t z⟩))) = _
  refine (J.apply_symm_apply _).trans ?_
  apply mergeSplitVal_injective N endpoint chart s a b
  refine Eq.trans ?_ (mergePuncturedFactorHomeomorph_val N endpoint chart s a b hends _).symm
  change mergeSplitVal N endpoint chart s a b
    (H (Quot.mk _ ⟨endpoint e.val t, boundaryPoint N endpoint chart hdisj e.val t z⟩)) =
      mergeAmbientSplit N endpoint chart s a
        (flagMap (mergeFactor N endpoint chart s a)
          (fun e t => (mergeFlag N endpoint chart s a b e t).fst)
          (fun e t => (mergeFlag N endpoint chart s a b e t).snd) (e, t) z)
  by_cases hi : endpoint e.val t = endpoint s false
  · obtain ⟨y, hy, hyval⟩ := hL ⟨(e.val, t), e.property, hi⟩ z
    rw [hy, mergeFlag_flagMap_left N endpoint chart s a b e t hi z]
    exact congrArg Sum.inl hyval
  · by_cases hj : endpoint e.val t = endpoint s true
    · obtain ⟨y, hy, hyval⟩ := hR ⟨(e.val, t), e.property, hj⟩ z
      rw [hy, mergeFlag_flagMap_right N endpoint chart s a b e t hi hj z]
      exact congrArg Sum.inl hyval
    · rw [hu ⟨endpoint e.val t, hi, hj⟩,
        mergeFlag_flagMap_remaining N endpoint chart s a b e t hi hj z]
      rfl


variable
  (hdisj : Pairwise fun p q =>
    Disjoint (flagMap N endpoint chart p '' closedBall (0 : E3) 2)
      (flagMap N endpoint chart q '' closedBall (0 : E3) 2))
  (attachment : E → BoundaryAttachment)

private theorem map_seamRel_iff
    {V' : Type*} (N' : V' → ConnectedClosedOrientedManifold.{u} 3)
    (endpoint' : {e // e ≠ s} → Bool → V')
    (chart' : (e : {e // e ≠ s}) → (t : Bool) →
      OrientedBallChart (N' (endpoint' e t)).toClosedOrientedManifold)
    (hdisj' : Pairwise fun p q =>
      Disjoint (flagMap N' endpoint' chart' p '' closedBall (0 : E3) 2)
        (flagMap N' endpoint' chart' q '' closedBall (0 : E3) 2))
    (F : (Σ v, PuncturedFactor N endpoint chart v) →
      (Σ v, PuncturedFactor N' endpoint' chart' v))
    (hF : ∀ (e : {e // e ≠ s}) (t : Bool) (z : sphere (0 : E3) 1),
      F ⟨endpoint e.val t, boundaryPoint N endpoint chart hdisj e.val t z⟩ =
        ⟨endpoint' e t, boundaryPoint N' endpoint' chart' hdisj' e t z⟩)
    (e : {e // e ≠ s}) (x y : Σ v, PuncturedFactor N' endpoint' chart' v) :
    Relation.Map (seamRel N endpoint chart hdisj e.val (attachment e.val)) F F x y ↔
      seamRel N' endpoint' chart' hdisj' e (attachment e.val) x y := by
  constructor
  · rintro ⟨p, q, ⟨z, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩, hpx, hqy⟩
    · exact ⟨z, Or.inl ⟨hpx.symm.trans (hF e false z),
        hqy.symm.trans (hF e true ((attachment e.val).1 z))⟩⟩
    · exact ⟨z, Or.inr ⟨hqy.symm.trans (hF e false z),
        hpx.symm.trans (hF e true ((attachment e.val).1 z))⟩⟩
  · rintro ⟨z, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact ⟨_, _, ⟨z, Or.inl ⟨rfl, rfl⟩⟩,
        hF e false z, hF e true ((attachment e.val).1 z)⟩
    · exact ⟨_, _, ⟨z, Or.inr ⟨rfl, rfl⟩⟩,
        hF e true ((attachment e.val).1 z), hF e false z⟩

theorem exists_quotient_homeomorph_merge
    (hends : endpoint s false ≠ endpoint s true) :
    let N' := mergeFactor N endpoint chart s (attachment s)
    ∃ b : ({p : E × Bool // p.1 ≠ s ∧ endpoint p.1 p.2 = endpoint s false} ⊕
        {p : E × Bool // p.1 ≠ s ∧ endpoint p.1 p.2 = endpoint s true}) →
      OrientedBallChart (N' none).toClosedOrientedManifold,
      let endpoint' := fun e t => (mergeFlag N endpoint chart s (attachment s) b e t).fst
      let chart' := fun e t => (mergeFlag N endpoint chart s (attachment s) b e t).snd
      (∀ p x, x ∈ closedBall (0 : E3) 2 →
        ∃ hx : (remainingIncidenceChart N endpoint chart s (endpoint s false) p).chart x ∉
            (chart s false).chart '' ball (0 : E3) 1,
          (b (Sum.inl p)).chart x = ConnectedSumQuotient.inl
            (chart s false).toBallChart (chart s true).toBallChart (attachment s).1.toHomeomorph
            ⟨(remainingIncidenceChart N endpoint chart s (endpoint s false) p).chart x, hx⟩) ∧
      (∀ p x, x ∈ closedBall (0 : E3) 2 →
        ∃ hx : (remainingIncidenceChart N endpoint chart s (endpoint s true) p).chart x ∉
            (chart s true).chart '' ball (0 : E3) 1,
          (b (Sum.inr p)).chart x = ConnectedSumQuotient.inr
            (chart s false).toBallChart (chart s true).toBallChart (attachment s).1.toHomeomorph
            ⟨(remainingIncidenceChart N endpoint chart s (endpoint s true) p).chart x, hx⟩) ∧
      ∃ hb : Pairwise fun p q =>
        Disjoint (flagMap N' endpoint' chart' p '' closedBall (0 : E3) 2)
          (flagMap N' endpoint' chart' q '' closedBall (0 : E3) 2),
        ∃ H : Quot (seamRel N endpoint chart hdisj s (attachment s)) ≃ₜ
          (Σ v, PuncturedFactor N' endpoint' chart' v),
          (∀ x : PuncturedFactor N endpoint chart (endpoint s false),
            ∃ y, mergePuncturedFactorHomeomorph N endpoint chart s (attachment s) b hends
                (H (Quot.mk _ ⟨endpoint s false, x⟩)) = Sum.inl y ∧
              y.val = ConnectedSumQuotient.inl (chart s false).toBallChart
                (chart s true).toBallChart (attachment s).1.toHomeomorph
                (selectedPuncturedFactorHomeomorph N endpoint chart s false hends x).val) ∧
          (∀ x : PuncturedFactor N endpoint chart (endpoint s true),
            ∃ y, mergePuncturedFactorHomeomorph N endpoint chart s (attachment s) b hends
                (H (Quot.mk _ ⟨endpoint s true, x⟩)) = Sum.inl y ∧
              y.val = ConnectedSumQuotient.inr (chart s false).toBallChart
                (chart s true).toBallChart (attachment s).1.toHomeomorph
                (selectedPuncturedFactorHomeomorph N endpoint chart s true hends x).val) ∧
          (∀ (v : {v // v ≠ endpoint s false ∧ v ≠ endpoint s true})
            (x : PuncturedFactor N endpoint chart v.val),
            mergePuncturedFactorHomeomorph N endpoint chart s (attachment s) b hends
              (H (Quot.mk _ ⟨v.val, x⟩)) = Sum.inr ⟨v, x⟩) ∧
          (∀ (e : {e // e ≠ s}) (t : Bool) (z : sphere (0 : E3) 1),
            H (Quot.mk _ ⟨endpoint e.val t, boundaryPoint N endpoint chart hdisj e.val t z⟩) =
              ⟨endpoint' e t, boundaryPoint N' endpoint' chart' hb e t z⟩) ∧
          ∃ J : Quot (fun x y => ∃ e, seamRel N endpoint chart hdisj e (attachment e) x y) ≃ₜ
              Quot (fun x y => ∃ e : {e // e ≠ s},
                seamRel N' endpoint' chart' hb e (attachment e.val) x y),
            ∀ x, J (Quot.mk _ x) = Quot.mk _ (H (Quot.mk _ x)) := by
  dsimp only
  obtain ⟨b, hbL, hbR, hb, H, hfirst, hsecond, hu, hH⟩ :=
    exists_merge_homeomorph N endpoint chart s (attachment s) hdisj hends
  let N' := mergeFactor N endpoint chart s (attachment s)
  let endpoint' := fun e t => (mergeFlag N endpoint chart s (attachment s) b e t).fst
  let chart' := fun e t => (mergeFlag N endpoint chart s (attachment s) b e t).snd
  let r := fun e => seamRel N endpoint chart hdisj e (attachment e)
  let K := Homeomorph.Quot.indexedRelationStep r s H
  have hrel (x y : Σ v, PuncturedFactor N' endpoint' chart' v) :
      (∃ e : {e // e ≠ s}, Relation.Map (r e.val)
        (H ∘ Quot.mk (r s)) (H ∘ Quot.mk (r s)) x y) ↔
      ∃ e : {e // e ≠ s}, seamRel N' endpoint' chart' hb e (attachment e.val) x y := by
    apply exists_congr
    intro e
    exact map_seamRel_iff N endpoint chart s hdisj attachment N' endpoint' chart' hb
      (H ∘ Quot.mk (r s)) hH e x y
  let J := K.trans (Homeomorph.Quot.congrRight hrel)
  exact ⟨b, hbL, hbR, hb, H, hfirst, hsecond, hu, hH, J, fun _ => rfl⟩

end DifferentialGeometry.Topology.PairedBallGluing
