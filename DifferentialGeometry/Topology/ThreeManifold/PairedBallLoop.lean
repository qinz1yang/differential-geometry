import DifferentialGeometry.Topology.ThreeManifold.PairedBallGluing
import DifferentialGeometry.Topology.ThreeManifold.SelfAttachment.FactorBallImage
import DifferentialGeometry.Topology.Homeomorph.Sigma
import DifferentialGeometry.Topology.Homeomorph.QuotientDescent

set_option autoImplicit false
noncomputable section
open Set Metric

section

namespace DifferentialGeometry.Topology.PairedBallGluing

universe u v w
private abbrev E3 := EuclideanSpace ℝ (Fin 3)
variable {V : Type v} {E : Type w}
  (N : V → ConnectedClosedOrientedManifold.{u} 3)
  (endpoint : E → Bool → V)
  (chart : (e : E) → (b : Bool) →
    OrientedBallChart (N (endpoint e b)).toClosedOrientedManifold)
  (s : E) (hloop : endpoint s true = endpoint s false)

def loopSecondChart : OrientedBallChart (N (endpoint s false)).toClosedOrientedManifold :=
  incidenceChart N endpoint chart (endpoint s false) ⟨(s, true), hloop⟩

theorem disjoint_loop_charts
    (hdisj : Pairwise fun p q =>
      Disjoint (flagMap N endpoint chart p '' closedBall (0 : E3) 2)
        (flagMap N endpoint chart q '' closedBall (0 : E3) 2)) :
    Disjoint ((chart s false).chart '' closedBall (0 : E3) 2)
      ((loopSecondChart N endpoint chart s hloop).chart '' closedBall (0 : E3) 2) := by
  apply pairwise_disjoint_incidenceChart_image N endpoint chart (endpoint s false) hdisj
    (i := ⟨(s, false), rfl⟩) (j := ⟨(s, true), hloop⟩)
  intro h
  have hh : false = true := congrArg (fun p => p.val.2) h
  cases hh

theorem remainingIncidenceChart_avoids_incidence
    (hdisj : Pairwise fun p q =>
      Disjoint (flagMap N endpoint chart p '' closedBall (0 : E3) 2)
        (flagMap N endpoint chart q '' closedBall (0 : E3) 2))
    (v : V) (p : {p : E × Bool // p.1 ≠ s ∧ endpoint p.1 p.2 = v})
    (t : Bool) (ht : endpoint s t = v) (x : E3) (hx : x ∈ closedBall (0 : E3) 2) :
    (remainingIncidenceChart N endpoint chart s v p).chart x ∉
      (incidenceChart N endpoint chart v ⟨(s, t), ht⟩).chart '' closedBall (0 : E3) 2 := by
  intro hm
  apply disjoint_left.mp (pairwise_disjoint_incidenceChart_image N endpoint chart v hdisj
    (i := ⟨p.val, p.property.2⟩) (j := ⟨(s, t), ht⟩) ?_) ⟨x, hx, rfl⟩ hm
  intro h
  exact p.property.1 (congrArg (fun q => q.val.1) h)

theorem loop_holes_iff (x : (N (endpoint s false)).Carrier) :
    Sigma.mk (endpoint s false) x ∈ ⋃ p, flagMap N endpoint chart p '' ball (0 : E3) 1 ↔
      (x ∈ (chart s false).chart '' ball (0 : E3) 1 ∨
        x ∈ (loopSecondChart N endpoint chart s hloop).chart '' ball (0 : E3) 1) ∨
      x ∈ ⋃ p, (remainingIncidenceChart N endpoint chart s (endpoint s false) p).chart ''
        ball (0 : E3) 1 := by
  have hinj : Function.Injective (fun x : (N (endpoint s false)).Carrier =>
      (⟨endpoint s false, x⟩ : Σ v, (N v).Carrier)) := by
    intro x y h
    cases h
    rfl
  constructor
  · intro hx
    obtain ⟨p, y, hy, hyx⟩ := mem_iUnion.mp hx
    have hpv : endpoint p.1 p.2 = endpoint s false := congrArg Sigma.fst hyx
    by_cases hps : p.1 = s
    · obtain ⟨e, t⟩ := p
      dsimp at hps
      subst e
      cases t
      · exact Or.inl (Or.inl ⟨y, hy, hinj hyx⟩)
      · refine Or.inl (Or.inr ⟨y, hy, ?_⟩)
        exact hinj ((incidenceChart_sigma_apply N endpoint chart (endpoint s false)
          ⟨(s, true), hloop⟩ y).trans hyx)
    · refine Or.inr (mem_iUnion.mpr ⟨⟨p, hps, hpv⟩, y, hy, ?_⟩)
      exact hinj ((remainingIncidenceChart_sigma_apply N endpoint chart s (endpoint s false)
        ⟨p, hps, hpv⟩ y).trans hyx)
  · rintro ((⟨y, hy, hxy⟩ | ⟨y, hy, hxy⟩) | hx)
    · exact mem_iUnion.mpr ⟨(s, false), y, hy, congrArg
        (fun x => (⟨endpoint s false, x⟩ : Σ v, (N v).Carrier)) hxy⟩
    · refine mem_iUnion.mpr ⟨(s, true), y, hy, ?_⟩
      exact (incidenceChart_sigma_apply N endpoint chart (endpoint s false)
        ⟨(s, true), hloop⟩ y).symm.trans (congrArg
          (fun x => (⟨endpoint s false, x⟩ : Σ v, (N v).Carrier)) hxy)
    · obtain ⟨p, y, hy, hyx⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨p.val, y, hy,
        (remainingIncidenceChart_sigma_apply N endpoint chart s (endpoint s false) p y).symm.trans
          (congrArg (fun x => (⟨endpoint s false, x⟩ : Σ v, (N v).Carrier)) hyx)⟩

def loopPuncturedFactorHomeomorph :
    PuncturedFactor N endpoint chart (endpoint s false) ≃ₜ
      {x : (chart s false).toBallChart.DoublePunctured
        (loopSecondChart N endpoint chart s hloop).toBallChart //
        x.val ∉ ⋃ p, (remainingIncidenceChart N endpoint chart s (endpoint s false) p).chart ''
          ball (0 : E3) 1} where
  toFun x := ⟨⟨x.val, fun h => x.property
      ((loop_holes_iff N endpoint chart s hloop x.val).mpr (Or.inl h))⟩,
    fun h => x.property ((loop_holes_iff N endpoint chart s hloop x.val).mpr (Or.inr h))⟩
  invFun x := ⟨x.val.val, fun h =>
    ((loop_holes_iff N endpoint chart s hloop x.val.val).mp h).elim
      x.val.property x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

@[simp] theorem loopPuncturedFactorHomeomorph_val (x : PuncturedFactor N endpoint chart
    (endpoint s false)) :
    (loopPuncturedFactorHomeomorph N endpoint chart s hloop x).val.val = x.val := rfl

end DifferentialGeometry.Topology.PairedBallGluing

end

section

namespace DifferentialGeometry.Topology.PairedBallGluing

universe u v w
variable {V : Type v} {E : Type w}
  (N : V → ConnectedClosedOrientedManifold.{u} 3)
  (endpoint : E → Bool → V)
  (chart : (e : E) → (b : Bool) →
    OrientedBallChart (N (endpoint e b)).toClosedOrientedManifold)
  (s : E) (hloop : endpoint s true = endpoint s false)
  (hdisj : Pairwise fun p q =>
    Disjoint (flagMap N endpoint chart p '' closedBall (0 : E3) 2)
      (flagMap N endpoint chart q '' closedBall (0 : E3) 2))

private theorem boundary_cast_sigma (e : E) (t : Bool) (v : V)
    (hv : endpoint e t = v) (z : sphere (0 : E3) 1) :
    (⟨v, hv ▸ boundaryPoint N endpoint chart hdisj e t z⟩ :
      Σ v, PuncturedFactor N endpoint chart v) =
      ⟨endpoint e t, boundaryPoint N endpoint chart hdisj e t z⟩ := by
  subst v
  rfl

private theorem boundary_cast_chart (e : E) (t : Bool) (v : V)
    (hv : endpoint e t = v) (z : sphere (0 : E3) 1) :
    (hv ▸ boundaryPoint N endpoint chart hdisj e t z).val =
      (incidenceChart N endpoint chart v ⟨(e, t), hv⟩).chart z := by
  subst v
  rfl

def loopSeamQuotientHomeomorph (a : BoundaryAttachment) :
    Quot (seamRel N endpoint chart hdisj s a) ≃ₜ
      Quot (fun x y : {x : (chart s false).toBallChart.DoublePunctured
          (loopSecondChart N endpoint chart s hloop).toBallChart //
          x.val ∉ ⋃ p, (remainingIncidenceChart N endpoint chart s (endpoint s false) p).chart ''
            ball (0 : E3) 1} =>
          SelfAttachment.directRel (chart s false).toBallChart
            (loopSecondChart N endpoint chart s hloop).toBallChart
            (disjoint_loop_charts N endpoint chart s hloop hdisj) a.val.toHomeomorph x.val y.val) ⊕
      (Σ v : {v // v ≠ endpoint s false}, PuncturedFactor N endpoint chart v.val) := by
  let X := PuncturedFactor N endpoint chart
  let i := endpoint s false
  let p := chart s false
  let q := loopSecondChart N endpoint chart s hloop
  let hd := disjoint_loop_charts N endpoint chart s hloop hdisj
  let EL := loopPuncturedFactorHomeomorph N endpoint chart s hloop
  let B := boundaryPoint N endpoint chart hdisj s false
  let D : sphere (0 : E3) 1 → X i := fun z =>
    (show PuncturedFactor N endpoint chart (endpoint s false) from
      hloop ▸ boundaryPoint N endpoint chart hdisj s true (a.val z))
  let r : X i → X i → Prop := fun x y =>
    ∃ z, (x = B z ∧ y = D z) ∨ (y = B z ∧ x = D z)
  have hBD (z : sphere (0 : E3) 1) : (EL (B z)).val = p.firstBoundaryMap q.toBallChart hd z := rfl
  have hDD (z : sphere (0 : E3) 1) :
      (EL (D z)).val = p.secondBoundaryMap q.toBallChart hd (a.val z) := by
    apply Subtype.ext
    exact boundary_cast_chart N endpoint chart hdisj s true i hloop (a.val z)
  have hρ (x y : Σ v, X v) : seamRel N endpoint chart hdisj s a x y ↔
      ∃ u v, r u v ∧ (⟨i, u⟩ : Σ v, X v) = x ∧ (⟨i, v⟩ : Σ v, X v) = y := by
    have hD (z : sphere (0 : E3) 1) :
        (⟨i, D z⟩ : Σ v, X v) =
          ⟨endpoint s true, boundaryPoint N endpoint chart hdisj s true (a.val z)⟩ :=
      boundary_cast_sigma N endpoint chart hdisj s true i hloop (a.val z)
    constructor
    · rintro ⟨z, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
      · exact ⟨B z, D z, ⟨z, Or.inl ⟨rfl, rfl⟩⟩, rfl, hD z⟩
      · exact ⟨D z, B z, ⟨z, Or.inr ⟨rfl, rfl⟩⟩, hD z, rfl⟩
    · rintro ⟨u, v, ⟨z, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩, rfl, rfl⟩
      · exact ⟨z, Or.inl ⟨rfl, hD z⟩⟩
      · exact ⟨z, Or.inr ⟨rfl, hD z⟩⟩
  have hrel (x y : X i) : r x y ↔ SelfAttachment.directRel p.toBallChart q.toBallChart hd
      a.val.toHomeomorph (EL x).val (EL y).val := by
    constructor
    · rintro ⟨z, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
      · exact ⟨z, Or.inl ⟨hBD z, hDD z⟩⟩
      · exact ⟨z, Or.inr ⟨hBD z, hDD z⟩⟩
    · rintro ⟨z, ⟨hx, hy⟩ | ⟨hy, hx⟩⟩
      · exact ⟨z, Or.inl ⟨EL.injective (Subtype.ext (hx.trans (hBD z).symm)),
          EL.injective (Subtype.ext (hy.trans (hDD z).symm))⟩⟩
      · exact ⟨z, Or.inr ⟨EL.injective (Subtype.ext (hy.trans (hBD z).symm)),
          EL.injective (Subtype.ext (hx.trans (hDD z).symm))⟩⟩
  exact (Homeomorph.Quot.congrRight hρ).trans
    ((Homeomorph.sigmaQuotient X i r).trans
      (Homeomorph.sumCongr (Homeomorph.Quot.congr EL hrel) (Homeomorph.refl _)))

@[simp] theorem loopSeamQuotientHomeomorph_selected (a : BoundaryAttachment)
    (x : PuncturedFactor N endpoint chart (endpoint s false)) :
    loopSeamQuotientHomeomorph N endpoint chart s hloop hdisj a
      (Quot.mk _ ⟨endpoint s false, x⟩) =
        Sum.inl (Quot.mk _ (loopPuncturedFactorHomeomorph N endpoint chart s hloop x)) := by
  unfold loopSeamQuotientHomeomorph
  change Sum.map _ id ((Homeomorph.sigmaQuotient (PuncturedFactor N endpoint chart)
    (endpoint s false) _) (Quot.mk _ ⟨endpoint s false, x⟩)) = _
  rw [Homeomorph.sigmaQuotient_mk_selected]
  rfl

@[simp] theorem loopSeamQuotientHomeomorph_remaining (a : BoundaryAttachment)
    (v : {v // v ≠ endpoint s false}) (x : PuncturedFactor N endpoint chart v.val) :
    loopSeamQuotientHomeomorph N endpoint chart s hloop hdisj a
      (Quot.mk _ ⟨v.val, x⟩) = Sum.inr ⟨v, x⟩ := by
  unfold loopSeamQuotientHomeomorph
  change Sum.map _ id ((Homeomorph.sigmaQuotient (PuncturedFactor N endpoint chart)
    (endpoint s false) _) (Quot.mk _ ⟨v.val, x⟩)) = _
  rw [Homeomorph.sigmaQuotient_mk_remaining]
  rfl

end DifferentialGeometry.Topology.PairedBallGluing

end

section

namespace DifferentialGeometry.Topology.PairedBallGluing

universe u v w
variable {V : Type v} {E : Type w}
  (N : V → ConnectedClosedOrientedManifold.{u} 3)
  (endpoint : E → Bool → V)
  (chart : (e : E) → (b : Bool) →
    OrientedBallChart (N (endpoint e b)).toClosedOrientedManifold)
  (s : E) (hloop : endpoint s true = endpoint s false)
  (hdisj : Pairwise fun p q =>
    Disjoint (flagMap N endpoint chart p '' closedBall (0 : E3) 2)
      (flagMap N endpoint chart q '' closedBall (0 : E3) 2))

theorem exists_loop_seam_homeomorph :
    let p := chart s false
    let q := loopSecondChart N endpoint chart s hloop
    let hd := disjoint_loop_charts N endpoint chart s hloop hdisj
    let e := remainingIncidenceChart N endpoint chart s (endpoint s false)
    ∃ S : SmoothSelfAttachment p q hd boundaryAttachment,
    ∃ F : ClosedOrientedManifold.OrientedDiffeomorph
      S.toConnectedClosedOrientedManifold.toClosedOrientedManifold
      (connectedSum (N (endpoint s false)) sphereTwoTimesCircleLift).toClosedOrientedManifold,
    ∃ b : {p : E × Bool // p.1 ≠ s ∧ endpoint p.1 p.2 = endpoint s false} →
      OrientedBallChart
        (connectedSum (N (endpoint s false)) sphereTwoTimesCircleLift).toClosedOrientedManifold,
      (∀ i x, x ∈ closedBall (0 : E3) 2 →
        ∃ hx : (e i).chart x ∈ (p.chart '' ball 0 1 ∪ q.chart '' ball 0 1)ᶜ,
          (b i).chart x = F.val (SelfAttachment.coreInclusion p.toBallChart q.toBallChart hd
            boundaryAttachment.val.toHomeomorph ⟨(e i).chart x, hx⟩)) ∧
      (Pairwise fun i j => Disjoint ((b i).chart '' closedBall (0 : E3) 2)
        ((b j).chart '' closedBall (0 : E3) 2)) ∧
      ∃ H : Quot (seamRel N endpoint chart hdisj s boundaryAttachment) ≃ₜ
        {y : (connectedSum (N (endpoint s false)) sphereTwoTimesCircleLift).Carrier //
          y ∉ ⋃ i, (b i).chart '' ball (0 : E3) 1} ⊕
        (Σ v : {v // v ≠ endpoint s false}, PuncturedFactor N endpoint chart v.val),
        (∀ x : PuncturedFactor N endpoint chart (endpoint s false),
          ∃ y, H (Quot.mk _ ⟨endpoint s false, x⟩) = Sum.inl y ∧
            y.val = F.val (SelfAttachment.coreToBand p.toBallChart q.toBallChart hd
              boundaryAttachment.val.toHomeomorph
              (loopPuncturedFactorHomeomorph N endpoint chart s hloop x).val)) ∧
        (∀ (v : {v // v ≠ endpoint s false}) (x : PuncturedFactor N endpoint chart v.val),
          H (Quot.mk _ ⟨v.val, x⟩) = Sum.inr ⟨v, x⟩) ∧
        (∀ (i : {p : E × Bool // p.1 ≠ s ∧ endpoint p.1 p.2 = endpoint s false})
          (z : sphere (0 : E3) 1),
          ∃ y, H (Quot.mk _ ⟨endpoint i.val.1 i.val.2,
            boundaryPoint N endpoint chart hdisj i.val.1 i.val.2 z⟩) = Sum.inl y ∧
              y.val = (b i).chart z) := by
  dsimp only
  let p := chart s false
  let q := loopSecondChart N endpoint chart s hloop
  let hd := disjoint_loop_charts N endpoint chart s hloop hdisj
  let e := remainingIncidenceChart N endpoint chart s (endpoint s false)
  have hep (i) (x : E3) (hx : x ∈ closedBall (0 : E3) 2) :
      (e i).chart x ∉ p.chart '' closedBall (0 : E3) 2 :=
    remainingIncidenceChart_avoids_incidence N endpoint chart s hdisj
      (endpoint s false) i false rfl x hx
  have heq (i) (x : E3) (hx : x ∈ closedBall (0 : E3) 2) :
      (e i).chart x ∉ q.chart '' closedBall (0 : E3) 2 :=
    remainingIncidenceChart_avoids_incidence N endpoint chart s hdisj
      (endpoint s false) i true hloop x hx
  obtain ⟨S, F, b, hb, hbd, H₀, hH₀, hHchart⟩ :=
    SelfAttachment.exists_orientedBallChart_family_complement_homeomorph
      (N (endpoint s false)) p q hd e hep heq
      (pairwise_disjoint_remainingIncidenceChart_image N endpoint chart s (endpoint s false) hdisj)
  let L := loopSeamQuotientHomeomorph N endpoint chart s hloop hdisj boundaryAttachment
  let H := L.trans (Homeomorph.sumCongr H₀ (Homeomorph.refl _))
  have hfirst (x : PuncturedFactor N endpoint chart (endpoint s false)) :
      H (Quot.mk _ ⟨endpoint s false, x⟩) =
        Sum.inl (H₀ (Quot.mk _ (loopPuncturedFactorHomeomorph N endpoint chart s hloop x))) := by
    change (Homeomorph.sumCongr H₀ (Homeomorph.refl _))
      (loopSeamQuotientHomeomorph N endpoint chart s hloop hdisj boundaryAttachment
        (Quot.mk _ ⟨endpoint s false, x⟩)) = _
    rw [loopSeamQuotientHomeomorph_selected]
    rfl
  refine ⟨S, F, b, hb, hbd, H, ?_, ?_, ?_⟩
  · intro x
    exact ⟨_, hfirst x, hH₀ _⟩
  · intro v x
    change (Homeomorph.sumCongr H₀ (Homeomorph.refl _))
      (loopSeamQuotientHomeomorph N endpoint chart s hloop hdisj boundaryAttachment
        (Quot.mk _ ⟨v.val, x⟩)) = _
    rw [loopSeamQuotientHomeomorph_remaining]
    rfl
  · intro i z
    let x : PuncturedFactor N endpoint chart (endpoint s false) :=
      i.property.2 ▸ boundaryPoint N endpoint chart hdisj i.val.1 i.val.2 z
    have hxSigma : (⟨endpoint s false, x⟩ : Σ v, PuncturedFactor N endpoint chart v) =
        ⟨endpoint i.val.1 i.val.2, boundaryPoint N endpoint chart hdisj i.val.1 i.val.2 z⟩ :=
      boundary_cast_sigma N endpoint chart hdisj i.val.1 i.val.2 (endpoint s false) i.property.2 z
    have hxVal : x.val = (e i).chart z :=
      boundary_cast_chart N endpoint chart hdisj i.val.1 i.val.2 (endpoint s false) i.property.2 z
    let x' := loopPuncturedFactorHomeomorph N endpoint chart s hloop x
    have hx' : x'.val.val = (e i).chart z := hxVal
    have hp : (e i).chart z ∈ (p.chart '' ball 0 1 ∪ q.chart '' ball 0 1)ᶜ :=
      hxVal ▸ x'.val.property
    have hu : (e i).chart z ∉ ⋃ j, (e j).chart '' ball (0 : E3) 1 := hxVal ▸ x'.property
    refine ⟨H₀ (Quot.mk _ x'), ?_, ?_⟩
    · exact (congrArg (fun w => H (Quot.mk _ w)) hxSigma).symm.trans (hfirst x)
    · have heq' : x' = ⟨⟨(e i).chart z, hp⟩, hu⟩ := Subtype.ext (Subtype.ext hx')
      exact (congrArg (fun x => (H₀ (Quot.mk _ x)).val) heq').trans
        (hHchart i z (sphere_subset_closedBall.trans
          (closedBall_subset_closedBall (by norm_num)) z.property) hp hu)

end DifferentialGeometry.Topology.PairedBallGluing

end

section

namespace DifferentialGeometry.Topology.PairedBallGluing

universe u v w
variable {V : Type v} {E : Type w}
  (N : V → ConnectedClosedOrientedManifold.{u} 3)
  (endpoint : E → Bool → V)
  (chart : (e : E) → (b : Bool) →
    OrientedBallChart (N (endpoint e b)).toClosedOrientedManifold)
  (s : E)

private abbrev RemainingVertex := {v // v ≠ endpoint s false}
private abbrev RemainingFlag := {p : E × Bool // p.1 ≠ s ∧ endpoint p.1 p.2 = endpoint s false}

def loopFactor : Option (RemainingVertex endpoint s) → ConnectedClosedOrientedManifold.{u} 3
  | none => connectedSum (N (endpoint s false)) sphereTwoTimesCircleLift
  | some v => N v.val

def loopVertex (v : V) : Option (RemainingVertex endpoint s) := by
  classical
  exact if hi : v = endpoint s false then none else some ⟨v, hi⟩

@[simp] theorem loopVertex_selected : loopVertex endpoint s (endpoint s false) = none := by
  simp [loopVertex]

@[simp] theorem loopVertex_remaining (v : RemainingVertex endpoint s) :
    loopVertex endpoint s v.val = some v := by
  simp [loopVertex, v.property]

def loopFlag
    (b : RemainingFlag endpoint s → OrientedBallChart (loopFactor N endpoint s
        none).toClosedOrientedManifold)
    (e : {e // e ≠ s}) (t : Bool) :
    Σ v, OrientedBallChart (loopFactor N endpoint s v).toClosedOrientedManifold := by
  classical
  exact if hi : endpoint e.val t = endpoint s false then
    ⟨none, b ⟨(e.val, t), e.property, hi⟩⟩
  else ⟨some ⟨endpoint e.val t, hi⟩, chart e.val t⟩

theorem loopFlag_fst
    (b : RemainingFlag endpoint s → OrientedBallChart (loopFactor N endpoint s
        none).toClosedOrientedManifold)
    (e : {e // e ≠ s}) (t : Bool) :
    (loopFlag N endpoint chart s b e t).fst = loopVertex endpoint s (endpoint e.val t) := by
  classical
  unfold loopFlag loopVertex
  split_ifs <;> rfl

theorem loopFlag_flagMap_selected
    (b : RemainingFlag endpoint s → OrientedBallChart (loopFactor N endpoint s
        none).toClosedOrientedManifold)
    (e : {e // e ≠ s}) (t : Bool) (hi : endpoint e.val t = endpoint s false) (x : E3) :
    flagMap (loopFactor N endpoint s)
      (fun e t => (loopFlag N endpoint chart s b e t).fst)
      (fun e t => (loopFlag N endpoint chart s b e t).snd) (e, t) x =
      ⟨none, (b ⟨(e.val, t), e.property, hi⟩).chart x⟩ := by
  classical
  have h : loopFlag N endpoint chart s b e t = ⟨none, b ⟨(e.val, t), e.property, hi⟩⟩ := by
    unfold loopFlag
    rw [dite_eq_left hi]
  exact congrArg (fun p : Σ v, OrientedBallChart (loopFactor N endpoint s
      v).toClosedOrientedManifold =>
    (⟨p.fst, p.snd.chart x⟩ : Σ v, (loopFactor N endpoint s v).Carrier)) h

theorem loopFlag_flagMap_remaining
    (b : RemainingFlag endpoint s → OrientedBallChart (loopFactor N endpoint s
        none).toClosedOrientedManifold)
    (e : {e // e ≠ s}) (t : Bool) (hi : endpoint e.val t ≠ endpoint s false) (x : E3) :
    flagMap (loopFactor N endpoint s)
      (fun e t => (loopFlag N endpoint chart s b e t).fst)
      (fun e t => (loopFlag N endpoint chart s b e t).snd) (e, t) x =
      ⟨some ⟨endpoint e.val t, hi⟩, (chart e.val t).chart x⟩ := by
  classical
  have h : loopFlag N endpoint chart s b e t =
      ⟨some ⟨endpoint e.val t, hi⟩, chart e.val t⟩ := by
    unfold loopFlag
    rw [dite_eq_right hi]
  exact congrArg (fun p : Σ v, OrientedBallChart (loopFactor N endpoint s
      v).toClosedOrientedManifold =>
    (⟨p.fst, p.snd.chart x⟩ : Σ v, (loopFactor N endpoint s v).Carrier)) h

theorem pairwise_disjoint_loopFlag_image
    (b : RemainingFlag endpoint s → OrientedBallChart (loopFactor N endpoint s
        none).toClosedOrientedManifold)
    (hdisj : Pairwise fun p q =>
      Disjoint (flagMap N endpoint chart p '' closedBall (0 : E3) 2)
        (flagMap N endpoint chart q '' closedBall (0 : E3) 2))
    (hb : Pairwise fun p q => Disjoint ((b p).chart '' closedBall (0 : E3) 2)
      ((b q).chart '' closedBall (0 : E3) 2)) :
    Pairwise fun p q : {e // e ≠ s} × Bool =>
      Disjoint (flagMap (loopFactor N endpoint s)
        (fun e t => (loopFlag N endpoint chart s b e t).fst)
        (fun e t => (loopFlag N endpoint chart s b e t).snd) p '' closedBall (0 : E3) 2)
      (flagMap (loopFactor N endpoint s)
        (fun e t => (loopFlag N endpoint chart s b e t).fst)
        (fun e t => (loopFlag N endpoint chart s b e t).snd) q '' closedBall (0 : E3) 2) := by
  classical
  let O := {e // e ≠ s} × Bool
  let original : O → E × Bool := fun p => (p.1.val, p.2)
  have horiginal : Function.Injective original := by
    intro p q h
    exact Prod.ext (Subtype.ext (congrArg Prod.fst h)) (congrArg (fun p : E × Bool => p.2) h)
  let F := flagMap (loopFactor N endpoint s)
    (fun e t => (loopFlag N endpoint chart s b e t).fst)
    (fun e t => (loopFlag N endpoint chart s b e t).snd)
  let P : (Σ v, (loopFactor N endpoint s v).Carrier) →
      (loopFactor N endpoint s none).Carrier ⊕ (Σ v, (N v).Carrier) :=
    fun q => match q with
      | ⟨none, x⟩ => Sum.inl x
      | ⟨some v, x⟩ => Sum.inr ⟨v.val, x⟩
  have hclass (p : O) (x : E3) :
      (∃ j : RemainingFlag endpoint s, j.val = original p ∧ P (F p x) = Sum.inl ((b j).chart x)) ∨
      P (F p x) = Sum.inr (flagMap N endpoint chart (original p) x) := by
    by_cases hi : endpoint p.1.val p.2 = endpoint s false
    · refine Or.inl ⟨⟨original p, p.1.property, hi⟩, rfl, ?_⟩
      rw [show F p x = _ from loopFlag_flagMap_selected N endpoint chart s b p.1 p.2 hi x]
    · refine Or.inr ?_
      rw [show F p x = _ from loopFlag_flagMap_remaining N endpoint chart s b p.1 p.2 hi x]
      rfl
  intro p q hpq
  rw [disjoint_left]
  rintro z ⟨x, hx, hxz⟩ ⟨y, hy, hyz⟩
  have hxy : P (F p x) = P (F q y) := congrArg P (hxz.trans hyz.symm)
  rcases hclass p x with ⟨i, hi, hix⟩ | hix <;>
    rcases hclass q y with ⟨j, hj, hjy⟩ | hjy
  · have hv : (b i).chart x = (b j).chart y := Sum.inl.inj (hix.symm.trans (hxy.trans hjy))
    have hij : i ≠ j := fun h => hpq (horiginal (hi.symm.trans ((congrArg Subtype.val h).trans hj)))
    exact disjoint_left.mp (hb hij) ⟨x, hx, hv⟩ ⟨y, hy, rfl⟩
  · exact Sum.inl_ne_inr (hix.symm.trans (hxy.trans hjy))
  · exact Sum.inr_ne_inl (hix.symm.trans (hxy.trans hjy))
  · have hv := Sum.inr.inj (hix.symm.trans (hxy.trans hjy))
    exact disjoint_left.mp (hdisj (fun h => hpq (horiginal h))) ⟨x, hx, hv⟩ ⟨y, hy, rfl⟩

theorem loopFlag_holes_none
    (b : RemainingFlag endpoint s → OrientedBallChart (loopFactor N endpoint s
        none).toClosedOrientedManifold)
    (S : Set E3) :
    (fun x : (loopFactor N endpoint s none).Carrier =>
      (⟨none, x⟩ : Σ v, (loopFactor N endpoint s v).Carrier)) ⁻¹'
      (⋃ p, flagMap (loopFactor N endpoint s)
        (fun e t => (loopFlag N endpoint chart s b e t).fst)
        (fun e t => (loopFlag N endpoint chart s b e t).snd) p '' S) =
      ⋃ p, (b p).chart '' S := by
  classical
  let F := flagMap (loopFactor N endpoint s)
    (fun e t => (loopFlag N endpoint chart s b e t).fst)
    (fun e t => (loopFlag N endpoint chart s b e t).snd)
  have hinj : Function.Injective (fun x : (loopFactor N endpoint s none).Carrier =>
      (⟨none, x⟩ : Σ v, (loopFactor N endpoint s v).Carrier)) := by
    intro x y h
    cases h
    rfl
  ext x
  constructor
  · intro hx
    obtain ⟨⟨e, t⟩, y, hy, hyx⟩ := mem_iUnion.mp hx
    change F (e, t) y = _ at hyx
    by_cases hi : endpoint e.val t = endpoint s false
    · have hf := loopFlag_flagMap_selected N endpoint chart s b e t hi y
      exact mem_iUnion.mpr ⟨⟨(e.val, t), e.property, hi⟩, y, hy, hinj (hf.symm.trans hyx)⟩
    · have hf := loopFlag_flagMap_remaining N endpoint chart s b e t hi y
      have hh := congrArg Sigma.fst (hf.symm.trans hyx)
      exact (Option.some_ne_none _ hh).elim
  · intro hx
    obtain ⟨p, y, hy, hyx⟩ := mem_iUnion.mp hx
    refine mem_iUnion.mpr ⟨(⟨p.val.1, p.property.1⟩, p.val.2), y, hy, ?_⟩
    exact (loopFlag_flagMap_selected N endpoint chart s b
      ⟨p.val.1, p.property.1⟩ p.val.2 p.property.2 y).trans
      (congrArg (fun x : (loopFactor N endpoint s none).Carrier =>
        (⟨none, x⟩ : Σ v, (loopFactor N endpoint s v).Carrier)) hyx)

private theorem loop_sigma_some_eq (v v' : RemainingVertex endpoint s)
    (x : (N v.val).Carrier) (y : (N v'.val).Carrier)
    (h : (⟨v.val, x⟩ : Σ v, (N v).Carrier) = ⟨v'.val, y⟩) :
    (⟨some v, x⟩ : Σ v, (loopFactor N endpoint s v).Carrier) = ⟨some v', y⟩ := by
  have hv : v = v' := Subtype.ext (congrArg Sigma.fst h)
  subst v'
  have hinj : Function.Injective (fun x : (N v.val).Carrier =>
      (⟨v.val, x⟩ : Σ v, (N v).Carrier)) := by
    intro x y h
    cases h
    rfl
  rw [hinj h]

theorem loopFlag_holes_some
    (b : RemainingFlag endpoint s → OrientedBallChart (loopFactor N endpoint s
        none).toClosedOrientedManifold)
    (hloop : endpoint s true = endpoint s false) (v : RemainingVertex endpoint s) (S : Set E3) :
    (fun x : (N v.val).Carrier =>
      (⟨some v, x⟩ : Σ v, (loopFactor N endpoint s v).Carrier)) ⁻¹'
      (⋃ p, flagMap (loopFactor N endpoint s)
        (fun e t => (loopFlag N endpoint chart s b e t).fst)
        (fun e t => (loopFlag N endpoint chart s b e t).snd) p '' S) =
      (fun x : (N v.val).Carrier => (⟨v.val, x⟩ : Σ v, (N v).Carrier)) ⁻¹'
        (⋃ p, flagMap N endpoint chart p '' S) := by
  classical
  let F := flagMap (loopFactor N endpoint s)
    (fun e t => (loopFlag N endpoint chart s b e t).fst)
    (fun e t => (loopFlag N endpoint chart s b e t).snd)
  let P : (Σ v, (loopFactor N endpoint s v).Carrier) →
      (loopFactor N endpoint s none).Carrier ⊕ (Σ v, (N v).Carrier) :=
    fun q => match q with
      | ⟨none, x⟩ => Sum.inl x
      | ⟨some v, x⟩ => Sum.inr ⟨v.val, x⟩
  ext x
  constructor
  · intro hx
    obtain ⟨⟨e, t⟩, y, hy, hyx⟩ := mem_iUnion.mp hx
    change F (e, t) y = _ at hyx
    by_cases hi : endpoint e.val t = endpoint s false
    · have hf := loopFlag_flagMap_selected N endpoint chart s b e t hi y
      have hh := congrArg Sigma.fst (hf.symm.trans hyx)
      exact (Option.some_ne_none _ hh.symm).elim
    · have hf := loopFlag_flagMap_remaining N endpoint chart s b e t hi y
      exact mem_iUnion.mpr ⟨(e.val, t), y, hy, Sum.inr.inj (congrArg P (hf.symm.trans hyx))⟩
  · intro hx
    obtain ⟨p, y, hy, hyx⟩ := mem_iUnion.mp hx
    have hpv : endpoint p.1 p.2 = v.val := congrArg Sigma.fst hyx
    have hi : endpoint p.1 p.2 ≠ endpoint s false := fun h => v.property (hpv.symm.trans h)
    have hps : p.1 ≠ s := by
      intro h
      obtain ⟨e, t⟩ := p
      dsimp at h hi
      subst e
      cases t
      · exact hi rfl
      · exact hi hloop
    refine mem_iUnion.mpr ⟨(⟨p.1, hps⟩, p.2), y, hy, ?_⟩
    exact (loopFlag_flagMap_remaining N endpoint chart s b ⟨p.1, hps⟩ p.2 hi y).trans
      (loop_sigma_some_eq N endpoint s ⟨endpoint p.1 p.2, hi⟩ v ((chart p.1 p.2).chart y) x hyx)

def loopPuncturedFactorHomeomorphSplit
    (b : RemainingFlag endpoint s → OrientedBallChart (loopFactor N endpoint s
        none).toClosedOrientedManifold)
    (hloop : endpoint s true = endpoint s false) :
    (Σ v, PuncturedFactor (loopFactor N endpoint s)
      (fun e t => (loopFlag N endpoint chart s b e t).fst)
      (fun e t => (loopFlag N endpoint chart s b e t).snd) v) ≃ₜ
      {q : (loopFactor N endpoint s none).Carrier // q ∉ ⋃ p, (b p).chart '' ball (0 : E3) 1} ⊕
      (Σ v : RemainingVertex endpoint s, PuncturedFactor N endpoint chart v.val) := by
  let N' := loopFactor N endpoint s
  let ep' := fun e t => (loopFlag N endpoint chart s b e t).fst
  let ch' := fun e t => (loopFlag N endpoint chart s b e t).snd
  let X := PuncturedFactor N' ep' ch'
  let Y : Option (RemainingVertex endpoint s) → Type u := fun v => match v with
    | none => {q : (N' none).Carrier // q ∉ ⋃ p, (b p).chart '' ball (0 : E3) 1}
    | some v => PuncturedFactor N endpoint chart v.val
  letI : ∀ v, TopologicalSpace (Y v) := fun v => by cases v <;> dsimp [Y] <;> infer_instance
  let h : ∀ v, X v ≃ₜ Y v := fun v => by
    cases v with
    | none =>
      apply Homeomorph.setCongr
      ext x
      exact not_congr (Set.ext_iff.mp (loopFlag_holes_none N endpoint chart s b (ball 0 1)) x)
    | some v =>
      apply Homeomorph.setCongr
      ext x
      exact not_congr (Set.ext_iff.mp (loopFlag_holes_some N endpoint chart s b hloop v (ball
          0 1)) x)
  exact (Homeomorph.sigmaCongrRight h).trans (Homeomorph.sigmaOption Y)

end DifferentialGeometry.Topology.PairedBallGluing

end

section

namespace DifferentialGeometry.Topology.PairedBallGluing
universe u v w
variable {V : Type v} {E : Type w}
  (N : V → ConnectedClosedOrientedManifold.{u} 3)
  (endpoint : E → Bool → V)
  (chart : (e : E) → (t : Bool) →
    OrientedBallChart (N (endpoint e t)).toClosedOrientedManifold)
  (s : E)

private def loopSplitVal
    (b : RemainingFlag endpoint s →
      OrientedBallChart (loopFactor N endpoint s none).toClosedOrientedManifold) :
    ({x : (loopFactor N endpoint s none).Carrier //
        x ∉ ⋃ p, (b p).chart '' ball (0 : E3) 1} ⊕
      (Σ v : RemainingVertex endpoint s, PuncturedFactor N endpoint chart v.val)) →
        (loopFactor N endpoint s none).Carrier ⊕ (Σ v, (N v).Carrier) :=
  Sum.elim (fun x => Sum.inl x.val) (fun p => Sum.inr ⟨p.fst.val, p.snd.val⟩)

private theorem loopSplitVal_injective
    (b : RemainingFlag endpoint s →
      OrientedBallChart (loopFactor N endpoint s none).toClosedOrientedManifold) :
    Function.Injective (loopSplitVal N endpoint chart s b) := by
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

private def loopAmbientSplit :
    (Σ v, (loopFactor N endpoint s v).Carrier) →
      (loopFactor N endpoint s none).Carrier ⊕ (Σ v, (N v).Carrier)
  | ⟨none, x⟩ => Sum.inl x
  | ⟨some v, x⟩ => Sum.inr ⟨v.val, x⟩

private theorem loopPuncturedFactorHomeomorphSplit_val
    (b : RemainingFlag endpoint s →
      OrientedBallChart (loopFactor N endpoint s none).toClosedOrientedManifold)
    (hloop : endpoint s true = endpoint s false)
    (x : Σ v, PuncturedFactor (loopFactor N endpoint s)
      (fun e t => (loopFlag N endpoint chart s b e t).fst)
      (fun e t => (loopFlag N endpoint chart s b e t).snd) v) :
    loopSplitVal N endpoint chart s b
      (loopPuncturedFactorHomeomorphSplit N endpoint chart s b hloop x) =
        loopAmbientSplit N endpoint s ⟨x.fst, x.snd.val⟩ := by
  obtain ⟨v, x⟩ := x
  cases v <;> rfl

variable (hloop : endpoint s true = endpoint s false)
  (hdisj : Pairwise fun p q =>
    Disjoint (flagMap N endpoint chart p '' closedBall (0 : E3) 2)
      (flagMap N endpoint chart q '' closedBall (0 : E3) 2))

theorem exists_loop_homeomorph :
    let p := chart s false
    let q := loopSecondChart N endpoint chart s hloop
    let hd := disjoint_loop_charts N endpoint chart s hloop hdisj
    let e := remainingIncidenceChart N endpoint chart s (endpoint s false)
    ∃ S : SmoothSelfAttachment p q hd boundaryAttachment,
    ∃ F : ClosedOrientedManifold.OrientedDiffeomorph
      S.toConnectedClosedOrientedManifold.toClosedOrientedManifold
      (connectedSum (N (endpoint s false)) sphereTwoTimesCircleLift).toClosedOrientedManifold,
    ∃ b : {p : E × Bool // p.1 ≠ s ∧ endpoint p.1 p.2 = endpoint s false} →
      OrientedBallChart
        (connectedSum (N (endpoint s false)) sphereTwoTimesCircleLift).toClosedOrientedManifold,
      (∀ i x, x ∈ closedBall (0 : E3) 2 →
        ∃ hx : (e i).chart x ∈ (p.chart '' ball 0 1 ∪ q.chart '' ball 0 1)ᶜ,
          (b i).chart x = F.val (SelfAttachment.coreInclusion p.toBallChart q.toBallChart hd
            boundaryAttachment.val.toHomeomorph ⟨(e i).chart x, hx⟩)) ∧
      ∃ hb : Pairwise fun p q =>
        Disjoint (flagMap (loopFactor N endpoint s)
          (fun e t => (loopFlag N endpoint chart s b e t).fst)
          (fun e t => (loopFlag N endpoint chart s b e t).snd) p '' closedBall (0 : E3) 2)
        (flagMap (loopFactor N endpoint s)
          (fun e t => (loopFlag N endpoint chart s b e t).fst)
          (fun e t => (loopFlag N endpoint chart s b e t).snd) q '' closedBall (0 : E3) 2),
        ∃ H : Quot (seamRel N endpoint chart hdisj s boundaryAttachment) ≃ₜ
          (Σ v, PuncturedFactor (loopFactor N endpoint s)
            (fun e t => (loopFlag N endpoint chart s b e t).fst)
            (fun e t => (loopFlag N endpoint chart s b e t).snd) v),
          (∀ x : PuncturedFactor N endpoint chart (endpoint s false),
            ∃ y, loopPuncturedFactorHomeomorphSplit N endpoint chart s b hloop
                (H (Quot.mk _ ⟨endpoint s false, x⟩)) = Sum.inl y ∧
              y.val = F.val (SelfAttachment.coreToBand p.toBallChart q.toBallChart hd
                boundaryAttachment.val.toHomeomorph
                (loopPuncturedFactorHomeomorph N endpoint chart s hloop x).val)) ∧
          (∀ (v : {v // v ≠ endpoint s false}) (x : PuncturedFactor N endpoint chart v.val),
            loopPuncturedFactorHomeomorphSplit N endpoint chart s b hloop
              (H (Quot.mk _ ⟨v.val, x⟩)) = Sum.inr ⟨v, x⟩) ∧
          ∀ (e : {e // e ≠ s}) (t : Bool) (z : sphere (0 : E3) 1),
            H (Quot.mk _ ⟨endpoint e.val t, boundaryPoint N endpoint chart hdisj e.val t z⟩) =
              ⟨(loopFlag N endpoint chart s b e t).fst,
                boundaryPoint (loopFactor N endpoint s)
                  (fun e t => (loopFlag N endpoint chart s b e t).fst)
                  (fun e t => (loopFlag N endpoint chart s b e t).snd) hb e t z⟩ := by
  dsimp only
  obtain ⟨S, F, b, hb, hbd, H, hfirst, hu, hB⟩ :=
    exists_loop_seam_homeomorph N endpoint chart s hloop hdisj
  have hb' := pairwise_disjoint_loopFlag_image N endpoint chart s b hdisj hbd
  let J := loopPuncturedFactorHomeomorphSplit N endpoint chart s b hloop
  let H' := H.trans J.symm
  refine ⟨S, F, b, hb, hb', H', ?_, ?_, ?_⟩
  · intro x
    obtain ⟨y, hy, hyval⟩ := hfirst x
    exact ⟨y, (J.apply_symm_apply _).trans hy, hyval⟩
  · intro v x
    exact (J.apply_symm_apply _).trans (hu v x)
  intro e t z
  apply J.injective
  change J (J.symm (H (Quot.mk _
    ⟨endpoint e.val t, boundaryPoint N endpoint chart hdisj e.val t z⟩))) = _
  refine (J.apply_symm_apply _).trans ?_
  apply loopSplitVal_injective N endpoint chart s b
  refine Eq.trans ?_ (loopPuncturedFactorHomeomorphSplit_val N endpoint chart s b hloop _).symm
  change loopSplitVal N endpoint chart s b
    (H (Quot.mk _ ⟨endpoint e.val t, boundaryPoint N endpoint chart hdisj e.val t z⟩)) =
      loopAmbientSplit N endpoint s
        (flagMap (loopFactor N endpoint s)
          (fun e t => (loopFlag N endpoint chart s b e t).fst)
          (fun e t => (loopFlag N endpoint chart s b e t).snd) (e, t) z)
  by_cases hi : endpoint e.val t = endpoint s false
  · obtain ⟨y, hy, hyval⟩ := hB ⟨(e.val, t), e.property, hi⟩ z
    rw [hy, loopFlag_flagMap_selected N endpoint chart s b e t hi z]
    exact congrArg Sum.inl hyval
  · rw [hu ⟨endpoint e.val t, hi⟩, loopFlag_flagMap_remaining N endpoint chart s b e t hi z]
    rfl

end DifferentialGeometry.Topology.PairedBallGluing

end

section

namespace DifferentialGeometry.Topology.PairedBallGluing
universe u v w
variable {V : Type v} {E : Type w}
  (N : V → ConnectedClosedOrientedManifold.{u} 3)
  (endpoint : E → Bool → V)
  (chart : (e : E) → (t : Bool) →
    OrientedBallChart (N (endpoint e t)).toClosedOrientedManifold)
  (s : E) (hloop : endpoint s true = endpoint s false)
  (hdisj : Pairwise fun p q =>
    Disjoint (flagMap N endpoint chart p '' closedBall (0 : E3) 2)
      (flagMap N endpoint chart q '' closedBall (0 : E3) 2))
  (attachment : E → BoundaryAttachment) (hs : attachment s = boundaryAttachment)

private theorem map_loopSeamRel_iff
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


include hs in
theorem exists_quotient_homeomorph_loop :
    let p := chart s false
    let q := loopSecondChart N endpoint chart s hloop
    let hd := disjoint_loop_charts N endpoint chart s hloop hdisj
    let e := remainingIncidenceChart N endpoint chart s (endpoint s false)
    ∃ S : SmoothSelfAttachment p q hd boundaryAttachment,
    ∃ F : ClosedOrientedManifold.OrientedDiffeomorph
      S.toConnectedClosedOrientedManifold.toClosedOrientedManifold
      (connectedSum (N (endpoint s false)) sphereTwoTimesCircleLift).toClosedOrientedManifold,
    ∃ b : {p : E × Bool // p.1 ≠ s ∧ endpoint p.1 p.2 = endpoint s false} →
      OrientedBallChart
        (connectedSum (N (endpoint s false)) sphereTwoTimesCircleLift).toClosedOrientedManifold,
      (∀ i x, x ∈ closedBall (0 : E3) 2 →
        ∃ hx : (e i).chart x ∈ (p.chart '' ball 0 1 ∪ q.chart '' ball 0 1)ᶜ,
          (b i).chart x = F.val (SelfAttachment.coreInclusion p.toBallChart q.toBallChart hd
            boundaryAttachment.val.toHomeomorph ⟨(e i).chart x, hx⟩)) ∧
      ∃ hb : Pairwise fun p q =>
        Disjoint (flagMap (loopFactor N endpoint s)
          (fun e t => (loopFlag N endpoint chart s b e t).fst)
          (fun e t => (loopFlag N endpoint chart s b e t).snd) p '' closedBall (0 : E3) 2)
        (flagMap (loopFactor N endpoint s)
          (fun e t => (loopFlag N endpoint chart s b e t).fst)
          (fun e t => (loopFlag N endpoint chart s b e t).snd) q '' closedBall (0 : E3) 2),
        ∃ H : Quot (seamRel N endpoint chart hdisj s (attachment s)) ≃ₜ
          (Σ v, PuncturedFactor (loopFactor N endpoint s)
            (fun e t => (loopFlag N endpoint chart s b e t).fst)
            (fun e t => (loopFlag N endpoint chart s b e t).snd) v),
          (∀ x : PuncturedFactor N endpoint chart (endpoint s false),
            ∃ y, loopPuncturedFactorHomeomorphSplit N endpoint chart s b hloop
                (H (Quot.mk _ ⟨endpoint s false, x⟩)) = Sum.inl y ∧
              y.val = F.val (SelfAttachment.coreToBand p.toBallChart q.toBallChart hd
                boundaryAttachment.val.toHomeomorph
                (loopPuncturedFactorHomeomorph N endpoint chart s hloop x).val)) ∧
          (∀ (v : {v // v ≠ endpoint s false}) (x : PuncturedFactor N endpoint chart v.val),
            loopPuncturedFactorHomeomorphSplit N endpoint chart s b hloop
              (H (Quot.mk _ ⟨v.val, x⟩)) = Sum.inr ⟨v, x⟩) ∧
          (∀ (e : {e // e ≠ s}) (t : Bool) (z : sphere (0 : E3) 1),
            H (Quot.mk _ ⟨endpoint e.val t, boundaryPoint N endpoint chart hdisj e.val t z⟩) =
              ⟨(loopFlag N endpoint chart s b e t).fst,
                boundaryPoint (loopFactor N endpoint s)
                  (fun e t => (loopFlag N endpoint chart s b e t).fst)
                  (fun e t => (loopFlag N endpoint chart s b e t).snd) hb e t z⟩ ) ∧
          ∃ J : Quot (fun x y => ∃ e,
              seamRel N endpoint chart hdisj e (attachment e) x y) ≃ₜ
            Quot (fun x y => ∃ e : {e // e ≠ s},
              seamRel (loopFactor N endpoint s)
                (fun e t => (loopFlag N endpoint chart s b e t).fst)
                (fun e t => (loopFlag N endpoint chart s b e t).snd) hb e (attachment e.val) x y),
            ∀ x, J (Quot.mk _ x) = Quot.mk _ (H (Quot.mk _ x)) := by
  dsimp only
  obtain ⟨S, F, b, hb, hb', H₀, hfirst, hu, hH₀⟩ :=
    exists_loop_homeomorph N endpoint chart s hloop hdisj
  let N' := loopFactor N endpoint s
  let endpoint' := fun e t => (loopFlag N endpoint chart s b e t).fst
  let chart' := fun e t => (loopFlag N endpoint chart s b e t).snd
  have heq (x y) : seamRel N endpoint chart hdisj s (attachment s) x y ↔
      seamRel N endpoint chart hdisj s boundaryAttachment x y := by rw [hs]
  let H := (Homeomorph.Quot.congrRight heq).trans H₀
  have hH : ∀ (e : {e // e ≠ s}) (t : Bool) (z : sphere (0 : E3) 1),
      H (Quot.mk _ ⟨endpoint e.val t, boundaryPoint N endpoint chart hdisj e.val t z⟩) =
        ⟨endpoint' e t, boundaryPoint N' endpoint' chart' hb' e t z⟩ := by
    exact hH₀
  let r := fun e => seamRel N endpoint chart hdisj e (attachment e)
  let K := Homeomorph.Quot.indexedRelationStep r s H
  have hrel (x y : Σ v, PuncturedFactor N' endpoint' chart' v) :
      (∃ e : {e // e ≠ s}, Relation.Map (r e.val)
        (H ∘ Quot.mk (r s)) (H ∘ Quot.mk (r s)) x y) ↔
      ∃ e : {e // e ≠ s}, seamRel N' endpoint' chart' hb' e (attachment e.val) x y := by
    apply exists_congr
    intro e
    exact map_loopSeamRel_iff N endpoint chart s hdisj attachment N' endpoint' chart' hb'
      (H ∘ Quot.mk (r s)) hH e x y
  let J := K.trans (Homeomorph.Quot.congrRight hrel)
  refine ⟨S, F, b, hb, hb', H, ?_, ?_, hH, J, fun _ => rfl⟩
  · exact hfirst
  · exact hu

end DifferentialGeometry.Topology.PairedBallGluing

end
