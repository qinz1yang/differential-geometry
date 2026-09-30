import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.PuncturedQuotient
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.QuotientTransport
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

def flagMap (p : E × Bool) (x : E3) : Σ v, (N v).Carrier :=
  ⟨endpoint p.1 p.2, (chart p.1 p.2).chart x⟩

abbrev PuncturedFactor (v : V) :=
  {x : (N v).Carrier // Sigma.mk v x ∉ ⋃ p, flagMap N endpoint chart p '' ball (0 : E3) 1}

def incidenceChart (v : V) (p : {p : E × Bool // endpoint p.1 p.2 = v}) :
    OrientedBallChart (N v).toClosedOrientedManifold :=
  p.property ▸ chart p.val.1 p.val.2

@[simp] theorem incidenceChart_sigma_apply (v : V)
    (p : {p : E × Bool // endpoint p.1 p.2 = v}) (x : E3) :
    Sigma.mk v ((incidenceChart N endpoint chart v p).chart x) =
      flagMap N endpoint chart p.val x := by
  obtain ⟨p, hp⟩ := p
  subst v
  rfl

theorem pairwise_disjoint_incidenceChart_image (v : V)
    (hdisj : Pairwise fun p q =>
      Disjoint (flagMap N endpoint chart p '' closedBall (0 : E3) 2)
        (flagMap N endpoint chart q '' closedBall (0 : E3) 2)) :
    Pairwise fun p q : {p : E × Bool // endpoint p.1 p.2 = v} =>
      Disjoint ((incidenceChart N endpoint chart v p).chart '' closedBall (0 : E3) 2)
        ((incidenceChart N endpoint chart v q).chart '' closedBall (0 : E3) 2) := by
  intro p q hpq
  rw [disjoint_left]
  rintro x ⟨y, hy, hyx⟩ ⟨z, hz, hzx⟩
  apply disjoint_left.mp (hdisj (fun h => hpq (Subtype.ext h)))
    (⟨y, hy, rfl⟩ : flagMap N endpoint chart p.val y ∈
      flagMap N endpoint chart p.val '' closedBall (0 : E3) 2)
  refine ⟨z, hz, ?_⟩
  rw [← incidenceChart_sigma_apply N endpoint chart v p,
    ← incidenceChart_sigma_apply N endpoint chart v q, hyx, hzx]

def remainingIncidenceChart (s : E) (v : V)
    (p : {p : E × Bool // p.1 ≠ s ∧ endpoint p.1 p.2 = v}) :
    OrientedBallChart (N v).toClosedOrientedManifold :=
  incidenceChart N endpoint chart v ⟨p.val, p.property.2⟩

@[simp] theorem remainingIncidenceChart_sigma_apply (s : E) (v : V)
    (p : {p : E × Bool // p.1 ≠ s ∧ endpoint p.1 p.2 = v}) (x : E3) :
    Sigma.mk v ((remainingIncidenceChart N endpoint chart s v p).chart x) =
      flagMap N endpoint chart p.val x :=
  incidenceChart_sigma_apply N endpoint chart v ⟨p.val, p.property.2⟩ x

theorem pairwise_disjoint_remainingIncidenceChart_image (s : E) (v : V)
    (hdisj : Pairwise fun p q =>
      Disjoint (flagMap N endpoint chart p '' closedBall (0 : E3) 2)
        (flagMap N endpoint chart q '' closedBall (0 : E3) 2)) :
    Pairwise fun p q : {p : E × Bool // p.1 ≠ s ∧ endpoint p.1 p.2 = v} =>
      Disjoint ((remainingIncidenceChart N endpoint chart s v p).chart '' closedBall (0 : E3) 2)
        ((remainingIncidenceChart N endpoint chart s v q).chart '' closedBall (0 : E3) 2) := by
  intro p q hpq
  exact pairwise_disjoint_incidenceChart_image N endpoint chart v hdisj
    (fun h => hpq (Subtype.ext (congrArg
      (fun z : {p : E × Bool // endpoint p.1 p.2 = v} => z.val) h)))

theorem remainingIncidenceChart_avoids_selected (s : E) (b : Bool)
    (hdisj : Pairwise fun p q =>
      Disjoint (flagMap N endpoint chart p '' closedBall (0 : E3) 2)
        (flagMap N endpoint chart q '' closedBall (0 : E3) 2))
    (p : {p : E × Bool // p.1 ≠ s ∧ endpoint p.1 p.2 = endpoint s b})
    (x : E3) (hx : x ∈ closedBall (0 : E3) 2) :
    (remainingIncidenceChart N endpoint chart s (endpoint s b) p).chart x ∉
      (chart s b).chart '' closedBall (0 : E3) 1 := by
  rintro ⟨y, hy, hyx⟩
  have hpne : p.val ≠ (s, b) := fun h => p.property.1 (congrArg Prod.fst h)
  apply disjoint_left.mp (hdisj hpne)
    (⟨x, hx, rfl⟩ : flagMap N endpoint chart p.val x ∈
      flagMap N endpoint chart p.val '' closedBall (0 : E3) 2)
  refine ⟨y, closedBall_subset_closedBall (by norm_num) hy, ?_⟩
  rw [← remainingIncidenceChart_sigma_apply N endpoint chart s (endpoint s b) p]
  exact congrArg (Sigma.mk (endpoint s b)) hyx

theorem selected_holes_iff (s : E) (b : Bool)
    (hends : endpoint s false ≠ endpoint s true) (x : (N (endpoint s b)).Carrier) :
    Sigma.mk (endpoint s b) x ∈ ⋃ p, flagMap N endpoint chart p '' ball (0 : E3) 1 ↔
      x ∈ (chart s b).chart '' ball (0 : E3) 1 ∨
        x ∈ ⋃ p, (remainingIncidenceChart N endpoint chart s (endpoint s b) p).chart ''
          ball (0 : E3) 1 := by
  have hinj : Function.Injective (fun x : (N (endpoint s b)).Carrier =>
      (⟨endpoint s b, x⟩ : Σ v, (N v).Carrier)) := by
    intro x y h
    cases h
    rfl
  constructor
  · intro hx
    obtain ⟨p, y, hy, hyx⟩ := mem_iUnion.mp hx
    have hpv : endpoint p.1 p.2 = endpoint s b := congrArg Sigma.fst hyx
    by_cases hps : p.1 = s
    · have hpb : p.2 = b := by
        obtain ⟨t, t'⟩ := p
        dsimp at hps hpv ⊢
        subst t
        cases t' <;> cases b <;> simp_all
      have hp : p = (s, b) := Prod.ext hps hpb
      subst p
      exact Or.inl ⟨y, hy, hinj hyx⟩
    · refine Or.inr (mem_iUnion.mpr ⟨⟨p, hps, hpv⟩, y, hy, ?_⟩)
      apply hinj
      exact (remainingIncidenceChart_sigma_apply N endpoint chart s (endpoint s b)
        ⟨p, hps, hpv⟩ y).trans hyx
  · rintro (⟨y, hy, rfl⟩ | hx)
    · exact mem_iUnion.mpr ⟨(s, b), y, hy, rfl⟩
    · obtain ⟨p, y, hy, hyx⟩ := mem_iUnion.mp hx
      refine mem_iUnion.mpr ⟨p.val, y, hy, ?_⟩
      exact (remainingIncidenceChart_sigma_apply N endpoint chart s (endpoint s b) p y).symm.trans
        (congrArg (Sigma.mk (endpoint s b)) hyx)

def selectedPuncturedFactorHomeomorph (s : E) (b : Bool)
    (hends : endpoint s false ≠ endpoint s true) :
    PuncturedFactor N endpoint chart (endpoint s b) ≃ₜ
      {x : (chart s b).Punctured // x.val ∉
        ⋃ p, (remainingIncidenceChart N endpoint chart s (endpoint s b) p).chart ''
          ball (0 : E3) 1} where
  toFun x := ⟨⟨x.val, fun h => x.property
      ((selected_holes_iff N endpoint chart s b hends x.val).mpr (Or.inl h))⟩,
    fun h => x.property
      ((selected_holes_iff N endpoint chart s b hends x.val).mpr (Or.inr h))⟩
  invFun x := ⟨x.val.val, fun h =>
    ((selected_holes_iff N endpoint chart s b hends x.val.val).mp h).elim
      x.val.property x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

@[simp] theorem selectedPuncturedFactorHomeomorph_apply_val (s : E) (b : Bool)
    (hends : endpoint s false ≠ endpoint s true)
    (x : PuncturedFactor N endpoint chart (endpoint s b)) :
    (selectedPuncturedFactorHomeomorph N endpoint chart s b hends x).val.val = x.val := rfl

@[simp] theorem selectedPuncturedFactorHomeomorph_symm_apply_val (s : E) (b : Bool)
    (hends : endpoint s false ≠ endpoint s true)
    (x : {x : (chart s b).Punctured // x.val ∉
      ⋃ p, (remainingIncidenceChart N endpoint chart s (endpoint s b) p).chart ''
        ball (0 : E3) 1}) :
    ((selectedPuncturedFactorHomeomorph N endpoint chart s b hends).symm x).val = x.val.val := rfl

theorem boundary_not_mem_holes
    (hdisj : Pairwise fun p q =>
      Disjoint (flagMap N endpoint chart p '' closedBall (0 : E3) 2)
        (flagMap N endpoint chart q '' closedBall (0 : E3) 2))
    (e : E) (b : Bool) (z : sphere (0 : E3) 1) :
    flagMap N endpoint chart (e, b) z ∉
      ⋃ p, flagMap N endpoint chart p '' ball (0 : E3) 1 := by
  intro hz
  obtain ⟨p, y, hy, hyz⟩ := mem_iUnion.mp hz
  by_cases hp : p = (e, b)
  · subst p
    have hinj : Function.Injective (fun x : (N (endpoint e b)).Carrier =>
        (⟨endpoint e b, x⟩ : Σ v, (N v).Carrier)) := by
      intro x y h
      cases h
      rfl
    exact (chart e b).boundaryMap z |>.property ⟨y, hy, hinj hyz⟩
  · exact disjoint_left.mp (hdisj hp)
      ⟨y, ball_subset_closedBall.trans (closedBall_subset_closedBall (by norm_num)) hy, hyz⟩
      ⟨z, sphere_subset_closedBall.trans (closedBall_subset_closedBall (by norm_num)) z.property,
        rfl⟩

def boundaryPoint
    (hdisj : Pairwise fun p q =>
      Disjoint (flagMap N endpoint chart p '' closedBall (0 : E3) 2)
        (flagMap N endpoint chart q '' closedBall (0 : E3) 2))
    (e : E) (b : Bool) (z : sphere (0 : E3) 1) :
    PuncturedFactor N endpoint chart (endpoint e b) :=
  ⟨(chart e b).chart z, boundary_not_mem_holes N endpoint chart hdisj e b z⟩

@[simp] theorem boundaryPoint_val
    (hdisj : Pairwise fun p q =>
      Disjoint (flagMap N endpoint chart p '' closedBall (0 : E3) 2)
        (flagMap N endpoint chart q '' closedBall (0 : E3) 2))
    (e : E) (b : Bool) (z : sphere (0 : E3) 1) :
    (boundaryPoint N endpoint chart hdisj e b z).val = (chart e b).chart z := rfl

theorem continuous_boundaryPoint
    (hdisj : Pairwise fun p q =>
      Disjoint (flagMap N endpoint chart p '' closedBall (0 : E3) 2)
        (flagMap N endpoint chart q '' closedBall (0 : E3) 2))
    (e : E) (b : Bool) : Continuous (boundaryPoint N endpoint chart hdisj e b) :=
  ((chart e b).continuous_boundaryMap.subtype_val).subtype_mk _

def seamRel
    (hdisj : Pairwise fun p q =>
      Disjoint (flagMap N endpoint chart p '' closedBall (0 : E3) 2)
        (flagMap N endpoint chart q '' closedBall (0 : E3) 2))
    (s : E) (a : BoundaryAttachment)
    (x y : Σ v, PuncturedFactor N endpoint chart v) : Prop :=
  ∃ z : sphere (0 : E3) 1,
    (x = ⟨endpoint s false, boundaryPoint N endpoint chart hdisj s false z⟩ ∧
      y = ⟨endpoint s true, boundaryPoint N endpoint chart hdisj s true (a.1 z)⟩) ∨
    (y = ⟨endpoint s false, boundaryPoint N endpoint chart hdisj s false z⟩ ∧
      x = ⟨endpoint s true, boundaryPoint N endpoint chart hdisj s true (a.1 z)⟩)

private theorem boundaryPoint_cast_sigma
    (hdisj : Pairwise fun p q =>
      Disjoint (flagMap N endpoint chart p '' closedBall (0 : E3) 2)
        (flagMap N endpoint chart q '' closedBall (0 : E3) 2))
    (v : V) (p : E × Bool) (hp : endpoint p.1 p.2 = v) (z : sphere (0 : E3) 1) :
    (⟨v, hp ▸ boundaryPoint N endpoint chart hdisj p.1 p.2 z⟩ :
      Σ v, PuncturedFactor N endpoint chart v) =
        ⟨endpoint p.1 p.2, boundaryPoint N endpoint chart hdisj p.1 p.2 z⟩ := by
  subst v
  rfl

private theorem boundaryPoint_cast_val
    (hdisj : Pairwise fun p q =>
      Disjoint (flagMap N endpoint chart p '' closedBall (0 : E3) 2)
        (flagMap N endpoint chart q '' closedBall (0 : E3) 2))
    (v : V) (p : E × Bool) (hp : endpoint p.1 p.2 = v) (z : sphere (0 : E3) 1) :
    (hp ▸ boundaryPoint N endpoint chart hdisj p.1 p.2 z).val =
      (incidenceChart N endpoint chart v ⟨p, hp⟩).chart z := by
  subst v
  rfl

theorem exists_seam_quotient_homeomorph
    (hdisj : Pairwise fun p q =>
      Disjoint (flagMap N endpoint chart p '' closedBall (0 : E3) 2)
        (flagMap N endpoint chart q '' closedBall (0 : E3) 2))
    (s : E) (a : BoundaryAttachment) (hends : endpoint s false ≠ endpoint s true) :
    let L := {p : E × Bool // p.1 ≠ s ∧ endpoint p.1 p.2 = endpoint s false}
    let R := {p : E × Bool // p.1 ≠ s ∧ endpoint p.1 p.2 = endpoint s true}
    let CS := smoothConnectedSum (N (endpoint s false)) (N (endpoint s true))
      (chart s false) (chart s true) a
    ∃ b : L ⊕ R → OrientedBallChart CS.toConnectedClosedOrientedManifold.toClosedOrientedManifold,
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
      (Pairwise fun p q => Disjoint ((b p).chart '' closedBall (0 : E3) 2)
        ((b q).chart '' closedBall (0 : E3) 2)) ∧
      ∃ H : Quot (seamRel N endpoint chart hdisj s a) ≃ₜ
          {q : CS.toConnectedClosedOrientedManifold.Carrier //
            q ∉ ⋃ p, (b p).chart '' ball (0 : E3) 1} ⊕
          (Σ v : {v // v ≠ endpoint s false ∧ v ≠ endpoint s true},
            PuncturedFactor N endpoint chart v.val),
        (∀ x : PuncturedFactor N endpoint chart (endpoint s false),
          ∃ y, H (Quot.mk _ ⟨endpoint s false, x⟩) = Sum.inl y ∧
            y.val = ConnectedSumQuotient.inl (chart s false).toBallChart
              (chart s true).toBallChart a.1.toHomeomorph
              (selectedPuncturedFactorHomeomorph N endpoint chart s false hends x).val) ∧
        (∀ x : PuncturedFactor N endpoint chart (endpoint s true),
          ∃ y, H (Quot.mk _ ⟨endpoint s true, x⟩) = Sum.inl y ∧
            y.val = ConnectedSumQuotient.inr (chart s false).toBallChart
              (chart s true).toBallChart a.1.toHomeomorph
              (selectedPuncturedFactorHomeomorph N endpoint chart s true hends x).val) ∧
        (∀ (v : {v // v ≠ endpoint s false ∧ v ≠ endpoint s true})
          (x : PuncturedFactor N endpoint chart v.val),
          H (Quot.mk _ ⟨v.val, x⟩) = Sum.inr ⟨v, x⟩) ∧
        (∀ (p : L) (z : sphere (0 : E3) 1),
          ∃ y, H (Quot.mk _ ⟨endpoint p.val.1 p.val.2,
            boundaryPoint N endpoint chart hdisj p.val.1 p.val.2 z⟩) = Sum.inl y ∧
              y.val = (b (Sum.inl p)).chart z) ∧
        (∀ (p : R) (z : sphere (0 : E3) 1),
          ∃ y, H (Quot.mk _ ⟨endpoint p.val.1 p.val.2,
            boundaryPoint N endpoint chart hdisj p.val.1 p.val.2 z⟩) = Sum.inl y ∧
              y.val = (b (Sum.inr p)).chart z) := by
  dsimp only
  let c := chart s false
  let d := chart s true
  let eL := remainingIncidenceChart N endpoint chart s (endpoint s false)
  let eR := remainingIncidenceChart N endpoint chart s (endpoint s true)
  obtain ⟨b, hbL, hbR, hbdisj, _, _, l, r, hl, hr, H, hHL, hHR⟩ :=
    ConnectedSumQuotient.exists_orientedBallChart_sum_family_complement_homeomorph c d a eL eR
      (remainingIncidenceChart_avoids_selected N endpoint chart s false hdisj)
      (remainingIncidenceChart_avoids_selected N endpoint chart s true hdisj)
      (pairwise_disjoint_remainingIncidenceChart_image N endpoint chart s (endpoint s false) hdisj)
      (pairwise_disjoint_remainingIncidenceChart_image N endpoint chart s (endpoint s true) hdisj)
  let B := boundaryPoint N endpoint chart hdisj s false
  let D := boundaryPoint N endpoint chart hdisj s true ∘ a.1
  let EL := selectedPuncturedFactorHomeomorph N endpoint chart s false hends
  let ER := selectedPuncturedFactorHomeomorph N endpoint chart s true hends
  have hEL (z : sphere (0 : E3) 1) : EL (B z) = l z := by
    apply Subtype.ext
    exact (hl z).symm
  have hER (z : sphere (0 : E3) 1) : ER (D z) = (r ∘ a.1) z := by
    apply Subtype.ext
    exact (hr (a.1 z)).symm
  let J := adjunctionSpaceHomeomorphOfHomeomorph B D l (r ∘ a.1)
    (Homeomorph.refl _) EL ER hEL hER
  let K := (Homeomorph.sigmaAdjunction (PuncturedFactor N endpoint chart)
      (endpoint s false) (endpoint s true) hends B D).trans
    (Homeomorph.sumCongr (J.trans H) (Homeomorph.refl _))
  have hKL (x : PuncturedFactor N endpoint chart (endpoint s false)) :
      ∃ y, K (Quot.mk _ ⟨endpoint s false, x⟩) = Sum.inl y ∧
        y.val = ConnectedSumQuotient.inl c.toBallChart d.toBallChart a.1.toHomeomorph
          (EL x).val := by
    refine ⟨H (adjunctionCell l (r ∘ a.1) (EL x)), ?_, hHL (EL x)⟩
    change (Homeomorph.sumCongr (J.trans H) (Homeomorph.refl _))
      (Homeomorph.sigmaAdjunction (PuncturedFactor N endpoint chart)
        (endpoint s false) (endpoint s true) hends B D (Quot.mk _ ⟨endpoint s false, x⟩)) = _
    rw [Homeomorph.sigmaAdjunction_mk_left]
    rfl
  have hKR (x : PuncturedFactor N endpoint chart (endpoint s true)) :
      ∃ y, K (Quot.mk _ ⟨endpoint s true, x⟩) = Sum.inl y ∧
        y.val = ConnectedSumQuotient.inr c.toBallChart d.toBallChart a.1.toHomeomorph
          (ER x).val := by
    refine ⟨H (adjunctionLower (i := l) (r ∘ a.1) (ER x)), ?_, hHR (ER x)⟩
    change (Homeomorph.sumCongr (J.trans H) (Homeomorph.refl _))
      (Homeomorph.sigmaAdjunction (PuncturedFactor N endpoint chart)
        (endpoint s false) (endpoint s true) hends B D (Quot.mk _ ⟨endpoint s true, x⟩)) = _
    rw [Homeomorph.sigmaAdjunction_mk_right]
    rfl
  have hKU (v : {v // v ≠ endpoint s false ∧ v ≠ endpoint s true})
      (x : PuncturedFactor N endpoint chart v.val) :
      K (Quot.mk _ ⟨v.val, x⟩) = Sum.inr ⟨v, x⟩ := by
    change (Homeomorph.sumCongr (J.trans H) (Homeomorph.refl _))
      (Homeomorph.sigmaAdjunction (PuncturedFactor N endpoint chart)
        (endpoint s false) (endpoint s true) hends B D (Quot.mk _ ⟨v.val, x⟩)) = _
    rw [Homeomorph.sigmaAdjunction_mk_remaining]
    rfl
  refine ⟨b, hbL, hbR, hbdisj, K, hKL, hKR, hKU, ?_, ?_⟩
  · intro p z
    let x : PuncturedFactor N endpoint chart (endpoint s false) :=
      p.property.2 ▸ boundaryPoint N endpoint chart hdisj p.val.1 p.val.2 z
    have hxSigma : (⟨endpoint s false, x⟩ : Σ v, PuncturedFactor N endpoint chart v) =
        ⟨endpoint p.val.1 p.val.2, boundaryPoint N endpoint chart hdisj p.val.1 p.val.2 z⟩ := by
      exact boundaryPoint_cast_sigma N endpoint chart hdisj (endpoint s false)
        p.val p.property.2 z
    have hxVal : x.val = (eL p).chart z := by
      exact boundaryPoint_cast_val N endpoint chart hdisj (endpoint s false)
        p.val p.property.2 z
    obtain ⟨y, hy, hyVal⟩ := hKL x
    refine ⟨y, ?_, ?_⟩
    · exact (congrArg (fun q => K (Quot.mk _ q)) hxSigma).symm.trans hy
    · obtain ⟨hx, hb⟩ := hbL p z
        (sphere_subset_closedBall.trans (closedBall_subset_closedBall (by norm_num)) z.property)
      refine hyVal.trans ((congrArg (ConnectedSumQuotient.inl c.toBallChart d.toBallChart
        a.1.toHomeomorph) (Subtype.ext hxVal)).trans hb.symm)
  · intro p z
    let x : PuncturedFactor N endpoint chart (endpoint s true) :=
      p.property.2 ▸ boundaryPoint N endpoint chart hdisj p.val.1 p.val.2 z
    have hxSigma : (⟨endpoint s true, x⟩ : Σ v, PuncturedFactor N endpoint chart v) =
        ⟨endpoint p.val.1 p.val.2, boundaryPoint N endpoint chart hdisj p.val.1 p.val.2 z⟩ := by
      exact boundaryPoint_cast_sigma N endpoint chart hdisj (endpoint s true)
        p.val p.property.2 z
    have hxVal : x.val = (eR p).chart z := by
      exact boundaryPoint_cast_val N endpoint chart hdisj (endpoint s true)
        p.val p.property.2 z
    obtain ⟨y, hy, hyVal⟩ := hKR x
    refine ⟨y, ?_, ?_⟩
    · exact (congrArg (fun q => K (Quot.mk _ q)) hxSigma).symm.trans hy
    · obtain ⟨hx, hb⟩ := hbR p z
        (sphere_subset_closedBall.trans (closedBall_subset_closedBall (by norm_num)) z.property)
      refine hyVal.trans ((congrArg (ConnectedSumQuotient.inr c.toBallChart d.toBallChart
        a.1.toHomeomorph) (Subtype.ext hxVal)).trans hb.symm)

end DifferentialGeometry.Topology.PairedBallGluing
