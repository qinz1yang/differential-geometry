import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.FactorBallImage
import DifferentialGeometry.Topology.Attachment.AdjunctionHomeomorph
import Mathlib.Topology.ContinuousMap.Basic

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.ConnectedSumQuotient

universe u v

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

variable {M : ConnectedClosedOrientedManifold.{u} 3}
  {N : ConnectedClosedOrientedManifold.{v} 3}
  (c : OrientedBallChart M.toClosedOrientedManifold)
  (d : OrientedBallChart N.toClosedOrientedManifold) (a : BoundaryAttachment)

private theorem exists_restricted_sum_quotientMap
    (A : Set M.Carrier) (B : Set N.Carrier)
    (hA : IsOpen A) (hB : IsOpen B)
    (U : Set (ConnectedSumQuotient c.toBallChart d.toBallChart a.1.toHomeomorph))
    (hL : (inl c.toBallChart d.toBallChart a.1.toHomeomorph) ⁻¹' U =
      {x : c.Punctured | x.val ∈ A})
    (hR : (inr c.toBallChart d.toBallChart a.1.toHomeomorph) ⁻¹' U =
      {x : d.Punctured | x.val ∈ B}) :
    ∃ F : C(({x : c.Punctured | x.val ∉ A} ⊕ {x : d.Punctured | x.val ∉ B}), ↥(Uᶜ)),
      (∀ x, (F (Sum.inl x)).val = inl c.toBallChart d.toBallChart a.1.toHomeomorph x.val) ∧
      (∀ y, (F (Sum.inr y)).val = inr c.toBallChart d.toBallChart a.1.toHomeomorph y.val) ∧
      _root_.Topology.IsQuotientMap F := by
  let L := {x : c.Punctured | x.val ∉ A}
  let R := {x : d.Punctured | x.val ∉ B}
  have hlc : IsClosed L := (hA.preimage continuous_subtype_val).isClosed_compl
  have hrc : IsClosed R := (hB.preimage continuous_subtype_val).isClosed_compl
  let : CompactSpace L := isCompact_iff_compactSpace.mp hlc.isCompact
  let : CompactSpace R := isCompact_iff_compactSpace.mp hrc.isCompact
  have hl (x : L) : inl c.toBallChart d.toBallChart a.1.toHomeomorph x.val ∈ Uᶜ := by
    intro hx
    exact x.property ((Set.ext_iff.mp hL x.val).mp hx)
  have hr (y : R) : inr c.toBallChart d.toBallChart a.1.toHomeomorph y.val ∈ Uᶜ := by
    intro hy
    exact y.property ((Set.ext_iff.mp hR y.val).mp hy)
  let F : C(L ⊕ R, ↥(Uᶜ)) :=
    { toFun := Sum.elim
        (fun x => ⟨inl c.toBallChart d.toBallChart a.1.toHomeomorph x.val, hl x⟩)
        (fun y => ⟨inr c.toBallChart d.toBallChart a.1.toHomeomorph y.val, hr y⟩)
      continuous_toFun := Continuous.sumElim
        (((continuous_inl c.toBallChart d.toBallChart a.1.toHomeomorph).comp
          continuous_subtype_val).subtype_mk hl)
        (((continuous_inr c.toBallChart d.toBallChart a.1.toHomeomorph).comp
          continuous_subtype_val).subtype_mk hr) }
  have hsurj : Function.Surjective F := by
    intro z
    rcases jointly_surjective c.toBallChart d.toBallChart a.1.toHomeomorph z.val with
      ⟨x, hx⟩ | ⟨y, hy⟩
    · have hxA : x.val ∉ A := by
        intro hm
        exact z.property (hx ▸ (Set.ext_iff.mp hL x).mpr hm)
      exact ⟨Sum.inl ⟨x, hxA⟩, Subtype.ext hx⟩
    · have hyB : y.val ∉ B := by
        intro hm
        exact z.property (hy ▸ (Set.ext_iff.mp hR y).mpr hm)
      exact ⟨Sum.inr ⟨y, hyB⟩, Subtype.ext hy⟩
  exact ⟨F, fun _ => rfl, fun _ => rfl, F.continuous.isClosedMap.isQuotientMap F.continuous hsurj⟩

private theorem exists_orientedBallChart_sum_family_with_complement_quotient {ι κ : Type*}
    (e : ι → OrientedBallChart M.toClosedOrientedManifold)
    (f : κ → OrientedBallChart N.toClosedOrientedManifold)
    (hec : ∀ i x, x ∈ closedBall (0 : E3) 2 →
      (e i).chart x ∉ c.chart '' closedBall (0 : E3) 1)
    (hfd : ∀ i x, x ∈ closedBall (0 : E3) 2 →
      (f i).chart x ∉ d.chart '' closedBall (0 : E3) 1)
    (he : Pairwise fun i j => Disjoint ((e i).chart '' closedBall (0 : E3) 2)
      ((e j).chart '' closedBall (0 : E3) 2))
    (hf : Pairwise fun i j => Disjoint ((f i).chart '' closedBall (0 : E3) 2)
      ((f j).chart '' closedBall (0 : E3) 2)) :
    ∃ b : ι ⊕ κ → OrientedBallChart
        (smoothConnectedSum M N c d a).toConnectedClosedOrientedManifold.toClosedOrientedManifold,
      (∀ i x, x ∈ closedBall (0 : E3) 2 →
        ∃ hx : (e i).chart x ∉ c.chart '' ball (0 : E3) 1,
          (b (Sum.inl i)).chart x = inl c.toBallChart d.toBallChart a.1.toHomeomorph
            ⟨(e i).chart x, hx⟩) ∧
      (∀ i x, x ∈ closedBall (0 : E3) 2 →
        ∃ hx : (f i).chart x ∉ d.chart '' ball (0 : E3) 1,
          (b (Sum.inr i)).chart x = inr c.toBallChart d.toBallChart a.1.toHomeomorph
            ⟨(f i).chart x, hx⟩) ∧
      (Pairwise fun i j => Disjoint ((b i).chart '' closedBall (0 : E3) 2)
        ((b j).chart '' closedBall (0 : E3) 2)) ∧
      (∀ (S : Set E3), S ⊆ closedBall (0 : E3) 2 →
        (inl c.toBallChart d.toBallChart a.1.toHomeomorph) ⁻¹'
            (⋃ i, (b i).chart '' S) =
          {x : c.Punctured | x.val ∈ ⋃ i, (e i).chart '' S}) ∧
      (∀ (S : Set E3), S ⊆ closedBall (0 : E3) 2 →
        (inr c.toBallChart d.toBallChart a.1.toHomeomorph) ⁻¹'
            (⋃ i, (b i).chart '' S) =
          {x : d.Punctured | x.val ∈ ⋃ i, (f i).chart '' S}) ∧
      ∃ F : C(({x : c.Punctured | x.val ∉ ⋃ i, (e i).chart '' ball (0 : E3) 1} ⊕
          {x : d.Punctured | x.val ∉ ⋃ i, (f i).chart '' ball (0 : E3) 1}),
          {x : ConnectedSumQuotient c.toBallChart d.toBallChart a.1.toHomeomorph |
            x ∉ ⋃ i, (b i).chart '' ball (0 : E3) 1}),
        (∀ x, (F (Sum.inl x)).val = inl c.toBallChart d.toBallChart a.1.toHomeomorph x.val) ∧
        (∀ y, (F (Sum.inr y)).val = inr c.toBallChart d.toBallChart a.1.toHomeomorph y.val) ∧
        (∀ x y, F (Sum.inl x) = F (Sum.inl y) ↔ x = y) ∧
        (∀ x y, F (Sum.inr x) = F (Sum.inr y) ↔ x = y) ∧
        (∀ x y, F (Sum.inl x) = F (Sum.inr y) ↔
          ∃ z, c.boundaryMap z = x.val ∧ d.boundaryMap (a.1 z) = y.val) ∧
        _root_.Topology.IsQuotientMap F := by
  obtain ⟨b, hbL, hbR, hbdisj, hL, hR⟩ :=
    exists_orientedBallChart_sum_family_preimage c d a e f hec hfd he hf
  have hball : ball (0 : E3) 1 ⊆ closedBall (0 : E3) 2 :=
    ball_subset_closedBall.trans (closedBall_subset_closedBall (by norm_num))
  obtain ⟨F, hFL, hFR, hquot⟩ := exists_restricted_sum_quotientMap c d a
    (⋃ i, (e i).chart '' ball (0 : E3) 1) (⋃ i, (f i).chart '' ball (0 : E3) 1)
    (isOpen_iUnion fun i => (e i).toBallChart.isOpen_chart_image_ball)
    (isOpen_iUnion fun i => (f i).toBallChart.isOpen_chart_image_ball)
    (⋃ i, (b i).chart '' ball (0 : E3) 1) (hL _ hball) (hR _ hball)
  refine ⟨b, hbL, hbR, hbdisj, hL, hR, F, hFL, hFR, ?_, ?_, ?_, hquot⟩
  · intro x y
    constructor
    · intro h
      apply Subtype.ext
      apply inl_injective c.toBallChart d.toBallChart a.1.toHomeomorph
      exact (hFL x).symm.trans ((congrArg Subtype.val h).trans (hFL y))
    · rintro rfl
      rfl
  · intro x y
    constructor
    · intro h
      apply Subtype.ext
      apply inr_injective c.toBallChart d.toBallChart a.1.toHomeomorph
      exact (hFR x).symm.trans ((congrArg Subtype.val h).trans (hFR y))
    · rintro rfl
      rfl
  · intro x y
    constructor
    · intro h
      apply (inl_eq_inr_iff c.toBallChart d.toBallChart a.1.toHomeomorph x.val y.val).mp
      exact (hFL x).symm.trans ((congrArg Subtype.val h).trans (hFR y))
    · intro h
      apply Subtype.ext
      exact (hFL x).trans
        (((inl_eq_inr_iff c.toBallChart d.toBallChart a.1.toHomeomorph x.val y.val).mpr h).trans
          (hFR y).symm)

theorem exists_orientedBallChart_sum_family_complement_homeomorph {ι κ : Type*}
    (e : ι → OrientedBallChart M.toClosedOrientedManifold)
    (f : κ → OrientedBallChart N.toClosedOrientedManifold)
    (hec : ∀ i x, x ∈ closedBall (0 : E3) 2 →
      (e i).chart x ∉ c.chart '' closedBall (0 : E3) 1)
    (hfd : ∀ i x, x ∈ closedBall (0 : E3) 2 →
      (f i).chart x ∉ d.chart '' closedBall (0 : E3) 1)
    (he : Pairwise fun i j => Disjoint ((e i).chart '' closedBall (0 : E3) 2)
      ((e j).chart '' closedBall (0 : E3) 2))
    (hf : Pairwise fun i j => Disjoint ((f i).chart '' closedBall (0 : E3) 2)
      ((f j).chart '' closedBall (0 : E3) 2)) :
    ∃ b : ι ⊕ κ → OrientedBallChart
        (smoothConnectedSum M N c d a).toConnectedClosedOrientedManifold.toClosedOrientedManifold,
      (∀ i x, x ∈ closedBall (0 : E3) 2 →
        ∃ hx : (e i).chart x ∉ c.chart '' ball (0 : E3) 1,
          (b (Sum.inl i)).chart x = inl c.toBallChart d.toBallChart a.1.toHomeomorph
            ⟨(e i).chart x, hx⟩) ∧
      (∀ i x, x ∈ closedBall (0 : E3) 2 →
        ∃ hx : (f i).chart x ∉ d.chart '' ball (0 : E3) 1,
          (b (Sum.inr i)).chart x = inr c.toBallChart d.toBallChart a.1.toHomeomorph
            ⟨(f i).chart x, hx⟩) ∧
      (Pairwise fun i j => Disjoint ((b i).chart '' closedBall (0 : E3) 2)
        ((b j).chart '' closedBall (0 : E3) 2)) ∧
      (∀ (S : Set E3), S ⊆ closedBall (0 : E3) 2 →
        (inl c.toBallChart d.toBallChart a.1.toHomeomorph) ⁻¹'
            (⋃ i, (b i).chart '' S) =
          {x : c.Punctured | x.val ∈ ⋃ i, (e i).chart '' S}) ∧
      (∀ (S : Set E3), S ⊆ closedBall (0 : E3) 2 →
        (inr c.toBallChart d.toBallChart a.1.toHomeomorph) ⁻¹'
            (⋃ i, (b i).chart '' S) =
          {x : d.Punctured | x.val ∈ ⋃ i, (f i).chart '' S}) ∧
      ∃ (l : C(sphere (0 : E3) 1,
          {x : c.Punctured | x.val ∉ ⋃ i, (e i).chart '' ball (0 : E3) 1}))
        (r : C(sphere (0 : E3) 1,
          {x : d.Punctured | x.val ∉ ⋃ i, (f i).chart '' ball (0 : E3) 1})),
        (∀ z, (l z).val = c.boundaryMap z) ∧
        (∀ z, (r z).val = d.boundaryMap z) ∧
        ∃ H : AdjunctionSpace l (r ∘ a.1) ≃ₜ
            {x : ConnectedSumQuotient c.toBallChart d.toBallChart a.1.toHomeomorph |
              x ∉ ⋃ i, (b i).chart '' ball (0 : E3) 1},
          (∀ x, (H (adjunctionCell l (r ∘ a.1) x)).val =
            inl c.toBallChart d.toBallChart a.1.toHomeomorph x.val) ∧
          (∀ y, (H (adjunctionLower (i := l) (r ∘ a.1) y)).val =
            inr c.toBallChart d.toBallChart a.1.toHomeomorph y.val) := by
  obtain ⟨b, hbL, hbR, hbdisj, hL, hR, F, hFL, hFR, hLL, hRR, hLR, hquot⟩ :=
    exists_orientedBallChart_sum_family_with_complement_quotient c d a e f hec hfd he hf
  let L := {x : c.Punctured | x.val ∉ ⋃ i, (e i).chart '' ball (0 : E3) 1}
  let R := {x : d.Punctured | x.val ∉ ⋃ i, (f i).chart '' ball (0 : E3) 1}
  have hball : ball (0 : E3) 1 ⊆ closedBall (0 : E3) 2 :=
    ball_subset_closedBall.trans (closedBall_subset_closedBall (by norm_num))
  have hl (z : sphere (0 : E3) 1) : c.boundaryMap z ∈ L := by
    intro hz
    obtain ⟨i, x, hx, hxeq⟩ := mem_iUnion.mp hz
    exact hec i x (hball hx) ⟨z, sphere_subset_closedBall z.property, hxeq.symm⟩
  have hr (z : sphere (0 : E3) 1) : d.boundaryMap z ∈ R := by
    intro hz
    obtain ⟨i, x, hx, hxeq⟩ := mem_iUnion.mp hz
    exact hfd i x (hball hx) ⟨z, sphere_subset_closedBall z.property, hxeq.symm⟩
  let l : C(sphere (0 : E3) 1, L) :=
    ⟨fun z => ⟨c.boundaryMap z, hl z⟩, c.continuous_boundaryMap.subtype_mk hl⟩
  let r : C(sphere (0 : E3) 1, R) :=
    ⟨fun z => ⟨d.boundaryMap z, hr z⟩, d.continuous_boundaryMap.subtype_mk hr⟩
  have hcross (x : L) (y : R) : F (Sum.inl x) = F (Sum.inr y) ↔
      ∃ z, l z = x ∧ (r ∘ a.1) z = y := by
    constructor
    · intro h
      obtain ⟨z, hz, hz'⟩ := (hLR x y).mp h
      exact ⟨z, Subtype.ext hz, Subtype.ext hz'⟩
    · rintro ⟨z, hz, hz'⟩
      exact (hLR x y).mpr ⟨z, congrArg Subtype.val hz, congrArg Subtype.val hz'⟩
  let H := adjunctionHomeomorphOfFibers l (r ∘ a.1) F hquot
    (fun x y h => (hLL x y).mp h) (fun x y h => (hRR x y).mp h) hcross
  exact ⟨b, hbL, hbR, hbdisj, hL, hR, l, r, fun _ => rfl, fun _ => rfl,
    H, hFL, hFR⟩

end DifferentialGeometry.Topology.ConnectedSumQuotient
