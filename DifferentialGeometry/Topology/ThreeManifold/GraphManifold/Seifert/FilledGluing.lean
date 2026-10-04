import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.FilledCarrier
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Sphere

/-!
# Gluing the filling solid torus into the pants

Chapter 6, packet K06c, third part. The matching is `linearTorusDiffeomorph` of
`!![-p, a; -q, b]` (`matching`), whose inverse `!![-b, a; -q, p]` is the angular part of
`coneLift` on the outward collar of the hole about `3/2` (`coneLift_productCollar`). Both the
collar of the solid torus and the collar of the hole are then restrictions of the single signed
map `seamPoint (t, s) = (seamRadius p s t₁, t₂)` (`solidCollar_val_eq`,
`coneLift_productCollar_matching`). The boundary gluing `gluing` of `FilledCut` identifies the
solid-torus side `leftTorus t` with `rightTorus (matching t)`; the fold identifies exactly the
glued points (`filledFold_eq_iff_rel`) and is onto, so it descends to `filledReconstruction`. The
cut carrier has two pieces (`filledComponents`), its boundary is the two sides of the seam and the
two free tori `cutExternal` (`cut_boundary`), and the boundary of the filled carrier is the image of
the free tori `external` (`filled_boundary`), carried by `outerLift`, the restriction of
`coneLift` away from the filled hole. The seam is `seam`, and `filledInteriorDiffeomorph`
identifies the interior of the cut carrier with the complement of the boundary and the seam torus.
-/

set_option autoImplicit false

noncomputable section
open Set Metric Function Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology ComplexConjugate

universe u

namespace GC.Seifert

namespace ConeFilling

variable (c : ConeFilling)

def reflectMatrix : Matrix (Fin 2) (Fin 2) ℤ := !![-1, 0; 0, 1]

def portMatrix : Matrix (Fin 2) (Fin 2) ℤ := c.liftMatrix * reflectMatrix

def matchingMatrix : Matrix (Fin 2) (Fin 2) ℤ := reflectMatrix * c.chartMatrix

theorem reflectMatrix_mul_self : reflectMatrix * reflectMatrix = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [reflectMatrix, Matrix.mul_apply, Fin.sum_univ_two]

theorem portMatrix_mul_matchingMatrix : c.portMatrix * c.matchingMatrix = 1 := by
  rw [portMatrix, matchingMatrix, Matrix.mul_assoc, ← Matrix.mul_assoc reflectMatrix,
    reflectMatrix_mul_self, Matrix.one_mul, liftMatrix_mul_chartMatrix]

theorem matchingMatrix_mul_portMatrix : c.matchingMatrix * c.portMatrix = 1 := by
  rw [portMatrix, matchingMatrix, Matrix.mul_assoc, ← Matrix.mul_assoc c.chartMatrix,
    chartMatrix_mul_liftMatrix, Matrix.one_mul, reflectMatrix_mul_self]

def matchingUnit : GL (Fin 2) ℤ :=
  ⟨c.matchingMatrix, c.portMatrix, c.matchingMatrix_mul_portMatrix,
    c.portMatrix_mul_matchingMatrix⟩

def matching : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus := linearTorusDiffeomorph c.matchingUnit

theorem matching_apply (t : Torus) : c.matching t = linearTorusMap c.matchingMatrix t := rfl

theorem matching_symm_apply (t : Torus) :
    c.matching.symm t = linearTorusMap c.portMatrix t := rfl

theorem linearTorusMap_port_matching (t : Torus) :
    linearTorusMap c.portMatrix (c.matching t) = t := by
  rw [matching_apply, ← linearTorusMap_mul, portMatrix_mul_matchingMatrix, linearTorusMap_one]

theorem linearTorusMap_reflect (τ : Torus) : linearTorusMap reflectMatrix τ = (τ.1⁻¹, τ.2) := by
  simp [linearTorusMap, reflectMatrix]

def seamPoint (y : Torus × ℝ) : PlaneLift.{u} × Circle :=
  (ULift.up (seamRadius c.p y.2 • (y.1.1 : ℂ)), y.1.2)

theorem norm_seamPoint {y : Torus × ℝ} (hy : -2 < y.2) :
    ‖(c.seamPoint y).1.down‖ = seamRadius c.p y.2 :=
  norm_seamRadius_smul c.p hy _

theorem norm_conePoint_seamPoint_sub {y : Torus × ℝ} (hy : -2 < y.2) :
    ‖c.conePoint (c.seamPoint y) - ((3 / 2 : ℝ) : ℂ)‖ = (1 + y.2 / 2) / 2 := by
  rw [c.norm_conePoint_sub, c.norm_seamPoint hy, div_three_pow_seamRadius c.p hy]

theorem solidCollar_val_eq (t : Torus) {h : EuclideanHalfSpace 1} (hh : (t, h) ∈ halfCollarSource) :
    (solidCollar.{u} c.p (t, h)).val = c.seamPoint (t, -h.val 0) :=
  solidCollar_apply_val c.p hh

theorem productCollar_one_sub (τ : Torus) {h : EuclideanHalfSpace 1}
    (hh : (τ, h) ∈ halfCollarSource) :
    (productCollar.{u} 3 (Or.inr rfl) 1 (τ, h)).val.1.down - ((3 / 2 : ℝ) : ℂ) =
      (1 / 2 + h.val 0 / 4 : ℝ) • ((τ.1⁻¹ : Circle) : ℂ) := by
  have h1 : (productCollar.{u} 3 (Or.inr rfl) 1 (τ, h)).val.1.down =
      planarCollarFormula 3 1 ((τ.1 : ℂ), h.val 0) :=
    planarCollar_apply_val.{u} (Or.inr rfl) 1 (p := (τ.1, h)) hh
  rw [h1, Circle.coe_inv_eq_conj]
  simp [planarCollarFormula, planarCenter, planarRadius, planarSign, planarTwist]

theorem coneLift_productCollar (τ : Torus) {h : EuclideanHalfSpace 1}
    (hh : (τ, h) ∈ halfCollarSource) :
    c.coneLift (productCollar.{u} 3 (Or.inr rfl) 1 (τ, h)).val =
      c.seamPoint (linearTorusMap c.portMatrix τ, h.val 0) := by
  have h0 : 0 ≤ h.val 0 := h.2
  have hpos : 0 < (1 / 2 + h.val 0 / 4 : ℝ) := by linarith
  have hsub := productCollar_one_sub.{u} τ hh
  have hdepth : coneDepth (productCollar.{u} 3 (Or.inr rfl) 1 (τ, h)).val = h.val 0 := by
    unfold coneDepth
    rw [hsub, norm_smul, Circle.norm_coe, mul_one, Real.norm_of_nonneg hpos.le]
    ring
  have htorus : c.coneTorus (productCollar.{u} 3 (Or.inr rfl) 1 (τ, h)).val =
      linearTorusMap c.portMatrix τ := by
    unfold coneTorus
    rw [hsub, unitOf_smul hpos, portMatrix, linearTorusMap_mul, linearTorusMap_reflect]
    rfl
  unfold coneLift seamPoint
  rw [hdepth, htorus]

theorem coneLift_productCollar_matching (t : Torus) {h : EuclideanHalfSpace 1}
    (hh : (t, h) ∈ halfCollarSource) :
    c.coneLift (productCollar.{u} 3 (Or.inr rfl) 1 (c.matching t, h)).val =
      c.seamPoint (t, h.val 0) := by
  rw [c.coneLift_productCollar (c.matching t) hh, linearTorusMap_port_matching]

instance : Nonempty (productSet.{u} 3) := ⟨productCollar 3 (Or.inr rfl) 0 (1, halfZero)⟩

instance : Nonempty c.filledSet.{u} := ⟨c.solidFold (Classical.arbitrary _)⟩

def leftCollar :
    PartialDiffeomorph halfCollarModel (𝓡∂ 3) (Torus × EuclideanHalfSpace 1) FilledCut.{u} ∞ :=
  (solidCollar c.p).trans partialDiffeomorphSumInr

def rightCollar :
    PartialDiffeomorph halfCollarModel (𝓡∂ 3) (Torus × EuclideanHalfSpace 1) FilledCut.{u} ∞ :=
  (productCollar 3 (Or.inr rfl) 1).trans partialDiffeomorphSumInl

theorem leftCollar_apply (q : Torus × EuclideanHalfSpace 1) :
    c.leftCollar.{u} q = Sum.inr (solidCollar c.p q) := rfl

theorem rightCollar_apply (q : Torus × EuclideanHalfSpace 1) :
    rightCollar.{u} q = Sum.inl (productCollar 3 (Or.inr rfl) 1 q) := rfl

theorem leftCollar_source : c.leftCollar.{u}.source = halfCollarSource := by
  change (solidCollar.{u} c.p).source ∩ _ ⁻¹' univ = _
  rw [preimage_univ, inter_univ]
  rfl

theorem rightCollar_source : rightCollar.{u}.source = halfCollarSource := by
  change (productCollar.{u} 3 (Or.inr rfl) 1).source ∩ _ ⁻¹' univ = _
  rw [preimage_univ, inter_univ]
  rfl

def leftTorus (t : Torus) : FilledCut.{u} := c.leftCollar (t, halfZero)

def rightTorus (t : Torus) : FilledCut.{u} := rightCollar (t, halfZero)

theorem continuous_leftTorus : Continuous c.leftTorus.{u} :=
  (c.leftCollar.contMDiffOn.comp_contMDiff (contMDiff_id.prodMk contMDiff_const)
    (fun t => c.leftCollar_source ▸ zero_mem_halfCollarSource t)).continuous

theorem continuous_rightTorus : Continuous rightTorus.{u} :=
  (rightCollar.contMDiffOn.comp_contMDiff (contMDiff_id.prodMk contMDiff_const)
    (fun t => rightCollar_source ▸ zero_mem_halfCollarSource t)).continuous

theorem injective_leftTorus : Injective c.leftTorus.{u} := fun t s h =>
  congrArg Prod.fst (c.leftCollar.toOpenPartialHomeomorph.injOn
    (c.leftCollar_source ▸ zero_mem_halfCollarSource t)
    (c.leftCollar_source ▸ zero_mem_halfCollarSource s) h)

theorem injective_rightTorus : Injective rightTorus.{u} := fun t s h =>
  congrArg Prod.fst (rightCollar.toOpenPartialHomeomorph.injOn
    (rightCollar_source ▸ zero_mem_halfCollarSource t)
    (rightCollar_source ▸ zero_mem_halfCollarSource s) h)

def leftParam : Torus ≃ₜ range c.leftTorus.{u} :=
  (c.continuous_leftTorus.isClosedEmbedding c.injective_leftTorus).isEmbedding.toHomeomorph

def rightParam : Torus ≃ₜ range rightTorus.{u} :=
  (continuous_rightTorus.isClosedEmbedding injective_rightTorus).isEmbedding.toHomeomorph

def attaching : range c.leftTorus.{u} ≃ₜ range rightTorus.{u} :=
  c.leftParam.symm.trans (c.matching.toHomeomorph.trans rightParam)

theorem attaching_leftParam (t : Torus) :
    c.attaching.{u} (c.leftParam t) = rightParam (c.matching t) := by
  simp [attaching]

theorem attaching_val (t : Torus) (h : c.leftTorus.{u} t ∈ range c.leftTorus) :
    (c.attaching ⟨c.leftTorus t, h⟩ : FilledCut.{u}) = rightTorus (c.matching t) := by
  have hl : (⟨c.leftTorus t, h⟩ : range c.leftTorus.{u}) = c.leftParam t := Subtype.ext rfl
  rw [hl, attaching_leftParam]
  rfl

theorem attaching_symm_val (t : Torus) (h : rightTorus.{u} t ∈ range rightTorus) :
    (c.attaching.symm ⟨rightTorus t, h⟩ : FilledCut.{u}) = c.leftTorus (c.matching.symm t) := by
  have hr : (⟨rightTorus t, h⟩ : range rightTorus.{u}) =
      c.attaching (c.leftParam (c.matching.symm t)) := by
    rw [attaching_leftParam, Diffeomorph.apply_symm_apply]
    exact Subtype.ext rfl
  rw [hr, Homeomorph.symm_apply_apply]
  rfl

def gluing : BoundaryGluing FilledCut.{u} (Fin 1) where
  left _ := range c.leftTorus
  right _ := range rightTorus
  attaching _ := c.attaching
  isClosed_left _ := isClosed_range_of_continuous_of_compactSpace c.continuous_leftTorus
  isClosed_right _ := isClosed_range_of_continuous_of_compactSpace continuous_rightTorus
  disjoint_left_right _ := by
    rw [Set.disjoint_left]
    rintro _ ⟨t, rfl⟩ ⟨s, hs⟩
    exact Sum.inl_ne_inr hs
  disjoint_blocks i j h := (h (Subsingleton.elim i j)).elim

theorem filledFold_leftTorus (t : Torus) :
    (c.filledFold (c.leftTorus.{u} t)).val = c.seamPoint (t, 0) := by
  change (solidCollar.{u} c.p (t, halfZero)).val = _
  rw [c.solidCollar_val_eq t (zero_mem_halfCollarSource t)]
  change c.seamPoint (t, -(0 : ℝ)) = _
  rw [neg_zero]

theorem filledFold_rightTorus_matching (t : Torus) :
    (c.filledFold (rightTorus.{u} (c.matching t))).val = c.seamPoint (t, 0) :=
  c.coneLift_productCollar_matching t (zero_mem_halfCollarSource _)

theorem filledFold_rightTorus (τ : Torus) :
    (c.filledFold (rightTorus.{u} τ)).val = c.seamPoint (c.matching.symm τ, 0) := by
  rw [← c.filledFold_rightTorus_matching, Diffeomorph.apply_symm_apply]

theorem gluing_rel_left_right (t : Torus) :
    c.gluing.{u}.rel (c.leftTorus t) (rightTorus (c.matching t)) := by
  refine Or.inr ⟨0, Or.inl ⟨t, rfl⟩, ?_⟩
  rw [c.gluing.flip_of_mem_left ⟨t, rfl⟩]
  exact (c.attaching_val t _).symm

theorem filledFold_eq_of_rel {x y : FilledCut.{u}} (h : c.gluing.rel x y) :
    c.filledFold x = c.filledFold y := by
  rcases h with rfl | ⟨i, hx, rfl⟩
  · rfl
  · obtain rfl : i = 0 := Subsingleton.elim i 0
    rcases hx with hx | hx
    · obtain ⟨t, rfl⟩ := id hx
      rw [c.gluing.flip_of_mem_left hx]
      change c.filledFold (c.leftTorus t) = c.filledFold (c.attaching ⟨c.leftTorus t, hx⟩ : _)
      rw [c.attaching_val t hx]
      apply Subtype.ext
      rw [filledFold_leftTorus, filledFold_rightTorus_matching]
    · obtain ⟨τ, rfl⟩ := id hx
      rw [c.gluing.flip_of_mem_right hx]
      change c.filledFold (rightTorus τ) =
        c.filledFold (c.attaching.symm ⟨rightTorus τ, hx⟩ : _)
      rw [c.attaching_symm_val τ hx]
      apply Subtype.ext
      rw [filledFold_leftTorus, filledFold_rightTorus]

theorem planarSign_one : planarSign (1 : Fin 3) = 1 := by simp [planarSign]

theorem planarCenter_one : planarCenter 3 (1 : Fin 3) = 3 / 2 := by simp [planarCenter]

theorem planarRadius_one : planarRadius (1 : Fin 3) = 1 / 2 := by simp [planarRadius]

theorem fin_three_cases (j : Fin 3) : j = 0 ∨ j = 1 ∨ j = 2 := by
  fin_cases j <;> simp

theorem productCollar_one_target {a : productSet.{u} 3}
    (ha : ‖a.val.1.down - ((3 / 2 : ℝ) : ℂ)‖ = 1 / 2) :
    a ∈ (productCollar.{u} 3 (Or.inr rfl) 1).target := by
  change planarSign (1 : Fin 3) * (‖a.val.1.down - planarCenter 3 1‖ - planarRadius (1 : Fin 3))
    < 1 / 4
  rw [planarSign_one, planarCenter_one, planarRadius_one, ha]
  norm_num

theorem exists_productCollar_one {a : productSet.{u} 3}
    (ha : ‖a.val.1.down - ((3 / 2 : ℝ) : ℂ)‖ = 1 / 2) :
    ∃ τ, productCollar.{u} 3 (Or.inr rfl) 1 (τ, halfZero) = a := by
  set P := productCollar.{u} 3 (Or.inr rfl) 1
  have hmem := productCollar_one_target ha
  have h2 : P.symm a = ((P.symm a).1, halfZero) := by
    refine Prod.ext rfl ?_
    change Manifold.halfSpaceOneLift (4 * (planarSign (1 : Fin 3) *
      (‖a.val.1.down - planarCenter 3 1‖ - planarRadius (1 : Fin 3)))) = halfZero
    rw [planarSign_one, planarCenter_one, planarRadius_one, ha, sub_self, mul_zero, mul_zero,
      ← halfPoint_eq_halfSpaceOneLift 0 le_rfl]
    rfl
  exact ⟨(P.symm a).1, by rw [← h2]; exact P.right_inv hmem⟩

theorem mem_productSet_iff (x : PlaneLift.{u} × Circle) :
    x ∈ productSet.{u} 3 ↔ x.1.down ∈ planarModel 3 :=
  mem_planarSet_iff (Or.inr rfl) x.1

theorem one_half_le_of_mem_productSet (a : productSet.{u} 3) :
    1 / 2 ≤ ‖a.val.1.down - ((3 / 2 : ℝ) : ℂ)‖ :=
  ((mem_planarModel_three _).mp ((mem_productSet_iff a.val).mp a.2)).2.1

theorem coneDepth_nonneg (a : productSet.{u} 3) : 0 ≤ coneDepth a.val := by
  have := one_half_le_of_mem_productSet a
  unfold coneDepth
  linarith

theorem gluing_rel_inl_inr {a : productSet.{u} 3} {b : solidSet.{u}}
    (h : c.coneLift a.val = b.val) : c.gluing.rel (Sum.inl a) (Sum.inr b) := by
  have hne := ne_three_halves_of_mem_productSet a
  have hd0 := coneDepth_nonneg a
  have hb := (mem_solidSet_iff b.val).mp b.2
  have hd : coneDepth a.val = 0 := by
    have h1 := c.norm_coneLift a.val hne
    rw [h] at h1
    have h2 : seamDepth c.p (seamRadius c.p (coneDepth a.val)) ≤ 0 := by
      rw [← h1]
      exact seamDepth_nonpos c.p (norm_nonneg _) hb
    rw [seamDepth_seamRadius c.p (by linarith)] at h2
    linarith
  have ha : ‖a.val.1.down - ((3 / 2 : ℝ) : ℂ)‖ = 1 / 2 := by
    unfold coneDepth at hd
    linarith
  obtain ⟨τ, hτ⟩ := exists_productCollar_one ha
  have hb' : b = solidCollar c.p (c.matching.symm τ, halfZero) := by
    apply Subtype.ext
    rw [c.solidCollar_val_eq _ (zero_mem_halfCollarSource _), ← h, ← hτ,
      c.coneLift_productCollar τ (zero_mem_halfCollarSource τ), matching_symm_apply]
    change c.seamPoint (_, 0) = c.seamPoint (_, -(0 : ℝ))
    rw [neg_zero]
  have hl : (Sum.inr b : FilledCut.{u}) = c.leftTorus (c.matching.symm τ) := by
    rw [hb']
    rfl
  have hr : (Sum.inl a : FilledCut.{u}) = rightTorus (c.matching (c.matching.symm τ)) := by
    rw [Diffeomorph.apply_symm_apply, ← hτ]
    rfl
  rw [hl, hr]
  exact c.gluing.isEquivalence_rel.symm (c.gluing_rel_left_right _)

theorem gluing_rel_of_filledFold_eq {x y : FilledCut.{u}}
    (h : c.filledFold x = c.filledFold y) : c.gluing.rel x y := by
  rcases x with a | a <;> rcases y with b | b
  · refine Or.inl (congrArg Sum.inl (Subtype.ext ?_))
    have h1 := congrArg (fun z : c.filledSet.{u} => c.coneChart z.val) h
    change c.coneChart (c.coneLift a.val) = c.coneChart (c.coneLift b.val) at h1
    rwa [c.coneChart_coneLift _ (ne_three_halves_of_mem_productSet a),
      c.coneChart_coneLift _ (ne_three_halves_of_mem_productSet b)] at h1
  · have h1 : c.coneLift a.val = b.val := congrArg Subtype.val h
    exact c.gluing_rel_inl_inr h1
  · have h1 : c.coneLift b.val = a.val := congrArg Subtype.val h.symm
    exact c.gluing.isEquivalence_rel.symm (c.gluing_rel_inl_inr h1)
  · have h1 : (c.filledFold (Sum.inr a)).val = (c.filledFold (Sum.inr b)).val :=
      congrArg Subtype.val h
    exact Or.inl (congrArg Sum.inr (Subtype.ext h1))

theorem conePoint_mem_planarModel_of_three_lt {y : PlaneLift.{u} × Circle} (hy : y ∈ c.filledSet)
    (h3 : 3 < ‖y.1.down‖) : c.conePoint y ∈ planarModel 3 := by
  have hgt : 1 / 2 < ‖c.conePoint y - ((3 / 2 : ℝ) : ℂ)‖ := by
    rw [c.norm_conePoint_sub]
    have : 1 < (‖y.1.down‖ / 3) ^ c.p :=
      one_lt_pow₀ (by rw [lt_div_iff₀ (by norm_num)]; linarith) (NeZero.ne c.p)
    linarith
  exact (filledFunction_nonpos_iff_mem hgt.le).mp hy

theorem coneChart_mem_productSet {y : PlaneLift.{u} × Circle} (hy : y ∈ c.filledSet)
    (h3 : 3 < ‖y.1.down‖) : c.coneChart y ∈ productSet.{u} 3 :=
  (mem_productSet_iff _).mpr (c.conePoint_mem_planarModel_of_three_lt hy h3)

theorem ne_zero_of_three_lt {y : PlaneLift.{u} × Circle} (h3 : 3 < ‖y.1.down‖) : y.1.down ≠ 0 := by
  rw [← norm_pos_iff]
  linarith

theorem surjective_filledFold : Surjective c.filledFold.{u} := by
  intro y
  by_cases hy : ‖y.val.1.down‖ ≤ 3
  · exact ⟨Sum.inr ⟨y.val, (mem_solidSet_iff _).mpr hy⟩, rfl⟩
  · have h3 : 3 < ‖y.val.1.down‖ := not_le.mp hy
    refine ⟨Sum.inl ⟨c.coneChart y.val, c.coneChart_mem_productSet y.2 h3⟩, ?_⟩
    apply Subtype.ext
    exact c.coneLift_coneChart y.val (ne_zero_of_three_lt h3)

def filledQuotientMap : Quotient c.gluing.{u}.setoid → c.filledSet.{u} :=
  Quotient.lift c.filledFold (fun _ _ h => c.filledFold_eq_of_rel h)

theorem bijective_filledQuotientMap : Bijective c.filledQuotientMap.{u} := by
  constructor
  · intro q q' h
    induction q using Quotient.inductionOn with
    | h x =>
      induction q' using Quotient.inductionOn with
      | h y => exact Quotient.sound (c.gluing_rel_of_filledFold_eq h)
  · intro p
    obtain ⟨x, hx⟩ := c.surjective_filledFold p
    exact ⟨Quotient.mk _ x, hx⟩

instance : CompactSpace FilledCut.{u} := inferInstance

def filledReconstruction : Quotient c.gluing.{u}.setoid ≃ₜ c.filledSet.{u} :=
  Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective _ c.bijective_filledQuotientMap)
    (continuous_quot_lift _ c.contMDiff_filledFold.continuous)

theorem filledReconstruction_mk (x : FilledCut.{u}) :
    c.filledReconstruction (Quotient.mk _ x) = c.filledFold x := rfl

theorem productSet_isBoundaryPoint_iff' (a : productSet.{u} 3) :
    (𝓡∂ 3).IsBoundaryPoint a ↔ ∃ j t, productCollar.{u} 3 (Or.inr rfl) j (t, halfZero) = a := by
  constructor
  · intro h
    have h0 : a ∈ (𝓡∂ 3).boundary (productSet.{u} 3) := h
    rw [productBoundary_eq 3 (Or.inr rfl)] at h0
    obtain ⟨j, t, ht⟩ := mem_iUnion.mp h0
    exact ⟨j, t, ht⟩
  · rintro ⟨j, t, rfl⟩
    exact (productBoundaryTori.{u} 3 (Or.inr rfl)).boundary_zero j t

theorem productSet_isInteriorPoint_iff (a : productSet.{u} 3) :
    (𝓡∂ 3).IsInteriorPoint a ↔ planarFunction 3 a.val.1.down < 0 := by
  rw [← not_iff_not, ← ModelWithCorners.isBoundaryPoint_iff_not_isInteriorPoint,
    productSet_isBoundaryPoint_iff, not_lt]
  exact ⟨fun h => h.ge, fun h => le_antisymm a.2 h⟩

theorem cut_isInteriorPoint_inl_iff (a : productSet.{u} 3) :
    (𝓡∂ 3).IsInteriorPoint (Sum.inl a : FilledCut.{u}) ↔ (𝓡∂ 3).IsInteriorPoint a :=
  ⟨fun h => ModelWithCorners.isInteriorPoint_disjointUnion_left h rfl,
    ModelWithCorners.interiorPoint_inl a⟩

theorem cut_isInteriorPoint_inr_iff (b : solidSet.{u}) :
    (𝓡∂ 3).IsInteriorPoint (Sum.inr b : FilledCut.{u}) ↔ (𝓡∂ 3).IsInteriorPoint b :=
  ⟨fun h => ModelWithCorners.isInteriorPoint_disjointUnion_right h rfl,
    ModelWithCorners.interiorPoint_inr b⟩

theorem cut_isBoundaryPoint_inl_iff (a : productSet.{u} 3) :
    (𝓡∂ 3).IsBoundaryPoint (Sum.inl a : FilledCut.{u}) ↔ (𝓡∂ 3).IsBoundaryPoint a := by
  rw [ModelWithCorners.isBoundaryPoint_iff_not_isInteriorPoint,
    ModelWithCorners.isBoundaryPoint_iff_not_isInteriorPoint, cut_isInteriorPoint_inl_iff]

theorem cut_isBoundaryPoint_inr_iff (b : solidSet.{u}) :
    (𝓡∂ 3).IsBoundaryPoint (Sum.inr b : FilledCut.{u}) ↔ (𝓡∂ 3).IsBoundaryPoint b := by
  rw [ModelWithCorners.isBoundaryPoint_iff_not_isInteriorPoint,
    ModelWithCorners.isBoundaryPoint_iff_not_isInteriorPoint, cut_isInteriorPoint_inr_iff]

def externalPort : Fin 2 → Fin 3 := ![0, 2]

theorem externalPort_injective : Injective externalPort := by
  intro i j h
  fin_cases i <;> fin_cases j <;> first | rfl | exact absurd h (by decide)

theorem externalPort_ne_one (i : Fin 2) : externalPort i ≠ 1 := by
  fin_cases i <;> decide

theorem exists_externalPort {j : Fin 3} (hj : j ≠ 1) : ∃ i, externalPort i = j := by
  fin_cases j
  · exact ⟨0, rfl⟩
  · exact absurd rfl hj
  · exact ⟨1, rfl⟩

def cutExternal : BoundaryTori c.filledCutCarrier.{u} 2 where
  collar i := (productCollar 3 (Or.inr rfl) (externalPort i)).trans partialDiffeomorphSumInl
  source_eq i := by
    change (productCollar.{u} 3 (Or.inr rfl) (externalPort i)).source ∩ _ ⁻¹' univ = _
    rw [preimage_univ, inter_univ]
    rfl
  boundary_zero i t := (cut_isBoundaryPoint_inl_iff _).mpr
    ((productBoundaryTori.{u} 3 (Or.inr rfl)).boundary_zero _ t)
  disjoint i j hij := by
    refine Set.disjoint_left.mpr ?_
    rintro x ⟨⟨a, rfl⟩, hxi⟩ ⟨-, hxj⟩
    exact Set.disjoint_left.mp ((productBoundaryTori.{u} 3 (Or.inr rfl)).disjoint
      (externalPort_injective.ne hij)) hxi hxj

theorem cutExternal_torusMap (i : Fin 2) (t : Torus) :
    c.cutExternal.{u}.torusMap i t =
      Sum.inl (productCollar 3 (Or.inr rfl) (externalPort i) (t, halfZero)) := rfl

theorem gluing_block : (⋃ i, c.gluing.{u}.block i) = range c.leftTorus ∪ range rightTorus :=
  iUnion_const (range c.leftTorus ∪ range rightTorus)

theorem productCollar_mem_target (j : Fin 3) (t : Torus) :
    productCollar.{u} 3 (Or.inr rfl) j (t, halfZero) ∈ (productCollar 3 (Or.inr rfl) j).target :=
  (productCollar 3 (Or.inr rfl) j).map_source' (zero_mem_halfCollarSource t)

theorem productCollar_ne {j k : Fin 3} (hjk : j ≠ k) (t s : Torus) :
    productCollar.{u} 3 (Or.inr rfl) j (t, halfZero) ≠
      productCollar 3 (Or.inr rfl) k (s, halfZero) := by
  intro h
  have h1 := productCollar_mem_target j t
  rw [h] at h1
  exact Set.disjoint_left.mp ((productBoundaryTori.{u} 3 (Or.inr rfl)).disjoint hjk) h1
    (productCollar_mem_target k s)

theorem cut_boundary : (𝓡∂ 3).boundary FilledCut.{u} =
    (⋃ i, c.gluing.block i) ∪ c.cutExternal.image := by
  rw [gluing_block]
  ext x
  change (𝓡∂ 3).IsBoundaryPoint x ↔ _
  simp only [mem_union, mem_range, BoundaryTori.image, mem_iUnion, cutExternal_torusMap]
  rcases x with a | b
  · rw [cut_isBoundaryPoint_inl_iff, productSet_isBoundaryPoint_iff']
    constructor
    · rintro ⟨j, t, rfl⟩
      by_cases hj : j = 1
      · subst hj
        exact Or.inl (Or.inr ⟨t, rfl⟩)
      · obtain ⟨i, rfl⟩ := exists_externalPort hj
        exact Or.inr ⟨i, t, rfl⟩
    · rintro ((⟨t, ht⟩ | ⟨t, ht⟩) | ⟨i, t, ht⟩)
      · exact absurd ht (by simp [leftTorus, leftCollar_apply])
      · exact ⟨1, t, Sum.inl_injective ht⟩
      · exact ⟨externalPort i, t, Sum.inl_injective ht⟩
  · rw [cut_isBoundaryPoint_inr_iff]
    have h0 : (𝓡∂ 3).IsBoundaryPoint b ↔ b ∈ (𝓡∂ 3).boundary solidSet.{u} := Iff.rfl
    rw [h0, solidSet_boundary_eq c.p, mem_range]
    constructor
    · rintro ⟨t, rfl⟩
      exact Or.inl (Or.inl ⟨t, rfl⟩)
    · rintro ((⟨t, ht⟩ | ⟨t, ht⟩) | ⟨i, t, ht⟩)
      · exact ⟨t, Sum.inr_injective ht⟩
      · exact absurd ht (by simp [rightTorus, rightCollar_apply])
      · exact absurd ht (by simp)

theorem cut_external_disjoint :
    Disjoint (⋃ i, c.gluing.{u}.block i) c.cutExternal.image := by
  rw [gluing_block, Set.disjoint_left]
  rintro x hx hy
  simp only [BoundaryTori.image, mem_iUnion, mem_range, cutExternal_torusMap] at hy
  obtain ⟨i, s, rfl⟩ := hy
  rcases hx with ⟨t, ht⟩ | ⟨t, ht⟩
  · exact Sum.inl_ne_inr ht.symm
  · exact productCollar_ne (externalPort_ne_one i).symm t s (Sum.inl_injective ht)

def filledPieces : Fin 2 → TopologicalSpace.Opens FilledCut.{u} :=
  ![⟨range Sum.inl, isOpen_range_inl⟩, ⟨range Sum.inr, isOpen_range_inr⟩]

theorem isConnected_interior_of_connected {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 3) M] [IsManifold (𝓡∂ 3) ∞ M] [ConnectedSpace M] :
    IsConnected ((𝓡∂ 3).interior M) :=
  ⟨Manifold.dense_manifold_interior.nonempty, Manifold.isPreconnected_manifold_interior⟩

theorem filledPieceInterior_zero :
    ((c.filledCutCarrier.{u}.pieceInterior (filledPieces 0) :
      Set c.filledCutCarrier.{u}.Carrier)) = Sum.inl '' (𝓡∂ 3).interior (productSet.{u} 3) := by
  ext x
  constructor
  · rintro ⟨⟨a, rfl⟩, hx⟩
    exact ⟨a, (cut_isInteriorPoint_inl_iff a).mp hx, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨⟨a, rfl⟩, (cut_isInteriorPoint_inl_iff a).mpr ha⟩

theorem filledPieceInterior_one :
    ((c.filledCutCarrier.{u}.pieceInterior (filledPieces 1) :
      Set c.filledCutCarrier.{u}.Carrier)) = Sum.inr '' (𝓡∂ 3).interior solidSet.{u} := by
  ext x
  constructor
  · rintro ⟨⟨a, rfl⟩, hx⟩
    exact ⟨a, (cut_isInteriorPoint_inr_iff a).mp hx, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨⟨a, rfl⟩, (cut_isInteriorPoint_inr_iff a).mpr ha⟩

abbrev filledComponents : c.filledCutCarrier.{u}.Components where
  count := 2
  count_pos := by decide
  piece := filledPieces
  closed i := by
    fin_cases i
    · exact isClosed_range_inl
    · exact isClosed_range_inr
  connected i := by
    have := connectedSpace_productSet.{u} (k := 3) (Or.inr rfl)
    fin_cases i
    · exact isConnected_iff_connectedSpace.mp (isConnected_range continuous_inl)
    · exact isConnected_iff_connectedSpace.mp (isConnected_range continuous_inr)
  disjoint i j h := by
    fin_cases i <;> fin_cases j
    · exact (h rfl).elim
    · exact isCompl_range_inl_range_inr.disjoint
    · exact isCompl_range_inl_range_inr.disjoint.symm
    · exact (h rfl).elim
  covers := by
    refine eq_univ_of_forall fun x => ?_
    rcases x with a | b
    · exact mem_iUnion.mpr ⟨0, a, rfl⟩
    · exact mem_iUnion.mpr ⟨1, b, rfl⟩
  interior_connected i := by
    have := connectedSpace_productSet.{u} (k := 3) (Or.inr rfl)
    fin_cases i
    · apply isConnected_iff_connectedSpace.mp
      change IsConnected (c.filledCutCarrier.{u}.pieceInterior (filledPieces 0) :
        Set c.filledCutCarrier.{u}.Carrier)
      rw [filledPieceInterior_zero]
      exact isConnected_interior_of_connected.image _ continuous_inl.continuousOn
    · apply isConnected_iff_connectedSpace.mp
      change IsConnected (c.filledCutCarrier.{u}.pieceInterior (filledPieces 1) :
        Set c.filledCutCarrier.{u}.Carrier)
      rw [filledPieceInterior_one]
      exact isConnected_interior_of_connected.image _ continuous_inr.continuousOn

def outerSet : Set (PlaneLift.{u} × Circle) := {x | 1 / 2 < ‖x.1.down - ((3 / 2 : ℝ) : ℂ)‖}

theorem isOpen_outerSet : IsOpen outerSet.{u} :=
  isOpen_lt continuous_const (continuous_norm.comp ((continuous_uliftDown.comp continuous_fst).sub
    continuous_const))

def outerAmbient : PartialDiffeomorph PlaneCircleModel PlaneCircleModel (PlaneLift.{u} × Circle)
    (PlaneLift.{u} × Circle) ∞ :=
  DifferentialGeometry.Topology.PartialDiffeomorph.restrict c.coneLiftPartialDiffeomorph
    outerSet isOpen_outerSet

theorem mem_outerAmbient_source {x : PlaneLift.{u} × Circle} :
    x ∈ c.outerAmbient.source ↔ x.1.down ≠ ((3 / 2 : ℝ) : ℂ) ∧ x ∈ outerSet := Iff.rfl

theorem mem_outerAmbient_source_of {x : PlaneLift.{u} × Circle}
    (h : 1 / 2 < ‖x.1.down - ((3 / 2 : ℝ) : ℂ)‖) : x ∈ c.outerAmbient.source := by
  refine ⟨fun he => ?_, h⟩
  rw [he, sub_self, norm_zero] at h
  linarith

theorem outer_iff (x : PlaneLift.{u} × Circle) (hx : x ∈ c.outerAmbient.source) :
    x ∈ productSet.{u} 3 ↔ c.outerAmbient x ∈ c.filledSet := by
  change _ ↔ filledFunction (c.conePoint (c.coneLift x)) ≤ 0
  rw [c.conePoint_coneLift x hx.1, filledFunction_nonpos_iff_mem hx.2.le, mem_productSet_iff]

def outerLift : PartialDiffeomorph (𝓡∂ 3) (𝓡∂ 3) (productSet.{u} 3) c.filledSet.{u} ∞ :=
  (productAtlas.{u} 3).partialDiffeomorphOfAmbient c.filledAtlas c.outerAmbient
    (Classical.arbitrary _) (Classical.arbitrary _) c.outer_iff

theorem outerLift_source : c.outerLift.{u}.source = Subtype.val ⁻¹' c.outerAmbient.source := rfl

theorem outerLift_apply_val (x : productSet.{u} 3) (hx : x.val ∈ c.outerAmbient.source) :
    (c.outerLift x).val = c.coneLift x.val :=
  (productAtlas.{u} 3).partialDiffeomorphOfAmbient_apply_val c.filledAtlas c.outerAmbient _ _
    c.outer_iff x hx

theorem far_of_mem_target {j : Fin 3} (hj : j ≠ 1) {x : productSet.{u} 3}
    (hx : x ∈ (productCollar 3 (Or.inr rfl) j).target) :
    5 / 4 < ‖x.val.1.down - ((3 / 2 : ℝ) : ℂ)‖ := by
  change planarSign j * (‖x.val.1.down - planarCenter 3 j‖ - planarRadius j) < 1 / 4 at hx
  have hb := norm_sub_real_bounds x.val.1.down (3 / 2)
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)] at hb
  have h2 := norm_add_three_halves_ge x.val.1.down
  rcases fin_three_cases j with rfl | rfl | rfl
  · rw [show planarSign (0 : Fin 3) = -1 by simp [planarSign],
      show planarCenter 3 (0 : Fin 3) = 0 by simp [planarCenter],
      show planarRadius (0 : Fin 3) = 3 by simp [planarRadius], Complex.ofReal_zero,
      sub_zero] at hx
    linarith
  · exact absurd rfl hj
  · rw [show planarSign (2 : Fin 3) = 1 by simp [planarSign],
      show planarCenter 3 (2 : Fin 3) = -(3 / 2) by simp [planarCenter],
      show planarRadius (2 : Fin 3) = 1 / 2 by simp [planarRadius]] at hx
    linarith

theorem productCollar_far (i : Fin 2) {p : Torus × EuclideanHalfSpace 1}
    (hp : p ∈ halfCollarSource) :
    5 / 4 < ‖(productCollar.{u} 3 (Or.inr rfl) (externalPort i) p).val.1.down -
      ((3 / 2 : ℝ) : ℂ)‖ :=
  far_of_mem_target (externalPort_ne_one i) ((productCollar 3 (Or.inr rfl) _).map_source' hp)

def externalCollar (i : Fin 2) :
    PartialDiffeomorph halfCollarModel (𝓡∂ 3) (Torus × EuclideanHalfSpace 1) c.filledSet.{u} ∞ :=
  (productCollar 3 (Or.inr rfl) (externalPort i)).trans c.outerLift

theorem externalCollar_source (i : Fin 2) :
    (c.externalCollar.{u} i).source = halfCollarSource := by
  ext p
  refine ⟨fun hp => hp.1, fun hp => ⟨hp, ?_⟩⟩
  exact c.mem_outerAmbient_source_of (lt_trans (by norm_num) (productCollar_far i hp))

theorem externalCollar_apply_val (i : Fin 2) {p : Torus × EuclideanHalfSpace 1}
    (hp : p ∈ halfCollarSource) :
    (c.externalCollar.{u} i p).val =
      c.coneLift (productCollar 3 (Or.inr rfl) (externalPort i) p).val :=
  c.outerLift_apply_val _ (c.mem_outerAmbient_source_of
    (lt_trans (by norm_num) (productCollar_far i hp)))

theorem fin_two_cases (i : Fin 2) : i = 0 ∨ i = 1 := by
  fin_cases i <;> simp

theorem filledFunction_planarCircleMap (i : Fin 2) (t : Circle) :
    filledFunction (planarCircleMap 3 (externalPort i) t) = 0 := by
  unfold filledFunction
  rcases fin_two_cases i with rfl | rfl
  · refine mul_eq_zero_of_left ?_ _
    rw [sqDist_eq_zero_iff 0 (by norm_num), sub_zero, show externalPort 0 = 0 from rfl]
    simp [planarCircleMap, planarCenter, planarRadius]
  · refine mul_eq_zero_of_right _ ?_
    rw [sqDist_eq_zero_iff _ (by norm_num), show externalPort 1 = 2 from rfl]
    simp [planarCircleMap, planarCenter, planarRadius]

theorem conePoint_externalCollar_zero (i : Fin 2) (t : Torus) :
    c.conePoint (c.externalCollar.{u} i (t, halfZero)).val =
      planarCircleMap 3 (externalPort i) t.1 := by
  rw [c.externalCollar_apply_val i (zero_mem_halfCollarSource t), c.conePoint_coneLift _
    (c.mem_outerAmbient_source_of (lt_trans (by norm_num)
      (productCollar_far i (zero_mem_halfCollarSource t)))).1]
  exact planarCollar_zero_val (Or.inr rfl) _ t.1

def external : BoundaryTori c.filledCarrier.{u} 2 where
  collar := c.externalCollar
  source_eq := c.externalCollar_source
  boundary_zero i t := by
    change (𝓡∂ 3).IsBoundaryPoint (c.externalCollar i (t, halfZero))
    rw [filledSet_isBoundaryPoint_iff, conePoint_externalCollar_zero]
    exact filledFunction_planarCircleMap i t.1
  disjoint i j hij := by
    refine Set.disjoint_left.mpr ?_
    rintro y ⟨-, hyi⟩ ⟨-, hyj⟩
    exact Set.disjoint_left.mp ((productBoundaryTori.{u} 3 (Or.inr rfl)).disjoint
      (externalPort_injective.ne hij)) hyi hyj

theorem filled_boundary : (𝓡∂ 3).boundary c.filledSet.{u} = c.external.image := by
  ext y
  change (𝓡∂ 3).IsBoundaryPoint y ↔ _
  rw [filledSet_isBoundaryPoint_iff]
  simp only [BoundaryTori.image, mem_iUnion, mem_range]
  constructor
  · intro hy
    have h3 : 3 < ‖y.val.1.down‖ := by
      by_contra hn
      have := c.filledFunction_conePoint_neg_of_mem_solidSet
        ((mem_solidSet_iff y.val).mpr (not_lt.mp hn))
      linarith
    set x : productSet.{u} 3 := ⟨c.coneChart y.val, c.coneChart_mem_productSet y.2 h3⟩
    have hxb : (𝓡∂ 3).IsBoundaryPoint x := by
      rw [productSet_isBoundaryPoint_iff]
      change planarFunction 3 (c.conePoint y.val) = 0
      rw [planarFunction_three]
      unfold filledFunction sqDist at hy
      rw [sub_zero] at hy
      rcases mul_eq_zero.mp hy with h | h
      · rw [h, zero_mul]
      · rw [h, mul_zero, mul_zero]
    obtain ⟨j, τ, hτ⟩ := (productSet_isBoundaryPoint_iff' x).mp hxb
    have hfar : 1 / 2 < ‖x.val.1.down - ((3 / 2 : ℝ) : ℂ)‖ := by
      change 1 / 2 < ‖c.conePoint y.val - ((3 / 2 : ℝ) : ℂ)‖
      rw [c.norm_conePoint_sub]
      have : 1 < (‖y.val.1.down‖ / 3) ^ c.p :=
        one_lt_pow₀ (by rw [lt_div_iff₀ (by norm_num)]; linarith) (NeZero.ne c.p)
      linarith
    have hj : j ≠ 1 := by
      rintro rfl
      have h1 := productCollar_one_sub.{u} τ (zero_mem_halfCollarSource τ)
      rw [hτ] at h1
      have h2 : ‖x.val.1.down - ((3 / 2 : ℝ) : ℂ)‖ = 1 / 2 := by
        rw [h1, norm_smul, Circle.norm_coe, mul_one, show halfZero.val 0 = (0 : ℝ) from rfl]
        norm_num
      linarith
    obtain ⟨i, rfl⟩ := exists_externalPort hj
    refine ⟨i, τ, Subtype.ext ?_⟩
    change (c.externalCollar i (τ, halfZero)).val = y.val
    rw [c.externalCollar_apply_val i (zero_mem_halfCollarSource τ)]
    rw [hτ]
    exact c.coneLift_coneChart y.val (ne_zero_of_three_lt h3)
  · rintro ⟨i, t, rfl⟩
    change filledFunction (c.conePoint (c.externalCollar i (t, halfZero)).val) = 0
    rw [conePoint_externalCollar_zero]
    exact filledFunction_planarCircleMap i t.1

theorem cut_filled_external (i : Fin 2) (p : Torus × EuclideanHalfSpace 1)
    (hp : p ∈ halfCollarSource) :
    c.filledFold (c.cutExternal.{u}.collar i p) = c.external.collar i p := by
  apply Subtype.ext
  change c.coneLift (productCollar 3 (Or.inr rfl) (externalPort i) p).val = _
  exact (c.externalCollar_apply_val i hp).symm

def seamTarget : Set c.filledSet.{u} :=
  {y | -1 < seamDepth c.p ‖y.val.1.down‖ ∧ seamDepth c.p ‖y.val.1.down‖ < 1}

theorem ne_zero_of_mem_seamTarget {y : c.filledSet.{u}} (hy : y ∈ c.seamTarget) :
    y.val.1.down ≠ 0 := by
  intro h0
  have := hy.1
  rw [h0, norm_zero] at this
  simp [seamDepth, NeZero.ne c.p] at this

theorem seamPoint_mem_filledSet {y : Torus × ℝ} (h1 : -1 ≤ y.2) (h2 : y.2 ≤ 1) :
    c.seamPoint y ∈ c.filledSet.{u} := by
  refine (filledFunction_neg_of_near ?_).le
  rw [c.norm_conePoint_seamPoint_sub (by linarith)]
  linarith

def seamMap (y : Torus × ℝ) : c.filledSet.{u} :=
  ⟨c.seamPoint (y.1, seamClamp y.2), c.seamPoint_mem_filledSet (neg_one_le_seamClamp _)
    (seamClamp_le_one _)⟩

def seamInv (y : c.filledSet.{u}) : Torus × ℝ :=
  ((unitOf y.val.1.down, y.val.2), seamDepth c.p ‖y.val.1.down‖)

theorem seamMap_val {y : Torus × ℝ} (hy : y ∈ signedCollarSource) :
    (c.seamMap.{u} y).val = c.seamPoint y := by
  change c.seamPoint (y.1, seamClamp y.2) = _
  rw [seamClamp_of_mem hy.1.le hy.2.le]

theorem contMDiffAt_seamPoint {y : Torus × ℝ} (hy : -2 < y.2) :
    ContMDiffAt signedCollarModel PlaneCircleModel ∞ c.seamPoint.{u} y := by
  have hr : ContMDiffAt signedCollarModel 𝓘(ℝ, ℝ) ∞ (fun y : Torus × ℝ => seamRadius c.p y.2) y :=
    (contDiffAt_seamRadius c.p hy).contMDiffAt.comp y contMDiff_snd.contMDiffAt
  have hc : ContMDiffAt signedCollarModel 𝓘(ℝ, ℂ) ∞ (fun y : Torus × ℝ => (y.1.1 : ℂ)) y :=
    (contMDiff_circle_coe.comp (contMDiff_fst.comp contMDiff_fst)).contMDiffAt
  exact (contMDiff_planeLift_up.contMDiffAt.comp y (hr.smul hc)).prodMk
    (contMDiff_snd.comp contMDiff_fst).contMDiffAt

def seam : PartialDiffeomorph signedCollarModel (𝓡∂ 3) (Torus × ℝ) c.filledSet.{u} ∞ where
  toFun := c.seamMap
  invFun := c.seamInv
  source := signedCollarSource
  target := c.seamTarget
  map_source' y hy := by
    change -1 < seamDepth c.p ‖(c.seamMap.{u} y).val.1.down‖ ∧
      seamDepth c.p ‖(c.seamMap.{u} y).val.1.down‖ < 1
    rw [c.seamMap_val hy, c.norm_seamPoint (by linarith [hy.1]),
      seamDepth_seamRadius c.p (by linarith [hy.1])]
    exact hy
  map_target' y hy := hy
  left_inv' y hy := by
    change ((unitOf (c.seamMap.{u} y).val.1.down, (c.seamMap.{u} y).val.2),
      seamDepth c.p ‖(c.seamMap.{u} y).val.1.down‖) = y
    rw [c.seamMap_val hy, c.norm_seamPoint (by linarith [hy.1]),
      seamDepth_seamRadius c.p (by linarith [hy.1])]
    change ((unitOf (seamRadius c.p y.2 • (y.1.1 : ℂ)), y.1.2), y.2) = y
    rw [unitOf_smul (seamRadius_pos c.p (by linarith [hy.1]))]
  right_inv' y hy := by
    apply Subtype.ext
    rw [c.seamMap_val hy]
    change (ULift.up (seamRadius c.p (seamDepth c.p ‖y.val.1.down‖) •
      (unitOf y.val.1.down : ℂ)), y.val.2) = y.val
    rw [seamRadius_seamDepth c.p (norm_nonneg _), norm_smul_unitOf]
  open_source := isOpen_signedCollarSource
  open_target := by
    have hn : Continuous fun y : c.filledSet.{u} => seamDepth c.p ‖y.val.1.down‖ :=
      (contDiff_seamDepth c.p).continuous.comp
        (continuous_norm.comp (continuous_uliftDown.comp
          (continuous_fst.comp continuous_subtype_val)))
    exact (isOpen_lt continuous_const hn).inter (isOpen_lt hn continuous_const)
  contMDiffOn_toFun := by
    refine (c.filledAtlas.contMDiffOn_iff_subtype_val _ _).mpr fun y hy => ?_
    refine ((c.contMDiffAt_seamPoint (by linarith [hy.1])).contMDiffWithinAt).congr
      (fun y' hy' => c.seamMap_val hy') (c.seamMap_val hy)
  contMDiffOn_invFun := by
    intro y hy
    have hne := c.ne_zero_of_mem_seamTarget hy
    have hd : ContMDiffAt (𝓡∂ 3) 𝓘(ℝ, ℂ) ∞ (fun y : c.filledSet.{u} => y.val.1.down) y :=
      (contMDiff_planeLift_down.comp (contMDiff_fst.comp c.filledAtlas.contMDiff_subtype_val)) y
    have hv : ContMDiffAt (𝓡∂ 3) (𝓡 1) ∞ (fun y : c.filledSet.{u} => unitOf y.val.1.down) y :=
      (contMDiffOn_unitOf.contMDiffAt (isOpen_ne.mem_nhds hne)).comp y hd
    have hw : ContMDiffAt (𝓡∂ 3) (𝓡 1) ∞ (fun y : c.filledSet.{u} => y.val.2) y :=
      (contMDiff_snd.comp c.filledAtlas.contMDiff_subtype_val) y
    have hn : ContMDiffAt (𝓡∂ 3) 𝓘(ℝ, ℝ) ∞
        (fun y : c.filledSet.{u} => seamDepth c.p ‖y.val.1.down‖) y :=
      (contDiff_seamDepth c.p).contMDiff.contMDiffAt.comp y
        ((contDiffAt_norm ℝ hne).contMDiffAt.comp y hd)
    exact ((hv.prodMk hw).prodMk hn).contMDiffWithinAt

theorem seam_apply_val {y : Torus × ℝ} (hy : y ∈ signedCollarSource) :
    (c.seam.{u} y).val = c.seamPoint y :=
  c.seamMap_val hy

theorem seam_target_subset_interior : c.seam.{u}.target ⊆ c.filledCarrier.interior := by
  intro y hy
  change (𝓡∂ 3).IsInteriorPoint y
  rw [filledSet_isInteriorPoint_iff]
  refine filledFunction_neg_of_near ?_
  rw [c.norm_conePoint_sub]
  have h1 := hy.2
  unfold seamDepth at h1
  linarith

theorem external_seam_disjoint (i : Fin 2) :
    Disjoint (c.external.{u}.collar i).target c.seam.target := by
  rw [Set.disjoint_left]
  rintro y ⟨hy1, hy2⟩ hys
  have hsrc : (c.outerLift.symm y).val = c.coneChart y.val :=
    (productAtlas.{u} 3).partialDiffeomorphOfAmbient_symm_apply_val c.filledAtlas c.outerAmbient
      _ _ c.outer_iff y hy1
  have hfar : 5 / 4 < ‖(c.outerLift.symm y).val.1.down - ((3 / 2 : ℝ) : ℂ)‖ :=
    far_of_mem_target (externalPort_ne_one i) hy2
  rw [hsrc] at hfar
  change 5 / 4 < ‖c.conePoint y.val - ((3 / 2 : ℝ) : ℂ)‖ at hfar
  rw [c.norm_conePoint_sub] at hfar
  have h1 := hys.2
  unfold seamDepth at h1
  linarith

end ConeFilling

end GC.Seifert
