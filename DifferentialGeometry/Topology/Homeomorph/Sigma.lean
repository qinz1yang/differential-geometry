import DifferentialGeometry.Topology.Attachment.Basic
import Mathlib.Topology.Homeomorph.Lemmas

noncomputable section

namespace Homeomorph

variable {ι : Type*} (X : ι → Type*) [∀ i, TopologicalSpace (X i)]

noncomputable def sigmaSplitPair (i j : ι) (hij : i ≠ j) :
    (Σ k, X k) ≃ₜ (X i ⊕ X j) ⊕ (Σ k : {k // k ≠ i ∧ k ≠ j}, X k.val) := by
  classical
  refine
    { toFun := fun x =>
        if hi : x.1 = i then Sum.inl (Sum.inl (hi ▸ x.2))
        else if hj : x.1 = j then Sum.inl (Sum.inr (hj ▸ x.2))
        else Sum.inr ⟨⟨x.1, hi, hj⟩, x.2⟩
      invFun := Sum.elim (Sum.elim (Sigma.mk i) (Sigma.mk j))
        (fun x => ⟨x.1.val, x.2⟩)
      left_inv := ?_
      right_inv := ?_
      continuous_toFun := ?_
      continuous_invFun := ?_ }
  · rintro ⟨k, x⟩
    by_cases hki : k = i
    · subst k
      simp
    · by_cases hkj : k = j
      · subst k
        simp [hki]
      · simp [hki, hkj]
  · rintro ((x | x) | ⟨⟨k, hki, hkj⟩, x⟩)
    · simp
    · simp [hij.symm]
    · simp [hki, hkj]
  · apply continuous_sigma
    intro k
    by_cases hki : k = i
    · subst k
      simp only
      exact (continuous_inl : Continuous (Sum.inl : X i ⊕ X j →
        (X i ⊕ X j) ⊕ (Σ k : {k // k ≠ i ∧ k ≠ j}, X k.val))).comp
          (continuous_inl : Continuous (Sum.inl : X i → X i ⊕ X j))
    · by_cases hkj : k = j
      · subst k
        simp only [dif_neg hki]
        exact (continuous_inl : Continuous (Sum.inl : X i ⊕ X j →
          (X i ⊕ X j) ⊕ (Σ k : {k // k ≠ i ∧ k ≠ j}, X k.val))).comp
            (continuous_inr : Continuous (Sum.inr : X j → X i ⊕ X j))
      · simp only [dif_neg hki, dif_neg hkj]
        exact continuous_inr.comp
          (@continuous_sigmaMk {k // k ≠ i ∧ k ≠ j} (fun k => X k.val)
            (fun k => inferInstance) ⟨k, hki, hkj⟩)
  · exact Continuous.sumElim
      (Continuous.sumElim continuous_sigmaMk continuous_sigmaMk)
      (continuous_sigma fun _ => continuous_sigmaMk)

@[simp] theorem sigmaSplitPair_mk_left (i j : ι) (hij : i ≠ j) (x : X i) :
    sigmaSplitPair X i j hij ⟨i, x⟩ = Sum.inl (Sum.inl x) := by
  classical
  simp [sigmaSplitPair]

@[simp] theorem sigmaSplitPair_mk_right (i j : ι) (hij : i ≠ j) (x : X j) :
    sigmaSplitPair X i j hij ⟨j, x⟩ = Sum.inl (Sum.inr x) := by
  classical
  simp [sigmaSplitPair, hij.symm]

@[simp] theorem sigmaSplitPair_mk_remaining (i j : ι) (hij : i ≠ j)
    (k : {k // k ≠ i ∧ k ≠ j}) (x : X k.val) :
    sigmaSplitPair X i j hij ⟨k.val, x⟩ = Sum.inr ⟨k, x⟩ := by
  classical
  simp [sigmaSplitPair, k.property.1, k.property.2]

@[simp] theorem sigmaSplitPair_symm_inl_inl (i j : ι) (hij : i ≠ j) (x : X i) :
    (sigmaSplitPair X i j hij).symm (Sum.inl (Sum.inl x)) = ⟨i, x⟩ := rfl

@[simp] theorem sigmaSplitPair_symm_inl_inr (i j : ι) (hij : i ≠ j) (x : X j) :
    (sigmaSplitPair X i j hij).symm (Sum.inl (Sum.inr x)) = ⟨j, x⟩ := rfl

@[simp] theorem sigmaSplitPair_symm_inr (i j : ι) (hij : i ≠ j)
    (x : Σ k : {k // k ≠ i ∧ k ≠ j}, X k.val) :
    (sigmaSplitPair X i j hij).symm (Sum.inr x) = ⟨x.1.val, x.2⟩ := rfl

end Homeomorph

namespace Homeomorph

variable {V A : Type*} (X : V → Type*) [∀ v, TopologicalSpace (X v)]

def sigmaAdjunction (i j : V) (hij : i ≠ j) (l : A → X i) (r : A → X j) :
    Quot (fun x y : Σ v, X v => ∃ a,
      (x = ⟨i, l a⟩ ∧ y = ⟨j, r a⟩) ∨ (y = ⟨i, l a⟩ ∧ x = ⟨j, r a⟩)) ≃ₜ
        DifferentialGeometry.Topology.AdjunctionSpace l r ⊕
          (Σ v : {v // v ≠ i ∧ v ≠ j}, X v.val) := by
  let U := Σ v : {v // v ≠ i ∧ v ≠ j}, X v.val
  let ρ := fun x y : Σ v, X v => ∃ a,
    (x = ⟨i, l a⟩ ∧ y = ⟨j, r a⟩) ∨ (y = ⟨i, l a⟩ ∧ x = ⟨j, r a⟩)
  let e := sigmaSplitPair X i j hij
  let F : (Σ v, X v) → DifferentialGeometry.Topology.AdjunctionSpace l r ⊕ U :=
    (Sum.map (DifferentialGeometry.Topology.adjunctionMk l r) id) ∘ e
  have hFquotient : _root_.Topology.IsQuotientMap F := by
    apply _root_.Topology.IsQuotientMap.comp _ e.isQuotientMap
    rw [_root_.Topology.isQuotientMap_iff]
    refine ⟨_root_.Topology.isCoinducing_iff.mpr ?_, ?_⟩
    · intro S
      conv_lhs => rw [isOpen_sum_iff]
      conv_rhs => rw [isOpen_sum_iff]
      have hq := (DifferentialGeometry.Topology.isQuotientMap_adjunctionMk l r).isOpen_preimage
        (s := Sum.inl ⁻¹' S)
      exact and_congr hq Iff.rfl
    · exact Sum.map_surjective.mpr
        ⟨(DifferentialGeometry.Topology.isQuotientMap_adjunctionMk l r).surjective,
          Function.surjective_id⟩
  have hrel : ∀ x y, ρ x y → F x = F y := by
    rintro x y ⟨a, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · simp only [F, e, Function.comp_apply, sigmaSplitPair_mk_left, sigmaSplitPair_mk_right,
        Sum.map_inl]
      exact congrArg Sum.inl (DifferentialGeometry.Topology.adjunction_coherence l r a)
    · simp only [F, e, Function.comp_apply, sigmaSplitPair_mk_left, sigmaSplitPair_mk_right,
        Sum.map_inl]
      exact congrArg Sum.inl (DifferentialGeometry.Topology.adjunction_coherence l r a).symm
  let G : Quot ρ → DifferentialGeometry.Topology.AdjunctionSpace l r ⊕ U :=
    Quot.lift F hrel
  have hGinj : Function.Injective G := by
    intro q q' h
    obtain ⟨x, rfl⟩ := Quot.exists_rep q
    obtain ⟨y, rfl⟩ := Quot.exists_rep q'
    change F x = F y at h
    have hfiber : ∀ p q : (X i ⊕ X j) ⊕ U,
        Sum.map (DifferentialGeometry.Topology.adjunctionMk l r) id p =
          Sum.map (DifferentialGeometry.Topology.adjunctionMk l r) id q →
        Quot.mk ρ (e.symm p) = Quot.mk ρ (e.symm q) := by
      intro p q hpq
      cases p with
      | inl p =>
        cases q with
        | inl q =>
          have hpq' := Sum.inl.inj hpq
          have hgen := Quot.eqvGen_exact hpq'
          clear hpq hpq'
          induction hgen with
          | rel p q hpq =>
            rcases hpq with ⟨a, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
            · exact Quot.sound ⟨a, Or.inl ⟨rfl, rfl⟩⟩
            · exact Quot.sound ⟨a, Or.inr ⟨rfl, rfl⟩⟩
          | refl p => rfl
          | symm p q _ ih => exact ih.symm
          | trans p q r _ _ ih ih' => exact ih.trans ih'
        | inr q => exact (Sum.inl_ne_inr (by simpa only [Sum.map_inl, Sum.map_inr] using hpq)).elim
      | inr p =>
        cases q with
        | inl q => exact (Sum.inr_ne_inl (by simpa only [Sum.map_inl, Sum.map_inr] using hpq)).elim
        | inr q => exact congrArg (fun z => Quot.mk ρ (e.symm (Sum.inr z))) (Sum.inr.inj hpq)
    exact (by simpa only [e.symm_apply_apply] using hfiber (e x) (e y) h)
  have hGquotient : _root_.Topology.IsQuotientMap G :=
    (isQuotientMap_quot_mk (r := ρ)).of_comp_isQuotientMap hFquotient
  exact IsHomeomorph.homeomorph G
    (isHomeomorph_iff_isQuotientMap_injective.mpr ⟨hGquotient, hGinj⟩)

@[simp] theorem sigmaAdjunction_mk_left (i j : V) (hij : i ≠ j)
    (l : A → X i) (r : A → X j) (x : X i) :
    sigmaAdjunction X i j hij l r (Quot.mk _ ⟨i, x⟩) =
      Sum.inl (DifferentialGeometry.Topology.adjunctionCell l r x) := by
  change Sum.map (DifferentialGeometry.Topology.adjunctionMk l r) id
    (sigmaSplitPair X i j hij ⟨i, x⟩) = _
  rw [sigmaSplitPair_mk_left]
  rfl

@[simp] theorem sigmaAdjunction_mk_right (i j : V) (hij : i ≠ j)
    (l : A → X i) (r : A → X j) (x : X j) :
    sigmaAdjunction X i j hij l r (Quot.mk _ ⟨j, x⟩) =
      Sum.inl (DifferentialGeometry.Topology.adjunctionLower r x) := by
  change Sum.map (DifferentialGeometry.Topology.adjunctionMk l r) id
    (sigmaSplitPair X i j hij ⟨j, x⟩) = _
  rw [sigmaSplitPair_mk_right]
  rfl

@[simp] theorem sigmaAdjunction_mk_remaining (i j : V) (hij : i ≠ j)
    (l : A → X i) (r : A → X j)
    (v : {v // v ≠ i ∧ v ≠ j}) (x : X v.val) :
    sigmaAdjunction X i j hij l r (Quot.mk _ ⟨v.val, x⟩) = Sum.inr ⟨v, x⟩ := by
  change Sum.map (DifferentialGeometry.Topology.adjunctionMk l r) id
    (sigmaSplitPair X i j hij ⟨v.val, x⟩) = _
  rw [sigmaSplitPair_mk_remaining]
  rfl



variable {V : Type*} (X : Option V → Type*) [∀ v, TopologicalSpace (X v)]

def sigmaOption : (Σ v, X v) ≃ₜ X none ⊕ (Σ v, X (some v)) where
  toFun p := match p with
    | ⟨none, x⟩ => Sum.inl x
    | ⟨some v, x⟩ => Sum.inr ⟨v, x⟩
  invFun := Sum.elim (fun x => ⟨none, x⟩) (fun p => ⟨some p.fst, p.snd⟩)
  left_inv p := by rcases p with ⟨v, x⟩; cases v <;> rfl
  right_inv p := by rcases p with x | ⟨v, x⟩ <;> rfl
  continuous_toFun := by
    apply continuous_sigma
    intro v
    cases v with
    | none => exact continuous_inl
    | some v => exact continuous_inr.comp continuous_sigmaMk
  continuous_invFun := Continuous.sumElim continuous_sigmaMk
    (continuous_sigma fun v => continuous_sigmaMk)

@[simp] theorem sigmaOption_none (x : X none) : sigmaOption X ⟨none, x⟩ = Sum.inl x := rfl

@[simp] theorem sigmaOption_some (v : V) (x : X (some v)) :
    sigmaOption X ⟨some v, x⟩ = Sum.inr ⟨v, x⟩ := rfl

@[simp] theorem sigmaOption_symm_inl (x : X none) :
    (sigmaOption X).symm (Sum.inl x) = ⟨none, x⟩ := rfl

@[simp] theorem sigmaOption_symm_inr (v : V) (x : X (some v)) :
    (sigmaOption X).symm (Sum.inr ⟨v, x⟩) = ⟨some v, x⟩ := rfl

variable {I : Type*} {Y Z : I → Type*}
  [∀ i, TopologicalSpace (Y i)] [∀ i, TopologicalSpace (Z i)]

def sigmaCongrRight (h : ∀ i, Y i ≃ₜ Z i) : (Σ i, Y i) ≃ₜ (Σ i, Z i) where
  toEquiv := Equiv.sigmaCongrRight fun i => (h i).toEquiv
  continuous_toFun := Continuous.sigma_map fun i => (h i).continuous
  continuous_invFun := Continuous.sigma_map fun i => (h i).symm.continuous

@[simp] theorem sigmaCongrRight_apply (h : ∀ i, Y i ≃ₜ Z i) (i : I) (x : Y i) :
    sigmaCongrRight h ⟨i, x⟩ = ⟨i, h i x⟩ := rfl

@[simp] theorem sigmaCongrRight_symm_apply (h : ∀ i, Y i ≃ₜ Z i) (i : I) (x : Z i) :
    (sigmaCongrRight h).symm ⟨i, x⟩ = ⟨i, (h i).symm x⟩ := rfl


end Homeomorph
