import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Presentation
import DifferentialGeometry.Topology.ThreeManifold.TorusCut.TorusCylinder

/-!
# Slopes on the torus

`torusMatrix φ` is the matrix of a diffeomorphism of `Torus` (the type of `TorusPairing.matching`)
on π₁ at `torusBase`, in coordinates extending `GC.Topology.torusFundamentalGroup`, conjugated back
along a path; π₁ is abelian, so the path does not matter (`torusMatrix_well_defined`). It is
functorial, so `torusUnit φ : GL (Fin 2) ℤ` and `det = ±1`. A `PrimitiveSlope` is a coprime pair
`(p, q)` up to sign, acted on by `GL (Fin 2) ℤ` through column vectors; `delta` is the absolute
value of the determinant of two slopes (chapter 6, S0 and the F01 regressions).
-/

set_option autoImplicit false

noncomputable section
open DifferentialGeometry.Topology GC.Endpoint
open scoped Manifold ContDiff

namespace GC.Seifert

abbrev torusBase : Torus := (1, 1)

def torusCoordinates : FundamentalGroup Torus torusBase ≃* Multiplicative (Fin 2 → ℤ) :=
  GC.Topology.torusFundamentalGroup.trans ((MulEquiv.prodMultiplicative ℤ ℤ).symm.trans
    (AddEquiv.toMultiplicative (LinearEquiv.finTwoArrow ℤ ℤ).toAddEquiv.symm))

theorem torus_mul_comm (a b : FundamentalGroup Torus torusBase) : a * b = b * a :=
  torusCoordinates.injective (by rw [map_mul, map_mul, mul_comm])

theorem markedMap_torus_eq (f : C(Torus, Torus)) (γ γ' : Path torusBase (f torusBase)) :
    GC.Topology.markedMap f torusBase γ = GC.Topology.markedMap f torusBase γ' := by
  ext g
  simp only [GC.Topology.markedMap, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  rw [fundamentalGroupChangeBasepoint_connector γ γ', MulAut.conj_apply, torus_mul_comm _ _,
    inv_mul_cancel_left]

private theorem markedMap_comp {X : Type*} [TopologicalSpace X] (f g : C(X, X)) (b : X)
    (γ : Path b (f b)) (δ : Path b (g b)) :
    GC.Topology.markedMap (g.comp f) b (δ.trans (γ.map g.continuous)) =
      (GC.Topology.markedMap g b δ).comp (GC.Topology.markedMap f b γ) := by
  ext x
  simp only [GC.Topology.markedMap, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    fundamentalGroupChangeBasepoint_apply, FundamentalGroup.map_apply]
  induction x using Path.Homotopic.Quotient.ind with | _ p => ?_
  have hq : ∀ {x y : X} (q : Path x y),
      (⟦q⟧ : Path.Homotopic.Quotient x y) = Path.Homotopic.Quotient.mk q := fun _ => rfl
  simp only [hq, ← Path.Homotopic.Quotient.mk_map, ← Path.Homotopic.Quotient.mk_trans,
    ← Path.Homotopic.Quotient.mk_symm]
  simp only [Path.map_trans, Path.map_symm, Path.map_map, Path.trans_symm]
  simp only [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm,
    Path.Homotopic.Quotient.trans_assoc]

private theorem markedMap_refl {X : Type*} [TopologicalSpace X] (b : X) :
    GC.Topology.markedMap (ContinuousMap.id X) b (Path.refl b) = MonoidHom.id _ := by
  ext x
  induction x using Path.Homotopic.Quotient.ind with | _ p => ?_
  change Path.Homotopic.Quotient.trans (Path.Homotopic.Quotient.trans
      (Path.Homotopic.Quotient.mk (Path.refl b)) (Path.Homotopic.Quotient.mk (p.map continuous_id)))
      (Path.Homotopic.Quotient.symm (Path.Homotopic.Quotient.mk (Path.refl b))) =
    Path.Homotopic.Quotient.mk p
  rw [← Path.Homotopic.Quotient.mk_symm, Path.refl_symm]
  simp only [Path.map_id, Path.Homotopic.Quotient.mk_refl, Path.Homotopic.Quotient.refl_trans]
  exact Path.Homotopic.Quotient.trans_refl _

def torusAut (f : C(Torus, Torus)) :
    FundamentalGroup Torus torusBase →* FundamentalGroup Torus torusBase :=
  GC.Topology.markedMap f torusBase (PathConnectedSpace.somePath _ _)

theorem torusAut_eq (f : C(Torus, Torus)) (γ : Path torusBase (f torusBase)) :
    torusAut f = GC.Topology.markedMap f torusBase γ :=
  markedMap_torus_eq f _ γ

theorem torusAut_comp (f g : C(Torus, Torus)) :
    torusAut (g.comp f) = (torusAut g).comp (torusAut f) := by
  rw [torusAut_eq (g.comp f) ((PathConnectedSpace.somePath torusBase (g torusBase)).trans
    ((PathConnectedSpace.somePath torusBase (f torusBase)).map g.continuous))]
  exact markedMap_comp f g torusBase _ _

theorem torusAut_id : torusAut (ContinuousMap.id Torus) = MonoidHom.id _ := by
  rw [torusAut_eq _ (Path.refl torusBase)]
  exact markedMap_refl torusBase

def coordinateLinear (h : FundamentalGroup Torus torusBase →* FundamentalGroup Torus torusBase) :
    (Fin 2 → ℤ) →ₗ[ℤ] (Fin 2 → ℤ) :=
  (AddMonoidHom.toMultiplicative.symm
    ((torusCoordinates.toMonoidHom.comp h).comp torusCoordinates.symm.toMonoidHom)).toIntLinearMap

def torusMapMatrix (f : C(Torus, Torus)) : Matrix (Fin 2) (Fin 2) ℤ :=
  LinearMap.toMatrix' (coordinateLinear (torusAut f))

theorem torusMapMatrix_mulVec (f : C(Torus, Torus)) (g : FundamentalGroup Torus torusBase) :
    (torusMapMatrix f).mulVec (Multiplicative.toAdd (torusCoordinates g)) =
      Multiplicative.toAdd (torusCoordinates (torusAut f g)) := by
  rw [torusMapMatrix, LinearMap.toMatrix'_mulVec]
  simp [coordinateLinear]

theorem torusMapMatrix_comp (f g : C(Torus, Torus)) :
    torusMapMatrix (g.comp f) = torusMapMatrix g * torusMapMatrix f := by
  rw [torusMapMatrix, torusMapMatrix, torusMapMatrix, ← LinearMap.toMatrix'_comp, torusAut_comp]
  exact congrArg _ (LinearMap.ext fun v => by simp [coordinateLinear])

theorem torusMapMatrix_id : torusMapMatrix (ContinuousMap.id Torus) = 1 := by
  rw [torusMapMatrix, torusAut_id, ← LinearMap.toMatrix'_id]
  exact congrArg _ (LinearMap.ext fun v => by simp [coordinateLinear])

def torusMatrix (φ : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus) : Matrix (Fin 2) (Fin 2) ℤ :=
  torusMapMatrix ⟨φ, φ.continuous⟩

theorem torusMatrix_well_defined (φ : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus)
    (γ : Path torusBase (φ torusBase)) :
    torusMatrix φ = LinearMap.toMatrix'
      (coordinateLinear (GC.Topology.markedMap ⟨φ, φ.continuous⟩ torusBase γ)) := by
  rw [torusMatrix, torusMapMatrix, torusAut_eq _ γ]

theorem torusMatrix_trans (φ ψ : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus) :
    torusMatrix (φ.trans ψ) = torusMatrix ψ * torusMatrix φ :=
  torusMapMatrix_comp ⟨φ, φ.continuous⟩ ⟨ψ, ψ.continuous⟩

theorem torusMatrix_refl : torusMatrix (Diffeomorph.refl torusModel Torus ∞) = 1 :=
  torusMapMatrix_id

def torusUnit (φ : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus) : GL (Fin 2) ℤ :=
  ⟨torusMatrix φ, torusMatrix φ.symm,
    by rw [← torusMatrix_trans, Diffeomorph.symm_trans_self, torusMatrix_refl],
    by rw [← torusMatrix_trans, Diffeomorph.self_trans_symm, torusMatrix_refl]⟩

theorem val_torusUnit (φ : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus) :
    (torusUnit φ : Matrix (Fin 2) (Fin 2) ℤ) = torusMatrix φ :=
  rfl

theorem torusMatrix_det (φ : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus) :
    (torusMatrix φ).det = 1 ∨ (torusMatrix φ).det = -1 :=
  Int.isUnit_iff.mp (Matrix.isUnits_det_units (torusUnit φ))

def IsPrimitive (v : ℤ × ℤ) : Prop := Int.gcd v.1 v.2 = 1

instance : DecidablePred IsPrimitive := fun v => inferInstanceAs (Decidable (Int.gcd v.1 v.2 = 1))

def slopeDet (v w : ℤ × ℤ) : ℤ := v.1 * w.2 - v.2 * w.1

def smulVec (A : Matrix (Fin 2) (Fin 2) ℤ) (v : ℤ × ℤ) : ℤ × ℤ :=
  (A 0 0 * v.1 + A 0 1 * v.2, A 1 0 * v.1 + A 1 1 * v.2)

theorem smulVec_eq_mulVec (A : Matrix (Fin 2) (Fin 2) ℤ) (v : ℤ × ℤ) :
    smulVec A v = LinearEquiv.finTwoArrow ℤ ℤ (A.mulVec ![v.1, v.2]) := by
  simp [smulVec, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem slopeDet_smulVec (A : Matrix (Fin 2) (Fin 2) ℤ) (v w : ℤ × ℤ) :
    slopeDet (smulVec A v) (smulVec A w) = A.det * slopeDet v w := by
  rw [Matrix.det_fin_two]
  simp only [slopeDet, smulVec]
  ring

theorem isPrimitive_smulVec {A : Matrix (Fin 2) (Fin 2) ℤ} (hA : IsUnit A.det) {v : ℤ × ℤ}
    (hv : IsPrimitive v) : IsPrimitive (smulVec A v) := by
  rw [IsPrimitive, ← Int.isCoprime_iff_gcd_eq_one] at hv ⊢
  obtain ⟨u, w, huw⟩ := hv
  have hd := Int.isUnit_mul_self hA
  refine ⟨A.det * (u * A 1 1 - w * A 1 0), A.det * (w * A 0 0 - u * A 0 1), ?_⟩
  rw [Matrix.det_fin_two] at hd ⊢
  simp only [smulVec]
  linear_combination (A 0 0 * A 1 1 - A 0 1 * A 1 0) ^ 2 * huw + hd

theorem eq_or_eq_neg_of_slopeDet_eq_zero {v w : ℤ × ℤ} (hv : IsPrimitive v) (hw : IsPrimitive w)
    (h : slopeDet v w = 0) : w = v ∨ w = -v := by
  rw [IsPrimitive, ← Int.isCoprime_iff_gcd_eq_one] at hv hw
  obtain ⟨u, u', hu⟩ := hv
  obtain ⟨x, x', hx⟩ := hw
  simp only [slopeDet] at h
  have h1 : w.1 = (u * w.1 + u' * w.2) * v.1 := by linear_combination (-u') * h + (-w.1) * hu
  have h2 : w.2 = (u * w.1 + u' * w.2) * v.2 := by linear_combination u * h + (-w.2) * hu
  have h3 : (u * w.1 + u' * w.2) * (x * v.1 + x' * v.2) = 1 := by
    linear_combination (-x) * h1 - x' * h2 + hx
  rcases Int.eq_one_or_neg_one_of_mul_eq_one h3 with hk | hk
  · exact Or.inl (Prod.ext (by linear_combination h1 + v.1 * hk)
      (by linear_combination h2 + v.2 * hk))
  · exact Or.inr (Prod.ext (by simp only [Prod.fst_neg]; linear_combination h1 + v.1 * hk)
      (by simp only [Prod.snd_neg]; linear_combination h2 + v.2 * hk))

def slopeSetoid : Setoid {v : ℤ × ℤ // IsPrimitive v} where
  r v w := w.1 = v.1 ∨ w.1 = -v.1
  iseqv := ⟨fun _ => Or.inl rfl, by rintro v w (h | h) <;> simp [h], by
    rintro u v w (h | h) (h' | h') <;> simp [h, h']⟩

def PrimitiveSlope : Type := Quotient slopeSetoid

namespace PrimitiveSlope

def mk (v : ℤ × ℤ) (hv : IsPrimitive v) : PrimitiveSlope := Quotient.mk slopeSetoid ⟨v, hv⟩

theorem mk_eq_mk_iff {v w : ℤ × ℤ} (hv : IsPrimitive v) (hw : IsPrimitive w) :
    mk v hv = mk w hw ↔ w = v ∨ w = -v :=
  Quotient.eq (r := slopeSetoid)

@[elab_as_elim]
theorem ind {motive : PrimitiveSlope → Prop} (h : ∀ v hv, motive (mk v hv))
    (s : PrimitiveSlope) : motive s :=
  Quotient.ind (fun v => h v.1 v.2) s

private theorem slopeDet_neg_left (v w : ℤ × ℤ) : slopeDet (-v) w = -slopeDet v w := by
  simp only [slopeDet, Prod.fst_neg, Prod.snd_neg]; ring

private theorem slopeDet_neg_right (v w : ℤ × ℤ) : slopeDet v (-w) = -slopeDet v w := by
  simp only [slopeDet, Prod.fst_neg, Prod.snd_neg]; ring

def delta (a b : PrimitiveSlope) : ℕ :=
  Quotient.lift₂ (s₁ := slopeSetoid) (s₂ := slopeSetoid)
    (fun v w => (slopeDet v.1 w.1).natAbs) (by
      rintro v w v' w' (h | h) (h' | h') <;>
        simp only [h, h', slopeDet_neg_left, slopeDet_neg_right, Int.natAbs_neg]) a b

theorem delta_mk {v w : ℤ × ℤ} (hv : IsPrimitive v) (hw : IsPrimitive w) :
    delta (mk v hv) (mk w hw) = (slopeDet v w).natAbs :=
  rfl

theorem delta_comm (a b : PrimitiveSlope) : delta a b = delta b a := by
  induction a using ind with | h v hv => ?_
  induction b using ind with | h w hw => ?_
  rw [delta_mk, delta_mk, ← Int.natAbs_neg]
  exact congrArg _ (by simp only [slopeDet]; ring)

theorem delta_eq_zero_iff (a b : PrimitiveSlope) : delta a b = 0 ↔ a = b := by
  induction a using ind with | h v hv => ?_
  induction b using ind with | h w hw => ?_
  rw [delta_mk, Int.natAbs_eq_zero, mk_eq_mk_iff]
  refine ⟨eq_or_eq_neg_of_slopeDet_eq_zero hv hw, ?_⟩
  rintro (rfl | rfl) <;> simp only [slopeDet, Prod.fst_neg, Prod.snd_neg] <;> ring

theorem delta_self (a : PrimitiveSlope) : delta a a = 0 :=
  (delta_eq_zero_iff a a).2 rfl

def act (A : GL (Fin 2) ℤ) : PrimitiveSlope → PrimitiveSlope :=
  Quotient.map (sa := slopeSetoid) (sb := slopeSetoid)
    (fun v => ⟨smulVec A v.1, isPrimitive_smulVec (Matrix.isUnits_det_units A) v.2⟩) (by
      rintro v w (h | h)
      · exact Or.inl (by simp only [h])
      · refine Or.inr ?_
        simp only [h, smulVec, Prod.fst_neg, Prod.snd_neg, Prod.neg_mk]
        congr 1 <;> ring)

instance : MulAction (GL (Fin 2) ℤ) PrimitiveSlope where
  smul := act
  one_smul s := by
    induction s using ind with | h v hv => ?_
    exact (mk_eq_mk_iff _ hv).2 (Or.inl (by simp [smulVec]))
  mul_smul A B s := by
    induction s using ind with | h v hv => ?_
    refine (mk_eq_mk_iff _ _).2 (Or.inl ?_)
    simp only [smulVec, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
    congr 1 <;> ring

theorem smul_mk (A : GL (Fin 2) ℤ) {v : ℤ × ℤ} (hv : IsPrimitive v) :
    A • mk v hv = mk (smulVec A v) (isPrimitive_smulVec (Matrix.isUnits_det_units A) hv) :=
  rfl

theorem delta_smul (A : GL (Fin 2) ℤ) (a b : PrimitiveSlope) :
    delta (A • a) (A • b) = delta a b := by
  induction a using ind with | h v hv => ?_
  induction b using ind with | h w hw => ?_
  rw [smul_mk, smul_mk, delta_mk, delta_mk, slopeDet_smulVec, Int.natAbs_mul,
    Int.isUnit_iff_natAbs_eq.mp (Matrix.isUnits_det_units A), one_mul]

def unitOfDet (A : Matrix (Fin 2) (Fin 2) ℤ) (hA : A.det = 1 ∨ A.det = -1) : GL (Fin 2) ℤ :=
  Matrix.nonsingInvUnit A (Int.isUnit_iff.mpr hA)

theorem val_unitOfDet (A : Matrix (Fin 2) (Fin 2) ℤ) (hA : A.det = 1 ∨ A.det = -1) :
    (unitOfDet A hA : Matrix (Fin 2) (Fin 2) ℤ) = A :=
  rfl

example : ¬ IsPrimitive (0, 2) := by decide

example (a : PrimitiveSlope) : delta a a = 0 := delta_self a

example : delta (mk (1, 0) (by decide)) (mk (0, 1) (by decide)) = 1 := rfl

example (p q : ℤ) (h : IsPrimitive (p, q)) :
    delta (mk (1, 0) (by decide)) (mk (p, q) h) = q.natAbs := by
  simp [delta_mk, slopeDet]

example : mk (1, 0) (by decide) ≠ mk (0, 1) (by decide) := by
  rw [Ne, ← delta_eq_zero_iff, delta_mk]; decide

example : unitOfDet !![0, 1; 1, 0] (Or.inr (by rw [Matrix.det_fin_two_of]; rfl)) •
    mk (1, 0) (by decide) = mk (0, 1) (by decide) := by
  rw [smul_mk, mk_eq_mk_iff]
  left
  simp [smulVec, val_unitOfDet]

end PrimitiveSlope

end GC.Seifert
