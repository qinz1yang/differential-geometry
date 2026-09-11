import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.MetricCompatibleTimeDerivative
import DifferentialGeometry.Tensor.Multilinear.Bundle.TensorProduct

set_option autoImplicit false
noncomputable section
open Set Bundle Manifold DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature Bundle.continuousMultilinearMap
open scoped Manifold ContDiff BigOperators
namespace DifferentialGeometry.PDE.RicciFlow
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private theorem castAdd_ne_natAdd {s q : ℕ} (a : Fin s) (b : Fin q) :
    Fin.castAdd q a ≠ Fin.natAdd s b := by
  intro h
  have hh := Fin.val_eq_of_eq h
  simp only [Fin.val_castAdd, Fin.val_natAdd] at hh
  omega

omit [FiniteDimensional ℝ E] in
private theorem product_eval {s q : ℕ} {x : M}
    (A : Tensor0SSpace s I x) (B : Tensor0SSpace q I x)
    (v : Fin (s + q) → TangentSpace I x) :
    (productFun (F := E) (E := TangentSpace I) A B : Tensor0SSpace (s + q) I x) v =
      A (v ∘ Fin.castAdd q) * B (v ∘ Fin.natAdd s) := by
  exact product_fun_apply A B v

theorem hasDerivWithinAt_tensor0S_product {s q : ℕ} {x : M}
    (A : ℝ → Tensor0SSpace s I x) (B : ℝ → Tensor0SSpace q I x)
    (Adot : Tensor0SSpace s I x) (Bdot : Tensor0SSpace q I x) (J : Set ℝ) (t : ℝ)
    (hA : ∀ v : Fin s → TangentSpace I x, HasDerivWithinAt (fun r => A r v) (Adot v) J t)
    (hB : ∀ v : Fin q → TangentSpace I x, HasDerivWithinAt (fun r => B r v) (Bdot v) J t) :
    HasDerivWithinAt (fun r => (productFun (F := E) (E := TangentSpace I) (A r) (B r) :
      Tensor0SSpace (s + q) I x))
      (productFun (F := E) (E := TangentSpace I) Adot (B t) +
        productFun (F := E) (E := TangentSpace I) (A t) Bdot) J t := by
  apply hasDerivWithinAt_tensor0S_of_eval (I := I)
  intro v
  have hh := (hA (v ∘ Fin.castAdd q)).mul (hB (v ∘ Fin.natAdd s))
  convert hh using 1 <;> try rfl
  · funext r
    exact product_eval (A r) (B r) v
  · exact (Tensor0SSpace.add_apply (s + q) x
      (productFun (F := E) (E := TangentSpace I) Adot (B t))
      (productFun (F := E) (E := TangentSpace I) (A t) Bdot) v).trans
        (congrArg₂ (fun z w : ℝ => z + w) (product_eval Adot (B t) v) (product_eval (A t) Bdot v))

variable [T2Space M] [BoundarylessManifold I M]

theorem ricciTimeCorrection_product {s q : ℕ} {x : M}
    (g : SmoothRiemannianMetric I M) (A : Tensor0SSpace s I x) (B : Tensor0SSpace q I x) :
    ricciTimeCorrection g (productFun (F := E) (E := TangentSpace I) A B) =
      productFun (F := E) (E := TangentSpace I) (ricciTimeCorrection g A) B +
        productFun (F := E) (E := TangentSpace I) A (ricciTimeCorrection g B) := by
  apply tensor0SSpace_ext (I := I) (s + q) x
  intro v
  have hsplit : (∑ k : Fin (s + q),
      A (Function.update v k (ricciSharp g x (v k)) ∘ Fin.castAdd q) *
        B (Function.update v k (ricciSharp g x (v k)) ∘ Fin.natAdd s)) =
          (∑ a : Fin s, A (Function.update (v ∘ Fin.castAdd q) a (ricciSharp g x (v (Fin.castAdd q a))))) *
              B (v ∘ Fin.natAdd s) + A (v ∘ Fin.castAdd q) *
          (∑ b : Fin q, B (Function.update (v ∘ Fin.natAdd s) b (ricciSharp g x (v (Fin.natAdd s b))))) := by
    rw [Fin.sum_univ_add, Finset.sum_mul, Finset.mul_sum]
    congr 1
    · apply Finset.sum_congr rfl
      intro a _
      rw [Function.update_comp_eq_of_injective v (Fin.castAdd_injective s q),
        Function.update_comp_eq_of_forall_ne v _ (fun b => Ne.symm (castAdd_ne_natAdd a b))]
    · apply Finset.sum_congr rfl
      intro b _
      rw [Function.update_comp_eq_of_forall_ne v _ (fun a => castAdd_ne_natAdd a b),
        Function.update_comp_eq_of_injective v (Fin.natAdd_injective q s)]
  have he := ricciTimeCorrection_apply g (productFun (F := E) (E := TangentSpace I) A B) v
  have hs := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun k _ => product_eval A B (Function.update v k (ricciSharp g x (v k))))
  have hr : (productFun (F := E) (E := TangentSpace I) (ricciTimeCorrection g A) B +
      productFun (F := E) (E := TangentSpace I) A (ricciTimeCorrection g B) : Tensor0SSpace (s + q) I x) v =
        (ricciTimeCorrection g A (v ∘ Fin.castAdd q)) * B (v ∘ Fin.natAdd s) +
          A (v ∘ Fin.castAdd q) * (ricciTimeCorrection g B (v ∘ Fin.natAdd s)) :=
    (Tensor0SSpace.add_apply (s + q) x _ _ v).trans
      (congrArg₂ (fun z w : ℝ => z + w) (product_eval (ricciTimeCorrection g A) B v)
        (product_eval A (ricciTimeCorrection g B) v))
  exact (he.trans (hs.trans hsplit)).trans ((hr.trans
    (congrArg₂ (fun z w : ℝ => z * B (v ∘ Fin.natAdd s) + A (v ∘ Fin.castAdd q) * w)
      (ricciTimeCorrection_apply g A (v ∘ Fin.castAdd q))
      (ricciTimeCorrection_apply g B (v ∘ Fin.natAdd s)))).symm)

theorem covariantTimeDerivWithin_product {s q : ℕ} {x : M}
    (g : ℝ → SmoothRiemannianMetric I M)
    (A : ℝ → Tensor0SSpace s I x) (B : ℝ → Tensor0SSpace q I x)
    (Adot : Tensor0SSpace s I x) (Bdot : Tensor0SSpace q I x)
    (J : Set ℝ) (t : ℝ) (hJ : UniqueDiffWithinAt ℝ J t)
    (hA : ∀ v : Fin s → TangentSpace I x, HasDerivWithinAt (fun r => A r v) (Adot v) J t)
    (hB : ∀ v : Fin q → TangentSpace I x, HasDerivWithinAt (fun r => B r v) (Bdot v) J t) :
    covariantTimeDerivWithin g
      (fun r => productFun (F := E) (E := TangentSpace I) (A r) (B r)) J t =
        productFun (F := E) (E := TangentSpace I) (covariantTimeDerivWithin g A J t) (B t) +
          productFun (F := E) (E := TangentSpace I) (A t) (covariantTimeDerivWithin g B J t) := by
  have ha : derivWithin A J t = Adot := (hasDerivWithinAt_tensor0S_of_eval A Adot J t hA).derivWithin hJ
  have hb : derivWithin B J t = Bdot := (hasDerivWithinAt_tensor0S_of_eval B Bdot J t hB).derivWithin hJ
  let P : ℝ → Tensor0SSpace (s + q) I x := fun r => productFun (F := E) (E := TangentSpace I) (A r) (B r)
  let Pdot : Tensor0SSpace (s + q) I x := productFun (F := E) (E := TangentSpace I) Adot (B t) +
    productFun (F := E) (E := TangentSpace I) (A t) Bdot
  have hprod : HasDerivWithinAt P Pdot J t := hasDerivWithinAt_tensor0S_product A B Adot Bdot J t hA hB
  have hp : derivWithin P J t = Pdot := hprod.derivWithin hJ
  have hca : covariantTimeDerivWithin g A J t = Adot + ricciTimeCorrection (g t) (A t) :=
    congrArg (fun V : Tensor0SSpace s I x => V + ricciTimeCorrection (g t) (A t)) ha
  have hcb : covariantTimeDerivWithin g B J t = Bdot + ricciTimeCorrection (g t) (B t) :=
    congrArg (fun V : Tensor0SSpace q I x => V + ricciTimeCorrection (g t) (B t)) hb
  have hcp : covariantTimeDerivWithin g P J t = Pdot + ricciTimeCorrection (g t) (P t) :=
    congrArg (fun V : Tensor0SSpace (s + q) I x => V + ricciTimeCorrection (g t) (P t)) hp
  change covariantTimeDerivWithin g P J t = _
  rw [hcp, hca, hcb, ricciTimeCorrection_product]
  apply tensor0SSpace_ext (s + q) x
  intro v
  let C := ricciTimeCorrection (g t) (A t)
  let D := ricciTimeCorrection (g t) (B t)
  let va := v ∘ Fin.castAdd q
  let vb := v ∘ Fin.natAdd s
  have hv (U V : Tensor0SSpace (s + q) I x) : (U + V) v = U v + V v :=
    Tensor0SSpace.add_apply (s + q) x U V v
  let C₁ : Tensor0SSpace (s + q) I x := productFun (F := E) (E := TangentSpace I) C (B t)
  let C₂ : Tensor0SSpace (s + q) I x := productFun (F := E) (E := TangentSpace I) (A t) D
  let Q₁ : Tensor0SSpace (s + q) I x := productFun (F := E) (E := TangentSpace I) (Adot + C) (B t)
  let Q₂ : Tensor0SSpace (s + q) I x := productFun (F := E) (E := TangentSpace I) (A t) (Bdot + D)
  have hL : (Pdot + (C₁ + C₂)) v =
        (Adot va * B t vb + A t va * Bdot vb) + (C va * B t vb + A t va * D vb) :=
    (hv _ _).trans (congrArg₂ (fun z w : ℝ => z + w)
      ((hv _ _).trans (congrArg₂ (fun z w : ℝ => z + w)
        (product_eval Adot (B t) v) (product_eval (A t) Bdot v)))
      ((hv _ _).trans (congrArg₂ (fun z w : ℝ => z + w)
        (product_eval C (B t) v) (product_eval (A t) D v))))
  have hR : (Q₁ + Q₂) v =
        (Adot va + C va) * B t vb + A t va * (Bdot vb + D vb) :=
    (hv _ _).trans (congrArg₂ (fun z w : ℝ => z + w)
      ((product_eval (Adot + C) (B t) v).trans
        (congrArg (fun z : ℝ => z * B t vb) (Tensor0SSpace.add_apply s x Adot C va)))
      ((product_eval (A t) (Bdot + D) v).trans
        (congrArg (fun z : ℝ => A t va * z) (Tensor0SSpace.add_apply q x Bdot D vb))))
  exact hL.trans ((by ring :
    (Adot va * B t vb + A t va * Bdot vb) + (C va * B t vb + A t va * D vb) =
      (Adot va + C va) * B t vb + A t va * (Bdot vb + D vb)).trans hR.symm)
end DifferentialGeometry.PDE.RicciFlow
