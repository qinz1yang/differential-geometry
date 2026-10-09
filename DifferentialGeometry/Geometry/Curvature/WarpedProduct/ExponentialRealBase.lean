import DifferentialGeometry.Geometry.Connection.Product
import DifferentialGeometry.Geometry.Curvature.Product
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.ConnectionDifference.Curvature
import DifferentialGeometry.Geometry.Curvature.WarpedProduct
import DifferentialGeometry.Geometry.Curvature.Line
import DifferentialGeometry.Geometry.Metric.Euclidean
import DifferentialGeometry.Bundle.PartialMfderiv.Basic

set_option autoImplicit false
noncomputable section

open Bundle Manifold
open scoped Manifold ContDiff
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.Geometry.VectorField

namespace DifferentialGeometry.Geometry.Curvature

private def realConst (a : ℝ) :
    Cₛ^∞⟮𝓘(ℝ, ℝ); ℝ, (TangentSpace 𝓘(ℝ, ℝ) : ℝ → Type _)⟯ where
  toFun _ := a
  contMDiff_toFun := by
    apply (contMDiff_vectorSpace_iff_contDiff (𝕜 := ℝ)).mpr
    exact contDiff_const

private theorem mlieBracket_realConst (a b r : ℝ) :
    _root_.VectorField.mlieBracket 𝓘(ℝ, ℝ) (realConst a) (realConst b) r = 0 := by
  rw [← _root_.VectorField.mlieBracketWithin_univ,
    _root_.VectorField.mlieBracketWithin_eq_lieBracketWithin]
  change (fderivWithin ℝ (fun _ : ℝ => b) Set.univ r) a -
    (fderivWithin ℝ (fun _ : ℝ => a) Set.univ r) b = 0
  simp

private theorem leviCivita_realConst (a r v : ℝ) :
    (LeviCivita (euclideanMetric (E := ℝ))) (realConst a) r v = 0 := by
  dsimp only [TangentSpace] at *
  have hk := leviCivitaConnectionOfMetric_inner_eq_koszulScalar
    (euclideanMetric (E := ℝ)) (realConst v) (realConst a) (realConst 1) r
    (realConst v).mdifferentiableAt (realConst a).mdifferentiableAt
    (realConst 1).mdifferentiableAt
  simp only [koszulScalar, directionalDerivAlong, mlieBracket_realConst,
    map_zero, sub_zero, add_zero] at hk
  change (1 : ℝ) * (show ℝ from (LeviCivita (euclideanMetric (E := ℝ))) (realConst a) r v) =
    (1 / 2 : ℝ) *
      ((show ℝ from mvfderiv 𝓘(ℝ, ℝ) (fun _ : ℝ => 1 * a) r v) +
        (show ℝ from mvfderiv 𝓘(ℝ, ℝ) (fun _ : ℝ => v * 1) r a) -
        (show ℝ from mvfderiv 𝓘(ℝ, ℝ) (fun _ : ℝ => a * v) r 1)) at hk
  have hc : ∀ c x : ℝ, (show ℝ from mvfderiv 𝓘(ℝ, ℝ) (fun _ : ℝ => c) r x) = 0 :=
    fun c x => by rw [mvfderiv_const]; rfl
  have hc1 : (show ℝ from mvfderiv 𝓘(ℝ, ℝ) (fun _ : ℝ => a * v) r 1) = 0 := by
    rw [mvfderiv_const]; rfl
  simp only [hc, hc1] at hk
  exact (one_mul _).symm.trans (hk.trans (by norm_num; rfl))

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

private def realBaseField (a : ℝ)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :=
  productVectorField (realConst a) X

omit [FiniteDimensional ℝ E] [T2Space M] in
private theorem realBaseField_apply (a : ℝ)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (p : ℝ × M) :
    realBaseField a X p = (a, X p.2) := rfl

set_option backward.isDefEq.respectTransparency false in
private theorem mlieBracket_realBaseField (a b : ℝ)
    (X Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (p : ℝ × M) :
    _root_.VectorField.mlieBracket (𝓘(ℝ, ℝ).prod I)
        (realBaseField a X) (realBaseField b Y) p =
      (0, _root_.VectorField.mlieBracket I X Y p.2) := by
  rw [realBaseField, realBaseField, mlieBracket_productVectorField,
    mlieBracket_realConst]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M] in
private theorem mvfderiv_exp_mul_snd (F : M → ℝ) (p : ℝ × M)
    (hF : MDifferentiableAt I 𝓘(ℝ, ℝ) F p.2)
    (v : TangentSpace (𝓘(ℝ, ℝ).prod I) p) :
    mvfderiv (𝓘(ℝ, ℝ).prod I) (fun z : ℝ × M => Real.exp (-z.1) * F z.2) p v =
      Real.exp (-p.1) * (mvfderiv I F p.2 v.2 - v.1 * F p.2) := by
  have he : HasDerivAt (fun r : ℝ => Real.exp (-r)) (-Real.exp (-p.1)) p.1 := by
    simpa using (hasDerivAt_id p.1).neg.exp
  have hec := mvfderiv_comp p he.differentiableAt.mdifferentiableAt
    (mdifferentiableAt_fst (I := 𝓘(ℝ, ℝ)) (I' := I))
  have hFc := mvfderiv_comp p hF
    (mdifferentiableAt_snd (I := 𝓘(ℝ, ℝ)) (I' := I))
  have heD : mvfderiv 𝓘(ℝ, ℝ) (fun r : ℝ => Real.exp (-r)) p.1 =
      (1 : ℝ →L[ℝ] ℝ).smulRight (-Real.exp (-p.1)) := by
    change mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) _ _ = _
    rw [mfderiv_eq_fderiv]
    exact he.hasFDerivAt.fderiv
  rw [mfderiv_fst, heD] at hec
  rw [mfderiv_snd] at hFc
  have hm := congrArg (fun L : TangentSpace (𝓘(ℝ, ℝ).prod I) p →L[ℝ] ℝ => L v)
    (mvfderiv_mul
      (he.differentiableAt.mdifferentiableAt.comp p mdifferentiableAt_fst)
      (hF.comp p mdifferentiableAt_snd))
  rw [hec, hFc] at hm
  change mvfderiv (𝓘(ℝ, ℝ).prod I) (fun z : ℝ × M => Real.exp (-z.1) * F z.2) p v =
    Real.exp (-p.1) * mvfderiv I F p.2 v.2 + F p.2 * (v.1 * -Real.exp (-p.1)) at hm
  exact hm.trans (by ring)

variable (G : SmoothRiemannianMetric (𝓘(ℝ, ℝ).prod I) (ℝ × M))
  (h : SmoothRiemannianMetric I M)
  (hG : ∀ (p : ℝ × M) (v w : TangentSpace (𝓘(ℝ, ℝ).prod I) p),
    G.inner p v w = v.1 * w.1 + Real.exp (-p.1) * h.inner p.2 v.2 w.2)

include hG

omit [FiniteDimensional ℝ E] [T2Space M] in
set_option backward.isDefEq.respectTransparency false in
private theorem exponential_inner_deriv (a b : ℝ)
    (X Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (p : ℝ × M)
    (v : TangentSpace (𝓘(ℝ, ℝ).prod I) p) :
    mvfderiv (𝓘(ℝ, ℝ).prod I)
        (fun z => G.inner z (realBaseField a X z) (realBaseField b Y z)) p v =
      Real.exp (-p.1) *
        (mvfderiv I (fun q => h.inner q (X q) (Y q)) p.2 v.2 -
          v.1 * h.inner p.2 (X p.2) (Y p.2)) := by
  have heq : (fun z => G.inner z (realBaseField a X z) (realBaseField b Y z)) =
      (fun z : ℝ × M => a * b + Real.exp (-z.1) * h.inner z.2 (X z.2) (Y z.2)) := by
    funext z
    exact hG z _ _
  rw [heq]
  have hF := (contMDiff_metric_inner h X Y).mdifferentiable (by simp) p.2
  have he : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ)
      (fun z : ℝ × M => Real.exp (-z.1) * h.inner z.2 (X z.2) (Y z.2)) p :=
    ((Real.contDiff_exp.contMDiff.comp contMDiff_fst.neg).mul
      ((contMDiff_metric_inner h X Y).comp contMDiff_snd)).mdifferentiableAt (by simp)
  rw [show (fun z : ℝ × M => a * b + Real.exp (-z.1) * h.inner z.2 (X z.2) (Y z.2)) =
    (fun _ : ℝ × M => a * b) +
      (fun z : ℝ × M => Real.exp (-z.1) * h.inner z.2 (X z.2) (Y z.2)) from rfl,
    mvfderiv_add mdifferentiableAt_const he, mvfderiv_const, zero_add]
  exact mvfderiv_exp_mul_snd _ p hF v

set_option backward.isDefEq.respectTransparency false in
private theorem koszulScalar_exponential (a b c : ℝ)
    (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (p : ℝ × M) :
    koszulScalar G (realBaseField a X) (realBaseField b Y) (realBaseField c Z) p =
      Real.exp (-p.1) * (koszulScalar h X Y Z p.2 -
        a * h.inner p.2 (Y p.2) (Z p.2) -
        b * h.inner p.2 (Z p.2) (X p.2) +
        c * h.inner p.2 (X p.2) (Y p.2)) := by
  simp only [koszulScalar, directionalDerivAlong]
  rw [exponential_inner_deriv G h hG, exponential_inner_deriv G h hG,
    exponential_inner_deriv G h hG]
  simp only [mlieBracket_realBaseField, realBaseField_apply, hG,
    mul_zero, zero_add]
  ring

set_option backward.isDefEq.respectTransparency false in
private theorem leviCivita_exponential_realBaseField (b : ℝ)
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (p : ℝ × M)
    (v : TangentSpace (𝓘(ℝ, ℝ).prod I) p) :
    (LeviCivita G) (realBaseField b Y) p v =
      (Real.exp (-p.1) / 2 * h.inner p.2 v.2 (Y p.2),
        (show E from (LeviCivita h) Y p.2 v.2) -
          (1 / 2 : ℝ) • (v.1 • (show E from Y p.2) + b • (show E from v.2))) := by
  dsimp only [TangentSpace] at *
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  apply SmoothRiemannianMetric.eq_of_inner_eq G
  intro w
  obtain ⟨X, hX⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
    (V := TangentSpace I) (n := (⊤ : ℕ∞)) p.2 v.2
  obtain ⟨Z, hZ⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
    (V := TangentSpace I) (n := (⊤ : ℕ∞)) p.2 w.2
  have hv : realBaseField v.1 X p = v := Prod.ext rfl hX
  have hw : realBaseField w.1 Z p = w := Prod.ext rfl hZ
  have hk := leviCivitaConnectionOfMetric_inner_eq_koszulScalar G
    (realBaseField v.1 X) (realBaseField b Y) (realBaseField w.1 Z) p
    (realBaseField v.1 X).mdifferentiableAt
    (realBaseField b Y).mdifferentiableAt (realBaseField w.1 Z).mdifferentiableAt
  rw [hv, hw] at hk
  change G.inner p ((LeviCivita G) (realBaseField b Y) p v) w = _ at hk
  refine hk.trans ?_
  rw [koszulScalar_exponential G h hG]
  have hb := leviCivitaConnectionOfMetric_inner_eq_koszulScalar h X Y Z p.2
    X.mdifferentiableAt Y.mdifferentiableAt Z.mdifferentiableAt
  rw [hX, hZ] at hb
  change h.inner p.2 ((LeviCivita h) Y p.2 v.2) w.2 = _ at hb
  rw [hX, hZ]
  erw [hG]
  have hexp : ∀ A B C : E, h.inner p.2 (A - (1 / 2 : ℝ) • (v.1 • B + b • C)) w.2 =
      h.inner p.2 A w.2 - 1 / 2 * (v.1 * h.inner p.2 B w.2 + b * h.inner p.2 C w.2) := by
    intro A B C
    simp only [map_sub, sub_apply, map_smul, smul_apply, map_add, add_apply, smul_eq_mul]
  erw [hexp]
  erw [hb, h.symm p.2 w.2 v.2]
  ring_nf
  rfl

omit G hG in
private theorem leviCivita_product_realBaseField (b : ℝ)
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (p : ℝ × M)
    (v : TangentSpace (𝓘(ℝ, ℝ).prod I) p) :
    (LeviCivita ((euclideanMetric (E := ℝ)).prod h)) (realBaseField b Y) p v =
      (0, (LeviCivita h) Y p.2 v.2) := by
  dsimp only [TangentSpace] at *
  have he := leviCivita_productVectorField_apply (euclideanMetric (E := ℝ)) h
    (realConst b) Y p v
  change (LeviCivita ((euclideanMetric (E := ℝ)).prod h)) (realBaseField b Y) p v =
    ((LeviCivita (euclideanMetric (E := ℝ))) (realConst b) p.1 v.1,
      (LeviCivita h) Y p.2 v.2) at he
  refine he.trans ?_
  exact Prod.ext (leviCivita_realConst b p.1 v.1) rfl

set_option backward.isDefEq.respectTransparency false in
private theorem connectionDifference_exponential (p : ℝ × M)
    (v w : TangentSpace (𝓘(ℝ, ℝ).prod I) p) :
    CovariantDerivative.difference (LeviCivita G)
        (LeviCivita ((euclideanMetric (E := ℝ)).prod h)) p w v =
      (Real.exp (-p.1) / 2 * h.inner p.2 v.2 w.2,
        -(1 / 2 : ℝ) • (v.1 • w.2 + w.1 • v.2)) := by
  dsimp only [TangentSpace] at *
  obtain ⟨Y, hY⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
    (V := TangentSpace I) (n := (⊤ : ℕ∞)) p.2 w.2
  have hw : realBaseField w.1 Y p = w := Prod.ext rfl hY
  have he := diff_eval (LeviCivita ((euclideanMetric (E := ℝ)).prod h)) (LeviCivita G)
    (realBaseField w.1 Y).mdifferentiableAt v
  rw [hw, leviCivita_exponential_realBaseField G h hG,
    leviCivita_product_realBaseField h, hY] at he
  refine he.trans ?_
  apply Prod.ext
  · exact sub_zero _
  · change (_ - (1 / 2 : ℝ) • _) - _ = _
    module

set_option backward.isDefEq.respectTransparency false in
private theorem covDerivDiff_exponential (a b c : ℝ)
    (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (p : ℝ × M) :
    covDerivDiff (LeviCivita ((euclideanMetric (E := ℝ)).prod h)) (LeviCivita G)
        (realBaseField a X) (realBaseField b Y) (realBaseField c Z) p =
      (-Real.exp (-p.1) / 2 * a * h.inner p.2 (Y p.2) (Z p.2), 0) := by
  dsimp only [TangentSpace] at *
  let C := LeviCivita ((euclideanMetric (E := ℝ)).prod h)
  let A := realBaseField (I := I) (M := M) 1 0
  let Y₀ := realBaseField 0 Y
  let Z₀ := realBaseField 0 Z
  let F : ℝ × M → ℝ := fun q => Real.exp (-q.1) / 2 * h.inner q.2 (Y q.2) (Z q.2)
  have hF : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) F p := by
    exact (((Real.contDiff_exp.contMDiff.comp contMDiff_fst.neg).mul contMDiff_const).mul
      ((contMDiff_metric_inner h Y Z).comp contMDiff_snd)).mdifferentiableAt (by simp)
  have hd : diffSec C (LeviCivita G) (realBaseField b Y) (realBaseField c Z) =
      F • (A : (q : ℝ × M) → TangentSpace (𝓘(ℝ, ℝ).prod I) q) +
        (fun _ : ℝ × M => -(b / 2)) • Z₀ +
        (fun _ : ℝ × M => -(c / 2)) • Y₀ := by
    funext q
    change CovariantDerivative.difference (LeviCivita G)
      (LeviCivita ((euclideanMetric (E := ℝ)).prod h)) q _ _ = _
    rw [connectionDifference_exponential G h hG]
    apply Prod.ext
    · change Real.exp (-q.1) / 2 * h.inner q.2 (Y q.2) (Z q.2) =
        F q * 1 + (-(b / 2)) * 0 + (-(c / 2)) * 0
      simp [F]
    · change -(1 / 2 : ℝ) • (b • Z q.2 + c • Y q.2) =
        F q • (0 : TangentSpace I q.2) + (-(b / 2)) • Z q.2 + (-(c / 2)) • Y q.2
      module
  have hA := A.mdifferentiableAt (x := p)
  have hY := Y₀.mdifferentiableAt (x := p)
  have hZ := Z₀.mdifferentiableAt (x := p)
  have hb := mdifferentiableAt_const (I := 𝓘(ℝ, ℝ).prod I) (I' := 𝓘(ℝ, ℝ)) (M' := ℝ)
    (x := p) (c := -(b / 2))
  have hc := mdifferentiableAt_const (I := 𝓘(ℝ, ℝ).prod I) (I' := 𝓘(ℝ, ℝ)) (M' := ℝ)
    (x := p) (c := -(c / 2))
  have hDA := C.isCovariantDerivativeOnUniv.leibniz hA hF
  have hDZ := C.isCovariantDerivativeOnUniv.leibniz hZ hb
  have hDY := C.isCovariantDerivativeOnUniv.leibniz hY hc
  have hsum := C.isCovariantDerivativeOnUniv.add
    (mdifferentiableAt_add_section (hF.smul_section hA) (hb.smul_section hZ))
    (hc.smul_section hY)
  have hsum' := C.isCovariantDerivativeOnUniv.add (hF.smul_section hA)
    (hb.smul_section hZ)
  have hFval : mvfderiv (𝓘(ℝ, ℝ).prod I) F p (realBaseField a X p) =
      Real.exp (-p.1) / 2 *
        (h.inner p.2 ((LeviCivita h) Y p.2 (X p.2)) (Z p.2) +
          h.inner p.2 (Y p.2) ((LeviCivita h) Z p.2 (X p.2)) -
          a * h.inner p.2 (Y p.2) (Z p.2)) := by
    have heq : F = fun q : ℝ × M =>
        (1 / 2 : ℝ) * (Real.exp (-q.1) * h.inner q.2 (Y q.2) (Z q.2)) := by
      funext q
      dsimp [F]
      ring
    have hraw : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ)
        (fun q : ℝ × M => Real.exp (-q.1) * h.inner q.2 (Y q.2) (Z q.2)) p :=
      ((Real.contDiff_exp.contMDiff.comp contMDiff_fst.neg).mul
        ((contMDiff_metric_inner h Y Z).comp contMDiff_snd)).mdifferentiableAt (by simp)
    rw [heq, DifferentialGeometry.mvfderiv_const_mul _ _ hraw]
    change (1 / 2 : ℝ) * mvfderiv (𝓘(ℝ, ℝ).prod I)
      (fun q : ℝ × M => Real.exp (-q.1) * h.inner q.2 (Y q.2) (Z q.2))
        p (realBaseField a X p) = _
    rw [mvfderiv_exp_mul_snd _ p
      ((contMDiff_metric_inner h Y Z).mdifferentiableAt (by simp))]
    have hmc : IsMetricCompatible (LeviCivita h) h := by
      simpa only [LeviCivita_eq_leviCivitaConnectionOfMetric] using
        leviCivitaConnectionOfMetric_isMetricCompatible h
    have hm := hmc.apply
      Y.mdifferentiableAt Z.mdifferentiableAt (X p.2)
    change mvfderiv I (fun q => h.inner q (Y q) (Z q)) p.2 (X p.2) = _ at hm
    rw [show (realBaseField a X p).2 = X p.2 from rfl, hm]
    have ha : (realBaseField a X p).1 = a := rfl
    erw [ha]
    ring
  unfold covDerivDiff
  change C _ p _ - _ - _ = _
  rw [hd, hsum, hsum', hDA, hDZ, hDY]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
    mvfderiv_const, ContinuousLinearMap.zero_apply, zero_smul, add_zero]
  rw [hFval]
  change _ - CovariantDerivative.difference (LeviCivita G)
      (LeviCivita ((euclideanMetric (E := ℝ)).prod h)) p _ _ -
      CovariantDerivative.difference (LeviCivita G)
      (LeviCivita ((euclideanMetric (E := ℝ)).prod h)) p _ _ = _
  simp only [C, A, Y₀, Z₀, covApply, leviCivita_product_realBaseField,
    connectionDifference_exponential G h hG, realBaseField_apply]
  have hz := (LeviCivita h).zero
  have hz0 : ((LeviCivita h) (⇑(0 : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)) p.2) (X p.2) =
      0 := by
    rw [show (⇑(0 : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)) = 0 from rfl, hz]
    rfl
  apply Prod.ext
  · change (_ : ℝ) * 0 + _ * 1 + _ * 0 + _ * 0 - _ - _ = _
    ring_nf
    rfl
  · rw [hz0]
    let u2 : E := (LeviCivita h) Y p.2 (X p.2)
    let u3 : E := (LeviCivita h) Z p.2 (X p.2)
    change (F p • (0 : E) + (_ : ℝ) • (0 : E) + (-(b / 2)) • u3 + (-(c / 2)) • u2) -
      (-(1 / 2 : ℝ)) • ((0 : ℝ) • (show E from Z p.2) + c • u2) -
      (-(1 / 2 : ℝ)) • (b • u3 + (0 : ℝ) • (show E from Y p.2)) = 0
    module

/-- The actual Levi-Civita connection difference for `dr² + exp(-r) h`.
The formula retains the supplied metric and requires no fiber curvature premise. -/
theorem connectionDifference_of_exponentialRealBase_inner (p : ℝ × M)
    (v w : TangentSpace (𝓘(ℝ, ℝ).prod I) p) :
    CovariantDerivative.difference (LeviCivita G)
        (LeviCivita ((euclideanMetric (E := ℝ)).prod h)) p w v =
      (Real.exp (-p.1) / 2 * h.inner p.2 v.2 w.2,
        -(1 / 2 : ℝ) • (v.1 • w.2 + w.1 • v.2)) :=
  connectionDifference_exponential G h hG p v w

variable [I.Boundaryless] [BoundarylessManifold I M]

set_option backward.isDefEq.respectTransparency false in
/-- The actual curvature numerator of `dr² + exp(-r) h`, with no flatness
assumption on the fiber. The fiber term keeps the same metric and point. -/
theorem metricRm04StandardAt_of_exponentialRealBase_inner
    (p : ℝ × M) (v w : TangentSpace (𝓘(ℝ, ℝ).prod I) p) :
    metricRm04StandardAt G p v w w v =
      Real.exp (-p.1) * metricRm04StandardAt h p.2 v.2 w.2 w.2 v.2 -
        (1 / 4 : ℝ) * (G.inner p v v * G.inner p w w - G.inner p v w ^ 2) := by
  dsimp only [TangentSpace] at *
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨X, hX⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
    (V := TangentSpace I) (n := (⊤ : ℕ∞)) p.2 v.2
  obtain ⟨Y, hY⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
    (V := TangentSpace I) (n := (⊤ : ℕ∞)) p.2 w.2
  let V := realBaseField v.1 X
  let W := realBaseField w.1 Y
  let B := (euclideanMetric (E := ℝ)).prod h
  have hv : V p = v := Prod.ext rfl hX
  have hw : W p = w := Prod.ext rfl hY
  have hr := riemannSec_difference (LeviCivita B) (LeviCivita G)
    V.contMDiff W.contMDiff W.contMDiff (LeviCivita_torsion_eq_zero B) p
  change riemannSec (LeviCivita G) V W W p =
    riemannSec (LeviCivita B) V W W p +
      (covDerivDiff (LeviCivita B) (LeviCivita G) V W W p -
        covDerivDiff (LeviCivita B) (LeviCivita G) W V W p) + _ at hr
  rw [show V = realBaseField v.1 X from rfl,
    show W = realBaseField w.1 Y from rfl,
    covDerivDiff_exponential G h hG, covDerivDiff_exponential G h hG] at hr
  change riemannSec (LeviCivita G) V W W p = _ at hr
  rw [← riemannOp_apply_smooth (cov := LeviCivita G) V.contMDiff W.contMDiff W.contMDiff,
    ← riemannOp_apply_smooth (cov := LeviCivita B) V.contMDiff W.contMDiff W.contMDiff,
    hv, hw, hX, hY] at hr
  simp only [diffSec, B, connectionDifference_exponential G h hG,
    realBaseField_apply, hX, hY] at hr
  rw [riemannOp_productMetric, riemannOp_line_eq_zero] at hr
  set R : E := (riemannOp (LeviCivita h) p.2) v.2 w.2 w.2 with hR
  have hr1 : ((riemannOp (LeviCivita G) p) v w w).1 =
      0 + (-Real.exp (-p.1) / 2 * v.1 * h.inner p.2 w.2 w.2 -
        -Real.exp (-p.1) / 2 * w.1 * h.inner p.2 v.2 w.2) +
      (Real.exp (-p.1) / 2 * h.inner p.2 v.2 (-(1 / 2 : ℝ) • (w.1 • w.2 + w.1 • w.2)) -
        Real.exp (-p.1) / 2 * h.inner p.2 w.2 (-(1 / 2 : ℝ) • (v.1 • w.2 + w.1 • v.2))) := by
    rw [hr]; rfl
  obtain ⟨S, hSdef⟩ : ∃ S : E, S = (-(1 / 2 : ℝ)) • (v.1 • (-(1 / 2 : ℝ)) • (w.1 • w.2 + w.1 • w.2) +
        (Real.exp (-p.1) / 2 * h.inner p.2 w.2 w.2) • v.2) -
        (-(1 / 2 : ℝ)) • (w.1 • (-(1 / 2 : ℝ)) • (v.1 • w.2 + w.1 • v.2) +
        (Real.exp (-p.1) / 2 * h.inner p.2 v.2 w.2) • w.2) := ⟨_, rfl⟩
  have hr2 : ((riemannOp (LeviCivita G) p) v w w).2 = R + S := by
    rw [hr, hSdef]
    change (R + ((0 : E) - 0)) + _ = _
    rw [sub_self, add_zero]
    rfl
  have hadd : ∀ u A B : E, h.inner p.2 u (A + B) = h.inner p.2 u A + h.inner p.2 u B := by
    intro u A B; simp only [map_add]
  have hsub : ∀ u A B : E, h.inner p.2 u (A - B) = h.inner p.2 u A - h.inner p.2 u B := by
    intro u A B; simp only [map_sub]
  have hsm : ∀ (u : E) (c : ℝ) (A : E), h.inner p.2 u (c • A) = c * h.inner p.2 u A := by
    intro u c A; simp only [map_smul, smul_eq_mul]
  have hS : h.inner p.2 v.2 S =
      -(1 / 2 : ℝ) * ((v.1 * (-(1 / 2 : ℝ)) * (w.1 * h.inner p.2 v.2 w.2 +
          w.1 * h.inner p.2 v.2 w.2)) +
        (Real.exp (-p.1) / 2 * h.inner p.2 w.2 w.2) * h.inner p.2 v.2 v.2) -
      (-(1 / 2 : ℝ)) * ((w.1 * (-(1 / 2 : ℝ)) * (v.1 * h.inner p.2 v.2 w.2 +
          w.1 * h.inner p.2 v.2 v.2)) +
        (Real.exp (-p.1) / 2 * h.inner p.2 v.2 w.2) * h.inner p.2 v.2 w.2) := by
    rw [hSdef]
    simp only [hadd, hsub, hsm]
    ring
  have hRS : h.inner p.2 v.2 (R + S) = h.inner p.2 v.2 R + h.inner p.2 v.2 S := hadd _ _ _
  rw [rm04_eq_inner_riem]
  erw [hG p v ((riemannOp (LeviCivita G) p) v w w), hr1, hr2]
  rw [rm04_eq_inner_riem]
  erw [hG, hG, hG]
  erw [hRS, hS]
  simp only [hadd, hsm]
  rw [h.symm p.2 w.2 v.2, ← hR]
  ring_nf
  rw [mul_right_comm (Real.exp (-p.1) ^ 2) (h.inner p.2 w.2 w.2) (h.inner p.2 v.2 v.2)]
  rfl

/-- The flat-fiber exponential metric has sectional curvature `-1/4`. -/
theorem metricRm04StandardAt_of_exponentialRealBase_inner_of_flat
    (hflat : ∀ (x : M) (u v : TangentSpace I x),
      metricRm04StandardAt h x u v v u = 0)
    (p : ℝ × M) (v w : TangentSpace (𝓘(ℝ, ℝ).prod I) p) :
    metricRm04StandardAt G p v w w v =
      -(1 / 4 : ℝ) * (G.inner p v v * G.inner p w w - G.inner p v w ^ 2) := by
  dsimp only [TangentSpace] at *
  rw [metricRm04StandardAt_of_exponentialRealBase_inner G h hG, hflat p.2 v.2 w.2]
  ring_nf
  rfl

end DifferentialGeometry.Geometry.Curvature
