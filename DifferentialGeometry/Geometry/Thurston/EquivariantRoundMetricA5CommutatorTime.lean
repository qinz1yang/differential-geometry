import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Algebra
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Connection.Intrinsic
import DifferentialGeometry.Bundle.PartialMfderiv.Interior

/-!
# The time commutator of the Levi-Civita derivative along a Ricci flow

Chapter 7, surface lemma U1, route (a), step a5.2 (iii), first commutator of the Bernstein
tower (lane U1C; design D18,
`docs/geometrization/handoffs/20261004-design-u1-a5-potential-gauge.md`, review 18 §2).

* `flow_covStep_hasDerivAt`: for a jointly smooth family `A(t)` of covariant `r`-tensor fields
  with slot-wise time derivative `Ȧ(t)` along a Ricci flow `g(t)`, the plain time derivative of
  `∇_{g(t)} A(t)` at fixed tangent vectors is `∇_{g(t)} Ȧ(t) - Σᵢ A(t)(…, Γ̇(vᵢ, w), …)`, where
  `Γ̇ = leviCivitaVariation` is the time derivative of the Levi-Civita connection
  (`leviCivita_hasDerivAt_of_solution`; it is linear in `∇Ric`). The proof evaluates `covStep` on
  smooth extensions of the slots (`covStep_eval_smooth_slots`), exchanges the time derivative with
  the spatial derivative (`hasDerivAt_mvfderiv_of_contMDiffAt`) and differentiates the slot
  `∇_w Vᵢ` through a basis expansion of the multilinear form.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.CheegerGromovCompactness
open Set
open scoped Manifold ContDiff

namespace GC.Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

omit [I.Boundaryless] [T2Space M] in
private theorem section_apply_contMDiff {r : ℕ}
    (A : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) r)
    (V : Fin r → ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _)) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun y => A y (fun i => V i y)) := fun y =>
  TensorMultilinear.contMDiffAt_section_apply (fun b => A b) (A.contMDiff y)
    (fun i b => V i b) (fun i => (V i).contMDiff y)

omit [I.Boundaryless] [T2Space M] in
private theorem hasDerivAt_apply_update {r : ℕ} {x : M}
    {B : ℝ → Tensor0SSpace (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) r x}
    {Bd : Tensor0SSpace (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) r x}
    {t : ℝ} (hB : ∀ u, HasDerivAt (fun s => B s u) (Bd u) t)
    (u : Fin r → TangentSpace I x) (q : Fin r) {Y : ℝ → TangentSpace I x}
    {Yd : TangentSpace I x} (hY : HasDerivAt Y Yd t) :
    HasDerivAt (fun s => B s (Function.update u q (Y s)))
      (Bd (Function.update u q (Y t)) + B t (Function.update u q Yd)) t := by
  classical
  let e := Module.finBasis ℝ (TangentSpace I x)
  have hexp : ∀ (L : Tensor0SSpace (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) r x)
      (y : TangentSpace I x), L (Function.update u q y) =
        ∑ k, e.repr y k * L (Function.update u q (e k)) := by
    intro L y
    have h := congrArg (L.toContinuousLinearMap u q) (e.sum_repr y).symm
    simp only [map_sum, map_smul, smul_eq_mul] at h
    exact h
  have hc : ∀ k, HasDerivAt (fun s => e.repr (Y s) k) (e.repr Yd k) t := fun k =>
    ((e.coord k).toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t hY)
  have hsum := HasDerivAt.sum (u := Finset.univ)
    (fun k _ => (hc k).mul (hB (Function.update u q (e k))))
  have hfun : (fun s => B s (Function.update u q (Y s))) =
      fun s => ∑ k ∈ Finset.univ, e.repr (Y s) k * B s (Function.update u q (e k)) :=
    funext fun s => hexp (B s) (Y s)
  rw [hfun]
  convert hsum using 1
  · funext s; simp
  · rw [hexp Bd, hexp (B t), ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring


theorem flow_covStep_hasDerivAt {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) {r : ℕ}
    (A Ad : ℝ → Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r)
    (hA : ∀ V : Fin r → ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ (fun p : ℝ × M => A p.1 p.2 (fun i => V i p.2))
        (D.regular ×ˢ univ))
    (hAd : ∀ t ∈ D.regular, ∀ x (v : Fin r → TangentSpace I x),
      HasDerivAt (fun s => A s x v) (Ad t x v) t)
    {t : ℝ} (ht : t ∈ D.regular) (x : M) (w : TangentSpace I x) (v : Fin r → TangentSpace I x) :
    HasDerivAt (fun s => covStep (S.family.metric s) r (A s) x (Fin.cons w v))
      (covStep (S.family.metric t) r (Ad t) x (Fin.cons w v) -
        ∑ i, A t x (Function.update v i (leviCivitaVariation S.family.metric t x (v i) w))) t := by
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨X, hX⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E) (V := TangentSpace I)
    (n := (⊤ : ℕ∞)) x w
  choose V hV using fun a : Fin r => ContMDiffSection.exists_eq_at (I := I) (F := E)
    (V := TangentSpace I) (n := (⊤ : ℕ∞)) x (v a)
  have hv : v = fun q => V q x := funext fun q => (hV q).symm
  subst hv hX
  have hfun : (fun s => covStep (S.family.metric s) r (A s) x (Fin.cons (X x) fun q => V q x)) =
      fun s => mvfderiv I (fun y => A s y (fun q => V q y)) x (X x) -
        ∑ q : Fin r, A s x (Function.update (fun b => V b x) q
          ((leviCivitaConnectionOfMetric (S.family.metric s)) (fun y => V q y) x (X x))) :=
    funext fun s => covStep_eval_smooth_slots _ r (A s) X V x
  rw [hfun, covStep_eval_smooth_slots _ r (Ad t) X V x]
  have hint : I.IsInteriorPoint x := BoundarylessManifold.isInteriorPoint
  have hF : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 2
      (fun p : ℝ × M => A p.1 p.2 (fun i => V i p.2)) (t, x) :=
    ((hA V).contMDiffAt ((D.regular_isOpen.prod isOpen_univ).mem_nhds ⟨ht, mem_univ x⟩)).of_le
      (by
        change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
        exact WithTop.coe_le_coe.mpr le_top)
  have h1 := hasDerivAt_mvfderiv_of_contMDiffAt (F := fun s y => A s y (fun q => V q y))
    (Ft := fun y => Ad t y (fun q => V q y)) hint hF
    (fun s => (section_apply_contMDiff (A s) V x).mdifferentiableAt (by simp))
    ((section_apply_contMDiff (Ad t) V x).mdifferentiableAt (by simp))
    (fun y => hAd t ht y _) (X x)
  have h2 : ∀ q ∈ (Finset.univ : Finset (Fin r)), HasDerivAt
      (fun s => A s x (Function.update (fun b => V b x) q
        ((leviCivitaConnectionOfMetric (S.family.metric s)) (fun y => V q y) x (X x))))
      (Ad t x (Function.update (fun b => V b x) q
          ((leviCivitaConnectionOfMetric (S.family.metric t)) (fun y => V q y) x (X x))) +
        A t x (Function.update (fun b => V b x) q
          (leviCivitaVariation S.family.metric t x (V q x) (X x)))) t := fun q _ =>
    hasDerivAt_apply_update (hAd t ht x) _ q
      (leviCivita_hasDerivAt_of_solution S hS ⟨t, ht⟩
        ((V q).contMDiff x |>.mdifferentiableAt (by simp)) (X x))
  have h3 := h1.sub (HasDerivAt.sum h2)
  convert h3 using 1
  · funext s; simp
  · rw [Finset.sum_add_distrib]
    ring

end GC.Geometry
