import DifferentialGeometry.Geometry.Connection.TensorNabla.Iterated.FiniteJetCongruence
import DifferentialGeometry.Bundle.Section

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.RSTensor DifferentialGeometry.TensorLieDeriv Bundle
open scoped Manifold ContDiff Topology BigOperators

namespace DifferentialGeometry.Geometry.Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [FiniteDimensional ℝ E] in
private theorem mvfderiv_tangentConstInChart_eq_fderivWithin
    {f : M → ℝ} {x₀ p : M} (hp : p ∈ (chartAt H x₀).source)
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f p) (v : E) :
    mvfderiv (I := I) f p (tangentConstInChart (I := I) x₀ v p) =
      fderivWithin ℝ (f ∘ (extChartAt I x₀).symm)
        (Set.range I) (extChartAt I x₀ p) v := by
  let z := extChartAt I x₀ p
  have hsource : p ∈ (extChartAt I x₀).source := by
    simpa only [extChartAt_source] using hp
  have hz : z ∈ (extChartAt I x₀).target := (extChartAt I x₀).map_source hsource
  have hsymm : (extChartAt I x₀).symm z = p := (extChartAt I x₀).left_inv hsource
  have hf' : MDifferentiableWithinAt I 𝓘(ℝ, ℝ) f Set.univ
      ((extChartAt I x₀).symm z) := by
    rw [hsymm]
    exact hf.mdifferentiableWithinAt
  have huniq : UniqueMDiffWithinAt 𝓘(ℝ, E) (Set.range I) z :=
    (I.uniqueDiffOn z (extChartAt_target_subset_range x₀ hz)).uniqueMDiffWithinAt
  have hchain := mfderivWithin_comp
    (I := 𝓘(ℝ, E)) (I' := I) (I'' := 𝓘(ℝ, ℝ))
    (x := z) (g := f) (f := (extChartAt I x₀).symm)
    hf' (mdifferentiableWithinAt_extChartAt_symm (I := I) hz)
    (by intro y hy; exact Set.mem_univ _) huniq
  have hchain_apply :
      fderivWithin ℝ (f ∘ (extChartAt I x₀).symm) (Set.range I) z v =
        NormedSpace.fromTangentSpace (𝕜 := ℝ) (f p)
          (mfderiv I 𝓘(ℝ, ℝ) f p
            (mfderivWithin 𝓘(ℝ, E) I (extChartAt I x₀).symm (Set.range I) z v)) := by
    have happ := congrArg (fun L => L v) hchain
    rw [mfderivWithin_univ, hsymm] at happ
    have happ' := congrArg (NormedSpace.fromTangentSpace (𝕜 := ℝ) (f p)) happ
    calc
      fderivWithin ℝ (f ∘ (extChartAt I x₀).symm) (Set.range I) z v =
          NormedSpace.fromTangentSpace (𝕜 := ℝ) (f p)
            (mfderivWithin 𝓘(ℝ, E) 𝓘(ℝ, ℝ)
              (f ∘ (extChartAt I x₀).symm) (Set.range I) z v) := by
                rw [mfderivWithin_eq_fderivWithin]
                rfl
      _ = _ := happ'
  have hfield : tangentConstInChart (I := I) x₀ v p =
      mfderivWithin 𝓘(ℝ, E) I (extChartAt I x₀).symm (Set.range I) z v := by
    exact congrArg (fun L => L v)
      (TangentBundle.symmL_trivializationAt (𝕜 := ℝ) (I := I) (x₀ := x₀) (x := p) hp)
  rw [mvfderiv_real_eq_mfderiv, hfield]
  exact hchain_apply.symm

private theorem tensor0SModelInChart_contDiffWithinAt_of_contMDiffAt
    (n s : ℕ) (A : (p : M) → Tensor0SSpace s I p) (x₀ : M)
    {y : E} (hy : y ∈ (extChartAt I x₀).target)
    (hA : ContMDiffAt I (I.prod 𝓘(ℝ, Tensor0SModel s ℝ E)) n
      (fun p => (⟨p, A p⟩ : TotalSpace (Tensor0SModel s ℝ E)
        (fun q => Tensor0SSpace s I q))) ((extChartAt I x₀).symm y)) :
    ContDiffWithinAt ℝ n (tensor0SModelInChart s x₀ A) (Set.range I) y := by
  let := tensor0SBundleTopology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) s
  let e := trivializationAt (Tensor0SModel s ℝ E) (fun p => Tensor0SSpace s I p) x₀
  have hp : (extChartAt I x₀).symm y ∈ e.baseSet := by
    change (extChartAt I x₀).symm y ∈
      (trivializationAt E (TangentSpace I : M → Type _) x₀).baseSet
    simpa only [TangentBundle.trivializationAt_baseSet, extChartAt_source] using
      (extChartAt I x₀).map_target hy
  have hcoord : ContMDiffAt I 𝓘(ℝ, Tensor0SModel s ℝ E) n
      (fun p => (e ⟨p, A p⟩).2) ((extChartAt I x₀).symm y) :=
    (e.contMDiffAt_section_iff hp).mp hA
  have hcomp := hcoord.comp_contMDiffWithinAt (x := y)
    (contMDiffWithinAt_extChartAt_symm_range (I := I) (n := n) x₀ hy)
  change ContDiffWithinAt ℝ n
    ((fun p : M => (e ⟨p, A p⟩).2) ∘ (extChartAt I x₀).symm) (Set.range I) y
  exact hcomp.contDiffWithinAt

/-- In any fixed chart, the actual metric covariant derivative of a raw tensor
with `C¹` regularity at the evaluation point has the usual coordinate formula.
The within derivative preserves the model's boundary convention. -/
theorem tensor0SModelInChart_metricCovariantDerivative [T2Space M]
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (A : (p : M) → Tensor0SSpace s I p) (x₀ : M)
    {y : E} (hy : y ∈ (extChartAt I x₀).target)
    (hA : ContMDiffAt I (I.prod 𝓘(ℝ, Tensor0SModel s ℝ E)) 1
      (fun p => (⟨p, A p⟩ : TotalSpace (Tensor0SModel s ℝ E)
        (fun q => Tensor0SSpace s I q))) ((extChartAt I x₀).symm y)) :
    tensor0SModelInChart (s + 1) x₀ (metricCovariantDerivative g s A) y =
      totalCovDerivTensor0SModelAt s
        (fderivWithin ℝ (tensor0SModelInChart s x₀ A) (Set.range I) y)
        (connectionEndomorphismInChartL (leviCivitaConnectionOfMetric g) x₀ y)
        (tensor0SModelInChart s x₀ A y) := by
  classical
  let p := (extChartAt I x₀).symm y
  let e := trivializationAt E (TangentSpace I : M → Type _) x₀
  have hpsource : p ∈ (extChartAt I x₀).source := (extChartAt I x₀).map_target hy
  have hpchart : p ∈ (chartAt H x₀).source := by
    simpa only [extChartAt_source] using hpsource
  have hpbase : p ∈ e.baseSet := by
    simpa only [e, TangentBundle.trivializationAt_baseSet] using hpchart
  have hpy : extChartAt I x₀ p = y := (extChartAt I x₀).right_inv hy
  have hmodel : DifferentiableWithinAt ℝ (tensor0SModelInChart s x₀ A)
      (Set.range I) y :=
    (tensor0SModelInChart_contDiffWithinAt_of_contMDiffAt 1 s A x₀ hy hA).differentiableWithinAt
      (by norm_num)
  apply ContinuousMultilinearMap.ext
  intro slots
  let v := slots 0
  let w : Fin s → E := Fin.tail slots
  have hslots : slots = Fin.cons v w := (Fin.cons_self_tail slots).symm
  rw [hslots, totalCovDeriv_tensor0SModelAt_apply_cons,
    covariantDeriv_tensor0SModelAt_apply_slots]
  let V : Fin s → (q : M) → TangentSpace I q :=
    fun a => tangentConstInChart (I := I) x₀ (w a)
  have hV : ∀ a, ContMDiffAt I (I.prod 𝓘(ℝ, E)) 1
      (fun q => (⟨q, V a q⟩ : TotalSpace E (TangentSpace I : M → Type _))) p := by
    intro a
    let : IsManifold I ((1 : WithTop ℕ∞) + 1) M :=
      IsManifold.of_le (n := ∞) (by simp)
    have h := tangentConstInChart_contMDiffOn_baseSet
      (𝕜 := ℝ) (I := I) (n := (1 : WithTop ℕ∞)) x₀ (w a)
    exact (h p hpbase).contMDiffAt (e.open_baseSet.mem_nhds hpbase)
  obtain ⟨X, hX⟩ := ContMDiffSection.exists_eq_at
    (I := I) (F := E) (V := (TangentSpace I : M → Type _))
    (n := (⊤ : ℕ∞)) p (tangentConstInChart (I := I) x₀ v p)
  have hleibniz := metricCovariantDerivative_apply_of_contMDiffAt g s A X V p hA hV
  rw [hX] at hleibniz
  have hleft :
      tensor0SModelInChart (s + 1) x₀ (metricCovariantDerivative g s A) y
          (Fin.cons v w) =
        metricCovariantDerivative g s A p
          (Fin.cons (tangentConstInChart (I := I) x₀ v p) (fun a => V a p)) := by
    rw [tensor0SModelInChart_apply]
    congr 1
    funext a
    cases a using Fin.cases <;> rfl
  rw [hleft, hleibniz]
  have hpair : MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun q => A q (fun a => V a q)) p :=
    (TensorMultilinear.contMDiffAt_section_apply_one A hA V hV).mdifferentiableAt
      (by norm_num)
  have hprincipal :
      mvfderiv (I := I) (fun q => A q (fun a => V a q)) p
          (tangentConstInChart (I := I) x₀ v p) =
        fderivWithin ℝ (tensor0SModelInChart s x₀ A) (Set.range I) y v w := by
    rw [mvfderiv_tangentConstInChart_eq_fderivWithin hpchart hpair, hpy]
    have hfun : (fun q => A q (fun a => V a q)) ∘ (extChartAt I x₀).symm =
        fun z => tensor0SModelInChart s x₀ A z w := by
      funext z
      rw [tensor0SModelInChart_apply]
      rfl
    rw [hfun]
    let L := ContinuousMultilinearMap.apply ℝ (fun _ : Fin s => E) ℝ w
    have hchain := L.hasFDerivAt.comp_hasFDerivWithinAt y hmodel.hasFDerivWithinAt
    have hfd := hchain.fderivWithin
      (I.uniqueDiffOn y (extChartAt_target_subset_range x₀ hy))
    exact congrArg (fun D : E →L[ℝ] ℝ => D v) hfd
  rw [hprincipal]
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  rw [tensor0SModelInChart_apply]
  congr 1
  funext b
  by_cases hb : b = a
  · subst b
    simp only [Function.update_self]
    rw [connectionEndomorphismInChartL_apply_of_mem
      (leviCivitaConnectionOfMetric g) x₀ hy]
    exact (e.symmL_continuousLinearMapAt (R := ℝ) hpbase
      ((leviCivitaConnectionOfMetric g (V a) p)
        (tangentConstInChart (I := I) x₀ v p))).symm
  · simp only [Function.update_of_ne hb]
    rfl

end DifferentialGeometry.Geometry.Connection
