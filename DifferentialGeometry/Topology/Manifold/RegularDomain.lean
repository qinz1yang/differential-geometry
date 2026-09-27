import DifferentialGeometry.Topology.Morse.SublevelEuclidean
import DifferentialGeometry.Topology.Morse.RegularSublevelBoundary

set_option autoImplicit false

open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.Morse

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem interior_sublevel_eq_lt_sublevel
    (f : M → ℝ) (a : ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x : M, f x = a → ¬ IsCriticalPointAt I f x) :
    interior {x | f x ≤ a} = {x | f x < a} := by
  have hneg : ∀ x : M, (-f) x = -a → ¬ IsCriticalPointAt I (-f) x := by
    intro x hx hc
    apply hreg x (neg_inj.mp hx)
    change mfderiv I 𝓘(ℝ, ℝ) (-f) x = 0 at hc
    rw [mfderiv_neg] at hc
    change -(mfderiv I 𝓘(ℝ, ℝ) f x : TangentSpace I x →L[ℝ] ℝ) = 0 at hc
    exact neg_eq_zero.mp hc
  have hcl := closure_lt_sublevel_eq_sublevel (-f) (-a) hf.neg hneg
  have hlt : {x | (-f) x < -a} = {x | f x ≤ a}ᶜ := by
    ext x
    simp only [Pi.neg_apply, neg_lt_neg_iff, Set.mem_ofPred_eq,
      Set.mem_compl_iff, not_le]
  rw [hlt, closure_compl] at hcl
  have h := congrArg (fun s : Set M => sᶜ) hcl
  simpa only [compl_compl, Set.compl_ofPred, Pi.neg_apply,
    neg_le_neg_iff, not_le] using h

private theorem exists_isManifold_sublevel_of_finrank_eq
    {m : ℕ} (hdim : Module.finrank ℝ E = m + 1)
    (f : M → ℝ) (a : ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x : M, f x = a → ¬ IsCriticalPointAt I f x) :
    ∃ cs : ChartedSpace (EuclideanHalfSpace (m + 1)) (SublevelSpace f a),
      let := cs
      IsManifold (modelWithCornersEuclideanHalfSpace (m + 1)) ∞ (SublevelSpace f a) ∧
      ContMDiff (modelWithCornersEuclideanHalfSpace (m + 1)) I ∞
        (fun x : SublevelSpace f a => x.1) ∧
      (∀ x : SublevelSpace f a, Function.Bijective
        (mfderiv (modelWithCornersEuclideanHalfSpace (m + 1)) I
          (fun y : SublevelSpace f a => y.1) x)) ∧
      (∀ x : SublevelSpace f a,
        (modelWithCornersEuclideanHalfSpace (m + 1)).IsBoundaryPoint x ↔ f x.1 = a) := by
  let e : E ≃L[ℝ] MorseModel (m + 1) :=
    ContinuousLinearEquiv.ofFinrankEq (hdim.trans (Module.finrank_fin_fun ℝ).symm)
  let J := I.transContinuousLinearEquiv e
  let hfJ : ContMDiff J 𝓘(ℝ, ℝ) ∞ f :=
    (e.contMDiff_transContinuousLinearEquiv_left).mpr hf
  have hregJ : ∀ x : M, f x = a → ¬ IsCriticalPointAt J f x := fun x hx hc =>
    hreg x hx ((isCriticalPointAt_transContinuousLinearEquiv_iff I e f x).mp hc)
  let cs := manifoldSublevelEuclideanChartedSpace J f a hfJ hregJ
  let := cs
  let := manifoldSublevelEuclidean_isManifold J f a hfJ hregJ
  refine ⟨cs, inferInstance, ?_, ?_, ?_⟩
  · exact e.contMDiff_transContinuousLinearEquiv_right.mp
      (contMDiff_manifoldSublevelEuclideanInclusion J f a hfJ hregJ)
  · intro x
    let Φ := (ContinuousLinearEquiv.toTransContinuousLinearEquiv (n := ∞) I M e).symm
    have hΦ := (Φ.contMDiff x.1).mdifferentiableAt (by simp)
    have hi := (contMDiff_manifoldSublevelEuclideanInclusion J f a hfJ hregJ x)
      |>.mdifferentiableAt (by simp)
    have hb := ((Φ.mfderivToContinuousLinearEquiv (by simp) x.1).bijective).comp
      (mfderiv_manifoldSublevelEuclideanInclusion_bijective J f a hfJ hregJ x)
    change Function.Bijective
      (⇑(mfderiv J I Φ x.1) ∘ ⇑(mfderiv (modelWithCornersEuclideanHalfSpace (m + 1)) J
        (fun y : SublevelSpace f a => y.1) x)) at hb
    rw [← ContinuousLinearMap.coe_comp, ← mfderiv_comp x hΦ hi] at hb
    exact hb
  · exact manifoldSublevelEuclidean_isBoundaryPoint_iff J f a hfJ hregJ

theorem exists_isManifold_sublevel [Nontrivial E]
    (f : M → ℝ) (a : ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x : M, f x = a → ¬ IsCriticalPointAt I f x) :
    ∃ m : ℕ, Module.finrank ℝ E = m + 1 ∧
      ∃ cs : ChartedSpace (EuclideanHalfSpace (m + 1)) (SublevelSpace f a),
        letI := cs
        IsManifold (modelWithCornersEuclideanHalfSpace (m + 1)) ∞
          (SublevelSpace f a) ∧
        ContMDiff (modelWithCornersEuclideanHalfSpace (m + 1)) I ∞
          (fun x : SublevelSpace f a => x.1) ∧
        (∀ x : SublevelSpace f a, Function.Bijective
          (mfderiv (modelWithCornersEuclideanHalfSpace (m + 1)) I
            (fun y : SublevelSpace f a => y.1) x)) ∧
        (∀ x : SublevelSpace f a,
          (modelWithCornersEuclideanHalfSpace (m + 1)).IsBoundaryPoint x ↔ f x.1 = a) := by
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero
    (Module.finrank_pos (R := ℝ) (M := E)).ne'
  exact ⟨m, hm, exists_isManifold_sublevel_of_finrank_eq hm f a hf hreg⟩

end DifferentialGeometry.Topology.Morse
