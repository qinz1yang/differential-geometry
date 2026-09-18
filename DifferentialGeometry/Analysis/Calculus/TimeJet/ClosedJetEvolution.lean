import DifferentialGeometry.Analysis.Calculus.IteratedDerivative.SpaceJets
import DifferentialGeometry.Analysis.Calculus.TimeJet.SliceSwap
import DifferentialGeometry.Analysis.Calculus.TimeJet.SliceBootstrap
import DifferentialGeometry.Analysis.Calculus.TimeJet.EndpointJets

set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff
namespace DifferentialGeometry.Analysis
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace F] in
private theorem continuousOn_of_zero_jet {G : ℝ → E → F} {J : Set ℝ} {V : Set E}
    (h : SpaceJetDiff 0 G J V) : ContinuousOn (Function.uncurry G) (J ×ˢ V) := by
  have hh := (continuousMultilinearCurryFin0 ℝ E F).continuous.comp_continuousOn
    (h 0).continuousOn
  exact hh.congr (fun p _ => by rcases p with ⟨t, x⟩; rfl)

theorem contDiffOn_and_equation_Icc_of_time_dependent_spatial_jets
    (G : ℝ → E → F) (a b : ℝ) (hab : a < b) (V : Set E) (hV : IsOpen V)
    (Φ : (ℝ × E) × F × (E →L[ℝ] F) × (E →L[ℝ] (E →L[ℝ] F)) → F)
    (Ω : Set ((ℝ × E) × F × (E →L[ℝ] F) × (E →L[ℝ] (E →L[ℝ] F)))) (hΩ : IsOpen Ω)
    (hΦ : ContDiffOn ℝ ∞ Φ Ω)
    (hmap : MapsTo (fun p : ℝ × E => (p, jet2 (G p.1) p.2)) (Icc a b ×ˢ V) Ω)
    (hGs : ∀ t ∈ Icc a b, ContDiffOn ℝ ∞ (G t) V)
    (hjets : ∀ r : ℕ, ContinuousOn
      (fun p : ℝ × E => iteratedFDeriv ℝ r (G p.1) p.2) (Icc a b ×ˢ V))
    (hpde : ∀ t ∈ Ioo a b, ∀ x ∈ V,
      HasDerivAt (fun s => G s x) (Φ ((t, x), jet2 (G t) x)) t) :
    ContDiffOn ℝ ∞ (Function.uncurry G) (Icc a b ×ˢ V) ∧
      ∀ t ∈ Icc a b, ∀ x ∈ V,
        HasDerivWithinAt (fun s => G s x) (Φ ((t, x), jet2 (G t) x)) (Icc a b) t := by
  let R := fun t x => Φ ((t, x), jet2 (G t) x)
  have hJetSlices (t : ℝ) (ht : t ∈ Icc a b) :
      ContDiffOn ℝ ∞ (fun x => jet2 (G t) x) V := by
    have h1 := (hGs t ht).fderiv_of_isOpen hV (m := ∞) (by simp)
    have h2 := h1.fderiv_of_isOpen hV (m := ∞) (by simp)
    exact (hGs t ht).prodMk (h1.prodMk h2)
  have hRs (t : ℝ) (ht : t ∈ Icc a b) : ContDiffOn ℝ ∞ (R t) V :=
    hΦ.comp ((contDiffOn_const.prodMk contDiffOn_id).prodMk (hJetSlices t ht))
      (fun x hx => hmap (x := (t, x)) ⟨ht, hx⟩)
  have hRjets (q : ℕ) (hG : SpaceJetDiff q G (Icc a b) V) :
      SpaceJetDiff q R (Icc a b) V := by
    have hcoord : SpaceJetDiff q (fun t (x : E) => (t, x)) (Icc a b) V := by
      intro r
      have h := spatial_iteratedFDeriv_contDiffOn (G := fun t (x : E) => (t, x))
        (uniqueDiffOn_Icc hab) hV contDiffOn_id r
      exact h.of_le (by exact_mod_cast le_top)
    exact spaceJet_comp_Icc hV hΩ hmap hΦ
      (fun t ht => (contDiffOn_const.prodMk contDiffOn_id).prodMk (hJetSlices t ht))
      (hcoord.prodMk hV (fun t _ => contDiffOn_const.prodMk contDiffOn_id)
        hJetSlices (hG.jet2 hV hGs))
  have hbase : SpaceJetDiff 0 G (Icc a b) V := fun r => contDiffOn_zero.mpr (hjets r)
  have hGcont := continuousOn_of_zero_jet hbase
  have hRcont := continuousOn_of_zero_jet (hRjets 0 hbase)
  have hclosed : ∀ t ∈ Icc a b, ∀ x ∈ V,
      HasDerivWithinAt (fun s => G s x) (R t x) (Icc a b) t := by
    intro t ht x hx
    exact hasDerivIcc_of_int hab
      (hGcont.comp (continuousOn_id.prodMk continuousOn_const) (fun s hs => ⟨hs, hx⟩))
      (hRcont.comp (continuousOn_id.prodMk continuousOn_const) (fun s hs => ⟨hs, hx⟩))
      (fun s hs => hpde s hs x hx) ht
  have hAll : ∀ q : ℕ, SpaceJetDiff q G (Icc a b) V := by
    intro q
    induction q with
    | zero => exact hbase
    | succ q ih =>
      have hR := hRjets q ih
      intro r
      have htime : ∀ p ∈ Icc a b ×ˢ V,
          HasDerivWithinAt (fun s => iteratedFDeriv ℝ r (G s) p.2)
            (iteratedFDeriv ℝ r (R p.1) p.2) (Icc a b) p.1 :=
        fun p hp => hasDerivWithin_iterF hV r hGs hRs hclosed
          (fun m _ => (hR m).continuousOn) hp.1 hp.2
      have hspace : ∀ p ∈ Icc a b ×ˢ V,
          HasFDerivAt (iteratedFDeriv ℝ r (G p.1))
            (fderiv ℝ (iteratedFDeriv ℝ r (G p.1)) p.2) p.2 := by
        intro p hp
        have hAt := (hGs p.1 hp.1 p.2 hp.2).contDiffAt (hV.mem_nhds hp.2)
        exact ((hAt.iteratedFDeriv_right (m := 1) (i := r) (by exact_mod_cast le_top)).differentiableAt
          (by norm_num)).hasFDerivAt
      simpa only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one] using
        contDiffIcc_succ (q := q) hab hV htime hspace (hR r) (ih.jet_fderiv r)
  refine ⟨?_, hclosed⟩
  rw [contDiffOn_infty]
  intro q
  have hh := (continuousMultilinearCurryFin0 ℝ E F).contDiff.comp_contDiffOn (hAll q 0)
  exact hh.congr (fun p _ => by rcases p with ⟨t, x⟩; rfl)

theorem contDiffOn_and_equation_Icc_of_spatial_jets
    (G : ℝ → E → F) (a b : ℝ) (hab : a < b) (V : Set E) (hV : IsOpen V)
    (Φ : F × (E →L[ℝ] F) × (E →L[ℝ] (E →L[ℝ] F)) → F)
    (Ω : Set (F × (E →L[ℝ] F) × (E →L[ℝ] (E →L[ℝ] F)))) (hΩ : IsOpen Ω)
    (hΦ : ContDiffOn ℝ ∞ Φ Ω)
    (hmap : MapsTo (Function.uncurry (fun t x => jet2 (G t) x)) (Icc a b ×ˢ V) Ω)
    (hGs : ∀ t ∈ Icc a b, ContDiffOn ℝ ∞ (G t) V)
    (hjets : ∀ r : ℕ, ContinuousOn
      (fun p : ℝ × E => iteratedFDeriv ℝ r (G p.1) p.2) (Icc a b ×ˢ V))
    (hpde : ∀ t ∈ Ioo a b, ∀ x ∈ V,
      HasDerivAt (fun s => G s x) (Φ (jet2 (G t) x)) t) :
    ContDiffOn ℝ ∞ (Function.uncurry G) (Icc a b ×ˢ V) ∧
      ∀ t ∈ Icc a b, ∀ x ∈ V,
        HasDerivWithinAt (fun s => G s x) (Φ (jet2 (G t) x)) (Icc a b) t := by
  exact contDiffOn_and_equation_Icc_of_time_dependent_spatial_jets G a b hab V hV
    (fun p => Φ p.2) (Prod.snd ⁻¹' Ω) (hΩ.preimage continuous_snd)
    (hΦ.comp contDiffOn_snd (fun _ hp => hp)) hmap hGs hjets hpde

end DifferentialGeometry.Analysis

namespace DifferentialGeometry.Analysis

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem contDiffOn_of_scalar_jet_equation
    {G : ℝ → ℝ → F} {a b σ : ℝ} {V : Set ℝ}
    {Φ : (ℝ × ℝ × (Fin 3 → F)) → F} {Ω : Set (ℝ × ℝ × (Fin 3 → F))}
    (hab : a < b) (hV : IsOpen V) (hΩ : IsOpen Ω)
    (hΦ : ContDiffOn ℝ ∞ Φ Ω)
    (hGs : ∀ t ∈ Icc a b, ContDiffOn ℝ ∞ (G t) V)
    (hjets : ∀ r : ℕ, ContinuousOn
      (fun p : ℝ × ℝ => iteratedDeriv r (G p.1) p.2) (Icc a b ×ˢ V))
    (hmap : ∀ t ∈ Icc a b, ∀ x ∈ V,
      (σ + t, x, fun i : Fin 3 => iteratedDeriv i.val (G t) x) ∈ Ω)
    (hpde : ∀ t ∈ Ioo a b, ∀ x ∈ V,
      HasDerivAt (fun s => G s x)
        (Φ (σ + t, x, fun i : Fin 3 => iteratedDeriv i.val (G t) x)) t) :
    ContDiffOn ℝ ∞ (Function.uncurry G) (Icc a b ×ˢ V) := by
  let Q := (ℝ × ℝ) × F × (ℝ →L[ℝ] F) × (ℝ →L[ℝ] (ℝ →L[ℝ] F))
  let A : Q → ℝ × ℝ × (Fin 3 → F) := fun q =>
    (σ + q.1.1, q.1.2, ![q.2.1, q.2.2.1 1, q.2.2.2 1 1])
  have hA : ContDiff ℝ ∞ A := by
    apply ContDiff.prodMk
    · fun_prop
    apply ContDiff.prodMk
    · fun_prop
    apply contDiff_pi.mpr
    intro i
    fin_cases i
    · change ContDiff ℝ ∞ (fun q : Q => q.2.1)
      fun_prop
    · change ContDiff ℝ ∞ (fun q : Q => q.2.2.1 1)
      fun_prop
    · change ContDiff ℝ ∞ (fun q : Q => q.2.2.2 1 1)
      fun_prop
  have hactual (t x : ℝ) :
      A ((t, x), jet2 (G t) x) =
        (σ + t, x, fun i : Fin 3 => iteratedDeriv i.val (G t) x) := by
    dsimp only [A]
    congr 2
    funext i
    fin_cases i
    · rfl
    · change fderiv ℝ (G t) x 1 = iteratedDeriv 1 (G t) x
      simp only [iteratedDeriv_one, fderiv_apply_one_eq_deriv]
    · change fderiv ℝ (fderiv ℝ (G t)) x 1 1 = iteratedDeriv 2 (G t) x
      simp only [iteratedDeriv_eq_iteratedFDeriv, iteratedFDeriv_two_apply]
  have hjetsF (r : ℕ) : ContinuousOn
      (fun p : ℝ × ℝ => iteratedFDeriv ℝ r (G p.1) p.2) (Icc a b ×ˢ V) := by
    simp_rw [iteratedFDeriv_eq_equiv_comp, Function.comp_apply]
    exact (ContinuousMultilinearMap.piFieldEquiv ℝ (Fin r) F).continuous.comp_continuousOn
      (hjets r)
  have hmapA : MapsTo (fun p : ℝ × ℝ => (p, jet2 (G p.1) p.2))
      (Icc a b ×ˢ V) (A ⁻¹' Ω) := by
    intro p hp
    change A ((p.1, p.2), jet2 (G p.1) p.2) ∈ Ω
    rw [hactual]
    exact hmap p.1 hp.1 p.2 hp.2
  have hpdeA : ∀ t ∈ Ioo a b, ∀ x ∈ V,
      HasDerivAt (fun s => G s x) ((Φ ∘ A) ((t, x), jet2 (G t) x)) t := by
    intro t ht x hx
    simpa only [Function.comp_apply, hactual] using hpde t ht x hx
  exact (contDiffOn_and_equation_Icc_of_time_dependent_spatial_jets G a b hab V hV
    (Φ ∘ A) (A ⁻¹' Ω) (hΩ.preimage hA.continuous)
    (hΦ.comp hA.contDiffOn (fun _ h => h)) hmapA hGs hjetsF hpdeA).1

end DifferentialGeometry.Analysis
