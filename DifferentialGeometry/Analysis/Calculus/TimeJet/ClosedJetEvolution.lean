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
      have h := spatial_iteratedFDeriv_contDiffOn (𝕜 := ℝ) (J := Icc a b)
        (G := fun (t : ℝ) (x : E) => (t, x))
        hV contDiffOn_id r
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
