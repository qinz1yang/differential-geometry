import DifferentialGeometry.Analysis.Calculus.IteratedDerivative.Families
import DifferentialGeometry.Analysis.Calculus.TimeJet.MixedJets

noncomputable section

open Set
open scoped ContDiff Topology

namespace DifferentialGeometry.Analysis

private theorem continuousOn_iteratedFDerivWithin_timeShift
    {P : Type*} [TopologicalSpace P] {S : Set P} {J : Set ℝ}
    {σ : P → ℝ} (hσ : ContinuousOn σ S) (hJ : UniqueDiffOn ℝ J) (n : ℕ) :
    ContinuousOn
      (fun q : P × ℝ × ℝ => iteratedFDerivWithin ℝ n
        (fun z : ℝ × ℝ => σ q.1 + z.1) (J ×ˢ univ) q.2)
      (S ×ˢ J ×ˢ univ) := by
  have hK := hJ.prod (uniqueDiffOn_univ : UniqueDiffOn ℝ (univ : Set ℝ))
  have hconst : ContinuousOn
      (fun q : P × ℝ × ℝ => iteratedFDerivWithin ℝ n
        (fun _ : ℝ × ℝ => σ q.1) (J ×ˢ univ) q.2) (S ×ˢ J ×ˢ univ) := by
    cases n with
    | zero =>
      exact (continuousMultilinearCurryFin0 ℝ (ℝ × ℝ) ℝ).symm.continuous.comp_continuousOn
        (hσ.comp continuousOn_fst (fun _ hq => hq.1))
    | succ n =>
      simpa only [iteratedFDerivWithin_succ_const, Pi.zero_apply] using
        (continuousOn_const : ContinuousOn
          (fun _ : P × ℝ × ℝ =>
            (0 : ContinuousMultilinearMap ℝ (fun _ : Fin (n + 1) => ℝ × ℝ) ℝ))
          (S ×ˢ J ×ˢ univ))
  have hfs : ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => z.1) (J ×ˢ univ) := contDiff_fst.contDiffOn
  have hfst : ContinuousOn
      (fun q : P × ℝ × ℝ => iteratedFDerivWithin ℝ n
        (fun z : ℝ × ℝ => z.1) (J ×ˢ univ) q.2) (S ×ˢ J ×ˢ univ) :=
    (hfs.continuousOn_iteratedFDerivWithin (WithTop.coe_le_coe.mpr le_top) hK).comp
      continuousOn_snd (fun _ hq => hq.2)
  apply (hconst.add hfst).congr
  intro q hq
  exact (fun_iteratedFDerivWithin_add_apply contDiffWithinAt_const
    contDiffWithinAt_fst hK hq.2)

theorem contDiffOn_shifted_firstJet_comp
    {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {J : Set ℝ} (hJ : UniqueDiffOn ℝ J) (σ : ℝ) {d : ℝ → ℝ → F}
    (hd : ContDiffOn ℝ ∞ (Function.uncurry d) (J ×ˢ univ))
    {Ω : Set (ℝ × F × F)} (Φ : ℝ × F × F → G) (hΦ : ContDiffOn ℝ ∞ Φ Ω)
    (hmap : ∀ t ∈ J, ∀ x, (σ + t, d t x, deriv (d t) x) ∈ Ω) :
    ContDiffOn ℝ ∞
      (fun z : ℝ × ℝ => Φ (σ + z.1, d z.1 z.2, deriv (d z.1) z.2))
      (J ×ˢ univ) := by
  have hd₁ : ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => deriv (d z.1) z.2) (J ×ˢ univ) := by
    have h := (ContinuousLinearMap.apply ℝ F (1 : ℝ)).contDiff.comp_contDiffOn
      (spatialFDeriv_contDiffOn hJ isOpen_univ hd)
    change ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => fderiv ℝ (d q.1) q.2 1)
      (J ×ˢ univ) at h
    simpa only [fderiv_apply_one_eq_deriv] using h
  exact hΦ.comp ((contDiffOn_const.add contDiffOn_fst).prodMk (hd.prodMk hd₁))
    (fun z hz => hmap z.1 hz.1 z.2)

theorem continuousOn_iteratedFDerivWithin_shifted_firstJet_comp
    {P F G : Type*} [TopologicalSpace P]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {S : Set P} {J : Set ℝ} {σ : P → ℝ} {d : P → ℝ → ℝ → F}
    (hJ : UniqueDiffOn ℝ J) (hacc : J ⊆ closure (interior J))
    (hσ : ContinuousOn σ S)
    (hd : ∀ p ∈ S, ContDiffOn ℝ ∞ (Function.uncurry (d p)) (J ×ˢ univ))
    (hmixed : ∀ k j : ℕ, ContinuousOn
      (fun q : P × ℝ × ℝ => iteratedDerivWithin k
        (fun t => iteratedDeriv j (d q.1 t) q.2.2) J q.2.1)
      (S ×ˢ J ×ˢ univ))
    {Ω : Set (ℝ × F × F)} (hΩ : IsOpen Ω)
    (Φ : ℝ × F × F → G) (hΦ : ContDiffOn ℝ ∞ Φ Ω)
    (hmap : ∀ p ∈ S, ∀ t ∈ J, ∀ x,
      (σ p + t, d p t x, deriv (d p t) x) ∈ Ω) (n : ℕ) :
    ContinuousOn
      (fun q : P × ℝ × ℝ => iteratedFDerivWithin ℝ n
        (fun z : ℝ × ℝ => Φ (σ q.1 + z.1, d q.1 z.1 z.2,
          deriv (d q.1 z.1) z.2)) (J ×ˢ univ) q.2)
      (S ×ˢ J ×ˢ univ) := by
  let d₁ := fun p t x => deriv (d p t) x
  have hd₁ (p : P) (hp : p ∈ S) :
      ContDiffOn ℝ ∞ (Function.uncurry (d₁ p)) (J ×ˢ univ) := by
    have h := (ContinuousLinearMap.apply ℝ F (1 : ℝ)).contDiff.comp_contDiffOn
      (spatialFDeriv_contDiffOn hJ isOpen_univ (hd p hp))
    change ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => fderiv ℝ (d p q.1) q.2 1)
      (J ×ˢ univ) at h
    simpa only [fderiv_apply_one_eq_deriv, d₁, Function.uncurry_def] using h
  have hfull (n : ℕ) := continuousOn_iteratedFDerivWithin_of_mixed_derivatives
    hJ hacc isOpen_univ hd hmixed n
  have hfull₁ (n : ℕ) : ContinuousOn
      (fun q : P × ℝ × ℝ => iteratedFDerivWithin ℝ n
        (Function.uncurry (d₁ q.1)) (J ×ˢ univ) q.2) (S ×ˢ J ×ˢ univ) := by
    apply continuousOn_iteratedFDerivWithin_of_mixed_derivatives hJ hacc isOpen_univ hd₁
    intro k j
    simpa only [d₁, ← iteratedDeriv_succ'] using hmixed k (j + 1)
  let Q := fun p (z : ℝ × ℝ) => (σ p + z.1, d p z.1 z.2, d₁ p z.1 z.2)
  have hQ (p : P) (hp : p ∈ S) : ContDiffOn ℝ ∞ (Q p) (J ×ˢ univ) :=
    (contDiffOn_const.add contDiffOn_fst).prodMk ((hd p hp).prodMk (hd₁ p hp))
  have hQjet (m : ℕ) : ContinuousOn
      (fun q : P × ℝ × ℝ => iteratedFDerivWithin ℝ m (Q q.1) (J ×ˢ univ) q.2)
      (S ×ˢ J ×ˢ univ) := by
    apply continuousOn_iteratedFDerivWithin_prod
      (hJ.prod uniqueDiffOn_univ) m
      (fun _ _ => contDiffOn_const.add contDiffOn_fst)
      (fun p hp => ((hd p hp).prodMk (hd₁ p hp)).of_le (WithTop.coe_le_coe.mpr le_top))
      (continuousOn_iteratedFDerivWithin_timeShift hσ hJ m)
    exact continuousOn_iteratedFDerivWithin_prod (hJ.prod uniqueDiffOn_univ) m
      (fun p hp => (hd p hp).of_le (WithTop.coe_le_coe.mpr le_top))
      (fun p hp => (hd₁ p hp).of_le (WithTop.coe_le_coe.mpr le_top)) (hfull m) (hfull₁ m)
  exact continuousOn_iteratedFDerivWithin_family_comp (hJ.prod uniqueDiffOn_univ)
    hΩ.uniqueDiffOn (fun p hp => (hQ p hp).of_le (WithTop.coe_le_coe.mpr le_top))
    (hΦ.of_le (WithTop.coe_le_coe.mpr le_top))
    (fun m _ => hQjet m) (fun q hq => hmap q.1 hq.1 q.2.1 hq.2.1 q.2.2)

end DifferentialGeometry.Analysis

end
