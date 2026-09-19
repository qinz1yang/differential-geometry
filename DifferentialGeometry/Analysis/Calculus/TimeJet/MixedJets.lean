import DifferentialGeometry.Analysis.Calculus.TimeJet.EndpointJets
import DifferentialGeometry.Analysis.Calculus.TimeJet.Matching

noncomputable section
open Set
open scoped ContDiff

namespace DifferentialGeometry.Analysis

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem scalar_spatial_jets_contDiffOn
    {G : ℝ → ℝ → F} {J V : Set ℝ}
    (hV : IsOpen V)
    (hG : ContDiffOn ℝ ∞ (Function.uncurry G) (J ×ˢ V)) (j : ℕ) :
    ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => iteratedDeriv j (G q.1) q.2) (J ×ˢ V) := by
  simpa only [iteratedDeriv_eq_equiv_comp, Function.comp_def] using
    (ContinuousMultilinearMap.piFieldEquiv ℝ (Fin j) F).symm.contDiff.comp_contDiffOn
      (spatial_iteratedFDeriv_contDiffOn hV hG j)

private theorem scalar_mixed_jets_contDiffOn
    {G : ℝ → ℝ → F} {J V : Set ℝ}
    (hJ : UniqueDiffOn ℝ J) (hV : IsOpen V)
    (hG : ContDiffOn ℝ ∞ (Function.uncurry G) (J ×ˢ V)) (k j : ℕ) :
    ContDiffOn ℝ ∞
      (fun q : ℝ × ℝ => iteratedDerivWithin k
        (fun t => iteratedDeriv j (G t) q.2) J q.1) (J ×ˢ V) :=
  time_iteratedDerivWithin_contDiffOn (G := fun t x => iteratedDeriv j (G t) x) hJ hV
    (scalar_spatial_jets_contDiffOn hV hG j) k

private theorem fderivWithin_prod_eq_partials
    {H : ℝ × ℝ → F} {J V : Set ℝ}
    (hJ : UniqueDiffOn ℝ J) (hV : IsOpen V)
    (hH : DifferentiableOn ℝ H (J ×ˢ V)) {q : ℝ × ℝ} (hq : q ∈ J ×ˢ V) :
    fderivWithin ℝ H (J ×ˢ V) q =
      (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight
        (derivWithin (fun t => H (t, q.2)) J q.1) +
      (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight
        (deriv (fun x => H (q.1, x)) q.2) := by
  have ht : derivWithin (fun t => H (t, q.2)) J q.1 =
      fderivWithin ℝ H (J ×ˢ V) q (1, 0) := by
    have hh : HasDerivWithinAt (fun t : ℝ => (t, q.2)) ((1, 0) : ℝ × ℝ) J q.1 :=
      (hasDerivWithinAt_id q.1 J).prodMk (hasDerivWithinAt_const q.1 J q.2)
    have hm : MapsTo (fun t : ℝ => (t, q.2)) J (J ×ˢ V) := fun t ht => ⟨ht, hq.2⟩
    exact ((hH q hq).hasFDerivWithinAt.comp_hasDerivWithinAt q.1 hh hm).derivWithin
      (hJ q.1 hq.1)
  have hx : deriv (fun x => H (q.1, x)) q.2 =
      fderivWithin ℝ H (J ×ˢ V) q (0, 1) := by
    have hh : HasDerivWithinAt (fun x : ℝ => (q.1, x)) ((0, 1) : ℝ × ℝ) V q.2 :=
      (hasDerivWithinAt_const q.2 V q.1).prodMk (hasDerivWithinAt_id q.2 V)
    have hm : MapsTo (fun x : ℝ => (q.1, x)) V (J ×ˢ V) := fun x hx => ⟨hq.1, hx⟩
    exact (((hH q hq).hasFDerivWithinAt.comp_hasDerivWithinAt q.2 hh hm).hasDerivAt
      (hV.mem_nhds hq.2)).deriv
  apply ContinuousLinearMap.ext
  intro z
  have hz : z = z.1 • ((1, 0) : ℝ × ℝ) + z.2 • ((0, 1) : ℝ × ℝ) := by
    ext <;> simp
  calc
    fderivWithin ℝ H (J ×ˢ V) q z =
        z.1 • fderivWithin ℝ H (J ×ˢ V) q (1, 0) +
          z.2 • fderivWithin ℝ H (J ×ˢ V) q (0, 1) := by
      conv_lhs => rw [hz]
      simp only [map_add, map_smul]
    _ = _ := by rw [← ht, ← hx]; rfl

private theorem deriv_scalar_mixed_jets
    {G : ℝ → ℝ → F} {J V : Set ℝ}
    (hJ : UniqueDiffOn ℝ J) (hacc : J ⊆ closure (interior J)) (hV : IsOpen V)
    (hG : ContDiffOn ℝ ∞ (Function.uncurry G) (J ×ˢ V))
    (k j : ℕ) {t x : ℝ} (ht : t ∈ J) (hx : x ∈ V) :
    deriv (fun y => iteratedDerivWithin k
      (fun s => iteratedDeriv j (G s) y) J t) x =
      iteratedDerivWithin k (fun s => iteratedDeriv (j + 1) (G s) x) J t := by
  have hs := scalar_spatial_jets_contDiffOn hV hG j
  have hcomm := fderiv_iteratedDerivWithin_time_comm
    (G := fun s y => iteratedDeriv j (G s) y) hJ hacc hV k ht hx hs
  have hc : ContDiffOn ℝ ∞
      (fun s => fderiv ℝ (fun y => iteratedDeriv j (G s) y) x) J :=
    (spatialFDeriv_contDiffOn (G := fun s y => iteratedDeriv j (G s) y) hJ hV hs).comp
      (contDiff_id.prodMk contDiff_const).contDiffOn (fun s hs => ⟨hs, hx⟩)
  have hev := iteratedDerivWithin_clm_comp (n := k) (ContinuousLinearMap.apply ℝ F (1 : ℝ))
    ((hc t ht).of_le (WithTop.coe_le_coe.mpr le_top : (k : ℕ∞ω) ≤ ∞)) hJ ht
  calc
    deriv (fun y => iteratedDerivWithin k
        (fun s => iteratedDeriv j (G s) y) J t) x =
        (iteratedDerivWithin k
          (fun s => fderiv ℝ (fun y => iteratedDeriv j (G s) y) x) J t) 1 :=
      congrArg (fun L : ℝ →L[ℝ] F => L 1) hcomm
    _ = iteratedDerivWithin k
        (fun s => deriv (fun y => iteratedDeriv j (G s) y) x) J t := hev.symm
    _ = _ := by simp only [iteratedDeriv_succ]

private theorem fderivWithin_scalar_mixed_jets
    {G : ℝ → ℝ → F} {J V : Set ℝ}
    (hJ : UniqueDiffOn ℝ J) (hacc : J ⊆ closure (interior J)) (hV : IsOpen V)
    (hG : ContDiffOn ℝ ∞ (Function.uncurry G) (J ×ˢ V))
    (k j : ℕ) {q : ℝ × ℝ} (hq : q ∈ J ×ˢ V) :
    fderivWithin ℝ
        (fun q : ℝ × ℝ => iteratedDerivWithin k
          (fun t => iteratedDeriv j (G t) q.2) J q.1) (J ×ˢ V) q =
      (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight
        (iteratedDerivWithin (k + 1) (fun t => iteratedDeriv j (G t) q.2) J q.1) +
      (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight
        (iteratedDerivWithin k (fun t => iteratedDeriv (j + 1) (G t) q.2) J q.1) := by
  rw [fderivWithin_prod_eq_partials hJ hV
    ((scalar_mixed_jets_contDiffOn hJ hV hG k j).differentiableOn (by simp)) hq]
  rw [deriv_scalar_mixed_jets hJ hacc hV hG k j hq.1 hq.2]
  simp only [iteratedDerivWithin_succ]

theorem continuousOn_iteratedFDerivWithin_of_mixed_derivatives
    {P : Type*} [TopologicalSpace P] {S : Set P} {J V : Set ℝ}
    (hJ : UniqueDiffOn ℝ J) (hacc : J ⊆ closure (interior J)) (hV : IsOpen V)
    {G : P → ℝ → ℝ → F}
    (hG : ∀ p ∈ S, ContDiffOn ℝ ∞ (Function.uncurry (G p)) (J ×ˢ V))
    (hmixed : ∀ k j : ℕ, ContinuousOn
      (fun q : P × ℝ × ℝ => iteratedDerivWithin k
        (fun t => iteratedDeriv j (G q.1 t) q.2.2) J q.2.1) (S ×ˢ J ×ˢ V))
    (n : ℕ) :
    ContinuousOn
      (fun q : P × ℝ × ℝ => iteratedFDerivWithin ℝ n
        (Function.uncurry (G q.1)) (J ×ˢ V) q.2) (S ×ˢ J ×ˢ V) := by
  let H : ℕ → ℕ → P → ℝ × ℝ → F := fun k j p q =>
    iteratedDerivWithin k (fun t => iteratedDeriv j (G p t) q.2) J q.1
  let T : F →L[ℝ] (ℝ × ℝ →L[ℝ] F) :=
    ContinuousLinearMap.smulRightL ℝ (ℝ × ℝ) F (ContinuousLinearMap.fst ℝ ℝ ℝ)
  let X : F →L[ℝ] (ℝ × ℝ →L[ℝ] F) :=
    ContinuousLinearMap.smulRightL ℝ (ℝ × ℝ) F (ContinuousLinearMap.snd ℝ ℝ ℝ)
  have hu : UniqueDiffOn ℝ (J ×ˢ V) := hJ.prod hV.uniqueDiffOn
  have hs (k j : ℕ) (p : P) (hp : p ∈ S) : ContDiffOn ℝ ∞ (H k j p) (J ×ˢ V) :=
    scalar_mixed_jets_contDiffOn hJ hV (hG p hp) k j
  have hd (k j : ℕ) (p : P) (hp : p ∈ S) :
      EqOn (fderivWithin ℝ (H k j p) (J ×ˢ V))
        (fun q => T (H (k + 1) j p q) + X (H k (j + 1) p q)) (J ×ˢ V) := by
    intro q hq
    exact fderivWithin_scalar_mixed_jets hJ hacc hV (hG p hp) k j hq
  have hall (m : ℕ) : ∀ k j : ℕ, ContinuousOn
      (fun q : P × ℝ × ℝ => iteratedFDerivWithin ℝ m (H k j q.1) (J ×ˢ V) q.2)
      (S ×ˢ J ×ˢ V) := by
    induction m with
    | zero =>
      intro k j
      exact (continuousMultilinearCurryFin0 ℝ (ℝ × ℝ) F).symm.continuous.comp_continuousOn
        (hmixed k j)
    | succ m ih =>
      intro k j
      let : ContinuousAdd
          (ContinuousMultilinearMap ℝ (fun _ : Fin m => ℝ × ℝ) ((ℝ × ℝ) →L[ℝ] F)) :=
        ContinuousMultilinearMap.instIsTopologicalAddGroup.toContinuousAdd
      have htcont := (T.continuous_postcomp_continuousMultilinearMap
        (E := fun _ : Fin m => ℝ × ℝ)).comp_continuousOn (ih (k + 1) j)
      have hxcont := (X.continuous_postcomp_continuousMultilinearMap
        (E := fun _ : Fin m => ℝ × ℝ)).comp_continuousOn (ih k (j + 1))
      have hc := htcont.add hxcont
      have hc' := (continuousMultilinearCurryRightEquiv' ℝ m (ℝ × ℝ) F).symm.continuous.comp_continuousOn hc
      apply hc'.congr
      intro q hq
      dsimp only [Function.comp_apply, Pi.add_apply]
      rw [iteratedFDerivWithin_succ_eq_comp_right hu hq.2]
      change (continuousMultilinearCurryRightEquiv' ℝ m (ℝ × ℝ) F).symm
          (iteratedFDerivWithin ℝ m (fderivWithin ℝ (H k j q.1) (J ×ˢ V))
            (J ×ˢ V) q.2) =
        (continuousMultilinearCurryRightEquiv' ℝ m (ℝ × ℝ) F).symm
          (T.compContinuousMultilinearMap
              (iteratedFDerivWithin ℝ m (H (k + 1) j q.1) (J ×ˢ V) q.2) +
            X.compContinuousMultilinearMap
              (iteratedFDerivWithin ℝ m (H k (j + 1) q.1) (J ×ˢ V) q.2))
      apply congrArg (continuousMultilinearCurryRightEquiv' ℝ m (ℝ × ℝ) F).symm
      rw [iteratedFDerivWithin_congr (hd k j q.1 hq.1) hq.2 m]
      have ht : ContDiffWithinAt ℝ m (H (k + 1) j q.1) (J ×ˢ V) q.2 :=
        (hs (k + 1) j q.1 hq.1 q.2 hq.2).of_le (WithTop.coe_le_coe.mpr le_top)
      have hx : ContDiffWithinAt ℝ m (H k (j + 1) q.1) (J ×ˢ V) q.2 :=
        (hs k (j + 1) q.1 hq.1 q.2 hq.2).of_le (WithTop.coe_le_coe.mpr le_top)
      calc
        iteratedFDerivWithin ℝ m
            (fun z => T (H (k + 1) j q.1 z) + X (H k (j + 1) q.1 z)) (J ×ˢ V) q.2 =
            iteratedFDerivWithin ℝ m (T ∘ H (k + 1) j q.1) (J ×ˢ V) q.2 +
              iteratedFDerivWithin ℝ m (X ∘ H k (j + 1) q.1) (J ×ˢ V) q.2 := by
          simpa only [Function.comp_def] using fun_iteratedFDerivWithin_add_apply
            (ht.continuousLinearMap_comp T) (hx.continuousLinearMap_comp X) hu hq.2
        _ = _ := by
          rw [T.iteratedFDerivWithin_comp_left ht hu hq.2 le_rfl,
            X.iteratedFDerivWithin_comp_left hx hu hq.2 le_rfl]
  simpa only [H, iteratedDerivWithin_zero, iteratedDeriv_zero, Function.uncurry_def] using hall n 0 0

end DifferentialGeometry.Analysis
