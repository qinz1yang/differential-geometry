import DifferentialGeometry.Analysis.Calculus.TimeJet.PartialDerivatives

open scoped ContDiff

namespace DifferentialGeometry.Analysis

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem contDiffOn_deriv_fst {f : ℝ × ℝ → F} {U J : Set ℝ}
    (hU : IsOpen U) (hJ : UniqueDiffOn ℝ J)
    (hf : ContDiffOn ℝ ∞ f (U ×ˢ J)) :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => deriv (fun y => f (y, p.2)) p.1)
      (U ×ˢ J) := by
  have hG : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => f (p.2, p.1)) (J ×ˢ U) :=
    hf.comp (contDiff_snd.prodMk contDiff_fst).contDiffOn (fun _ hp => ⟨hp.2, hp.1⟩)
  have hcd : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => fderiv ℝ (fun y => f (y, p.2)) p.1)
      (U ×ˢ J) :=
    (spatialFDeriv_contDiffOn (G := fun s y => f (y, s)) hJ hU hG).comp
      (contDiff_snd.prodMk contDiff_fst).contDiffOn (fun _ hp => ⟨hp.2, hp.1⟩)
  exact (ContinuousLinearMap.apply ℝ F (1 : ℝ)).contDiff.comp_contDiffOn hcd

theorem deriv_derivWithin_snd_comm {f : ℝ × ℝ → F} {U J : Set ℝ}
    (hU : IsOpen U) (hJ : UniqueDiffOn ℝ J) (hacc : J ⊆ closure (interior J))
    (hf : ContDiffOn ℝ ∞ f (U ×ˢ J)) {x t : ℝ} (hx : x ∈ U) (ht : t ∈ J) :
    deriv (fun y => derivWithin (fun s => f (y, s)) J t) x =
      derivWithin (fun s => deriv (fun y => f (y, s)) x) J t := by
  have hG : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => f (p.2, p.1)) (J ×ˢ U) :=
    hf.comp (contDiff_snd.prodMk contDiff_fst).contDiffOn (fun _ hp => ⟨hp.2, hp.1⟩)
  have hcomm := fderiv_derivWithin_time_comm
    (G := fun s y => f (y, s)) hJ hacc hU ht hx hG
  have hcd : ContDiffOn ℝ ∞ (fun s => fderiv ℝ (fun y => f (y, s)) x) J :=
    (spatialFDeriv_contDiffOn (G := fun s y => f (y, s)) hJ hU hG).comp
      (contDiff_id.prodMk contDiff_const).contDiffOn (fun _ hs => ⟨hs, hx⟩)
  have hd := ((ContinuousLinearMap.apply ℝ F (1 : ℝ)).hasFDerivAt.comp_hasDerivWithinAt t
    (hcd.differentiableOn (by simp) t ht).hasDerivWithinAt).derivWithin (hJ t ht)
  exact (congrArg (fun L : ℝ →L[ℝ] F => L 1) hcomm).trans hd.symm

end DifferentialGeometry.Analysis


namespace DifferentialGeometry.Analysis

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem contDiffOn_iteratedDeriv_fst_of_uniqueDiffOn {G : ℝ → ℝ → F} {U J : Set ℝ}
    (hU : IsOpen U) (hJ : UniqueDiffOn ℝ J)
    (hG : ContDiffOn ℝ ∞ (Function.uncurry G) (U ×ˢ J)) (j : ℕ) :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => iteratedDeriv j (fun y => G y p.2) p.1)
      (U ×ˢ J) := by
  induction j with
  | zero =>
    rintro ⟨x, t⟩ hp
    exact hG (x, t) hp
  | succ j ih =>
    simpa only [iteratedDeriv_succ] using contDiffOn_deriv_fst hU hJ ih

theorem derivWithin_iteratedDeriv_fst_comm {G : ℝ → ℝ → F} {U J : Set ℝ}
    (hU : IsOpen U) (hJ : UniqueDiffOn ℝ J) (hacc : J ⊆ closure (interior J))
    (hG : ContDiffOn ℝ ∞ (Function.uncurry G) (U ×ˢ J)) (j : ℕ)
    {x t : ℝ} (hx : x ∈ U) (ht : t ∈ J) :
    derivWithin (fun s => iteratedDeriv j (fun y => G y s) x) J t =
      iteratedDeriv j (fun y => derivWithin (fun s => G y s) J t) x := by
  induction j generalizing x with
  | zero => simp only [iteratedDeriv_zero]
  | succ j ih =>
    have hp := contDiffOn_iteratedDeriv_fst_of_uniqueDiffOn hU hJ hG j
    have hcomm := deriv_derivWithin_snd_comm hU hJ hacc hp hx ht
    simp only [iteratedDeriv_succ]
    rw [← hcomm]
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [hU.mem_nhds hx] with y hy
    exact ih hy

theorem hasDerivWithinAt_iteratedDeriv_fst {G : ℝ → ℝ → F} {U J : Set ℝ}
    (hU : IsOpen U) (hJ : UniqueDiffOn ℝ J) (hacc : J ⊆ closure (interior J))
    (hG : ContDiffOn ℝ ∞ (Function.uncurry G) (U ×ˢ J)) (j : ℕ)
    {x t : ℝ} (hx : x ∈ U) (ht : t ∈ J) :
    HasDerivWithinAt (fun s => iteratedDeriv j (fun y => G y s) x)
      (iteratedDeriv j (fun y => derivWithin (fun s => G y s) J t) x) J t := by
  have hj := contDiffOn_iteratedDeriv_fst_of_uniqueDiffOn hU hJ hG j
  have hd := ((hj (x, t) ⟨hx, ht⟩).comp t
    (contDiffWithinAt_const.prodMk contDiffWithinAt_id)
    (fun s hs => ⟨hx, hs⟩)).differentiableWithinAt (by simp)
  exact (derivWithin_iteratedDeriv_fst_comm hU hJ hacc hG j hx ht) ▸ hd.hasDerivWithinAt

end DifferentialGeometry.Analysis


namespace DifferentialGeometry.Analysis

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem contDiffOn_iteratedDeriv_fst {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {G : ℝ → E → F} {U : Set ℝ} {V : Set E}
    (hU : IsOpen U) (hV : IsOpen V)
    (hG : ContDiffOn ℝ ∞ (Function.uncurry G) (U ×ˢ V)) (j : ℕ) :
    ContDiffOn ℝ ∞ (fun p : ℝ × E => iteratedDeriv j (fun y => G y p.2) p.1)
      (U ×ˢ V) := by
  induction j with
  | zero =>
    rintro ⟨x, t⟩ hp
    exact hG (x, t) hp
  | succ j ih =>
    intro p hp
    simpa only [iteratedDeriv_succ] using
      (contDiffAt_deriv_fst (m := ∞)
        ((ih p hp).contDiffAt ((hU.prod hV).mem_nhds hp)) (by simp)).contDiffWithinAt

theorem deriv_iteratedDeriv_fst_comm {G : ℝ → ℝ → F} {U V : Set ℝ}
    (hU : IsOpen U) (hV : IsOpen V)
    (hG : ContDiffOn ℝ ∞ (Function.uncurry G) (U ×ˢ V)) (j : ℕ)
    {x t : ℝ} (hx : x ∈ U) (ht : t ∈ V) :
    deriv (fun s => iteratedDeriv j (fun y => G y s) x) t =
      iteratedDeriv j (fun y => deriv (fun s => G y s) t) x := by
  have hacc : V ⊆ closure (interior V) := by
    rw [hV.interior_eq]
    exact subset_closure
  simpa only [derivWithin_of_isOpen hV ht] using
    derivWithin_iteratedDeriv_fst_comm hU hV.uniqueDiffOn hacc hG j hx ht

theorem hasDerivAt_iteratedDeriv_fst {G : ℝ → ℝ → F} {U V : Set ℝ}
    (hU : IsOpen U) (hV : IsOpen V)
    (hG : ContDiffOn ℝ ∞ (Function.uncurry G) (U ×ˢ V)) (j : ℕ)
    {x t : ℝ} (hx : x ∈ U) (ht : t ∈ V) :
    HasDerivAt (fun s => iteratedDeriv j (fun y => G y s) x)
      (iteratedDeriv j (fun y => deriv (fun s => G y s) t) x) t := by
  have hacc : V ⊆ closure (interior V) := by
    rw [hV.interior_eq]
    exact subset_closure
  simpa only [derivWithin_of_isOpen hV ht] using
    (hasDerivWithinAt_iteratedDeriv_fst hU hV.uniqueDiffOn hacc hG j hx ht).hasDerivAt
      (hV.mem_nhds ht)

end DifferentialGeometry.Analysis
