import DifferentialGeometry.Analysis.Calculus.TimeJet.Commutation

open scoped ContDiff

namespace DifferentialGeometry.Analysis

variable {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem contDiffAt_deriv_fst {Φ : ℝ × E → F} {z : ℝ × E}
    {m n : WithTop ℕ∞} (hΦ : ContDiffAt ℝ n Φ z) (hmn : m + 1 ≤ n) :
    ContDiffAt ℝ m (fun p : ℝ × E => deriv (fun s => Φ (s, p.2)) p.1) z := by
  have hcomp : ContDiffAt ℝ n
      (fun p : (ℝ × E) × ℝ => Φ (p.2, p.1.2)) (z, z.1) :=
    hΦ.comp (z, z.1) (contDiffAt_snd.prodMk contDiffAt_fst.snd)
  exact (hcomp.fderiv contDiffAt_fst hmn).clm_apply contDiffAt_const

theorem deriv_deriv_time_comm_on_open {G : ℝ → ℝ → F} {U V : Set ℝ}
    (hU : IsOpen U) (hV : IsOpen V)
    (hG : ContDiffOn ℝ ∞ (Function.uncurry G) (U ×ˢ V))
    {x t : ℝ} (hx : x ∈ U) (ht : t ∈ V) :
    deriv (fun s => deriv (fun y => G y s) x) t =
      deriv (fun y => deriv (fun s => G y s) t) x := by
  have hacc : U ⊆ closure (interior U) := by
    rw [hU.interior_eq]
    exact subset_closure
  have hcomm := fderiv_derivWithin_time_comm hU.uniqueDiffOn hacc hV hx ht hG
  simp only [derivWithin_of_isOpen hU hx] at hcomm
  have hcd : ContDiffAt ℝ ∞ (fun y => fderiv ℝ (G y) t) x :=
    (((spatialFDeriv_contDiffOn hU.uniqueDiffOn hV hG) (x, t) ⟨hx, ht⟩).contDiffAt
      ((hU.prod hV).mem_nhds ⟨hx, ht⟩)).comp x (contDiffAt_id.prodMk contDiffAt_const)
  have hd := ((ContinuousLinearMap.apply ℝ F (1 : ℝ)).hasFDerivAt.comp_hasDerivAt x
    (hcd.differentiableAt (by simp)).hasDerivAt).deriv
  exact (congrArg (fun L : ℝ →L[ℝ] F => L 1) hcomm).trans hd.symm

theorem deriv_deriv_deriv_time_comm {G : ℝ → ℝ → F} {U V : Set ℝ}
    (hU : IsOpen U) (hV : IsOpen V)
    (hG : ContDiffOn ℝ ∞ (Function.uncurry G) (U ×ˢ V))
    {x t : ℝ} (hx : x ∈ U) (ht : t ∈ V) :
    deriv (fun s => deriv (deriv (fun y => G y s)) x) t =
      deriv (deriv (fun y => deriv (fun s => G y s) t)) x := by
  have hp : ContDiffOn ℝ ∞
      (fun p : ℝ × ℝ => deriv (fun y => G y p.2) p.1) (U ×ˢ V) := by
    intro p hp
    exact (contDiffAt_deriv_fst (m := ∞)
      ((hG p hp).contDiffAt ((hU.prod hV).mem_nhds hp)) (by simp)).contDiffWithinAt
  have hcomm := deriv_deriv_time_comm_on_open
    (G := fun y s => deriv (fun z => G z s) y) hU hV hp hx ht
  change deriv (fun s => deriv (deriv (fun y => G y s)) x) t =
    deriv (fun y => deriv (fun s => deriv (fun z => G z s) y) t) x at hcomm
  rw [hcomm]
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [hU.mem_nhds hx] with y hy
  exact deriv_deriv_time_comm_on_open hU hV hG hy ht

end DifferentialGeometry.Analysis
