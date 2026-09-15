import DifferentialGeometry.Bundle.PartialMfderiv.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.ContDiff.Comp

section

open Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem contMDiffAt_deriv_snd {G : M × ℝ → F} {p : M × ℝ} {m n : ℕ∞ω}
    (hG : ContMDiffAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, F) n G p) (hmn : m + 1 ≤ n) :
    ContMDiffAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, F) m
      (fun q : M × ℝ => deriv (fun s => G (q.1, s)) q.2) p := by
  have hs : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, F) n
      (fun q : ℝ × M => G (q.2, q.1)) (p.2, p.1) :=
    hG.comp (p.2, p.1) (contMDiffAt_snd.prodMk contMDiffAt_fst)
  have hd := DifferentialGeometry.timeDeriv_smoothAt hs hmn
  exact hd.comp p (contMDiffAt_snd.prodMk contMDiffAt_fst)

theorem contMDiffAt_iteratedDeriv_snd_of_add_le {G : M × ℝ → F} {p : M × ℝ}
    {m n : ℕ∞ω} (hG : ContMDiffAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, F) n G p)
    (j : ℕ) (hmn : m + j ≤ n) :
    ContMDiffAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, F) m
      (fun q : M × ℝ => iteratedDeriv j (fun s => G (q.1, s)) q.2) p := by
  induction j generalizing m with
  | zero =>
    exact hG.of_le (by simpa only [Nat.cast_zero, add_zero] using hmn)
  | succ j ih =>
    have hsum : (m + 1) + j ≤ n := by
      simpa only [Nat.cast_add, Nat.cast_one, add_assoc, add_comm (1 : ℕ∞ω) (j : ℕ∞ω)] using hmn
    simpa only [iteratedDeriv_succ] using contMDiffAt_deriv_snd (ih hsum) le_rfl

theorem contMDiffAt_iteratedDeriv_snd {G : M × ℝ → F} {p : M × ℝ}
    (hG : ContMDiffAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, F) ∞ G p) (j : ℕ) :
    ContMDiffAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, F) ∞
      (fun q : M × ℝ => iteratedDeriv j (fun s => G (q.1, s)) q.2) p := by
  exact contMDiffAt_iteratedDeriv_snd_of_add_le hG j
    (WithTop.coe_le_coe.mpr le_top)

theorem contMDiffOn_iteratedDeriv_snd {G : M × ℝ → F} {U : Set (M × ℝ)}
    (hU : IsOpen U) (hG : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, F) ∞ G U) (j : ℕ) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, F) ∞
      (fun q : M × ℝ => iteratedDeriv j (fun s => G (q.1, s)) q.2) U := by
  intro p hp
  exact (contMDiffAt_iteratedDeriv_snd (hG.contMDiffAt (hU.mem_nhds hp)) j).contMDiffWithinAt

theorem continuousOn_iteratedDeriv_snd_of_contMDiffOn {G : M × ℝ → F} {U : Set (M × ℝ)}
    (hU : IsOpen U) (hG : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, F) ∞ G U) (j : ℕ) :
    ContinuousOn (fun q : M × ℝ => iteratedDeriv j (fun s => G (q.1, s)) q.2) U :=
  (contMDiffOn_iteratedDeriv_snd hU hG j).continuousOn

end DifferentialGeometry.Analysis

end

section

open Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K : Type*} [TopologicalSpace K]

theorem continuousOn_iteratedDeriv_parameter_comp
    {G : M × ℝ → F} {U : Set M} {J : Set ℝ}
    (hU : IsOpen U) (hJ : IsOpen J)
    (hG : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, F) ∞ G (U ×ˢ J))
    {v : K → M} (hv : Continuous v) (hvU : ∀ k, v k ∈ U)
    {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β) {s : Set ℝ} (hs : MapsTo β s J) (j : ℕ) :
    ContinuousOn (fun q : K × ℝ =>
      iteratedDeriv j (fun t => G (v q.1, β t)) q.2) (univ ×ˢ s) := by
  have hsm : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, F) ∞
      (fun p : M × ℝ => G (p.1, β p.2)) (U ×ˢ (β ⁻¹' J)) := by
    apply hG.comp
      (contMDiff_fst.prodMk (hβ.contMDiff.comp contMDiff_snd)).contMDiffOn
    intro p hp
    exact ⟨hp.1, hp.2⟩
  have hj := continuousOn_iteratedDeriv_snd_of_contMDiffOn
    (hU.prod (hJ.preimage hβ.continuous)) hsm j
  exact hj.comp (hv.comp continuous_fst |>.prodMk continuous_snd).continuousOn
    (fun p hp => ⟨hvU p.1, hs hp.2⟩)

end DifferentialGeometry.Analysis

end
