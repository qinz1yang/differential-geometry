import DifferentialGeometry.Analysis.Calculus.MapConvergence.Basic
import DifferentialGeometry.Analysis.Calculus.MapConvergence.Derivative

section

set_option autoImplicit false

namespace DifferentialGeometry.CheegerGromovCompactness

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E]
  [NormedAddCommGroup F] [NormedSpace Real F]

theorem MapCInfConvergenceOnCompacts.unique
    {U V : Set E} {Phi : Nat → E → F} {f g : E → F}
    (hf : MapCInfConvergenceOnCompacts U Phi f)
    (hg : MapCInfConvergenceOnCompacts V Phi g) : Set.EqOn f g (U ∩ V) := by
  intro z hz
  exact tendsto_nhds_unique (tendsto_of_cInf hf hz.1) (tendsto_of_cInf hg hz.2)

end DifferentialGeometry.CheegerGromovCompactness


end

section

open Filter Topology
open scoped ContDiff

namespace DifferentialGeometry.CheegerGromovCompactness

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem MapCInfConvergenceOnCompacts.tendsto_comp
    {V : Set F} (hV : IsOpen V) {C : ℕ → F → G} {Cinf : F → G}
    (hC : MapCInfConvergenceOnCompacts V C Cinf)
    {y : ℕ → F} {yinf : F} (hy : Tendsto y atTop (𝓝 yinf))
    (hyinf : yinf ∈ V) (hCinf : ContinuousWithinAt Cinf V yinf) :
    Tendsto (fun n => C n (y n)) atTop (𝓝 (Cinf yinf)) := by
  classical
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hy.eventually_mem (hV.mem_nhds hyinf))
  let y' : ℕ → F := fun n => if N ≤ n then y n else yinf
  have heq : y' =ᶠ[atTop] y := by
    filter_upwards [eventually_ge_atTop N] with n hn
    simp only [y', if_pos hn]
  have hy' : Tendsto y' atTop (𝓝 yinf) := hy.congr' heq.symm
  let K : Set F := insert yinf (Set.range y')
  have hKV : K ⊆ V := by
    rintro a (rfl | ⟨n, rfl⟩)
    · exact hyinf
    · dsimp only [y']
      split_ifs with hn
      · exact hN n hn
      · exact hyinf
  have hK : IsCompact K := hy'.isCompact_insert_range
  have hwithin : Tendsto y' atTop (𝓝[K] yinf) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hy'
      (Eventually.of_forall fun n => Set.mem_insert_of_mem _ (Set.mem_range_self n))
  have hcomp := (tendstoUniformlyOn_of_cPConvergence (hC K hK hKV 0)).tendsto_comp
    (hCinf.mono hKV) hwithin
  exact hcomp.congr' (heq.mono fun n hn => congrArg (C n) hn)

theorem eq_pullbackForm_of_mapCInfConvergenceOnCompacts
    {U : Set E} {V : Set F} (hU : IsOpen U) (hV : IsOpen V)
    {B : ℕ → E → E →L[ℝ] E →L[ℝ] ℝ} {Binf : E → E →L[ℝ] E →L[ℝ] ℝ}
    {C : ℕ → F → F →L[ℝ] F →L[ℝ] ℝ} {Cinf : F → F →L[ℝ] F →L[ℝ] ℝ}
    {Φ : ℕ → E → F} {Φinf : E → F}
    (hB : MapCInfConvergenceOnCompacts U B Binf)
    (hC : MapCInfConvergenceOnCompacts V C Cinf)
    (hΦ : MapCInfConvergenceOnCompacts U Φ Φinf)
    (hΦsmooth : ∀ n, ContDiffOn ℝ ∞ (Φ n) U)
    (hΦinf : ContDiffOn ℝ ∞ Φinf U)
    (hCinf : ContinuousOn Cinf V)
    (hmetric : ∀ᶠ n in atTop, ∀ z ∈ U, Φ n z ∈ V → ∀ u v,
      B n z u v = C n (Φ n z) (fderiv ℝ (Φ n) z u) (fderiv ℝ (Φ n) z v))
    {z : E} (hz : z ∈ U) (hzV : Φinf z ∈ V) :
    Binf z = pullbackForm (Cinf (Φinf z), fderiv ℝ Φinf z) := by
  have hΦz := tendsto_of_cInf hΦ hz
  have hCz := hC.tendsto_comp hV hΦz hzV (hCinf _ hzV)
  have hDz := tendsto_of_cInf (hΦ.fderivOn hU hΦsmooth hΦinf) hz
  have hpull : Tendsto (fun n => pullbackForm (C n (Φ n z), fderiv ℝ (Φ n) z))
      atTop (𝓝 (pullbackForm (Cinf (Φinf z), fderiv ℝ Φinf z))) :=
    (pullbackForm.contDiff.continuous.tendsto _).comp (hCz.prodMk_nhds hDz)
  have heq : (fun n => B n z) =ᶠ[atTop]
      (fun n => pullbackForm (C n (Φ n z), fderiv ℝ (Φ n) z)) := by
    filter_upwards [hmetric, hΦz.eventually_mem (hV.mem_nhds hzV)] with n hn hnV
    ext u v
    exact hn z hz hnV u v
  exact tendsto_nhds_unique (tendsto_of_cInf hB hz) (hpull.congr' heq.symm)

end DifferentialGeometry.CheegerGromovCompactness


end

section

namespace DifferentialGeometry.CheegerGromovCompactness

open Filter Topology

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem comp_eq_of_mapCInfConvergenceOnCompacts_on
    {U : Set E} {V : Set F}
    {phi : ℕ → F → G} {phiInf : F → G}
    {psi : ℕ → E → F} {psiInf : E → F}
    {chi : ℕ → E → G} {chiInf : E → G}
    (hV : IsOpen V)
    (hphi : MapCInfConvergenceOnCompacts V phi phiInf)
    (hphiCont : ContinuousOn phiInf V)
    (hpsi : MapCInfConvergenceOnCompacts U psi psiInf)
    (hchi : MapCInfConvergenceOnCompacts U chi chiInf)
    (hcomp : ∀ᶠ k in atTop, ∀ x ∈ U, phi k (psi k x) = chi k x)
    {x : E} (hx : x ∈ U) (hpsiInf : psiInf x ∈ V) :
    phiInf (psiInf x) = chiInf x := by
  have hlim := hphi.tendsto_comp hV (tendsto_of_cInf hpsi hx) hpsiInf
    (hphiCont _ hpsiInf)
  apply tendsto_nhds_unique hlim
  exact (tendsto_of_cInf hchi hx).congr' (hcomp.mono fun k hk => (hk x hx).symm)

end DifferentialGeometry.CheegerGromovCompactness


end
