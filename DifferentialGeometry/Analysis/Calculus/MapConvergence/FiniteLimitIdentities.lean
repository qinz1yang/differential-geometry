import DifferentialGeometry.Analysis.Calculus.MapConvergence.Basic

set_option autoImplicit false

namespace DifferentialGeometry.CheegerGromovCompactness

open Filter Topology

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem tendsto_comp_of_mapCP_zero_on_compacts
    {V : Set F} (hV : IsOpen V) {C : ℕ → F → G} {Cinf : F → G}
    (hC : ∀ S : Set F, IsCompact S → S ⊆ V → MapCPConvergenceOn S 0 C Cinf)
    {y : ℕ → F} {yinf : F} (hy : Tendsto y atTop (𝓝 yinf))
    (hyinf : yinf ∈ V) (hCinf : ContinuousWithinAt Cinf V yinf) :
    Tendsto (fun k => C k (y k)) atTop (𝓝 (Cinf yinf)) := by
  classical
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hy.eventually_mem (hV.mem_nhds hyinf))
  let y' : ℕ → F := fun k => if N ≤ k then y k else yinf
  have heq : y' =ᶠ[atTop] y := by
    filter_upwards [eventually_ge_atTop N] with k hk
    simp only [y', ite_eq_left hk]
  have hy' : Tendsto y' atTop (𝓝 yinf) := hy.congr' heq.symm
  let S : Set F := insert yinf (Set.range y')
  have hSV : S ⊆ V := by
    rintro a (rfl | ⟨k, rfl⟩)
    · exact hyinf
    · dsimp only [y']
      split_ifs with hk
      · exact hN k hk
      · exact hyinf
  have hS : IsCompact S := hy'.isCompact_insert_range
  have hwithin : Tendsto y' atTop (𝓝[S] yinf) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hy'
      (Eventually.of_forall fun k => Set.mem_insert_of_mem _ (Set.mem_range_self k))
  have hcomp := (tendstoUniformlyOn_of_cPConvergence (hC S hS hSV)).tendsto_comp
    (hCinf.mono hSV) hwithin
  exact hcomp.congr' (heq.mono fun k hk => congrArg (C k) hk)

theorem MapCPConvergenceOn.tendsto_fderiv_at
    {S : Set E} {Φ : ℕ → E → F} {Φinf : E → F}
    (hΦ : MapCPConvergenceOn S 1 Φ Φinf)
    {x : E} (hx : x ∈ S)
    (hΦdiff : ∀ k, DifferentiableAt ℝ (Φ k) x)
    (hΦinf : DifferentiableAt ℝ Φinf x) :
    Tendsto (fun k => fderiv ℝ (Φ k) x) atTop (𝓝 (fderiv ℝ Φinf x)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := hΦ (ε / 2) (by positivity)
  refine ⟨N, fun k hk => ?_⟩
  have hb := hN k hk 1 le_rfl x hx
  rw [mapDerivNorm, norm_iteratedFDeriv_one, fderiv_fun_sub (hΦdiff k) hΦinf] at hb
  rw [dist_eq_norm]
  exact lt_of_le_of_lt hb (by linarith)

theorem bilinear_pullback_identity_of_mapCP_convergence
    {U : Set E} {V : Set F} (hU : IsOpen U) (hV : IsOpen V)
    {B : ℕ → E → E →L[ℝ] E →L[ℝ] ℝ} {Binf : E → E →L[ℝ] E →L[ℝ] ℝ}
    {C : ℕ → F → F →L[ℝ] F →L[ℝ] ℝ} {Cinf : F → F →L[ℝ] F →L[ℝ] ℝ}
    {Φ : ℕ → E → F} {Φinf : E → F}
    (hB : ∀ S : Set E, IsCompact S → S ⊆ U → MapCPConvergenceOn S 0 B Binf)
    (hC : ∀ S : Set F, IsCompact S → S ⊆ V → MapCPConvergenceOn S 0 C Cinf)
    (hΦ : ∀ S : Set E, IsCompact S → S ⊆ U → MapCPConvergenceOn S 1 Φ Φinf)
    (hΦdiff : ∀ k, ContDiffOn ℝ 1 (Φ k) U)
    (hΦinf : ContDiffOn ℝ 1 Φinf U)
    (hCinf : ContinuousOn Cinf V)
    (hmetric : ∀ᶠ k in atTop, ∀ z ∈ U, Φ k z ∈ V → ∀ v w,
      B k z v w = C k (Φ k z) (fderiv ℝ (Φ k) z v) (fderiv ℝ (Φ k) z w))
    {z : E} (hz : z ∈ U) (hzV : Φinf z ∈ V) (v w : E) :
    Binf z v w = Cinf (Φinf z) (fderiv ℝ Φinf z v) (fderiv ℝ Φinf z w) := by
  have hΦone := hΦ {z} isCompact_singleton (Set.singleton_subset_iff.mpr hz)
  have hΦz := (tendstoUniformlyOn_of_cPConvergence
    (hΦone.mono_order (Nat.zero_le 1))).tendsto_at rfl
  have hCz := tendsto_comp_of_mapCP_zero_on_compacts hV hC hΦz hzV (hCinf _ hzV)
  have hDz := hΦone.tendsto_fderiv_at rfl
    (fun k => ((hΦdiff k).contDiffAt (hU.mem_nhds hz)).differentiableAt (by norm_num))
    ((hΦinf.contDiffAt (hU.mem_nhds hz)).differentiableAt (by norm_num))
  have heval : Continuous (fun a : (F →L[ℝ] F →L[ℝ] ℝ) × (E →L[ℝ] F) =>
      a.1 (a.2 v) (a.2 w)) := by fun_prop
  have hlim := (heval.tendsto _).comp (hCz.prodMk_nhds hDz)
  have heq : (fun k => B k z v w) =ᶠ[atTop]
      (fun k => C k (Φ k z) (fderiv ℝ (Φ k) z v) (fderiv ℝ (Φ k) z w)) := by
    filter_upwards [hmetric, hΦz.eventually_mem (hV.mem_nhds hzV)] with k hk hkV
    exact hk z hz hkV v w
  have hBz := (tendstoUniformlyOn_of_cPConvergence
    (hB {z} isCompact_singleton (Set.singleton_subset_iff.mpr hz))).tendsto_at rfl
  have hBeval : Continuous (fun b : E →L[ℝ] E →L[ℝ] ℝ => b v w) := by fun_prop
  exact tendsto_nhds_unique ((hBeval.tendsto _).comp hBz) (hlim.congr' heq.symm)

theorem comp_eq_of_mapCP_zero_on_compacts
    {U : Set E} {V : Set F}
    {φ : ℕ → F → G} {φinf : F → G}
    {ψ : ℕ → E → F} {ψinf : E → F}
    {χ : ℕ → E → G} {χinf : E → G}
    (hV : IsOpen V)
    (hφ : ∀ S : Set F, IsCompact S → S ⊆ V → MapCPConvergenceOn S 0 φ φinf)
    (hφcont : ContinuousOn φinf V)
    (hψ : ∀ S : Set E, IsCompact S → S ⊆ U → MapCPConvergenceOn S 0 ψ ψinf)
    (hχ : ∀ S : Set E, IsCompact S → S ⊆ U → MapCPConvergenceOn S 0 χ χinf)
    (hcomp : ∀ᶠ k in atTop, ∀ x ∈ U, φ k (ψ k x) = χ k x)
    {x : E} (hx : x ∈ U) (hψinf : ψinf x ∈ V) :
    φinf (ψinf x) = χinf x := by
  have hψx := (tendstoUniformlyOn_of_cPConvergence
    (hψ {x} isCompact_singleton (Set.singleton_subset_iff.mpr hx))).tendsto_at rfl
  have hχx := (tendstoUniformlyOn_of_cPConvergence
    (hχ {x} isCompact_singleton (Set.singleton_subset_iff.mpr hx))).tendsto_at rfl
  have hlim := tendsto_comp_of_mapCP_zero_on_compacts hV hφ hψx hψinf (hφcont _ hψinf)
  exact tendsto_nhds_unique hlim (hχx.congr' (hcomp.mono fun k hk => (hk x hx).symm))

theorem comp_eq_of_mapCP_zero_on_compacts_on_overlaps
    {U : Set E} {V : Set F} {W : Set G}
    {φ : ℕ → F → G} {φinf : F → G}
    {ψ : ℕ → E → F} {ψinf : E → F}
    {χ : ℕ → E → G} {χinf : E → G}
    (hV : IsOpen V) (hW : IsOpen W)
    (hφ : ∀ S : Set F, IsCompact S → S ⊆ V → MapCPConvergenceOn S 0 φ φinf)
    (hφcont : ContinuousOn φinf V)
    (hψ : ∀ S : Set E, IsCompact S → S ⊆ U → MapCPConvergenceOn S 0 ψ ψinf)
    (hχ : ∀ S : Set E, IsCompact S → S ⊆ U → MapCPConvergenceOn S 0 χ χinf)
    (hcomp : ∀ᶠ k in atTop, ∀ x ∈ U, ψ k x ∈ V → φ k (ψ k x) ∈ W →
      φ k (ψ k x) = χ k x)
    {x : E} (hx : x ∈ U) (hψinf : ψinf x ∈ V) (hφψinf : φinf (ψinf x) ∈ W) :
    φinf (ψinf x) = χinf x := by
  have hψx := (tendstoUniformlyOn_of_cPConvergence
    (hψ {x} isCompact_singleton (Set.singleton_subset_iff.mpr hx))).tendsto_at rfl
  have hχx := (tendstoUniformlyOn_of_cPConvergence
    (hχ {x} isCompact_singleton (Set.singleton_subset_iff.mpr hx))).tendsto_at rfl
  have hlim := tendsto_comp_of_mapCP_zero_on_compacts hV hφ hψx hψinf (hφcont _ hψinf)
  have heq : (fun k => χ k x) =ᶠ[atTop] (fun k => φ k (ψ k x)) := by
    filter_upwards [hcomp, hψx.eventually_mem (hV.mem_nhds hψinf),
      hlim.eventually_mem (hW.mem_nhds hφψinf)] with k hk hψk hφψk
    exact (hk x hx hψk hφψk).symm
  exact tendsto_nhds_unique hlim (hχx.congr' heq)

end DifferentialGeometry.CheegerGromovCompactness
