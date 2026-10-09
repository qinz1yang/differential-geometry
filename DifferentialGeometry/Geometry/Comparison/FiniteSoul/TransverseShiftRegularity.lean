import DifferentialGeometry.Geometry.Exponential.FiniteMetric.GaussLemma
import DifferentialGeometry.Bundle.TangentChart
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# A continuous unit normal along a geodesic of a surface is `C^r` (S-SHIFT2, regularity)

In dimension two, a unit vector field `ξ` along a unit-speed geodesic `γ = π φ_t(p)` of a `C^(r+1)`
metric which is orthogonal to `γ'` and continuous (as a curve in the tangent bundle) is locally the
Gram–Schmidt normal of the chart velocity, hence `t ↦ (γ t, ξ t)` is `C^r`
(`contMDiffAt_unitNormal_dim_two`). No parallel transport is used: in a two-dimensional inner product
space the unit vectors orthogonal to a unit vector are `±` one vector (`eq_smul_of_orthonormal_dim_two`),
and the sign is locally constant.
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.FiniteSoul

section Algebra

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- In a two-dimensional space with a positive symmetric bilinear form `B`, a vector `X` orthogonal to
a unit vector `U` is a multiple of any unit vector `N` orthogonal to `U`: `X = B(X, N) N`. -/
theorem eq_smul_of_orthonormal_dim_two (hdim : Module.finrank ℝ E = 2)
    {B : E →L[ℝ] E →L[ℝ] ℝ} (hsymm : ∀ u v, B u v = B v u) {U N X : E}
    (hU : B U U = 1) (hN : B N N = 1) (hNU : B N U = 0) (hXU : B X U = 0) :
    X = B X N • N := by
  have hli : LinearIndependent ℝ ![U, N] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h1 := congrArg (fun z => B z U) hst
    have h2 := congrArg (fun z => B z N) hst
    simp only [map_add, map_smul, add_apply, smul_apply,
      smul_eq_mul, map_zero, zero_apply] at h1 h2
    rw [hU, hNU] at h1
    rw [hN, hsymm U N, hNU] at h2
    constructor <;> linarith
  have hspan := hli.span_eq_top_of_card_eq_finrank' (by simp [hdim])
  have hX : X ∈ Submodule.span ℝ (range ![U, N]) := by rw [hspan]; exact Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hX
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at hc
  have h1 := congrArg (fun z => B z U) hc
  have h2 := congrArg (fun z => B z N) hc
  simp only [map_add, map_smul, add_apply, smul_apply,
    smul_eq_mul] at h1 h2
  rw [hU, hNU, hXU] at h1
  rw [hN, hsymm U N, hNU] at h2
  have hc0 : c 0 = 0 := by linarith
  have hc1 : c 1 = B X N := by linarith
  calc X = c 0 • U + c 1 • N := hc.symm
    _ = B X N • N := by rw [hc0, zero_smul, zero_add, hc1]

end Algebra

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

/-- **Regularity of a continuous unit normal (dimension two).** -/
theorem contMDiffAt_unitNormal_dim_two {r : ℕ∞}
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 1 ≤ r) (hdim : Module.finrank ℝ E = 2) (p : TangentBundle I M)
    (hdom : ∀ t, (p, t) ∈ g.geodesicFlowDomain) (hp : g.inner p.proj p.snd p.snd = 1)
    {ξ : ℝ → E} {J : Set ℝ} (hJ : IsOpen J)
    (hcont : ContinuousOn (fun t => (⟨(g.geodesicFlow p t).proj, ξ t⟩ : TangentBundle I M)) J)
    (hunit : ∀ t ∈ J, g.inner (g.geodesicFlow p t).proj (ξ t) (ξ t) = 1)
    (hperp : ∀ t ∈ J, g.inner (g.geodesicFlow p t).proj (ξ t) (g.geodesicFlow p t).snd = 0)
    {t₀ : ℝ} (ht₀ : t₀ ∈ J) :
    ContMDiffAt 𝓘(ℝ, ℝ) I.tangent r
      (fun t => (⟨(g.geodesicFlow p t).proj, ξ t⟩ : TangentBundle I M)) t₀ := by
  set Fl : ℝ → TangentBundle I M := fun t => g.geodesicFlow p t with hFl
  set V : ℝ → TangentBundle I M := fun t => ⟨(g.geodesicFlow p t).proj, ξ t⟩ with hV
  set q₀ := Fl t₀ with hq₀
  set x₀ := q₀.proj with hx₀
  set ψ := extChartAt I.tangent q₀ with hψ
  -- regularity of the flow line and its chart reading
  have hFlc : ∀ t, ContMDiffAt 𝓘(ℝ, ℝ) I.tangent r Fl t := by
    intro t
    have hin : ContMDiff 𝓘(ℝ, ℝ) (I.tangent.prod 𝓘(ℝ, ℝ)) ∞ (fun s : ℝ => (p, s)) :=
      contMDiff_const.prodMk contMDiff_id
    exact ((g.contMDiffOn_geodesicFlow hr).contMDiffAt
      ((g.isOpen_geodesicFlowDomain hr).mem_nhds (hdom t))).comp t
      ((hin t).of_le (by exact_mod_cast le_top))
  have hψFl : ContDiffAt ℝ r (fun t => ψ (Fl t)) t₀ := by
    have h := (contMDiffAt_extChartAt (I := I.tangent) (x := q₀) (n := r)).comp t₀ (hFlc t₀)
    exact contMDiffAt_iff_contDiffAt.mp h
  set Y : ℝ → E := fun t => (ψ (Fl t)).1 with hY
  set U : ℝ → E := fun t => (ψ (Fl t)).2 with hU
  set X : ℝ → E := fun t => (ψ (V t)).2 with hX
  have hYc : ContDiffAt ℝ r Y t₀ := hψFl.fst
  have hUc : ContDiffAt ℝ r U t₀ := hψFl.snd
  -- the chart neighbourhood
  have hFlcont : Continuous Fl := continuous_iff_continuousAt.mpr fun t => (hFlc t).continuousAt
  have hγc : Continuous fun t => (g.geodesicFlow p t).proj :=
    (FiberBundle.continuous_proj E (TangentSpace I : M → Type _)).comp hFlcont
  have hγt₀ : (g.geodesicFlow p t₀).proj = x₀ := rfl
  have hS : ∀ᶠ t in 𝓝 t₀, (g.geodesicFlow p t).proj ∈ (chartAt H x₀).source :=
    hγc.continuousAt.preimage_mem_nhds
      ((chartAt H x₀).open_source.mem_nhds (by rw [hγt₀]; exact mem_chart_source H x₀))
  have hJn : ∀ᶠ t in 𝓝 t₀, t ∈ J := hJ.mem_nhds ht₀
  -- chart readings
  have hV1 : ∀ t, (ψ (V t)).1 = Y t := fun t => by
    simp only [hY, hψ]
    rw [TangentBundle.extChartAt_tangent_apply_fst q₀, TangentBundle.extChartAt_tangent_apply_fst q₀]
  have hUeq : ∀ t, (g.geodesicFlow p t).proj ∈ (chartAt H x₀).source →
      U t = mfderiv I 𝓘(ℝ, E) (extChartAt I x₀) (g.geodesicFlow p t).proj
        (g.geodesicFlow p t).snd := by
    intro t ht
    simp only [hU, hψ]
    rw [TangentBundle.extChartAt_tangent_apply_snd q₀ ht,
      TangentBundle.continuousLinearMapAt_trivializationAt ht]
    rfl
  have hXeq : ∀ t, (g.geodesicFlow p t).proj ∈ (chartAt H x₀).source →
      X t = mfderiv I 𝓘(ℝ, E) (extChartAt I x₀) (g.geodesicFlow p t).proj (ξ t) := by
    intro t ht
    simp only [hX, hψ]
    rw [TangentBundle.extChartAt_tangent_apply_snd q₀ (p := V t) ht,
      TangentBundle.continuousLinearMapAt_trivializationAt ht]
    rfl
  have hYeq : ∀ t, Y t = extChartAt I x₀ (g.geodesicFlow p t).proj := fun t =>
    TangentBundle.extChartAt_tangent_apply_fst q₀
  -- the chart coefficients along the geodesic
  set B : ℝ → E →L[ℝ] E →L[ℝ] ℝ := fun t => g.chartInner x₀ (Y t) with hB
  have hYt₀ : Y t₀ ∈ (extChartAt I x₀).target := by
    rw [hYeq, hγt₀]; exact mem_extChartAt_target x₀
  have hBc : ContDiffAt ℝ r B t₀ :=
    ((g.contDiffOn_chartInner x₀).contDiffAt
      ((isOpen_extChartAt_target x₀).mem_nhds hYt₀)).comp t₀ hYc
  have hspeed : ∀ t, g.inner (g.geodesicFlow p t).proj (g.geodesicFlow p t).snd
      (g.geodesicFlow p t).snd = 1 := fun t => by
    rw [g.inner_geodesicFlow_eq hr p t (hdom t), hp]
  have hread : ∀ t, (g.geodesicFlow p t).proj ∈ (chartAt H x₀).source → ∀ a b : E,
      g.inner (g.geodesicFlow p t).proj a b = B t (mfderiv I 𝓘(ℝ, E) (extChartAt I x₀)
        (g.geodesicFlow p t).proj a) (mfderiv I 𝓘(ℝ, E) (extChartAt I x₀)
        (g.geodesicFlow p t).proj b) := by
    intro t ht a b
    simp only [hB]
    rw [hYeq]
    exact g.inner_eq_chartInner ht a b
  have hBUU : ∀ t, (g.geodesicFlow p t).proj ∈ (chartAt H x₀).source → B t (U t) (U t) = 1 :=
    fun t ht => by
      have h := hread t ht (g.geodesicFlow p t).snd (g.geodesicFlow p t).snd
      rw [hspeed t] at h
      rw [hUeq t ht]; exact h.symm
  have hBXX : ∀ t, (g.geodesicFlow p t).proj ∈ (chartAt H x₀).source → t ∈ J →
      B t (X t) (X t) = 1 := fun t ht htJ => by
    have h := hread t ht (ξ t) (ξ t)
    rw [hunit t htJ] at h
    rw [hXeq t ht]; exact h.symm
  have hBXU : ∀ t, (g.geodesicFlow p t).proj ∈ (chartAt H x₀).source → t ∈ J →
      B t (X t) (U t) = 0 := fun t ht htJ => by
    have h := hread t ht (ξ t) (g.geodesicFlow p t).snd
    rw [hperp t htJ] at h
    rw [hXeq t ht, hUeq t ht]; exact h.symm
  have hBsymm : ∀ t (a b : E), B t a b = B t b a := fun t a b => g.chartInner_symm x₀ _ a b
  -- the Gram–Schmidt normal
  set W : E := X t₀ with hW
  have hS₀ : (g.geodesicFlow p t₀).proj ∈ (chartAt H x₀).source := by
    rw [hγt₀]; exact mem_chart_source H x₀
  have hW1 : B t₀ W W = 1 := hBXX t₀ hS₀ ht₀
  have hW0 : B t₀ W (U t₀) = 0 := hBXU t₀ hS₀ ht₀
  set a : ℝ → ℝ := fun t => B t W (U t) with ha
  have hac : ContDiffAt ℝ r a t₀ := (hBc.clm_apply contDiffAt_const).clm_apply hUc
  set d : ℝ → ℝ := fun t => B t W W - a t ^ 2 with hd
  have hdc : ContDiffAt ℝ r d t₀ := ((hBc.clm_apply contDiffAt_const).clm_apply
    contDiffAt_const).sub (hac.pow 2)
  have hd₀ : d t₀ = 1 := by simp only [hd, ha, hW1, hW0]; norm_num
  set N : ℝ → E := fun t => (Real.sqrt (d t))⁻¹ • (W - a t • U t) with hN
  have hNc : ContDiffAt ℝ r N t₀ := by
    have hs : ContDiffAt ℝ r (fun t => Real.sqrt (d t)) t₀ := hdc.sqrt (by rw [hd₀]; norm_num)
    have hs0 : Real.sqrt (d t₀) ≠ 0 := by rw [hd₀]; norm_num
    exact (hs.inv hs0).smul (contDiffAt_const.sub (hac.smul hUc))
  have hN₀ : N t₀ = W := by
    simp only [hN, hd₀, Real.sqrt_one, inv_one, one_smul, ha, hW0, zero_smul, sub_zero]
  have hdpos : ∀ᶠ t in 𝓝 t₀, 0 < d t :=
    continuousAt_const.eventually_lt hdc.continuousAt (by rw [hd₀]; norm_num)
  have hNorth : ∀ t, (g.geodesicFlow p t).proj ∈ (chartAt H x₀).source → 0 < d t →
      B t (N t) (U t) = 0 ∧ B t (N t) (N t) = 1 := by
    intro t ht hdt
    have hUU := hBUU t ht
    have hUW : B t (U t) W = a t := hBsymm t _ _
    have hsq := Real.sq_sqrt hdt.le
    have hsp := Real.sqrt_pos.mpr hdt
    constructor
    · simp only [hN, map_smul, map_sub, smul_apply,
        sub_apply, smul_eq_mul, hUU]
      simp only [ha]
      ring
    · simp only [hN, map_smul, map_sub, smul_apply,
        sub_apply, smul_eq_mul, hUU, hUW]
      simp only [ha] at hUW ⊢
      have : B t W W - a t ^ 2 = Real.sqrt (d t) ^ 2 := by rw [hsq]
      field_simp
      simp only [hd] at hsq
      nlinarith [hsq]
  -- the sign is locally constant
  have hVc : ContinuousAt V t₀ := hcont.continuousAt (hJ.mem_nhds ht₀)
  have hVsrc : V t₀ ∈ (chartAt (ModelProd H E) q₀).source := by
    rw [TangentBundle.mem_chart_source_iff]; exact hS₀
  have hXc : ContinuousAt X t₀ :=
    continuousAt_snd.comp ((continuousAt_extChartAt' (by rw [extChartAt_source]; exact hVsrc)).comp hVc)
  set c : ℝ → ℝ := fun t => B t (X t) (N t) with hc
  have hcc : ContinuousAt c t₀ :=
    (hBc.continuousAt.clm_apply hXc).clm_apply hNc.continuousAt
  have hc₀ : c t₀ = 1 := by simp only [hc, hN₀]; exact hW1
  have hcpos : ∀ᶠ t in 𝓝 t₀, 0 < c t :=
    continuousAt_const.eventually_lt hcc (by rw [hc₀]; norm_num)
  have hXN : ∀ᶠ t in 𝓝 t₀, X t = N t := by
    filter_upwards [hS, hJn, hdpos, hcpos] with t ht htJ hdt hct
    obtain ⟨hNU, hNN⟩ := hNorth t ht hdt
    have hrep := eq_smul_of_orthonormal_dim_two hdim (hBsymm t) (hBUU t ht) hNN hNU
      (hBXU t ht htJ)
    have hXX := hBXX t ht htJ
    rw [hrep] at hXX
    simp only [map_smul, smul_apply, smul_eq_mul, hNN, mul_one] at hXX
    have hc1 : c t = 1 := by
      have h2 : c t * c t = 1 := by simpa [hc] using hXX
      nlinarith
    rw [hrep]
    change c t • N t = N t
    rw [hc1, one_smul]
  -- conclusion
  have hVeq : V =ᶠ[𝓝 t₀] fun t => ψ.symm (Y t, N t) := by
    filter_upwards [hS, hXN] with t ht hxt
    have hsrc : V t ∈ ψ.source := by
      rw [hψ, extChartAt_source, TangentBundle.mem_chart_source_iff]; exact ht
    have hpair : ψ (V t) = (Y t, N t) := Prod.ext (hV1 t) hxt
    rw [← hpair, ψ.left_inv hsrc]
  have htarget : (Y t₀, N t₀) ∈ ψ.target := by
    have h := ψ.map_source (show V t₀ ∈ ψ.source by rw [hψ, extChartAt_source]; exact hVsrc)
    have hpair₀ : ψ (V t₀) = (Y t₀, N t₀) := Prod.ext (hV1 t₀) (by rw [hN₀])
    rw [hpair₀] at h
    exact h
  have hsymm_sm := (contMDiffOn_extChartAt_symm (I := I.tangent) (n := ∞) q₀).contMDiffAt
    ((isOpen_extChartAt_target q₀).mem_nhds htarget)
  have hpairc : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E × E) r (fun t => (Y t, N t)) t₀ :=
    (hYc.prodMk hNc).contMDiffAt
  exact ((hsymm_sm.of_le (by exact_mod_cast le_top)).comp t₀ hpairc).congr_of_eventuallyEq hVeq

end DifferentialGeometry.Geometry.FiniteSoul
