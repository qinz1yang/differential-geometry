import DifferentialGeometry.Geometry.Comparison.FiniteSoul.FiniteParallelChart
import DifferentialGeometry.Geometry.Comparison.FiniteSoul.TransverseShiftGauss

/-!
# A parallel field along a geodesic is `C^r` (lane CMS3-SHIFT, group G3)

* `contDiffOn_of_hasDerivAt_linear`: a solution of a linear ODE `f' = A f` with `C^n` coefficients on an
  open set is `C^n` there (bootstrap through `contDiffOn_succ_iff_deriv_of_isOpen`).
* `contMDiffAt_parallel_geodesicFlow`: for a `C^(r+1)` metric, a field `ξ` parallel along a complete
  geodesic `t ↦ π φ_t p` (`IsParallelAlongFinite … univ`) gives a `C^r` curve `t ↦ (γ t, ξ t)` in `TM`
  (the chart ODE `ξ' = −Γ(γ', ξ)` has `C^r` coefficients).
* `contMDiffAt_transverseFlow`: then `(t, h) ↦ φ_h(γ t, ξ t)` is `C^r` in `TM`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Filter Function
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.FiniteSoul

section Bootstrap

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Bootstrap for linear ODEs.** -/
theorem contDiffOn_of_hasDerivAt_linear {s : Set ℝ} (hs : IsOpen s) {A : ℝ → F →L[ℝ] F}
    {f : ℝ → F} {n : ℕ∞} (hA : ContDiffOn ℝ n A s) (hf : ∀ t ∈ s, HasDerivAt f (A t (f t)) t) :
    ContDiffOn ℝ n f s := by
  have key : ∀ k : ℕ, (k : ℕ∞) ≤ n → ContDiffOn ℝ k f s := by
    intro k
    induction k with
    | zero =>
      intro _
      exact contDiffOn_zero.mpr fun t ht => (hf t ht).continuousAt.continuousWithinAt
    | succ k ih =>
      intro hk
      have hk' : (k : ℕ∞) ≤ n := le_trans (by exact_mod_cast Nat.le_succ k) hk
      have hfk := ih hk'
      have hcast : ((k + 1 : ℕ) : WithTop ℕ∞) = (k : WithTop ℕ∞) + 1 := by push_cast; rfl
      rw [hcast, contDiffOn_succ_iff_deriv_of_isOpen hs]
      refine ⟨fun t ht => (hf t ht).differentiableAt.differentiableWithinAt,
        fun h => absurd h (by simp), ?_⟩
      have heq : EqOn (fun t => A t (f t)) (deriv f) s := fun t ht => (hf t ht).deriv.symm
      refine ContDiffOn.congr ?_ heq.symm
      exact (hA.of_le (by exact_mod_cast hk')).clm_apply hfk
  rcases eq_or_ne n ⊤ with hn | hn
  · subst hn
    exact contDiffOn_infty.mpr fun k => key k le_top
  · obtain ⟨k, rfl⟩ := WithTop.ne_top_iff_exists.mp hn
    exact key k le_rfl

end Bootstrap

section Parallel

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {r : ℕ∞}

local instance continuousDualEquiv_CMS3SHIFTr : DifferentialGeometry.ContinuousDualEquiv E :=
  IsCoercive.continuousDualEquivOfFiniteDimensional

local instance bilinNormedGroup_CMS3SHIFTr : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance bilinNormedSpace_CMS3SHIFTr : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

omit [T2Space M] in
/-- The chart Christoffel operator of a `C^(r+1)` metric is `C^r` on the chart target. -/
theorem contDiffOn_chartChristoffelFinite
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _)) (q : M) :
    ContDiffOn ℝ r (chartChristoffelFinite g q) (extChartAt I q).target := by
  have hb : ContDiffOn ℝ ((r : ℕ∞ω) + 1) (chartCoeffFinite g q) (extChartAt I q).target :=
    contDiffOn_chartCoeffFinite g le_rfl (by exact_mod_cast le_top) q
  have hD : ContDiffOn ℝ r (fun y => fderiv ℝ (chartCoeffFinite g q) y) (extChartAt I q).target :=
    hb.fderiv_of_isOpen (isOpen_extChartAt_target q) le_rfl
  exact MetricKoszul.raisedKoszulOp_contDiffOn (hb.of_le le_self_add) hD
    fun y hy => isCoercive_chartCoeffFinite g hy

/-- **A parallel field along a complete geodesic is `C^r`** as a curve in `TM`. -/
theorem contMDiffAt_parallel_geodesicFlow (hr : 1 ≤ r)
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    {p : TangentBundle I M} (hdom : ∀ t : ℝ, (p, t) ∈ g.geodesicFlowDomain) {ξ : ℝ → E}
    (hξ : IsParallelAlongFinite g (fun t => (g.geodesicFlow p t).proj) ξ univ) (t₀ : ℝ) :
    ContMDiffAt 𝓘(ℝ, ℝ) I.tangent r
      (fun t => (⟨(g.geodesicFlow p t).proj, ξ t⟩ : TangentBundle I M)) t₀ := by
  set Fl : ℝ → TangentBundle I M := fun t => g.geodesicFlow p t with hFl
  set V : ℝ → TangentBundle I M := fun t => ⟨(g.geodesicFlow p t).proj, ξ t⟩ with hV
  set x₀ := (g.geodesicFlow p t₀).proj with hx₀
  set ψ := extChartAt I.tangent (⟨x₀, 0⟩ : TangentBundle I M) with hψ
  have hFlc : ∀ t, ContMDiffAt 𝓘(ℝ, ℝ) I.tangent r Fl t := by
    intro t
    have hin : ContMDiff 𝓘(ℝ, ℝ) (I.tangent.prod 𝓘(ℝ, ℝ)) ∞ (fun s : ℝ => (p, s)) :=
      contMDiff_const.prodMk contMDiff_id
    exact ((g.contMDiffOn_geodesicFlow hr).contMDiffAt
      ((g.isOpen_geodesicFlowDomain hr).mem_nhds (hdom t))).comp t
      ((hin t).of_le (by exact_mod_cast le_top))
  have hγc : Continuous fun t => (g.geodesicFlow p t).proj :=
    (FiberBundle.continuous_proj E (TangentSpace I : M → Type _)).comp
      (continuous_iff_continuousAt.mpr fun t => (hFlc t).continuousAt)
  set s : Set ℝ := (fun t => (g.geodesicFlow p t).proj) ⁻¹' (chartAt H x₀).source with hs
  have hso : IsOpen s := (chartAt H x₀).open_source.preimage hγc
  have ht₀ : t₀ ∈ s := mem_chart_source H x₀
  have hsrc : ∀ t ∈ s, Fl t ∈ (chartAt (ModelProd H E) (⟨x₀, 0⟩ : TangentBundle I M)).source :=
    fun t ht => (TangentBundle.mem_chart_source_iff _ _).mpr ht
  have hsrcV : ∀ t ∈ s, V t ∈ (chartAt (ModelProd H E) (⟨x₀, 0⟩ : TangentBundle I M)).source :=
    fun t ht => (TangentBundle.mem_chart_source_iff _ _).mpr ht
  -- chart reading of the flow line
  have hψFl : ContDiffOn ℝ r (fun t => ψ (Fl t)) s := by
    intro t ht
    have h := (contMDiffAt_extChartAt' (I := I.tangent) (n := r) (hsrc t ht)).comp t (hFlc t)
    exact (contMDiffAt_iff_contDiffAt.mp h).contDiffWithinAt
  have hfst : ∀ t, (ψ (Fl t)).1 = extChartAt I x₀ (g.geodesicFlow p t).proj := fun t =>
    TangentBundle.extChartAt_tangent_apply_fst (⟨x₀, 0⟩ : TangentBundle I M)
  have hfstV : ∀ t, (ψ (V t)).1 = (ψ (Fl t)).1 := fun t => by
    rw [hfst t]
    exact TangentBundle.extChartAt_tangent_apply_fst (⟨x₀, 0⟩ : TangentBundle I M)
  have hmaps : ∀ t ∈ s, (ψ (Fl t)).1 ∈ (extChartAt I x₀).target := fun t ht => by
    rw [hfst t]
    exact (extChartAt I x₀).map_source (by rw [extChartAt_source]; exact ht)
  -- the coefficient of the chart ODE
  set A : ℝ → E →L[ℝ] E := fun t => -(chartChristoffelFinite g x₀ (ψ (Fl t)).1 (ψ (Fl t)).2)
    with hA
  have hAc : ContDiffOn ℝ r A s := by
    have h1 : ContDiffOn ℝ r (fun t => chartChristoffelFinite g x₀ (ψ (Fl t)).1) s :=
      (contDiffOn_chartChristoffelFinite g x₀).comp hψFl.fst hmaps
    exact (h1.clm_apply hψFl.snd).neg
  -- the chart representative of `ξ` solves the chart ODE
  have hode : ∀ t ∈ s, HasDerivAt (fun τ => (ψ (V τ)).2) (A t (ψ (V t)).2) t := by
    intro t ht
    have h := (isParallelAlongFinite_geodesicFlow_iff hr (fun τ _ => hdom τ)
      (fun τ _ => uniqueDiffWithinAt_univ)).mp hξ t (mem_univ t) x₀ ht
    rw [hasDerivWithinAt_univ] at h
    convert h using 1
    rw [hA]
    dsimp only
    rw [neg_apply, hfst t]
  have hXc : ContDiffOn ℝ r (fun τ => (ψ (V τ)).2) s := contDiffOn_of_hasDerivAt_linear hso hAc hode
  -- conclusion through the inverse chart
  have hVeq : V =ᶠ[𝓝 t₀] fun t => ψ.symm ((ψ (Fl t)).1, (ψ (V t)).2) := by
    filter_upwards [hso.mem_nhds ht₀] with t ht
    have hsrc' : V t ∈ ψ.source := by rw [hψ, extChartAt_source]; exact hsrcV t ht
    have hpair : ψ (V t) = ((ψ (Fl t)).1, (ψ (V t)).2) := Prod.ext (hfstV t) rfl
    rw [← hpair, ψ.left_inv hsrc']
  have htarget : ((ψ (Fl t₀)).1, (ψ (V t₀)).2) ∈ ψ.target := by
    have h := ψ.map_source (show V t₀ ∈ ψ.source by rw [hψ, extChartAt_source]; exact hsrcV t₀ ht₀)
    have hpair₀ : ψ (V t₀) = ((ψ (Fl t₀)).1, (ψ (V t₀)).2) := Prod.ext (hfstV t₀) rfl
    rw [hpair₀] at h
    exact h
  have hsymm_sm := (contMDiffOn_extChartAt_symm (I := I.tangent) (n := ∞)
    (⟨x₀, 0⟩ : TangentBundle I M)).contMDiffAt
    ((isOpen_extChartAt_target (⟨x₀, 0⟩ : TangentBundle I M)).mem_nhds htarget)
  have hpairc : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E × E) r
      (fun t => ((ψ (Fl t)).1, (ψ (V t)).2)) t₀ :=
    (((hψFl.fst).contDiffAt (hso.mem_nhds ht₀)).prodMk
      (hXc.contDiffAt (hso.mem_nhds ht₀))).contMDiffAt
  exact ((hsymm_sm.of_le (by exact_mod_cast le_top)).comp t₀ hpairc).congr_of_eventuallyEq hVeq

/-- The transverse flow `(t, h) ↦ φ_h(γ t, ξ t)` is `C^r` when `t ↦ (γ t, ξ t)` is. -/
theorem contMDiffAt_transverseFlow (hr : 1 ≤ r)
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hdom : g.geodesicFlowDomain = univ) (p : TangentBundle I M) {ξ : ℝ → E} {z : ℝ × ℝ}
    (hV : ContMDiffAt 𝓘(ℝ, ℝ) I.tangent r
      (fun t => (⟨(g.geodesicFlow p t).proj, ξ t⟩ : TangentBundle I M)) z.1) :
    ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I.tangent r
      (fun z : ℝ × ℝ => g.geodesicFlow (⟨(g.geodesicFlow p z.1).proj, ξ z.1⟩ : TangentBundle I M)
        z.2) z := by
  have hmem : ∀ q : TangentBundle I M × ℝ, q ∈ g.geodesicFlowDomain := fun q => by
    rw [hdom]; exact mem_univ q
  have h1 : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I.tangent r
      (fun z : ℝ × ℝ => (⟨(g.geodesicFlow p z.1).proj, ξ z.1⟩ : TangentBundle I M)) z :=
    ContMDiffAt.comp (x := z) (f := Prod.fst) hV (contDiff_fst.contMDiff.contMDiffAt)
  have hin : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) (I.tangent.prod 𝓘(ℝ, ℝ)) r
      (fun z : ℝ × ℝ => ((⟨(g.geodesicFlow p z.1).proj, ξ z.1⟩ : TangentBundle I M), z.2)) z :=
    h1.prodMk (contDiff_snd.contMDiff.contMDiffAt)
  exact ((g.contMDiffOn_geodesicFlow hr).contMDiffAt
    ((g.isOpen_geodesicFlowDomain hr).mem_nhds (hmem _))).comp z hin

end Parallel

end DifferentialGeometry.Geometry.FiniteSoul
