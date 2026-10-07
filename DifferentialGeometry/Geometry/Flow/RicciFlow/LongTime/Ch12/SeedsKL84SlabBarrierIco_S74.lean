import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedsKL84SlabBarrier_S74

/-!
# CH12-S74 G2 (b1'), slab barrier including the initial time

The scalar of an incoming slab flow is right-continuous at the initial time `a`
(`scalar_curvature_evolution` is a `HasDerivWithinAt` on the carrier `Ico a s`), so the open-slab
barrier of `incoming_scalar_backward_barrier_S74` extends to `Ico a s`; at `t = a` the value is the
scalar of the initial metric of the stage (needed to chain across the previous event).
-/

set_option autoImplicit false

noncomputable section

open Set Filter DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Geometry.Curvature
  DifferentialGeometry.Geometry.Operator DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff Topology

namespace GC.LongTime.Ch12

universe u

theorem scalar_continuousWithinAt_initial_S74 {P : OrientedThreeStage.{u}} {a s : ℝ}
    (G : P.IncomingSlab a s) (y : P.Carrier) :
    ContinuousWithinAt (fun v => G.flow.scalar v y) (Ico a s) a := by
  set φ := extChartAt ThreeModel y with hφ
  set W := interior φ.target with hWdef
  let F : ℝ × ThreeSpace → ℝ := fun z =>
    DifferentialGeometry.Tensor.Coordinates.scalarOnE (I := ThreeModel) y
      (metricScalarAt (G.flow.base.metric z.1)) z.2
  have hF : ContDiffOn ℝ ∞ F (Ico a s ×ˢ W) :=
    scalarOnE_contDiffOn_of_chartGramFamilySmoothWithinOn _ y
      (G.chartGramFamilySmoothWithinOn_Ico y)
  have hW : W = φ.target := (isOpen_extChartAt_target y).interior_eq
  have hya : (a, φ y) ∈ Ico a s ×ˢ W :=
    ⟨⟨le_rfl, G.lt⟩, by rw [hW]; exact mem_extChartAt_target y⟩
  have hfun : (fun v => G.flow.scalar v y) = fun v => F (v, φ y) := by
    funext v
    exact (DifferentialGeometry.Tensor.Coordinates.scalarOnE_extChartAt y _
      (mem_extChartAt_source y)).symm
  rw [hfun]
  have hpair : ContinuousWithinAt (fun v : ℝ => (v, φ y)) (Ico a s) a :=
    continuousWithinAt_id.prodMk continuousWithinAt_const
  have hmaps : MapsTo (fun v : ℝ => (v, φ y)) (Ico a s) (Ico a s ×ˢ W) :=
    fun v hv => ⟨hv, by rw [hW]; exact mem_extChartAt_target y⟩
  exact ContinuousWithinAt.comp (g := F) (f := fun v : ℝ => (v, φ y))
    (hF.continuousOn.continuousWithinAt hya) hpair hmaps

theorem scalar_continuousWithinAt_Ico_S74 {P : OrientedThreeStage.{u}} {a s : ℝ}
    (G : P.IncomingSlab a s) (y : P.Carrier) {c : ℝ} (hc : c ∈ Ico a s) :
    ContinuousWithinAt (fun v => G.flow.scalar v y) (Ico a s) c := by
  rcases hc.1.eq_or_lt with rfl | hlt
  · exact scalar_continuousWithinAt_initial_S74 G y
  · have hd := G.hasDerivAt_scalar_scalarEvolutionRate ⟨hlt, hc.2⟩ y
    exact hd.continuousAt.continuousWithinAt

theorem incoming_scalar_backward_barrier_Ico_S74 {P : OrientedThreeStage.{u}} {a s : ℝ}
    (G : P.IncomingSlab a s) (y : P.Carrier) {θ : ℝ → ℝ} {C : ℝ} (hC : 0 < C)
    (hP2 : ∀ t ∈ Ioo a s, θ t < G.flow.scalar t y →
      |derivWithin (fun v => G.flow.scalar v y) (Iic t) t| ≤ C * G.flow.scalar t y ^ 2)
    {M β σ0 L c : ℝ} (hac : a ≤ c) (hcs : c < s) (hβ : 0 < β) (hβM : β * M < 1) (hσ0 : 0 ≤ σ0)
    (hθ : ∀ t ∈ Ioo a s, θ t ≤ M) (hden : 0 < β - 2 * C * (σ0 + (s - c)))
    (hL : Tendsto (fun v => G.flow.scalar v y) (𝓝[<] s) (𝓝 L))
    (hLB : L ≤ (β - 2 * C * σ0)⁻¹) :
    ∀ t ∈ Ico c s, G.flow.scalar t y ≤ (β - 2 * C * (σ0 + (s - t)))⁻¹ := by
  intro t ht
  rcases ht.1.eq_or_lt with rfl | hlt
  · have hmem : Ico c s ∈ 𝓝[>] c :=
      mem_of_superset (Ioo_mem_nhdsGT hcs) Ioo_subset_Ico_self
    have hT : Tendsto (fun v => G.flow.scalar v y) (𝓝[>] c) (𝓝 (G.flow.scalar c y)) :=
      ((scalar_continuousWithinAt_Ico_S74 G y ⟨hac, hcs⟩).mono (Ico_subset_Ico_left hac)).tendsto.mono_left
        (nhdsWithin_le_of_mem hmem)
    have hψ : Tendsto (fun v => (β - 2 * C * (σ0 + (s - v)))⁻¹) (𝓝[>] c)
        (𝓝 ((β - 2 * C * (σ0 + (s - c)))⁻¹)) := by
      have : ContinuousAt (fun v : ℝ => (β - 2 * C * (σ0 + (s - v)))⁻¹) c :=
        ContinuousAt.inv₀ (by fun_prop) hden.ne'
      exact this.tendsto.mono_left nhdsWithin_le_nhds
    refine le_of_tendsto_of_tendsto hT hψ ?_
    filter_upwards [Ioo_mem_nhdsGT hcs] with v hv
    exact incoming_scalar_backward_barrier_S74 G y hC hP2 hac hβ hβM hσ0 hθ hden hL hLB v hv
  · exact incoming_scalar_backward_barrier_S74 G y hC hP2 hac hβ hβM hσ0 hθ hden hL hLB t ⟨hlt, ht.2⟩

end GC.LongTime.Ch12
