import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Topology.VectorBundle.Riemannian
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Normed.Module.FiniteDimension

noncomputable section

open Bundle Set Filter
open scoped Manifold ContDiff Topology NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [ProperSpace F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  [IsContinuousRiemannianBundle F V] [ContMDiffVectorBundle 1 F V I]
  {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

private theorem exists_local_fiberwise_lipschitzOnWith
    {A : P → ∀ x : M, V x → V x} {S : Set P}
    (hS : IsCompact S) (hSconvex : Convex ℝ S)
    (hA : ContMDiffOn (𝓘(ℝ, P).prod (I.prod 𝓘(ℝ, F))) (I.prod 𝓘(ℝ, F)) 1
      (fun q : P × TotalSpace F V =>
        (⟨q.2.proj, A q.1 q.2.proj q.2.2⟩ : TotalSpace F V)) (S ×ˢ univ))
    (R : ℝ) (x₀ : M) :
    ∃ U ∈ 𝓝 x₀, ∃ L : ℝ≥0, ∀ p ∈ S, ∀ x ∈ U,
      LipschitzOnWith L (A p x) (Metric.closedBall 0 R) := by
  let e := trivializationAt F V x₀
  let c := extChartAt I x₀
  have he₀ : x₀ ∈ e.baseSet := mem_baseSet_trivializationAt F V x₀
  obtain ⟨C₁, hC₁, hbound₁⟩ := eventually_norm_trivializationAt_lt F V x₀
  obtain ⟨C₂, hC₂, hbound₂⟩ := eventually_norm_symmL_trivializationAt_lt F V x₀
  have hbase : ∀ᶠ x in 𝓝 x₀, x ∈ e.baseSet ∧
      ‖e.continuousLinearMapAt ℝ x‖ < C₁ ∧ ‖e.symmL ℝ x‖ < C₂ :=
by
    filter_upwards [e.open_baseSet.mem_nhds he₀, hbound₁, hbound₂] with x hx hx₁ hx₂
    exact ⟨hx, hx₁, hx₂⟩
  have hcinv : ContMDiffAt 𝓘(ℝ, E) I 1 c.symm (c x₀) :=
    (contMDiffOn_extChartAt_symm x₀).contMDiffAt
      (mem_of_superset (isOpen_interior.mem_nhds
        (I.isInteriorPoint_iff.mp BoundarylessManifold.isInteriorPoint)) interior_subset)
  have hcinv₀ : c.symm (c x₀) = x₀ := c.left_inv (mem_extChartAt_source x₀)
  have hnear : ∀ᶠ y in 𝓝 (c x₀), y ∈ c.target ∧
      c.symm y ∈ e.baseSet ∧ ‖e.continuousLinearMapAt ℝ (c.symm y)‖ < C₁ ∧
        ‖e.symmL ℝ (c.symm y)‖ < C₂ := by
    have ht : c.target ∈ 𝓝 (c x₀) :=
      mem_of_superset (isOpen_interior.mem_nhds
        (I.isInteriorPoint_iff.mp BoundarylessManifold.isInteriorPoint)) interior_subset
    have hc : Tendsto c.symm (𝓝 (c x₀)) (𝓝 x₀) := by
      have h : Tendsto c.symm (𝓝 (c x₀)) (𝓝 (c.symm (c x₀))) := hcinv.continuousAt
      rwa [hcinv₀] at h
    filter_upwards [ht, hc.eventually hbase] with y hy hb
    exact ⟨hy, hb⟩
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp hnear
  let B := Metric.closedBall (c x₀) (ε / 2)
  have hB (y : E) (hy : y ∈ B) : y ∈ c.target ∧
      c.symm y ∈ e.baseSet ∧ ‖e.continuousLinearMapAt ℝ (c.symm y)‖ < C₁ ∧
        ‖e.symmL ℝ (c.symm y)‖ < C₂ := by
    apply hεsub
    exact (Metric.mem_closedBall.mp hy).trans_lt (by linarith)
  let D := S ×ˢ (B ×ˢ Metric.closedBall (0 : F) (C₁ * R))
  let ψ : P × (E × F) → F := fun q =>
    (e (let z := e.toOpenPartialHomeomorph.symm (c.symm q.2.1, q.2.2)
      (⟨z.proj, A q.1 z.proj z.2⟩ : TotalSpace F V))).2
  have hψ : ContDiffOn ℝ 1 ψ D := by
    have hb : ContMDiffOn (𝓘(ℝ, P).prod (𝓘(ℝ, E).prod 𝓘(ℝ, F))) I 1
        (fun q : P × (E × F) => c.symm q.2.1) D :=
      (contMDiffOn_extChartAt_symm x₀).comp
        (contMDiff_fst.comp contMDiff_snd).contMDiffOn
        (fun q hq => (hB q.2.1 hq.2.1).1)
    have hv : ContMDiffOn (𝓘(ℝ, P).prod (𝓘(ℝ, E).prod 𝓘(ℝ, F))) 𝓘(ℝ, F) 1
        (fun q : P × (E × F) => q.2.2) D :=
      (contMDiff_snd.comp contMDiff_snd).contMDiffOn
    have hin := e.contMDiffOn_symm.comp (hb.prodMk hv)
      (fun q hq => e.mem_target.mpr (hB q.2.1 hq.2.1).2.1)
    have ha := hA.comp (contMDiffOn_fst.prodMk hin) (fun q hq => ⟨hq.1, mem_univ _⟩)
    have hout := e.contMDiffOn.comp ha (fun q hq => by
      apply e.mem_source.mpr
      change (e.toOpenPartialHomeomorph.symm (c.symm q.2.1, q.2.2)).proj ∈ e.baseSet
      rw [e.proj_symm_apply' (hB q.2.1 hq.2.1).2.1]
      exact (hB q.2.1 hq.2.1).2.1)
    have hsnd : ContMDiffOn (𝓘(ℝ, P).prod (𝓘(ℝ, E).prod 𝓘(ℝ, F))) 𝓘(ℝ, F) 1 ψ D :=
      fun q hq => (hout q hq).snd
    rw [← contMDiffOn_iff_contDiffOn, modelWithCornersSelf_prod,
      ← chartedSpaceSelf_prod, modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact hsnd
  obtain ⟨L, hL⟩ := hψ.exists_lipschitzOnWith (by simp)
    (hSconvex.prod ((convex_closedBall _ _).prod (convex_closedBall _ _)))
    (hS.prod ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _)))
  let U := c.source ∩ c ⁻¹' Metric.ball (c x₀) (ε / 2)
  have hU : U ∈ 𝓝 x₀ :=
    inter_mem ((isOpen_extChartAt_source (I := I) x₀).mem_nhds (mem_extChartAt_source x₀))
      ((continuousAt_extChartAt (I := I) x₀)
        (Metric.ball_mem_nhds (c x₀) (half_pos hε)))
  let K : ℝ≥0 := ⟨C₂ * L * C₁, by positivity⟩
  refine ⟨U, hU, K, ?_⟩
  intro p hp x hx
  have hxB : c x ∈ B := Metric.mem_closedBall.mpr hx.2.le
  have hcx : c.symm (c x) = x := c.left_inv hx.1
  have hxprop := hB (c x) hxB
  rw [hcx] at hxprop
  have hcoords (z : V x) (hz : z ∈ Metric.closedBall 0 R) :
      e.continuousLinearMapAt ℝ x z ∈ Metric.closedBall (0 : F) (C₁ * R) := by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact ((e.continuousLinearMapAt ℝ x).le_opNorm z).trans
      ((mul_le_mul_of_nonneg_right hxprop.2.2.1.le (norm_nonneg _)).trans
        (mul_le_mul_of_nonneg_left (by simpa only [Metric.mem_closedBall, dist_zero_right] using hz)
          hC₁.le))
  have hψval (z : V x) : ψ (p, c x, e.continuousLinearMapAt ℝ x z) =
      e.continuousLinearMapAt ℝ x (A p x z) := by
    dsimp only [ψ]
    rw [hcx]
    rw [e.continuousLinearMapAt_apply_of_mem ℝ hxprop.2.1 z]
    have heq : (x, (e (⟨x, z⟩ : TotalSpace F V)).2) = e (⟨x, z⟩ : TotalSpace F V) :=
      Prod.ext (e.coe_fst (show (⟨x, z⟩ : TotalSpace F V) ∈ e.source from
        e.mem_source.mpr hxprop.2.1)).symm rfl
    have hinv : e.toOpenPartialHomeomorph.symm (e (⟨x, z⟩ : TotalSpace F V)) =
        (⟨x, z⟩ : TotalSpace F V) := e.left_inv (e.mem_source.mpr hxprop.2.1)
    rw [heq, hinv]
    exact (e.continuousLinearMapAt_apply_of_mem ℝ hxprop.2.1 _).symm
  apply LipschitzOnWith.of_dist_le_mul
  intro v hv w hw
  have hcoord := hL.norm_sub_le (show (p, c x, e.continuousLinearMapAt ℝ x v) ∈ D from
      ⟨hp, hxB, hcoords v hv⟩)
    (show (p, c x, e.continuousLinearMapAt ℝ x w) ∈ D from ⟨hp, hxB, hcoords w hw⟩)
  rw [hψval, hψval] at hcoord
  rw [← dist_eq_norm (p, c x, e.continuousLinearMapAt ℝ x v)
    (p, c x, e.continuousLinearMapAt ℝ x w)] at hcoord
  simp only [Prod.dist_eq, dist_self, max_eq_right dist_nonneg] at hcoord
  rw [dist_eq_norm, ← map_sub, ← map_sub] at hcoord
  change dist (A p x v) (A p x w) ≤ C₂ * ↑L * C₁ * dist v w
  rw [dist_eq_norm, dist_eq_norm]
  calc
    ‖A p x v - A p x w‖ =
        ‖e.symmL ℝ x (e.continuousLinearMapAt ℝ x (A p x v - A p x w))‖ := by
      rw [e.symmL_continuousLinearMapAt hxprop.2.1]
    _ ≤ C₂ * ‖e.continuousLinearMapAt ℝ x (A p x v - A p x w)‖ :=
      ((e.symmL ℝ x).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right hxprop.2.2.2.le (norm_nonneg _))
    _ ≤ C₂ * (L * ‖e.continuousLinearMapAt ℝ x (v - w)‖) :=
      mul_le_mul_of_nonneg_left hcoord hC₂.le
    _ ≤ C₂ * (L * (C₁ * ‖v - w‖)) := by
      gcongr
      exact ((e.continuousLinearMapAt ℝ x).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right hxprop.2.2.1.le (norm_nonneg _))
    _ = C₂ * ↑L * C₁ * ‖v - w‖ := by ring

theorem ContMDiffOn.exists_fiberwise_lipschitzOnWith
    {A : P → ∀ x : M, V x → V x} {S : Set P}
    (hA : ContMDiffOn (𝓘(ℝ, P).prod (I.prod 𝓘(ℝ, F))) (I.prod 𝓘(ℝ, F)) 1
      (fun q : P × TotalSpace F V =>
        (⟨q.2.proj, A q.1 q.2.proj q.2.2⟩ : TotalSpace F V)) (S ×ˢ univ))
    (hS : IsCompact S) (hSconvex : Convex ℝ S) {C : Set M} (hC : IsCompact C) (R : ℝ) :
    ∃ L : ℝ≥0, ∀ p ∈ S, ∀ x ∈ C,
      LipschitzOnWith L (A p x) (Metric.closedBall 0 R) := by
  classical
  choose U hU L hL using exists_local_fiberwise_lipschitzOnWith hS hSconvex hA R
  obtain ⟨s, _, hs⟩ := hC.elim_nhds_subcover U (fun x _ => hU x)
  refine ⟨∑ x ∈ s, L x, ?_⟩
  intro p hp x hx
  obtain ⟨y, hys, hxy⟩ := mem_iUnion₂.mp (hs hx)
  exact (hL y p hp x hxy).weaken
    (Finset.single_le_sum (fun z _ => (show 0 ≤ L z from zero_le)) hys)
