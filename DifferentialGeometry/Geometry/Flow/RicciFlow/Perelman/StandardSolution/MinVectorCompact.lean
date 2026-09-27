import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.InitialVectorBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.RegDomainLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.MinVector
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.LowerBound
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.FiniteDimension

set_option autoImplicit false

noncomputable section

open Bundle Filter Set
open DifferentialGeometry
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.PDE.RicciFlow

variable {E H M : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [PseudoMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
  {D : RealTimeInterval}

theorem isCompact_lMinVec_over_of_rm
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (K T : ℝ)
    (hg : RiemannianMetricComplete (I := I) (S.base.metric T))
    (x : M) (tau : ℝ) (htau : 0 < tau)
    (hreg : Icc (T - tau) T ⊆ D.regular)
    (hRm : ∀ t ∈ Icc (T - tau) T, ∀ y : M,
      normSq0S (I := I) (S.base.metric t) y 4
        (S.base.rm04 t y) ≤ K)
    {Cpt : Set M} (hCpt : IsCompact Cpt) (A : ℝ)
    (hact : ∀ Z : TangentSpace I x,
      (Z, tau) ∈ lMinDomain S T x →
      lExp S T x Z tau ∈ Cpt →
      lRegularizedAction S T (lRegularizedCurve S T x Z) 0 (Real.sqrt tau) ≤ A) :
    IsCompact {Z : TangentSpace I x |
      (Z, tau) ∈ lMinDomain S T x ∧ lExp S T x Z tau ∈ Cpt} := by
  classical
  let F : Set (TangentSpace I x) :=
    {Z | (Z, tau) ∈ lMinDomain S T x ∧ lExp S T x Z tau ∈ Cpt}
  let b : ℝ := Real.sqrt tau
  have hb : 0 < b := Real.sqrt_pos.mpr htau
  have hb2 : b ^ 2 = tau := Real.sq_sqrt htau.le
  have hregSq : Icc (T - b ^ 2) T ⊆ D.regular := by
    simpa only [hb2] using hreg
  have hRmSq : ∀ t ∈ Icc (T - b ^ 2) T, ∀ y : M,
      normSq0S (I := I) (S.base.metric t) y 4
        (S.base.rm04 t y) ≤ K := by
    simpa only [hb2] using hRm
  have hfamilyDom (W : TangentSpace I x) (hW : W ∈ F) :
      b ∈ lRegularizedDomain S T x W := by
    have hpos := ((mem_lMinDomain S T x W tau).1 hW.1).1
    exact ((mem_lExpPosDom S T x W tau).1 hpos).2.2
  have hfamilyAct (W : TangentSpace I x) (hW : W ∈ F) :
      lRegularizedAction S T (lRegularizedCurve S T x W) 0 b ≤ A :=
    hact W hW.1 hW.2
  have hbounded : Bornology.IsBounded F := by
    by_contra hnot
    have hlarge : ∀ n : ℕ, ∃ W : TangentSpace I x,
        W ∈ F ∧ (n : ℝ) < ‖W‖ := by
      intro n
      by_contra hn
      apply hnot
      refine isBounded_iff_forall_norm_le.mpr ⟨(n : ℝ), ?_⟩
      intro W hW
      exact le_of_not_gt (fun hlt ↦ hn ⟨W, hW, hlt⟩)
    choose Z hZF hNZ using hlarge
    have hseq : Bornology.IsBounded (range Z) :=
      lRegInit_bound_of_rm (I := I) S hS K T hg x b A hb
        hregSq hRmSq Z
        (fun n ↦ hfamilyDom (Z n) (hZF n))
        (fun n ↦ hfamilyAct (Z n) (hZF n))
    obtain ⟨R, hR⟩ := hseq.exists_norm_le
    obtain ⟨n, hn⟩ := exists_nat_gt R
    exact (not_lt_of_ge (hR (Z n) ⟨n, rfl⟩)) (hn.trans (hNZ n))
  have hclosed : IsClosed F := by
    rw [← isSeqClosed_iff_isClosed]
    intro Z Z₀ hZF hZ
    have hdom₀ : b ∈ lRegularizedDomain S T x Z₀ :=
      lRegDomain_lim_of_rm (I := I) S hS K T hg x b A hb
        hregSq hRmSq
        (fun n ↦ hfamilyDom (Z n) (hZF n))
        (fun n ↦ hfamilyAct (Z n) (hZF n)) hZ
    have hpos₀ : (Z₀, tau) ∈ lExpPosDom S T x :=
      (mem_lExpPosDom S T x Z₀ tau).2 ⟨htau, htau.le, hdom₀⟩
    have hmin₀ : (Z₀, tau) ∈ lMinDomain S T x := by
      apply lMinVec_lim_of_bdd (I := I) S hS T x
        (fun n ↦ (hZF n).1) hZ hpos₀
      intro y
      exact lRegularizedCosts_bdd_rm (I := I) S hS K T 0 b le_rfl hb.le
        hregSq hRmSq x y
    have hExpAt : ContinuousAt
        (fun p : E × ℝ ↦ lExp S T x p.1 p.2) (Z₀, tau) :=
      ((lExp_smoothOn S hS T x) (Z₀, tau) hpos₀).continuousWithinAt.continuousAt
        ((lExpPosDom_open S hS T x).mem_nhds hpos₀)
    have hExpLim : Tendsto (fun n ↦ lExp S T x (Z n) tau) atTop
        (𝓝 (lExp S T x Z₀ tau)) :=
      hExpAt.tendsto.comp (hZ.prodMk_nhds tendsto_const_nhds)
    exact ⟨hmin₀, hCpt.isClosed.mem_of_tendsto hExpLim
      (Eventually.of_forall fun n ↦ (hZF n).2)⟩
  exact Metric.isCompact_iff_isClosed_bounded.mpr ⟨hclosed, hbounded⟩

end DifferentialGeometry.PDE.RicciFlow

end

noncomputable section
open Bundle Filter Set
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.PDE.RicciFlow
variable {E H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [PseudoMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] {D : RealTimeInterval}
theorem isCompact_lMinVec_over_of_compact_range
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (T : ℝ) (x : M) {tau : ℝ} (htau : 0 < tau)
    (hreg : Icc (T - tau) T ⊆ D.regular)
    (Q : Set M) (hQ : IsCompact Q) {Y : Set M} (hY : IsClosed Y) (A : ℝ)
    (hbdd : ∀ y : M, BddBelow {r : ℝ | ∃ γ : ℝ → M,
      ContMDiff 𝓘(ℝ, ℝ) I 1 γ ∧ γ 0 = x ∧ γ (Real.sqrt tau) = y ∧
        lRegularizedAction S T γ 0 (Real.sqrt tau) = r})
    (hact : ∀ Z : TangentSpace I x, (Z, tau) ∈ lMinDomain S T x → lExp S T x Z tau ∈ Y →
      lRegularizedAction S T (lRegularizedCurve S T x Z) 0 (Real.sqrt tau) ≤ A)
    (hrange : ∀ Z : TangentSpace I x, (Z, tau) ∈ lMinDomain S T x → lExp S T x Z tau ∈ Y →
      MapsTo (lRegularizedCurve S T x Z) (Icc 0 (Real.sqrt tau)) Q) :
    IsCompact {Z : TangentSpace I x | (Z, tau) ∈ lMinDomain S T x ∧ lExp S T x Z tau ∈ Y} := by
  classical
  let F : Set (TangentSpace I x) := {Z | (Z, tau) ∈ lMinDomain S T x ∧ lExp S T x Z tau ∈ Y}
  let b := Real.sqrt tau
  have hb : 0 < b := Real.sqrt_pos.mpr htau
  have hb2 : b ^ 2 = tau := Real.sq_sqrt htau.le
  have hregSq : Icc (T - b ^ 2) T ⊆ D.regular := by simpa only [hb2] using hreg
  have hfamilyDom (W : TangentSpace I x) (hW : W ∈ F) : b ∈ lRegularizedDomain S T x W :=
    ((mem_lExpPosDom S T x W tau).mp (((mem_lMinDomain S T x W tau).mp hW.1).1)).2.2
  have hbounded : Bornology.IsBounded F := by
    let Z : F → TangentSpace I x := Subtype.val
    have hbnd := lRegInit_bound_of_compact_range S hS T x b A hb hregSq hQ Z
      (fun z => hfamilyDom z z.property) (fun z => hact z z.property.1 z.property.2)
      (fun z => image_subset_iff.mpr (hrange z z.property.1 z.property.2))
    simpa only [Z, Subtype.range_coe_subtype, ofPred_mem_eq] using hbnd
  have hclosed : IsClosed F := by
    rw [← isSeqClosed_iff_isClosed]
    intro Z Z₀ hZF hZ
    have hdom₀ : b ∈ lRegularizedDomain S T x Z₀ :=
      lRegDomain_lim_of_compact_range S hS T x b hb hregSq Q hQ
        (fun n => hrange (Z n) (hZF n).1 (hZF n).2) hZ
    have hpos₀ : (Z₀, tau) ∈ lExpPosDom S T x :=
      (mem_lExpPosDom S T x Z₀ tau).mpr ⟨htau, htau.le, hdom₀⟩
    have hmin₀ := lMinVec_lim_of_bdd S hS T x (fun n => (hZF n).1) hZ hpos₀ hbdd
    have hExpAt : ContinuousAt (fun p : E × ℝ => lExp S T x p.1 p.2) (Z₀, tau) :=
      ((lExp_smoothOn S hS T x) (Z₀, tau) hpos₀).continuousWithinAt.continuousAt
        ((lExpPosDom_open S hS T x).mem_nhds hpos₀)
    have hExpLim := hExpAt.tendsto.comp (hZ.prodMk_nhds tendsto_const_nhds)
    exact ⟨hmin₀, hY.mem_of_tendsto hExpLim (Filter.Eventually.of_forall fun n => (hZF n).2)⟩
  exact Metric.isCompact_iff_isClosed_bounded.mpr ⟨hclosed, hbounded⟩

end DifferentialGeometry.PDE.RicciFlow

end
