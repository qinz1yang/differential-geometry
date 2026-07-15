import DifferentialGeometry.Geometry.Metric.Basic
import DifferentialGeometry.Geometry.Metric.ChartGram
import DifferentialGeometry.Geometry.Operator.Hessian
import DifferentialGeometry.Geometry.Operator.HessianTrace
import DifferentialGeometry.Geometry.Operator.Gradient
import DifferentialGeometry.Geometry.Connection.LeviCivita.LeviCivitaChartLocal
import DifferentialGeometry.Geometry.Connection.LeviCivita.LeviCivitaChartSmooth
import DifferentialGeometry.Geometry.Flow.RicciFlow.DeTurckRHS
import DifferentialGeometry.Geometry.Flow.VectorField
import DifferentialGeometry.Geometry.Flow.DeTurckVFChartCoord
import DifferentialGeometry.Analysis.Parabolic.DeTurckLinearization.ChartVectorField
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.LieMatrixChartBridge
import DifferentialGeometry.Analysis.Integration.Measure.Invariance
import DifferentialGeometry.Geometry.Curvature.Riemann.Defs
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.ChartDeTurckRemainderPolynomial
import Mathlib.Analysis.Calculus.TangentCone.Prod
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-! # Chart-regularity conjuncts of the DeTurck short-time bundle from a single joint datum

The headline `deturck_ricci_flow_parabolic_short_time_existence`
(`Geometry/Flow/RicciFlow/ShortTime/DeTurckInitialDataExistence.lean`) bundles, besides
the existence of a parabolic DeTurck–Ricci solution, six regularity conjuncts about the
solution family `g_DT : ℝ → SmoothRiemannianMetric I M` and the horizon `T`:

* `C2`/`C3` — the DeTurck vector field `(t, x) ↦ deTurckVF (g_DT t) g_bg x` is jointly
  `C∞` as a tangent-bundle section on `Ioo 0 T ×ˢ univ` / `Icc 0 T ×ˢ univ`;
* `C4` — joint `C∞` of the chart-Gram entries on `Ioo 0 T ×ˢ baseSet`;
* `C5` — joint `C⁰` of the chart-Gram entries on `Ico 0 T ×ˢ baseSet`;
* `C6` — joint `C⁰` of the Euclidean-pulled-back Gram entry `chartGramOnE` on
  `Icc 0 T ×ˢ source`;
* `C7` — joint `C⁰` of the `k ≤ 2` spatial iterated Fréchet derivatives of `chartGramOnE`
  on `Icc 0 T ×ˢ chartLeviCivitaGoodSet`.

This file derives the whole conjunction abstractly from a **single** consumer-minimal
joint-smoothness datum: joint `C∞` (up to `t = 0`) of the chart-Gram matrix entries
`(t, x) ↦ chartGramMatrix (g_DT t) α x i j` on `Icc 0 T ×ˢ (baseSet at α)`.  The family
`g_DT`/the time `T` are abstract inputs; no flow is constructed here.

`C4`, `C5`, `C6` are derived in full.  `C7` (the spatial iterated-derivative joint
continuity, a genuine Euclidean-analysis lift of the joint datum to partial spatial
jets) and `C2`/`C3` (the joint `C∞` of the DeTurck vector field, which is assembled from
the metric components and their first chart-coordinate derivatives via the
Christoffel/cometric chart formula) are isolated as named lemmas
`deTurckChartGramOnE_iteratedFDeriv_jointContinuousOn_of_jointChartGram` and
`deTurckVF_jointContMDiffOn_of_jointChartGram`, each with a precise true signature and
each taking exactly the same joint datum `hJ`.  Both are proved here in full: `C7` by
pulling the joint datum to a Euclidean joint `ContDiffOn` through the chart and taking the
jointly-continuous spatial iterated jet on the closed time slab; `C2`/`C3` by assembling
the chart-coordinate DeTurck components (inverse Gram by Cramer's rule, Christoffel symbols
by first chart-partials) jointly and patching the bundled section over the manifold. -/

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open scoped Manifold ContDiff NNReal ENNReal Topology BigOperators Pointwise
open DifferentialGeometry
open DifferentialGeometry.PDE
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.DeTurck
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
      [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-- **The single consumer-minimal joint datum.**

Joint `C∞` (up to `t = 0`) of the chart-Gram matrix entries of the family `g_DT` against
the fixed anchor chart at `α`, on the product of the closed time interval `Icc 0 T` with
the trivialization base set at `α`.  This is the weakest joint regularity the chart-Gram
conjuncts `C4`–`C7` (and, through the Christoffel/cometric chart formula, the DeTurck
vector field conjuncts `C2`/`C3`) jointly consume.

It uses only the fixed anchor chart `α` and its model frame, so it is free of any
locally-constant-chart hypothesis (T1-safe). -/
def JointChartGramSmooth (T : ℝ) (g_DT : ℝ → SmoothRiemannianMetric I M) : Prop :=
  ∀ (α : M) (i j : Fin (Module.finrank ℝ E)),
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
      (fun p : ℝ × M =>
        Integral.Measure.chartGramMatrix (I := I) (g_DT p.1) α p.2 i j)
      (Set.Icc 0 T ×ˢ (trivializationAt E (TangentSpace I) α).baseSet)

/-- **Manifold-joint to Euclidean-joint chart bridge.**

A family of scalar functions `F : ℝ → M → ℝ` that is jointly `C∞` in `(t, x)` on
`Icc 0 T ×ˢ baseSet_α` pulls back, through the inverse chart at `α`, to a Euclidean
function `(t, y) ↦ F t ((extChartAt I α).symm y)` that is jointly `C∞` in `(t, y)` on
`Icc 0 T ×ˢ interior (extChartAt I α).target`. -/
private theorem jointScalar_manifold_to_euclidean
    (F : ℝ → M → ℝ) (α : M) (T : ℝ)
    (h : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
      (fun p : ℝ × M => F p.1 p.2)
      (Set.Icc 0 T ×ˢ (trivializationAt E (TangentSpace I) α).baseSet)) :
    ContDiffOn ℝ ∞
      (fun q : ℝ × E => F q.1 ((extChartAt I α).symm q.2))
      (Set.Icc 0 T ×ˢ interior (extChartAt I α).target) := by
  have hsymm : ContMDiffOn 𝓘(ℝ, E) I ∞ (extChartAt I α).symm
      (interior (extChartAt I α).target) :=
    (contMDiffOn_extChartAt_symm α).mono interior_subset
  have hΨ : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) (𝓘(ℝ, ℝ).prod I) ∞
      (Prod.map (id : ℝ → ℝ) (extChartAt I α).symm)
      (Set.Icc 0 T ×ˢ interior (extChartAt I α).target) :=
    (contMDiffOn_id (I := 𝓘(ℝ, ℝ))).prodMap hsymm
  have hmapsTo : Set.MapsTo
      (Prod.map (id : ℝ → ℝ) (extChartAt I α).symm)
      (Set.Icc 0 T ×ˢ interior (extChartAt I α).target)
      (Set.Icc 0 T ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) := by
    rintro ⟨t, y⟩ ⟨ht, hy⟩
    refine ⟨ht, ?_⟩
    have hsource : (extChartAt I α).symm y ∈ (extChartAt I α).source :=
      (extChartAt I α).map_target (interior_subset hy)
    rw [extChartAt_source (I := I)] at hsource
    rw [Integral.Measure.trivializationAt_baseSet_eq_chartAt_source (I := I)]
    exact hsource
  have hcomp : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ) ∞
      ((fun p : ℝ × M => F p.1 p.2) ∘ Prod.map (id : ℝ → ℝ) (extChartAt I α).symm)
      (Set.Icc 0 T ×ˢ interior (extChartAt I α).target) :=
    h.comp hΨ hmapsTo
  have hfun : (fun p : ℝ × M => F p.1 p.2) ∘ Prod.map (id : ℝ → ℝ) (extChartAt I α).symm =
      fun q : ℝ × E => F q.1 ((extChartAt I α).symm q.2) := by
    funext q; simp [Prod.map]
  rw [hfun] at hcomp
  rw [← contMDiffOn_iff_contDiffOn, modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
  exact hcomp

/-- **Closed-slab joint spatial-jet continuity (Euclidean core).**

For a function `G : ℝ × E → ℝ` jointly `C∞` on the closed slab `Icc 0 T ×ˢ V` with `V`
open, the partial spatial order-`k` iterated Fréchet derivative of the time-slice,
evaluated at the moving point, is jointly continuous on `Icc 0 T ×ˢ V`.  The time
parameter `t` ranges over the *closed* interval; the derivative is taken spatially. -/
private theorem param_spatial_jet_continuity_closed
    (G : ℝ × E → ℝ) (T : ℝ) (V : Set E) (hV : IsOpen V)
    (hG : ContDiffOn ℝ ∞ G (Set.Icc 0 T ×ˢ V)) (k : ℕ) :
    ContinuousOn (fun q : ℝ × E => iteratedFDeriv ℝ k (fun y => G (q.1, y)) q.2)
      (Set.Icc 0 T ×ˢ V) := by
  classical
  have hspatial_within_eq_joint :
      ∀ (t : ℝ), t ∈ Set.Icc 0 T → 0 < T → ∀ (y : E), y ∈ V →
        iteratedFDerivWithin ℝ k (fun y' => G (t, y')) V y =
        (iteratedFDerivWithin ℝ k G (Set.Icc 0 T ×ˢ V) (t, y)).compContinuousLinearMap
          (fun _ => ContinuousLinearMap.inr ℝ ℝ E) := by
    intro t ht hT y hy
    set c : ℝ × E := (t, 0) with hc
    set S : Set (ℝ × E) := (fun w => w + c) ⁻¹' (Set.Icc 0 T ×ˢ V) with hS
    have hS_eq : S = Set.Icc (-t) (T - t) ×ˢ V := by
      ext ⟨s, z⟩
      simp only [S, Set.mem_preimage, Set.mem_prod, Set.mem_Icc, c, Prod.mk_add_mk, add_zero]
      exact ⟨fun ⟨⟨h1, h2⟩, hv⟩ => ⟨⟨by linarith, by linarith⟩, hv⟩,
             fun ⟨⟨h1, h2⟩, hv⟩ => ⟨⟨by linarith, by linarith⟩, hv⟩⟩
    have hG' : ContDiffOn ℝ ∞ (fun w : ℝ × E => G (w + c)) S :=
      hG.comp (contDiff_id.add contDiff_const).contDiffOn (fun _ hw => hw)
    have hUD_S : UniqueDiffOn ℝ S := by
      rw [hS_eq]
      exact UniqueDiffOn.prod (uniqueDiffOn_Icc (by linarith [ht.1, ht.2])) hV.uniqueDiffOn
    have hpre_V : (ContinuousLinearMap.inr ℝ ℝ E) ⁻¹' S = V := by
      rw [hS_eq]; ext y'
      simp only [Set.mem_preimage, ContinuousLinearMap.inr_apply, Set.mem_prod, Set.mem_Icc]
      exact ⟨fun ⟨_, hv⟩ => hv, fun hv => ⟨⟨by linarith [ht.1], by linarith [ht.2]⟩, hv⟩⟩
    have hUD_V : UniqueDiffOn ℝ ((ContinuousLinearMap.inr ℝ ℝ E) ⁻¹' S) := by
      rw [hpre_V]; exact hV.uniqueDiffOn
    have hinr_y : (ContinuousLinearMap.inr ℝ ℝ E) y ∈ S := by
      change (ContinuousLinearMap.inr ℝ ℝ E y) + c ∈ Set.Icc 0 T ×ˢ V
      simp only [ContinuousLinearMap.inr_apply, c, Prod.mk_add_mk, zero_add, add_zero]
      exact ⟨ht, hy⟩
    have h_vadd : c +ᵥ S = Set.Icc 0 T ×ˢ V := by
      ext p; rw [Set.mem_vadd_set]
      exact ⟨fun ⟨w, hw, hcw⟩ => by rw [show p = c + w from hcw.symm, add_comm]; exact hw,
             fun hp => ⟨p - c, by
                        change p - c + c ∈ Set.Icc 0 T ×ˢ V; rw [sub_add_cancel]; exact hp,
                        by change c + (p - c) = p; abel⟩⟩
    conv_lhs => rw [show (fun y' => G (t, y')) = (fun w : ℝ × E => G (w + c)) ∘
        (ContinuousLinearMap.inr ℝ ℝ E) from by
          ext y'; simp [c, ContinuousLinearMap.inr_apply]]
    rw [show V = (ContinuousLinearMap.inr ℝ ℝ E) ⁻¹' S from hpre_V.symm,
      ContinuousLinearMap.iteratedFDerivWithin_comp_right (ContinuousLinearMap.inr ℝ ℝ E)
        hG' hUD_S hUD_V hinr_y (by exact_mod_cast le_top)]
    congr 1
    simp only [ContinuousLinearMap.inr_apply]
    rw [iteratedFDerivWithin_comp_add_right k c (0, y), h_vadd, hpre_V]
    congr 1; simp [c, Prod.mk_add_mk]
  rcases lt_trichotomy T 0 with hT | rfl | hT_pos
  · have hempty : Set.Icc (0 : ℝ) T = ∅ := Set.Icc_eq_empty (not_le.mpr hT)
    rw [hempty, Set.empty_prod]; exact continuousOn_empty _
  · have hslice : ContDiffOn ℝ ∞ (fun y => G (0, y)) V :=
      hG.comp (contDiff_prodMk_right 0).contDiffOn
        (fun y hy => ⟨Set.left_mem_Icc.mpr (le_refl 0), hy⟩)
    have h_cts : ContinuousOn (iteratedFDerivWithin ℝ k (fun y => G (0, y)) V) V :=
      hslice.continuousOn_iteratedFDerivWithin (by exact_mod_cast le_top) hV.uniqueDiffOn
    apply ContinuousOn.congr (h_cts.comp continuousOn_snd (fun q hq => hq.2))
    rintro ⟨t, y⟩ hq
    have ht0 : t = 0 := le_antisymm hq.1.2 hq.1.1
    subst ht0
    exact (iteratedFDerivWithin_of_isOpen k hV hq.2).symm
  · have hUD : UniqueDiffOn ℝ (Set.Icc 0 T ×ˢ V) :=
      UniqueDiffOn.prod (uniqueDiffOn_Icc hT_pos) hV.uniqueDiffOn
    have h_joint_cts : ContinuousOn (iteratedFDerivWithin ℝ k G (Set.Icc 0 T ×ˢ V))
        (Set.Icc 0 T ×ˢ V) :=
      hG.continuousOn_iteratedFDerivWithin (by exact_mod_cast le_top) hUD
    set Φ : ContinuousMultilinearMap ℝ (fun _ : Fin k => ℝ × E) ℝ →L[ℝ]
            ContinuousMultilinearMap ℝ (fun _ : Fin k => E) ℝ :=
      ContinuousMultilinearMap.compContinuousLinearMapL
        (fun _ : Fin k => ContinuousLinearMap.inr ℝ ℝ E) with hΦ
    apply (Φ.continuous.comp_continuousOn h_joint_cts).congr
    rintro ⟨t, y⟩ hq
    obtain ⟨ht, hy⟩ := hq
    simp only [Function.comp, hΦ]
    rw [ContinuousMultilinearMap.compContinuousLinearMapL_apply,
        ← iteratedFDerivWithin_of_isOpen k hV hy]
    exact hspatial_within_eq_joint t ht hT_pos y hy

/-- **`C7` lift.**

From the joint chart-Gram smoothness datum, the `k ≤ 2` spatial iterated Fréchet
derivatives of the Euclidean-pulled-back Gram entry `chartGramOnE (g_DT t) α i j`,
evaluated along the chart at the moving point, are jointly continuous on
`Icc 0 T ×ˢ chartLeviCivitaGoodSet α`.

This is the genuine analytic content: a function jointly `C∞` in `(t, x)` has its partial
spatial order-`k` iterated Fréchet derivative `(t, x) ↦ iteratedFDeriv ℝ k (G t) x`
jointly continuous — the partial spatial jets of a jointly-smooth family vary continuously
in the parameter together with the base point.  The joint datum `hJ` is exactly its
hypothesis: it furnishes the Euclidean joint smoothness of the chart-pulled-back Gram
entry through `jointScalar_manifold_to_euclidean`, whence
`param_spatial_jet_continuity_closed` produces the spatial-jet continuity on the open
chart-target slab, which is finally precomposed with the smooth moving chart point. -/
theorem deTurckChartGramOnE_iteratedFDeriv_jointContinuousOn_of_jointChartGram
    (T : ℝ) (g_DT : ℝ → SmoothRiemannianMetric I M)
    (hJ : JointChartGramSmooth (I := I) T g_DT) :
    ∀ (α : M) (i j : Fin (Module.finrank ℝ E)) (k : ℕ), k ≤ 2 →
      ContinuousOn
        (fun q : ℝ × M => iteratedFDeriv ℝ k
          (Integral.DivergenceTheorem.chartGramOnE (I := I) (g_DT q.1) α i j)
          (extChartAt I α q.2))
        (Set.Icc 0 T ×ˢ chartLeviCivitaGoodSet (I := I) α) := by
  classical
  intro α i j k _hk
  set V : Set E := interior ((extChartAt I α).target : Set E) with hV_def
  have hVopen : IsOpen V := isOpen_interior
  set G : ℝ × E → ℝ :=
    fun q : ℝ × E =>
      Integral.Measure.chartGramMatrix (I := I) (g_DT q.1) α ((extChartAt I α).symm q.2) i j
    with hG_def
  have hG_smooth : ContDiffOn ℝ ∞ G (Set.Icc 0 T ×ˢ V) :=
    jointScalar_manifold_to_euclidean
      (fun t x => Integral.Measure.chartGramMatrix (I := I) (g_DT t) α x i j) α T (hJ α i j)
  have hjet :
      ContinuousOn (fun q : ℝ × E => iteratedFDeriv ℝ k (fun y => G (q.1, y)) q.2)
        (Set.Icc 0 T ×ˢ V) :=
    param_spatial_jet_continuity_closed G T V hVopen hG_smooth k
  have hslice_eq : ∀ t : ℝ, (fun y : E => G (t, y)) =
      Integral.DivergenceTheorem.chartGramOnE (I := I) (g_DT t) α i j := by
    intro t; funext y; rfl
  have hΨ_cont : ContinuousOn (fun q : ℝ × M => (q.1, extChartAt I α q.2))
      (Set.Icc 0 T ×ˢ chartLeviCivitaGoodSet (I := I) α) := by
    refine ContinuousOn.prodMk continuousOn_fst ?_
    refine (continuousOn_extChartAt α).comp continuousOn_snd ?_
    rintro ⟨t, x⟩ ⟨_, hx⟩
    exact chartLeviCivitaGoodSet_mem_extChartAt_source (I := I) hx
  have hΨ_maps : Set.MapsTo (fun q : ℝ × M => (q.1, extChartAt I α q.2))
      (Set.Icc 0 T ×ˢ chartLeviCivitaGoodSet (I := I) α)
      (Set.Icc 0 T ×ˢ V) := by
    rintro ⟨t, x⟩ ⟨ht, hx⟩
    exact ⟨ht, chartLeviCivitaGoodSet_extChartAt_mem_interior (I := I) hx⟩
  have hcomp := hjet.comp hΨ_cont hΨ_maps
  refine hcomp.congr ?_
  rintro ⟨t, x⟩ _
  simp only [Function.comp, hslice_eq]

/-- For `y ∈ interior (extChartAt I α).target`, the chart-inverse image lies in the
trivialization base set at `α`. -/
private lemma symm_of_interior_target_mem_baseSet (α : M) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    (extChartAt I α).symm y ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
  have hsource : (extChartAt I α).symm y ∈ (extChartAt I α).source :=
    (extChartAt I α).map_target (interior_subset hy)
  rw [extChartAt_source (I := I)] at hsource
  rw [Integral.Measure.trivializationAt_baseSet_eq_chartAt_source (I := I)]
  exact hsource

/-- The joint chart-Gram-entry datum, pulled back through the inverse chart at `α`, is
jointly `C∞` on the closed-time-slab over the interior of the chart target.  This is the
common Euclidean joint-smoothness input from which every chart-coordinate ingredient of the
DeTurck vector field inherits joint smoothness. -/
private lemma jointGramEntry_euclidean_contDiffOn
    (T : ℝ) (g_DT : ℝ → SmoothRiemannianMetric I M)
    (hJ : JointChartGramSmooth (I := I) T g_DT) (α : M)
    (l j : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (fun q : ℝ × E =>
      Integral.Measure.chartGramMatrix (I := I) (g_DT q.1) α ((extChartAt I α).symm q.2) l j)
      (Set.Icc 0 T ×ˢ interior (extChartAt I α).target) :=
  jointScalar_manifold_to_euclidean
    (fun t x => Integral.Measure.chartGramMatrix (I := I) (g_DT t) α x l j) α T (hJ α l j)

/-- `HasFDerivAt` of the constant-first-component embedding `y ↦ (t, y)`. -/
private lemma hasFDerivAt_prodMk_const_left (t : ℝ) (y : E) :
    HasFDerivAt (𝕜 := ℝ) (fun y' : E => (t, y'))
      (ContinuousLinearMap.inr ℝ ℝ E) y := by
  have heq : (fun y' : E => (t, y')) =
      fun y' => (ContinuousLinearMap.inr ℝ ℝ E y') + ((t, 0) : ℝ × E) := by
    ext y' <;> simp [ContinuousLinearMap.inr_apply]
  rw [heq]
  have h := (ContinuousLinearMap.inr ℝ ℝ E).hasFDerivAt (x := y) |>.add
    (hasFDerivAt_const ((t, 0) : ℝ × E) y)
  simp only [add_zero] at h
  exact h

/-- The spatial slice `fderivWithin` equals the joint `fderivWithin` postcomposed with the
inclusion of the spatial directions. -/
private lemma fderivWithin_spatial_slice_eq
    (G : ℝ × E → ℝ) (t : ℝ) (y : E)
    {V : Set E} (hVopen : IsOpen V) (hy : y ∈ V)
    {S : Set (ℝ × E)} (hmaps : ∀ y' ∈ V, (t, y') ∈ S)
    (hG : DifferentiableWithinAt ℝ G S (t, y)) (v : E) :
    fderivWithin ℝ (fun y' => G (t, y')) V y v =
      fderivWithin ℝ G S (t, y) (ContinuousLinearMap.inr ℝ ℝ E v) := by
  have hι_hfd := hasFDerivAt_prodMk_const_left (E := E) t y
  rw [show (fun y' => G (t, y')) = G ∘ (fun y' => (t, y')) from rfl]
  rw [fderivWithin_comp y hG hι_hfd.differentiableAt.differentiableWithinAt hmaps
      (hVopen.uniqueDiffOn y hy)]
  simp [hι_hfd.hasFDerivWithinAt.fderivWithin (hVopen.uniqueDiffOn y hy),
        ContinuousLinearMap.comp_apply]

private lemma infty_ne_zero_withTop : (∞ : WithTop ℕ∞) ≠ 0 :=
  WithTop.coe_ne_zero.mpr ENat.top_ne_zero

/-- Joint `C∞` of the chart-Gram determinant on the closed-time-slab. -/
private lemma jointGramDet_contDiffOn
    (T : ℝ) (g_DT : ℝ → SmoothRiemannianMetric I M)
    (hJ : JointChartGramSmooth (I := I) T g_DT) (α : M) :
    ContDiffOn ℝ ∞
      (fun q : ℝ × E =>
        (Integral.Measure.chartGramMatrix (I := I) (g_DT q.1) α
          ((extChartAt I α).symm q.2)).det)
      (Set.Icc 0 T ×ˢ interior (extChartAt I α).target) := by
  classical
  have hexp : (fun q : ℝ × E =>
        (Integral.Measure.chartGramMatrix (I := I) (g_DT q.1) α
          ((extChartAt I α).symm q.2)).det) =
      fun q => ∑ σ : Equiv.Perm (Fin (Module.finrank ℝ E)),
        (Equiv.Perm.sign σ : ℝ) *
          ∏ k, Integral.Measure.chartGramMatrix (I := I) (g_DT q.1) α
            ((extChartAt I α).symm q.2) (σ k) k := by
    funext q; rw [Matrix.det_apply]; simp [Units.smul_def]
  rw [hexp]
  exact ContDiffOn.sum (fun σ _ =>
    contDiffOn_const.mul
      (contDiffOn_prod (fun k _ => jointGramEntry_euclidean_contDiffOn T g_DT hJ α (σ k) k)))

/-- Joint `C∞` of a chart-Gram adjugate entry on the closed-time-slab. -/
private lemma jointGramAdjugate_contDiffOn
    (T : ℝ) (g_DT : ℝ → SmoothRiemannianMetric I M)
    (hJ : JointChartGramSmooth (I := I) T g_DT) (α : M)
    (a b : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (fun q : ℝ × E =>
        (Integral.Measure.chartGramMatrix (I := I) (g_DT q.1) α
          ((extChartAt I α).symm q.2)).adjugate a b)
      (Set.Icc 0 T ×ˢ interior (extChartAt I α).target) := by
  classical
  have hexp : (fun q : ℝ × E =>
        (Integral.Measure.chartGramMatrix (I := I) (g_DT q.1) α
          ((extChartAt I α).symm q.2)).adjugate a b) =
      fun q => ((Integral.Measure.chartGramMatrix (I := I) (g_DT q.1) α
          ((extChartAt I α).symm q.2)).updateRow b (Pi.single a (1 : ℝ))).det := by
    funext q; exact Matrix.adjugate_apply _ _ _
  rw [hexp]
  have hexp2 : (fun q : ℝ × E =>
      ((Integral.Measure.chartGramMatrix (I := I) (g_DT q.1) α
          ((extChartAt I α).symm q.2)).updateRow b (Pi.single a (1 : ℝ))).det) =
      fun q => ∑ σ : Equiv.Perm (Fin (Module.finrank ℝ E)),
        (Equiv.Perm.sign σ : ℝ) *
          ∏ k, (Integral.Measure.chartGramMatrix (I := I) (g_DT q.1) α
              ((extChartAt I α).symm q.2)).updateRow b (Pi.single a (1 : ℝ)) (σ k) k := by
    funext q; rw [Matrix.det_apply]; simp [Units.smul_def]
  rw [hexp2]
  refine ContDiffOn.sum (fun σ _ => contDiffOn_const.mul (contDiffOn_prod (fun k _ => ?_)))
  by_cases hσk : σ k = b
  · have heq : (fun q : ℝ × E =>
            (Integral.Measure.chartGramMatrix (I := I) (g_DT q.1) α
                ((extChartAt I α).symm q.2)).updateRow b
                (Pi.single a (1 : ℝ)) (σ k) k) =
          fun _ => (Pi.single (M := fun _ : Fin (Module.finrank ℝ E) => ℝ) a 1) k := by
        funext q; rw [hσk, Matrix.updateRow_self]
    rw [heq]; exact contDiffOn_const
  · have heq : (fun q : ℝ × E =>
            (Integral.Measure.chartGramMatrix (I := I) (g_DT q.1) α
                ((extChartAt I α).symm q.2)).updateRow b
                (Pi.single a (1 : ℝ)) (σ k) k) =
          fun q => Integral.Measure.chartGramMatrix (I := I) (g_DT q.1) α
            ((extChartAt I α).symm q.2) (σ k) k := by
        funext q; rw [Matrix.updateRow_ne hσk]
    rw [heq]; exact jointGramEntry_euclidean_contDiffOn T g_DT hJ α (σ k) k

/-- **Joint spatial partial derivative of a chart-Gram entry, Euclidean.**

The partial spatial derivative `(t, y) ↦ partialDeriv m (chartGramOnE (g_DT t) α l j) y`
inherits joint `C∞`-smoothness from the joint datum.  At `T < 0` the slab is empty; at
`T = 0` it is the single `t = 0` spatial slice; at `T > 0` the joint spatial Fréchet
derivative is itself jointly `C∞` and is evaluated in the fixed model-basis direction. -/
private lemma gramOnE_partialDeriv_joint_contDiffOn
    (T : ℝ) (g_DT : ℝ → SmoothRiemannianMetric I M)
    (hJ : JointChartGramSmooth (I := I) T g_DT) (α : M)
    (m l j : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (fun q : ℝ × E =>
      Integral.DivergenceTheorem.partialDeriv (E := E) m
        (Integral.DivergenceTheorem.chartGramOnE (I := I) (g_DT q.1) α l j) q.2)
      (Set.Icc 0 T ×ˢ interior (extChartAt I α).target) := by
  classical
  set V := interior ((extChartAt I α).target : Set E) with hV_def
  set S := Set.Icc (0 : ℝ) T ×ˢ V with hS_def
  set G : ℝ × E → ℝ :=
    fun q => Integral.Measure.chartGramMatrix (I := I) (g_DT q.1) α
      ((extChartAt I α).symm q.2) l j with hG_def
  have hGV : ContDiffOn ℝ ∞ G S := jointGramEntry_euclidean_contDiffOn T g_DT hJ α l j
  have hVopen : IsOpen V := isOpen_interior
  have hfun : ∀ t : ℝ, Integral.DivergenceTheorem.chartGramOnE (I := I) (g_DT t) α l j =
      fun y' => G (t, y') := fun t => by funext y'; simp [Integral.DivergenceTheorem.chartGramOnE,
        G]
  suffices h : ContDiffOn ℝ ∞
      (fun q : ℝ × E => fderiv ℝ (fun y' => G (q.1, y')) q.2 (chartModelBasis E m)) S from
    h.congr (fun ⟨t, y⟩ _ => by rw [Integral.DivergenceTheorem.partialDeriv, hfun t])
  rcases lt_trichotomy T 0 with hT | rfl | hT_pos
  · have hSempty : S = ∅ := by
      rw [hS_def, Set.Icc_eq_empty (not_le.mpr hT), Set.empty_prod]
    rw [hSempty]; exact contDiffOn_empty
  · have hslice0 : ContDiffOn ℝ ∞ (fun y => G (0, y)) V :=
      hGV.comp (contDiff_prodMk_right (0 : ℝ)).contDiffOn
        (fun y hy => Set.mk_mem_prod (Set.left_mem_Icc.mpr (le_refl 0)) hy)
    exact ((hslice0.fderiv_of_isOpen hVopen (by exact_mod_cast le_top)).clm_apply
        (contDiffOn_const (c := chartModelBasis E m))).comp
      contDiffOn_snd (fun q hq => hq.2) |>.congr
      (fun ⟨t, y⟩ ⟨ht, _⟩ => by
        have ht0 : t = 0 := le_antisymm ht.2 ht.1; subst ht0; rfl)
  · have hUD : UniqueDiffOn ℝ S :=
      UniqueDiffOn.prod (uniqueDiffOn_Icc hT_pos) hVopen.uniqueDiffOn
    exact ((hGV.fderivWithin hUD (by exact_mod_cast le_top)).clm_apply
        (contDiffOn_const (c := ContinuousLinearMap.inr ℝ ℝ E (chartModelBasis E m)))).congr
      (fun ⟨t, y⟩ ⟨ht, hy⟩ => by
        rw [← fderivWithin_of_isOpen (𝕜 := ℝ) hVopen hy]
        exact fderivWithin_spatial_slice_eq G t y hVopen hy
          (fun y' hy' => Set.mk_mem_prod ht hy')
          (hGV.differentiableOn infty_ne_zero_withTop (t, y) ⟨ht, hy⟩) _)

/-- **Joint inverse-Gram entry, Euclidean.**  Cramer's rule writes the inverse-Gram entry
as `det⁻¹ · adjugate`; both factors are jointly `C∞` (polynomial in the Gram entries) and
the determinant is nonzero on the slab by positive definiteness, so the entry is jointly
`C∞`. -/
private lemma invGramOnE_joint_contDiffOn
    (T : ℝ) (g_DT : ℝ → SmoothRiemannianMetric I M)
    (hJ : JointChartGramSmooth (I := I) T g_DT) (α : M)
    (a b : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (fun q : ℝ × E =>
      Integral.DivergenceTheorem.chartInvGramOnE (I := I) (g_DT q.1) α a b q.2)
      (Set.Icc 0 T ×ˢ interior (extChartAt I α).target) := by
  classical
  set V := interior ((extChartAt I α).target : Set E) with hV_def
  set S := Set.Icc (0 : ℝ) T ×ˢ V with hS_def
  have hcongr : ∀ q ∈ S,
      Integral.DivergenceTheorem.chartInvGramOnE (I := I) (g_DT q.1) α a b q.2 =
        ((Integral.Measure.chartGramMatrix (I := I) (g_DT q.1) α
            ((extChartAt I α).symm q.2)).det)⁻¹ *
          (Integral.Measure.chartGramMatrix (I := I) (g_DT q.1) α
            ((extChartAt I α).symm q.2)).adjugate a b := by
    rintro ⟨t, y⟩ ⟨_, hy⟩
    rw [Integral.DivergenceTheorem.chartInvGramOnE_def, chartInvGramMatrix]
    rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv]
  refine ContDiffOn.congr ?_ hcongr
  have hdet_smooth := jointGramDet_contDiffOn T g_DT hJ α
  have hdet_ne : ∀ q ∈ S, (Integral.Measure.chartGramMatrix (I := I) (g_DT q.1) α
      ((extChartAt I α).symm q.2)).det ≠ 0 := by
    rintro ⟨t, y⟩ ⟨_, hy⟩
    exact ne_of_gt (chartGramMatrix_det_pos (I := I) (g_DT t) α
      (symm_of_interior_target_mem_baseSet α hy))
  exact (hdet_smooth.inv hdet_ne).mul (jointGramAdjugate_contDiffOn T g_DT hJ α a b)

/-- **Joint chart-Christoffel symbol, Euclidean.**  Assembled from the joint inverse-Gram
entries and the joint spatial partials of the Gram entries through the chart-Christoffel
formula `Γ^k_{ij} = ½ ∑_l G^{kl}(∂_i G_{lj} + ∂_j G_{li} − ∂_l G_{ij})`. -/
private lemma jointChristoffel_contDiffOn
    (T : ℝ) (g_DT : ℝ → SmoothRiemannianMetric I M)
    (hJ : JointChartGramSmooth (I := I) T g_DT) (α : M)
    (i j k : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (fun q : ℝ × E => chartChristoffel (I := I) (g_DT q.1) α i j k q.2)
      (Set.Icc 0 T ×ˢ interior (extChartAt I α).target) := by
  classical
  have hexp : (fun q : ℝ × E => chartChristoffel (I := I) (g_DT q.1) α i j k q.2) =
      fun q : ℝ × E => (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
        Integral.DivergenceTheorem.chartInvGramOnE (I := I) (g_DT q.1) α k l q.2 *
          (Integral.DivergenceTheorem.partialDeriv (E := E) i
              (Integral.DivergenceTheorem.chartGramOnE (I := I) (g_DT q.1) α l j) q.2 +
           Integral.DivergenceTheorem.partialDeriv (E := E) j
              (Integral.DivergenceTheorem.chartGramOnE (I := I) (g_DT q.1) α l i) q.2 -
           Integral.DivergenceTheorem.partialDeriv (E := E) l
              (Integral.DivergenceTheorem.chartGramOnE (I := I) (g_DT q.1) α i j) q.2) := by
    funext q
    rw [chartChristoffel_def]
    simp only [Integral.DivergenceTheorem.chartInvGramOnE_def]
  rw [hexp]
  refine contDiffOn_const.mul (ContDiffOn.sum (fun l _ => ?_))
  refine (invGramOnE_joint_contDiffOn T g_DT hJ α k l).mul ?_
  refine ((gramOnE_partialDeriv_joint_contDiffOn T g_DT hJ α i l j).add
    (gramOnE_partialDeriv_joint_contDiffOn T g_DT hJ α j l i)).sub
    (gramOnE_partialDeriv_joint_contDiffOn T g_DT hJ α l i j)

/-- **Joint chart DeTurck-vector-field component, Euclidean.**  The chart component
`(t, y) ↦ chartDeTurckVFComp (g_DT t) g_bg α k y` is jointly `C∞` on the closed-time-slab:
the inverse-Gram factor and the Christoffel symbols of the evolving metric are jointly
`C∞` (from the joint datum), while the background-metric Christoffel symbols are `C∞` in
`y` (constant in `t`). -/
private lemma jointDeTurckVFComp_contDiffOn
    (g_bg : SmoothRiemannianMetric I M) (T : ℝ)
    (g_DT : ℝ → SmoothRiemannianMetric I M)
    (hJ : JointChartGramSmooth (I := I) T g_DT) (α : M)
    (k : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (fun q : ℝ × E =>
        DeTurckLinearization.chartDeTurckVFComp (I := I) (g_DT q.1) g_bg α k q.2)
      (Set.Icc 0 T ×ˢ interior (extChartAt I α).target) := by
  classical
  have hexp : (fun q : ℝ × E =>
        DeTurckLinearization.chartDeTurckVFComp (I := I) (g_DT q.1) g_bg α k q.2) =
      fun q : ℝ × E => ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        Integral.DivergenceTheorem.chartInvGramOnE (I := I) (g_DT q.1) α a b q.2 *
          (chartChristoffel (I := I) (g_DT q.1) α a b k q.2 -
            chartChristoffel (I := I) g_bg α a b k q.2) := by
    funext q
    rw [DeTurckLinearization.chartDeTurckVFComp_def]
  rw [hexp]
  refine ContDiffOn.sum (fun a _ => ContDiffOn.sum (fun b _ => ?_))
  refine (invGramOnE_joint_contDiffOn T g_DT hJ α a b).mul ?_
  refine (jointChristoffel_contDiffOn T g_DT hJ α a b k).sub ?_
  have hbg : ContDiffOn ℝ ∞ (chartChristoffel (I := I) g_bg α a b k)
      (interior (extChartAt I α).target) :=
    chartChristoffel_contDiffOn_interior (I := I) g_bg α a b k
  exact (hbg.comp contDiffOn_snd (fun q hq => hq.2))

/-- **Joint smoothness of the chart DeTurck-vector-field component along the moving chart
point.**  The scalar chart component `(t, x) ↦ chartDeTurckVFComp (g_DT t) g_bg α k
(extChartAt I α x)` is jointly `C∞` on the anchor's good set, obtained by composing the
joint-Euclidean chart component (a scalar function on `ℝ × E`) with the smooth moving
`(t, x) ↦ (t, extChartAt I α x)`.  The composition is carried out pointwise through the
single normed-space model `𝓘(ℝ, ℝ × E)` to avoid the product-model defeq blow-up. -/
private lemma jointDeTurckVFComp_alongChart_contMDiffOn
    (g_bg : SmoothRiemannianMetric I M) (T : ℝ)
    (g_DT : ℝ → SmoothRiemannianMetric I M)
    (hJ : JointChartGramSmooth (I := I) T g_DT) (α : M)
    (k : Fin (Module.finrank ℝ E)) {s : Set ℝ} (hs : s ⊆ Set.Icc 0 T) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
      (fun q : ℝ × M =>
        DeTurckLinearization.chartDeTurckVFComp (I := I) (g_DT q.1) g_bg α k
          (extChartAt I α q.2))
      (s ×ˢ chartLeviCivitaGoodSet (I := I) α) := by

  set G : ℝ × E → ℝ :=
    fun q : ℝ × E => DeTurckLinearization.chartDeTurckVFComp (I := I) (g_DT q.1) g_bg α k q.2
    with hG_def
  have hGEuclid : ContDiffOn ℝ ∞ G (Set.Icc 0 T ×ˢ interior (extChartAt I α).target) :=
    jointDeTurckVFComp_contDiffOn g_bg T g_DT hJ α k

  set f : ℝ × M → ℝ × E := fun q : ℝ × M => (q.1, extChartAt I α q.2) with hf_def
  have hf_smooth : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ × E) ∞ f
      (s ×ˢ chartLeviCivitaGoodSet (I := I) α) := by
    refine ContMDiffOn.prodMk_space contMDiffOn_fst ?_
    refine (contMDiffOn_extChartAt (I := I) (n := ∞) (x := α)).comp contMDiffOn_snd ?_
    rintro ⟨t, x⟩ ⟨_, hx⟩
    exact chartLeviCivitaGoodSet_mem_chartAt_source (I := I) hx
  have hmaps : Set.MapsTo f (s ×ˢ chartLeviCivitaGoodSet (I := I) α)
      (Set.Icc 0 T ×ˢ interior (extChartAt I α).target) := by
    rintro ⟨t, x⟩ ⟨ht, hx⟩
    exact ⟨hs ht, chartLeviCivitaGoodSet_extChartAt_mem_interior (I := I) hx⟩

  intro q hq
  have hGf : ContDiffWithinAt ℝ ∞ G (Set.Icc 0 T ×ˢ interior (extChartAt I α).target) (f q) :=
    hGEuclid.contDiffWithinAt (hmaps hq)
  exact hGf.comp_contMDiffWithinAt (hf_smooth q hq) hmaps

/-- **Per-anchor joint smoothness of the bundled DeTurck vector field.**  On the
chart-Levi-Civita good set of an anchor `α`, the bundled DeTurck vector field section is
jointly `C∞`, read through the trivialization at `α` as the joint-`C∞` chart-coordinate
components. -/
private lemma deTurckVF_jointContMDiffOn_goodSet
    (g_bg : SmoothRiemannianMetric I M) (T : ℝ)
    (g_DT : ℝ → SmoothRiemannianMetric I M)
    (hJ : JointChartGramSmooth (I := I) T g_DT) (α : M)
    {s : Set ℝ} (hs : s ⊆ Set.Icc 0 T) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (deTurckVF (I := I) (g_DT q.1) g_bg q.2)
        : TangentBundle I M))
      (s ×ˢ chartLeviCivitaGoodSet (I := I) α) := by
  classical
  set f : ℝ × M → TangentBundle I M :=
    fun q => (TotalSpace.mk' E q.2 (deTurckVF (I := I) (g_DT q.1) g_bg q.2)
      : TangentBundle I M) with hf
  have hmaps : Set.MapsTo f (s ×ˢ chartLeviCivitaGoodSet (I := I) α)
      (trivializationAt E (TangentSpace I) α).source := by
    rintro ⟨t, x⟩ ⟨_, hx⟩
    have hbase : x ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
      chartLeviCivitaGoodSet_mem_baseSet (I := I) hx
    rw [TangentBundle.trivializationAt_source]
    rwa [Integral.Measure.trivializationAt_baseSet_eq_chartAt_source (I := I)] at hbase
  rw [(trivializationAt E (TangentSpace I) α).contMDiffOn_iff
    (IM := 𝓘(ℝ, ℝ).prod I) (n := ∞) hmaps]
  refine ⟨?_, ?_⟩
  · -- projection q ↦ x is smooth
    refine contMDiffOn_snd.congr ?_
    rintro ⟨t, x⟩ _; rfl
  · -- the trivialization reading is the joint chart-coordinate model-basis sum
    have hread_eq : ∀ q ∈ s ×ˢ chartLeviCivitaGoodSet (I := I) α,
        ((trivializationAt E (TangentSpace I) α) (f q)).2 =
          ∑ k : Fin (Module.finrank ℝ E),
            DeTurckLinearization.chartDeTurckVFComp (I := I) (g_DT q.1) g_bg α k
                (extChartAt I α q.2) •
              ((chartModelBasis E) k : E) := by
      rintro ⟨t, x⟩ ⟨_, hx⟩
      have hrepr : ((trivializationAt E (TangentSpace I) α) (f (t, x))).2 =
          ∑ k : Fin (Module.finrank ℝ E),
            (chartModelBasis E).repr
                ((trivializationAt E (TangentSpace I) α) (f (t, x))).2 k •
              ((chartModelBasis E) k : E) :=
        (Module.Basis.sum_repr (chartModelBasis E)
          ((trivializationAt E (TangentSpace I) α) (f (t, x))).2).symm
      rw [hrepr]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      congr 1
      have hcoeff := chartCoeff_deTurckVF_eq_chartDeTurckVFComp (I := I) (g_DT t) g_bg α k hx
      rw [← hcoeff]
      rfl
    have hsummand : ∀ k : Fin (Module.finrank ℝ E),
        ContMDiffOn (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, E)) ∞
          (fun q : ℝ × M =>
            DeTurckLinearization.chartDeTurckVFComp (I := I) (g_DT q.1) g_bg α k
                (extChartAt I α q.2) •
              ((chartModelBasis E) k : E))
          (s ×ˢ chartLeviCivitaGoodSet (I := I) α) := by
      intro k
      refine ContMDiffOn.smul (V := E) ?_ contMDiffOn_const
      exact jointDeTurckVFComp_alongChart_contMDiffOn g_bg T g_DT hJ α k hs
    refine ContMDiffOn.congr ?_ hread_eq
    exact contMDiffOn_finset_sum (fun k _ => hsummand k)

/-- **`C2`/`C3` lift.**

From the joint chart-Gram smoothness datum, the bundled DeTurck vector field
`(t, x) ↦ deTurckVF (g_DT t) g_bg x`, viewed as a section of the tangent bundle, is
jointly `C∞` on `s ×ˢ Set.univ` for any time set `s ⊆ Icc 0 T`.

The DeTurck vector field is built in any chart from the metric components and their first
chart-coordinate derivatives through the Christoffel/cometric formula
`W^i = g^{jk}(Γ^i_{jk}(g) − Γ̄^i_{jk}(g_bg))`; each ingredient (the inverse Gram matrix
by Cramer's rule, the Christoffel symbols by first partials of the Gram entries) is joint-
`C∞` once the chart-Gram entries are, and the trace is a finite polynomial combination of
joint-`C∞` functions.  The conclusion is established locally on each anchor's good set by
`deTurckVF_jointContMDiffOn_goodSet` and patched globally.  Both the open `Ioo 0 T` and
closed `Icc 0 T` time-interval conjuncts are special cases (`s := Ioo 0 T`,
`s := Icc 0 T`). -/
theorem deTurckVF_jointContMDiffOn_of_jointChartGram
    (g_bg : SmoothRiemannianMetric I M) (T : ℝ) (g_DT : ℝ → SmoothRiemannianMetric I M)
    (hJ : JointChartGramSmooth (I := I) T g_DT)
    {s : Set ℝ} (hs : s ⊆ Set.Icc 0 T) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (deTurckVF (I := I) (g_DT q.1) g_bg q.2)
        : TangentBundle I M))
      (s ×ˢ Set.univ) := by
  refine contMDiffOn_of_locally_contMDiffOn ?_
  rintro ⟨t, x⟩ _
  refine ⟨Set.univ ×ˢ chartLeviCivitaGoodSet (I := I) x,
    isOpen_univ.prod (chartLeviCivitaGoodSet_isOpen (I := I) x),
    ⟨Set.mem_univ _, self_mem_chartLeviCivitaGoodSet (I := I) (α := x)⟩, ?_⟩
  have hset : (s ×ˢ (Set.univ : Set M)) ∩
      (Set.univ ×ˢ chartLeviCivitaGoodSet (I := I) x) =
      s ×ˢ chartLeviCivitaGoodSet (I := I) x := by
    ext ⟨u, y⟩
    simp only [Set.mem_inter_iff, Set.mem_prod, Set.mem_univ, true_and, and_true]
  rw [hset]
  exact deTurckVF_jointContMDiffOn_goodSet g_bg T g_DT hJ x hs

/-- **All six chart-regularity conjuncts of the DeTurck short-time bundle from the single
joint datum.**

For a background metric `g_bg`, a horizon `T`, and an abstract metric family `g_DT`, the
six regularity conjuncts `C2`–`C7` of `deturck_ricci_flow_parabolic_short_time_existence`
hold provided the single consumer-minimal joint chart-Gram smoothness datum
`hJ : JointChartGramSmooth T g_DT` holds.

`C4`, `C5`, `C6` are derived in full from `hJ`.  `C7` is supplied by
`deTurckChartGramOnE_iteratedFDeriv_jointContinuousOn_of_jointChartGram` and `C2`/`C3` by
`deTurckVF_jointContMDiffOn_of_jointChartGram`, both consuming the very same `hJ`. -/
theorem deTurckRicci_chartRegularity_of_jointChartGramSmooth
    (g_bg : SmoothRiemannianMetric I M) (T : ℝ) (g_DT : ℝ → SmoothRiemannianMetric I M)
    (hJ : JointChartGramSmooth (I := I) T g_DT) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
        (fun q : ℝ × M => (TotalSpace.mk' E q.2 (deTurckVF (I := I) (g_DT q.1) g_bg q.2)
          : TangentBundle I M))
        (Set.Ioo (0 : ℝ) T ×ˢ Set.univ) ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
        (fun q : ℝ × M => (TotalSpace.mk' E q.2 (deTurckVF (I := I) (g_DT q.1) g_bg q.2)
          : TangentBundle I M))
        (Set.Icc 0 T ×ˢ Set.univ) ∧
      (∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
        ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
          (fun p : ℝ × M =>
            Integral.Measure.chartGramMatrix (I := I) (g_DT p.1) x₀ p.2 i j)
          (Set.Ioo (0 : ℝ) T ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) ∧
      (∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
        ContinuousOn
          (fun p : ℝ × M =>
            Integral.Measure.chartGramMatrix (I := I) (g_DT p.1) x₀ p.2 i j)
          (Set.Ico (0 : ℝ) T ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) ∧
      (∀ (α : M) (i j : Fin (Module.finrank ℝ E)),
        ContinuousOn
          (fun q : ℝ × M =>
            Integral.DivergenceTheorem.chartGramOnE (I := I) (g_DT q.1) α i j
              (extChartAt I α q.2))
          (Set.Icc 0 T ×ˢ (chartAt H α).source)) ∧
      (∀ (α : M) (i j : Fin (Module.finrank ℝ E)) (k : ℕ), k ≤ 2 →
        ContinuousOn
          (fun q : ℝ × M => iteratedFDeriv ℝ k
            (Integral.DivergenceTheorem.chartGramOnE (I := I) (g_DT q.1) α i j)
            (extChartAt I α q.2))
          (Set.Icc 0 T ×ˢ chartLeviCivitaGoodSet (I := I) α)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- C2: deTurckVF joint C∞ on Ioo 0 T ×ˢ univ
    exact deTurckVF_jointContMDiffOn_of_jointChartGram (I := I) g_bg T g_DT hJ
      (Set.Ioo_subset_Icc_self)
  · -- C3: deTurckVF joint C∞ on Icc 0 T ×ˢ univ
    exact deTurckVF_jointContMDiffOn_of_jointChartGram (I := I) g_bg T g_DT hJ
      (subset_refl _)
  · -- C4: chartGram joint C∞ on Ioo 0 T ×ˢ baseSet, by restricting hJ from Icc to Ioo
    intro x₀ i j
    exact (hJ x₀ i j).mono
      (Set.prod_mono Set.Ioo_subset_Icc_self (subset_refl _))
  · -- C5: chartGram joint C⁰ on Ico 0 T ×ˢ baseSet, by restricting hJ and dropping to C⁰
    intro x₀ i j
    exact ((hJ x₀ i j).mono
      (Set.prod_mono Set.Ico_subset_Icc_self (subset_refl _))).continuousOn
  · -- C6: chartGramOnE ∘ extChartAt = chartGramMatrix on source, then hJ → C⁰
    intro α i j
    have hcont : ContinuousOn
        (fun p : ℝ × M =>
          Integral.Measure.chartGramMatrix (I := I) (g_DT p.1) α p.2 i j)
        (Set.Icc 0 T ×ˢ (chartAt H α).source) := by
      have hbase : (chartAt H α).source ⊆ (trivializationAt E (TangentSpace I) α).baseSet := by
        rw [trivializationAt_baseSet_eq_chartAt_source]
      exact (hJ α i j).continuousOn.mono (Set.prod_mono (subset_refl _) hbase)
    refine hcont.congr ?_
    intro q hq
    have hsrc : q.2 ∈ (chartAt H α).source := hq.2
    have hsrc' : q.2 ∈ (extChartAt I α).source := by
      rw [extChartAt_source]; exact hsrc
    change Integral.DivergenceTheorem.chartGramOnE (I := I) (g_DT q.1) α i j
          (extChartAt I α q.2)
        = Integral.Measure.chartGramMatrix (I := I) (g_DT q.1) α q.2 i j
    rw [chartGramOnE_def, (extChartAt I α).left_inv hsrc']
  · -- C7: supplied by the named Euclidean iterated-FDeriv lift
    exact deTurckChartGramOnE_iteratedFDeriv_jointContinuousOn_of_jointChartGram
      (I := I) T g_DT hJ

private lemma param_spatial_partialDeriv_contDiffOn
    (G : ℝ × E → ℝ) (T : ℝ) (V : Set E) (hVopen : IsOpen V)
    (hG : ContDiffOn ℝ ∞ G (Set.Icc 0 T ×ˢ V)) (m : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (fun q : ℝ × E => Integral.DivergenceTheorem.partialDeriv (E := E) m
        (fun y => G (q.1, y)) q.2)
      (Set.Icc 0 T ×ˢ V) := by
  classical
  set S := Set.Icc (0 : ℝ) T ×ˢ V with hS_def
  suffices h : ContDiffOn ℝ ∞
      (fun q : ℝ × E => fderiv ℝ (fun y' => G (q.1, y')) q.2 (chartModelBasis E m)) S from
    h.congr (fun ⟨t, y⟩ _ => by rw [Integral.DivergenceTheorem.partialDeriv])
  rcases lt_trichotomy T 0 with hT | rfl | hT_pos
  · have hSempty : S = ∅ := by
      rw [hS_def, Set.Icc_eq_empty (not_le.mpr hT), Set.empty_prod]
    rw [hSempty]; exact contDiffOn_empty
  · have hslice0 : ContDiffOn ℝ ∞ (fun y => G (0, y)) V :=
      hG.comp (contDiff_prodMk_right (0 : ℝ)).contDiffOn
        (fun y hy => Set.mk_mem_prod (Set.left_mem_Icc.mpr (le_refl 0)) hy)
    exact ((hslice0.fderiv_of_isOpen hVopen (by exact_mod_cast le_top)).clm_apply
        (contDiffOn_const (c := chartModelBasis E m))).comp
      contDiffOn_snd (fun q hq => hq.2) |>.congr
      (fun ⟨t, y⟩ ⟨ht, _⟩ => by
        have ht0 : t = 0 := le_antisymm ht.2 ht.1; subst ht0; rfl)
  · have hUD : UniqueDiffOn ℝ S :=
      UniqueDiffOn.prod (uniqueDiffOn_Icc hT_pos) hVopen.uniqueDiffOn
    exact ((hG.fderivWithin hUD (by exact_mod_cast le_top)).clm_apply
        (contDiffOn_const (c := ContinuousLinearMap.inr ℝ ℝ E (chartModelBasis E m)))).congr
      (fun ⟨t, y⟩ ⟨ht, hy⟩ => by
        rw [← fderivWithin_of_isOpen (𝕜 := ℝ) hVopen hy]
        exact fderivWithin_spatial_slice_eq G t y hVopen hy
          (fun y' hy' => Set.mk_mem_prod ht hy')
          (hG.differentiableOn infty_ne_zero_withTop (t, y) ⟨ht, hy⟩) _)

private lemma jointChartChristoffel_partialDeriv_contDiffOn
    (T : ℝ) (g_DT : ℝ → SmoothRiemannianMetric I M)
    (hJ : JointChartGramSmooth (I := I) T g_DT) (α : M)
    (m i j k : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (fun q : ℝ × E =>
      Integral.DivergenceTheorem.partialDeriv (E := E) m
        (chartChristoffel (I := I) (g_DT q.1) α i j k) q.2)
      (Set.Icc 0 T ×ˢ interior (extChartAt I α).target) := by
  have hbase := jointChristoffel_contDiffOn T g_DT hJ α i j k
  exact (param_spatial_partialDeriv_contDiffOn
    (fun q : ℝ × E => chartChristoffel (I := I) (g_DT q.1) α i j k q.2)
    T (interior (extChartAt I α).target) isOpen_interior hbase m).congr
    (fun ⟨t, y⟩ _ => rfl)

private lemma jointChartRiemann_contDiffOn
    (T : ℝ) (g_DT : ℝ → SmoothRiemannianMetric I M)
    (hJ : JointChartGramSmooth (I := I) T g_DT) (α : M)
    (i j k l : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (fun q : ℝ × E =>
        Integral.DivergenceTheorem.chartRiemannTensor (I := I) (g_DT q.1) α i j k l q.2)
      (Set.Icc 0 T ×ˢ interior (extChartAt I α).target) := by
  classical
  have hexp : (fun q : ℝ × E =>
        Integral.DivergenceTheorem.chartRiemannTensor (I := I) (g_DT q.1) α i j k l q.2) =
      fun q : ℝ × E =>
        Integral.DivergenceTheorem.partialDeriv (E := E) j
          (chartChristoffel (I := I) (g_DT q.1) α i k l) q.2 -
        Integral.DivergenceTheorem.partialDeriv (E := E) k
          (chartChristoffel (I := I) (g_DT q.1) α i j l) q.2 +
        (∑ m : Fin (Module.finrank ℝ E),
          (chartChristoffel (I := I) (g_DT q.1) α j m l q.2 *
              chartChristoffel (I := I) (g_DT q.1) α i k m q.2 -
            chartChristoffel (I := I) (g_DT q.1) α k m l q.2 *
              chartChristoffel (I := I) (g_DT q.1) α i j m q.2)) := by
    funext q; rw [Integral.DivergenceTheorem.chartRiemannTensor_def]
  rw [hexp]
  refine ((jointChartChristoffel_partialDeriv_contDiffOn T g_DT hJ α j i k l).sub
    (jointChartChristoffel_partialDeriv_contDiffOn T g_DT hJ α k i j l)).add ?_
  refine ContDiffOn.sum (fun m _ => ?_)
  exact ((jointChristoffel_contDiffOn T g_DT hJ α j m l).mul
      (jointChristoffel_contDiffOn T g_DT hJ α i k m)).sub
    ((jointChristoffel_contDiffOn T g_DT hJ α k m l).mul
      (jointChristoffel_contDiffOn T g_DT hJ α i j m))

private lemma jointChartRicci_contDiffOn
    (T : ℝ) (g_DT : ℝ → SmoothRiemannianMetric I M)
    (hJ : JointChartGramSmooth (I := I) T g_DT) (α : M)
    (i k : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (fun q : ℝ × E =>
        Integral.DivergenceTheorem.chartRicciTensor (I := I) (g_DT q.1) α i k q.2)
      (Set.Icc 0 T ×ˢ interior (extChartAt I α).target) := by
  classical
  have hexp : (fun q : ℝ × E =>
        Integral.DivergenceTheorem.chartRicciTensor (I := I) (g_DT q.1) α i k q.2) =
      fun q : ℝ × E => ∑ j : Fin (Module.finrank ℝ E),
        Integral.DivergenceTheorem.chartRiemannTensor (I := I) (g_DT q.1) α i j k j q.2 := by
    funext q; rw [Integral.DivergenceTheorem.chartRicciTensor_def]
  rw [hexp]
  exact ContDiffOn.sum (fun j _ => jointChartRiemann_contDiffOn T g_DT hJ α i j k j)

private lemma jointChartGramOnE_contDiffOn
    (T : ℝ) (g_DT : ℝ → SmoothRiemannianMetric I M)
    (hJ : JointChartGramSmooth (I := I) T g_DT) (α : M)
    (i j : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (fun q : ℝ × E =>
      Integral.DivergenceTheorem.chartGramOnE (I := I) (g_DT q.1) α i j q.2)
      (Set.Icc 0 T ×ˢ interior (extChartAt I α).target) :=
  (jointGramEntry_euclidean_contDiffOn T g_DT hJ α i j).congr
    (fun ⟨t, y⟩ _ => by rw [chartGramOnE_def])

private lemma jointChartDeTurckVFComp_partialDeriv_contDiffOn
    (g_bg : SmoothRiemannianMetric I M) (T : ℝ)
    (g_DT : ℝ → SmoothRiemannianMetric I M)
    (hJ : JointChartGramSmooth (I := I) T g_DT) (α : M)
    (m k : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (fun q : ℝ × E =>
      Integral.DivergenceTheorem.partialDeriv (E := E) m
        (DeTurckLinearization.chartDeTurckVFComp (I := I) (g_DT q.1) g_bg α k) q.2)
      (Set.Icc 0 T ×ˢ interior (extChartAt I α).target) := by
  have hbase := jointDeTurckVFComp_contDiffOn g_bg T g_DT hJ α k
  exact (param_spatial_partialDeriv_contDiffOn
    (fun q : ℝ × E => DeTurckLinearization.chartDeTurckVFComp (I := I) (g_DT q.1) g_bg α k q.2)
    T (interior (extChartAt I α).target) isOpen_interior hbase m).congr
    (fun ⟨t, y⟩ _ => rfl)

private lemma jointChartGramOnE_partialDeriv_contDiffOn
    (T : ℝ) (g_DT : ℝ → SmoothRiemannianMetric I M)
    (hJ : JointChartGramSmooth (I := I) T g_DT) (α : M)
    (m i j : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (fun q : ℝ × E =>
      Integral.DivergenceTheorem.partialDeriv (E := E) m
        (Integral.DivergenceTheorem.chartGramOnE (I := I) (g_DT q.1) α i j) q.2)
      (Set.Icc 0 T ×ˢ interior (extChartAt I α).target) :=
  gramOnE_partialDeriv_joint_contDiffOn T g_DT hJ α m i j

private lemma jointChartLieDeTurckComp_contDiffOn
    (g_bg : SmoothRiemannianMetric I M) (T : ℝ)
    (g_DT : ℝ → SmoothRiemannianMetric I M)
    (hJ : JointChartGramSmooth (I := I) T g_DT) (α : M)
    (i j : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (fun q : ℝ × E =>
        IntrinsicSpectral.DeTurckCoefficients.chartLieDeTurckComp (I := I) (g_DT q.1) g_bg α i j q.2)
      (Set.Icc 0 T ×ˢ interior (extChartAt I α).target) := by
  classical
  have hexp : (fun q : ℝ × E =>
        IntrinsicSpectral.DeTurckCoefficients.chartLieDeTurckComp
          (I := I) (g_DT q.1) g_bg α i j q.2) =
      fun q : ℝ × E =>
        (∑ k : Fin (Module.finrank ℝ E),
            DeTurckLinearization.chartDeTurckVFComp (I := I) (g_DT q.1) g_bg α k q.2 *
              Integral.DivergenceTheorem.partialDeriv (E := E) k
                (Integral.DivergenceTheorem.chartGramOnE (I := I) (g_DT q.1) α i j) q.2)
        + (∑ k : Fin (Module.finrank ℝ E),
            Integral.DivergenceTheorem.chartGramOnE (I := I) (g_DT q.1) α k j q.2 *
              Integral.DivergenceTheorem.partialDeriv (E := E) i
                (DeTurckLinearization.chartDeTurckVFComp (I := I) (g_DT q.1) g_bg α k) q.2)
        + (∑ k : Fin (Module.finrank ℝ E),
            Integral.DivergenceTheorem.chartGramOnE (I := I) (g_DT q.1) α i k q.2 *
              Integral.DivergenceTheorem.partialDeriv (E := E) j
                (DeTurckLinearization.chartDeTurckVFComp (I := I) (g_DT q.1) g_bg α k) q.2) := by
    funext q
    rw [IntrinsicSpectral.DeTurckCoefficients.chartLieDeTurckComp_def]
  rw [hexp]
  refine ((ContDiffOn.sum (fun k _ => ?_)).add (ContDiffOn.sum (fun k _ => ?_))).add
    (ContDiffOn.sum (fun k _ => ?_))
  · exact (jointDeTurckVFComp_contDiffOn g_bg T g_DT hJ α k).mul
      (jointChartGramOnE_partialDeriv_contDiffOn T g_DT hJ α k i j)
  · exact (jointChartGramOnE_contDiffOn T g_DT hJ α k j).mul
      (jointChartDeTurckVFComp_partialDeriv_contDiffOn g_bg T g_DT hJ α i k)
  · exact (jointChartGramOnE_contDiffOn T g_DT hJ α i k).mul
      (jointChartDeTurckVFComp_partialDeriv_contDiffOn g_bg T g_DT hJ α j k)

private lemma jointChartDeTurckRicciRHS_contDiffOn
    (g_bg : SmoothRiemannianMetric I M) (T : ℝ)
    (g_DT : ℝ → SmoothRiemannianMetric I M)
    (hJ : JointChartGramSmooth (I := I) T g_DT) (α : M)
    (i k : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (fun q : ℝ × E =>
        IntrinsicSpectral.DeTurckCoefficients.chartDeTurckRicciRHS
          (I := I) (g_DT q.1) g_bg α i k q.2)
      (Set.Icc 0 T ×ˢ interior (extChartAt I α).target) := by
  classical
  have hexp : (fun q : ℝ × E =>
        IntrinsicSpectral.DeTurckCoefficients.chartDeTurckRicciRHS
          (I := I) (g_DT q.1) g_bg α i k q.2) =
      fun q : ℝ × E =>
        -2 * Integral.DivergenceTheorem.chartRicciTensor (I := I) (g_DT q.1) α i k q.2 +
          IntrinsicSpectral.DeTurckCoefficients.chartLieDeTurckComp
            (I := I) (g_DT q.1) g_bg α i k q.2 := by
    funext q
    rw [IntrinsicSpectral.DeTurckCoefficients.chartDeTurckRicciRHS_def]
  rw [hexp]
  exact (contDiffOn_const.mul (jointChartRicci_contDiffOn T g_DT hJ α i k)).add
    (jointChartLieDeTurckComp_contDiffOn g_bg T g_DT hJ α i k)

theorem jointChartDeTurckRicciRHS_alongChart_contMDiffOn
    (g_bg : SmoothRiemannianMetric I M) (T : ℝ)
    (g_DT : ℝ → SmoothRiemannianMetric I M)
    (hJ : JointChartGramSmooth (I := I) T g_DT) (α : M)
    (i k : Fin (Module.finrank ℝ E)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
      (fun q : ℝ × M =>
        IntrinsicSpectral.DeTurckCoefficients.chartDeTurckRicciRHS (I := I) (g_DT q.1) g_bg α i k
          (extChartAt I α q.2))
      (Set.Icc 0 T ×ˢ chartLeviCivitaGoodSet (I := I) α) := by
  set G : ℝ × E → ℝ :=
    fun q : ℝ × E =>
      IntrinsicSpectral.DeTurckCoefficients.chartDeTurckRicciRHS (I := I) (g_DT q.1) g_bg α i k q.2
    with hG_def
  have hGEuclid : ContDiffOn ℝ ∞ G (Set.Icc 0 T ×ˢ interior (extChartAt I α).target) :=
    jointChartDeTurckRicciRHS_contDiffOn g_bg T g_DT hJ α i k
  set f : ℝ × M → ℝ × E := fun q : ℝ × M => (q.1, extChartAt I α q.2) with hf_def
  have hf_smooth : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ × E) ∞ f
      (Set.Icc 0 T ×ˢ chartLeviCivitaGoodSet (I := I) α) := by
    refine ContMDiffOn.prodMk_space contMDiffOn_fst ?_
    refine (contMDiffOn_extChartAt (I := I) (n := ∞) (x := α)).comp contMDiffOn_snd ?_
    rintro ⟨t, x⟩ ⟨_, hx⟩
    exact chartLeviCivitaGoodSet_mem_chartAt_source (I := I) hx
  have hmaps : Set.MapsTo f (Set.Icc 0 T ×ˢ chartLeviCivitaGoodSet (I := I) α)
      (Set.Icc 0 T ×ˢ interior (extChartAt I α).target) := by
    rintro ⟨t, x⟩ ⟨ht, hx⟩
    exact ⟨ht, chartLeviCivitaGoodSet_extChartAt_mem_interior (I := I) hx⟩
  intro q hq
  have hGf : ContDiffWithinAt ℝ ∞ G (Set.Icc 0 T ×ˢ interior (extChartAt I α).target) (f q) :=
    hGEuclid.contDiffWithinAt (hmaps hq)
  exact hGf.comp_contMDiffWithinAt (hf_smooth q hq) hmaps

end DifferentialGeometry.PDE.RicciFlow
