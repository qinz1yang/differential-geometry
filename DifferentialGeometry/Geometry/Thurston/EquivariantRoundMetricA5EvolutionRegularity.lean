import DifferentialGeometry.Geometry.Thurston.EquivariantRoundMetricA5EvolutionNorm
import DifferentialGeometry.Geometry.Metric.Family.ChartHeatRegularity
import DifferentialGeometry.Geometry.Operator.Laplacian.VossWeylFormula
import DifferentialGeometry.Geometry.Operator.Gradient.NormSquaredTime
import DifferentialGeometry.Geometry.Curvature.Bochner.Scalar.TensorFormula
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Scalar.JointRegularity
import DifferentialGeometry.Geometry.Metric.TensorInner.FiberMetric.Tensor0SMetricIneq

/-!
# Joint smoothness of the squared norm of the traceless Hessian

Chapter 7, packet P8, surface lemma U1, route (a), step a5.2 (potential gauge, design D18 (ii′)).

* `laplacian_family_contMDiffOn`: for a smooth metric family `g` and a function family `u` jointly
  smooth on `J × M` (`J` open, inside the regular times), `(t, x) ↦ Δ_{g(t)} u(t)(x)` is jointly
  smooth: in a chart it is the Voss–Weyl expression `ρ⁻¹ ∂ᵢ(ρ gⁱʲ ∂ⱼ u)`, whose ingredients are
  jointly smooth (`chartVossWeylIntegrand_contDiffOn_of_metricFamilySmoothOn`,
  `chartDensityOnE_contDiffOn`).
* `normSq0S_tracelessHessAt_eq`: in dimension two, with `M = ∇²f - ½ (Δf) g`,
  `|M|² = ½ Δ|∇f|² - (R / 2) |∇f|² - ⟨∇f, ∇Δf⟩ - (Δf)² / 2` (`|M|² = |∇²f|² - (Δf)² / 2` and the
  scalar Bochner formula `laplacian_gradient_norm_sq_eq`).
* `surfaceFlow_tracelessHess_normSq_contMDiffOn`: along the flow, with `Δf = R - 1 / (T* - t)`,
  `(t, x) ↦ |M(t, x)|²_{g(t)}` is jointly smooth on `(0, T) × M`: each term of the identity is
  (`gradSq_joint`, `scalar_joint`, `laplacian_family_contMDiffOn`; `⟨∇f, ∇R⟩` by polarization).
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Integral.Measure
open Bundle Filter Topology Set
open scoped Manifold ContDiff

namespace GC.Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem laplacian_family_contMDiffOn [SigmaCompactSpace M] {D : RealTimeInterval}
    {g : ℝ → SmoothRiemannianMetric I M} (hg : MetricFamilySmoothOn D g) {J : Set ℝ}
    (hJ : IsOpen J) (hJreg : J ⊆ D.regular) {u : ℝ → M → ℝ}
    (hu : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ (fun p : ℝ × M => u p.1 p.2) (J ×ˢ univ)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => laplacian (LeviCivita (g p.1)) (g p.1) (u p.1) p.2) (J ×ˢ univ) := by
  classical
  intro z hz
  set α := z.2 with hα
  have hus : ∀ s ∈ J, ContMDiff I 𝓘(ℝ, ℝ) ∞ (u s) := fun s hs q =>
    (hu.contMDiffAt ((hJ.prod isOpen_univ).mem_nhds ⟨hs, mem_univ q⟩)).curry_right
  have hy₀ : extChartAt I α α ∈ interior (extChartAt I α).target := by
    rw [(isOpen_extChartAt_target (I := I) α).interior_eq]
    exact mem_extChartAt_target α
  have hopen : IsOpen (J ×ˢ interior (extChartAt I α).target) := hJ.prod isOpen_interior
  have hint := fun i => chartVossWeylIntegrand_contDiffOn_of_metricFamilySmoothOn hg hJreg
    hJ.uniqueDiffOn hu α i
  have hdensOn := hg.chartDensityOnE_contDiffOn hJreg α
  have hpd : ∀ (i : Fin (Module.finrank ℝ E)),
      ContDiffAt ℝ ∞ (fun p : ℝ × E => partialDeriv (E := E) i
        (fun w : E => chartVossWeylIntegrand (I := I) (g p.1) α (u p.1) i w) p.2)
        (z.1, extChartAt I α α) := by
    intro i
    have hproj : ContDiffAt ℝ ∞ (fun q : (ℝ × E) × E => (q.1.1, q.2))
        ((z.1, extChartAt I α α), extChartAt I α α) :=
      contDiffAt_fst.fst.prodMk contDiffAt_snd
    have hi0 : ContDiffAt ℝ ∞
        (fun p : ℝ × E => chartVossWeylIntegrand (I := I) (g p.1) α (u p.1) i p.2)
        (z.1, extChartAt I α α) := (hint i).contDiffAt (hopen.mem_nhds ⟨hz.1, hy₀⟩)
    have hf'' : ContDiffAt ℝ ∞ (fun q : (ℝ × E) × E =>
        chartVossWeylIntegrand (I := I) (g q.1.1) α (u q.1.1) i q.2)
        ((z.1, extChartAt I α α), extChartAt I α α) :=
      ContDiffAt.comp (g := fun p : ℝ × E =>
        chartVossWeylIntegrand (I := I) (g p.1) α (u p.1) i p.2)
        (f := fun q : (ℝ × E) × E => (q.1.1, q.2)) _ hi0 hproj
    have hf' : ContDiffAt ℝ ∞ (Function.uncurry
        (fun (p : ℝ × E) => fun (w : E) => chartVossWeylIntegrand (I := I) (g p.1) α (u p.1) i w))
        ((z.1, extChartAt I α α), extChartAt I α α) := hf''
    have hfd := ContDiffAt.fderiv (m := ∞)
      (f := fun (p : ℝ × E) => fun (w : E) =>
        chartVossWeylIntegrand (I := I) (g p.1) α (u p.1) i w)
      (g := fun p : ℝ × E => p.2) hf' contDiffAt_snd (by simp)
    have hcomp :=
      (ContinuousLinearMap.apply ℝ ℝ (chartModelBasis E i)).contDiff.contDiffAt.comp _ hfd
    unfold partialDeriv
    exact hcomp.congr_of_eventuallyEq (Filter.Eventually.of_forall fun _ => rfl)
  have hbase : (extChartAt I α).symm (extChartAt I α α) ∈
      (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source,
      ← extChartAt_source_eq_chartAt_source (I := I)]
    exact (extChartAt I α).map_target (interior_subset hy₀)
  have hF : ContDiffAt ℝ ∞ (fun p : ℝ × E =>
      (∑ i : Fin (Module.finrank ℝ E),
        partialDeriv (E := E) i (chartVossWeylIntegrand (I := I) (g p.1) α (u p.1) i) p.2) /
        chartDensityOnE (I := I) (g p.1) α p.2) (z.1, extChartAt I α α) :=
    (ContDiffAt.sum fun i _ => hpd i).div (hdensOn.contDiffAt (hopen.mem_nhds ⟨hz.1, hy₀⟩))
      (ne_of_gt (chartDensity_pos (I := I) (g z.1) α hbase))
  have hc : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ × E) ∞
      (fun r : ℝ × M => (r.1, extChartAt I α r.2)) z :=
    contMDiffAt_fst.prodMk_space (contMDiffAt_extChartAt.comp z contMDiffAt_snd)
  apply (hF.contMDiffAt.comp z hc).contMDiffWithinAt.congr_of_eventuallyEq
  · filter_upwards [self_mem_nhdsWithin,
      (continuousAt_snd.eventually (extChartAt_source_mem_nhds (I := I) α)).filter_mono
        inf_le_left] with r hr hsrc
    have hsrc' : r.2 ∈ (chartAt H α).source := by
      rwa [extChartAt_source (I := I) α] at hsrc
    simp only [Function.comp_apply]
    rw [laplacian_levi_eq (g r.1) (hus r.1 hr.1) r.2,
      voss_weyl_laplacian_formula_pointwise (g r.1) α (hus r.1 hr.1) hsrc',
      chartVossWeylLaplacian_def, chartDensityOnE, (extChartAt I α).left_inv hsrc]
  · simp only [Function.comp_apply]
    rw [laplacian_levi_eq (g z.1) (hus z.1 hz.1) z.2,
      voss_weyl_laplacian_formula_pointwise (g z.1) α (hus z.1 hz.1) (mem_chart_source H α),
      chartVossWeylLaplacian_def, chartDensityOnE,
      (extChartAt I α).left_inv (mem_extChartAt_source α)]

theorem normSq0S_tracelessHessAt_eq [NeZero (Module.finrank ℝ E)] (hdim : Module.finrank ℝ E = 2)
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; ℝ⟯) (x : M) :
    normSq0S g x 2 (tracelessHessAt g f x) =
      laplacian (LeviCivita g) g
          (fun y => g.inner y (gradientFun g f y) (gradientFun g f y)) x / 2 -
        metricScalarAt g x / 2 * g.inner x (gradientFun g f x) (gradientFun g f x) -
        g.inner x (gradientFun g f x) (gradientFun g (ΔG g f) x) - (ΔG g f x) ^ 2 / 2 := by
  classical
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨b, hb⟩ := exists_orthonormal_basis g x
  have hinv := metricInverseInBasis_of_orthonormal g b hb
  set Hh := hessTensorAt g f x with hHh
  set Gm := metricTensor0S g x with hGm
  have hHs : Hh = hessianSec (metricCov g) (metricCov_smooth g) f f.contMDiff x := by
    refine tensor0SSpace_ext 2 x fun v => ?_
    have hv : v = vec2 (v 0) (v 1) := by funext i; fin_cases i <;> rfl
    rw [hv, hHh, hessTensorAt_apply, hessianSec_metricCov_eq_hessFun]
  have htr : inner0S g x 2 Gm Hh = ΔG g f x := by
    change metricTracePair0SAt g (hessTensorAt g f x) = _
    rw [← lap_eq_hess_on g isOpen_univ f.contMDiff.contMDiffOn (mem_univ x)]
    exact laplacian_levi_eq g f.contMDiff x
  have hGG : inner0S g x 2 Gm Gm = 2 := by
    change metricTracePair0SAt g (metricTensor0S g x) = 2
    rw [metricTracePair0SAt_eq_sum_basis g b _ hinv]
    rw [Finset.sum_congr rfl fun i _ => Finset.sum_eq_single i (fun j _ hji => by
      simp [identityInvMetric, diagonalInvMetric, Ne.symm hji]) (by simp)]
    simp only [identityInvMetric, diagonalInvMetric, ite_true, one_mul, metricTensor0S_apply]
    have e : ∀ i, g.inner x (vec2 (b i) (b i) 0) (vec2 (b i) (b i) 1) = 1 := by
      intro i; change g.inner x (b i) (b i) = 1; rw [hb]; simp
    simp only [e, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    have : Module.finrank ℝ (TangentSpace I x) = 2 := hdim
    rw [this]
    norm_num
  have hM : tracelessHessAt g f x = Hh - (ΔG g f x / 2) • Gm := rfl
  have hBoch := laplacian_gradient_norm_sq_eq g f.contMDiff x
  have hlapfun : (fun y => laplacian (metricCov g) g f y) = ΔG g f := by
    funext y; exact laplacian_levi_eq g f.contMDiff y
  rw [hlapfun, metricRicciAt_eq_half_metricScalarAt_smul_metric_of_finrank_eq_two g hdim,
    Tensor0SSpace.smul_apply, metricTensor0S_apply, ← hHs] at hBoch
  change laplacian (metricCov g) g _ x = _ at hBoch
  change _ = laplacian (metricCov g) g _ x / 2 - _ - _ - _
  rw [hBoch, hM]
  unfold normSq0S
  rw [inner0S_sub_left, inner0S_sub_right, inner0S_sub_right, inner0S_smul_left,
    inner0S_smul_right, inner0S_smul_left, inner0S_smul_right, inner0S_symm g x Hh Gm, htr, hGG]
  simp only [smul_eq_mul, vec2, ite_self]
  ring

omit [I.Boundaryless] [T2Space M] in
theorem gradientFun_add_of_mdifferentiableAt (g : SmoothRiemannianMetric I M) {u w : M → ℝ}
    {x : M} (hu : MDifferentiableAt I 𝓘(ℝ, ℝ) u x) (hw : MDifferentiableAt I 𝓘(ℝ, ℝ) w x) :
    gradientFun g (fun y => u y + w y) x = gradientFun g u x + gradientFun g w x := by
  apply SmoothRiemannianMetric.eq_of_inner_eq g
  intro v
  change g.inner x (gradFun g _ x) v = g.inner x (gradFun g u x + gradFun g w x) v
  rw [map_add, add_apply, inner_gradFun, inner_gradFun, inner_gradFun]
  change mvfderiv (I := I) (fun y => u y + w y) x v = mvfderiv (I := I) u x v +
    mvfderiv (I := I) w x v
  rw [mvfderiv_fun_add hu hw, add_apply]

omit [I.Boundaryless] [T2Space M] in
theorem gradientFun_sub_const (g : SmoothRiemannianMetric I M) {u : M → ℝ} (c : ℝ) {x : M}
    (hu : MDifferentiableAt I 𝓘(ℝ, ℝ) u x) :
    gradientFun g (fun y => u y - c) x = gradientFun g u x := by
  apply SmoothRiemannianMetric.eq_of_inner_eq g
  intro v
  change g.inner x (gradFun g _ x) v = g.inner x (gradFun g u x) v
  rw [inner_gradFun, inner_gradFun]
  change mvfderiv (I := I) (fun y => u y - c) x v = mvfderiv (I := I) u x v
  rw [mvfderiv_fun_sub hu mdifferentiableAt_const, mvfderiv_const, sub_zero]

theorem surfaceFlow_tracelessHess_normSq_contMDiffOn [NeZero (Module.finrank ℝ E)]
    [CompactSpace M] {T : ℝ} {hT : 0 < T} (hdim : Module.finrank ℝ E = 2)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 T hT)) (hS : IsSolutionOn S)
    (f : ℝ → C^∞⟮I, M; ℝ⟯)
    (hf : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ (fun q : ℝ × M => f q.1 q.2) (Ioo 0 T ×ˢ univ))
    {Tst : ℝ} (hTT : T ≤ Tst) (hfeq : ∀ t ∈ Ioo 0 T, ∀ x,
      ΔG (S.family.metric t) (f t) x = S.scalar t x - 1 / (Tst - t))
    (Mf : ℝ → Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2)
    (hM : ∀ t ∈ Ioo 0 T, ∀ x, Mf t x = tracelessHessAt (S.family.metric t) (f t) x) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun q : ℝ × M => normSq0S (S.family.metric q.1) q.2 2 (Mf q.1 q.2))
      (Ioo 0 T ×ˢ univ) := by
  set G := S.family.metric with hGdef
  have hmetric := MetricFamilySmoothOn.metricCLMSection_contMDiffOn
    (D := RealTimeInterval.closedOpen 0 T hT) hS.smoothMetric (J := Ioo 0 T) subset_rfl
  have hgram := fun (x₀ : M) (i j : Fin (Module.finrank ℝ E)) =>
    chartGramMatrix_joint_contMDiffOn G (Ioo 0 T) hmetric x₀ i j
  have hR : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ (fun q : ℝ × M => S.scalar q.1 q.2)
      (Ioo 0 T ×ˢ univ) := scalar_joint S hS
  have hW := gradSq_joint G isOpen_Ioo hgram (fun s y => f s y) hf
  have hΔW := laplacian_family_contMDiffOn hS.smoothMetric isOpen_Ioo subset_rfl
    (u := fun s y => (G s).inner y (gradientFun (G s) (fun z => f s z) y)
      (gradientFun (G s) (fun z => f s z) y)) hW
  have hPlus := gradSq_joint G isOpen_Ioo hgram (fun s y => f s y + S.scalar s y) (hf.add hR)
  have hMinus := gradSq_joint G isOpen_Ioo hgram (fun s y => f s y + (-1) * S.scalar s y)
    (hf.add (contMDiffOn_const.mul hR))
  have hr : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ (fun q : ℝ × M => (Tst - q.1)⁻¹)
      (Ioo 0 T ×ˢ univ) :=
    (contMDiffOn_const.sub contMDiffOn_fst).inv₀ fun q hq => by
      have : q.1 < Tst := hq.1.2.trans_le hTT
      exact (sub_pos.mpr this).ne'
  have hP2 : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun q : ℝ × M => (S.scalar q.1 q.2 - (Tst - q.1)⁻¹) ^ 2) (Ioo 0 T ×ˢ univ) :=
    (hR.sub hr).pow 2
  have hall := ((((hΔW.div_const 2).sub ((hR.mul hW).div_const 2)).sub
    ((hPlus.sub hMinus).div_const 4)).sub (hP2.div_const 2))
  refine hall.congr fun q hq => ?_
  obtain ⟨s, y⟩ := q
  have hs : s ∈ Ioo 0 T := hq.1
  have hfs : ContMDiff I 𝓘(ℝ, ℝ) ∞ (f s) := (f s).contMDiff
  have hRs : ContMDiff I 𝓘(ℝ, ℝ) ∞ (S.scalar s) := scalarSmoothOfSolution S s
  have hmf : MDifferentiableAt I 𝓘(ℝ, ℝ) (f s) y := (hfs y).mdifferentiableAt (by simp)
  have hmR : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun z => (-1) * S.scalar s z) y :=
    mdifferentiableAt_const.mul ((hRs y).mdifferentiableAt (by simp))
  have hmR' : MDifferentiableAt I 𝓘(ℝ, ℝ) (S.scalar s) y := (hRs y).mdifferentiableAt (by simp)
  have hΔfun : ΔG (G s) (f s) = fun z => S.scalar s z - 1 / (Tst - s) := by
    funext z; exact hfeq s hs z
  have hgradΔ : gradientFun (G s) (ΔG (G s) (f s)) y = gradientFun (G s) (S.scalar s) y := by
    rw [hΔfun, gradientFun_sub_const (G s) _ hmR']
  have hgp := gradientFun_add_of_mdifferentiableAt (G s) hmf hmR'
  have hgm := gradientFun_add_of_mdifferentiableAt (G s) hmf hmR
  have hneg : gradientFun (G s) (fun z => (-1) * S.scalar s z) y =
      (-1 : ℝ) • gradientFun (G s) (S.scalar s) y := by
    apply SmoothRiemannianMetric.eq_of_inner_eq (G s)
    intro v
    change (G s).inner y (gradFun (G s) _ y) v = (G s).inner y ((-1 : ℝ) • gradFun (G s) _ y) v
    rw [map_smul, smul_apply, inner_gradFun, inner_gradFun]
    change mvfderiv (I := I) (fun z => (-1) * S.scalar s z) y v = _
    rw [mvfderiv_const_mul I _ hmR']
    rfl
  simp only
  rw [hM s hs y, normSq0S_tracelessHessAt_eq hdim (G s) (f s) y, hgradΔ, hfeq s hs y]
  change _ = _ - _ - ((G s).inner y (gradientFun (G s) (fun z => f s z + S.scalar s z) y)
      (gradientFun (G s) (fun z => f s z + S.scalar s z) y) -
    (G s).inner y (gradientFun (G s) (fun z => f s z + (-1) * S.scalar s z) y)
      (gradientFun (G s) (fun z => f s z + (-1) * S.scalar s z) y)) / 4 - _
  rw [hgp, hgm, hneg]
  simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul]
  rw [(G s).symm y (gradientFun (G s) (S.scalar s) y) (gradientFun (G s) (f s) y)]
  have hRy : metricScalarAt (G s) y = S.scalar s y := rfl
  rw [hRy, one_div]
  simp only [Pi.mul_apply]
  ring

end GC.Geometry
