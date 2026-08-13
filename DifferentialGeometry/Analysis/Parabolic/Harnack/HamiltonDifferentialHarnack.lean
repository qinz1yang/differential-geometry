import DifferentialGeometry.Analysis.Parabolic.Harnack.LiYau
import DifferentialGeometry.Analysis.Parabolic.Harnack.LiYauHarnack

noncomputable section

open Set Filter Bundle Manifold MeasureTheory DifferentialGeometry
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Analysis.Parabolic.Energy
open DifferentialGeometry.Analysis.Calculus
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.DivergenceTheorem
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Analysis.Parabolic.Harnack

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private abbrev deltaLegacy
    (g : SmoothRiemannianMetric I M) {f : M → ℝ}
    (hf : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ f) : M → ℝ :=
  Δ_g (I := I) g ⟨f, hf⟩

omit [SigmaCompactSpace M] in
private theorem deltaLegacy_contMDiff
    (g : SmoothRiemannianMetric I M) {f : M → ℝ}
    (hf : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ f) :
    ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ (deltaLegacy (I := I) g hf) :=
  Δ_g_contMDiff (I := I) g ⟨f, hf⟩

omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem hasDerivAt_inner_self_of_hasDerivAt
    (g : SmoothRiemannianMetric I M) (x : M)
    {G : ℝ → TangentSpace I x} {G' : TangentSpace I x} {t : ℝ}
    (hG : HasDerivAt G G' t) :
    HasDerivAt (fun s => g.inner x (G s) (G s)) (2 * g.inner x G' (G t)) t := by
  have hB := ContinuousLinearMap.hasFDerivAt_of_bilinear
    (B := g.inner x) (f := G) (g := G) (x := t)
    hG.hasFDerivAt hG.hasFDerivAt
  let Gf : ℝ →L[ℝ] TangentSpace I x := ContinuousLinearMap.toSpanSingleton ℝ G'
  have hGf1 : Gf (1 : ℝ) = G' := by
    simp [Gf, ContinuousLinearMap.toSpanSingleton]
  have hder : HasDerivAt (fun s => g.inner x (G s) (G s))
      (((g.inner x).precompR ℝ (G t) Gf +
          (g.inner x).precompL ℝ Gf (G t)) (1 : ℝ)) t := by
    rw [hasDerivAt_iff_hasFDerivAt]
    have hB' : HasFDerivAt (fun s => g.inner x (G s) (G s))
        ((g.inner x).precompR ℝ (G t) Gf +
          (g.inner x).precompL ℝ Gf (G t)) t := by
      simpa [Gf] using hB
    have hL : ContinuousLinearMap.toSpanSingleton ℝ
          (((g.inner x).precompR ℝ (G t) Gf +
            (g.inner x).precompL ℝ Gf (G t)) (1 : ℝ)) =
        ((g.inner x).precompR ℝ (G t) Gf +
          (g.inner x).precompL ℝ Gf (G t)) :=
      ContinuousLinearMap.toSpanSingleton_apply_map_one (R₁ := ℝ)
        (c := ((g.inner x).precompR ℝ (G t) Gf +
          (g.inner x).precompL ℝ Gf (G t)))
    rwa [← hL] at hB'
  have hval : (((g.inner x).precompR ℝ (G t) Gf +
          (g.inner x).precompL ℝ Gf (G t)) (1 : ℝ)) =
      2 * g.inner x G' (G t) := by
    rw [ContinuousLinearMap.add_apply]
    have hr : ((g.inner x).precompR ℝ (G t) Gf) (1 : ℝ) =
        g.inner x (G t) (Gf (1 : ℝ)) := by
      rfl
    have hl : ((g.inner x).precompL ℝ Gf (G t)) (1 : ℝ) =
        g.inner x (Gf (1 : ℝ)) (G t) := by
      rfl
    rw [hr, hl, hGf1]
    rw [g.symm x (G t) G']
    ring
  rwa [hval] at hder

omit [T2Space M] [SigmaCompactSpace M] in
theorem normGradSq_timeDeriv_of_log_heat
    {D : RealTimeInterval}
    (g : SmoothRiemannianMetric I M)
    (u : ℝ → M → ℝ)
    (hu : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2) (D.regular ×ˢ univ))
    (hpos : ∀ t : ℝ, t ∈ D.carrier → ∀ x : M, 0 < u t x)
    {t : ℝ} (ht : t ∈ D.regular) (x : M) :
    HasDerivAt (fun s : ℝ =>
        g.inner x (gradientFun (I := I) g (fun y => Real.log (u s y)) x)
          (gradientFun (I := I) g (fun y => Real.log (u s y)) x))
      (2 * g.inner x
          (gradientFun (I := I) g (fun y => Real.log (u t y)) x)
            (gradientFun (I := I) g
            (fun y => deriv (fun σ : ℝ => Real.log (u σ y)) t) x)) t := by
  classical
  let f : ℝ → M → ℝ := fun s y => Real.log (u s y)
  have hlog' : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => f p.1 p.2) (D.regular ×ˢ univ) := by
    intro p hp
    have hnh : D.regular ×ˢ univ ∈ 𝓝 p :=
      (IsOpen.prod D.regular_isOpen isOpen_univ).mem_nhds ⟨hp.1, trivial⟩
    have hlogAt : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => Real.log (u p.1 p.2)) p :=
      (Real.contDiffAt_log.2 (hpos p.1 (D.regular_subset hp.1) p.2).ne').comp_contMDiffAt
        (x := p) (hu.contMDiffAt hnh)
    simpa [f] using hlogAt.contMDiffWithinAt
  have hgrad := gradientFun_time_deriv (I := I) (M := M) (D := D) g f hlog' ht (x := x)
  have hmain := hasDerivAt_inner_self_of_hasDerivAt g x
    (G := fun s => gradientFun (I := I) g (f s) x)
    (G' := gradientFun (I := I) g (fun y => deriv (fun σ : ℝ => f σ y) t) x) hgrad
  simpa [f, g.symm] using hmain

omit [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem gradientFun_add
    (g : SmoothRiemannianMetric I M) {f h : M → ℝ} (x : M)
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x) (hh : MDifferentiableAt I 𝓘(ℝ, ℝ) h x) :
    gradientFun (I := I) g (f + h) x = gradientFun (I := I) g f x + gradientFun (I := I) g h x := by
  simpa using (DifferentialGeometry.Geometry.Operator.gradFun_add g hf hh)

theorem normGradSq_log_heat_evolution_identity
    [NeZero (Module.finrank ℝ E)]
    {D : RealTimeInterval}
    (g : SmoothRiemannianMetric I M)
    (u : ℝ → M → ℝ)
    (hu : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2) (D.regular ×ˢ univ))
    (hslice : ∀ t : ℝ, t ∈ D.carrier → ContMDiff I 𝓘(ℝ, ℝ) ∞ (u t))
    (hlogslice : ∀ t : ℝ, t ∈ D.carrier → ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun y : M => Real.log (u t y)))
    (hpos : ∀ t : ℝ, t ∈ D.carrier → ∀ x : M, 0 < u t x)
    (hpde : ∀ t : ℝ, (ht : t ∈ D.regular) → ∀ x : M,
      HasDerivAt (fun s => u s x)
        (deltaLegacy (I := I) g (hslice t (D.regular_subset ht)) x) t)
    {t : ℝ} (ht : t ∈ D.regular) (x : M)
    (hNslice : ∀ t : ℝ, t ∈ D.regular → ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun y : M => g.inner y
        (gradientFun (I := I) g (fun z => Real.log (u t z)) y)
        (gradientFun (I := I) g (fun z => Real.log (u t z)) y))) :
    deriv (fun s : ℝ =>
        g.inner x (gradientFun (I := I) g (fun y => Real.log (u s y)) x)
          (gradientFun (I := I) g (fun y => Real.log (u s y)) x)) t -
      deltaLegacy (I := I) g (hNslice t ht) x =
      2 * g.inner x (gradientFun (I := I) g (fun y => Real.log (u t y)) x)
          (gradientFun (I := I) g (fun y => g.inner y
            (gradientFun (I := I) g (fun z => Real.log (u t z)) y)
            (gradientFun (I := I) g (fun z => Real.log (u t z)) y)) x) -
        2 * chartHessFrobeniusSq (I := I) g (fun y => Real.log (u t y)) x -
        2 * ricciTensor (I := I) g x (gradFun (I := I) g (fun y => Real.log (u t y)) x)
          (gradFun (I := I) g (fun y => Real.log (u t y)) x) := by
  classical
  let f : ℝ → M → ℝ := fun s y => Real.log (u s y)
  have hlog' : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => f p.1 p.2) (D.regular ×ˢ univ) := by
    intro p hp
    have hnh : D.regular ×ˢ univ ∈ 𝓝 p :=
      (IsOpen.prod D.regular_isOpen isOpen_univ).mem_nhds ⟨hp.1, trivial⟩
    have hlogAt : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => Real.log (u p.1 p.2)) p :=
      (Real.contDiffAt_log.2 (hpos p.1 (D.regular_subset hp.1) p.2).ne').comp_contMDiffAt
        (x := p) (hu.contMDiffAt hnh)
    simpa [f] using hlogAt.contMDiffWithinAt
  have hslice_ft : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun y : M => f t y) := by
    simpa [f] using hlogslice t (D.regular_subset ht)
  let N : ℝ → M → ℝ := fun s y => g.inner y
        (gradientFun (I := I) g (fun z => Real.log (u s z)) y)
        (gradientFun (I := I) g (fun z => Real.log (u s z)) y)
  have hNt := DifferentialGeometry.Analysis.Parabolic.Harnack.normGradSq_timeDeriv_of_log_heat
    (D := D) g u hu hpos ht x
  have hder_N : deriv (fun s : ℝ => N s x) t =
      2 * g.inner x (gradientFun (I := I) g (fun y => Real.log (u t y)) x)
        (gradientFun (I := I) g (fun y => deriv (fun σ : ℝ => Real.log (u σ y)) t) x) := by
    simpa [N] using hNt.deriv
  have hlog_ev : ∀ s (hs : s ∈ D.regular) y,
      deriv (fun σ : ℝ => Real.log (u σ y)) s =
        deltaLegacy (I := I) g (hlogslice s (D.regular_subset hs)) y + N s y := by
    intro s hs y
    have h := DifferentialGeometry.Analysis.Parabolic.Harnack.heatSolution_log_evolution
      (D := D) g u hslice hlogslice hpos hs (hpde s hs y)
    simpa [N, f] using h
  have hNslice_mdiff : MDifferentiableAt I 𝓘(ℝ, ℝ) (N t) x :=
    (hNslice t ht).mdifferentiableAt (x := x) (by norm_num)
  have hdel_cd : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun y : M => deltaLegacy (I := I) g (hlogslice t (D.regular_subset ht)) y) := by
    simpa using (deltaLegacy_contMDiff (I := I) g (hlogslice t (D.regular_subset ht)))
  have hDel_mdiff : MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun y : M => deltaLegacy (I := I) g (hlogslice t (D.regular_subset ht)) y) x :=
    hdel_cd.mdifferentiableAt (x := x) (by norm_num)
  have hgrad_ft : gradientFun (I := I) g
        (fun y => deriv (fun σ : ℝ => Real.log (u σ y)) t) x =
      gradientFun (I := I) g
          (fun y : M => deltaLegacy (I := I) g (hlogslice t (D.regular_subset ht)) y) x +
        gradientFun (I := I) g (N t) x := by
    have hfun : (fun y : M => deriv (fun σ : ℝ => Real.log (u σ y)) t) =
        (fun y : M => deltaLegacy (I := I) g (hlogslice t (D.regular_subset ht)) y +
          N t y) := by
      funext y
      exact hlog_ev t ht y
    rw [hfun]
    exact gradientFun_add g x hDel_mdiff hNslice_mdiff
  have hbochner :=
    DifferentialGeometry.Geometry.Curvature.bochner_pointwise_grad_normSq_of_boundaryless
    (I := I) g hslice_ft x
  have hbochner' : deltaLegacy (I := I) g (hNslice t ht) x =
      2 * frobeniusSq_grad_vector (I := I) g (fun b => gradFun (I := I) g (fun y => f t y) b) x +
        2 * ricciTensor (I := I) g x (gradFun (I := I) g (fun y => f t y) x) (gradFun (I := I) g
          (fun y => f t y) x) +
        2 * g.inner x (gradFun (I := I) g (fun y => f t y) x) (gradFun (I := I) g (deltaLegacy
          (I := I) g hslice_ft) x) := by
    have hcongr : deltaLegacy (I := I) g (hNslice t ht) x =
        deltaLegacy (I := I) g (normGradSqFun_contMDiff (I := I) g hslice_ft) x := by
      refine Δ_g_congr_of_eventuallyEq (I := I) g (hNslice t ht)
        (normGradSqFun_contMDiff (I := I) g hslice_ft) ?_
      rw [Filter.eventuallyEq_iff_exists_mem]
      refine ⟨Set.univ, Filter.univ_mem, ?_⟩
      intro y hy
      simp [f, normGradSqFun]
    exact hcongr.trans hbochner
  have hmain : deriv (fun s : ℝ => N s x) t -
        deltaLegacy (I := I) g (hNslice t ht) x =
      2 * g.inner x (gradientFun (I := I) g (fun y => Real.log (u t y)) x)
          (gradientFun (I := I) g (N t) x) -
        2 * frobeniusSq_grad_vector (I := I) g (fun b => gradFun (I := I) g (fun y => f t y) b) x -
        2 * ricciTensor (I := I) g x (gradFun (I := I) g (fun y => f t y) x)
          (gradFun (I := I) g (fun y => f t y) x) := by
    rw [hder_N]
    rw [hgrad_ft]
    rw [hbochner']
    rw [map_add]
    have hΔf_eq : g.inner x (gradientFun (I := I) g (fun y => Real.log (u t y)) x)
          (gradientFun (I := I) g (fun y => deltaLegacy (I := I) g (hlogslice t
            (D.regular_subset ht)) y) x) =
        g.inner x (gradFun (I := I) g (fun y => f t y) x) (gradFun (I := I) g (deltaLegacy
          (I := I) g hslice_ft) x) := by
      rfl
    rw [hΔf_eq]
    ring
  have hfrob : frobeniusSq_grad_vector (I := I) g (fun b => gradFun (I := I) g
    (fun y => f t y) b) x =
      chartHessFrobeniusSq (I := I) g (fun y => Real.log (u t y)) x := by
    simpa [f] using (frobeniusSq_grad_vector_eq_chartHessFrobeniusSq (I := I) g hslice_ft x)
  rw [hfrob] at hmain
  simpa [f, N] using hmain

theorem liYauQuantity_sq_div_n_le_chartHessFrobeniusSq
    [NeZero (Module.finrank ℝ E)]
    {D : RealTimeInterval}
    (g : SmoothRiemannianMetric I M)
    (u : ℝ → M → ℝ)
    (hslice : ∀ t : ℝ, t ∈ D.carrier → ContMDiff I 𝓘(ℝ, ℝ) ∞ (u t))
    (hlogslice : ∀ t : ℝ, t ∈ D.carrier → ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun y : M => Real.log (u t y)))
    (hpos : ∀ t : ℝ, t ∈ D.carrier → ∀ x : M, 0 < u t x)
    {t : ℝ} (ht : t ∈ D.regular) {x : M}
    (hpde : HasDerivAt (fun s => u s x)
      (deltaLegacy (I := I) g (hslice t (D.regular_subset ht)) x) t) :
    (liYauQuantity g (fun τ y => Real.log (u τ y)) t x)^2 /
        (Module.finrank ℝ E : ℝ) ≤
      chartHessFrobeniusSq (I := I) g (fun y => Real.log (u t y)) x := by
  classical
  have hn : (0 : ℝ) < (Module.finrank ℝ E : ℝ) := by
    exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E)))
  have htrace0 := laplacian_sq_le_dim_mul_hessianFrobeniusSq_of_boundaryless (I := I) g
    (hlogslice t (D.regular_subset ht)) x
  have hle0 : (deltaLegacy (I := I) g (hlogslice t (D.regular_subset ht)) x)^2 ≤
      chartHessFrobeniusSq (I := I) g (fun y : M => Real.log (u t y)) x *
        (Module.finrank ℝ E : ℝ) := by
    rw [mul_comm] at htrace0
    exact htrace0
  have hdiv : (deltaLegacy (I := I) g (hlogslice t (D.regular_subset ht)) x)^2 /
        (Module.finrank ℝ E : ℝ) ≤ chartHessFrobeniusSq (I := I) g (fun y => Real.log
          (u t y)) x := by
    exact (div_le_iff₀ hn).2 hle0
  have hqid := liYauQuantity_eq_neg_laplacian (I := I) (M := M)
    (D := D) g u hslice hlogslice hpos ht hpde
  have hqsq : (liYauQuantity g (fun τ y => Real.log (u τ y)) t x)^2 =
      (deltaLegacy (I := I) g (hlogslice t (D.regular_subset ht)) x)^2 := by
    rw [hqid]
    ring
  rwa [hqsq]

omit [SigmaCompactSpace M] in
theorem hamiltonF_ricci_dissipation_of_ricci_lower_bound
    (g : SmoothRiemannianMetric I M) {K : ℝ}
    (hRic : ∀ x v, -K * g.inner x v v ≤ ricciTensor (I := I) g x v v)
    (u : ℝ → M → ℝ)
    {t : ℝ} (x : M) :
    -(2 * Real.exp ((-(2 * K)) * t) *
        ricciTensor (I := I) g x (gradFun (I := I) g (fun y => Real.log (u t y)) x)
          (gradFun (I := I) g (fun y => Real.log (u t y)) x)) +
      (-(2 * K)) * Real.exp ((-(2 * K)) * t) *
        g.inner x (gradientFun (I := I) g (fun y => Real.log (u t y)) x)
          (gradientFun (I := I) g (fun y => Real.log (u t y)) x) ≤ 0 := by
  classical
  let logut : M → ℝ := fun y => Real.log (u t y)
  have hvecg : ∀ h : M → ℝ, gradientFun (I := I) g h x = gradFun (I := I) g h x := by
    intro h
    apply (metricFlatEquiv (I := I) g x).injective
    ext w
    change g.inner x (gradientFun (I := I) g h x) w = g.inner x (gradFun (I := I) g h x) w
    rw [inner_gradientFun (I := I) g h x w]
    rw [inner_gradFun (I := I) g h x w]
  have hr := hRic x (gradFun (I := I) g logut x)
  have hin : g.inner x (gradientFun (I := I) g logut x) (gradientFun (I := I) g logut x) =
      g.inner x (gradFun (I := I) g logut x) (gradFun (I := I) g logut x) := by
    rw [hvecg logut]
  have hstep : -2 * ricciTensor (I := I) g x (gradFun (I := I) g logut x)
        (gradFun (I := I) g logut x) +
      (-(2 * K)) * g.inner x (gradFun (I := I) g logut x) (gradFun (I := I) g logut x) ≤ 0 := by
    nlinarith [hr]
  have hstep' : -2 * ricciTensor (I := I) g x (gradFun (I := I) g logut x)
        (gradFun (I := I) g logut x) +
      (-(2 * K)) * g.inner x (gradientFun (I := I) g logut x) (gradientFun
        (I := I) g logut x) ≤ 0 := by
    rw [hin]
    exact hstep
  have he : 0 < Real.exp ((-(2 * K)) * t) := Real.exp_pos _
  have hmul := mul_le_mul_of_nonneg_left hstep' he.le
  calc
    -(2 * Real.exp ((-(2 * K)) * t) *
          ricciTensor (I := I) g x (gradFun (I := I) g logut x)
            (gradFun (I := I) g logut x)) +
        (-(2 * K)) * Real.exp ((-(2 * K)) * t) *
          g.inner x (gradientFun (I := I) g logut x)
            (gradientFun (I := I) g logut x)
        = Real.exp ((-(2 * K)) * t) *
            (-2 * ricciTensor (I := I) g x (gradFun (I := I) g logut x)
                (gradFun (I := I) g logut x) +
              (-(2 * K)) * g.inner x (gradientFun (I := I) g logut x)
                (gradientFun (I := I) g logut x)) := by
          ring
    _ ≤ 0 := by simpa using hmul

theorem hamiltonF_evolution_inequality_of_ricci_lower_bound
    [NeZero (Module.finrank ℝ E)]
    {D : RealTimeInterval}
    (g : SmoothRiemannianMetric I M) {K : ℝ}
    (hRic : ∀ x v, -K * g.inner x v v ≤ ricciTensor (I := I) g x v v)
    (u : ℝ → M → ℝ)
    (hu : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2) (D.regular ×ˢ univ))
    (hslice : ∀ t : ℝ, t ∈ D.carrier → ContMDiff I 𝓘(ℝ, ℝ) ∞ (u t))
    (hlogslice : ∀ t : ℝ, t ∈ D.carrier → ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun y : M => Real.log (u t y)))
    (hpos : ∀ t : ℝ, t ∈ D.carrier → ∀ x : M, 0 < u t x)
    (hpde : ∀ t : ℝ, (ht : t ∈ D.regular) → ∀ x : M,
      HasDerivAt (fun s => u s x)
        (deltaLegacy (I := I) g (hslice t (D.regular_subset ht)) x) t)
    (hqOn : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => liYauQuantity g (fun τ y => Real.log (u τ y)) p.1 p.2)
      (D.regular ×ˢ univ))
    (hqslice : ∀ t : ℝ, t ∈ D.regular → ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun y : M => liYauQuantity g (fun σ z => Real.log (u σ z)) t y))
    (hNOn : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => g.inner p.2
        (gradientFun (I := I) g (fun y => Real.log (u p.1 y)) p.2)
        (gradientFun (I := I) g (fun y => Real.log (u p.1 y)) p.2))
      (D.regular ×ˢ univ))
    (hNslice : ∀ t : ℝ, t ∈ D.regular → ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun y : M => g.inner y
        (gradientFun (I := I) g (fun z => Real.log (u t z)) y)
        (gradientFun (I := I) g (fun z => Real.log (u t z)) y)))
    (hFslice : ∀ t : ℝ, t ∈ D.regular → ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun y : M =>
        Real.exp ((-(2 * K)) * t) *
          g.inner y (gradientFun (I := I) g (fun z => Real.log (u t z)) y)
            (gradientFun (I := I) g (fun z => Real.log (u t z)) y) -
        deriv (fun σ : ℝ => Real.log (u σ y)) t))
    {s : ℝ} (hs : s ∈ D.regular) (x : M)
    (hgradF : gradientFun (I := I) g
      (fun y : M =>
        Real.exp ((-(2 * K)) * s) *
          g.inner y (gradientFun (I := I) g (fun z => Real.log (u s z)) y)
            (gradientFun (I := I) g (fun z => Real.log (u s z)) y) -
        deriv (fun σ : ℝ => Real.log (u σ y)) s) x = 0) :
    deriv (fun τ : ℝ =>
        Real.exp ((-(2 * K)) * τ) *
          g.inner x (gradientFun (I := I) g (fun z => Real.log (u τ z)) x)
            (gradientFun (I := I) g (fun z => Real.log (u τ z)) x) -
        deriv (fun σ : ℝ => Real.log (u σ x)) τ) s -
      deltaLegacy (I := I) g (hFslice s hs) x ≤
      -(2 / (Module.finrank ℝ E : ℝ)) * Real.exp ((-(2 * K)) * s) *
        (liYauQuantity g (fun τ y => Real.log (u τ y)) s x)^2 := by
  classical
  let f : ℝ → M → ℝ := fun τ y => Real.log (u τ y)
  let N : ℝ → M → ℝ := fun τ y => g.inner y
        (gradientFun (I := I) g (f τ) y) (gradientFun (I := I) g (f τ) y)
  let c2 : ℝ := -(2 * K)
  let n : ℝ := (Module.finrank ℝ E : ℝ)
  let F : ℝ → M → ℝ := fun τ y => Real.exp ((-(2 * K)) * τ) * N τ y -
        deriv (fun σ : ℝ => f σ y) τ
  let q : ℝ → M → ℝ := fun τ y => liYauQuantity g f τ y
  let Gfam : MetricConnectionFamily (I := I) (M := M) ℝ :=
    { metric := fun _ => g
      connection := fun _ => LeviCivita (I := I) g
      metricCompatible := fun _ =>
        leviCivitaConnectionOfMetric_isMetricCompatible (I := I) g }
  have hconn : Gfam.connection s = LeviCivita (Gfam.metric s) := by
    simp [Gfam]
  have hq_slice_cd : ContMDiff I 𝓘(ℝ, ℝ) ∞ (q s) := by
    exact hqslice s hs
  have hN_slice_cd : ContMDiff I 𝓘(ℝ, ℝ) ∞ (N s) := by
    exact hNslice s hs
  have hF_slice_cd : ContMDiff I 𝓘(ℝ, ℝ) ∞ (F s) := by
    exact hFslice s hs
  have hgradF' : gradientFun (I := I) g (F s) x = 0 := by
    exact hgradF
  have hqTimeDiff : ∀ τ : ℝ, τ ∈ D.regular →
      DifferentiableAt ℝ (fun τ' : ℝ => q τ' x) τ := by
    intro τ hτ
    have hnh : D.regular ×ˢ univ ∈ 𝓝 (τ, x) :=
      (IsOpen.prod D.regular_isOpen isOpen_univ).mem_nhds ⟨hτ, trivial⟩
    have hqat : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => q p.1 p.2) (τ, x) := hqOn.contMDiffAt hnh
    have hsliceAt : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun τ' : ℝ => q τ' x) τ :=
      hqat.comp (x := τ) (contMDiffAt_id.prodMk contMDiffAt_const)
    exact MDifferentiableAt.differentiableAt
      (ContMDiffAt.mdifferentiableAt (n := ∞) hsliceAt (by norm_num))
  have hNTimeDiff : ∀ τ : ℝ, τ ∈ D.regular →
      DifferentiableAt ℝ (fun τ' : ℝ => N τ' x) τ := by
    intro τ hτ
    have hnh : D.regular ×ˢ univ ∈ 𝓝 (τ, x) :=
      (IsOpen.prod D.regular_isOpen isOpen_univ).mem_nhds ⟨hτ, trivial⟩
    have hNat : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => N p.1 p.2) (τ, x) := hNOn.contMDiffAt hnh
    have hsliceAt : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun τ' : ℝ => N τ' x) τ :=
      hNat.comp (x := τ) (contMDiffAt_id.prodMk contMDiffAt_const)
    exact MDifferentiableAt.differentiableAt
      (ContMDiffAt.mdifferentiableAt (n := ∞) hsliceAt (by norm_num))
  have hqid_raw := liYauQuantity_evolution_identity (I := I) (M := M)
    (D := D) g u hu hslice hlogslice hpos hpde hqslice hs x
  have hNid_raw := normGradSq_log_heat_evolution_identity (I := I) (M := M)
    (D := D) g u hu hslice hlogslice hpos hpde
    hs x hNslice
  have hqid' : deriv (fun τ' : ℝ => liYauQuantity g f τ' x) s - deltaLegacy
    (I := I) g hq_slice_cd x =
      2 * g.inner x (gradientFun (I := I) g (f s) x) (gradientFun (I := I) g (q s) x) -
        2 * chartHessFrobeniusSq (I := I) g (f s) x -
        2 * ricciTensor (I := I) g x (gradFun (I := I) g (f s) x)
          (gradFun (I := I) g (f s) x) := by
    exact hqid_raw
  have hNid' : deriv (fun τ' : ℝ => N τ' x) s - deltaLegacy (I := I) g hN_slice_cd x =
      2 * g.inner x (gradientFun (I := I) g (f s) x) (gradientFun (I := I) g (N s) x) -
        2 * chartHessFrobeniusSq (I := I) g (f s) x -
        2 * ricciTensor (I := I) g x (gradFun (I := I) g (f s) x)
          (gradFun (I := I) g (f s) x) := by
    exact hNid_raw
  have hgradq : gradientFun (I := I) g (q s) x =
      (1 - Real.exp (c2 * s)) • gradientFun (I := I) g (N s) x := by
    have hqN : (q s) = fun y : M => F s y + (1 - Real.exp (c2 * s)) * N s y := by
      funext y
      simp [q, F, N, liYauQuantity, c2]
      ring
    rw [hqN]
    have hFmdiff : MDifferentiableAt I 𝓘(ℝ, ℝ) (F s) x :=
      hF_slice_cd.mdifferentiableAt (x := x) (by norm_num)
    have hNmdiff : MDifferentiableAt I 𝓘(ℝ, ℝ) (N s) x :=
      hN_slice_cd.mdifferentiableAt (x := x) (by norm_num)
    have hsmulN : gradientFun (I := I) g
          ((fun _ : M => (1 - Real.exp (c2 * s))) * N s) x =
        (1 - Real.exp (c2 * s)) • gradientFun (I := I) g (N s) x := by
      have hfun : ((fun _ : M => (1 - Real.exp (c2 * s))) * N s) =
          (fun y : M => (1 - Real.exp (c2 * s)) • N s y) := by
        funext y
        simp [smul_eq_mul]
      rw [hfun]
      exact gradientFun_const_smul (I := I) g (1 - Real.exp (c2 * s)) hNmdiff
    have hadd : gradientFun (I := I) g
          (fun y : M => F s y + (1 - Real.exp (c2 * s)) * N s y) x =
        gradientFun (I := I) g (F s) x + gradientFun (I := I) g
          ((fun _ : M => (1 - Real.exp (c2 * s))) * N s) x := by
      have hfun : (fun y : M => F s y + (1 - Real.exp (c2 * s)) * N s y) =
          (F s) + ((fun _ : M => (1 - Real.exp (c2 * s))) * N s) := by
        funext y
        rfl
      rw [hfun]
      exact gradientFun_add (I := I) g x hFmdiff
        ((contMDiff_const.mul hN_slice_cd).mdifferentiableAt (x := x) (by norm_num))
    rw [hadd, hsmulN, hgradF']
    simp
  have hFtime : deriv (fun τ' : ℝ => F τ' x) s =
      deriv (fun τ' : ℝ => liYauQuantity g f τ' x) s -
        (1 - Real.exp (c2 * s)) * deriv (fun τ' : ℝ => N τ' x) s +
        c2 * Real.exp (c2 * s) * N s x := by
    have hFqN : ∀ τ' : ℝ, F τ' x =
        liYauQuantity g f τ' x - (1 - Real.exp (c2 * τ')) * N τ' x := by
      intro τ'
      simp [F, N, liYauQuantity, c2]
      ring
    have hprod : HasDerivAt (fun τ' : ℝ => (1 - Real.exp (c2 * τ')) * N τ' x)
          ((-(c2 * Real.exp (c2 * s))) * N s x +
            (1 - Real.exp (c2 * s)) * deriv (fun τ' : ℝ => N τ' x) s) s := by
      have hlin : HasDerivAt (fun τ' : ℝ => c2 * τ') c2 s := by
        simpa using (hasDerivAt_const s c2).mul (hasDerivAt_id s)
      have hdexp : HasDerivAt (fun τ' : ℝ => Real.exp (c2 * τ'))
          (Real.exp (c2 * s) * c2) s := by
        simpa using (Real.hasDerivAt_exp (c2 * s)).comp s hlin
      have hcoefd : HasDerivAt (fun τ' : ℝ => 1 - Real.exp (c2 * τ'))
          (-(Real.exp (c2 * s) * c2)) s := by
        simpa using (hasDerivAt_const s (1 : ℝ)).sub hdexp
      have hval : (-(c2 * Real.exp (c2 * s))) * N s x +
            (1 - Real.exp (c2 * s)) * deriv (fun τ' : ℝ => N τ' x) s =
          (-(Real.exp (c2 * s) * c2)) * N s x +
            (1 - Real.exp (c2 * s)) * deriv (fun τ' : ℝ => N τ' x) s := by
        ring_nf
      rw [hval]
      exact hcoefd.mul (hNTimeDiff s hs).hasDerivAt
    have hF_deriv : HasDerivAt (fun τ' : ℝ => F τ' x)
          (deriv (fun τ' : ℝ => liYauQuantity g f τ' x) s -
            ((-(c2 * Real.exp (c2 * s))) * N s x +
              (1 - Real.exp (c2 * s)) * deriv (fun τ' : ℝ => N τ' x) s)) s := by
      have hq_d : HasDerivAt (fun τ' : ℝ => liYauQuantity g f τ' x)
          (deriv (fun τ' : ℝ => liYauQuantity g f τ' x) s) s :=
        (hqTimeDiff s hs).hasDerivAt
      have hfun_eq : (fun τ' : ℝ => F τ' x) =
          (fun τ' : ℝ => liYauQuantity g f τ' x - (1 - Real.exp (c2 * τ')) * N τ' x) := by
        funext τ'
        exact hFqN τ'
      rw [hfun_eq]
      exact hq_d.sub hprod
    convert hF_deriv.deriv using 1; ring
  have hlapq : laplacianAt (I := I) Gfam s (q s) x = deltaLegacy (I := I) g hq_slice_cd x := by
    rw [laplacianAt_eq_delta (I := I) Gfam s hq_slice_cd hconn]
  have hlapN : laplacianAt (I := I) Gfam s (N s) x = deltaLegacy (I := I) g hN_slice_cd x := by
    rw [laplacianAt_eq_delta (I := I) Gfam s hN_slice_cd hconn]
  have hlapF : laplacianAt (I := I) Gfam s (F s) x =
      laplacianAt (I := I) Gfam s (fun y : M => liYauQuantity g f s y) x -
        (1 - Real.exp (c2 * s)) * laplacianAt (I := I) Gfam s (N s) x := by
    have hqF : (F s) = fun y : M => liYauQuantity g f s y - (1 - Real.exp (c2 * s)) * N s y := by
      funext y
      simp [F, N, liYauQuantity, c2]
      ring
    rw [hqF]
    have hN_s_mdiff : ∀ y : M, MDifferentiableAt I 𝓘(ℝ, ℝ) (N s) y := by
      intro y
      exact hN_slice_cd.mdifferentiableAt (x := y) (by norm_num)
    have hsmulNlap : laplacianAt (I := I) Gfam s
          (fun y : M => (1 - Real.exp (c2 * s)) * N s y) x =
        (1 - Real.exp (c2 * s)) * laplacianAt (I := I) Gfam s (N s) x := by
      have hfun : (fun y : M => (1 - Real.exp (c2 * s)) * N s y) =
          (fun y : M => (1 - Real.exp (c2 * s)) • N s y) := by
        funext y
        simp [smul_eq_mul]
      rw [hfun]
      have hsmul := laplacianAt_smul (I := I) Gfam s (1 - Real.exp (c2 * s)) hN_s_mdiff
        (gradientFun_mdiffAt (I := I) (Gfam.metric s) hN_slice_cd x)
      simpa [smul_eq_mul] using hsmul
    have hsub := laplacianAt_sub (I := I) Gfam s
      (f := fun y : M => liYauQuantity g f s y)
      (h := fun y : M => (1 - Real.exp (c2 * s)) * N s y) (x := x)
      (fun y : M => hq_slice_cd.mdifferentiableAt (x := y) (by norm_num))
      (fun y : M => (contMDiff_const.mul hN_slice_cd).mdifferentiableAt (x := y) (by norm_num))
      (gradientFun_mdiffAt (I := I) (Gfam.metric s) hq_slice_cd x)
      (gradientFun_mdiffAt (I := I) (Gfam.metric s) (contMDiff_const.mul hN_slice_cd) x)
    rw [hsub]
    rw [hsmulNlap]
  have hFsplit : deriv (fun τ' : ℝ => F τ' x) s - laplacianAt (I := I) Gfam s (F s) x =
      (deriv (fun τ' : ℝ => liYauQuantity g f τ' x) s - deltaLegacy (I := I) g hq_slice_cd x) -
        (1 - Real.exp (c2 * s)) *
          (deriv (fun τ' : ℝ => N τ' x) s - deltaLegacy (I := I) g hN_slice_cd x) +
        c2 * Real.exp (c2 * s) * N s x := by
    rw [hFtime, hlapF, hlapq, hlapN]
    ring
  have hdrift : 2 * g.inner x (gradientFun (I := I) g (f s) x) (gradientFun (I := I) g (q s) x) -
        (1 - Real.exp (c2 * s)) *
          (2 * g.inner x (gradientFun (I := I) g (f s) x) (gradientFun (I := I) g
            (N s) x)) = 0 := by
    have hinner : g.inner x (gradientFun (I := I) g (f s) x) (gradientFun (I := I) g (q s) x) =
        (1 - Real.exp (c2 * s)) * g.inner x (gradientFun (I := I) g (f s) x)
          (gradientFun (I := I) g (N s) x) := by
      rw [hgradq]
      simp [smul_eq_mul]
    rw [hinner]
    ring
  let A : ℝ := deriv (fun τ' : ℝ => liYauQuantity g f τ' x) s - deltaLegacy (I := I) g hq_slice_cd x
  let B : ℝ := deriv (fun τ' : ℝ => N τ' x) s - deltaLegacy (I := I) g hN_slice_cd x
  have hsubst : A - (1 - Real.exp (c2 * s)) * B + c2 * Real.exp (c2 * s) * N s x ≤
      -(2 / n) * Real.exp (c2 * s) * (q s x)^2 := by
    change (deriv (fun τ' : ℝ => liYauQuantity g f τ' x) s - deltaLegacy (I := I) g hq_slice_cd x) -
        (1 - Real.exp (c2 * s)) *
          (deriv (fun τ' : ℝ => N τ' x) s - deltaLegacy (I := I) g hN_slice_cd x) +
        c2 * Real.exp (c2 * s) * N s x ≤
      -(2 / n) * Real.exp (c2 * s) * (q s x)^2
    rw [hqid', hNid']
    have he : 0 ≤ Real.exp (c2 * s) := le_of_lt (Real.exp_pos _)
    have hHess : chartHessFrobeniusSq (I := I) g (f s) x ≥ (q s x)^2 / n := by
      have h := liYauQuantity_sq_div_n_le_chartHessFrobeniusSq (I := I) (M := M) (D := D) g u
        hslice hlogslice hpos hs (hpde s hs x)
      exact h
    have hHess' : -2 * Real.exp (c2 * s) * chartHessFrobeniusSq (I := I) g (f s) x ≤
        -2 * Real.exp (c2 * s) * ((q s x)^2 / n) := by
      exact mul_le_mul_of_nonpos_left hHess (by nlinarith)
    have hHess'' : -2 * Real.exp (c2 * s) * chartHessFrobeniusSq (I := I) g (f s) x ≤
        -(2 / n) * Real.exp (c2 * s) * (q s x)^2 := by
      have hrewrite : -2 * Real.exp (c2 * s) * ((q s x)^2 / n) =
          -(2 / n) * Real.exp (c2 * s) * (q s x)^2 := by ring
      rw [hrewrite] at hHess'
      exact hHess'
    have hRic2 : -(2 * Real.exp (c2 * s) * ricciTensor (I := I) g x
          (gradFun (I := I) g (f s) x) (gradFun (I := I) g (f s) x)) +
        c2 * Real.exp (c2 * s) * N s x ≤ 0 := by
      have h := hamiltonF_ricci_dissipation_of_ricci_lower_bound (I := I) (M := M) g hRic u
        (t := s) x
      exact h
    nlinarith [hdrift, hHess'', hRic2]
  have hFle_at : deriv (fun τ' : ℝ => F τ' x) s - laplacianAt (I := I) Gfam s (F s) x ≤
      -(2 / n) * Real.exp (c2 * s) * (q s x)^2 := by
    rw [hFsplit]
    exact hsubst
  have hF_delta : laplacianAt (I := I) Gfam s (F s) x =
      deltaLegacy (I := I) g (hFslice s hs) x := by
    rw [laplacianAt_eq_delta (I := I) Gfam s hF_slice_cd hconn]
  rw [hF_delta] at hFle_at
  exact hFle_at

theorem hamilton_strict_neg_of_slab_positivity
    {F q eps s K n c2 : ℝ}
    (heps : 0 < eps) (hspos : 0 < s) (hn_pos : 0 < n) (hK : 0 ≤ K)
    (hc2 : c2 = -(2 * K))
    (hGpos : 0 < s * F - Real.exp (2 * K * s) * (n / 2) - eps * s)
    (hFq : F ≤ q) :
    F - (2 * s / n) * Real.exp (c2 * s) * q ^ 2 -
      2 * K * Real.exp (2 * K * s) * (n / 2) - eps < 0 := by
  have hFbig : Real.exp (2 * K * s) * (n / 2) / s + eps < F := by
    have hmain : Real.exp (2 * K * s) * (n / 2) + eps * s < s * F := by linarith
    have hdiv : (Real.exp (2 * K * s) * (n / 2) + eps * s) / s < F :=
      (div_lt_iff₀ hspos).mpr (by nlinarith [hmain])
    have hrewrite : (Real.exp (2 * K * s) * (n / 2) + eps * s) / s =
        Real.exp (2 * K * s) * (n / 2) / s + eps := by
      field_simp [hspos.ne']
    rw [hrewrite] at hdiv
    exact hdiv
  have hApos : 0 < Real.exp (2 * K * s) * (n / 2) / s := by positivity
  have hFgtA : Real.exp (2 * K * s) * (n / 2) / s < F := by linarith [hFbig]
  have hFpos : 0 < F := lt_trans hApos hFgtA
  have hsq : F ^ 2 ≤ q ^ 2 := by simpa [pow_two] using mul_self_le_mul_self hFpos.le hFq
  have hcpos : 0 < (2 * s / n) * Real.exp (c2 * s) := by
    have hs2 : 0 < 2 * s := mul_pos zero_lt_two hspos
    exact mul_pos (div_pos hs2 hn_pos) (Real.exp_pos _)
  have hmul1 : (2 * s / n) * Real.exp (c2 * s) * (Real.exp (2 * K * s) * (n / 2) / s) = 1 := by
    rw [hc2]
    field_simp [hspos.ne', hn_pos.ne']
    rw [← Real.exp_add]
    rw [show -(2 * s * K) + 2 * s * K = 0 by ring]
    exact Real.exp_zero
  have hcFgt1 : 1 < (2 * s / n) * Real.exp (c2 * s) * F := by
    have hmul := mul_lt_mul_of_pos_left hFgtA hcpos
    rwa [hmul1] at hmul
  have hFcF : F - (2 * s / n) * Real.exp (c2 * s) * F ^ 2 < 0 := by
    have hfactor : F - (2 * s / n) * Real.exp (c2 * s) * F ^ 2 =
        F * (1 - (2 * s / n) * Real.exp (c2 * s) * F) := by ring
    have h1 : 1 - (2 * s / n) * Real.exp (c2 * s) * F < 0 := by linarith
    rw [hfactor]
    exact mul_neg_of_pos_of_neg hFpos h1
  have hmain2 : F - (2 * s / n) * Real.exp (c2 * s) * q ^ 2 -
        2 * K * Real.exp (2 * K * s) * (n / 2) - eps ≤
      F - (2 * s / n) * Real.exp (c2 * s) * F ^ 2 - eps := by
    have hterm : (2 * s / n) * Real.exp (c2 * s) * F ^ 2 ≤
        (2 * s / n) * Real.exp (c2 * s) * q ^ 2 :=
      mul_le_mul_of_nonneg_left hsq hcpos.le
    have hKterm : 0 ≤ 2 * K * Real.exp (2 * K * s) * (n / 2) := by
      have h1 : 0 ≤ 2 * K := mul_nonneg (by norm_num) hK
      have h2 : 0 ≤ 2 * K * Real.exp (2 * K * s) := mul_nonneg h1 (le_of_lt (Real.exp_pos _))
      exact mul_nonneg h2 (div_nonneg (le_of_lt hn_pos) (by norm_num))
    linarith
  have hmain3 : F - (2 * s / n) * Real.exp (c2 * s) * F ^ 2 - eps < 0 := by
    linarith [hFcF, heps]
  linarith

omit [T2Space M] [SigmaCompactSpace M] in
theorem hamiltonQuantity_mul_time_continuousOn
    {D : RealTimeInterval} {K : ℝ}
    (g : SmoothRiemannianMetric I M)
    (u : ℝ → M → ℝ)
    (hu : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2) (D.carrier ×ˢ univ))
    (hslice : ∀ t : ℝ, t ∈ D.carrier → ContMDiff I 𝓘(ℝ, ℝ) ∞ (u t))
    (hpos : ∀ t : ℝ, t ∈ D.carrier → ∀ x : M, 0 < u t x)
    {t : ℝ} (ht : t ∈ D.regular) (ht0 : 0 < t)
    (hslabCarrier : Icc 0 t ⊆ D.carrier)
    (hslabRegular : Ioo 0 t ⊆ D.regular) :
    ContinuousOn (fun p : ℝ × M =>
      p.1 * (Real.exp ((-(2 * K)) * p.1) *
          g.inner p.2 (gradientFun (I := I) g (fun y => Real.log (u p.1 y)) p.2)
            (gradientFun (I := I) g (fun y => Real.log (u p.1 y)) p.2) -
        deriv (fun σ : ℝ => Real.log (u σ p.2)) p.1))
      (Icc 0 t ×ˢ univ) := by
  classical
  let f : ℝ → M → ℝ := fun s y => Real.log (u s y)
  let N : ℝ → M → ℝ := fun s y => g.inner y (gradientFun (I := I) g (f s) y)
      (gradientFun (I := I) g (f s) y)
  let F : ℝ → M → ℝ := fun s y => Real.exp ((-(2 * K)) * s) * N s y -
      deriv (fun σ : ℝ => f σ y) s
  have hsq : ContinuousOn (fun p : ℝ × M => p.1 * liYauQuantity g f p.1 p.2)
      (Icc 0 t ×ˢ univ) :=
    liYauQuantity_mul_time_continuousOn (I := I) (M := M) (D := D) g u hu hslice hpos ht ht0
      hslabCarrier hslabRegular
  have hsderiv : ContinuousOn (fun p : ℝ × M => p.1 * deriv (fun σ : ℝ => f σ p.2) p.1)
      (Icc 0 t ×ˢ univ) :=
    timeMulLogDeriv_continuousOn (I := I) (M := M) (D := D) g u hu hslice hpos ht ht0
      hslabCarrier hslabRegular
  have hcoeff : ContinuousOn (fun p : ℝ × M => Real.exp ((-(2 * K)) * p.1))
      (Icc 0 t ×ˢ univ) := by
    have hlin : ContinuousOn (fun p : ℝ × M => (-(2 * K)) * p.1)
        (Icc 0 t ×ˢ univ) := continuousOn_const.mul continuousOn_fst
    exact Real.continuous_exp.continuousOn.comp hlin (by intro p hp; exact Set.mem_univ _)
  have hq_eq : ∀ (s : ℝ) (y : M), liYauQuantity g f s y = N s y - deriv (fun σ : ℝ => f σ y) s := by
    intro s y
    unfold liYauQuantity N
    rfl
  have hmain' : ContinuousOn (fun p : ℝ × M =>
      Real.exp ((-(2 * K)) * p.1) * (p.1 * liYauQuantity g f p.1 p.2) +
        (Real.exp ((-(2 * K)) * p.1) - 1) * (p.1 * deriv (fun σ : ℝ => f σ p.2) p.1))
      (Icc 0 t ×ˢ univ) :=
    (hcoeff.mul hsq).add ((hcoeff.sub continuousOn_const).mul hsderiv)
  have hmain : ContinuousOn (fun p : ℝ × M => p.1 * F p.1 p.2) (Icc 0 t ×ˢ univ) := by
    refine hmain'.congr ?_
    intro p hp
    change p.1 * F p.1 p.2 =
      Real.exp ((-(2 * K)) * p.1) * (p.1 * liYauQuantity g f p.1 p.2) +
        (Real.exp ((-(2 * K)) * p.1) - 1) * (p.1 * deriv (fun σ : ℝ => f σ p.2) p.1)
    dsimp [F, N]
    rw [hq_eq p.1 p.2]
    ring
  simpa [F, N, f] using hmain

omit [SigmaCompactSpace M] in
theorem hamilton_quantity_slab_bound_of_ricci_lower_bound
    [CompactSpace M]
    [VectorBundle ℝ E (TangentSpace I : M → Type _)]
    [ContMDiffVectorBundle (1 : WithTop ℕ∞) E (TangentSpace I : M → Type _) I]
    [NeZero (Module.finrank ℝ E)]
    {D : RealTimeInterval}
    (g : SmoothRiemannianMetric I M) {K : ℝ} (hK : 0 ≤ K)
    (hRic : ∀ x v, -K * g.inner x v v ≤ ricciTensor (I := I) g x v v)
    (u : ℝ → M → ℝ)
    (hu : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2) (D.regular ×ˢ univ))
    (hslice : ∀ t : ℝ, t ∈ D.carrier → ContMDiff I 𝓘(ℝ, ℝ) ∞ (u t))
    (hlogslice : ∀ t : ℝ, t ∈ D.carrier → ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun y : M => Real.log (u t y)))
    (hpos : ∀ t : ℝ, t ∈ D.carrier → ∀ x : M, 0 < u t x)
    (hpde : ∀ t : ℝ, (ht : t ∈ D.regular) → ∀ x : M,
      HasDerivAt (fun s => u s x)
        (deltaLegacy (I := I) g (hslice t (D.regular_subset ht)) x) t)
    (hqOn : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => liYauQuantity g (fun τ y => Real.log (u τ y)) p.1 p.2)
      (D.regular ×ˢ univ))
    (hqslice : ∀ t : ℝ, t ∈ D.regular → ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun y : M => liYauQuantity g (fun σ z => Real.log (u σ z)) t y))
    (hNOn : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => g.inner p.2
        (gradientFun (I := I) g (fun y => Real.log (u p.1 y)) p.2)
        (gradientFun (I := I) g (fun y => Real.log (u p.1 y)) p.2))
      (D.regular ×ˢ univ))
    (hNslice : ∀ t : ℝ, t ∈ D.regular → ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun y : M => g.inner y
        (gradientFun (I := I) g (fun z => Real.log (u t z)) y)
        (gradientFun (I := I) g (fun z => Real.log (u t z)) y)))
    (hFOn : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M =>
        Real.exp ((-(2 * K)) * p.1) *
          g.inner p.2 (gradientFun (I := I) g (fun y => Real.log (u p.1 y)) p.2)
            (gradientFun (I := I) g (fun y => Real.log (u p.1 y)) p.2) -
        deriv (fun σ : ℝ => Real.log (u σ p.2)) p.1)
      (D.regular ×ˢ univ))
    (hFslice : ∀ t : ℝ, t ∈ D.regular → ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun y : M =>
        Real.exp ((-(2 * K)) * t) *
          g.inner y (gradientFun (I := I) g (fun z => Real.log (u t z)) y)
            (gradientFun (I := I) g (fun z => Real.log (u t z)) y) -
        deriv (fun σ : ℝ => Real.log (u σ y)) t))
    {eps : ℝ} (heps : 0 < eps) {τ : ℝ} (hτ : 0 < τ)
    (hFsq : ContinuousOn (fun p : ℝ × M =>
        p.1 * (Real.exp ((-(2 * K)) * p.1) *
          g.inner p.2 (gradientFun (I := I) g (fun y => Real.log (u p.1 y)) p.2)
            (gradientFun (I := I) g (fun y => Real.log (u p.1 y)) p.2) -
        deriv (fun σ : ℝ => Real.log (u σ p.2)) p.1))
        (Icc 0 τ ×ˢ univ))
    (hτreg : τ ∈ D.regular)
    (hslabRegular : Ioo 0 τ ⊆ D.regular)
    (y : M) :
    τ * (Real.exp ((-(2 * K)) * τ) *
          g.inner y (gradientFun (I := I) g (fun z => Real.log (u τ z)) y)
            (gradientFun (I := I) g (fun z => Real.log (u τ z)) y) -
        deriv (fun σ : ℝ => Real.log (u σ y)) τ) -
      Real.exp (2 * K * τ) * ((Module.finrank ℝ E : ℝ) / 2) - eps * τ ≤ 0 := by
  classical
  let f : ℝ → M → ℝ := fun s y => Real.log (u s y)
  let q : ℝ → M → ℝ := fun τ y => liYauQuantity g f τ y
  let N : ℝ → M → ℝ := fun s y => g.inner y
        (gradientFun (I := I) g (f s) y) (gradientFun (I := I) g (f s) y)
  let n : ℝ := (Module.finrank ℝ E : ℝ)
  have hn_pos : 0 < n := by
    dsimp [n]
    exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E)))
  let F : ℝ → M → ℝ := fun s y => Real.exp ((-(2 * K)) * s) * N s y - deriv (fun σ : ℝ => f σ y) s
  let G : ℝ → ℝ → M → ℝ := fun eps s y => s * F s y - Real.exp (2 * K * s) * (n / 2) - eps * s
  let Gfam : MetricConnectionFamily (I := I) (M := M) ℝ :=
    { metric := fun _ => g
      connection := fun _ => LeviCivita (I := I) g
      metricCompatible := fun _ =>
        leviCivitaConnectionOfMetric_isMetricCompatible (I := I) g }
  have hqTimeDiff : ∀ (s : ℝ) (hs : s ∈ D.regular) (x₀ : M),
      DifferentiableAt ℝ (fun τ' : ℝ => q τ' x₀) s := by
    intro s hs x₀
    have hnh : D.regular ×ˢ univ ∈ 𝓝 (s, x₀) :=
      (IsOpen.prod D.regular_isOpen isOpen_univ).mem_nhds ⟨hs, trivial⟩
    have hqat : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => q p.1 p.2) (s, x₀) := hqOn.contMDiffAt hnh
    have hsliceAt : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun τ' : ℝ => q τ' x₀) s :=
      hqat.comp (x := s) (contMDiffAt_id.prodMk contMDiffAt_const)
    exact MDifferentiableAt.differentiableAt
      (ContMDiffAt.mdifferentiableAt (n := ∞) hsliceAt (by norm_num))
  have hNTimeDiff : ∀ (s : ℝ) (hs : s ∈ D.regular) (x₀ : M),
      DifferentiableAt ℝ (fun τ' : ℝ => N τ' x₀) s := by
    intro s hs x₀
    have hnh : D.regular ×ˢ univ ∈ 𝓝 (s, x₀) :=
      (IsOpen.prod D.regular_isOpen isOpen_univ).mem_nhds ⟨hs, trivial⟩
    have hNat : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => N p.1 p.2) (s, x₀) := hNOn.contMDiffAt hnh
    have hsliceAt : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun τ' : ℝ => N τ' x₀) s :=
      hNat.comp (x := s) (contMDiffAt_id.prodMk contMDiffAt_const)
    exact MDifferentiableAt.differentiableAt
      (ContMDiffAt.mdifferentiableAt (n := ∞) hsliceAt (by norm_num))
  have hFTimeDiff : ∀ (s : ℝ) (hs : s ∈ D.regular) (x₀ : M),
      DifferentiableAt ℝ (fun τ' : ℝ => F τ' x₀) s := by
    intro s hs x₀
    have hnh : D.regular ×ˢ univ ∈ 𝓝 (s, x₀) :=
      (IsOpen.prod D.regular_isOpen isOpen_univ).mem_nhds ⟨hs, trivial⟩
    have hFat : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => F p.1 p.2) (s, x₀) := hFOn.contMDiffAt hnh
    have hsliceAt : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun τ' : ℝ => F τ' x₀) s :=
      hFat.comp (x := s) (contMDiffAt_id.prodMk contMDiffAt_const)
    exact MDifferentiableAt.differentiableAt
      (ContMDiffAt.mdifferentiableAt (n := ∞) hsliceAt (by norm_num))
  have hG_nonpos : ∀ eps : ℝ, 0 < eps → G eps τ y ≤ 0 := by
    intro eps heps
    by_contra hG
    have hGpos : 0 < G eps τ y := lt_of_not_ge hG
    have hslab : IsCompact (Set.Icc 0 τ ×ˢ (Set.univ : Set M)) :=
      (isCompact_Icc : IsCompact (Set.Icc 0 τ)).prod isCompact_univ
    have hcont : ContinuousOn (fun p : ℝ × M => G eps p.1 p.2)
        (Set.Icc 0 τ ×ˢ (Set.univ : Set M)) := by
      have hfst : ContinuousOn (fun p : ℝ × M => p.1)
          (Set.Icc 0 τ ×ˢ (Set.univ : Set M)) := continuousOn_fst
      have hmult : ContinuousOn (fun p : ℝ × M => p.1 * F p.1 p.2)
          (Set.Icc 0 τ ×ˢ (Set.univ : Set M)) := hFsq
      have hterm2 : ContinuousOn (fun p : ℝ × M => Real.exp (2 * K * p.1) * (n / 2))
          (Set.Icc 0 τ ×ˢ (Set.univ : Set M)) := by
        have hlin : ContinuousOn (fun p : ℝ × M => 2 * K * p.1)
            (Set.Icc 0 τ ×ˢ (Set.univ : Set M)) := continuousOn_const.mul continuousOn_fst
        have hexp : ContinuousOn (fun p : ℝ × M => Real.exp (2 * K * p.1))
            (Set.Icc 0 τ ×ˢ (Set.univ : Set M)) :=
          Real.continuous_exp.continuousOn.comp hlin (by intro p hp; exact Set.mem_univ _)
        exact hexp.mul continuousOn_const
      have hsub1 : ContinuousOn (fun p : ℝ × M =>
          p.1 * F p.1 p.2 - Real.exp (2 * K * p.1) * (n / 2))
          (Set.Icc 0 τ ×ˢ (Set.univ : Set M)) := hmult.sub hterm2
      have hterm3 : ContinuousOn (fun p : ℝ × M => eps * p.1)
          (Set.Icc 0 τ ×ˢ (Set.univ : Set M)) := continuousOn_const.mul hfst
      have hsub : ContinuousOn (fun p : ℝ × M =>
          p.1 * F p.1 p.2 - Real.exp (2 * K * p.1) * (n / 2) - eps * p.1)
          (Set.Icc 0 τ ×ˢ (Set.univ : Set M)) := hsub1.sub hterm3
      exact hsub.congr (by intro p hp; simp [G])
    have hnonempty : (Set.Icc 0 τ ×ˢ (Set.univ : Set M)).Nonempty :=
      ⟨(τ, y), ⟨⟨le_of_lt hτ, le_rfl⟩, trivial⟩⟩
    obtain ⟨sx, hsx, hmax⟩ := hslab.exists_isMaxOn hnonempty hcont
    rcases sx with ⟨s, x₀⟩
    have hmax' : ∀ z : ℝ × M, z ∈ Set.Icc 0 τ ×ˢ Set.univ → G eps z.1 z.2 ≤ G eps s x₀ :=
      hmax
    have hmpos : 0 < G eps s x₀ :=
      lt_of_lt_of_le hGpos (hmax' (τ, y) ⟨⟨le_of_lt hτ, le_rfl⟩, trivial⟩)
    have hsx0 : 0 ≤ s := hsx.1.1
    have hspos : 0 < s := by
      have hs_ne0 : s ≠ 0 := by
        intro hs0
        have h0 : G eps 0 x₀ ≤ 0 := by
          simp [G]
          have hn0 : 0 ≤ n / 2 := by positivity
          linarith
        have : G eps s x₀ ≤ 0 := by
          simpa [hs0] using h0
        exact (not_lt_of_ge this) hmpos
      exact lt_of_le_of_ne hsx0 (Ne.symm hs_ne0)
    have hsreg : s ∈ D.regular := by
      by_cases hst : s = τ
      · subst s
        exact hτreg
      · exact hslabRegular ⟨hspos, lt_of_le_of_ne hsx.1.2 hst⟩
    have hzmax : IsMaxOn (fun τ' : ℝ => G eps τ' x₀) (Set.Icc 0 s) s := by
      intro τ' hτ'
      exact hmax' (τ', x₀) ⟨⟨hτ'.1, hτ'.2.trans hsx.1.2⟩, trivial⟩
    have hFsmooth : DifferentiableAt ℝ (fun τ' : ℝ => F τ' x₀) s := hFTimeDiff s hsreg x₀
    have hval : deriv (fun τ' : ℝ => G eps τ' x₀) s =
        F s x₀ + s * deriv (fun τ' : ℝ => F τ' x₀) s -
          2 * K * Real.exp (2 * K * s) * (n / 2) - eps := by
      have hlin : HasDerivAt (fun τ' : ℝ => τ' * F τ' x₀)
          (F s x₀ + s * deriv (fun τ' : ℝ => F τ' x₀) s) s := by
        simpa using (hasDerivAt_id s).mul hFsmooth.hasDerivAt
      have hexp : HasDerivAt (fun τ' : ℝ => Real.exp (2 * K * τ') * (n / 2))
          (2 * K * Real.exp (2 * K * s) * (n / 2)) s := by
        have hdexp : HasDerivAt (fun τ' : ℝ => Real.exp (2 * K * τ')) (Real.exp (2 * K * s) *
          (2 * K)) s := by
          have hinner : HasDerivAt (fun τ' : ℝ => 2 * K * τ') (2 * K) s := by
            simpa using (hasDerivAt_const s (2 * K)).mul (hasDerivAt_id s)
          simpa using (Real.hasDerivAt_exp (2 * K * s)).comp s hinner
        convert (hdexp.mul (hasDerivAt_const s (n / 2))) using 1; ring
      have hconst : HasDerivAt (fun τ' : ℝ => eps * τ') eps s := by
        simpa using (hasDerivAt_id s).const_mul eps
      have hmain : HasDerivAt (fun τ' : ℝ => τ' * F τ' x₀ - Real.exp (2 * K * τ') *
        (n / 2) - eps * τ')
          (F s x₀ + s * deriv (fun τ' : ℝ => F τ' x₀) s -
            2 * K * Real.exp (2 * K * s) * (n / 2) - eps) s := by
        simpa using (hlin.sub hexp).sub hconst
      simpa [G] using hmain.deriv
    have hder : HasDerivAt (fun τ' : ℝ => G eps τ' x₀)
        (deriv (fun τ' : ℝ => G eps τ' x₀) s) s := by
      have hlin : HasDerivAt (fun τ' : ℝ => τ' * F τ' x₀)
          (F s x₀ + s * deriv (fun τ' : ℝ => F τ' x₀) s) s := by
        simpa using (hasDerivAt_id s).mul hFsmooth.hasDerivAt
      have hexp : HasDerivAt (fun τ' : ℝ => Real.exp (2 * K * τ') * (n / 2))
          (2 * K * Real.exp (2 * K * s) * (n / 2)) s := by
        have hdexp : HasDerivAt (fun τ' : ℝ => Real.exp (2 * K * τ')) (Real.exp (2 * K * s) *
          (2 * K)) s := by
          have hinner : HasDerivAt (fun τ' : ℝ => 2 * K * τ') (2 * K) s := by
            simpa using (hasDerivAt_const s (2 * K)).mul (hasDerivAt_id s)
          simpa using (Real.hasDerivAt_exp (2 * K * s)).comp s hinner
        convert (hdexp.mul (hasDerivAt_const s (n / 2))) using 1; ring
      have hconst : HasDerivAt (fun τ' : ℝ => eps * τ') eps s := by
        simpa using (hasDerivAt_id s).const_mul eps
      have hmain : HasDerivAt (fun τ' : ℝ => τ' * F τ' x₀ - Real.exp (2 * K * τ') *
        (n / 2) - eps * τ')
          (F s x₀ + s * deriv (fun τ' : ℝ => F τ' x₀) s -
            2 * K * Real.exp (2 * K * s) * (n / 2) - eps) s := by
        simpa using (hlin.sub hexp).sub hconst
      simpa [G, hval] using hmain
    have htime : 0 ≤ deriv (fun τ' : ℝ => G eps τ' x₀) s :=
      deriv_nonneg_at_right_endpoint_of_isMaxOn_Icc hspos hzmax hder
    have hxmax : IsLocalMax (G eps s) x₀ := by
      exact Filter.Eventually.of_forall (fun y => hmax' (s, y) ⟨⟨hsx.1.1, hsx.1.2⟩, trivial⟩)
    have hF_s : ContMDiff I 𝓘(ℝ, ℝ) ∞ (F s) := hFslice s hsreg
    have hslice_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ (G eps s) := by
      have hmain : ContMDiff I 𝓘(ℝ, ℝ) ∞
          (fun y : M => s * F s y - Real.exp (2 * K * s) * (n / 2) - eps * s) := by
        exact ((contMDiff_const.mul hF_s).sub contMDiff_const).sub
          (contMDiff_const.mul contMDiff_const)
      simpa [G] using hmain
    have hlap : laplacianAt (I := I) Gfam s (G eps s) x₀ ≤ 0 := by
      exact laplacianAt_nonpos_at_spatial_max (I := I) Gfam s hxmax hslice_smooth
    have hgrad : gradientFun (I := I) g (G eps s) x₀ = 0 :=
      gradientFun_eq_zero_of_isLocalMax (I := I) g hxmax
        (hslice_smooth.mdifferentiableAt (x := x₀) (by simp))
    have hgradF : gradientFun (I := I) g (F s) x₀ = 0 := by
      have hFslice_cd : ContMDiff I 𝓘(ℝ, ℝ) ∞ (F s) := hF_s
      have hFslice_mdiff : MDifferentiableAt I 𝓘(ℝ, ℝ) (F s) x₀ :=
        hFslice_cd.mdifferentiableAt (x := x₀) (by norm_num)
      have hsmul : gradientFun (I := I) g (fun y : M => s * F s y) x₀ =
          s • gradientFun (I := I) g (F s) x₀ := by
        exact gradientFun_const_smul (I := I) g s hFslice_mdiff
      have hsmul_cd : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y : M => s * F s y) x₀ :=
        (contMDiff_const.mul hFslice_cd).mdifferentiableAt (x := x₀) (by norm_num)
      have hconst_cd : MDifferentiableAt I 𝓘(ℝ, ℝ)
          (fun _ : M => Real.exp (2 * K * s) * (n / 2) + eps * s) x₀ :=
        (contMDiff_const (n := ∞) : ContMDiff I 𝓘(ℝ, ℝ) ∞
          (fun _ : M => Real.exp (2 * K * s) * (n / 2) + eps * s)).mdifferentiableAt
          (x := x₀) (by norm_num)
      have hGfun : (G eps s) = fun y : M => s * F s y - (Real.exp (2 * K * s) *
        (n / 2) + eps * s) := by
        funext y
        simp [G]
        ring
      have hgrad' : gradientFun (I := I) g (G eps s) x₀ = 0 := hgrad
      rw [hGfun] at hgrad'
      have hsub := gradientFun_sub (I := I) g hsmul_cd hconst_cd
      have hcst : gradientFun (I := I) g (fun _ : M => Real.exp (2 * K * s) *
        (n / 2) + eps * s) x₀ = 0 :=
        gradientFun_const (I := I) g (Real.exp (2 * K * s) * (n / 2) + eps * s) x₀
      rw [hsub, hcst, hsmul] at hgrad'
      have hsmul0 : s • gradientFun (I := I) g (F s) x₀ = 0 := by
        exact sub_eq_zero.mp hgrad'
      exact (smul_eq_zero.mp hsmul0).resolve_left (ne_of_gt hspos)
    have hF_slice_cd : ContMDiff I 𝓘(ℝ, ℝ) ∞ (F s) := hF_s
    have hN_slice_cd : ContMDiff I 𝓘(ℝ, ℝ) ∞ (N s) := hNslice s hsreg
    have hq_slice_cd : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun y : M => liYauQuantity g f s y) := hqslice s hsreg
    have hgradq : gradientFun (I := I) g (fun y : M => liYauQuantity g f s y) x₀ =
        (1 - Real.exp (-(2 * K) * s)) • gradientFun (I := I) g (N s) x₀ := by
      have hqN : (fun y : M => liYauQuantity g f s y) =
          (fun y : M => F s y + (1 - Real.exp (-(2 * K) * s)) * N s y) := by
        funext y
        simp [F, N, liYauQuantity]
        ring
      have hqN' : (fun y : M => liYauQuantity g f s y) =
          (fun y : M => F s y + (1 - Real.exp (-(2 * K) * s)) * N s y) := hqN
      rw [hqN']
      have hsmulN : gradientFun (I := I) g
            ((fun _ : M => (1 - Real.exp (-(2 * K) * s))) * N s) x₀ =
          (1 - Real.exp (-(2 * K) * s)) • gradientFun (I := I) g (N s) x₀ := by
        have hfun : ((fun _ : M => (1 - Real.exp (-(2 * K) * s))) * N s) =
            (fun y : M => (1 - Real.exp (-(2 * K) * s)) • N s y) := by
          funext y
          simp [smul_eq_mul]
        rw [hfun]
        exact gradientFun_const_smul (I := I) g (1 - Real.exp (-(2 * K) * s))
          (hN_slice_cd.mdifferentiableAt (x := x₀) (by norm_num))
      have hfun_eq : (fun y : M => F s y + (1 - Real.exp (-(2 * K) * s)) * N s y) =
          (fun y : M => F s y + ((fun _ : M => (1 - Real.exp (-(2 * K) * s))) * N s) y) := by
        funext y
        rfl
      rw [hfun_eq]
      rw [DifferentialGeometry.Geometry.Operator.gradientFun_add (I := I) g
        (hF_slice_cd.mdifferentiableAt (x := x₀) (by norm_num))
        ((contMDiff_const.mul hN_slice_cd).mdifferentiableAt (x := x₀) (by norm_num)), hgradF,
          hsmulN]
      simp
    let c2 : ℝ := -(2 * K)
    have hFqN : ∀ τ' : ℝ, F τ' x₀ =
        liYauQuantity g f τ' x₀ - (1 - Real.exp (c2 * τ')) * N τ' x₀ := by
      intro τ'
      simp [F, N, liYauQuantity, c2]
      ring
    have hFtime : deriv (fun τ' : ℝ => F τ' x₀) s =
        deriv (fun τ' : ℝ => liYauQuantity g f τ' x₀) s -
          (1 - Real.exp (c2 * s)) * deriv (fun τ' : ℝ => N τ' x₀) s +
          c2 * Real.exp (c2 * s) * N s x₀ := by
      have hq_t : DifferentiableAt ℝ (fun τ' : ℝ => liYauQuantity g f τ' x₀) s :=
        hqTimeDiff s hsreg x₀
      have hN_t : DifferentiableAt ℝ (fun τ' : ℝ => N τ' x₀) s :=
        hNTimeDiff s hsreg x₀
      have hprod : HasDerivAt (fun τ' : ℝ => (1 - Real.exp (c2 * τ')) * N τ' x₀)
          ((-(c2 * Real.exp (c2 * s))) * N s x₀ +
            (1 - Real.exp (c2 * s)) * deriv (fun τ' : ℝ => N τ' x₀) s) s := by
        have hlin : HasDerivAt (fun τ' : ℝ => c2 * τ') c2 s := by
          simpa using (hasDerivAt_const s c2).mul (hasDerivAt_id s)
        have hdexp : HasDerivAt (fun τ' : ℝ => Real.exp (c2 * τ'))
            (Real.exp (c2 * s) * c2) s := by
          simpa using (Real.hasDerivAt_exp (c2 * s)).comp s hlin
        have hcoefd : HasDerivAt (fun τ' : ℝ => 1 - Real.exp (c2 * τ'))
            (-(Real.exp (c2 * s) * c2)) s := by
          simpa using (hasDerivAt_const s (1 : ℝ)).sub hdexp
        have hval : (-(c2 * Real.exp (c2 * s))) * N s x₀ +
              (1 - Real.exp (c2 * s)) * deriv (fun τ' : ℝ => N τ' x₀) s =
            (-(Real.exp (c2 * s) * c2)) * N s x₀ +
              (1 - Real.exp (c2 * s)) * deriv (fun τ' : ℝ => N τ' x₀) s := by
          ring_nf
        rw [hval]
        exact hcoefd.mul hN_t.hasDerivAt
      have hF_deriv : HasDerivAt (fun τ' : ℝ => F τ' x₀)
          (deriv (fun τ' : ℝ => liYauQuantity g f τ' x₀) s -
            ((-(c2 * Real.exp (c2 * s))) * N s x₀ +
              (1 - Real.exp (c2 * s)) * deriv (fun τ' : ℝ => N τ' x₀) s)) s := by
        have hq_d : HasDerivAt (fun τ' : ℝ => liYauQuantity g f τ' x₀)
            (deriv (fun τ' : ℝ => liYauQuantity g f τ' x₀) s) s := hq_t.hasDerivAt
        have hfun_eq : (fun τ' : ℝ => F τ' x₀) =
            (fun τ' : ℝ => liYauQuantity g f τ' x₀ - (1 - Real.exp (c2 * τ')) * N τ' x₀) := by
          funext τ'
          exact hFqN τ'
        rw [hfun_eq]
        exact hq_d.sub hprod
      convert hF_deriv.deriv using 1; ring
    have hF_s_cd : ContMDiff I 𝓘(ℝ, ℝ) ∞ (F s) := hF_slice_cd
    have hlapF : laplacianAt (I := I) Gfam s (F s) x₀ =
        laplacianAt (I := I) Gfam s (fun y : M => liYauQuantity g f s y) x₀ -
          (1 - Real.exp (c2 * s)) * laplacianAt (I := I) Gfam s (N s) x₀ := by
      have hqF : (F s) = fun y : M => liYauQuantity g f s y - (1 - Real.exp (c2 * s)) * N s y := by
        funext y
        simp [F, N, liYauQuantity, c2]
        ring
      rw [hqF]
      have hconst_smooth : ContMDiff I 𝓘(ℝ,
        ℝ) ∞ (fun _ : M => 1 - Real.exp (c2 * s)) := contMDiff_const
      have hconst_mdiff : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun _ : M => 1 - Real.exp (c2 * s)) x₀ :=
        hconst_smooth.mdifferentiableAt (x := x₀) (by norm_num)
      have hN_s_mdiff : MDifferentiableAt I 𝓘(ℝ, ℝ) (N s) x₀ :=
        hN_slice_cd.mdifferentiableAt (x := x₀) (by norm_num)
      have hsmulNlap : laplacianAt (I := I) Gfam s (fun y : M => (1 - Real.exp
        (c2 * s)) * N s y) x₀ =
          (1 - Real.exp (c2 * s)) * laplacianAt (I := I) Gfam s (N s) x₀ := by
        have hfun : (fun y : M => (1 - Real.exp (c2 * s)) * N s y) =
            (fun y : M => (1 - Real.exp (c2 * s)) • N s y) := by
          funext y
          simp [smul_eq_mul]
        rw [hfun]
        have hsmul := laplacianAt_smul (I := I) Gfam s (1 - Real.exp (c2 * s))
          (fun y : M => hN_slice_cd.mdifferentiableAt (x := y) (by norm_num))
          (gradientFun_mdiffAt (I := I) (Gfam.metric s) hN_slice_cd x₀)
        simpa [smul_eq_mul] using hsmul
      have hsub := laplacianAt_sub (I := I) Gfam s
        (f := fun y : M => liYauQuantity g f s y)
        (h := fun y : M => (1 - Real.exp (c2 * s)) * N s y)
        (x := x₀)
        (fun y : M => hq_slice_cd.mdifferentiableAt (x := y) (by norm_num))
        (fun y : M => (contMDiff_const.mul hN_slice_cd).mdifferentiableAt (x := y) (by norm_num))
        (gradientFun_mdiffAt (I := I) (Gfam.metric s) hq_slice_cd x₀)
        (gradientFun_mdiffAt (I := I) (Gfam.metric s) (contMDiff_const.mul hN_slice_cd) x₀)
      rw [hsub, hsmulNlap]
    have hFle : deriv (fun τ' : ℝ => F τ' x₀) s - laplacianAt (I := I) Gfam s (F s) x₀ ≤
        -(2 / n) * Real.exp (c2 * s) * (liYauQuantity g f s x₀)^2 := by
      have hconn : Gfam.connection s = LeviCivita (Gfam.metric s) := by
        simp [Gfam]
      have hlapF_slice : laplacianAt (I := I) Gfam s (F s) x₀ =
          deltaLegacy (I := I) g (hF_s_cd) x₀ := by
        rw [laplacianAt_eq_delta (I := I) Gfam s hF_s_cd hconn]
      have h := hamiltonF_evolution_inequality_of_ricci_lower_bound (I := I) (M := M) (D := D) g
        hRic u hu hslice hlogslice hpos hpde hqOn hqslice hNOn hNslice hFslice
          (s := s) hsreg x₀ hgradF
      rw [hlapF_slice]
      exact h
    have hlapG : laplacianAt (I := I) Gfam s (G eps s) x₀ =
        s * laplacianAt (I := I) Gfam s (F s) x₀ := by
      have hGdef : (G eps s) = fun y : M => s • F s y - (Real.exp (2 * K * s) *
        (n / 2) + eps * s) := by
        funext y
        simp [G]
        ring
      have hconn : Gfam.connection s = LeviCivita (Gfam.metric s) := by
        simp [Gfam]
      have hcq : laplacianAt (I := I) Gfam s
          (fun _ : M => Real.exp (2 * K * s) * (n / 2) + eps * s) x₀ = 0 := by
        rw [laplacianAt_eq_delta (I := I) Gfam s contMDiff_const hconn]
        exact Δ_g_const (I := I) g (Real.exp (2 * K * s) * (n / 2) + eps * s) x₀
      have hscd : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun y : M => s • F s y) := by
        simpa [Pi.smul_apply] using contMDiff_const.mul hF_s_cd
      have hsub_cd : ContMDiff I 𝓘(ℝ, ℝ) ∞
          (fun y : M => s • F s y - (Real.exp (2 * K * s) * (n / 2) + eps * s)) :=
        hscd.sub contMDiff_const
      have hdiff : laplacianAt (I := I) Gfam s
          (fun y : M => s • F s y - (Real.exp (2 * K * s) * (n / 2) + eps * s)) x₀ =
          laplacianAt (I := I) Gfam s (s • F s) x₀ - laplacianAt (I := I) Gfam s
            (fun _ : M => Real.exp (2 * K * s) * (n / 2) + eps * s) x₀ := by
        exact laplacianAt_sub (I := I) Gfam s
          (f := fun y : M => s • F s y)
          (h := fun _ : M => Real.exp (2 * K * s) * (n / 2) + eps * s)
          (x := x₀)
          (fun y : M => hscd.mdifferentiableAt (x := y) (by norm_num))
          (fun y : M => (contMDiff_const : ContMDiff I 𝓘(ℝ, ℝ) ∞
            (fun _ : M => Real.exp (2 * K * s) * (n / 2) + eps * s)).mdifferentiableAt (x := y)
              (by norm_num))
          (gradientFun_mdiffAt (I := I) (Gfam.metric s) hscd x₀)
          (gradientFun_mdiffAt (I := I) (Gfam.metric s) (contMDiff_const : ContMDiff I 𝓘(ℝ, ℝ) ∞
            (fun _ : M => Real.exp (2 * K * s) * (n / 2) + eps * s)) x₀)
      have hlapS : laplacianAt (I := I) Gfam s (s • F s) x₀ =
          s * laplacianAt (I := I) Gfam s (F s) x₀ := by
        exact laplacianAt_smul (I := I) Gfam s s
          (fun y => hF_s_cd.mdifferentiableAt (x := y) (by simp))
          (gradientFun_mdiffAt (I := I) (Gfam.metric s) hF_s_cd x₀)
      rw [hGdef, hdiff, hcq, hlapS]
      ring
    have hineq : deriv (fun τ' : ℝ => G eps τ' x₀) s - laplacianAt (I := I) Gfam s (G eps s) x₀ ≤
        F s x₀ - (2 * s / n) * Real.exp (c2 * s) * (liYauQuantity g f s x₀)^2 -
          2 * K * Real.exp (2 * K * s) * (n / 2) - eps := by
      rw [hval, hlapG]
      have hlin2 : s * (deriv (fun τ' : ℝ => F τ' x₀) s - laplacianAt (I := I) Gfam s (F s) x₀) ≤
          s * (-(2 / n) * Real.exp (c2 * s) * (liYauQuantity g f s x₀)^2) :=
        mul_le_mul_of_nonneg_left hFle hspos.le
      have hrewrite : s * (-(2 / n) * Real.exp (c2 * s) * (liYauQuantity g f s x₀)^2) =
          -((2 * s / n) * Real.exp (c2 * s) * (liYauQuantity g f s x₀)^2) := by ring
      rw [hrewrite] at hlin2
      linarith
    have hnonneg : 0 ≤ deriv (fun τ' : ℝ => G eps τ' x₀) s -
        laplacianAt (I := I) Gfam s (G eps s) x₀ := by
      linarith [htime, hlap]
    have hneg : F s x₀ - (2 * s / n) * Real.exp (c2 * s) * (liYauQuantity g f s x₀)^2 -
        2 * K * Real.exp (2 * K * s) * (n / 2) - eps < 0 := by
      have hGpos' : 0 < s * F s x₀ - Real.exp (2 * K * s) * (n / 2) - eps * s := by
        simpa [G] using hmpos
      have hNge : 0 ≤ N s x₀ := metric_inner_nonneg g x₀ (gradientFun (I := I) g (f s) x₀)
      have hcoef : 0 ≤ 1 - Real.exp (c2 * s) := by
        have hc2le : c2 * s ≤ 0 := by
          dsimp [c2]
          exact mul_nonpos_of_nonpos_of_nonneg (by linarith) hspos.le
        exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr hc2le)
      have hqeq : liYauQuantity g f s x₀ = F s x₀ + (1 - Real.exp (c2 * s)) * N s x₀ := by
        have h := hFqN s
        linarith
      have hFq : F s x₀ ≤ liYauQuantity g f s x₀ := by
        rw [hqeq]
        have hprod : 0 ≤ (1 - Real.exp (c2 * s)) * N s x₀ := mul_nonneg hcoef hNge
        linarith
      exact hamilton_strict_neg_of_slab_positivity heps hspos hn_pos hK (by rfl) hGpos' hFq
    exact (lt_irrefl (0 : ℝ))
      (lt_of_le_of_lt (le_trans hnonneg hineq) hneg)
  simpa [G, F, N, f, n] using hG_nonpos eps heps

omit [SigmaCompactSpace M] in
theorem heat_solution_hamilton_differential_harnack_of_ricci_lower_bound_on
    [CompactSpace M]
    [VectorBundle ℝ E (TangentSpace I : M → Type _)]
    [ContMDiffVectorBundle (1 : WithTop ℕ∞) E (TangentSpace I : M → Type _) I]
    [NeZero (Module.finrank ℝ E)]
    {D : RealTimeInterval}
    (g : SmoothRiemannianMetric I M) {K : ℝ} (hK : 0 ≤ K)
    (hRic : ∀ x v, -K * g.inner x v v ≤ ricciTensor (I := I) g x v v)
    (u : ℝ → M → ℝ)
    (hu : IsHeatOnStationary D g u)
    (huClosed : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2) (D.carrier ×ˢ univ))
    (hpos : ∀ t : ℝ, t ∈ D.carrier → ∀ x : M, 0 < u t x)
    {t : ℝ} (ht : t ∈ D.regular) (ht0 : 0 < t)
    (hslabCarrier : Icc 0 t ⊆ D.carrier)
    (hslabRegular : Ioo 0 t ⊆ D.regular)
    (x : M) :
    g.inner x (gradientFun (I := I) g (u t) x) (gradientFun (I := I) g (u t) x) / (u t x ^ 2) -
      Real.exp (2 * K * t) * (deriv (fun s => u s x) t / u t x) ≤
        Real.exp (4 * K * t) * (Module.finrank ℝ E : ℝ) / (2 * t) := by
  classical
  let G : MetricConnectionFamily (I := I) (M := M) ℝ :=
    stationaryMetricFamily (I := I) (M := M) g
  have hGmetric : ∀ t : ℝ, G.metric t = g := by
    intro t
    dsimp [G]
    rfl
  have hGconn : ∀ t : ℝ, G.connection t = LeviCivita (G.metric t) := by
    intro t
    dsimp [G]
    rfl
  let f : ℝ → M → ℝ := fun s y => Real.log (u s y)
  have hFsq : ContinuousOn (fun p : ℝ × M =>
      p.1 * (Real.exp ((-(2 * K)) * p.1) *
        g.inner p.2 (gradientFun (I := I) g (fun y => Real.log (u p.1 y)) p.2)
          (gradientFun (I := I) g (fun y => Real.log (u p.1 y)) p.2) -
      deriv (fun σ : ℝ => Real.log (u σ p.2)) p.1))
      (Icc 0 t ×ˢ univ) :=
    hamiltonQuantity_mul_time_continuousOn (I := I) (M := M) (D := D) (K := K) g u huClosed
      hu.sliceSmooth hpos ht ht0 hslabCarrier hslabRegular
  let hlogslice : ∀ τ : ℝ, τ ∈ D.carrier → ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun y : M => f τ y) :=
    fun τ hτ => Moser.contMDiff_log_of_pos_slice (hu.sliceSmooth τ hτ) (hpos τ hτ)
  let q : ℝ → M → ℝ := fun τ y => liYauQuantity g f τ y
  have hqOn : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => q p.1 p.2) (D.regular ×ˢ univ) := by
    simpa [f, q] using liYauQuantity_contMDiff (I := I) (M := M) (D := D) g u
      hu.jointSmooth hu.sliceSmooth hpos
  have hqslice : ∀ τ : ℝ, τ ∈ D.regular → ContMDiff I 𝓘(ℝ, ℝ) ∞ (q τ) := by
    intro τ hτ x
    have hnh : D.regular ×ˢ univ ∈ 𝓝 (τ, x) :=
      (IsOpen.prod D.regular_isOpen isOpen_univ).mem_nhds ⟨hτ, trivial⟩
    have hqat : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => q p.1 p.2) (τ, x) := hqOn.contMDiffAt hnh
    exact (hqat.comp (x := x) (contMDiffAt_const.prodMk contMDiffAt_id))
  have hpd_all : ∀ (τ : ℝ) (hτ : τ ∈ D.regular) (x : M),
      HasDerivAt (fun s => u s x)
        (deltaLegacy (I := I) g (hu.sliceSmooth τ (D.regular_subset hτ)) x) τ := by
    intro τ hτ x
    have heq := hu.equation τ hτ x
    have hbridge : laplacianAt (I := I) G τ (u τ) x =
        deltaLegacy (I := I) g (hu.sliceSmooth τ (D.regular_subset hτ)) x := by
      rw [laplacianAt_eq_delta (I := I) G τ (hu.sliceSmooth τ (D.regular_subset hτ))
        (hGconn τ) x]
      rw [hGmetric τ]
    have heq0 : HasDerivAt (fun s => u s x) (laplacianAt (I := I) G τ (u τ) x) τ := by
      simpa using heq
    exact heq0.congr_deriv hbridge
  let N : ℝ → M → ℝ := fun s y => g.inner y (gradientFun (I := I) g (f s) y)
        (gradientFun (I := I) g (f s) y)
  let n : ℝ := (Module.finrank ℝ E : ℝ)
  have hn_pos : 0 < n := by
    dsimp [n]
    exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E)))
  let F : ℝ → M → ℝ := fun s y => Real.exp ((-(2 * K)) * s) * N s y - deriv (fun σ : ℝ => f σ y) s
  have hvec : ∀ (τ : ℝ) (y : M), gradientFun (I := I) g (f τ) y = gradFun (I := I) g (f τ) y := by
    intro τ y
    apply (metricFlatEquiv (I := I) g y).injective
    ext w
    change g.inner y (gradientFun (I := I) g (f τ) y) w = g.inner y (gradFun (I := I) g (f τ) y) w
    rw [inner_gradientFun (I := I) g (f τ) y w]
    rw [inner_gradFun (I := I) g (f τ) y w]
  have hN_eq : ∀ (τ : ℝ) (y : M), N τ y = normGradSqFun (I := I) g (f τ) y := by
    intro τ y
    unfold N normGradSqFun
    rw [hvec τ y]
  have hlog' : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => f p.1 p.2) (D.regular ×ˢ univ) := by
    intro p hp
    have hnh : D.regular ×ˢ univ ∈ 𝓝 p :=
      (IsOpen.prod D.regular_isOpen isOpen_univ).mem_nhds ⟨hp.1, trivial⟩
    have hlogAt : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => Real.log (u p.1 p.2)) p :=
      (Real.contDiffAt_log.2 (hpos p.1 (D.regular_subset hp.1) p.2).ne').comp_contMDiffAt
        (x := p) (hu.jointSmooth.contMDiffAt hnh)
    simpa [f] using hlogAt.contMDiffWithinAt
  have hNOn : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => N p.1 p.2) (D.regular ×ˢ univ) := by
    have hNnorm : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => normGradSqFun (I := I) g (f p.1) p.2)
        (D.regular ×ˢ univ) := by
      exact normGradSqFun_contMDiffOn (I := I) (M := M) (D := D) g f hlog'
        (fun τ hτ => hlogslice τ (D.regular_subset hτ))
    exact hNnorm.congr (by intro p hp; rw [hN_eq p.1 p.2])
  have hNslice : ∀ τ : ℝ, τ ∈ D.regular → ContMDiff I 𝓘(ℝ, ℝ) ∞ (N τ) := by
    intro τ hτ x
    have hnh : D.regular ×ˢ univ ∈ 𝓝 (τ, x) :=
      (IsOpen.prod D.regular_isOpen isOpen_univ).mem_nhds ⟨hτ, trivial⟩
    have hNat : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => N p.1 p.2) (τ, x) := hNOn.contMDiffAt hnh
    exact (hNat.comp (x := x) (contMDiffAt_const.prodMk contMDiffAt_id))
  have hF_eq : ∀ (τ : ℝ) (y : M), F τ y = q τ y + (Real.exp ((-(2 * K)) * τ) - 1) * N τ y := by
    intro τ y
    unfold F q N liYauQuantity
    ring
  have hFOn : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => F p.1 p.2) (D.regular ×ˢ univ) := by
    have hcoeff : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => Real.exp ((-(2 * K)) * p.1) - 1) (D.regular ×ˢ univ) := by
      have hlin : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
          (fun p : ℝ × M => (-(2 * K)) * p.1) (D.regular ×ˢ univ) :=
        (contMDiffOn_const.mul contMDiffOn_fst)
      have hexp : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
          (fun p : ℝ × M => Real.exp ((-(2 * K)) * p.1)) (D.regular ×ˢ univ) :=
        (Real.contDiff_exp.contMDiff : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ Real.exp).comp_contMDiffOn hlin
      exact hexp.sub contMDiffOn_const
    have hFalt : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => q p.1 p.2 + (Real.exp ((-(2 * K)) * p.1) - 1) * N p.1 p.2)
        (D.regular ×ˢ univ) := hqOn.add (hcoeff.mul hNOn)
    exact hFalt.congr (by intro p hp; rw [hF_eq p.1 p.2])
  have hFslice : ∀ τ : ℝ, τ ∈ D.regular → ContMDiff I 𝓘(ℝ, ℝ) ∞ (F τ) := by
    intro τ hτ x
    have hnh : D.regular ×ˢ univ ∈ 𝓝 (τ, x) :=
      (IsOpen.prod D.regular_isOpen isOpen_univ).mem_nhds ⟨hτ, trivial⟩
    have hFat : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => F p.1 p.2) (τ, x) := hFOn.contMDiffAt hnh
    exact (hFat.comp (x := x) (contMDiffAt_const.prodMk contMDiffAt_id))
  let G : ℝ → ℝ → M → ℝ := fun eps s y => s * F s y - Real.exp (2 * K * s) * (n / 2) - eps * s
  have hG_nonpos : ∀ eps : ℝ, 0 < eps → G eps t x ≤ 0 := by
    intro eps heps
    have h := hamilton_quantity_slab_bound_of_ricci_lower_bound (I := I) (M := M) (D := D) g
      (hK := hK) hRic u hu.jointSmooth hu.sliceSmooth hlogslice hpos hpd_all
      hqOn hqslice hNOn hNslice hFOn hFslice heps ht0 hFsq ht hslabRegular x
    simpa [G, F, N, f, n] using h
  have hfin : ∀ eps : ℝ, 0 < eps → G eps t x ≤ 0 := hG_nonpos
  have hFt : F t x ≤ Real.exp (2 * K * t) * (n / 2) / t := by
    have hle0 : t * F t x - Real.exp (2 * K * t) * (n / 2) ≤ 0 := by
      by_contra hnot
      have hpos : 0 < t * F t x - Real.exp (2 * K * t) * (n / 2) := lt_of_not_ge hnot
      let eps : ℝ := (t * F t x - Real.exp (2 * K * t) * (n / 2)) / (2 * t)
      have heps_pos : 0 < eps := div_pos hpos (mul_pos zero_lt_two ht0)
      have hfin_eps : G eps t x ≤ 0 := hfin eps heps_pos
      have hle : t * F t x - Real.exp (2 * K * t) * (n / 2) ≤ eps * t := by
        simpa [G, eps] using hfin_eps
      have hrewrite : eps * t = (t * F t x - Real.exp (2 * K * t) * (n / 2)) / 2 := by
        dsimp [eps]
        field_simp [ht0.ne']
      have heps_lt : eps * t < t * F t x - Real.exp (2 * K * t) * (n / 2) := by
        rw [hrewrite]
        linarith
      exact (not_le_of_gt heps_lt) hle
    have htle : t * F t x ≤ Real.exp (2 * K * t) * (n / 2) := by linarith
    exact (le_div_iff₀ ht0).mpr (by simpa [mul_comm] using htle)
  have hlogderiv : deriv (fun s => Real.log (u s x)) t = deriv (fun s => u s x) t / u t x := by
    have hder : HasDerivAt (fun s => u s x) (deriv (fun s => u s x) t) t := by
      exact (hu.equation t ht x).congr_deriv (hu.equation t ht x).deriv.symm
    exact (hder.log (hpos t (D.regular_subset ht) x).ne').deriv
  have hloggrad : g.inner x (gradientFun (I := I) g (fun y => Real.log (u t y)) x)
        (gradientFun (I := I) g (fun y => Real.log (u t y)) x) =
      (u t x ^ 2)⁻¹ * g.inner x (gradientFun (I := I) g (u t) x)
        (gradientFun (I := I) g (u t) x) := by
    have hu_slice_mdiff : MDifferentiableAt I 𝓘(ℝ, ℝ) (u t) x :=
      (hu.sliceSmooth t (D.regular_subset ht)).mdifferentiableAt (x := x) (by simp)
    exact DifferentialGeometry.Analysis.Parabolic.Moser.inner_gradientFun_log_self (I := I) g
      hu_slice_mdiff (hpos t (D.regular_subset ht) x)
  have hFrewrite : F t x =
      Real.exp ((-(2 * K)) * t) * (u t x ^ 2)⁻¹ *
          g.inner x (gradientFun (I := I) g (u t) x) (gradientFun (I := I) g (u t) x) -
        deriv (fun s => u s x) t / u t x := by
    calc
      F t x = Real.exp ((-(2 * K)) * t) * N t x - deriv (fun σ : ℝ => f σ x) t := by
        rfl
      _ = Real.exp ((-(2 * K)) * t) *
              ((u t x ^ 2)⁻¹ *
                g.inner x (gradientFun (I := I) g (u t) x) (gradientFun (I := I) g (u t) x)) -
            deriv (fun s => u s x) t / u t x := by
          change Real.exp ((-(2 * K)) * t) *
                (g.inner x (gradientFun (I := I) g (f t) x) (gradientFun (I := I) g (f t) x)) -
              deriv (fun σ : ℝ => f σ x) t =
            Real.exp ((-(2 * K)) * t) * ((u t x ^ 2)⁻¹ *
                g.inner x (gradientFun (I := I) g (u t) x) (gradientFun (I := I) g (u t) x)) -
              deriv (fun s => u s x) t / u t x
          rw [hloggrad, hlogderiv]
      _ = Real.exp ((-(2 * K)) * t) * (u t x ^ 2)⁻¹ *
              g.inner x (gradientFun (I := I) g (u t) x) (gradientFun (I := I) g (u t) x) -
            deriv (fun s => u s x) t / u t x := by ring
  have hmain : Real.exp ((-(2 * K)) * t) * (u t x ^ 2)⁻¹ *
        g.inner x (gradientFun (I := I) g (u t) x) (gradientFun (I := I) g (u t) x) -
      deriv (fun s => u s x) t / u t x ≤ Real.exp (2 * K * t) * (n / 2) / t := by
    rwa [hFrewrite] at hFt
  have hgoal : g.inner x (gradientFun (I := I) g (u t) x) (gradientFun (I := I) g (u t) x) /
        (u t x ^ 2) - Real.exp (2 * K * t) * (deriv (fun s => u s x) t / u t x) ≤
      Real.exp (4 * K * t) * (Module.finrank ℝ E : ℝ) / (2 * t) := by
    calc
      g.inner x (gradientFun (I := I) g (u t) x) (gradientFun (I := I) g (u t) x) / (u t x ^ 2) -
            Real.exp (2 * K * t) * (deriv (fun s => u s x) t / u t x)
          = Real.exp (2 * K * t) *
              (Real.exp ((-(2 * K)) * t) * (u t x ^ 2)⁻¹ *
                  g.inner x (gradientFun (I := I) g (u t) x) (gradientFun (I := I) g (u t) x) -
                deriv (fun s => u s x) t / u t x) := by
            have hu_ne : u t x ≠ 0 := ne_of_gt (hpos t (D.regular_subset ht) x)
            have hexp : Real.exp (2 * K * t) * Real.exp ((-(2 * K)) * t) = 1 := by
              rw [show (-(2 * K)) * t = -(2 * K * t) by ring]
              rw [Real.exp_neg]
              exact mul_inv_cancel₀ (ne_of_gt (Real.exp_pos _))
            have hstep1 : g.inner x (gradientFun (I := I) g (u t) x)
                  (gradientFun (I := I) g (u t) x) / (u t x ^ 2) =
                Real.exp (2 * K * t) * Real.exp ((-(2 * K)) * t) * (u t x ^ 2)⁻¹ *
                  g.inner x (gradientFun (I := I) g (u t) x) (gradientFun (I := I) g (u t) x) := by
              rw [hexp]
              field_simp [hu_ne]
            calc
              g.inner x (gradientFun (I := I) g (u t) x) (gradientFun (I := I) g (u t) x) /
                    (u t x ^ 2) - Real.exp (2 * K * t) * (deriv (fun s => u s x) t / u t x)
                  = Real.exp (2 * K * t) * Real.exp ((-(2 * K)) * t) * (u t x ^ 2)⁻¹ *
                        g.inner x (gradientFun (I := I) g (u t) x) (gradientFun (I := I) g
                          (u t) x) -
                      Real.exp (2 * K * t) * (deriv (fun s => u s x) t / u t x) := by
                    rw [hstep1]
              _ = Real.exp (2 * K * t) *
                    (Real.exp ((-(2 * K)) * t) * (u t x ^ 2)⁻¹ *
                        g.inner x (gradientFun (I := I) g (u t) x) (gradientFun (I := I) g
                          (u t) x) -
                      deriv (fun s => u s x) t / u t x) := by ring
      _ ≤ Real.exp (2 * K * t) * (Real.exp (2 * K * t) * (n / 2) / t) := by
        exact mul_le_mul_of_nonneg_left hmain (le_of_lt (Real.exp_pos _))
      _ = Real.exp (4 * K * t) * (Module.finrank ℝ E : ℝ) / (2 * t) := by
        have hexp2 : Real.exp (2 * K * t) ^ 2 = Real.exp (4 * K * t) := by
          rw [pow_two]
          rw [← Real.exp_add]
          rw [show 2 * K * t + 2 * K * t = 4 * K * t by ring]
        dsimp [n]
        calc
          Real.exp (2 * K * t) * (Real.exp (2 * K * t) * ((Module.finrank ℝ E : ℝ) / 2) / t)
              = Real.exp (2 * K * t) ^ 2 * ((Module.finrank ℝ E : ℝ) / 2) / t := by ring
          _ = Real.exp (4 * K * t) * ((Module.finrank ℝ E : ℝ) / 2) / t := by rw [hexp2]
          _ = Real.exp (4 * K * t) * (Module.finrank ℝ E : ℝ) / (2 * t) := by field_simp [ht0.ne']
  exact hgoal

omit [SigmaCompactSpace M] in
theorem heat_solution_hamilton_differential_harnack_of_ricci_lower_bound
    [CompactSpace M]
    [VectorBundle ℝ E (TangentSpace I : M → Type _)]
    [ContMDiffVectorBundle (1 : WithTop ℕ∞) E (TangentSpace I : M → Type _) I]
    [NeZero (Module.finrank ℝ E)]
    (g : SmoothRiemannianMetric I M) {K : ℝ} (hK : 0 ≤ K)
    (hRic : ∀ x v, -K * g.inner x v v ≤ ricciTensor (I := I) g x v v)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ (fun p : ℝ × M => u p.1 p.2))
    (hpos : ∀ t x, 0 < u t x)
    (hpde : ∀ t x, deriv (fun s => u s x) t =
      Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).toContMDiffMap x)
    {t : ℝ} (ht : 0 < t) (x : M) :
    g.inner x (gradientFun (I := I) g (u t) x) (gradientFun (I := I) g (u t) x) / (u t x ^ 2) -
      Real.exp (2 * K * t) * (deriv (fun s => u s x) t / u t x) ≤
        Real.exp (4 * K * t) * (Module.finrank ℝ E : ℝ) / (2 * t) := by
  classical
  let D : RealTimeInterval := RealTimeInterval.univ 0
  let Gfam : MetricConnectionFamily (I := I) (M := M) ℝ :=
    stationaryMetricFamily (I := I) (M := M) g
  have hGmetric : ∀ τ : ℝ, τ ∈ D.carrier → Gfam.metric τ = g := by
    intro τ hτ
    dsimp [Gfam]
    rfl
  have hGconn : ∀ τ : ℝ, τ ∈ D.carrier → Gfam.connection τ = LeviCivita (Gfam.metric τ) := by
    intro τ hτ
    dsimp [Gfam]
    rfl
  have huOn : IsHeatOn D Gfam u := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [D] using hu.contMDiffOn
    · exact hu.continuous.continuousOn
    · intro τ hτ
      exact hu.comp (contMDiff_const.prodMk contMDiff_id)
    · intro τ hτ x
      have hslice_cd : ContDiff ℝ ∞ (fun s => u s x) :=
        contMDiff_iff_contDiff.mp (hu.comp (contMDiff_id.prodMk contMDiff_const))
      have hder : HasDerivAt (fun s => u s x) (deriv (fun s => u s x) τ) τ :=
        (ContDiff.differentiable hslice_cd (by norm_num) τ).hasDerivAt
      have hlap : laplacianAt (I := I) Gfam τ (u τ) x =
          Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu τ).toContMDiffMap x := by
        change laplacianAt (I := I) Gfam τ (smoothScalarSlice (I := I) g u hu τ).toFun x =
          Δ_g (I := I) g
            ⟨(smoothScalarSlice (I := I) g u hu τ).toFun,
              (smoothScalarSlice (I := I) g u hu τ).smooth⟩ x
        rw [laplacianAt_eq_delta (I := I) Gfam τ (smoothScalarSlice (I := I) g u hu τ).smooth
          (hGconn τ hτ) x]
        rw [hGmetric τ hτ]
      have hderiv : deriv (fun s => u s x) τ = laplacianAt (I := I) Gfam τ (u τ) x := by
        rw [hpde τ x, ← hlap]
      convert hder.congr_deriv hderiv using 1
      simp
  let f : ℝ → M → ℝ := fun s y => Real.log (u s y)
  let hlog : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => f p.1 p.2) := by
    simpa [f] using DifferentialGeometry.Analysis.Parabolic.Moser.contMDiff_log_of_pos hu hpos
  let hq : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => liYauQuantity g f p.1 p.2) := by
    have hqOn : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => liYauQuantity g f p.1 p.2) univ := by
      simpa [f, D,
        RealTimeInterval.univ] using liYauQuantity_contMDiff (I := I) (M := M)
        (D := D) g u hu.contMDiffOn
        (fun τ hτ => hu.comp (contMDiff_const.prodMk contMDiff_id)) (fun τ hτ x => hpos τ x)
    simpa [f] using contMDiffOn_univ.mp hqOn
  let hft_cd : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => deriv (fun σ : ℝ => f σ p.2) p.1) := by
    simpa [f] using (DifferentialGeometry.contMDiff_partial_deriv_fst I
      ⟨fun p : ℝ × M => Real.log (u p.1 p.2),
        DifferentialGeometry.Analysis.Parabolic.Moser.contMDiff_log_of_pos hu hpos⟩)
  let N : ℝ → M → ℝ := fun s y => g.inner y (gradientFun (I := I) g (f s) y)
        (gradientFun (I := I) g (f s) y)
  let hN : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => N p.1 p.2) := by
    have hfun : (fun p : ℝ × M => N p.1 p.2) =
        (fun p : ℝ × M => liYauQuantity g f p.1 p.2 + deriv (fun σ : ℝ => f σ p.2) p.1) := by
      funext p
      simp [N, f, liYauQuantity]
    rw [hfun]
    exact hq.add hft_cd
  let F : ℝ → M → ℝ := fun s y => Real.exp ((-(2 * K)) * s) * N s y - deriv (fun σ : ℝ => f σ y) s
  let hF : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => F p.1 p.2) := by
    have hlin : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => (-(2 * K)) * p.1) := by
      have hc : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
          ((fun _ : ℝ × M => (-(2 * K))) * Prod.fst) :=
        (contMDiff_const (c := (-(2 * K)))).mul contMDiff_fst
      refine ContMDiff.congr hc ?_
      intro p
      rfl
    have hexp : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => Real.exp ((-(2 * K)) * p.1)) := by
      simpa using ((Real.contDiff_exp.contMDiff : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ Real.exp).comp hlin)
    have hterm1 : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => Real.exp ((-(2 * K)) * p.1) * N p.1 p.2) := hexp.mul hN
    change ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => Real.exp ((-(2 * K)) * p.1) * N p.1 p.2 - deriv (fun σ : ℝ => f σ p.2) p.1)
    exact hterm1.sub hft_cd
  have hNOn : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => N p.1 p.2) (D.regular ×ˢ univ) := by
    simpa [D] using hN.contMDiffOn
  have hNslice : ∀ τ : ℝ, τ ∈ D.regular → ContMDiff I 𝓘(ℝ, ℝ) ∞ (N τ) := by
    intro τ hτ
    exact hN.comp (contMDiff_const.prodMk contMDiff_id)
  have hFOn : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => F p.1 p.2) (D.regular ×ˢ univ) := by
    simpa [D] using hF.contMDiffOn
  have hFslice : ∀ τ : ℝ, τ ∈ D.regular → ContMDiff I 𝓘(ℝ, ℝ) ∞ (F τ) := by
    intro τ hτ
    exact hF.comp (contMDiff_const.prodMk contMDiff_id)
  simpa [D, Gfam] using
    heat_solution_hamilton_differential_harnack_of_ricci_lower_bound_on
    (I := I) (M := M) (D := D) g (K := K) hK hRic u huOn
    (by simpa [D] using hu.contMDiffOn)
    (fun τ hτ x => hpos τ x) (t := t) (by change t ∈ (Set.univ : Set ℝ); trivial)
    ht (by intro τ hτ; trivial) (by intro τ hτ; trivial)
    x

end DifferentialGeometry.Analysis.Parabolic.Harnack

end
