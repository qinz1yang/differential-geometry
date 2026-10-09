import DifferentialGeometry.Geometry.Thurston.EquivariantRoundMetricA5GaugeFlow
import DifferentialGeometry.Analysis.Integration.L2.Parametric.FiberInnerSmoothness
import DifferentialGeometry.Analysis.Integration.Measure.Parametric.FiniteIntegral
import DifferentialGeometry.Analysis.Integration.Measure.VolumeDensityFamily
import DifferentialGeometry.Geometry.Coordinates.Fields.Scalar
import Mathlib.MeasureTheory.Constructions.UnitInterval

/-!
# Time integrals, moving means and linear ODEs for the potential gauge

Chapter 7, packet P8, surface lemma U1, route (a), step a5.2 (i) (potential gauge, design D18,
errata "route change for (i)"). Calculus inputs of the pointwise ODE route:
* `contMDiffAt_prod_of_chart`: joint smoothness on `ℝ × M` from the chart expression;
* `contDiffOn_intervalIntegral_param`, `contMDiffOn_intervalIntegral_time`: `∫_{t₀}^t G(s, x) ds`
  is jointly smooth (substitution `s = t₀ + u (t - t₀)` and
  `contDiffOn_integral_subtype_of_isCompact` over `u ∈ [0, 1]`);
* `contDiffOn_integral_of_contMDiffOn_Ioo`, `surfaceFlow_contDiffOn_integral`: `t ↦ ∫_M G(t) dμ`
  is smooth on `(0, T)` for a fixed finite measure and for `dμ_{g(t)}`
  (`contDiffOn_integral_of_jointContMDiffOn_Icc`, `riemannianVolumeDensity_family_contMDiffOn`);
* `eqOn_zero_of_hasDerivAt_mul`: a solution of `P' = k P` on an open interval vanishing at one
  point vanishes identically.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.PDE.RicciFlow
open MeasureTheory Filter Topology Set
open scoped Manifold ContDiff

namespace GC.Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [CompactSpace M]
  {T : ℝ} {hT : 0 < T}

private local instance potentialMeasurable : MeasurableSpace M := borel M
private local instance potentialBorel : BorelSpace M := ⟨rfl⟩

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M]
  [CompactSpace M] in
theorem contMDiffAt_prod_of_chart {F : ℝ → M → ℝ} {t₀ : ℝ} {x₀ : M}
    (h : ContDiffAt ℝ ∞ (fun p : ℝ × E => F p.1 ((extChartAt I x₀).symm p.2))
      (t₀, extChartAt I x₀ x₀)) :
    ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ (fun p : ℝ × M => F p.1 p.2) (t₀, x₀) := by
  have hmap : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ × E) ∞
      (fun p : ℝ × M => (p.1, extChartAt I x₀ p.2)) (t₀, x₀) :=
    contMDiffAt_fst.prodMk_space
      ((contMDiffAt_extChartAt (I := I) (x := x₀)).comp (t₀, x₀) contMDiffAt_snd)
  have hc := ContDiffAt.comp_contMDiffAt
    (g := fun p : ℝ × E => F p.1 ((extChartAt I x₀).symm p.2))
    (f := fun p : ℝ × M => (p.1, extChartAt I x₀ p.2)) (x := (t₀, x₀)) h hmap
  refine hc.congr_of_eventuallyEq ?_
  have hsrc : {p : ℝ × M | p.2 ∈ (extChartAt I x₀).source} ∈ 𝓝 (t₀, x₀) :=
    continuousAt_snd.preimage_mem_nhds
      ((isOpen_extChartAt_source x₀).mem_nhds (mem_extChartAt_source x₀))
  filter_upwards [hsrc] with p hp
  simp only [Function.comp_apply, (extChartAt I x₀).left_inv hp]

theorem contDiffOn_intervalIntegral_param {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {a b t₀ : ℝ} (h0 : t₀ ∈ Ioo a b) {U : Set V} (hU : IsOpen U) {G : ℝ × V → ℝ}
    (hG : ContDiffOn ℝ ∞ G (Ioo a b ×ˢ U)) :
    ContDiffOn ℝ ∞ (fun p : ℝ × V => ∫ s in t₀..p.1, G (s, p.2)) (Ioo a b ×ˢ U) := by
  let φ : (ℝ × V) × ℝ → ℝ × V := fun q => ((q.1.1 - t₀) * q.2 + t₀, q.1.2)
  have hφ : ContDiff ℝ ∞ φ :=
    (((contDiff_fst.fst.sub contDiff_const).mul contDiff_snd).add contDiff_const).prodMk
      contDiff_fst.snd
  have hΩ : IsOpen (φ ⁻¹' (Ioo a b ×ˢ U)) := (isOpen_Ioo.prod hU).preimage hφ.continuous
  have hsub : (Ioo a b ×ˢ U) ×ˢ Icc (0 : ℝ) 1 ⊆ φ ⁻¹' (Ioo a b ×ˢ U) := by
    rintro ⟨⟨t, y⟩, u⟩ ⟨⟨ht, hy⟩, hu⟩
    refine ⟨?_, hy⟩
    have he : (t - t₀) * u + t₀ = (1 - u) * t₀ + u * t := by ring
    change (t - t₀) * u + t₀ ∈ Ioo a b
    rw [he]
    exact (convex_Ioo a b) h0 ht (by linarith [hu.2]) hu.1 (by ring)
  have hf : ContDiffOn ℝ ∞ (G ∘ φ) (φ ⁻¹' (Ioo a b ×ˢ U)) :=
    hG.comp hφ.contDiffOn (fun _ hq => hq)
  have hint := contDiffOn_integral_subtype_of_isCompact (⊤ : ℕ∞) isCompact_Icc
    (volume : Measure unitInterval) (isOpen_Ioo.prod hU) hΩ hsub hf
  have hmul := (contDiffOn_fst.sub (contDiffOn_const (c := t₀))).mul hint
  refine hmul.congr ?_
  rintro ⟨t, y⟩ -
  have hsub' := intervalIntegral.smul_integral_comp_mul_add (a := 0) (b := 1)
    (fun s => G (s, y)) (t - t₀) t₀
  simp only [mul_zero, zero_add, mul_one, sub_add_cancel, smul_eq_mul] at hsub'
  change (∫ s in t₀..t, G (s, y)) = (t - t₀) * ∫ u : unitInterval, G ((t - t₀) * u + t₀, y)
  rw [← hsub', intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc,
    unitInterval.volume_def]
  congr 1
  exact (integral_subtype_comap measurableSet_Icc (fun u => G ((t - t₀) * u + t₀, y))).symm

omit [FiniteDimensional ℝ E] [T2Space M] [CompactSpace M] in
theorem contMDiffOn_intervalIntegral_time {a b t₀ : ℝ} (h0 : t₀ ∈ Ioo a b) (G : ℝ → M → ℝ)
    (hG : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ (fun q : ℝ × M => G q.1 q.2)
      (Ioo a b ×ˢ univ)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ (fun q : ℝ × M => ∫ s in t₀..q.1, G s q.2)
      (Ioo a b ×ˢ univ) := by
  rintro ⟨t, x⟩ ⟨ht, -⟩
  refine ContMDiffAt.contMDiffWithinAt ?_
  apply contMDiffAt_prod_of_chart (F := fun t x => ∫ s in t₀..t, G s x)
  have hc := scalarOnE_contDiffOn_prod (I := I) x hG
  have hi := contDiffOn_intervalIntegral_param h0 (isOpen_extChartAt_target (I := I) x) hc
  exact hi.contDiffAt ((isOpen_Ioo.prod (isOpen_extChartAt_target (I := I) x)).mem_nhds
    ⟨ht, mem_extChartAt_target (I := I) x⟩)

omit [FiniteDimensional ℝ E] [I.Boundaryless] in
theorem contDiffOn_integral_of_contMDiffOn_Ioo (μ : Measure M) [IsFiniteMeasure μ] {a b : ℝ}
    (G : ℝ → M → ℝ)
    (hG : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ (fun q : ℝ × M => G q.1 q.2)
      (Ioo a b ×ˢ univ)) :
    ContDiffOn ℝ ∞ (fun t => ∫ x, G t x ∂μ) (Ioo a b) := by
  intro t₁ ht₁
  set c := (a + t₁) / 2 with hc
  set d := (t₁ + b) / 2 with hd
  have hac : a < c := by rw [hc]; linarith [ht₁.1]
  have hct : c < t₁ := by rw [hc]; linarith [ht₁.1]
  have htd : t₁ < d := by rw [hd]; linarith [ht₁.2]
  have hdb : d < b := by rw [hd]; linarith [ht₁.2]
  have hmap : ContMDiff (I.prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod I) ∞ (fun p : M × ℝ => (c + p.2, p.1)) :=
    (contMDiff_const.add contMDiff_snd).prodMk contMDiff_fst
  have hf : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ (fun p : M × ℝ => G (c + p.2) p.1)
      (univ ×ˢ Icc (0 : ℝ) (d - c)) := by
    refine hG.comp hmap.contMDiffOn ?_
    rintro ⟨x, s⟩ ⟨-, hs⟩
    exact ⟨⟨by linarith [hs.1], by linarith [hs.2]⟩, mem_univ x⟩
  have hint := contDiffOn_integral_of_jointContMDiffOn_Icc μ (fun x s => G (c + s) x) hf
  have hat : ContDiffAt ℝ ∞ (fun s => ∫ x, G (c + s) x ∂μ) (t₁ - c) :=
    hint.contDiffAt (Icc_mem_nhds (by linarith) (by linarith))
  have hcomp := hat.comp t₁ (contDiffAt_id.sub contDiffAt_const)
  refine (hcomp.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)).contDiffWithinAt
  simp only [Function.comp_apply, id, add_sub_cancel]

omit [I.Boundaryless] in
theorem surfaceFlow_contDiffOn_integral
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 T hT)) (hS : IsSolutionOn S)
    (G : ℝ → M → ℝ)
    (hG : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ (fun q : ℝ × M => G q.1 q.2)
      (Ioo 0 T ×ˢ univ)) :
    ContDiffOn ℝ ∞ (fun t => ∫ x, G t x ∂riemannianVolumeMeasure I M (S.family.metric t))
      (Ioo 0 T) := by
  let q := S.family.metric (T / 2)
  let _ : IsFiniteMeasure (riemannianVolumeMeasure I M q) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) q
  have hρ : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => riemannianVolumeDensity q (S.family.metric p.1) p.2) (Ioo 0 T ×ˢ univ) :=
    riemannianVolumeDensity_family_contMDiffOn q S.family.metric isOpen_Ioo
      (fun α i j => hS.smoothMetric.chartGramMatrix_contDiffOn (G := S.family)
        (fun _ h => h) α i j)
  have hH := contDiffOn_integral_of_contMDiffOn_Ioo (riemannianVolumeMeasure I M q)
    (fun t x => riemannianVolumeDensity q (S.family.metric t) x * G t x) (hρ.mul hG)
  refine hH.congr fun t _ => ?_
  simpa only [smul_eq_mul] using
    integral_riemannianVolumeMeasure_eq_integral_volumeDensity_smul q (S.family.metric t) (G t)

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M]
  [T2Space M] [CompactSpace M] in
theorem eqOn_zero_of_hasDerivAt_mul {a b t₀ : ℝ} (h0 : t₀ ∈ Ioo a b) {P k : ℝ → ℝ}
    (hk : ContinuousOn k (Ioo a b)) (hP : ∀ t ∈ Ioo a b, HasDerivAt P (k t * P t) t)
    (hP0 : P t₀ = 0) : ∀ t ∈ Ioo a b, P t = 0 := by
  let K : ℝ → ℝ := fun t => ∫ s in t₀..t, k s
  have hK : ∀ t ∈ Ioo a b, HasDerivAt K (k t) t := by
    intro t ht
    have hsub : uIcc t₀ t ⊆ Ioo a b := (ordConnected_Ioo).uIcc_subset h0 ht
    exact intervalIntegral.integral_hasDerivAt_right ((hk.mono hsub).intervalIntegrable)
      (hk.stronglyMeasurableAtFilter isOpen_Ioo t ht) (hk.continuousAt (isOpen_Ioo.mem_nhds ht))
  let Q : ℝ → ℝ := fun t => P t * Real.exp (-K t)
  have hQ : ∀ t ∈ Ioo a b, HasDerivAt Q 0 t := by
    intro t ht
    have he := ((hK t ht).neg).exp
    have h := (hP t ht).mul he
    refine h.congr_deriv ?_
    ring
  intro t ht
  have hQt : Q t = Q t₀ := isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
    (fun t ht => (hQ t ht).differentiableAt.differentiableWithinAt)
    (fun t ht => (hQ t ht).deriv) ht h0
  have hQ0 : Q t₀ = 0 := by simp only [Q, hP0, zero_mul]
  have hpos : 0 < Real.exp (-K t) := Real.exp_pos _
  have hzero : P t * Real.exp (-K t) = 0 := hQt.trans hQ0
  rcases mul_eq_zero.mp hzero with h | h
  · exact h
  · exact absurd h hpos.ne'

end GC.Geometry

end
