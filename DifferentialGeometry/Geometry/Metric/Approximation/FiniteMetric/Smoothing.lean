import DifferentialGeometry.Analysis.Calculus.MapConvergence.Derivative
import DifferentialGeometry.Bundle.Hom
import DifferentialGeometry.Geometry.Metric.Construction.SmoothMetricFromCoefficients
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Chart
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-!
# Gluing chartwise bilinear fields into a smooth metric (LFR50, part A1, first half)

For a finite-regularity Riemannian metric `g` (a `Bundle.ContMDiffRiemannianMetric I n`) on a
manifold with a boundaryless model, `chartCoeff g p` is the coefficient field of `g` in the
extended chart at `p`: `y ↦ g((φ_p)⁻¹ y)(D(φ_p)⁻¹ ·, D(φ_p)⁻¹ ·)`. This file proves

* the chart calculus used below (chain rule for chart transitions, frames in charts);
* `chartCoeff_transition`: the transformation law of chart coefficients under a transition;
* `contDiffOn_chartCoeff`: the coefficients of a `C^n` metric, `2 ≤ n`, are `C²` on the chart
  target;
* `exists_smoothMetric_glued`: smooth symmetric positive bilinear fields `G i` on the model
  space, pulled back by the charts at finitely many points `c i` and glued by a smooth
  partition of unity subordinate to the chart sources, form a smooth Riemannian metric;
* `chartCoeff_glued` and `chartCoeff_eq_sum_transition`: the chart coefficients of the glued
  metric and of `g` in any chart, as partition-of-unity sums over the transitions.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.Geometry.MetricSmoothing

open DifferentialGeometry.CheegerGromovCompactness (pullbackForm pullbackForm_apply)

section ChartCalculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem mdifferentiableAt_extChartAt_symm_of_mem (q : M) {y : E}
    (hy : y ∈ (extChartAt I q).target) :
    MDifferentiableAt 𝓘(ℝ, E) I (extChartAt I q).symm y :=
  ((contMDiffOn_extChartAt_symm (n := ∞) q).contMDiffAt
    ((isOpen_extChartAt_target q).mem_nhds hy)).mdifferentiableAt (by simp)

/-- The transition between the extended charts at `q` and `p`, as a map of the model space. -/
def chartTransition (p q : M) : E → E := (extChartAt I p) ∘ (extChartAt I q).symm

/-- The open set of the chart at `q` on which the transition to the chart at `p` is defined. -/
def transitionDomain (p q : M) : Set E :=
  (extChartAt I q).target ∩ (extChartAt I q).symm ⁻¹' (extChartAt I p).source

omit [IsManifold I ∞ M] in
theorem isOpen_transitionDomain (p q : M) : IsOpen (transitionDomain (I := I) p q) :=
  (continuousOn_extChartAt_symm q).isOpen_inter_preimage (isOpen_extChartAt_target q)
    (isOpen_extChartAt_source p)

omit [I.Boundaryless] in
theorem contDiffOn_chartTransition (p q : M) :
    ContDiffOn ℝ ∞ (chartTransition (I := I) p q) (transitionDomain (I := I) p q) := by
  have h : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (chartTransition (I := I) p q)
      (transitionDomain (I := I) p q) :=
    (contMDiffOn_extChartAt (n := ∞) (x := p)).comp
      ((contMDiffOn_extChartAt_symm (n := ∞) q).mono inter_subset_left)
      (fun y hy => by simpa only [extChartAt_source] using hy.2)
  exact contMDiffOn_iff_contDiffOn.mp h

omit [I.Boundaryless] [IsManifold I ∞ M] in
theorem chartTransition_mapsTo (p q : M) :
    MapsTo (chartTransition (I := I) p q) (transitionDomain (I := I) p q)
      (extChartAt I p).target :=
  fun _ hy => (extChartAt I p).map_source hy.2

theorem mfderiv_extChartAt_comp_symm (p q : M) {y : E}
    (hy : y ∈ transitionDomain (I := I) p q) :
    (mfderiv I 𝓘(ℝ, E) (extChartAt I p) ((extChartAt I q).symm y) : E →L[ℝ] E).comp
        (mfderiv 𝓘(ℝ, E) I (extChartAt I q).symm y : E →L[ℝ] E) =
      fderiv ℝ (chartTransition (I := I) p q) y := by
  have h1 : MDifferentiableAt I 𝓘(ℝ, E) (extChartAt I p) ((extChartAt I q).symm y) :=
    mdifferentiableAt_extChartAt (by
      have h := hy.2
      rw [mem_preimage, extChartAt_source] at h
      exact h)
  have h2 := mdifferentiableAt_extChartAt_symm_of_mem (I := I) q hy.1
  have hc := (mfderiv_comp y h1 h2).symm
  rw [mfderiv_eq_fderiv] at hc
  ext v
  exact congrArg (fun L => L v) hc

theorem mfderiv_extChartAt_symm_comp_fderiv (p q : M) {y : E}
    (hy : y ∈ transitionDomain (I := I) p q) :
    ((mfderiv 𝓘(ℝ, E) I (extChartAt I p).symm (chartTransition (I := I) p q y) :
        E →L[ℝ] E).comp (fderiv ℝ (chartTransition (I := I) p q) y) : E →L[ℝ] E) =
      (mfderiv 𝓘(ℝ, E) I (extChartAt I q).symm y : E →L[ℝ] E) := by
  have hT : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) (chartTransition (I := I) p q) y :=
    ((contDiffOn_chartTransition (I := I) p q).contDiffAt
      ((isOpen_transitionDomain (I := I) p q).mem_nhds hy)).contMDiffAt.mdifferentiableAt
      (by simp)
  have hs := mdifferentiableAt_extChartAt_symm_of_mem (I := I) p
    (chartTransition_mapsTo (I := I) p q hy)
  have heq : (extChartAt I p).symm ∘ chartTransition (I := I) p q =ᶠ[𝓝 y]
      (extChartAt I q).symm := by
    filter_upwards [(isOpen_transitionDomain (I := I) p q).mem_nhds hy] with z hz
    exact (extChartAt I p).left_inv hz.2
  have hc := (mfderiv_comp y hs hT).symm.trans heq.mfderiv_eq
  rw [mfderiv_eq_fderiv] at hc
  ext v
  exact congrArg (fun L => L v) hc

variable [FiniteDimensional ℝ E]

theorem frameVec_eq_mfderiv (x₀ : M) (k : Fin (Module.finrank ℝ E)) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    DifferentialGeometry.Geometry.frameVec (I := I) x₀ k x =
      (mfderiv 𝓘(ℝ, E) I (extChartAt I x₀).symm (extChartAt I x₀ x) : E →L[ℝ] E)
        (Module.finBasis ℝ E k) := by
  have hx' : x ∈ (chartAt H x₀).source := by simpa using hx
  unfold DifferentialGeometry.Geometry.frameVec
  rw [TangentBundle.symmL_trivializationAt hx', I.range_eq_univ, mfderivWithin_univ]
  rfl

omit [FiniteDimensional ℝ E] in
theorem injective_mfderiv_extChartAt (p : M) {x : M} (hx : x ∈ (extChartAt I p).source) :
    Function.Injective (mfderiv I 𝓘(ℝ, E) (extChartAt I p) x) :=
  ((DifferentialGeometry.PartialDiffeomorph.extChartAt I ∞ p).isLocalDiffeomorphAt _ _ _ hx
    |>.mfderivToContinuousLinearEquiv (by simp)).injective

omit [FiniteDimensional ℝ E] in
theorem injective_mfderiv_extChartAt_symm (p : M) {y : E} (hy : y ∈ (extChartAt I p).target) :
    Function.Injective (mfderiv 𝓘(ℝ, E) I (extChartAt I p).symm y) :=
  ((DifferentialGeometry.PartialDiffeomorph.extChartAt I ∞ p).symm.isLocalDiffeomorphAt _ _ _
    hy |>.mfderivToContinuousLinearEquiv (by simp)).injective

end ChartCalculus

section ChartCoefficients

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The coefficient field of a finite-regularity metric in the extended chart at `p`. -/
def chartCoeff {n : ℕ∞ω} (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _))
    (p : M) (y : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  let D : E →L[ℝ] E := mfderiv 𝓘(ℝ, E) I (extChartAt I p).symm y
  let B : E →L[ℝ] E →L[ℝ] ℝ := g.inner ((extChartAt I p).symm y)
  B.bilinearComp D D

omit [I.Boundaryless] in
theorem chartCoeff_apply {n : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) (p : M) (y v w : E) :
    chartCoeff g p y v w = g.inner ((extChartAt I p).symm y)
      (mfderiv 𝓘(ℝ, E) I (extChartAt I p).symm y v)
      (mfderiv 𝓘(ℝ, E) I (extChartAt I p).symm y w) :=
  rfl

omit [I.Boundaryless] in
theorem chartCoeff_symm {n : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) (p : M) (y v w : E) :
    chartCoeff g p y v w = chartCoeff g p y w v := by
  rw [chartCoeff_apply, chartCoeff_apply]
  exact g.symm _ _ _

theorem chartCoeff_pos {n : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) (p : M) {y : E}
    (hy : y ∈ (extChartAt I p).target) {v : E} (hv : v ≠ 0) :
    0 < chartCoeff g p y v v := by
  apply g.pos
  intro h0
  exact hv (injective_mfderiv_extChartAt_symm (I := I) p hy (h0.trans (map_zero _).symm))

/-- **Transformation law** of chart coefficients under a chart transition. -/
theorem chartCoeff_transition {n : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) (p q : M) {y : E}
    (hy : y ∈ transitionDomain (I := I) p q) :
    chartCoeff g q y = pullbackForm (chartCoeff g p (chartTransition (I := I) p q y),
      fderiv ℝ (chartTransition (I := I) p q) y) := by
  have hd := mfderiv_extChartAt_symm_comp_fderiv (I := I) p q hy
  have hr : (extChartAt I p).symm (chartTransition (I := I) p q y) =
      (extChartAt I q).symm y := (extChartAt I p).left_inv hy.2
  ext v w
  have hv : (mfderiv 𝓘(ℝ, E) I (extChartAt I p).symm (chartTransition (I := I) p q y) :
      E →L[ℝ] E) (fderiv ℝ (chartTransition (I := I) p q) y v) =
      (mfderiv 𝓘(ℝ, E) I (extChartAt I q).symm y : E →L[ℝ] E) v :=
    congrArg (fun L : E →L[ℝ] E => L v) hd
  have hw : (mfderiv 𝓘(ℝ, E) I (extChartAt I p).symm (chartTransition (I := I) p q y) :
      E →L[ℝ] E) (fderiv ℝ (chartTransition (I := I) p q) y w) =
      (mfderiv 𝓘(ℝ, E) I (extChartAt I q).symm y : E →L[ℝ] E) w :=
    congrArg (fun L : E →L[ℝ] E => L w) hd
  rw [pullbackForm_apply, chartCoeff_apply, chartCoeff_apply, hv, hw, hr]

end ChartCoefficients

section Regularity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [I.Boundaryless] in
private theorem source_mfderiv_contMDiffAt {f : E → M} {x : E}
    (hf : ContMDiffAt 𝓘(ℝ, E) I 3 f x) :
    ContMDiffAt 𝓘(ℝ, E) (I.prod 𝓘(ℝ, E →L[ℝ] E)) 2
      (fun y => (⟨f y, mfderiv 𝓘(ℝ, E) I f y⟩ :
        TotalSpace (E →L[ℝ] E)
          (fun m => Bundle.Trivial M E m →L[ℝ] TangentSpace I m))) x := by
  rw [contMDiffAt_hom_bundle]
  refine ⟨hf.of_le (by norm_num), ?_⟩
  have hd := hf.mfderiv_const (m := 2) (by norm_num)
  apply hd.congr_of_eventuallyEq
  filter_upwards [] with y
  ext v
  simp [inTangentCoordinates, ContinuousLinearMap.inCoordinates,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_def]
  rfl

/-- The chart coefficients of a `C^n` metric, `2 ≤ n`, are `C²` on the chart target. -/
theorem contDiffOn_chartCoeff {n : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) (hn : (2 : ℕ∞ω) ≤ n)
    (p : M) : ContDiffOn ℝ 2 (chartCoeff g p) (extChartAt I p).target := by
  let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  intro x hx
  have hfx : ContMDiffAt 𝓘(ℝ, E) I 3 (extChartAt I p).symm x :=
    ((contMDiffOn_extChartAt_symm (n := 3) p).contMDiffAt
      ((isOpen_extChartAt_target p).mem_nhds hx))
  have hD := source_mfderiv_contMDiffAt hfx
  have hG := (g.contMDiff.of_le hn).contMDiffAt.comp x
    (hfx.of_le (by norm_num : (2 : ℕ∞ω) ≤ 3))
  have hB := hG.clm_bundle_bilinearComp
    (U₁ := TangentSpace I) (U₂ := TangentSpace I) (U₃ := Bundle.Trivial M ℝ)
    (U₄ := Bundle.Trivial M E) (U₅ := Bundle.Trivial M E) hD hD
  have h := (contMDiffAt_totalSpace.mp hB).2.contDiffAt
  refine (h.congr_of_eventuallyEq ?_).contDiffWithinAt
  filter_upwards [] with y
  ext v w
  simp [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates,
    ContinuousLinearMap.comp_apply, Trivialization.continuousLinearMapAt_apply]
  rfl

end Regularity

section Gluing

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The pullback by the extended chart at `p` of a bilinear field on the model space. -/
def chartPullbackForm (p : M) (G : E → E →L[ℝ] E →L[ℝ] ℝ) (x : M) : E →L[ℝ] E →L[ℝ] ℝ :=
  let D : E →L[ℝ] E := mfderiv I 𝓘(ℝ, E) (extChartAt I p) x
  let B : E →L[ℝ] E →L[ℝ] ℝ := G (extChartAt I p x)
  B.bilinearComp D D

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] in
theorem chartPullbackForm_apply (p : M) (G : E → E →L[ℝ] E →L[ℝ] ℝ) (x : M)
    (v w : E) :
    chartPullbackForm (I := I) p G x v w = G (extChartAt I p x)
      (mfderiv I 𝓘(ℝ, E) (extChartAt I p) x v) (mfderiv I 𝓘(ℝ, E) (extChartAt I p) x w) :=
  rfl

/-- The coefficients of a chart pullback, cut off by a smooth function supported in the chart,
against the local frames are smooth. -/
theorem contMDiffOn_chartPullbackForm_coeff (p : M) {G : E → E →L[ℝ] E →L[ℝ] ℝ}
    (hG : ContDiff ℝ ∞ G) {χ : M → ℝ} (hχ : ContMDiff I 𝓘(ℝ, ℝ) ∞ χ)
    (hχs : tsupport χ ⊆ (extChartAt I p).source) (x₀ : M) (k l : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun x => χ x * chartPullbackForm (I := I) p G x
        (DifferentialGeometry.Geometry.frameVec (I := I) x₀ k x)
        (DifferentialGeometry.Geometry.frameVec (I := I) x₀ l x))
      (trivializationAt E (TangentSpace I) x₀).baseSet := by
  intro x hx
  by_cases hxs : x ∈ (extChartAt I p).source
  · set b := Module.finBasis ℝ E with hb
    let T := chartTransition (I := I) p x₀
    let W := transitionDomain (I := I) p x₀
    have hWo : IsOpen W := isOpen_transitionDomain (I := I) p x₀
    have hT : ContDiffOn ℝ ∞ T W := contDiffOn_chartTransition (I := I) p x₀
    have hDT : ContDiffOn ℝ ∞ (fun y => fderiv ℝ T y) W :=
      hT.fderiv_of_isOpen hWo (by simp)
    let Q : E → ℝ := fun y => G (T y) (fderiv ℝ T y (b k)) (fderiv ℝ T y (b l))
    have hQ : ContDiffOn ℝ ∞ Q W :=
      ((hG.comp_contDiffOn hT).clm_apply (hDT.clm_apply contDiffOn_const)).clm_apply
        (hDT.clm_apply contDiffOn_const)
    have hsrc : ∀ z ∈ (trivializationAt E (TangentSpace I) x₀).baseSet,
        z ∈ (extChartAt I x₀).source := by
      intro z hz
      simpa [extChartAt_source] using hz
    have hmemW : ∀ z ∈ (trivializationAt E (TangentSpace I) x₀).baseSet,
        z ∈ (extChartAt I p).source → extChartAt I x₀ z ∈ W := by
      intro z hz hzp
      refine ⟨(extChartAt I x₀).map_source (hsrc z hz), ?_⟩
      rw [mem_preimage, (extChartAt I x₀).left_inv (hsrc z hz)]
      exact hzp
    have heq : (fun x => χ x * chartPullbackForm (I := I) p G x
        (DifferentialGeometry.Geometry.frameVec (I := I) x₀ k x)
        (DifferentialGeometry.Geometry.frameVec (I := I) x₀ l x)) =ᶠ[𝓝 x]
        fun z => χ z * Q (extChartAt I x₀ z) := by
      filter_upwards [(trivializationAt E (TangentSpace I) x₀).open_baseSet.mem_nhds hx,
        (isOpen_extChartAt_source p).mem_nhds hxs] with z hz hzp
      have hc := mfderiv_extChartAt_comp_symm (I := I) p x₀ (hmemW z hz hzp)
      rw [(extChartAt I x₀).left_inv (hsrc z hz)] at hc
      have hTz : T (extChartAt I x₀ z) = extChartAt I p z := by
        change extChartAt I p ((extChartAt I x₀).symm (extChartAt I x₀ z)) = _
        rw [(extChartAt I x₀).left_inv (hsrc z hz)]
      change χ z * G (extChartAt I p z)
          (mfderiv I 𝓘(ℝ, E) (extChartAt I p) z
            (DifferentialGeometry.Geometry.frameVec (I := I) x₀ k z))
          (mfderiv I 𝓘(ℝ, E) (extChartAt I p) z
            (DifferentialGeometry.Geometry.frameVec (I := I) x₀ l z)) = _
      rw [frameVec_eq_mfderiv (I := I) x₀ k hz, frameVec_eq_mfderiv (I := I) x₀ l hz]
      change χ z * G (extChartAt I p z)
          (((mfderiv I 𝓘(ℝ, E) (extChartAt I p) z : E →L[ℝ] E).comp
            (mfderiv 𝓘(ℝ, E) I (extChartAt I x₀).symm (extChartAt I x₀ z) : E →L[ℝ] E)) (b k))
          (((mfderiv I 𝓘(ℝ, E) (extChartAt I p) z : E →L[ℝ] E).comp
            (mfderiv 𝓘(ℝ, E) I (extChartAt I x₀).symm (extChartAt I x₀ z) : E →L[ℝ] E)) (b l))
        = χ z * Q (extChartAt I x₀ z)
      rw [hc]
      simp only [Q, hTz]
      rfl
    have hx' : x ∈ (chartAt H x₀).source := by simpa using hx
    have hQx : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun z => Q (extChartAt I x₀ z)) x :=
      (hQ.contDiffAt (hWo.mem_nhds (hmemW x hx hxs))).comp_contMDiffAt
        (contMDiffAt_extChartAt' hx')
    exact ((hχ.contMDiffAt.mul hQx).congr_of_eventuallyEq heq).contMDiffWithinAt
  · have hxt : x ∉ tsupport χ := fun h => hxs (hχs h)
    have h0 : (fun x => χ x * chartPullbackForm (I := I) p G x
        (DifferentialGeometry.Geometry.frameVec (I := I) x₀ k x)
        (DifferentialGeometry.Geometry.frameVec (I := I) x₀ l x)) =ᶠ[𝓝 x]
        fun _ => (0 : ℝ) := by
      filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hxt] with z hz
      rw [image_eq_zero_of_notMem_tsupport hz, zero_mul]
    exact (contMDiffAt_const.congr_of_eventuallyEq h0).contMDiffWithinAt

variable {ι : Type*} [Fintype ι]

/-- The glued bilinear form `∑ᵢ ρᵢ · (φ_{cᵢ})^* Gᵢ`. -/
def gluedForm (c : ι → M) (ρ : ι → M → ℝ) (G : ι → E → E →L[ℝ] E →L[ℝ] ℝ) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ := by
  exact (∑ i, ρ i x • chartPullbackForm (I := I) (c i) (G i) x : E →L[ℝ] E →L[ℝ] ℝ)

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] in
theorem gluedForm_apply (c : ι → M) (ρ : ι → M → ℝ) (G : ι → E → E →L[ℝ] E →L[ℝ] ℝ)
    (x : M) (v w : E) :
    gluedForm (I := I) c ρ G x v w = ∑ i, ρ i x * G i (extChartAt I (c i) x)
      (mfderiv I 𝓘(ℝ, E) (extChartAt I (c i)) x v)
      (mfderiv I 𝓘(ℝ, E) (extChartAt I (c i)) x w) := by
  change (∑ i, ρ i x • chartPullbackForm (I := I) (c i) (G i) x : E →L[ℝ] E →L[ℝ] ℝ) v w = _
  simp only [_root_.sum_apply, _root_.smul_apply, smul_eq_mul]
  rfl

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] in
theorem sum_partition_eq_one {s : Set M} (ρ : SmoothPartitionOfUnity ι I M s) {x : M}
    (hx : x ∈ s) : ∑ i, ρ i x = 1 := by
  rw [← finsum_eq_sum_of_fintype]
  exact ρ.sum_eq_one hx

/-- **Gluing.** Smooth symmetric positive bilinear fields on the model space, pulled back by the
charts at the points `c i` and glued by a smooth partition of unity subordinate to the chart
sources, form a smooth Riemannian metric. -/
theorem exists_smoothMetric_glued (c : ι → M) (ρ : SmoothPartitionOfUnity ι I M univ)
    (hρ : ρ.IsSubordinate fun i => (extChartAt I (c i)).source)
    (G : ι → E → E →L[ℝ] E →L[ℝ] ℝ) (hG : ∀ i, ContDiff ℝ ∞ (G i))
    (hsymm : ∀ i y v w, G i y v w = G i y w v) (hpos : ∀ i y (v : E), v ≠ 0 → 0 < G i y v v) :
    ∃ h : SmoothRiemannianMetric I M, ∀ x (v w : TangentSpace I x),
      h.inner x v w = ∑ i, ρ i x * G i (extChartAt I (c i) x)
        (mfderiv I 𝓘(ℝ, E) (extChartAt I (c i)) x v)
        (mfderiv I 𝓘(ℝ, E) (extChartAt I (c i)) x w) := by
  have hnn : ∀ i y (v : E), 0 ≤ G i y v v := by
    intro i y v
    by_cases hv : v = 0
    · simp [hv]
    · exact (hpos i y v hv).le
  have hgsymm : ∀ (x : M) (v w : TangentSpace I x),
      gluedForm (I := I) c (fun i => ρ i) G x v w = gluedForm (I := I) c (fun i => ρ i) G x w v := by
    intro x v w
    exact (gluedForm_apply (I := I) c (fun i => ρ i) G x v w).trans
      ((Finset.sum_congr rfl fun i _ => congrArg (ρ i x * ·) (hsymm i _ _ _)).trans
        (gluedForm_apply (I := I) c (fun i => ρ i) G x w v).symm)
  have hgpos : ∀ (x : M) (v : TangentSpace I x), v ≠ 0 →
      0 < gluedForm (I := I) c (fun i => ρ i) G x v v := by
    intro x v hv
    refine lt_of_lt_of_eq ?_ (gluedForm_apply (I := I) c (fun i => ρ i) G x v v).symm
    have hsum := sum_partition_eq_one ρ (mem_univ x)
    obtain ⟨i, -, hi⟩ : ∃ i ∈ Finset.univ, ρ i x ≠ 0 := by
      by_contra hcon
      push Not at hcon
      rw [Finset.sum_eq_zero hcon] at hsum
      exact zero_ne_one hsum
    have hipos : 0 < ρ i x := lt_of_le_of_ne (ρ.nonneg i x) (Ne.symm hi)
    have hxs : x ∈ (extChartAt I (c i)).source :=
      hρ i (subset_tsupport _ (Function.mem_support.mpr hi))
    refine Finset.sum_pos' (fun j _ => mul_nonneg (ρ.nonneg j x) (hnn j _ _)) ⟨i,
      Finset.mem_univ i, mul_pos hipos (hpos i _ _ ?_)⟩
    intro h0
    exact hv (injective_mfderiv_extChartAt (I := I) (c i) hxs (h0.trans (map_zero _).symm))
  have hcoeff : ∀ x₀ : M, ∀ k l : Fin (Module.finrank ℝ E),
      ContMDiffOn I 𝓘(ℝ) ∞
        (fun x => gluedForm (I := I) c (fun i => ρ i) G x
          (DifferentialGeometry.Geometry.frameVec (I := I) x₀ k x)
          (DifferentialGeometry.Geometry.frameVec (I := I) x₀ l x))
        (trivializationAt E (TangentSpace I) x₀).baseSet := by
    intro x₀ k l
    have hsum : (fun x => gluedForm (I := I) c (fun i => ρ i) G x
          (DifferentialGeometry.Geometry.frameVec (I := I) x₀ k x)
          (DifferentialGeometry.Geometry.frameVec (I := I) x₀ l x)) =
        fun x => ∑ i, ρ i x * chartPullbackForm (I := I) (c i) (G i) x
          (DifferentialGeometry.Geometry.frameVec (I := I) x₀ k x)
          (DifferentialGeometry.Geometry.frameVec (I := I) x₀ l x) := by
      funext x
      exact gluedForm_apply (I := I) c (fun i => ρ i) G x _ _
    rw [hsum]
    exact contMDiffOn_finsetSum fun i _ =>
      contMDiffOn_chartPullbackForm_coeff (c i) (hG i) (ρ i).contMDiff (hρ i) x₀ k l
  obtain ⟨h, hh⟩ := DifferentialGeometry.Geometry.smoothMetric_of_localCoeff
    (gluedForm (I := I) c (fun i => ρ i) G) hgsymm hgpos hcoeff
  exact ⟨h, fun x v w => (hh x v w).trans (gluedForm_apply (I := I) c (fun i => ρ i) G x v w)⟩

end Gluing

section ChartSums

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {ι : Type*} [Fintype ι]

/-- The chart coefficients of a glued metric, as a sum over the chart transitions. -/
theorem chartCoeff_glued (c : ι → M) (ρ : ι → M → ℝ)
    (hρ : ∀ i, tsupport (ρ i) ⊆ (extChartAt I (c i)).source)
    (G : ι → E → E →L[ℝ] E →L[ℝ] ℝ) (h : SmoothRiemannianMetric I M)
    (hh : ∀ x (v w : TangentSpace I x), h.inner x v w = ∑ i, ρ i x * G i (extChartAt I (c i) x)
        (mfderiv I 𝓘(ℝ, E) (extChartAt I (c i)) x v)
        (mfderiv I 𝓘(ℝ, E) (extChartAt I (c i)) x w))
    (q : M) {y : E} (hy : y ∈ (extChartAt I q).target) :
    chartCoeff h q y = ∑ i, ρ i ((extChartAt I q).symm y) •
      pullbackForm (G i (chartTransition (I := I) (c i) q y),
        fderiv ℝ (chartTransition (I := I) (c i) q) y) := by
  ext v w
  rw [chartCoeff_apply, hh, _root_.sum_apply, _root_.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [_root_.smul_apply, _root_.smul_apply, smul_eq_mul, pullbackForm_apply]
  by_cases hi : ρ i ((extChartAt I q).symm y) = 0
  · rw [hi, zero_mul, zero_mul]
  · have hxs : (extChartAt I q).symm y ∈ (extChartAt I (c i)).source :=
      hρ i (subset_tsupport _ (Function.mem_support.mpr hi))
    have hc := mfderiv_extChartAt_comp_symm (I := I) (c i) q ⟨hy, hxs⟩
    have hv : (mfderiv I 𝓘(ℝ, E) (extChartAt I (c i)) ((extChartAt I q).symm y) : E →L[ℝ] E)
        ((mfderiv 𝓘(ℝ, E) I (extChartAt I q).symm y : E →L[ℝ] E) v) =
        fderiv ℝ (chartTransition (I := I) (c i) q) y v := congrArg (fun L => L v) hc
    have hw : (mfderiv I 𝓘(ℝ, E) (extChartAt I (c i)) ((extChartAt I q).symm y) : E →L[ℝ] E)
        ((mfderiv 𝓘(ℝ, E) I (extChartAt I q).symm y : E →L[ℝ] E) w) =
        fderiv ℝ (chartTransition (I := I) (c i) q) y w := congrArg (fun L => L w) hc
    rw [hv, hw]
    rfl

/-- The chart coefficients of a finite-regularity metric, as the partition-of-unity sum of the
transformed coefficients in the other charts. -/
theorem chartCoeff_eq_sum_transition {n : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) (c : ι → M)
    (ρ : ι → M → ℝ) (hρ : ∀ i, tsupport (ρ i) ⊆ (extChartAt I (c i)).source)
    (hsum : ∀ x, ∑ i, ρ i x = 1) (q : M) {y : E} (hy : y ∈ (extChartAt I q).target) :
    chartCoeff g q y = ∑ i, ρ i ((extChartAt I q).symm y) •
      pullbackForm (chartCoeff g (c i) (chartTransition (I := I) (c i) q y),
        fderiv ℝ (chartTransition (I := I) (c i) q) y) := by
  ext v w
  rw [_root_.sum_apply, _root_.sum_apply]
  simp only [_root_.smul_apply, smul_eq_mul]
  calc chartCoeff g q y v w = (∑ i, ρ i ((extChartAt I q).symm y)) * chartCoeff g q y v w := by
        rw [hsum, one_mul]
    _ = ∑ i, ρ i ((extChartAt I q).symm y) * chartCoeff g q y v w := Finset.sum_mul _ _ _
    _ = _ := by
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases hi : ρ i ((extChartAt I q).symm y) = 0
      · rw [hi, zero_mul, zero_mul]
      · have hxs : (extChartAt I q).symm y ∈ (extChartAt I (c i)).source :=
          hρ i (subset_tsupport _ (Function.mem_support.mpr hi))
        rw [chartCoeff_transition g (c i) q ⟨hy, hxs⟩]

end ChartSums

end DifferentialGeometry.Geometry.MetricSmoothing
