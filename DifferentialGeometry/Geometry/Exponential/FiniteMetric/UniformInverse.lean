import DifferentialGeometry.Geometry.Exponential.FiniteMetric.DerivativeAtZero
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-!
# Uniform local inverses of the exponential map of a finite-regularity metric

Around every `x₀` there are a neighbourhood `W` and a radius `δ > 0` such that for every `x ∈ W`
and `ρ ≤ δ`, `exp_x` is a `C^r` diffeomorphism from the `g_x`-ball of radius `ρ` onto an open set
(`exists_nhds_expMap_partialHomeomorph`). This is the classical totally-normal-neighbourhood
argument: the two-point map `(x, v) ↦ (x, exp_x v)`, read in the charts at `x₀`
(`expChartPair`), has derivative `(a, b) ↦ (a, a + b)` at `(x₀, 0)`, and the inverse function
theorem applies.
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Filter Metric
open scoped Manifold ContDiff Topology

namespace Bundle.ContMDiffRiemannianMetric

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

local instance uniformBilinNormedGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance uniformBilinNormedSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

omit [FiniteDimensional ℝ E] [I.Boundaryless] in
/-- The tangent-bundle chart at `⟨x₀, 0⟩` on a tangent vector based in the chart domain. -/
theorem extChartAt_tangent_mk (x₀ : M) {x : M} (hx : x ∈ (chartAt H x₀).source)
    (v : TangentSpace I x) :
    extChartAt I.tangent (⟨x₀, 0⟩ : TangentBundle I M) (⟨x, v⟩ : TangentBundle I M) =
      ((extChartAt I x₀ x, (mfderiv I 𝓘(ℝ, E) (extChartAt I x₀) x v : E)) : E × E) := by
  apply Prod.ext
  · exact TangentBundle.extChartAt_tangent_apply_fst _
  · rw [TangentBundle.extChartAt_tangent_apply_snd _ (p := (⟨x, v⟩ : TangentBundle I M)) hx,
      TangentBundle.continuousLinearMapAt_trivializationAt hx]
    rfl

omit [FiniteDimensional ℝ E] in
/-- The inverse tangent-bundle chart at `⟨x₀, 0⟩` over a point of the chart domain. -/
theorem extChartAt_tangent_symm_mk (x₀ : M) {x : M} (hx : x ∈ (chartAt H x₀).source) (ξ : E) :
    (extChartAt I.tangent (⟨x₀, 0⟩ : TangentBundle I M)).symm ((extChartAt I x₀ x, ξ) : E × E) =
      (⟨x, mfderiv 𝓘(ℝ, E) I (extChartAt I x₀).symm (extChartAt I x₀ x) ξ⟩ :
        TangentBundle I M) := by
  have hx' : x ∈ (extChartAt I x₀).source := by rwa [extChartAt_source]
  have hcomp := mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm' (I := I) hx'
  rw [I.range_eq_univ, mfderivWithin_univ] at hcomp
  have hξ : mfderiv I 𝓘(ℝ, E) (extChartAt I x₀) x
      (mfderiv 𝓘(ℝ, E) I (extChartAt I x₀).symm (extChartAt I x₀ x) ξ) = ξ :=
    congrArg (fun L => L ξ) hcomp
  have hmem : (⟨x, mfderiv 𝓘(ℝ, E) I (extChartAt I x₀).symm (extChartAt I x₀ x) ξ⟩ :
      TangentBundle I M) ∈ (extChartAt I.tangent (⟨x₀, 0⟩ : TangentBundle I M)).source := by
    rw [extChartAt_source, TangentBundle.mem_chart_source_iff]
    exact hx
  have h := congrArg (extChartAt I.tangent (⟨x₀, 0⟩ : TangentBundle I M)).symm
    (extChartAt_tangent_mk (I := I) x₀ hx
      (mfderiv 𝓘(ℝ, E) I (extChartAt I x₀).symm (extChartAt I x₀ x) ξ))
  rw [(extChartAt I.tangent (⟨x₀, 0⟩ : TangentBundle I M)).left_inv hmem, hξ] at h
  exact h.symm

omit [FiniteDimensional ℝ E] in
/-- The inverse tangent-bundle chart at `⟨x₀, 0⟩` on the zero section. -/
theorem extChartAt_tangent_symm_zero (x₀ : M) {x : M} (hx : x ∈ (chartAt H x₀).source) :
    (extChartAt I.tangent (⟨x₀, 0⟩ : TangentBundle I M)).symm
        ((extChartAt I x₀ x, (0 : E)) : E × E) = (⟨x, 0⟩ : TangentBundle I M) := by
  rw [extChartAt_tangent_symm_mk x₀ hx]
  congr 1
  exact map_zero _

omit [FiniteDimensional ℝ E] [I.Boundaryless] in
/-- The tangent-bundle chart at `⟨x₀, 0⟩` on the zero section. -/
theorem extChartAt_tangent_zero (x₀ : M) {x : M} (hx : x ∈ (chartAt H x₀).source) :
    extChartAt I.tangent (⟨x₀, 0⟩ : TangentBundle I M) (⟨x, 0⟩ : TangentBundle I M) =
      ((extChartAt I x₀ x, (0 : E)) : E × E) := by
  rw [extChartAt_tangent_mk x₀ hx]
  congr 1
  exact map_zero _

/-- The two-point map `(x, v) ↦ (x, exp_x v)` read in the charts at `x₀`. -/
def expChartPair {n : ℕ∞ω} (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _))
    (x₀ : M) (z : E × E) : E × E :=
  (z.1, extChartAt I x₀
    (g.expMap ((extChartAt I.tangent (⟨x₀, 0⟩ : TangentBundle I M)).symm z)))

omit [I.Boundaryless] in
theorem expChartPair_mk {n : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) (x₀ : M) {x : M}
    (hx : x ∈ (chartAt H x₀).source) (v : TangentSpace I x) :
    g.expChartPair x₀
        ((extChartAt I x₀ x, (mfderiv I 𝓘(ℝ, E) (extChartAt I x₀) x v : E)) : E × E) =
      (extChartAt I x₀ x, extChartAt I x₀ (g.expMap (⟨x, v⟩ : TangentBundle I M))) := by
  unfold expChartPair
  rw [← extChartAt_tangent_mk x₀ hx,
    (extChartAt I.tangent (⟨x₀, 0⟩ : TangentBundle I M)).left_inv (by
      rw [extChartAt_source, TangentBundle.mem_chart_source_iff]
      exact hx)]
  rfl

variable [T2Space M] {r : ℕ∞}
  (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))

/-- The open set of `E × E` on which `expChartPair` is a composition of `C^r` maps. -/
def expChartPairDomain (x₀ : M) : Set (E × E) :=
  (extChartAt I.tangent (⟨x₀, 0⟩ : TangentBundle I M)).target ∩
    (extChartAt I.tangent (⟨x₀, 0⟩ : TangentBundle I M)).symm ⁻¹'
      (g.expDomain ∩ g.expMap ⁻¹' (extChartAt I x₀).source)

theorem isOpen_expChartPairDomain (hr : 1 ≤ r) (x₀ : M) : IsOpen (g.expChartPairDomain x₀) := by
  have h1 : IsOpen (g.expDomain ∩ g.expMap ⁻¹' (extChartAt I x₀).source) :=
    (g.contMDiffOn_expMap hr).continuousOn.isOpen_inter_preimage (g.isOpen_expDomain hr)
      (isOpen_extChartAt_source x₀)
  exact (continuousOn_extChartAt_symm _).isOpen_inter_preimage (isOpen_extChartAt_target _) h1

theorem contDiffAt_expChartPair (hr : 1 ≤ r) (x₀ : M) {z : E × E}
    (hz : z ∈ g.expChartPairDomain x₀) : ContDiffAt ℝ r (g.expChartPair x₀) z := by
  rw [← contMDiffAt_iff_contDiffAt]
  have hT : ContMDiffAt 𝓘(ℝ, E × E) I.tangent r
      (extChartAt I.tangent (⟨x₀, 0⟩ : TangentBundle I M)).symm z :=
    ((contMDiffOn_extChartAt_symm (n := r) _).contMDiffAt
      ((isOpen_extChartAt_target _).mem_nhds hz.1))
  have hexp : ContMDiffAt I.tangent I r g.expMap
      ((extChartAt I.tangent (⟨x₀, 0⟩ : TangentBundle I M)).symm z) :=
    (g.contMDiffOn_expMap hr).contMDiffAt ((g.isOpen_expDomain hr).mem_nhds hz.2.1)
  have hκ : ContMDiffAt I 𝓘(ℝ, E) r (extChartAt I x₀)
      (g.expMap ((extChartAt I.tangent (⟨x₀, 0⟩ : TangentBundle I M)).symm z)) :=
    contMDiffAt_extChartAt' (by simpa [extChartAt_source] using hz.2.2)
  exact (contDiff_fst.contMDiff.contMDiffAt).prodMk_space (hκ.comp z (hexp.comp z hT))

theorem mem_expChartPairDomain_zero (hr : 1 ≤ r) (x₀ : M) :
    ((extChartAt I x₀ x₀, (0 : E)) : E × E) ∈ g.expChartPairDomain x₀ := by
  have hx₀ : x₀ ∈ (chartAt H x₀).source := mem_chart_source H x₀
  refine ⟨?_, ?_⟩
  · rw [← extChartAt_tangent_zero (I := I) x₀ hx₀]
    exact (extChartAt I.tangent (⟨x₀, 0⟩ : TangentBundle I M)).map_source
      (by rw [extChartAt_source, TangentBundle.mem_chart_source_iff]; exact hx₀)
  · simp only [mem_preimage]
    rw [extChartAt_tangent_symm_zero (I := I) x₀ hx₀]
    refine ⟨g.zero_mem_expDomain x₀, ?_⟩
    simp only [mem_preimage, g.expMap_zero hr, extChartAt_source]
    exact hx₀

/-- The derivative of the two-point map at `(x₀, 0)` is `(a, b) ↦ (a, a + b)`. -/
theorem hasFDerivAt_expChartPair (hr : 1 ≤ r) (x₀ : M) :
    HasFDerivAt (g.expChartPair x₀)
      ((ContinuousLinearMap.fst ℝ E E).prod
        (ContinuousLinearMap.fst ℝ E E + ContinuousLinearMap.snd ℝ E E))
      ((extChartAt I x₀ x₀, 0) : E × E) := by
  set z₀ : E × E := (extChartAt I x₀ x₀, 0) with hz₀
  have hx₀ : x₀ ∈ (chartAt H x₀).source := mem_chart_source H x₀
  have hz₀mem : z₀ ∈ g.expChartPairDomain x₀ := by
    refine ⟨?_, ?_⟩
    · rw [hz₀, ← extChartAt_tangent_zero (I := I) x₀ hx₀]
      exact (extChartAt I.tangent (⟨x₀, 0⟩ : TangentBundle I M)).map_source
        (by rw [extChartAt_source, TangentBundle.mem_chart_source_iff]; exact hx₀)
    · simp only [mem_preimage, hz₀]
      rw [extChartAt_tangent_symm_zero (I := I) x₀ hx₀]
      refine ⟨g.zero_mem_expDomain x₀, ?_⟩
      simp only [mem_preimage, g.expMap_zero hr, extChartAt_source]
      exact hx₀
  have hdiff : DifferentiableAt ℝ (g.expChartPair x₀) z₀ :=
    (g.contDiffAt_expChartPair hr x₀ hz₀mem).differentiableAt
      (by exact_mod_cast (zero_lt_one.trans_le hr).ne')
  set D := fderiv ℝ (g.expChartPair x₀) z₀ with hD
  have hF : HasFDerivAt (g.expChartPair x₀) D ((extChartAt I x₀ x₀, (0 : E)) : E × E) :=
    hdiff.hasFDerivAt
  -- the base direction
  have hbase : ∀ᶠ y in 𝓝 (extChartAt I x₀ x₀), g.expChartPair x₀ (y, 0) = (y, y) := by
    filter_upwards [(isOpen_extChartAt_target x₀).mem_nhds (mem_extChartAt_target x₀)] with y hy
    have hys : (extChartAt I x₀).symm y ∈ (chartAt H x₀).source := by
      have := (extChartAt I x₀).map_target hy
      rwa [extChartAt_source] at this
    have h := extChartAt_tangent_symm_zero (I := I) x₀ hys
    rw [(extChartAt I x₀).right_inv hy] at h
    unfold expChartPair
    rw [h, g.expMap_zero hr, (extChartAt I x₀).right_inv hy]
  have hD1 : ∀ a : E, D (a, 0) = (a, a) := by
    intro a
    have h1 :=
      hF.comp (extChartAt I x₀ x₀) (hasFDerivAt_prodMk_left (𝕜 := ℝ) (extChartAt I x₀ x₀) (0 : E))
    have h2 : HasFDerivAt (fun y : E => g.expChartPair x₀ (y, 0))
        ((ContinuousLinearMap.id ℝ E).prod (ContinuousLinearMap.id ℝ E)) (extChartAt I x₀ x₀) :=
      ((hasFDerivAt_id (extChartAt I x₀ x₀)).prodMk (hasFDerivAt_id (extChartAt I x₀ x₀))).congr_of_eventuallyEq hbase
    have h3 := congrArg (fun L : E →L[ℝ] E × E => L a) (h1.unique h2)
    simpa using h3
  -- the fibre direction
  have hfib : ∀ ξ : E, g.expChartPair x₀ (extChartAt I x₀ x₀, ξ) =
      (extChartAt I x₀ x₀, extChartAt I x₀ (g.expMap (⟨x₀, ξ⟩ : TangentBundle I M))) := by
    intro ξ
    have h := extChartAt_tangent_symm_mk (I := I) x₀ hx₀ ξ
    have hid := mfderivWithin_range_extChartAt_symm (I := I) (x := x₀)
    rw [I.range_eq_univ, mfderivWithin_univ] at hid
    rw [hid] at h
    unfold expChartPair
    rw [h]
    rfl
  have hD2 : ∀ b : E, D (0, b) = (0, b) := by
    intro b
    have hexp := g.hasMFDerivAt_expMap_zero hr x₀
    have hκd : MDifferentiableAt I 𝓘(ℝ, E) (extChartAt I x₀)
        (g.expMap (⟨x₀, 0⟩ : TangentBundle I M)) :=
      mdifferentiableAt_extChartAt (by rw [g.expMap_zero hr]; exact hx₀)
    have hcomp := hκd.hasMFDerivAt.comp (0 : E) hexp
    rw [hasMFDerivAt_iff_hasFDerivAt] at hcomp
    have key : ∀ y : M, y = x₀ →
        mfderiv I 𝓘(ℝ, E) (extChartAt I x₀) y = ContinuousLinearMap.id ℝ E := by
      rintro y rfl
      exact mfderiv_extChartAt_self
    have hκid := key _ (g.expMap_zero hr x₀)
    have h1 :=
      hF.comp (0 : E) (hasFDerivAt_prodMk_right (𝕜 := ℝ) (extChartAt I x₀ x₀) (0 : E))
    have h2 : HasFDerivAt (fun ξ : E => g.expChartPair x₀ (extChartAt I x₀ x₀, ξ))
        ((0 : E →L[ℝ] E).prod (ContinuousLinearMap.id ℝ E)) 0 := by
      have h := (hasFDerivAt_const (extChartAt I x₀ x₀) (0 : E)).prodMk hcomp
      rw [hκid] at h
      refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun ξ => ?_)
      exact hfib ξ
    have h3 := congrArg (fun L : E →L[ℝ] E × E => L b) (h1.unique h2)
    simpa using h3
  have hDL : D = (ContinuousLinearMap.fst ℝ E E).prod
      (ContinuousLinearMap.fst ℝ E E + ContinuousLinearMap.snd ℝ E E) := by
    apply ContinuousLinearMap.ext
    intro z
    obtain ⟨a, b⟩ := z
    have hz : ((a, b) : E × E) = (a, 0) + (0, b) := by simp
    rw [hz, map_add, hD1, hD2]
    simp
  rw [← hDL]
  exact hdiff.hasFDerivAt

/-- **Uniform local inverses of `exp`.** Around every `x₀` there are a neighbourhood `W` and a
radius `δ > 0` such that, for `x ∈ W` and `ρ ≤ δ`, `exp_x` restricted to the `g_x`-ball of radius
`ρ` is a `C^r` diffeomorphism onto an open subset of `M`. -/
theorem exists_nhds_expMap_partialHomeomorph (hr : 1 ≤ r) (x₀ : M) :
    ∃ W ∈ 𝓝 x₀, ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ W, ∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ δ →
      ∃ e : OpenPartialHomeomorph E M, e.source = {v : E | g.inner x v v < ρ ^ 2} ∧
        (∀ v ∈ e.source, (⟨x, v⟩ : TangentBundle I M) ∈ g.expDomain ∧
          e v = g.expMap (⟨x, v⟩ : TangentBundle I M)) ∧
        ContMDiffOn 𝓘(ℝ, E) I r e e.source ∧ ContMDiffOn I 𝓘(ℝ, E) r e.symm e.target := by
  have hr0 : (r : ℕ∞ω) ≠ 0 := by exact_mod_cast (zero_lt_one.trans_le hr).ne'
  set F := g.expChartPair x₀ with hFdef
  set z₀ : E × E := (extChartAt I x₀ x₀, (0 : E)) with hz₀
  set U := g.expChartPairDomain x₀ with hUdef
  have hU : IsOpen U := g.isOpen_expChartPairDomain hr x₀
  have hz₀U : z₀ ∈ U := g.mem_expChartPairDomain_zero hr x₀
  let L : (E × E) ≃L[ℝ] (E × E) := ContinuousLinearEquiv.equivOfInverse
    ((ContinuousLinearMap.fst ℝ E E).prod
      (ContinuousLinearMap.fst ℝ E E + ContinuousLinearMap.snd ℝ E E))
    ((ContinuousLinearMap.fst ℝ E E).prod
      (ContinuousLinearMap.snd ℝ E E - ContinuousLinearMap.fst ℝ E E))
    (fun z => by simp) (fun z => by simp)
  have hFd : HasFDerivAt F (L : E × E →L[ℝ] E × E) z₀ := g.hasFDerivAt_expChartPair hr x₀
  have hstrict : HasStrictFDerivAt F (L : E × E →L[ℝ] E × E) z₀ := by
    have h := (g.contDiffAt_expChartPair hr x₀ hz₀U).hasStrictFDerivAt hr0
    rwa [hFd.fderiv] at h
  set Ψ := hstrict.toOpenPartialHomeomorph F with hΨdef
  have hΨF : (Ψ : E × E → E × E) = F := hstrict.toOpenPartialHomeomorph_coe
  have hFC1 : ContDiffOn ℝ 1 F U := fun z hz =>
    ((g.contDiffAt_expChartPair hr x₀ hz).of_le (by exact_mod_cast hr)).contDiffWithinAt
  set S := Ψ.source ∩ (U ∩ fderiv ℝ F ⁻¹'
    range ((↑) : ((E × E) ≃L[ℝ] (E × E)) → (E × E →L[ℝ] E × E))) with hSdef
  have hS : IsOpen S := Ψ.open_source.inter
    ((hFC1.continuousOn_fderiv_of_isOpen hU le_rfl).isOpen_inter_preimage hU
      ContinuousLinearEquiv.isOpen)
  have hz₀S : z₀ ∈ S := ⟨hstrict.mem_toOpenPartialHomeomorph_source, hz₀U, ⟨L, hFd.fderiv.symm⟩⟩
  set Ψ' := Ψ.restrOpen S hS with hΨ'def
  have hΨ'src : Ψ'.source = S := by
    rw [hΨ'def, OpenPartialHomeomorph.restrOpen_source]
    exact inter_eq_right.mpr inter_subset_left
  have hΨ'F : (Ψ' : E × E → E × E) = F := by rw [hΨ'def, OpenPartialHomeomorph.coe_restrOpen, hΨF]
  -- uniform coercivity near `x₀`
  obtain ⟨c, hc, hcoer⟩ := g.isCoercive_chartInner x₀ (mem_extChartAt_target (I := I) x₀)
  have hBc : ContinuousAt (g.chartInner x₀) (extChartAt I x₀ x₀) :=
    (g.contDiffOn_chartInner x₀).continuousOn.continuousAt
      ((isOpen_extChartAt_target x₀).mem_nhds (mem_extChartAt_target x₀))
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hS z₀ hz₀S
  obtain ⟨a₁, ha₁, hB⟩ := Metric.continuousAt_iff.mp hBc (c / 2) (by positivity)
  obtain ⟨a₂, ha₂, htgt⟩ := Metric.isOpen_iff.mp (isOpen_extChartAt_target (I := I) x₀)
    (extChartAt I x₀ x₀) (mem_extChartAt_target x₀)
  set a := min ε (min a₁ a₂) with ha
  have ha0 : 0 < a := lt_min hε (lt_min ha₁ ha₂)
  set δ := a * Real.sqrt (c / 2) with hδ
  have hδ0 : 0 < δ := mul_pos ha0 (Real.sqrt_pos.mpr (by positivity))
  set W := (extChartAt I x₀).source ∩ extChartAt I x₀ ⁻¹' ball (extChartAt I x₀ x₀) a with hW
  have hWo : IsOpen W := (continuousOn_extChartAt x₀).isOpen_inter_preimage
    (isOpen_extChartAt_source x₀) isOpen_ball
  have hx₀W : x₀ ∈ W := ⟨mem_extChartAt_source x₀, mem_ball_self ha0⟩
  refine ⟨W, hWo.mem_nhds hx₀W, δ, hδ0, fun x hx ρ hρ0 hρ => ?_⟩
  have hxc : x ∈ (chartAt H x₀).source := by
    have := hx.1
    rwa [extChartAt_source] at this
  have hxa : dist (extChartAt I x₀ x) (extChartAt I x₀ x₀) < a := hx.2
  -- the chart differential at `x` and its inverse
  set A : E →L[ℝ] E := mfderiv I 𝓘(ℝ, E) (extChartAt I x₀) x with hA
  set A' : E →L[ℝ] E := mfderiv 𝓘(ℝ, E) I (extChartAt I x₀).symm (extChartAt I x₀ x) with hA'
  have hxs : x ∈ (extChartAt I x₀).source := hx.1
  have hA'A : ∀ v : E, A' (A v) = v := by
    intro v
    have hcomp := mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt' (I := I) hxs
    rw [I.range_eq_univ, mfderivWithin_univ] at hcomp
    exact congrArg (fun T => T v) hcomp
  -- the norm comparison
  have hnormA : ∀ v : E, g.inner x v v < ρ ^ 2 → ‖A v‖ < a := by
    intro v hv
    have hread := g.inner_eq_chartInner hxc v v
    have hBy : ‖g.chartInner x₀ (extChartAt I x₀ x) - g.chartInner x₀ (extChartAt I x₀ x₀)‖ <
        c / 2 := by
      rw [← dist_eq_norm]
      exact hB (lt_of_lt_of_le hxa ((min_le_right _ _).trans (min_le_left _ _)))
    have hlow : c / 2 * ‖A v‖ * ‖A v‖ ≤ g.inner x v v := by
      rw [hread]
      have h1 := hcoer (A v)
      have h2 : |(g.chartInner x₀ (extChartAt I x₀ x) - g.chartInner x₀ (extChartAt I x₀ x₀))
          (A v) (A v)| ≤ c / 2 * ‖A v‖ * ‖A v‖ := by
        calc _ ≤ ‖g.chartInner x₀ (extChartAt I x₀ x) - g.chartInner x₀ (extChartAt I x₀ x₀)‖ *
              ‖A v‖ * ‖A v‖ := by
              rw [← Real.norm_eq_abs]
              exact ContinuousLinearMap.le_opNorm₂ _ _ _
          _ ≤ c / 2 * ‖A v‖ * ‖A v‖ := by gcongr
      have h3 := neg_abs_le ((g.chartInner x₀ (extChartAt I x₀ x) -
        g.chartInner x₀ (extChartAt I x₀ x₀)) (A v) (A v))
      simp only [sub_apply] at h2 h3
      change c / 2 * ‖A v‖ * ‖A v‖ ≤ g.chartInner x₀ (extChartAt I x₀ x) (A v) (A v)
      nlinarith
    have hρ2 : ρ ^ 2 ≤ δ ^ 2 := pow_le_pow_left₀ hρ0 hρ 2
    have hδ2 : δ ^ 2 = a ^ 2 * (c / 2) := by
      rw [hδ, mul_pow, Real.sq_sqrt (by positivity)]
    have hlt : c / 2 * ‖A v‖ ^ 2 < c / 2 * a ^ 2 := by nlinarith
    have hsq : ‖A v‖ ^ 2 < a ^ 2 := lt_of_mul_lt_mul_left hlt (by positivity)
    exact (pow_lt_pow_iff_left₀ (norm_nonneg _) ha0.le (by norm_num)).mp hsq
  -- the slice of `S` over `x`
  have hsliceS : ∀ v : E, g.inner x v v < ρ ^ 2 →
      ((extChartAt I x₀ x, A v) : E × E) ∈ S := by
    intro v hv
    apply hball
    rw [mem_ball, hz₀, Prod.dist_eq]
    refine max_lt (lt_of_lt_of_le hxa (min_le_left _ _)) ?_
    rw [dist_zero_right]
    exact lt_of_lt_of_le (hnormA v hv) (min_le_left _ _)
  have hsymm_mk : ∀ v : E, (extChartAt I.tangent (⟨x₀, 0⟩ : TangentBundle I M)).symm
      ((extChartAt I x₀ x, A v) : E × E) = (⟨x, v⟩ : TangentBundle I M) := by
    intro v
    rw [extChartAt_tangent_symm_mk x₀ hxc]
    congr 1
    exact hA'A v
  have hdom : ∀ v : E, g.inner x v v < ρ ^ 2 →
      (⟨x, v⟩ : TangentBundle I M) ∈ g.expDomain ∧
        g.expMap (⟨x, v⟩ : TangentBundle I M) ∈ (extChartAt I x₀).source := by
    intro v hv
    have h := (hsliceS v hv).2.1.2
    rw [mem_preimage, hsymm_mk] at h
    exact h
  have hΨ'mem : ∀ v : E, g.inner x v v < ρ ^ 2 →
      ((extChartAt I x₀ x, A v) : E × E) ∈ Ψ'.source := fun v hv => by
    rw [hΨ'src]
    exact hsliceS v hv
  have hΨ'app : ∀ v : E, Ψ' ((extChartAt I x₀ x, A v) : E × E) =
      (extChartAt I x₀ x, extChartAt I x₀ (g.expMap (⟨x, v⟩ : TangentBundle I M))) := by
    intro v
    rw [hΨ'F]
    exact g.expChartPair_mk x₀ hxc v
  set invFun : M → E := fun y =>
    A' (Ψ'.symm ((extChartAt I x₀ x, extChartAt I x₀ y) : E × E)).2 with hinvFun
  have hleft : ∀ v : E, g.inner x v v < ρ ^ 2 →
      invFun (g.expMap (⟨x, v⟩ : TangentBundle I M)) = v := by
    intro v hv
    simp only [hinvFun]
    rw [← hΨ'app v, Ψ'.left_inv (hΨ'mem v hv)]
    exact hA'A v
  have hright : ∀ y : M, y ∈ (extChartAt I x₀).source →
      ((extChartAt I x₀ x, extChartAt I x₀ y) : E × E) ∈ Ψ'.target →
      g.expMap (⟨x, invFun y⟩ : TangentBundle I M) = y := by
    intro y hy hyt
    set z := Ψ'.symm ((extChartAt I x₀ x, extChartAt I x₀ y) : E × E) with hz
    have hzS : z ∈ S := hΨ'src ▸ Ψ'.map_target hyt
    have hFz : F z = (extChartAt I x₀ x, extChartAt I x₀ y) := by
      rw [← hΨ'F]
      exact Ψ'.right_inv hyt
    have hz1 : z.1 = extChartAt I x₀ x := congrArg Prod.fst hFz
    have hzeq : z = ((extChartAt I x₀ x, z.2) : E × E) := Prod.ext hz1 rfl
    have hsym : (extChartAt I.tangent (⟨x₀, 0⟩ : TangentBundle I M)).symm z =
        (⟨x, invFun y⟩ : TangentBundle I M) := by
      rw [hzeq, extChartAt_tangent_symm_mk x₀ hxc]
      rfl
    have hexps : g.expMap (⟨x, invFun y⟩ : TangentBundle I M) ∈ (extChartAt I x₀).source := by
      have h := hzS.2.1.2.2
      rw [mem_preimage, hsym] at h
      exact h
    have h2 := congrArg Prod.snd hFz
    change extChartAt I x₀
      (g.expMap ((extChartAt I.tangent (⟨x₀, 0⟩ : TangentBundle I M)).symm z)) = _ at h2
    rw [hsym] at h2
    exact (extChartAt I x₀).injOn hexps hy h2
  set src : Set E := {v : E | g.inner x v v < ρ ^ 2} with hsrc
  have hsrc_open : IsOpen src :=
    isOpen_lt ((g.inner x).continuous.clm_apply continuous_id) continuous_const
  set A₀ : Set M := (extChartAt I x₀).source ∩
    (fun y => ((extChartAt I x₀ x, extChartAt I x₀ y) : E × E)) ⁻¹' Ψ'.target with hA₀
  have hA₀open : IsOpen A₀ :=
    (continuousOn_const.prodMk (continuousOn_extChartAt x₀)).isOpen_inter_preimage
      (isOpen_extChartAt_source x₀) Ψ'.open_target
  have hcont_inv : ContinuousOn invFun A₀ := by
    have h1 : ContinuousOn (fun y => ((extChartAt I x₀ x, extChartAt I x₀ y) : E × E)) A₀ :=
      (continuousOn_const.prodMk (continuousOn_extChartAt x₀)).mono inter_subset_left
    have h2 := Ψ'.continuousOn_symm.comp h1 (fun y hy => hy.2)
    exact A'.continuous.comp_continuousOn (continuous_snd.comp_continuousOn h2)
  set tgt : Set M := A₀ ∩ invFun ⁻¹' src with htgt
  have htgt_open : IsOpen tgt := hcont_inv.isOpen_inter_preimage hA₀open hsrc_open
  let e : OpenPartialHomeomorph E M :=
    { toFun := fun v => g.expMap (⟨x, v⟩ : TangentBundle I M)
      invFun := invFun
      source := src
      target := tgt
      map_source' := fun v hv => by
        refine ⟨⟨(hdom v hv).2, ?_⟩, ?_⟩
        · change ((extChartAt I x₀ x,
            extChartAt I x₀ (g.expMap (⟨x, v⟩ : TangentBundle I M))) : E × E) ∈ Ψ'.target
          rw [← hΨ'app v]
          exact Ψ'.map_source (hΨ'mem v hv)
        · change invFun (g.expMap (⟨x, v⟩ : TangentBundle I M)) ∈ src
          rw [hleft v hv]
          exact hv
      map_target' := fun y hy => hy.2
      left_inv' := fun v hv => hleft v hv
      right_inv' := fun y hy => hright y hy.1.1 hy.1.2
      open_source := hsrc_open
      open_target := htgt_open
      continuousOn_toFun := (g.contMDiffOn_expMap_fiber hr x).continuousOn.mono
        (fun v hv => (hdom v hv).1)
      continuousOn_invFun := hcont_inv.mono inter_subset_left }
  refine ⟨e, rfl, fun v hv => ⟨(hdom v hv).1, rfl⟩, ?_, ?_⟩
  · exact (g.contMDiffOn_expMap_fiber hr x).mono (fun v hv => (hdom v hv).1)
  · intro y hy
    apply ContMDiffAt.contMDiffWithinAt
    have hyt : ((extChartAt I x₀ x, extChartAt I x₀ y) : E × E) ∈ Ψ'.target := hy.1.2
    set w := Ψ'.symm ((extChartAt I x₀ x, extChartAt I x₀ y) : E × E) with hw
    have hwS : w ∈ S := hΨ'src ▸ Ψ'.map_target hyt
    obtain ⟨L', hL'⟩ := hwS.2.2
    have hFw : HasFDerivAt F (L' : E × E →L[ℝ] E × E) w := by
      have hd : DifferentiableAt ℝ F w :=
        ((hFC1 w hwS.2.1).differentiableWithinAt (by norm_num)).differentiableAt
          (hU.mem_nhds hwS.2.1)
      rw [hL']
      exact hd.hasFDerivAt
    have hΨsymm : ContDiffAt ℝ r Ψ'.symm ((extChartAt I x₀ x, extChartAt I x₀ y) : E × E) := by
      apply Ψ'.contDiffAt_symm hyt
      · rw [hΨ'F]
        exact hFw
      · rw [hΨ'F]
        exact g.contDiffAt_expChartPair hr x₀ hwS.2.1
    have hyc : y ∈ (chartAt H x₀).source := by
      have := hy.1.1
      rwa [extChartAt_source] at this
    have hpair : ContMDiffAt I 𝓘(ℝ, E × E) r
        (fun y => ((extChartAt I x₀ x, extChartAt I x₀ y) : E × E)) y :=
      contMDiffAt_const.prodMk_space (contMDiffAt_extChartAt' hyc)
    have hlin : ContDiffAt ℝ r (fun z : E × E => A' z.2) w :=
      (A'.contDiff.comp contDiff_snd).contDiffAt
    have h1 : ContDiffAt ℝ r ((fun z : E × E => A' z.2) ∘ Ψ'.symm)
        ((extChartAt I x₀ x, extChartAt I x₀ y) : E × E) := hlin.comp _ hΨsymm
    have h2 : ContMDiffAt 𝓘(ℝ, E × E) 𝓘(ℝ, E) r ((fun z : E × E => A' z.2) ∘ Ψ'.symm)
        ((extChartAt I x₀ x, extChartAt I x₀ y) : E × E) := h1.contMDiffAt
    have h3 := h2.comp y hpair
    exact h3

end Bundle.ContMDiffRiemannianMetric
