import DifferentialGeometry.Geometry.Collapse.BoundaryScale.CuspFinitePatch
import DifferentialGeometry.Geometry.Collapse.BoundaryScale.CuspMetricEquivalence
import DifferentialGeometry.Geometry.Metric.Pullback.ChartJet
import DifferentialGeometry.Geometry.Connection.TensorNabla.FixedChart.Models
import DifferentialGeometry.Analysis.Calculus.Taylor.JetProd
import DifferentialGeometry.Topology.Manifold.InverseFunctionTheorem.Basic
import DifferentialGeometry.Topology.Manifold.InteriorChart
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Open

/-!
# Taylor patches of a cusp embedding

At a point `p` of positive height in a cusp collar, the `C^{K+1}` embedding `e` (`K ≥ 2`) is
replaced near `p` by the smooth map `f = d⁻¹ ∘ ψ ∘ c`, where `c, d` are the charts at `p` and
`e p` and `ψ` is the cubic Taylor polynomial of `d ∘ e ∘ c⁻¹` at `c p`. The map `f` is a local
diffeomorphism near `p` with `f p = e p` and `Df p = De p`, and the chart representatives at `p`
of the two metric errors `e^* g - H` and `f^* g - H` are `C²` with the same second-order jet.
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Filter TopologicalSpace Function
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.TensorLieDeriv
open GC.Endpoint
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Collapse

universe u

local notation "Ec" => (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) × EuclideanSpace ℝ (Fin 1)

/-- Bilinear forms as `(0,2)` model tensors: `B ↦ (m ↦ B (m 0) (m 1))`. -/
def bilinToTensor0SModel (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] : (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] Tensor0SModel 2 ℝ E :=
  ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin 2 => E) ℝ).symm.toContinuousLinearEquiv.toContinuousLinearMap).comp
    (ContinuousLinearMap.compL ℝ E (E →L[ℝ] ℝ) (ContinuousMultilinearMap ℝ (fun _ : Fin 1 => E) ℝ)
      (continuousMultilinearCurryFin1 ℝ E ℝ).symm.toContinuousLinearEquiv.toContinuousLinearMap)

theorem bilinToTensor0SModel_apply (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (B : E →L[ℝ] E →L[ℝ] ℝ) (m : Fin 2 → E) :
    bilinToTensor0SModel E B m = B (m 0) (m 1) :=
  rfl

/-- A map `F` written in the chart at `p` (source) and the chart at `b` (target). -/
def cuspChartMap {W : CompactCarrier.{u}} (F : CuspHalfSpace → W.Carrier) (p : CuspHalfSpace)
    (b : W.Carrier) (y : Ec) : EuclideanSpace ℝ (Fin 3) :=
  extChartAt W.model b (F ((extChartAt halfCollarModel p).symm y))

/-- The chart representative of `F^* g - H` at `p` as a function of `(φ y, Dφ y, y)`. -/
def cuspChartTheta {W : CompactCarrier.{u}} (g : SmoothRiemannianMetric W.model W.Carrier)
    (H : HyperbolicCusp) (p : CuspHalfSpace) (b : W.Carrier)
    (t : EuclideanSpace ℝ (Fin 3) × (Ec →L[ℝ] EuclideanSpace ℝ (Fin 3)) × Ec) :
    Tensor0SModel 2 ℝ Ec :=
  bilinToTensor0SModel Ec ((chartMetricBilin g b t.1).bilinearComp t.2.1 t.2.1 -
    chartMetricBilin H.metric p t.2.2)

theorem cuspChartTheta_contDiffAt {W : CompactCarrier.{u}}
    (g : SmoothRiemannianMetric W.model W.Carrier) (H : HyperbolicCusp) {p : CuspHalfSpace}
    {b : W.Carrier} (hp : halfCollarModel.IsInteriorPoint p) (hb : W.model.IsInteriorPoint b)
    (L₀ : Ec →L[ℝ] EuclideanSpace ℝ (Fin 3)) :
    ContDiffAt ℝ ∞ (cuspChartTheta g H p b)
      (extChartAt W.model b b, L₀, extChartAt halfCollarModel p p) := by
  have hg := contDiffAt_chartMetricBilin_of_isInteriorPoint g hb
  have hH := contDiffAt_chartMetricBilin_of_isInteriorPoint H.metric hp
  let t₀ : EuclideanSpace ℝ (Fin 3) × (Ec →L[ℝ] EuclideanSpace ℝ (Fin 3)) × Ec :=
    (extChartAt W.model b b, L₀, extChartAt halfCollarModel p p)
  have h1 : ContDiffAt ℝ ∞ (fun t : EuclideanSpace ℝ (Fin 3) ×
      (Ec →L[ℝ] EuclideanSpace ℝ (Fin 3)) × Ec => chartMetricBilin g b t.1) t₀ :=
    hg.comp t₀ contDiffAt_fst
  have h2 : ContDiffAt ℝ ∞ (fun t : EuclideanSpace ℝ (Fin 3) ×
      (Ec →L[ℝ] EuclideanSpace ℝ (Fin 3)) × Ec => t.2.1) t₀ :=
    contDiffAt_fst.comp t₀ contDiffAt_snd
  have h3 : ContDiffAt ℝ ∞ (fun t : EuclideanSpace ℝ (Fin 3) ×
      (Ec →L[ℝ] EuclideanSpace ℝ (Fin 3)) × Ec => chartMetricBilin H.metric p t.2.2) t₀ :=
    hH.comp t₀ (contDiffAt_snd.comp t₀ contDiffAt_snd)
  let fl₁ := ContinuousLinearMap.flipₗᵢ ℝ Ec (EuclideanSpace ℝ (Fin 3)) ℝ
  let fl₂ := ContinuousLinearMap.flipₗᵢ ℝ Ec Ec ℝ
  have hc : ContDiffAt ℝ ∞ (fun t : EuclideanSpace ℝ (Fin 3) ×
      (Ec →L[ℝ] EuclideanSpace ℝ (Fin 3)) × Ec =>
        (chartMetricBilin g b t.1).bilinearComp t.2.1 t.2.1) t₀ := by
    have hfl₁ := fl₁.contDiff (n := ∞)
    have hfl₂ := fl₂.contDiff (n := ∞)
    have hA := h1.clm_comp h2
    have hB := (hfl₁.contDiffAt.comp t₀ hA).clm_comp h2
    exact hfl₂.contDiffAt.comp t₀ hB
  exact (bilinToTensor0SModel Ec).contDiff.contDiffAt.comp t₀ (hc.sub h3)

/-- **Chart formula for the metric error.** Near the chart image of an interior point `p`, the
chart representative of `F^* g - H` at `p` is `Θ (φ y, Dφ y, y)` with `φ` the chart expression of
`F` into the chart at `b`. -/
theorem cuspMetricError_chart_eventuallyEq {W : CompactCarrier.{u}}
    (g : SmoothRiemannianMetric W.model W.Carrier) (H : HyperbolicCusp)
    (F : CuspHalfSpace → W.Carrier) (p : CuspHalfSpace) (b : W.Carrier)
    (hp : halfCollarModel.IsInteriorPoint p) (hFc : ContinuousAt F p)
    (hFb : F p ∈ (chartAt (W.kind.Space) b).source)
    (hFd : ∀ᶠ z in 𝓝 p, MDifferentiableAt halfCollarModel W.model F z) :
    tensor0SModelInChart (𝕜 := ℝ) (I := halfCollarModel) 2 p (cuspMetricError g H F)
      =ᶠ[𝓝 (extChartAt halfCollarModel p p)]
      fun y => cuspChartTheta g H p b
        (cuspChartMap F p b y, fderiv ℝ (cuspChartMap F p b) y, y) := by
  have htarget : (extChartAt halfCollarModel p).target ∈ 𝓝 (extChartAt halfCollarModel p p) :=
    mem_interior_iff_mem_nhds.mp (halfCollarModel.isInteriorPoint_iff.mp hp)
  have hint : interior (range halfCollarModel) ∈ 𝓝 (extChartAt halfCollarModel p p) :=
    isOpen_interior.mem_nhds hp
  have hsymm := continuousAt_extChartAt_symm (I := halfCollarModel) p
  have htend : Tendsto (extChartAt halfCollarModel p).symm
      (𝓝 (extChartAt halfCollarModel p p)) (𝓝 p) := by
    have h := hsymm.tendsto
    rwa [extChartAt_to_inv] at h
  have hcomp : ContinuousAt (fun y => F ((extChartAt halfCollarModel p).symm y))
      (extChartAt halfCollarModel p p) := by
    refine ContinuousAt.comp (f := (extChartAt halfCollarModel p).symm) ?_ hsymm
    rw [extChartAt_to_inv]
    exact hFc
  have hsrc : ∀ᶠ y in 𝓝 (extChartAt halfCollarModel p p),
      F ((extChartAt halfCollarModel p).symm y) ∈ (chartAt (W.kind.Space) b).source := by
    apply hcomp.preimage_mem_nhds
    rw [extChartAt_to_inv]
    exact (chartAt (W.kind.Space) b).open_source.mem_nhds hFb
  filter_upwards [htarget, hint, hsrc, htend.eventually hFd] with y hy hyi hyF hyd
  ext m
  rw [tensor0SModelInChart_apply]
  change cuspMetricError g H F ((extChartAt halfCollarModel p).symm y) _ =
    bilinToTensor0SModel Ec _ m
  rw [bilinToTensor0SModel_apply]
  change localPullInner (I := halfCollarModel) (J := W.model) g F
      ((extChartAt halfCollarModel p).symm y)
      (trivFromE (I := halfCollarModel) p ((extChartAt halfCollarModel p).symm y) (m 0))
      (trivFromE (I := halfCollarModel) p ((extChartAt halfCollarModel p).symm y) (m 1)) -
    H.metric.inner ((extChartAt halfCollarModel p).symm y)
      (trivFromE (I := halfCollarModel) p ((extChartAt halfCollarModel p).symm y) (m 0))
      (trivFromE (I := halfCollarModel) p ((extChartAt halfCollarModel p).symm y) (m 1)) = _
  rw [localPullInner_trivFromE_eq_chartMetricBilin g F p b hy hyi hyF hyd]
  rfl

private theorem taylorPatch_jet3 {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f₁ f₂ : E → F} {x : E} (h : f₁ =ᶠ[𝓝 x] f₂) :
    f₁ x = f₂ x ∧ fderiv ℝ f₁ x = fderiv ℝ f₂ x ∧
      fderiv ℝ (fderiv ℝ f₁) x = fderiv ℝ (fderiv ℝ f₂) x ∧
      fderiv ℝ (fderiv ℝ (fderiv ℝ f₁)) x = fderiv ℝ (fderiv ℝ (fderiv ℝ f₂)) x := by
  have h1 : fderiv ℝ f₁ =ᶠ[𝓝 x] fderiv ℝ f₂ :=
    h.eventuallyEq_nhds.mono fun y hy => Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) hy
  have h2 : fderiv ℝ (fderiv ℝ f₁) =ᶠ[𝓝 x] fderiv ℝ (fderiv ℝ f₂) :=
    h1.eventuallyEq_nhds.mono fun y hy => Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) hy
  exact ⟨h.eq_of_nhds, h.fderiv_eq, h1.fderiv_eq, h2.fderiv_eq⟩

private theorem taylorPatch_finrank :
    Module.finrank ℝ Ec = Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) := by
  simp [Module.finrank_prod]

/-- **Taylor patch (G2.a).** At a point of positive height of a cusp collar with `K ≥ 2`, there
are an open set `P ∋ p` of interior points and a map `f`, a smooth local diffeomorphism on `P`,
with `f p = e p`, `Df p = De p`, and such that the chart representatives at `p` of the metric
errors of `e` and of `f` are `C²` with the same second-order jet. -/
theorem CuspEmbedding.exists_taylorPatch {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ : ℝ} {X : Set W.Carrier}
    (e : CuspEmbedding W g K δ X) (hK : 2 ≤ K) {p : CuspHalfSpace} (hp : p ∈ cuspDomain)
    (hz : 0 < p.2.val 0) :
    ∃ (P : Opens CuspHalfSpace) (f : CuspHalfSpace → W.Carrier), p ∈ P ∧
      (P : Set CuspHalfSpace) ⊆ halfCollarModel.interior CuspHalfSpace ∧
      IsLocalDiffeomorphOn halfCollarModel W.model ∞ f P ∧ f p = e.toFun p ∧
      mfderiv halfCollarModel W.model f p = mfderiv halfCollarModel W.model e.toFun p ∧
      ContDiffAt ℝ 2 (tensor0SModelInChart (𝕜 := ℝ) (I := halfCollarModel) 2 p
        (cuspMetricError g e.cusp e.toFun)) (extChartAt halfCollarModel p p) ∧
      ContDiffAt ℝ 2 (tensor0SModelInChart (𝕜 := ℝ) (I := halfCollarModel) 2 p
        (cuspMetricError g e.cusp f)) (extChartAt halfCollarModel p p) ∧
      tensor0SModelInChart (𝕜 := ℝ) (I := halfCollarModel) 2 p
          (cuspMetricError g e.cusp e.toFun) (extChartAt halfCollarModel p p) =
        tensor0SModelInChart (𝕜 := ℝ) (I := halfCollarModel) 2 p
          (cuspMetricError g e.cusp f) (extChartAt halfCollarModel p p) ∧
      fderiv ℝ (tensor0SModelInChart (𝕜 := ℝ) (I := halfCollarModel) 2 p
          (cuspMetricError g e.cusp e.toFun)) (extChartAt halfCollarModel p p) =
        fderiv ℝ (tensor0SModelInChart (𝕜 := ℝ) (I := halfCollarModel) 2 p
          (cuspMetricError g e.cusp f)) (extChartAt halfCollarModel p p) ∧
      fderiv ℝ (fderiv ℝ (tensor0SModelInChart (𝕜 := ℝ) (I := halfCollarModel) 2 p
          (cuspMetricError g e.cusp e.toFun))) (extChartAt halfCollarModel p p) =
        fderiv ℝ (fderiv ℝ (tensor0SModelInChart (𝕜 := ℝ) (I := halfCollarModel) 2 p
          (cuspMetricError g e.cusp f))) (extChartAt halfCollarModel p p) := by
  classical
  have hpI : halfCollarModel.IsInteriorPoint p := cusp_isInteriorPoint_of_height_pos hz
  have hepI : W.model.IsInteriorPoint (e.toFun p) := by
    apply (W.model.isInteriorPoint_iff_not_isBoundaryPoint (e.toFun p)).mpr
    intro hb
    exact hz.ne' ((CuspEmbedding.boundary_preimage e (p := p) hp).mp hb)
  set c := extChartAt halfCollarModel p with hcdef
  set d := extChartAt W.model (e.toFun p) with hddef
  set y₀ := c p with hy₀def
  set φ := cuspChartMap e.toFun p (e.toFun p) with hφdef
  have hcm : ContMDiffAt halfCollarModel W.model (K + 1) e.toFun p :=
    e.contMDiffOn.contMDiffAt (isOpen_cuspDomain.mem_nhds hp)
  have hrange : range halfCollarModel ∈ 𝓝 y₀ := mem_interior_iff_mem_nhds.mp hpI
  have hφK : ContDiffAt ℝ (K + 1) φ y₀ := (contMDiffAt_iff.mp hcm).2.contDiffAt hrange
  have hφ3 : ContDiffAt ℝ 3 φ y₀ := hφK.of_le (by exact_mod_cast (by omega : 3 ≤ K + 1))
  obtain ⟨ψ, hψ, hψ0, hψ1, hψ2, hψ3⟩ := DifferentialGeometry.Analysis.exists_contDiff_eq_jet3 hφ3
  let f : CuspHalfSpace → W.Carrier := fun z => d.symm (ψ (c z))
  have hepd : e.toFun p ∈ d.source := mem_extChartAt_source (e.toFun p)
  have hφy₀ : φ y₀ = d (e.toFun p) := by
    simp only [hφdef, cuspChartMap, hy₀def, hcdef, extChartAt_to_inv, hddef]
  have hfp : f p = e.toFun p := by
    change d.symm (ψ y₀) = e.toFun p
    rw [hψ0, hφy₀, d.left_inv hepd]
  -- interior charts
  let c' := DifferentialGeometry.Manifold.interiorChart halfCollarModel ∞ p
  let d' := DifferentialGeometry.Manifold.interiorChart W.model ∞ (e.toFun p)
  have hpc' : p ∈ c'.source :=
    (DifferentialGeometry.Manifold.mem_interiorChart_source_iff halfCollarModel ∞ p).mpr hpI
  have hepd' : e.toFun p ∈ d'.source :=
    (DifferentialGeometry.Manifold.mem_interiorChart_source_iff W.model ∞ (e.toFun p)).mpr hepI
  let V : Set Ec := c'.target ∩ ψ ⁻¹' d'.target ∩ {y | (fderiv ℝ ψ y).IsInvertible}
  have hinvset : {L : Ec →L[ℝ] EuclideanSpace ℝ (Fin 3) | L.IsInvertible} =
      range ((↑) : (Ec ≃L[ℝ] EuclideanSpace ℝ (Fin 3)) → Ec →L[ℝ] EuclideanSpace ℝ (Fin 3)) := by
    ext L
    exact ⟨fun ⟨A, hA⟩ => ⟨A, hA⟩, fun ⟨A, hA⟩ => ⟨A, hA⟩⟩
  have hVo : IsOpen V := by
    refine (c'.open_target.inter (d'.open_target.preimage hψ.continuous)).inter ?_
    have hc := hψ.continuous_fderiv (by simp)
    have ho := ContinuousLinearEquiv.isOpen (𝕜 := ℝ) (E := Ec) (F := EuclideanSpace ℝ (Fin 3))
    rw [← hinvset] at ho
    exact ho.preimage hc
  have hctarget (z : Ec) (hz : z ∈ c'.target) : c (c.symm z) = z :=
    c.right_inv (interior_subset hz)
  have hdtarget (z : Ec) (hz : z ∈ V) : d (d.symm (ψ z)) = ψ z :=
    d.right_inv (interior_subset hz.1.2)
  have hfV (z : Ec) (hz : z ∈ V) : f (c'.symm z) = d.symm (ψ z) := by
    change d.symm (ψ (c (c.symm z))) = d.symm (ψ z)
    rw [hctarget z hz.1.1]
  have hdfV (z : Ec) (hz : z ∈ V) : d' (f (c'.symm z)) = ψ z := by
    rw [hfV z hz]
    exact hdtarget z hz
  -- the derivative of `φ` at `y₀` is invertible
  have hed : MDifferentiableAt halfCollarModel W.model e.toFun p :=
    hcm.mdifferentiableAt (by simp)
  have hme : mfderiv halfCollarModel W.model e.toFun p = fderiv ℝ φ y₀ := by
    rw [hed.mfderiv_abuse, fderivWithin_of_mem_nhds hrange]
    rfl
  have hφinv : (fderiv ℝ φ y₀).IsInvertible := by
    have hinj : Injective (fderiv ℝ φ y₀) := by
      have h := e.immersion p hp
      rw [hme] at h
      exact h
    exact ⟨((fderiv ℝ φ y₀).toLinearMap.linearEquivOfInjective hinj
      taylorPatch_finrank).toContinuousLinearEquiv, rfl⟩
  have hy₀V : y₀ ∈ V := by
    refine ⟨⟨c'.map_source hpc', ?_⟩, ?_⟩
    · change ψ y₀ ∈ d'.target
      rw [hψ0, hφy₀]
      exact d'.map_source hepd'
    · change (fderiv ℝ ψ y₀).IsInvertible
      rw [hψ1]
      exact hφinv
  -- the patch
  let P : Opens CuspHalfSpace :=
    ⟨c'.source ∩ c' ⁻¹' V ∩ cuspDomain,
      (c'.contMDiffOn.continuousOn.isOpen_inter_preimage c'.open_source hVo).inter
        isOpen_cuspDomain⟩
  have hpP : p ∈ P := ⟨⟨hpc', hy₀V⟩, hp⟩
  have hPint : (P : Set CuspHalfSpace) ⊆ halfCollarModel.interior CuspHalfSpace := fun x hx =>
    DifferentialGeometry.Manifold.isInteriorPoint_of_mem_interiorChart_source halfCollarModel ∞
      (by simp) hx.1.1
  have hloc : IsLocalDiffeomorphOn halfCollarModel W.model ∞ f P := by
    intro x
    refine DifferentialGeometry.Coordinates.isLocalDiffeomorphAt_of_coordinates c' d' hVo
      x.property.1.1 x.property.1.2 ?_ ?_ ?_
    · intro z hz
      change f (c'.symm z) ∈ d'.source
      rw [hfV z hz]
      refine ⟨?_, ?_⟩
      · have h := d.map_target (interior_subset hz.1.2)
        rwa [hddef, extChartAt_source] at h
      · change d (d.symm (ψ z)) ∈ interior d.target
        rw [hdtarget z hz]
        exact hz.1.2
    · exact hψ.contDiffOn.congr fun z hz => hdfV z hz
    · intro z hz
      have hev : (fun w => d' (f (c'.symm w))) =ᶠ[𝓝 z] ψ := by
        filter_upwards [hVo.mem_nhds hz] with w hw
        exact hdfV w hw
      rw [hev.fderiv_eq]
      exact hz.2
  -- the chart expression of `f` agrees with `ψ` near `y₀`
  have hPn : (P : Set CuspHalfSpace) ∈ 𝓝 p := P.isOpen.mem_nhds hpP
  have hfmap : cuspChartMap f p (e.toFun p) =ᶠ[𝓝 y₀] ψ := by
    filter_upwards [hVo.mem_nhds hy₀V] with y hy
    change d (f (c.symm y)) = ψ y
    exact hdfV y hy
  have hfd : MDifferentiableAt halfCollarModel W.model f p :=
    (hloc ⟨p, hpP⟩).mdifferentiableAt (by simp)
  have hmf : mfderiv halfCollarModel W.model f p = fderiv ℝ ψ y₀ := by
    rw [hfd.mfderiv_abuse, fderivWithin_of_mem_nhds hrange]
    have hw : writtenInExtChartAt halfCollarModel W.model p f = cuspChartMap f p (e.toFun p) := by
      funext y
      simp only [writtenInExtChartAt, Function.comp_apply, cuspChartMap, hfp]
    rw [hw]
    exact hfmap.fderiv_eq
  -- jets
  obtain ⟨j0, j1, j2, j3⟩ := taylorPatch_jet3 hfmap
  have hf3 : ContDiffAt ℝ 3 (cuspChartMap f p (e.toFun p)) y₀ :=
    (hψ.contDiffAt.of_le (by simp)).congr_of_eventuallyEq hfmap
  have hΘ : ContDiffAt ℝ 2 (cuspChartTheta g e.cusp p (e.toFun p)) (φ y₀, fderiv ℝ φ y₀, y₀) := by
    rw [hφy₀]
    exact (cuspChartTheta_contDiffAt g e.cusp hpI hepI (fderiv ℝ φ y₀)).of_le
      (by simp)
  obtain ⟨k1, k2, k0, k1', k2'⟩ := DifferentialGeometry.Analysis.jet2_comp_prolong_eq
    (cuspChartTheta g e.cusp p (e.toFun p)) hΘ hφ3 hf3 (hψ0.symm.trans j0.symm)
    (hψ1.symm.trans j1.symm) (hψ2.symm.trans j2.symm) (hψ3.symm.trans j3.symm)
  have hEe := cuspMetricError_chart_eventuallyEq g e.cusp e.toFun p (e.toFun p) hpI
    hcm.continuousAt (mem_chart_source _ _) (by
      filter_upwards [isOpen_cuspDomain.mem_nhds hp] with z hz
      exact (e.contMDiffOn.contMDiffAt (isOpen_cuspDomain.mem_nhds hz)).mdifferentiableAt
        (by simp))
  have hEf := cuspMetricError_chart_eventuallyEq g e.cusp f p (e.toFun p) hpI
    hfd.continuousAt (by rw [hfp]; exact mem_chart_source _ _) (by
      filter_upwards [hPn] with z hz
      exact (hloc ⟨z, hz⟩).mdifferentiableAt (by simp))
  obtain ⟨e0, e1, e2, -⟩ := taylorPatch_jet3 hEe
  obtain ⟨f0, f1, f2, -⟩ := taylorPatch_jet3 hEf
  refine ⟨P, f, hpP, hPint, hloc, hfp, hmf.trans (hψ1.trans hme.symm),
    k1.congr_of_eventuallyEq hEe, k2.congr_of_eventuallyEq hEf, ?_, ?_, ?_⟩
  · rw [e0, f0]
    exact k0
  · rw [e1, f1]
    exact k1'
  · rw [e2, f2]
    exact k2'

end DifferentialGeometry.Geometry.Collapse
