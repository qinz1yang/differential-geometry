import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Periodicity
import DifferentialGeometry.Topology.Manifold.AddCircle.PeriodicExtension
import DifferentialGeometry.Topology.Manifold.AddCircle.VectorField
import DifferentialGeometry.Topology.Manifold.AddCircle.LocalLift
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.DiffeomorphismFamily.CenteredInterval
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Reparametrization
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Connection

noncomputable section

open Manifold Set
open scoped Manifold ContDiff
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

variable [FiniteDimensional ℝ E] [IsManifold I ∞ M] [I.Boundaryless]

omit [I.Boundaryless] in
theorem IsGeometricSolutionOn.tangent_periodic {g : ℝ → SmoothRiemannianMetric I M}
    {c : CurveMap M} {J : Set ℝ} {α : ℝ → ℝ → ℝ}
    (hc : c.IsGeometricSolutionOn g J α) {t : ℝ} (ht : t ∈ J) :
    Function.Periodic (fun x => α x t) 1 := by
  intro x
  have hγ := (contMDiffOn_univ.mp (c.space_slice_contMDiffOn J hc.smooth t ht)).mdifferentiableAt (x := x + 1)
    (by norm_num)
  have hT : c.unitTangent g x t ≠ 0 :=
    smul_ne_zero (inv_ne_zero (c.speed_pos g hc.immersed x t ht).ne') (hc.immersed x t ht)
  apply smul_left_injective ℝ hT
  have h := hc.equation (x + 1) t ht
  rw [c.velocity_add_period J t x, c.curvatureVector_add_period g J hc.smooth hc.immersed t ht x,
    c.unitTangent_add_period g t x hγ, hc.equation x t ht] at h
  change (c.curvatureVector g x t : E) + α x t • c.unitTangent g x t =
    c.curvatureVector g x t + α (x + 1) t • c.unitTangent g x t at h
  exact (add_left_cancel h).symm

omit [I.Boundaryless] in
theorem IsGeometricSolutionOn.neg_tangent_div_speed_periodic
    {g : ℝ → SmoothRiemannianMetric I M} {c : CurveMap M} {J : Set ℝ}
    {α : ℝ → ℝ → ℝ} (hc : c.IsGeometricSolutionOn g J α) {t : ℝ} (ht : t ∈ J) :
    Function.Periodic (fun x => -(α x t / c.speed g x t)) 1 := by
  intro x
  have hγ := (contMDiffOn_univ.mp (c.space_slice_contMDiffOn J hc.smooth t ht)).mdifferentiableAt (x := x + 1)
    (by norm_num)
  change -(α (x + 1) t / c.speed g (x + 1) t) = -(α x t / c.speed g x t)
  have hα : α (x + 1) t = α x t := hc.tangent_periodic ht x
  rw [hα, c.speed_add_period g t x hγ]

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap

end

noncomputable section
open Set Filter Manifold
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [I.Boundaryless] in
theorem CurveMap.IsGeometricSolutionOn.exists_reparametrization_isSolutionOn
    {D : RealTimeInterval} {g : ℝ → SmoothRiemannianMetric I M}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D g)
    {a b : ℝ} (hab : a < b) (hJ : Icc a b ⊆ D.regular)
    {c : CurveMap M} {α : ℝ → ℝ → ℝ}
    (hc : c.IsGeometricSolutionOn g (Icc a b) α) :
    ∃ φ : CircleReparametrization (Icc a b),
      (∀ z, φ.map a z = z) ∧
      CurveMap.IsSolutionOn (I := I) (fun z t => c (φ.map t z) t) g (Icc a b) := by
  let β : ℝ → ℝ → ℝ := fun t x => -(α x t / c.speed g x t)
  have hspeed := CurveMap.Field.smoothOn_speed g hG hJ c hc.smooth hc.immersed
  have hβraw : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => -(α p.1 p.2 / c.speed g p.1 p.2))
      (univ ×ˢ Icc a b) :=
    (hc.tangentSmooth.div hspeed (fun p hp => (c.speed_pos g hc.immersed p.1 p.2 hp.2).ne')).neg
  have hβ : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => β p.1 p.2) (Icc a b ×ˢ univ) := by
    exact hβraw.comp (contDiff_snd.prodMk contDiff_fst).contDiffOn
      (fun p hp => ⟨hp.2, hp.1⟩)
  have hper : ∀ t ∈ Icc a b, Function.Periodic (β t) 1 :=
    fun t ht => hc.neg_tangent_div_speed_periodic ht
  obtain ⟨γ, hγ, hγeq⟩ := AddCircle.exists_contMDiff_extension_of_periodic hβ hper
  let X : ℝ → ∀ z : AddCircle (1 : ℝ), TangentSpace 𝓘(ℝ, ℝ) z :=
    fun t z => γ (t, z) • AddCircle.parameterTangent z
  have hX := AddCircle.contMDiff_parameterTangent_smul hγ
  obtain ⟨F, hF0, hFsm, hGsm, hFode⟩ :=
    DifferentialGeometry.Analysis.ODE.exists_diffeomorph_flow_on_centered_interval X hX a
      (b - a + 1) (by linarith)
  have hsub : Icc a b ⊆ Ioo (a - (b - a + 1)) (a + (b - a + 1)) := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  let φ : CircleReparametrization (Icc a b) :=
    CircleReparametrization.ofContMDiffOn (fun t => (F t).toHomeomorph)
      (hFsm.mono (prod_mono hsub (subset_refl _)))
      (hGsm.mono (prod_mono hsub (subset_refl _)))
  refine ⟨φ, hF0, hc.isSolutionOn_reparam_of_local_lifts φ (uniqueDiffOn_Icc hab) ?_⟩
  intro x t ht
  obtain ⟨l, hl, hleq⟩ := φ.smooth x t ht
  refine ⟨l, hl, hleq, ?_⟩
  have htime : (fun s => (l (x, s) : AddCircle (1 : ℝ))) =ᶠ[𝓝[Icc a b] t]
      fun s => F s (x : AddCircle (1 : ℝ)) := by
    have hi : Continuous (fun s : ℝ => (x, s)) := continuous_const.prodMk continuous_id
    have hm : MapsTo (fun s : ℝ => (x, s)) (Icc a b) (univ ×ˢ Icc a b) :=
      fun s hs => ⟨mem_univ _, hs⟩
    exact (hi.continuousWithinAt.tendsto_nhdsWithin hm).eventually hleq
  have hlt : (l (x, t) : AddCircle (1 : ℝ)) = F t (x : AddCircle (1 : ℝ)) :=
    htime.eq_of_nhdsWithin ht
  have hls : DifferentiableWithinAt ℝ (fun s => l (x, s)) (Icc a b) t := by
    have hm : MapsTo (fun s : ℝ => (x, s)) (Icc a b) (univ ×ˢ Icc a b) :=
      fun s hs => ⟨mem_univ _, hs⟩
    exact (hl.comp t (contDiff_const.prodMk contDiff_id).contDiffWithinAt hm).differentiableWithinAt (by simp)
  have hgval : γ (t, F t (x : AddCircle (1 : ℝ))) =
      -(α (l (x, t)) t) / c.speed g (l (x, t)) t := by
    rw [← hlt, hγeq t ht]
    change -(α (l (x, t)) t / c.speed g (l (x, t)) t) = _
    rw [neg_div]
  have ho := (hFode t (hsub ht) (x : AddCircle (1 : ℝ))).hasMFDerivWithinAt (s := Icc a b)
  change HasMFDerivWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s => F s (x : AddCircle (1 : ℝ)))
    (Icc a b) t ((1 : ℝ →L[ℝ] ℝ).smulRight
      (γ (t, F t (x : AddCircle (1 : ℝ))) •
        AddCircle.parameterTangent (F t (x : AddCircle (1 : ℝ))))) at ho
  rw [hgval] at ho
  exact AddCircle.hasDerivWithinAt_of_local_lift ht (uniqueDiffOn_Icc hab t ht) hls htime ho

omit [I.Boundaryless] in
theorem geometric_solution_gauge_normalization
    {D : RealTimeInterval} {a b : ℝ}
    (B : SmoothMetricWindow (I := I) (M := M) D a b) :
    geometricSolutionGaugeNormalization (I := I) (M := M) B := by
  intro s u hsu hwindow c α hc
  obtain ⟨φ, hφ, hsol⟩ := hc.exists_reparametrization_isSolutionOn B.smooth hsu
    (hwindow.trans B.regular)
  refine ⟨u - s, sub_pos.mpr hsu, by linarith, ?_⟩
  have hsu' : s + (u - s) = u := by ring
  rw [hsu']
  exact
    (show ∃ ψ : CircleReparametrization (Icc s u),
      (∀ z, ψ.map s z = z) ∧
      CurveMap.IsSolutionOn (I := I) (fun z t => c (ψ.map t z) t)
        B.family.metric (Icc s u) from ⟨φ, hφ, hsol⟩)

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

end
