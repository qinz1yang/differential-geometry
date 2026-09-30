import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.CalculusGeometry
import Mathlib.Topology.UniformSpace.UniformConvergence
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.AddCircleLift
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
theorem CurveMap.IsGeometricSolutionOn.exists_diffeomorph_flow_isSolutionOn
    {D : RealTimeInterval} {g : ℝ → SmoothRiemannianMetric I M}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D g)
    {a b : ℝ} (hab : a < b) (hJ : Icc a b ⊆ D.regular)
    {c : CurveMap M} {α : ℝ → ℝ → ℝ}
    (hc : c.IsGeometricSolutionOn g (Icc a b) α) :
    ∃ (βcircle : ℝ → AddCircle (1 : ℝ) → ℝ)
      (F : ℝ → (AddCircle (1 : ℝ) ≃ₘ⟮𝓘(ℝ, ℝ), 𝓘(ℝ, ℝ)⟯ AddCircle (1 : ℝ))),
      ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
        (Function.uncurry βcircle) ∧
      (∀ t ∈ Icc a b, ∀ x : ℝ,
        βcircle t (x : AddCircle (1 : ℝ)) = -(α x t) / c.speed g x t) ∧
      (∀ z, F a z = z) ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
        (fun q : ℝ × AddCircle (1 : ℝ) => F q.1 q.2) (Icc a b ×ˢ univ) ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
        (fun q : ℝ × AddCircle (1 : ℝ) => (F q.1).symm q.2) (Icc a b ×ˢ univ) ∧
      (∀ t ∈ Icc a b, ∀ z,
        HasMFDerivWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s => F s z) (Icc a b) t
          ((1 : ℝ →L[ℝ] ℝ).smulRight
            (βcircle t (F t z) • AddCircle.parameterTangent (F t z)))) ∧
      CurveMap.IsSolutionOn (I := I) (fun z t => c (F t z) t) g (Icc a b) := by
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
  refine ⟨(fun t z => γ (t, z)), F, hγ, ?_, hF0,
    hFsm.mono (prod_mono hsub (subset_refl _)),
    hGsm.mono (prod_mono hsub (subset_refl _)), ?_, ?_⟩
  · intro t ht x
    simpa only [β, neg_div] using hγeq t ht x
  · intro t ht z
    exact (hFode t (hsub ht) z).hasMFDerivWithinAt (s := Icc a b)
  · let φ : CircleReparametrization (Icc a b) :=
      CircleReparametrization.ofContMDiffOn (fun t => (F t).toHomeomorph)
        (hFsm.mono (prod_mono hsub (subset_refl _)))
        (hGsm.mono (prod_mono hsub (subset_refl _)))
    apply hc.isSolutionOn_reparam_of_local_lifts φ (uniqueDiffOn_Icc hab)
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
theorem CurveMap.IsGeometricSolutionOn.exists_reparametrization_isSolutionOn
    {D : RealTimeInterval} {g : ℝ → SmoothRiemannianMetric I M}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D g)
    {a b : ℝ} (hab : a < b) (hJ : Icc a b ⊆ D.regular)
    {c : CurveMap M} {α : ℝ → ℝ → ℝ}
    (hc : c.IsGeometricSolutionOn g (Icc a b) α) :
    ∃ φ : CircleReparametrization (Icc a b),
      (∀ z, φ.map a z = z) ∧
      CurveMap.IsSolutionOn (I := I) (fun z t => c (φ.map t z) t) g (Icc a b) := by
  obtain ⟨_, F, _, _, hF0, hFsm, hGsm, _, hsol⟩ :=
    hc.exists_diffeomorph_flow_isSolutionOn hG hab hJ
  let φ : CircleReparametrization (Icc a b) :=
    CircleReparametrization.ofContMDiffOn (fun t => (F t).toHomeomorph) hFsm hGsm
  exact ⟨φ, hF0, hsol⟩

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

noncomputable section

open Filter Set Manifold
open DifferentialGeometry.Geometry.Curvature
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem exists_diffeomorph_flow_lift_tendstoUniformlyOn
    {ι : Type*} {l : Filter ι}
    {D : ι → RealTimeInterval} {DInf : RealTimeInterval}
    {g : ι → ℝ → SmoothRiemannianMetric I M} {gInf : ℝ → SmoothRiemannianMetric I M}
    (hG : ∀ i, MetricFamilySmoothOn (I := I) (M := M) (D i) (g i))
    (hGInf : MetricFamilySmoothOn (I := I) (M := M) DInf gInf)
    {a b : ℝ} (hab : a < b)
    (hJ : ∀ i, Icc a b ⊆ (D i).regular) (hJInf : Icc a b ⊆ DInf.regular)
    {c : ι → CurveMap M} {cInf : CurveMap M}
    {α : ι → ℝ → ℝ → ℝ} {αInf : ℝ → ℝ → ℝ}
    (hc : ∀ i, (c i).IsGeometricSolutionOn (g i) (Icc a b) (α i))
    (hcInf : cInf.IsGeometricSolutionOn gInf (Icc a b) αInf)
    (hv : TendstoUniformlyOn
      (fun i (q : ℝ × ℝ) => -(α i q.1 q.2) / (c i).speed (g i) q.1 q.2)
      (fun q : ℝ × ℝ => -(αInf q.1 q.2) / cInf.speed gInf q.1 q.2)
      l (Icc (0 : ℝ) 1 ×ˢ Icc a b))
    (hDv : TendstoUniformlyOn
      (fun i (q : ℝ × ℝ) =>
        fderiv ℝ (fun x => -(α i x q.2) / (c i).speed (g i) x q.2) q.1)
      (fun q : ℝ × ℝ =>
        fderiv ℝ (fun x => -(αInf x q.2) / cInf.speed gInf x q.2) q.1)
      l (Icc (0 : ℝ) 1 ×ˢ Icc a b))
    (hD₂v : TendstoUniformlyOn
      (fun i (q : ℝ × ℝ) =>
        fderiv ℝ (fderiv ℝ (fun x => -(α i x q.2) / (c i).speed (g i) x q.2)) q.1)
      (fun q : ℝ × ℝ =>
        fderiv ℝ (fderiv ℝ (fun x => -(αInf x q.2) / cInf.speed gInf x q.2)) q.1)
      l (Icc (0 : ℝ) 1 ×ˢ Icc a b)) :
    ∃ (F : ι → ℝ → (AddCircle (1 : ℝ) ≃ₘ⟮𝓘(ℝ, ℝ), 𝓘(ℝ, ℝ)⟯ AddCircle (1 : ℝ)))
      (FInf : ℝ → (AddCircle (1 : ℝ) ≃ₘ⟮𝓘(ℝ, ℝ), 𝓘(ℝ, ℝ)⟯ AddCircle (1 : ℝ)))
      (γ : ι → ℝ → ℝ → ℝ) (γInf : ℝ → ℝ → ℝ),
      (∀ i, CurveMap.IsSolutionOn (I := I) (fun z t => c i (F i t z) t) (g i) (Icc a b)) ∧
      CurveMap.IsSolutionOn (I := I) (fun z t => cInf (FInf t z) t) gInf (Icc a b) ∧
      (∀ i z, F i a z = z) ∧ (∀ z, FInf a z = z) ∧
      (∀ i, ContDiffOn ℝ ∞ (Function.uncurry (γ i)) (univ ×ˢ Icc a b)) ∧
      ContDiffOn ℝ ∞ (Function.uncurry γInf) (univ ×ˢ Icc a b) ∧
      (∀ i x t, t ∈ Icc a b →
        (γ i x t : AddCircle (1 : ℝ)) = F i t (x : AddCircle (1 : ℝ))) ∧
      (∀ x t, t ∈ Icc a b →
        (γInf x t : AddCircle (1 : ℝ)) = FInf t (x : AddCircle (1 : ℝ))) ∧
      (∀ i x t, t ∈ Icc a b → γ i (x + 1) t = γ i x t + 1) ∧
      (∀ x t, t ∈ Icc a b → γInf (x + 1) t = γInf x t + 1) ∧
      (∀ i x, γ i x a = x) ∧ (∀ x, γInf x a = x) ∧
      (∀ i x, IsIntegralCurveOn (γ i x)
        (fun t y => -(α i y t) / (c i).speed (g i) y t) (Icc a b)) ∧
      (∀ x, IsIntegralCurveOn (γInf x)
        (fun t y => -(αInf y t) / cInf.speed gInf y t) (Icc a b)) ∧
      ∀ K : Set ℝ, IsCompact K → TendstoUniformlyOn
        (fun i (q : ℝ × ℝ) => Analysis.ODE.Flow.paramTangentCurve (γ i) q.1 q.2)
        (fun q : ℝ × ℝ => Analysis.ODE.Flow.paramTangentCurve γInf q.1 q.2)
        l (K ×ˢ Icc a b) := by
  classical
  choose β F hβ hβeq hF0 hFsm hGsm hFode hsol using
    fun i => (hc i).exists_diffeomorph_flow_isSolutionOn (hG i) hab (hJ i)
  obtain ⟨βInf, FInf, hβInf, hβInfEq, hFInf0, hFInfSm, hGInfSm, hFInfOde, hsolInf⟩ :=
    hcInf.exists_diffeomorph_flow_isSolutionOn hGInf hab hJInf
  have hvEq (i : ι) (t : ℝ) (ht : t ∈ Icc a b) :
      (fun x : ℝ => β i t (x : AddCircle (1 : ℝ))) =
        fun x => -(α i x t) / (c i).speed (g i) x t :=
    funext (hβeq i t ht)
  have hvInfEq (t : ℝ) (ht : t ∈ Icc a b) :
      (fun x : ℝ => βInf t (x : AddCircle (1 : ℝ))) =
        fun x => -(αInf x t) / cInf.speed gInf x t :=
    funext (hβInfEq t ht)
  have hvc : TendstoUniformlyOn
      (fun i (q : ℝ × ℝ) => β i q.2 (q.1 : AddCircle (1 : ℝ)))
      (fun q : ℝ × ℝ => βInf q.2 (q.1 : AddCircle (1 : ℝ)))
      l (Icc (0 : ℝ) 1 ×ˢ Icc a b) :=
    (hv.congr (Eventually.of_forall fun i q hq => (hβeq i q.2 hq.2 q.1).symm)).congr_right
      (fun q hq => (hβInfEq q.2 hq.2 q.1).symm)
  have hDvc : TendstoUniformlyOn
      (fun i (q : ℝ × ℝ) => fderiv ℝ (fun x : ℝ => β i q.2 (x : AddCircle (1 : ℝ))) q.1)
      (fun q : ℝ × ℝ => fderiv ℝ (fun x : ℝ => βInf q.2 (x : AddCircle (1 : ℝ))) q.1)
      l (Icc (0 : ℝ) 1 ×ˢ Icc a b) := by
    apply (hDv.congr (Eventually.of_forall fun i q hq => ?_)).congr_right
      (fun q hq => ?_)
    · rw [hvEq i q.2 hq.2]
    · rw [hvInfEq q.2 hq.2]
  have hD₂vc : TendstoUniformlyOn
      (fun i (q : ℝ × ℝ) =>
        fderiv ℝ (fderiv ℝ (fun x : ℝ => β i q.2 (x : AddCircle (1 : ℝ)))) q.1)
      (fun q : ℝ × ℝ =>
        fderiv ℝ (fderiv ℝ (fun x : ℝ => βInf q.2 (x : AddCircle (1 : ℝ)))) q.1)
      l (Icc (0 : ℝ) 1 ×ˢ Icc a b) := by
    apply (hD₂v.congr (Eventually.of_forall fun i q hq => ?_)).congr_right
      (fun q hq => ?_)
    · rw [hvEq i q.2 hq.2]
    · rw [hvInfEq q.2 hq.2]
  obtain ⟨γ, γInf, hγsm, hγInfSm, hγcoe, hγInfCoe, hγper, hγInfPer,
      hγ0, hγInf0, hγode, hγInfOde, hconv⟩ :=
    AddCircle.exists_affine_periodic_integralCurve_lift_tendstoUniformlyOn
      (F := fun i t z => F i t z) (FInf := fun t z => FInf t z)
      hab.le hFsm hFInfSm hF0 hFInf0 (fun i => (hβ i).contMDiffOn)
      hβInf.contMDiffOn hFode hFInfOde hvc hDvc hD₂vc
  refine ⟨F, FInf, γ, γInf, hsol, hsolInf, hF0, hFInf0, hγsm, hγInfSm,
    hγcoe, hγInfCoe, hγper, hγInfPer, hγ0, hγInf0, ?_, ?_, hconv⟩
  · intro i x t ht
    have hh := hγode i x t ht
    dsimp only at hh
    rw [hβeq i t ht] at hh
    exact hh
  · intro x t ht
    have hh := hγInfOde x t ht
    dsimp only at hh
    rw [hβInfEq t ht] at hh
    exact hh

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

end

noncomputable section

open Filter Set
open DifferentialGeometry.Geometry.Curvature
open scoped ContDiff Manifold

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem tendstoUniformlyOn_gaugeCoefficient_of_diffusion
    {ι : Type*} {l : Filter ι} {J K : Set ℝ}
    {g : ι → ℝ → SmoothRiemannianMetric I M} {gInf : ℝ → SmoothRiemannianMetric I M}
    {c : ι → CurveMap M} {cInf : CurveMap M}
    (hc : ∀ i, (c i).SmoothOn (I := I) J) (hi : ∀ i, (c i).ImmersedOn (I := I) J)
    (hcInf : cInf.SmoothOn (I := I) J) (hiInf : cInf.ImmersedOn (I := I) J)
    (h₀ : TendstoUniformlyOn
      (fun i (q : ℝ × ℝ) => deriv (fun x => (c i).speed (g i) x q.2 ^ (-2 : ℤ)) q.1)
      (fun q : ℝ × ℝ => deriv (fun x => cInf.speed gInf x q.2 ^ (-2 : ℤ)) q.1)
      l (K ×ˢ J))
    (h₁ : TendstoUniformlyOn
      (fun i (q : ℝ × ℝ) => fderiv ℝ
        (deriv (fun x => (c i).speed (g i) x q.2 ^ (-2 : ℤ))) q.1)
      (fun q : ℝ × ℝ => fderiv ℝ
        (deriv (fun x => cInf.speed gInf x q.2 ^ (-2 : ℤ))) q.1)
      l (K ×ˢ J))
    (h₂ : TendstoUniformlyOn
      (fun i (q : ℝ × ℝ) => fderiv ℝ (fderiv ℝ
        (deriv (fun x => (c i).speed (g i) x q.2 ^ (-2 : ℤ)))) q.1)
      (fun q : ℝ × ℝ => fderiv ℝ (fderiv ℝ
        (deriv (fun x => cInf.speed gInf x q.2 ^ (-2 : ℤ)))) q.1)
      l (K ×ˢ J)) :
    let β := fun i t x =>
      -(deriv (fun y => (c i).speed (g i) y t) x / (c i).speed (g i) x t ^ 2) /
        (c i).speed (g i) x t
    let βInf := fun t x =>
      -(deriv (fun y => cInf.speed gInf y t) x / cInf.speed gInf x t ^ 2) /
        cInf.speed gInf x t
    TendstoUniformlyOn (fun i (q : ℝ × ℝ) => β i q.2 q.1)
      (fun q : ℝ × ℝ => βInf q.2 q.1) l (K ×ˢ J) ∧
    TendstoUniformlyOn (fun i (q : ℝ × ℝ) => fderiv ℝ (β i q.2) q.1)
      (fun q : ℝ × ℝ => fderiv ℝ (βInf q.2) q.1) l (K ×ˢ J) ∧
    TendstoUniformlyOn (fun i (q : ℝ × ℝ) => fderiv ℝ (fderiv ℝ (β i q.2)) q.1)
      (fun q : ℝ × ℝ => fderiv ℝ (fderiv ℝ (βInf q.2)) q.1) l (K ×ˢ J) := by
  intro β βInf
  have hEq (i : ι) (t : ℝ) (ht : t ∈ J) : β i t =
      (1 / 2 : ℝ) • deriv (fun x => (c i).speed (g i) x t ^ (-2 : ℤ)) :=
    funext fun x => neg_deriv_speed_div_sq_div_speed_eq (hc i) (hi i) ht x
  have hEqInf (t : ℝ) (ht : t ∈ J) : βInf t =
      (1 / 2 : ℝ) • deriv (fun x => cInf.speed gInf x t ^ (-2 : ℤ)) :=
    funext fun x => neg_deriv_speed_div_sq_div_speed_eq hcInf hiInf ht x
  have H₀ := ((1 / 2 : ℝ) • ContinuousLinearMap.id ℝ ℝ).uniformContinuous.comp_tendstoUniformlyOn h₀
  have H₁ := ((1 / 2 : ℝ) • ContinuousLinearMap.id ℝ (ℝ →L[ℝ] ℝ)).uniformContinuous.comp_tendstoUniformlyOn h₁
  have H₂ := ((1 / 2 : ℝ) • ContinuousLinearMap.id ℝ (ℝ →L[ℝ] (ℝ →L[ℝ] ℝ))).uniformContinuous.comp_tendstoUniformlyOn h₂
  refine ⟨?_, ?_, ?_⟩
  · apply (H₀.congr (Eventually.of_forall fun i q hq => ?_)).congr_right
      (fun q hq => ?_)
    · rw [hEq i q.2 hq.2]
      rfl
    · rw [hEqInf q.2 hq.2]
      rfl
  · apply (H₁.congr (Eventually.of_forall fun i q hq => ?_)).congr_right
      (fun q hq => ?_)
    · rw [hEq i q.2 hq.2, fderiv_const_smul_field]
      rfl
    · rw [hEqInf q.2 hq.2, fderiv_const_smul_field]
      rfl
  · apply (H₂.congr (Eventually.of_forall fun i q hq => ?_)).congr_right
      (fun q hq => ?_)
    · rw [hEq i q.2 hq.2, fderiv_const_smul_field, fderiv_const_smul_field]
      rfl
    · rw [hEqInf q.2 hq.2, fderiv_const_smul_field, fderiv_const_smul_field]
      rfl

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap

end

noncomputable section

open Filter Set
open DifferentialGeometry.Geometry.Curvature
open scoped ContDiff Manifold

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem tendstoUniformlyOn_iteratedFDeriv_gaugeCoefficient_of_diffusion
    {ι : Type*} {l : Filter ι} {J K : Set ℝ}
    {g : ι → ℝ → SmoothRiemannianMetric I M} {gInf : ℝ → SmoothRiemannianMetric I M}
    {c : ι → CurveMap M} {cInf : CurveMap M}
    (hc : ∀ i, (c i).SmoothOn (I := I) J) (hi : ∀ i, (c i).ImmersedOn (I := I) J)
    (hcInf : cInf.SmoothOn (I := I) J) (hiInf : cInf.ImmersedOn (I := I) J) (k : ℕ)
    (hconv : TendstoUniformlyOn
      (fun i (q : ℝ × ℝ) => iteratedDeriv (k + 1)
        (fun x => (c i).speed (g i) x q.2 ^ (-2 : ℤ)) q.1)
      (fun q : ℝ × ℝ => iteratedDeriv (k + 1)
        (fun x => cInf.speed gInf x q.2 ^ (-2 : ℤ)) q.1)
      l (K ×ˢ J)) :
    let β := fun i t x =>
      -(deriv (fun y => (c i).speed (g i) y t) x / (c i).speed (g i) x t ^ 2) /
        (c i).speed (g i) x t
    let βInf := fun t x =>
      -(deriv (fun y => cInf.speed gInf y t) x / cInf.speed gInf x t ^ 2) /
        cInf.speed gInf x t
    TendstoUniformlyOn
      (fun i (q : ℝ × ℝ) => iteratedFDeriv ℝ k (β i q.2) q.1)
      (fun q : ℝ × ℝ => iteratedFDeriv ℝ k (βInf q.2) q.1) l (K ×ˢ J) := by
  intro β βInf
  have hscalar : TendstoUniformlyOn
      (fun i (q : ℝ × ℝ) => iteratedDeriv k (β i q.2) q.1)
      (fun q : ℝ × ℝ => iteratedDeriv k (βInf q.2) q.1) l (K ×ˢ J) := by
    have hh := ((1 / 2 : ℝ) • ContinuousLinearMap.id ℝ ℝ).uniformContinuous.comp_tendstoUniformlyOn hconv
    apply (hh.congr (Eventually.of_forall fun i q hq => ?_)).congr_right (fun q hq => ?_)
    · exact (iteratedDeriv_neg_deriv_speed_div_sq_div_speed (hc i) (hi i) hq.2 k q.1).symm
    · exact (iteratedDeriv_neg_deriv_speed_div_sq_div_speed hcInf hiInf hq.2 k q.1).symm
  have hh := (ContinuousMultilinearMap.piFieldEquiv ℝ (Fin k) ℝ).isometry.uniformContinuous.comp_tendstoUniformlyOn hscalar
  simpa only [iteratedFDeriv_eq_equiv_comp, Function.comp_def] using hh

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap

end

noncomputable section

open Filter Set Manifold
open DifferentialGeometry.Geometry.Curvature
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem exists_diffeomorph_flow_lift_iteratedFDeriv_tendstoUniformlyOn
    {ι : Type*} {l : Filter ι}
    {D : ι → RealTimeInterval} {DInf : RealTimeInterval}
    {g : ι → ℝ → SmoothRiemannianMetric I M} {gInf : ℝ → SmoothRiemannianMetric I M}
    (hG : ∀ i, MetricFamilySmoothOn (I := I) (M := M) (D i) (g i))
    (hGInf : MetricFamilySmoothOn (I := I) (M := M) DInf gInf)
    {a b : ℝ} (hab : a < b)
    (hJ : ∀ i, Icc a b ⊆ (D i).regular) (hJInf : Icc a b ⊆ DInf.regular)
    {c : ι → CurveMap M} {cInf : CurveMap M}
    {α : ι → ℝ → ℝ → ℝ} {αInf : ℝ → ℝ → ℝ}
    (hc : ∀ i, (c i).IsGeometricSolutionOn (g i) (Icc a b) (α i))
    (hcInf : cInf.IsGeometricSolutionOn gInf (Icc a b) αInf)
    (hconv : ∀ k : ℕ, TendstoUniformlyOn
      (fun i (q : ℝ × ℝ) => iteratedFDeriv ℝ k
        (fun x : ℝ => -(α i x q.2) / (c i).speed (g i) x q.2) q.1)
      (fun q : ℝ × ℝ => iteratedFDeriv ℝ k
        (fun x : ℝ => -(αInf x q.2) / cInf.speed gInf x q.2) q.1)
      l (Icc (0 : ℝ) 1 ×ˢ Icc a b)) :
    ∃ (F : ι → ℝ → (AddCircle (1 : ℝ) ≃ₘ⟮𝓘(ℝ, ℝ), 𝓘(ℝ, ℝ)⟯ AddCircle (1 : ℝ)))
      (FInf : ℝ → (AddCircle (1 : ℝ) ≃ₘ⟮𝓘(ℝ, ℝ), 𝓘(ℝ, ℝ)⟯ AddCircle (1 : ℝ)))
      (γ : ι → ℝ → ℝ → ℝ) (γInf : ℝ → ℝ → ℝ),
      (∀ i, CurveMap.IsSolutionOn (I := I) (fun z t => c i (F i t z) t) (g i) (Icc a b)) ∧
      CurveMap.IsSolutionOn (I := I) (fun z t => cInf (FInf t z) t) gInf (Icc a b) ∧
      (∀ i z, F i a z = z) ∧ (∀ z, FInf a z = z) ∧
      (∀ i, ContDiffOn ℝ ∞ (Function.uncurry (γ i)) (univ ×ˢ Icc a b)) ∧
      ContDiffOn ℝ ∞ (Function.uncurry γInf) (univ ×ˢ Icc a b) ∧
      (∀ i x t, t ∈ Icc a b →
        (γ i x t : AddCircle (1 : ℝ)) = F i t (x : AddCircle (1 : ℝ))) ∧
      (∀ x t, t ∈ Icc a b →
        (γInf x t : AddCircle (1 : ℝ)) = FInf t (x : AddCircle (1 : ℝ))) ∧
      (∀ i x t, t ∈ Icc a b → γ i (x + 1) t = γ i x t + 1) ∧
      (∀ x t, t ∈ Icc a b → γInf (x + 1) t = γInf x t + 1) ∧
      (∀ i x, γ i x a = x) ∧ (∀ x, γInf x a = x) ∧
      (∀ i x, IsIntegralCurveOn (γ i x)
        (fun t y => -(α i y t) / (c i).speed (g i) y t) (Icc a b)) ∧
      (∀ x, IsIntegralCurveOn (γInf x)
        (fun t y => -(αInf y t) / cInf.speed gInf y t) (Icc a b)) ∧
      ∀ K : Set ℝ, IsCompact K → ∀ k : ℕ, TendstoUniformlyOn
        (fun i (q : ℝ × ℝ) => iteratedFDeriv ℝ k (fun x => γ i x q.2) q.1)
        (fun q : ℝ × ℝ => iteratedFDeriv ℝ k (fun x => γInf x q.2) q.1)
        l (K ×ˢ Icc a b) := by
  classical
  choose β F hβ hβeq hF0 hFsm hGsm hFode hsol using
    fun i => (hc i).exists_diffeomorph_flow_isSolutionOn (hG i) hab (hJ i)
  obtain ⟨βInf, FInf, hβInf, hβInfEq, hFInf0, hFInfSm, hGInfSm, hFInfOde, hsolInf⟩ :=
    hcInf.exists_diffeomorph_flow_isSolutionOn hGInf hab hJInf
  have hvEq (i : ι) (t : ℝ) (ht : t ∈ Icc a b) :
      (fun x : ℝ => β i t (x : AddCircle (1 : ℝ))) =
        fun x => -(α i x t) / (c i).speed (g i) x t :=
    funext (hβeq i t ht)
  have hvInfEq (t : ℝ) (ht : t ∈ Icc a b) :
      (fun x : ℝ => βInf t (x : AddCircle (1 : ℝ))) =
        fun x => -(αInf x t) / cInf.speed gInf x t :=
    funext (hβInfEq t ht)
  have hconvβ : ∀ k : ℕ, TendstoUniformlyOn
      (fun i (q : ℝ × ℝ) => iteratedFDeriv ℝ k
        (fun x : ℝ => β i q.2 (x : AddCircle (1 : ℝ))) q.1)
      (fun q : ℝ × ℝ => iteratedFDeriv ℝ k
        (fun x : ℝ => βInf q.2 (x : AddCircle (1 : ℝ))) q.1)
      l (Icc (0 : ℝ) 1 ×ˢ Icc a b) := by
    intro k
    apply ((hconv k).congr (Eventually.of_forall fun i q hq => ?_)).congr_right
      (fun q hq => ?_)
    · rw [hvEq i q.2 hq.2]
    · rw [hvInfEq q.2 hq.2]
  obtain ⟨γ, γInf, hγsm, hγInfSm, hγcoe, hγInfCoe, hγper, hγInfPer,
      hγ0, hγInf0, hγode, hγInfOde, hconv⟩ :=
    AddCircle.exists_affine_periodic_integralCurve_lift_iteratedFDeriv_tendstoUniformlyOn
      (F := fun i t z => F i t z) (FInf := fun t z => FInf t z)
      hab.le hFsm hFInfSm hF0 hFInf0 (fun i => (hβ i).contMDiffOn)
      hβInf.contMDiffOn hFode hFInfOde hconvβ
  refine ⟨F, FInf, γ, γInf, hsol, hsolInf, hF0, hFInf0, hγsm, hγInfSm,
    hγcoe, hγInfCoe, hγper, hγInfPer, hγ0, hγInf0, ?_, ?_, hconv⟩
  · intro i x t ht
    have hh := hγode i x t ht
    dsimp only at hh
    rw [hβeq i t ht] at hh
    exact hh
  · intro x t ht
    have hh := hγInfOde x t ht
    dsimp only at hh
    rw [hβInfEq t ht] at hh
    exact hh

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

end
