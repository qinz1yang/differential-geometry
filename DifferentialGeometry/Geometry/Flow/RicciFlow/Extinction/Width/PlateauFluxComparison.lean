import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.PlateauUpperComparisonAttainment
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.DiskAreaMetricFirstVariation
import DifferentialGeometry.Geometry.Metric.ParameterPullbackFamily

noncomputable section

open Bundle Manifold Set MeasureTheory Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Width

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
  [T2Space Q]

theorem SmoothDisk.transportedArea_eq_diskArea_pullbackMetric
    (u : SmoothDisk (I := I) (Q := Q)) (G : ℝ → SmoothRiemannianMetric I Q)
    (Φ : ℝ → Q ≃ₘ⟮I, I⟯ Q) (t : ℝ) :
    u.transportedArea G Φ t = diskArea (Diffeomorph.pullbackMetric (G t) (Φ t)) u.map := by
  rw [SmoothDisk.transportedArea, ← diskArea_comp_diffeomorph (Φ t) (G t) u,
    Diffeomorph.pullbackMetricCross_eq_pullbackMetric]

section ParameterPullbackSmoothness

private theorem pullbackMetric_comp_conj
    {A : Type*} [TopologicalSpace A] [ChartedSpace E A] [IsManifold 𝓘(ℝ, E) ∞ A] [T2Space A]
    (φ : Q ≃ₘ⟮I, 𝓘(ℝ, E)⟯ A) (g : SmoothRiemannianMetric I Q)
    (Φ : Q ≃ₘ⟮I, I⟯ Q) :
    Diffeomorph.pullbackMetric (Diffeomorph.pullbackMetricCross g φ.symm)
        ((φ.symm.trans Φ).trans φ) =
      Diffeomorph.pullbackMetricCross (Diffeomorph.pullbackMetric g Φ) φ.symm := by
  have hcancel : (((φ.symm.trans Φ).trans φ).trans φ.symm) = (φ.symm.trans Φ) := by
    ext x
    simp only [Diffeomorph.coe_trans, Function.comp_apply, φ.symm_apply_apply]
  have hL : Diffeomorph.pullbackMetric (Diffeomorph.pullbackMetricCross g φ.symm)
        ((φ.symm.trans Φ).trans φ) =
      Diffeomorph.pullbackMetricCross g (φ.symm.trans Φ) := by
    rw [← Diffeomorph.pullbackMetricCross_eq_pullbackMetric,
      Diffeomorph.pullbackMetricCross_trans (g := g)
        (Φ := (φ.symm.trans Φ).trans φ) (Ψ := φ.symm), hcancel]
  have hR : Diffeomorph.pullbackMetricCross (Diffeomorph.pullbackMetric g Φ) φ.symm =
      Diffeomorph.pullbackMetricCross g (φ.symm.trans Φ) := by
    rw [← Diffeomorph.pullbackMetricCross_eq_pullbackMetric (g := g) (Φ := Φ),
      Diffeomorph.pullbackMetricCross_trans (g := g) (Φ := φ.symm) (Ψ := Φ)]
  rw [hL, hR]

end ParameterPullbackSmoothness

end DifferentialGeometry.PDE.RicciFlow.Extinction.Width

namespace DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q] [T2Space Q]

theorem MetricFamilySmoothOn.parameterPullback
    (c : Topology.StandardModelCopy I Q E)
    {D : RealTimeInterval} {G : ℝ → SmoothRiemannianMetric I Q}
    (hG : MetricFamilySmoothOn D G)
    {Φ : ℝ → Q ≃ₘ⟮I, I⟯ Q} {T : Set ℝ} (hT : IsOpen T)
    (hΦ : ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞ (fun p : ℝ × Q => Φ p.1 p.2) (T ×ˢ univ))
    (D' : RealTimeInterval) (hopen : D'.carrier = D'.regular)
    (hsub : D'.carrier ⊆ T ∩ D.regular) :
    MetricFamilySmoothOn D' (fun t => Diffeomorph.pullbackMetric (G t) (Φ t)) := by
  let φ : Q ≃ₘ⟮I, 𝓘(ℝ, E)⟯ c.Q := c.equiv
  let G' : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) c.Q :=
    fun t => Diffeomorph.pullbackMetricCross (G t) φ.symm
  have hG' : MetricFamilySmoothOn D G' :=
    MetricFamilySmoothOn.of_pullback (I := I) (M := Q) (J := 𝓘(ℝ, E)) (N := c.Q)
      hG G' (fun x => φ.symm x) φ.symm.contMDiff
      (fun t x v w => Diffeomorph.pullbackMetricCross_inner (G t) φ.symm x v w)
  let Φ' : ℝ → c.Q ≃ₘ⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ c.Q :=
    fun t => (φ.symm.trans (Φ t)).trans φ
  have hΦ'sm : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞
      (fun p : ℝ × c.Q => Φ' p.1 p.2) (T ×ˢ univ) := by
    have h1 : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) (𝓘(ℝ, ℝ).prod I) ∞
        (fun p : ℝ × c.Q => (p.1, φ.symm p.2)) (T ×ˢ univ) :=
      contMDiffOn_fst.prodMk
        (φ.symm.contMDiff.comp_contMDiffOn contMDiffOn_snd)
    have h2 := hΦ.comp h1 (fun p hp => ⟨hp.1, Set.mem_univ _⟩)
    have h3 := φ.contMDiff.comp_contMDiffOn h2
    exact h3.congr (fun p _ => by
      simp only [Φ', Diffeomorph.coe_trans, Function.comp_apply])
  have h' := DifferentialGeometry.Geometry.metricFamilySmoothOn_parameterPullback
    (M := c.Q) hG' hT hΦ'sm D' hopen hsub
  refine MetricFamilySmoothOn.of_pullback (I := 𝓘(ℝ, E)) (M := c.Q) (J := I) (N := Q)
    h' (fun t => Diffeomorph.pullbackMetric (G t) (Φ t)) (fun x => φ x) φ.contMDiff ?_
  intro t x v w
  have hinner := congrArg (fun (m : SmoothRiemannianMetric 𝓘(ℝ, E) c.Q) =>
      m.inner (φ x) (mfderiv I 𝓘(ℝ, E) (φ : Q → c.Q) x v)
        (mfderiv I 𝓘(ℝ, E) (φ : Q → c.Q) x w))
    (DifferentialGeometry.PDE.RicciFlow.Extinction.Width.pullbackMetric_comp_conj φ (G t) (Φ t))
  rw [hinner, Diffeomorph.pullbackMetricCross_inner]
  rw [Diffeomorph.mfderiv_symm_apply_mfderiv_apply φ x v,
    Diffeomorph.mfderiv_symm_apply_mfderiv_apply φ x w, φ.symm_apply_apply]

theorem exists_metricFamilySmoothOn_parameterPullback :
    ∃ (G : ℝ → SmoothRiemannianMetric 𝓘(ℝ, ℂ) ℂ)
      (Φ : ℝ → ℂ ≃ₘ⟮𝓘(ℝ, ℂ), 𝓘(ℝ, ℂ)⟯ ℂ),
      MetricFamilySmoothOn (RealTimeInterval.openInterval (-1) 1 0 (by norm_num))
        (fun t => Diffeomorph.pullbackMetric (G t) (Φ t)) := by
  refine ⟨fun _ => DifferentialGeometry.Geometry.euclideanMetric ℂ,
    fun _ => Diffeomorph.refl 𝓘(ℝ, ℂ) ℂ ∞, ?_⟩
  let D' := RealTimeInterval.openInterval (-1) 1 0 (by norm_num)
  have hG : MetricFamilySmoothOn (I := 𝓘(ℝ, ℂ)) (M := ℂ) D'
      (fun _ => DifferentialGeometry.Geometry.euclideanMetric ℂ) :=
    DifferentialGeometry.Geometry.Curvature.metricFamilySmoothOn_stationary
      (DifferentialGeometry.Geometry.euclideanMetric ℂ) D'
  have hΦ : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, ℂ)) 𝓘(ℝ, ℂ) ∞
      (fun p : ℝ × ℂ => (Diffeomorph.refl 𝓘(ℝ, ℂ) ℂ ∞) p.2) (Set.univ ×ˢ Set.univ) :=
    contMDiffOn_snd
  have hsub : D'.carrier ⊆ Set.univ ∩ D'.regular := fun t ht => ⟨trivial, ht⟩
  exact MetricFamilySmoothOn.parameterPullback
    (Geometry.Topology.standardModelCopy (I := 𝓘(ℝ, ℂ)) (M := ℂ)
      (ContinuousLinearEquiv.refl ℝ ℂ))
    hG isOpen_univ hΦ D' rfl hsub

end DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Width

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
  [T2Space Q] [CompactSpace Q] [SigmaCompactSpace Q] [I.Boundaryless]

theorem SmoothDisk.hasDerivAt_transportedArea_metricFamily
    (c : Geometry.Topology.StandardModelCopy I Q E) [CompactSpace c.Q]
    (u : SmoothDisk (I := I) (Q := Q)) (G : ℝ → SmoothRiemannianMetric I Q)
    {D : RealTimeInterval} {t₀ : ℝ} {hG : MetricFamilySmoothOn D G} (ht₀ : D.regular ∈ 𝓝 t₀)
    {Φ : ℝ → Q ≃ₘ⟮I, I⟯ Q} {T : Set ℝ} (hT : IsOpen T) (hTt : t₀ ∈ T)
    (hΦ : ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞ (fun p : ℝ × Q => Φ p.1 p.2) (T ×ˢ univ))
    (hΦt : Φ t₀ = Diffeomorph.refl I Q ∞)
    {J : Set ℝ} (hJ : J ∈ 𝓝 t₀) (hconf : u.IsConformal (G t₀)) :
    IntegrableOn (diskExtension (u.metricVariationDensity
        (fun r => Diffeomorph.pullbackMetric (G r) (Φ r)) J t₀))
        (Metric.closedBall (0 : ℂ) 1) ∧
      HasDerivAt (fun t => u.transportedArea G Φ t)
        ((1 / 2) * ∫ z in Metric.closedBall (0 : ℂ) 1,
          diskExtension (u.metricVariationDensity
            (fun r => Diffeomorph.pullbackMetric (G r) (Φ r)) J t₀) z) t₀ := by
  obtain ⟨r, _hr, hball⟩ := Metric.mem_nhds_iff.mp (inter_mem (hT.mem_nhds hTt) ht₀)
  have hi : t₀ ∈ Set.Ioo (t₀ - r) (t₀ + r) := ⟨by linarith, by linarith⟩
  let D' := RealTimeInterval.openInterval (t₀ - r) (t₀ + r) t₀ hi
  have hsub : D'.carrier ⊆ T ∩ D.regular := by
    intro t ht
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    change t₀ - r < t ∧ t < t₀ + r at ht
    constructor <;> linarith [ht.1, ht.2]
  have hG' : MetricFamilySmoothOn D'
      (fun t => Diffeomorph.pullbackMetric (G t) (Φ t)) :=
    DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn.parameterPullback
      c hG hT hΦ D' rfl hsub
  have hconf' : u.IsConformal (Diffeomorph.pullbackMetric (G t₀) (Φ t₀)) := by
    rw [hΦt, Diffeomorph.pullbackMetric_refl]
    exact hconf
  obtain ⟨hint, hderiv⟩ := SmoothDisk.hasDerivAt_diskArea_metricFamily (c := c) u
    (fun r => Diffeomorph.pullbackMetric (G r) (Φ r)) J (hG := hG')
    (isOpen_Ioo.mem_nhds hi) hJ hconf'
  refine ⟨hint, ?_⟩
  rw [show (fun t => diskArea (Diffeomorph.pullbackMetric (G t) (Φ t)) u.map) =
      (fun t => u.transportedArea G Φ t) from
    funext fun t => (SmoothDisk.transportedArea_eq_diskArea_pullbackMetric u G Φ t).symm]
    at hderiv
  exact hderiv

end DifferentialGeometry.PDE.RicciFlow.Extinction.Width
