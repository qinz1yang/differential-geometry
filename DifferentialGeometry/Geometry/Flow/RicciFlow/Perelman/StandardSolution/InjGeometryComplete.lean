import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.InjGeometry
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.CutNullComplete
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Minimizer.CompleteManifoldExistence
import DifferentialGeometry.Geometry.Metric.Path.Length
import DifferentialGeometry.Geometry.Exponential.MinimizingGeodesic

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set MeasureTheory
open DifferentialGeometry
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry.PDE.RicciFlow

private theorem exists_larger_regular_slab
    (D : RealTimeInterval) (T tau : ℝ) (htau : 0 < tau)
    (hslab : Icc (T - tau) T ⊆ D.regular) :
    ∃ rho : ℝ, tau < rho ∧ Icc (T - rho) T ⊆ D.regular := by
  have hleft : T - tau ∈ D.regular :=
    hslab ⟨le_rfl, sub_le_self T htau.le⟩
  obtain ⟨a, b, hwin, hreg⟩ := D.exists_Icc_regular hleft
  refine ⟨T - a, ?_, ?_⟩
  · linarith only [hwin.1]
  · intro t ht
    by_cases hold : T - tau ≤ t
    · exact hslab ⟨hold, ht.2⟩
    · apply hreg
      exact ⟨by linarith only [ht.1], by linarith only [hold, hwin.2]⟩

variable {E H M : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [PseudoMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
  [ConnectedSpace M]
  {D : RealTimeInterval}

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_lMin_slab_of_rm
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (K T : ℝ)
    (hg : RiemannianMetricComplete (I := I) (S.base.metric T))
    (x y : M) (tau : ℝ) (htau : 0 < tau)
    (hslab : Icc (T - tau) T ⊆ D.regular)
    (hRm : ∀ t ∈ Icc (T - tau) T, ∀ z : M,
      normSq0S (I := I) (S.base.metric t) z 4
        (S.base.rm04 t z) ≤ K) :
    ∃ Z : TangentSpace I x,
      (Z, tau) ∈ lMinDomain S T x ∧ lExp S T x Z tau = y := by
  obtain ⟨alpha, halpha, ha0, hat⟩ :
      ∃ alpha : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I 1 alpha ∧
        alpha 0 = x ∧ alpha (Real.sqrt tau) = y := by
    let g := S.base.metric T
    let : RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    let : IsContinuousRiemannianBundle E
        (TangentSpace I : M → Type _) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩
    have hxy : Manifold.riemannianEDist I x y < (⊤ : ENNReal) :=
      lt_of_le_of_ne le_top
        (DifferentialGeometry.Geometry.Riemannian.Exponential.riemannianEDist_ne_top
          (I := I) x y)
    obtain ⟨p, hp, _hlen⟩ :=
      Manifold.exists_path_isContMDiffWithSittingInstants_of_riemannianEDist_lt
        (I := I) hxy
    let b : ℝ := Real.sqrt tau
    have hb : 0 < b := Real.sqrt_pos.mpr htau
    let alpha : ℝ → M := fun s ↦ p.extend (s / b)
    have halpha : ContMDiff 𝓘(ℝ, ℝ) I 1 alpha := by
      apply hp.contMDiff.comp
      rw [contMDiff_iff_contDiff]
      fun_prop
    refine ⟨alpha, halpha, ?_, ?_⟩
    · simp only [alpha, zero_div, Path.extend_zero]
    · change p.extend (b / b) = y
      simp only [div_self hb.ne', Path.extend_one]
  exact exists_lMinimizingVector_rm (I := I) S hS K T hg tau htau hslab hRm
    x y alpha halpha ha0 hat

theorem lExp_inj_image_eq_compl_cut_of_rm
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : ℝ)
    (hg : RiemannianMetricComplete (I := I) (S.base.metric T))
    (x : M)
    (hRm : ∀ sigma : ℝ, 0 < sigma → Icc (T - sigma) T ⊆ D.regular →
      ∃ K : ℝ, ∀ t ∈ Icc (T - sigma) T, ∀ z : M,
        normSq0S (I := I) (S.base.metric t) z 4
          (S.base.rm04 t z) ≤ K)
    (tau : ℝ) (htau : 0 < tau)
    (hslab : Icc (T - tau) T ⊆ D.regular) :
    (fun Z : E ↦ lExp S T x Z tau) '' lInjDomain S T x tau =
      (lCutImage S T x tau)ᶜ := by
  classical
  ext y
  constructor
  · rintro ⟨Z, hZ, hZy⟩ hcut
    obtain ⟨W, hWcut, hWy⟩ := hcut
    obtain ⟨hWmin, hWnot⟩ := (mem_lCutDomain S T x tau W).mp hWcut
    obtain ⟨sigma, hsigma, hZmin⟩ := hZ
    have hsigmapos : 0 < sigma := htau.trans hsigma
    have hZdom : (Z, sigma) ∈ lExpPosDom S T x :=
      ((mem_lMinDomain S T x Z sigma).mp hZmin).1
    have hregSigma : Icc (T - sigma) T ⊆ D.regular := by
      intro t ht
      have hnonneg : 0 ≤ T - t := sub_nonneg.mpr ht.2
      have hback : T - t ≤ sigma := by linarith only [ht.1]
      have hsqrt : Real.sqrt (T - t) ∈ Icc (0 : ℝ) (Real.sqrt sigma) :=
        ⟨Real.sqrt_nonneg _, Real.sqrt_le_sqrt hback⟩
      have hclock := lExpPosDom_regularity S T x Z hZdom hsqrt
      have heq : T - (Real.sqrt (T - t)) ^ 2 = t := by
        rw [Real.sq_sqrt hnonneg]
        ring
      simpa only [heq] using hclock
    obtain ⟨K, hK⟩ := hRm sigma hsigmapos hregSigma
    have hWZ : W = Z := lMinVec_unique_lt_of_rm S hS K T x
      hZmin htau hsigma hWmin (hWy.trans hZy.symm) hK
    apply hWnot
    rw [hWZ]
    exact ⟨sigma, hsigma, hZmin⟩
  · intro hy
    obtain ⟨K, hK⟩ := hRm tau htau hslab
    obtain ⟨Z, hZmin, hZy⟩ :=
      exists_lMin_slab_of_rm S hS K T hg x y tau htau hslab hK
    have hZinj : (Z : E) ∈ lInjDomain S T x tau := by
      by_contra hnot
      exact hy ⟨(Z : E),
        (mem_lCutDomain S T x tau (Z : E)).mpr ⟨hZmin, hnot⟩, hZy⟩
    exact ⟨(Z : E), hZinj, hZy⟩

theorem exists_lExpPartial_full_of_rm
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : ℝ)
    (hg : RiemannianMetricComplete (I := I) (S.base.metric T))
    (x : M)
    (hRm : ∀ sigma : ℝ, 0 < sigma → Icc (T - sigma) T ⊆ D.regular →
      ∃ K : ℝ, ∀ t ∈ Icc (T - sigma) T, ∀ z : M,
        normSq0S (I := I) (S.base.metric t) z 4
          (S.base.rm04 t z) ≤ K)
    (tau : ℝ) (htau : 0 < tau)
    (hslab : Icc (T - tau) T ⊆ D.regular) :
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞,
      Φ.source = lInjDomain S T x tau ∧
      Φ.target =
        (fun Z : E ↦ lExp S T x Z tau) '' lInjDomain S T x tau ∧
      Set.EqOn Φ (fun Z : E ↦ lExp S T x Z tau)
        (lInjDomain S T x tau) ∧
      Φ.target = (lCutImage S T x tau)ᶜ ∧
      riemannianVolumeMeasure (I := I) (M := M)
        (S.base.metric (T - tau)) (Φ.targetᶜ) = 0 := by
  obtain ⟨Φ, hsource, himage, hmap⟩ :=
    exists_lExpPartial_of_rm S hS T hg x hRm tau htau
  have hcut : Φ.target = (lCutImage S T x tau)ᶜ :=
    himage.trans
      (lExp_inj_image_eq_compl_cut_of_rm S hS T hg x hRm tau htau hslab)
  obtain ⟨rho, htr, hreg⟩ := exists_larger_regular_slab D T tau htau hslab
  obtain ⟨K, hK⟩ := hRm rho (htau.trans htr) hreg
  have hnull :
      riemannianVolumeMeasure (I := I) (M := M)
        (S.base.metric (T - tau)) (lCutImage S T x tau) = 0 :=
    lCut_null_of_rm S hS K T hg x tau rho htau htr hreg hK
      (S.base.metric (T - tau))
  refine ⟨Φ, hsource, himage, hmap, hcut, ?_⟩
  rw [hcut, compl_compl]
  exact hnull

end DifferentialGeometry.PDE.RicciFlow

end
