import DifferentialGeometry.Geometry.Submanifold.SecondFundamentalForm.RetractionResidual
import DifferentialGeometry.Geometry.Metric.Family.ChartCurvature.ChristoffelContraction
import DifferentialGeometry.Analysis.Parabolic.Euclidean.InvariantImage
import DifferentialGeometry.Analysis.Parabolic.Euclidean.PeriodicJet

noncomputable section
open Set
open scoped ContDiff Manifold NNReal

namespace DifferentialGeometry.Analysis.Parabolic

open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Curvature

section

variable {E F H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem retractionParabolicResidual_christoffel_eq_zero
    (g : SmoothRiemannianMetric I M) {O : TopologicalSpace.Opens F}
    (G : ℝ → SmoothRiemannianMetric 𝓘(ℝ, F) O) (α : O) (t : ℝ)
    {e : M → O} (he : ContMDiff I 𝓘(ℝ, F) ∞ e)
    (hgeo : hasVanishingSecondFundamentalFormAlongCurves g (G t) e)
    {r : F → M} (hleft : ∀ x, r (e x) = x) {z : F}
    (hr : MDifferentiableAt 𝓘(ℝ, F) I r z)
    (hP : ContDiffAt ℝ 2 (fun y => (e (r y) : F)) (e (r z) : F)) (v : F)
    (a : ℝ × F × F → ℝ) :
    retractionParabolicResidual (fun y => (e (r y) : F))
      (fun q => a q • chartChristoffelContraction (G q.1) α q.2.2 q.2.2 q.2.1) a
      (t, (e (r z) : F), fderiv ℝ (fun y => (e (r y) : F)) z v) = 0 := by
  have h := retraction_christoffel_residual_fderiv_eq_zero_open g (G t) he hgeo
    hleft hr hP v
  dsimp only at h
  rw [chartChristoffelContraction_opens_basepoint_eq O (G t) (e (r z)) α] at h
  unfold retractionParabolicResidual
  simp only [map_smul]
  rw [← smul_sub, ← smul_add, h, smul_zero]

theorem exists_retractionParabolicResidual_christoffel_bound_on_open_set
    (g : ℝ → SmoothRiemannianMetric I M) {O : TopologicalSpace.Opens F}
    (G : ℝ → SmoothRiemannianMetric 𝓘(ℝ, F) O) (α : O)
    {e : M → O} (he : ContMDiff I 𝓘(ℝ, F) ∞ e)
    {J : Set ℝ} (hgeo : ∀ t ∈ J, hasVanishingSecondFundamentalFormAlongCurves (g t) (G t) e)
    {r : F → M} (hleft : ∀ x, r (e x) = x)
    {V : Set F} {U K : Set (ℝ × F × F)}
    (hU : IsOpen U) (hV : IsOpen V)
    (hK : IsCompact K) (hKU : K ⊆ U) (hUJV : U ⊆ J ×ˢ V ×ˢ univ)
    (hr : ∀ z ∈ V, MDifferentiableAt 𝓘(ℝ, F) I r z)
    (hP : ContDiffOn ℝ 3 (fun y => (e (r y) : F)) V)
    (hΓ : ContDiffOn ℝ 1
      (fun q : ℝ × F × F => chartChristoffelContraction (G q.1) α q.2.2 q.2.2 q.2.1) U)
    {a : ℝ × F × F → ℝ} (ha : ContDiffOn ℝ 1 a U)
    (hPU : ∀ q ∈ K,
      (q.1, (e (r q.2.1) : F), fderiv ℝ (fun y => (e (r y) : F)) q.2.1 q.2.2) ∈ U) :
    ∃ L : ℝ≥0, ∀ q ∈ K,
      ‖retractionParabolicResidual (fun y => (e (r y) : F))
        (fun q => a q • chartChristoffelContraction (G q.1) α q.2.2 q.2.2 q.2.1) a q‖ ≤
        L * (‖q.2.1 - (e (r q.2.1) : F)‖ +
          ‖q.2.2 - fderiv ℝ (fun y => (e (r y) : F)) q.2.1 q.2.2‖) := by
  have hzero : ∀ q ∈ K,
      retractionParabolicResidual (fun y => (e (r y) : F))
        (fun q => a q • chartChristoffelContraction (G q.1) α q.2.2 q.2.2 q.2.1) a
        (q.1, (e (r q.2.1) : F), fderiv ℝ (fun y => (e (r y) : F)) q.2.1 q.2.2) = 0 := by
    intro q hq
    exact retractionParabolicResidual_christoffel_eq_zero (g q.1) G α q.1 he
      (hgeo q.1 (hUJV (hKU hq)).1) hleft (hr _ (hUJV (hKU hq)).2.1)
      ((hP.contDiffAt (hV.mem_nhds (hUJV (hPU q hq)).2.1)).of_le (by norm_num)) q.2.2 a
  exact exists_retractionParabolicResidual_bound hU hV hK hKU hP (ha.smul hΓ) ha
    (fun q hq => (hUJV hq).2.1) hPU hzero

theorem exists_retractionParabolicResidual_christoffel_bound
    (g : ℝ → SmoothRiemannianMetric I M) {O : TopologicalSpace.Opens F}
    (G : ℝ → SmoothRiemannianMetric 𝓘(ℝ, F) O) (α : O)
    {e : M → O} (he : ContMDiff I 𝓘(ℝ, F) ∞ e)
    {J : Set ℝ} (hgeo : ∀ t ∈ J, hasVanishingSecondFundamentalFormAlongCurves (g t) (G t) e)
    {r : F → M} (hleft : ∀ x, r (e x) = x)
    {V : Set F} {K : Set (ℝ × F × F)}
    (hJ : IsOpen J) (hV : IsOpen V)
    (hK : IsCompact K) (hKU : K ⊆ J ×ˢ V ×ˢ univ)
    (hr : ∀ z ∈ V, MDifferentiableAt 𝓘(ℝ, F) I r z)
    (hP : ContDiffOn ℝ 3 (fun y => (e (r y) : F)) V)
    (hΓ : ContDiffOn ℝ 1
      (fun q : ℝ × F × F => chartChristoffelContraction (G q.1) α q.2.2 q.2.2 q.2.1)
      (J ×ˢ V ×ˢ univ))
    {a : ℝ × F × F → ℝ} (ha : ContDiffOn ℝ 1 a (J ×ˢ V ×ˢ univ))
    (heV : range (fun x => (e x : F)) ⊆ V) :
    ∃ L : ℝ≥0, ∀ q ∈ K,
      ‖retractionParabolicResidual (fun y => (e (r y) : F))
        (fun q => a q • chartChristoffelContraction (G q.1) α q.2.2 q.2.2 q.2.1) a q‖ ≤
        L * (‖q.2.1 - (e (r q.2.1) : F)‖ +
          ‖q.2.2 - fderiv ℝ (fun y => (e (r y) : F)) q.2.1 q.2.2‖) := by
  exact exists_retractionParabolicResidual_christoffel_bound_on_open_set g G α he hgeo hleft
    (hJ.prod (hV.prod isOpen_univ)) hV hK hKU Subset.rfl hr hP hΓ ha
    (fun q hq => ⟨(hKU hq).1, heV (mem_range_self _), mem_univ _⟩)


theorem exists_retractionParabolicResidual_christoffel_bound_on_open_set_of_metricFamilySmoothOn
    (g : ℝ → SmoothRiemannianMetric I M) {O : TopologicalSpace.Opens F}
    (G : ℝ → SmoothRiemannianMetric 𝓘(ℝ, F) O) (α : O)
    {D : RealTimeInterval} (hG : MetricFamilySmoothOn D G)
    {e : M → O} (he : ContMDiff I 𝓘(ℝ, F) ∞ e)
    {J : Set ℝ} (hgeo : ∀ t ∈ J, hasVanishingSecondFundamentalFormAlongCurves (g t) (G t) e)
    {r : F → M} (hleft : ∀ x, r (e x) = x)
    {V : Set F} {U K : Set (ℝ × F × F)}
    (hU : IsOpen U) (hJD : J ⊆ D.regular) (hV : IsOpen V) (hVO : V ⊆ O)
    (hK : IsCompact K) (hKU : K ⊆ U) (hUJV : U ⊆ J ×ˢ V ×ˢ univ)
    (hr : ContMDiffOn 𝓘(ℝ, F) I 3 r V)
    {a : ℝ × F × F → ℝ} (ha : ContDiffOn ℝ 1 a U)
    (hPU : ∀ q ∈ K,
      (q.1, (e (r q.2.1) : F), fderiv ℝ (fun y => (e (r y) : F)) q.2.1 q.2.2) ∈ U) :
    ∃ L : ℝ≥0, ∀ q ∈ K,
      ‖retractionParabolicResidual (fun y => (e (r y) : F))
        (fun q => a q • chartChristoffelContraction (G q.1) α q.2.2 q.2.2 q.2.1) a q‖ ≤
        L * (‖q.2.1 - (e (r q.2.1) : F)‖ +
          ‖q.2.2 - fderiv ℝ (fun y => (e (r y) : F)) q.2.1 q.2.2‖) := by
  have hP : ContDiffOn ℝ 3 (fun y => (e (r y) : F)) V :=
    (((contMDiff_subtype_val.comp he).of_le (by decide : (3 : ℕ∞ω) ≤ ∞)).comp_contMDiffOn hr).contDiffOn
  exact exists_retractionParabolicResidual_christoffel_bound_on_open_set g G α he hgeo hleft
    hU hV hK hKU hUJV
    (fun z hz => (hr.contMDiffAt (hV.mem_nhds hz)).mdifferentiableAt (by norm_num)) hP
    (((hG.chartChristoffelContraction_opens_joint_contDiffOn α hJD hVO).of_le (by simp)).mono hUJV)
    ha hPU

theorem exists_retractionParabolicResidual_christoffel_bound_of_metricFamilySmoothOn
    (g : ℝ → SmoothRiemannianMetric I M) {O : TopologicalSpace.Opens F}
    (G : ℝ → SmoothRiemannianMetric 𝓘(ℝ, F) O) (α : O)
    {D : RealTimeInterval} (hG : MetricFamilySmoothOn D G)
    {e : M → O} (he : ContMDiff I 𝓘(ℝ, F) ∞ e)
    {J : Set ℝ} (hgeo : ∀ t ∈ J, hasVanishingSecondFundamentalFormAlongCurves (g t) (G t) e)
    {r : F → M} (hleft : ∀ x, r (e x) = x)
    {V : Set F} {K : Set (ℝ × F × F)}
    (hJ : IsOpen J) (hJD : J ⊆ D.regular) (hV : IsOpen V) (hVO : V ⊆ O)
    (hK : IsCompact K) (hKU : K ⊆ J ×ˢ V ×ˢ univ)
    (hr : ContMDiffOn 𝓘(ℝ, F) I 3 r V)
    {a : ℝ × F × F → ℝ} (ha : ContDiffOn ℝ 1 a (J ×ˢ V ×ˢ univ))
    (heV : range (fun x => (e x : F)) ⊆ V) :
    ∃ L : ℝ≥0, ∀ q ∈ K,
      ‖retractionParabolicResidual (fun y => (e (r y) : F))
        (fun q => a q • chartChristoffelContraction (G q.1) α q.2.2 q.2.2 q.2.1) a q‖ ≤
        L * (‖q.2.1 - (e (r q.2.1) : F)‖ +
          ‖q.2.2 - fderiv ℝ (fun y => (e (r y) : F)) q.2.1 q.2.2‖) := by
  exact exists_retractionParabolicResidual_christoffel_bound_on_open_set_of_metricFamilySmoothOn
    g G α hG he hgeo hleft (hJ.prod (hV.prod isOpen_univ)) hJD hV hVO hK hKU Subset.rfl
    hr ha (fun q hq => ⟨(hKU hq).1, heV (mem_range_self _), mem_univ _⟩)


end

variable {E F H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]


theorem periodic_mem_range_of_christoffel_parabolic_equation_on_open_set
    (g : ℝ → SmoothRiemannianMetric I M) {O : TopologicalSpace.Opens F}
    (G : ℝ → SmoothRiemannianMetric 𝓘(ℝ, F) O) (α : O)
    {D : RealTimeInterval} (hG : MetricFamilySmoothOn D G)
    {e : M → O} (he : ContMDiff I 𝓘(ℝ, F) ∞ e)
    {J : Set ℝ} (hgeo : ∀ t ∈ J, hasVanishingSecondFundamentalFormAlongCurves (g t) (G t) e)
    {r : F → M} (hleft : ∀ x, r (e x) = x)
    {V : Set F} {U K : Set (ℝ × F × F)}
    (hU : IsOpen U) (hJD : J ⊆ D.regular) (hV : IsOpen V) (hVO : V ⊆ O)
    (hK : IsCompact K) (hKU : K ⊆ U) (hUJV : U ⊆ J ×ˢ V ×ˢ univ)
    (hr : ContMDiffOn 𝓘(ℝ, F) I 3 r V)
    {a : ℝ × F × F → ℝ} (ha : ContDiffOn ℝ 1 a U)
    (hPU : ∀ q ∈ K,
      (q.1, (e (r q.2.1) : F), fderiv ℝ (fun y => (e (r y) : F)) q.2.1 q.2.2) ∈ U)
    {u : ℝ → ℝ → F} {s v δ : ℝ} (hsv : s < v) (hδ : 0 < δ)
    (hper : ∀ x t, u (x + 1) t = u x t)
    (hcont : ContinuousOn (Function.uncurry u) (Icc 0 1 ×ˢ Icc s v))
    (hinit : ∀ x, u x s ∈ range (fun y => (e y : F)))
    (hx : ∀ x t, t ∈ Ioo s v → ContDiffAt ℝ 2 (fun y => u y t) x)
    (ht : ∀ x t, t ∈ Ioo s v → DifferentiableAt ℝ (fun τ => u x τ) t)
    (hjet : ∀ x t, t ∈ Icc s v → (t, u x t, deriv (fun y => u y t) x) ∈ K)
    (hell : ∀ q ∈ K, δ ≤ a q)
    (heq : ∀ x t, t ∈ Ioo s v →
      deriv (fun τ => u x τ) t -
          a (t, u x t, deriv (fun y => u y t) x) • deriv (deriv (fun y => u y t)) x =
        a (t, u x t, deriv (fun y => u y t) x) •
          chartChristoffelContraction (G t) α (deriv (fun y => u y t) x)
            (deriv (fun y => u y t) x) (u x t)) :
    ∀ x t, t ∈ Icc s v → u x t ∈ range (fun y => (e y : F)) := by
  obtain ⟨L, hL⟩ := exists_retractionParabolicResidual_christoffel_bound_on_open_set_of_metricFamilySmoothOn
    g G α hG he hgeo hleft hU hJD hV hVO hK hKU hUJV hr ha hPU
  have hP : ContDiffOn ℝ 3 (fun y => (e (r y) : F)) V :=
    (((contMDiff_subtype_val.comp he).of_le (by decide : (3 : ℕ∞ω) ≤ ∞)).comp_contMDiffOn hr).contDiffOn
  have hfix := periodic_comp_eq_of_parabolic_residual_bound
    (P := fun y => (e (r y) : F))
    (a := fun x t => a (t, u x t, deriv (fun y => u y t) x))
    (L := L) hsv hδ hper hcont
    (hP.continuousOn.mono (by
      rintro _ ⟨⟨x, t⟩, hxt, rfl⟩
      exact (hUJV (hKU (hjet x t hxt.2))).2.1))
    (fun x => by obtain ⟨y, hy⟩ := hinit x; rw [← hy, hleft]) hx ht
    (fun x t ht' => (hP.contDiffAt
      (hV.mem_nhds (hUJV (hKU (hjet x t ⟨ht'.1.le, ht'.2.le⟩))).2.1)).of_le (by norm_num))
    (fun x t ht' => hell _ (hjet x t ⟨ht'.1.le, ht'.2.le⟩)) (by
      intro x t ht'
      rw [heq x t ht']
      exact hL _ (hjet x t ⟨ht'.1.le, ht'.2.le⟩))
  intro x t ht'
  exact ⟨r (u x t), hfix x t ht'⟩

theorem periodic_mem_range_of_christoffel_parabolic_equation
    (g : ℝ → SmoothRiemannianMetric I M) {O : TopologicalSpace.Opens F}
    (G : ℝ → SmoothRiemannianMetric 𝓘(ℝ, F) O) (α : O)
    {D : RealTimeInterval} (hG : MetricFamilySmoothOn D G)
    {e : M → O} (he : ContMDiff I 𝓘(ℝ, F) ∞ e)
    {J : Set ℝ} (hgeo : ∀ t ∈ J, hasVanishingSecondFundamentalFormAlongCurves (g t) (G t) e)
    {r : F → M} (hleft : ∀ x, r (e x) = x)
    {V : Set F} {K : Set (ℝ × F × F)}
    (hJ : IsOpen J) (hJD : J ⊆ D.regular) (hV : IsOpen V) (hVO : V ⊆ O)
    (hK : IsCompact K) (hKU : K ⊆ J ×ˢ V ×ˢ univ)
    (hr : ContMDiffOn 𝓘(ℝ, F) I 3 r V)
    {a : ℝ × F × F → ℝ} (ha : ContDiffOn ℝ 1 a (J ×ˢ V ×ˢ univ))
    (heV : range (fun x => (e x : F)) ⊆ V)
    {u : ℝ → ℝ → F} {s v δ : ℝ} (hsv : s < v) (hδ : 0 < δ)
    (hper : ∀ x t, u (x + 1) t = u x t)
    (hcont : ContinuousOn (Function.uncurry u) (Icc 0 1 ×ˢ Icc s v))
    (hinit : ∀ x, u x s ∈ range (fun y => (e y : F)))
    (hx : ∀ x t, t ∈ Ioo s v → ContDiffAt ℝ 2 (fun y => u y t) x)
    (ht : ∀ x t, t ∈ Ioo s v → DifferentiableAt ℝ (fun τ => u x τ) t)
    (hjet : ∀ x t, t ∈ Icc s v → (t, u x t, deriv (fun y => u y t) x) ∈ K)
    (hell : ∀ q ∈ K, δ ≤ a q)
    (heq : ∀ x t, t ∈ Ioo s v →
      deriv (fun τ => u x τ) t -
          a (t, u x t, deriv (fun y => u y t) x) • deriv (deriv (fun y => u y t)) x =
        a (t, u x t, deriv (fun y => u y t) x) •
          chartChristoffelContraction (G t) α (deriv (fun y => u y t) x)
            (deriv (fun y => u y t) x) (u x t)) :
    ∀ x t, t ∈ Icc s v → u x t ∈ range (fun y => (e y : F)) := by
  exact periodic_mem_range_of_christoffel_parabolic_equation_on_open_set g G α hG he hgeo hleft
    (hJ.prod (hV.prod isOpen_univ)) hJD hV hVO hK hKU Subset.rfl hr ha
    (fun q hq => ⟨(hKU hq).1, heV (mem_range_self _), mem_univ _⟩)
    hsv hδ hper hcont hinit hx ht hjet hell heq


theorem periodic_mem_range_of_christoffel_parabolic_equation_on_open_set_of_continuous_deriv
    (g : ℝ → SmoothRiemannianMetric I M) {O : TopologicalSpace.Opens F}
    (G : ℝ → SmoothRiemannianMetric 𝓘(ℝ, F) O) (α : O)
    {D : RealTimeInterval} (hG : MetricFamilySmoothOn D G)
    {e : M → O} (he : ContMDiff I 𝓘(ℝ, F) ∞ e)
    {J : Set ℝ} (hgeo : ∀ t ∈ J, hasVanishingSecondFundamentalFormAlongCurves (g t) (G t) e)
    {r : F → M} (hleft : ∀ x, r (e x) = x)
    {V : Set F} {U : Set (ℝ × F × F)}
    (hU : IsOpen U) (hJD : J ⊆ D.regular) (hV : IsOpen V) (hVO : V ⊆ O)
    (hr : ContMDiffOn 𝓘(ℝ, F) I 3 r V)
    {a : ℝ × F × F → ℝ} (ha : ContDiffOn ℝ 1 a U) (hUJV : U ⊆ J ×ˢ V ×ˢ univ)
    {u : ℝ → ℝ → F} {s v δ : ℝ} (hsv : s < v) (hδ : 0 < δ)
    (hper : ∀ x t, u (x + 1) t = u x t)
    (hcont : ContinuousOn (Function.uncurry u) (Icc 0 1 ×ˢ Icc s v))
    (hinit : ∀ x, u x s ∈ range (fun y => (e y : F)))
    (hx : ∀ x t, t ∈ Ioo s v → ContDiffAt ℝ 2 (fun y => u y t) x)
    (ht : ∀ x t, t ∈ Ioo s v → DifferentiableAt ℝ (fun τ => u x τ) t)
    (hDu : ContinuousOn (fun p : ℝ × ℝ => deriv (fun y => u y p.2) p.1)
      (Icc 0 1 ×ˢ Icc s v))
    (hjetU : ∀ x t, t ∈ Icc s v → (t, u x t, deriv (fun y => u y t) x) ∈ U)
    (hprojectedJetU : ∀ x t, t ∈ Icc s v →
      (t, (e (r (u x t)) : F),
        fderiv ℝ (fun y => (e (r y) : F)) (u x t) (deriv (fun y => u y t) x)) ∈ U)
    (hell : ∀ x t, t ∈ Icc s v → δ ≤ a (t, u x t, deriv (fun y => u y t) x))
    (heq : ∀ x t, t ∈ Ioo s v →
      deriv (fun τ => u x τ) t -
          a (t, u x t, deriv (fun y => u y t) x) • deriv (deriv (fun y => u y t)) x =
        a (t, u x t, deriv (fun y => u y t) x) •
          chartChristoffelContraction (G t) α (deriv (fun y => u y t) x)
            (deriv (fun y => u y t) x) (u x t)) :
    ∀ x t, t ∈ Icc s v → u x t ∈ range (fun y => (e y : F)) := by
  let K : Set (ℝ × F × F) :=
    (fun p : ℝ × ℝ => (p.2, u p.1 p.2, deriv (fun y => u y p.2) p.1)) ''
      (univ ×ˢ Icc s v)
  have hK : IsCompact K := isCompact_image_firstJet_of_periodic hper hcont hDu
  have hKU : K ⊆ U := by
    rintro q ⟨⟨x, t⟩, hxt, rfl⟩
    exact hjetU x t hxt.2
  have hPU : ∀ q ∈ K,
      (q.1, (e (r q.2.1) : F), fderiv ℝ (fun y => (e (r y) : F)) q.2.1 q.2.2) ∈ U := by
    rintro q ⟨⟨x, t⟩, hxt, rfl⟩
    exact hprojectedJetU x t hxt.2
  apply periodic_mem_range_of_christoffel_parabolic_equation_on_open_set g G α hG he hgeo hleft
    hU hJD hV hVO hK hKU hUJV hr ha hPU hsv hδ hper hcont hinit hx ht
  · intro x t ht'
    exact ⟨(x,t), ⟨mem_univ x, ht'⟩, rfl⟩
  · rintro q ⟨⟨x, t⟩, hxt, rfl⟩
    exact hell x t hxt.2
  · exact heq

theorem periodic_mem_range_of_christoffel_parabolic_equation_of_continuous_deriv
    (g : ℝ → SmoothRiemannianMetric I M) {O : TopologicalSpace.Opens F}
    (G : ℝ → SmoothRiemannianMetric 𝓘(ℝ, F) O) (α : O)
    {D : RealTimeInterval} (hG : MetricFamilySmoothOn D G)
    {e : M → O} (he : ContMDiff I 𝓘(ℝ, F) ∞ e)
    {J : Set ℝ} (hgeo : ∀ t ∈ J, hasVanishingSecondFundamentalFormAlongCurves (g t) (G t) e)
    {r : F → M} (hleft : ∀ x, r (e x) = x)
    {V : Set F}
    (hJ : IsOpen J) (hJD : J ⊆ D.regular) (hV : IsOpen V) (hVO : V ⊆ O)
    (hr : ContMDiffOn 𝓘(ℝ, F) I 3 r V)
    {a : ℝ × F × F → ℝ} (ha : ContDiffOn ℝ 1 a (J ×ˢ V ×ˢ univ))
    (heV : range (fun x => (e x : F)) ⊆ V)
    {u : ℝ → ℝ → F} {s v δ : ℝ} (hsv : s < v) (hδ : 0 < δ)
    (hper : ∀ x t, u (x + 1) t = u x t)
    (hcont : ContinuousOn (Function.uncurry u) (Icc 0 1 ×ˢ Icc s v))
    (hinit : ∀ x, u x s ∈ range (fun y => (e y : F)))
    (hx : ∀ x t, t ∈ Ioo s v → ContDiffAt ℝ 2 (fun y => u y t) x)
    (ht : ∀ x t, t ∈ Ioo s v → DifferentiableAt ℝ (fun τ => u x τ) t)
    (hDu : ContinuousOn (fun p : ℝ × ℝ => deriv (fun y => u y p.2) p.1)
      (Icc 0 1 ×ˢ Icc s v))
    (hwindow : Icc s v ⊆ J) (himage : ∀ x t, t ∈ Icc s v → u x t ∈ V)
    (hell : ∀ x t, t ∈ Icc s v → δ ≤ a (t, u x t, deriv (fun y => u y t) x))
    (heq : ∀ x t, t ∈ Ioo s v →
      deriv (fun τ => u x τ) t -
          a (t, u x t, deriv (fun y => u y t) x) • deriv (deriv (fun y => u y t)) x =
        a (t, u x t, deriv (fun y => u y t) x) •
          chartChristoffelContraction (G t) α (deriv (fun y => u y t) x)
            (deriv (fun y => u y t) x) (u x t)) :
    ∀ x t, t ∈ Icc s v → u x t ∈ range (fun y => (e y : F)) := by
  let K : Set (ℝ × F × F) :=
    (fun p : ℝ × ℝ => (p.2, u p.1 p.2, deriv (fun y => u y p.2) p.1)) ''
      (univ ×ˢ Icc s v)
  have hK : IsCompact K := isCompact_image_firstJet_of_periodic hper hcont hDu
  have hKU : K ⊆ J ×ˢ V ×ˢ univ := by
    rintro q ⟨⟨x, t⟩, hxt, rfl⟩
    exact ⟨hwindow hxt.2, himage x t hxt.2, mem_univ _⟩
  apply periodic_mem_range_of_christoffel_parabolic_equation g G α hG he hgeo hleft
    hJ hJD hV hVO hK hKU hr ha heV hsv hδ hper hcont hinit hx ht
  · intro x t ht'
    exact ⟨(x,t), ⟨mem_univ x, ht'⟩, rfl⟩
  · rintro q ⟨⟨x, t⟩, hxt, rfl⟩
    exact hell x t hxt.2
  · exact heq

end DifferentialGeometry.Analysis.Parabolic
