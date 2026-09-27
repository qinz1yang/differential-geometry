import DifferentialGeometry.Analysis.Elliptic.ComplexPlane.ConformalBoundaryRegularity
import DifferentialGeometry.Geometry.Coordinates.ConformalEnergy
import DifferentialGeometry.Geometry.Coordinates.EmbeddedCurve
import DifferentialGeometry.Geometry.HarmonicMap.Coordinates
import DifferentialGeometry.Geometry.Metric.Pullback.Coefficients

noncomputable section
open Set Filter Metric Manifold
open scoped Topology ContDiff Manifold
namespace DifferentialGeometry.Geometry

private theorem exists_halfDisk_mapsTo_of_continuousWithinAt
    {V : Type*} [TopologicalSpace V] {X : ℂ → V} {R : ℝ} (hR : 0 < R)
    (hX : ContinuousWithinAt X {z : ℂ | ‖z‖ ≤ R ∧ 0 ≤ z.im} 0)
    {Ω : Set V} (hΩ : IsOpen Ω) (h0 : X 0 ∈ Ω) :
    ∃ r : ℝ, 0 < r ∧ r < R ∧ MapsTo X {z : ℂ | ‖z‖ ≤ r ∧ 0 ≤ z.im} Ω := by
  obtain ⟨δ, hδ, hsub⟩ := Metric.mem_nhdsWithin_iff.mp (hX (hΩ.mem_nhds h0))
  let r := min R δ / 2
  have hr : 0 < r := half_pos (lt_min hR hδ)
  have hrR : r < R := by dsimp [r]; linarith [min_le_left R δ]
  have hrδ : r < δ := by dsimp [r]; linarith [min_le_right R δ]
  refine ⟨r, hr, hrR, fun z hz => hsub ⟨?_, ⟨hz.1.trans hrR.le, hz.2⟩⟩⟩
  simpa using hz.1.trans_lt hrδ

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [I.Boundaryless]

theorem exists_contMDiffOn_halfDisk_of_orthogonal_coordinates
    (g : SmoothRiemannianMetric I M) (Φ : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞)
    (t : E) (l : E →L[ℝ] ℝ) (ht : t ≠ 0)
    {U : ℂ → M} {R : ℝ} (hR : 0 < R)
    (hU : ContinuousOn U {z : ℂ | ‖z‖ ≤ R ∧ 0 ≤ z.im})
    (hUi : ContMDiffOn 𝓘(ℝ, ℂ) I ∞ U {z : ℂ | ‖z‖ < R ∧ 0 < z.im})
    (hmap : MapsTo U {z : ℂ | ‖z‖ ≤ R ∧ 0 ≤ z.im} Φ.target)
    (htrace : ∀ x : ℝ, |x| ≤ R → Φ.symm (U x) - l (Φ.symm (U x)) • t = 0)
    (haxis : ∀ x : ℝ, |x| ≤ R → ∀ v : E,
      pullbackMetricCoefficients g Φ (Φ.symm (U x)) t v =
        pullbackMetricCoefficients g Φ (Φ.symm (U x)) t t * l v)
    (ho : ∀ z ∈ {z : ℂ | ‖z‖ < R ∧ 0 < z.im},
      g.inner (U z) (mfderiv 𝓘(ℝ, ℂ) I U z (1 : ℂ)) (mfderiv 𝓘(ℝ, ℂ) I U z Complex.I) = 0)
    (he : ∀ z ∈ {z : ℂ | ‖z‖ < R ∧ 0 < z.im},
      g.inner (U z) (mfderiv 𝓘(ℝ, ℂ) I U z (1 : ℂ)) (mfderiv 𝓘(ℝ, ℂ) I U z (1 : ℂ)) =
        g.inner (U z) (mfderiv 𝓘(ℝ, ℂ) I U z Complex.I) (mfderiv 𝓘(ℝ, ℂ) I U z Complex.I))
    (hH : ∀ z ∈ {z : ℂ | ‖z‖ < R ∧ 0 < z.im}, planarTension g U z = 0) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < R ∧
      ContMDiffOn 𝓘(ℝ, ℂ) I ∞ U {z : ℂ | ‖z‖ ≤ ρ ∧ 0 ≤ z.im} := by
  let K : Set ℂ := {z | ‖z‖ ≤ R ∧ 0 ≤ z.im}
  let S : Set ℂ := {z | ‖z‖ < R ∧ 0 < z.im}
  let X := Φ.symm ∘ U
  let x₀ := X 0
  let a := U 0
  let e := Φ.trans (extChartAtPartialDiffeomorph I ∞ a)
  let Ω := e.source
  have h0K : (0 : ℂ) ∈ K := by simp [K, hR.le]
  have hXmap : MapsTo X K Φ.source := fun z hz =>
    Φ.toOpenPartialHomeomorph.map_target (hmap hz)
  have hX : ContinuousOn X K := Φ.contMDiffOn_invFun.continuousOn.comp hU hmap
  have hSO : IsOpen S := (isOpen_lt continuous_norm continuous_const).inter
    (isOpen_lt continuous_const Complex.continuous_im)
  have hSiK : S ⊆ K := fun z hz => ⟨hz.1.le, hz.2.le⟩
  have hXi : ContDiffOn ℝ ∞ X S :=
    (Φ.contMDiffOn_invFun.comp hUi (fun z hz => hmap (hSiK hz))).contDiffOn
  have hright (z : ℂ) (hz : z ∈ K) : Φ (X z) = U z :=
    Φ.toOpenPartialHomeomorph.right_inv (hmap hz)
  have hΩ : IsOpen Ω := e.open_source
  have hx₀ : x₀ ∈ Ω := by
    change x₀ ∈ Φ.source ∧ Φ x₀ ∈ (extChartAtPartialDiffeomorph I ∞ a).source
    refine ⟨hXmap h0K, ?_⟩
    rw [hright 0 h0K]
    exact mem_extChartAt_source a
  obtain ⟨δ, C, hδ, hC, hδs, henergy⟩ := exists_transverse_coordinate_energy_bound g Φ (hXmap h0K)
  obtain ⟨η, hη, hηs⟩ := Metric.mem_nhds_iff.mp (hΩ.mem_nhds hx₀)
  let ε := min δ (η / 2)
  have hε : 0 < ε := lt_min hδ (half_pos hη)
  have hεδ : ε ≤ δ := min_le_left _ _
  have hεη : ε < η := by dsimp [ε]; linarith [min_le_right δ (η / 2)]
  let L := Metric.closedBall x₀ ε
  have hLΩ : L ⊆ Ω := (Metric.closedBall_subset_ball hεη).trans hηs
  have hLδ : L ⊆ Metric.closedBall x₀ δ := Metric.closedBall_subset_closedBall hεδ
  obtain ⟨Q, hQ, _, hQbound, hPDE⟩ := exists_quadratic_laplacian_coordinates g Φ a
  obtain ⟨A, hA, hQA⟩ := hQbound L (isCompact_closedBall _ _) hLΩ
  obtain ⟨r, hr, hrR, hXr⟩ := exists_halfDisk_mapsTo_of_continuousWithinAt hR (hX 0 h0K)
    Metric.isOpen_ball (Metric.mem_ball_self hε)
  let Kr : Set ℂ := {z | ‖z‖ ≤ r ∧ 0 ≤ z.im}
  let Sr : Set ℂ := {z | ‖z‖ < r ∧ 0 < z.im}
  have hKrK : Kr ⊆ K := fun z hz => ⟨hz.1.trans hrR.le, hz.2⟩
  have hSrKr : Sr ⊆ Kr := fun z hz => ⟨hz.1.le, hz.2.le⟩
  have hSrS : Sr ⊆ S := fun z hz => ⟨hz.1.trans hrR, hz.2⟩
  have hSrO : IsOpen Sr := (isOpen_lt continuous_norm continuous_const).inter
    (isOpen_lt continuous_const Complex.continuous_im)
  have hXL : MapsTo X Kr L := fun z hz => Metric.ball_subset_closedBall (hXr hz)
  have hXΩ : MapsTo X Kr Ω := fun z hz => hLΩ (hXL hz)
  have hU2 : ContMDiffOn 𝓘(ℝ, ℂ) I 2 U Sr :=
    (hUi.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).mono hSrS
  have hUd (z : ℂ) (hz : z ∈ Sr) : MDifferentiableAt 𝓘(ℝ, ℂ) I U z :=
    (hU2.contMDiffAt (hSrO.mem_nhds hz)).mdifferentiableAt (by norm_num)
  have hUchart : MapsTo U Sr (Φ.target ∩ (extChartAt I a).source) := by
    intro z hz
    have hx := hXΩ (hSrKr hz)
    change X z ∈ Φ.source ∧ Φ (X z) ∈ (extChartAtPartialDiffeomorph I ∞ a).source at hx
    refine ⟨hmap (hSiK (hSrS hz)), ?_⟩
    rw [hright z (hKrK (hSrKr hz))] at hx
    exact hx.2
  have hΔX (z : ℂ) (hz : z ∈ Sr) : Laplacian.laplacian X z = Q (X z, fderiv ℝ X z) :=
    hPDE U Sr hSrO hU2 hUchart z hz (hH z (hSrS hz))
  let P : E →L[ℝ] E := ContinuousLinearMap.id ℝ E - l.smulRight t
  have hΔY : ∀ z : ℂ, ‖z‖ < r → 0 < z.im →
      ‖Laplacian.laplacian (fun w => X w - l (X w) • t) z‖ ≤
        (4 * ‖P‖ * A * C) * ‖fderiv ℝ (fun w => X w - l (X w) • t) z‖ ^ 2 := by
    intro z hz hi
    have hs : z ∈ Sr := ⟨hz, hi⟩
    have hXd := (contDiffOn_infty.mp hXi 2).contDiffAt (hSO.mem_nhds (hSrS hs))
    apply hXd.norm_laplacian_clm_comp_le_of_energy_bound P hA hC
    · rw [hΔX z hs]
      exact hQA _ (hXL (hSrKr hs)) _
    · exact henergy t l U z (hUd z hs) (hmap (hKrK (hSrKr hs)))
        (hLδ (hXL (hSrKr hs))) (ho z (hSrS hs)) (he z (hSrS hs))
  have hBt : ∀ z ∈ Kr, 0 < pullbackMetricCoefficients g Φ (X z) t t := by
    intro z hz
    exact pullbackMetricCoefficients_pos g
      ((Φ.isLocalDiffeomorphAt 𝓘(ℝ, E) I ∞ (hXmap (hKrK hz))).mfderivToContinuousLinearEquiv
        (by simp)).injective ht
  obtain ⟨ρ, hρ, hρr, hreg⟩ := Analysis.exists_contDiffOn_halfDisk_of_conformal_transverse
    l t hr (by positivity) (hX.mono hKrK) (hXi.mono hSrS)
    (by intro z hz hi
        have heq : z = (z.re : ℂ) := by apply Complex.ext <;> simp [hi]
        have hab : |z.re| ≤ r := (Complex.abs_re_le_norm z).trans hz
        rw [heq]
        exact htrace z.re (hab.trans hrR.le))
    hΔY hΩ
    (((contDiffOn_pullback_metric_coefficients g Φ.open_source Φ.contMDiffOn_toFun).of_le
      (by norm_num)).mono (fun z hz => hz.1)) hXΩ
    (fun x _ => pullbackMetricCoefficients_isPosSemidef g Φ x) hBt
    (fun x hx => haxis x (hx.trans hrR.le))
    (by intro z hz
        rw [pullbackMetricCoefficients_fderiv_symm g Φ (hUd z hz) (hmap (hKrK (hSrKr hz)))]
        exact ho z (hSrS hz))
    (by intro z hz
        rw [pullbackMetricCoefficients_fderiv_symm g Φ (hUd z hz) (hmap (hKrK (hSrKr hz))),
          pullbackMetricCoefficients_fderiv_symm g Φ (hUd z hz) (hmap (hKrK (hSrKr hz)))]
        exact he z (hSrS hz)) hQ (fun z hz => hΔX z hz)
  refine ⟨ρ, hρ, hρr.trans hrR, ?_⟩
  have hρK : {z : ℂ | ‖z‖ ≤ ρ ∧ 0 ≤ z.im} ⊆ K :=
    fun z hz => ⟨hz.1.trans ((hρr.trans hrR).le), hz.2⟩
  exact (Φ.contMDiffOn_toFun.comp hreg.contMDiffOn (fun z hz => hXmap (hρK hz))).congr
    (fun z hz => (hright z (hρK hz)).symm)

theorem exists_contMDiffOn_halfDisk_of_embedded_curve
    (g : SmoothRiemannianMetric I M) {C : Type*} [TopologicalSpace C]
    {γ : C → M} (hγ : Topology.IsEmbedding γ)
    (p : OpenPartialHomeomorph ℝ C) (hp0 : (0 : ℝ) ∈ p.source)
    (hc : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ (γ ∘ p) p.source)
    (hv : mfderiv 𝓘(ℝ, ℝ) I (γ ∘ p) 0 1 ≠ 0)
    {U : ℂ → M} {R : ℝ} (hR : 0 < R) (h0 : U 0 = γ (p 0))
    (hU : ContinuousOn U {z : ℂ | ‖z‖ ≤ R ∧ 0 ≤ z.im})
    (hUi : ContMDiffOn 𝓘(ℝ, ℂ) I ∞ U {z : ℂ | ‖z‖ < R ∧ 0 < z.im})
    (htrace : ∀ x : ℝ, |x| ≤ R → U x ∈ range γ)
    (ho : ∀ z ∈ {z : ℂ | ‖z‖ < R ∧ 0 < z.im},
      g.inner (U z) (mfderiv 𝓘(ℝ, ℂ) I U z (1 : ℂ)) (mfderiv 𝓘(ℝ, ℂ) I U z Complex.I) = 0)
    (he : ∀ z ∈ {z : ℂ | ‖z‖ < R ∧ 0 < z.im},
      g.inner (U z) (mfderiv 𝓘(ℝ, ℂ) I U z (1 : ℂ)) (mfderiv 𝓘(ℝ, ℂ) I U z (1 : ℂ)) =
        g.inner (U z) (mfderiv 𝓘(ℝ, ℂ) I U z Complex.I) (mfderiv 𝓘(ℝ, ℂ) I U z Complex.I))
    (hH : ∀ z ∈ {z : ℂ | ‖z‖ < R ∧ 0 < z.im}, planarTension g U z = 0) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < R ∧
      ContMDiffOn 𝓘(ℝ, ℂ) I ∞ U {z : ℂ | ‖z‖ ≤ ρ ∧ 0 ≤ z.im} := by
  obtain ⟨t, l, Φ, hlt, hΦ0, hΦc, _, haxis, hcurve⟩ :=
    exists_orthogonal_chart_of_embedded_curve g hγ p hp0 hc hv
  have h0t : U 0 ∈ Φ.target := by
    rw [h0, ← hΦc]
    exact Φ.toOpenPartialHomeomorph.map_source hΦ0
  have h0K : (0 : ℂ) ∈ {z : ℂ | ‖z‖ ≤ R ∧ 0 ≤ z.im} := by simp [hR.le]
  obtain ⟨r, hr, hrR, hmap⟩ := exists_halfDisk_mapsTo_of_continuousWithinAt hR (hU 0 h0K)
    Φ.open_target h0t
  let Kr : Set ℂ := {z | ‖z‖ ≤ r ∧ 0 ≤ z.im}
  let Sr : Set ℂ := {z | ‖z‖ < r ∧ 0 < z.im}
  have hKrK : Kr ⊆ {z : ℂ | ‖z‖ ≤ R ∧ 0 ≤ z.im} := fun z hz => ⟨hz.1.trans hrR.le, hz.2⟩
  have hSrS : Sr ⊆ {z : ℂ | ‖z‖ < R ∧ 0 < z.im} := fun z hz => ⟨hz.1.trans hrR, hz.2⟩
  have hreal (x : ℝ) (hx : |x| ≤ r) : (x : ℂ) ∈ Kr := by simpa [Kr] using hx
  have htrans (x : ℝ) (hx : |x| ≤ r) : Φ.symm (U x) - l (Φ.symm (U x)) • t = 0 :=
    (hcurve _ (hmap (hreal x hx))).mp (htrace x (hx.trans hrR.le))
  have horth (x : ℝ) (hx : |x| ≤ r) (v : E) :
      pullbackMetricCoefficients g Φ (Φ.symm (U x)) t v =
        pullbackMetricCoefficients g Φ (Φ.symm (U x)) t t * l v := by
    have hs : Φ.symm (U x) ∈ Φ.source := Φ.toOpenPartialHomeomorph.map_target (hmap (hreal x hx))
    have hrep : Φ.symm (U x) = l (Φ.symm (U x)) • t := sub_eq_zero.mp (htrans x hx)
    have ha := (haxis (l (Φ.symm (U x))) (by rwa [← hrep])).2.2 v
    rw [← hrep] at ha
    exact ha
  have ht : t ≠ 0 := by intro ht; rw [ht, map_zero] at hlt; exact zero_ne_one hlt
  obtain ⟨ρ, hρ, hρr, hreg⟩ := exists_contMDiffOn_halfDisk_of_orthogonal_coordinates g Φ t l ht hr
    (hU.mono hKrK) (hUi.mono hSrS) hmap htrans horth
    (fun z hz => ho z (hSrS hz)) (fun z hz => he z (hSrS hz)) (fun z hz => hH z (hSrS hz))
  exact ⟨ρ, hρ, hρr.trans hrR, hreg⟩


end DifferentialGeometry.Geometry
