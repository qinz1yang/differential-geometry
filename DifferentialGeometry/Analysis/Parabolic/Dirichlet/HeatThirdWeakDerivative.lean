import DifferentialGeometry.Analysis.Parabolic.Dirichlet.HeatGradientScalarSource
import DifferentialGeometry.Analysis.Parabolic.Dirichlet.LocalSecondDerivative
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.TimeMeasureRestrict
import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative.Basic

noncomputable section

open Filter Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet

open DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]

local notation "I_hs" => modelWithCornersEuclideanHalfSpace n
local notation "EuN" => EuclideanSpace ℝ (Fin n)
local notation "EuStd" => EuclideanSpace ℝ (Fin (Module.finrank ℝ EuN))

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem exists_local_third_weak_derivative_of_heat_timeH1
    {D : RealTimeInterval} {g : ℝ → SmoothRiemannianMetric I_hs M}
    (hG : MetricFamilySmoothOn (I := I_hs) (M := M) D g)
    {T : ℝ} (hT : 0 ≤ T) (hreg : Icc (0 : ℝ) T ⊆ D.regular)
    (q : SmoothRiemannianMetric I_hs M)
    {Cg : ℝ} (hCg : 1 ≤ Cg)
    (hequiv : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, ∀ w : TangentSpace I_hs x,
      Cg⁻¹ * q.inner x w w ≤ (g t).inner x w w ∧
        (g t).inner x w w ≤ Cg * q.inner x w w)
    (Cv : ℝ≥0∞) (hCv0 : Cv ≠ 0) (hCvtop : Cv ≠ ⊤)
    (hvol : ∀ t ∈ Icc (0 : ℝ) T,
      riemannianVolumeMeasure (I := I_hs) (M := M) (g t) ≤
        Cv • riemannianVolumeMeasure (I := I_hs) (M := M) q)
    (α : M) {Ω Ω₀ : Set EuStd} (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (hΩ₀ : IsOpen Ω₀) (hΩ₀Ω : closure Ω₀ ⊆ Ω)
    {a b : ℝ} (ha : 0 < a) (hb : b < T) (hab : a ≤ b)
    (u : timeL2 (H1ComplDirichlet q) T)
    (f : timeL2 (Lp ℝ 2 (riemannianVolumeMeasure (I := I_hs) (M := M) q)) T)
    (w : timeH1 (H1ComplDirichlet q →L[ℝ] ℝ) T)
    (hwmass : ∀ᵐ t ∂timeMeasure T, ∀ z,
      w.toFun t z = inner ℝ (H1ComplDirichletToLp q (u t)) (H1ComplDirichletToLp q z))
    (hwderiv : ∀ᵐ t ∂timeMeasure T, ∀ ht : t ∈ Icc (0 : ℝ) T, ∀ z,
      w.deriv t z = dirichletWeakFormCompl (g t) 0 0 0 (by intro x; simp)
        hCg (hequiv t ht) Cv hCv0 hCvtop (hvol t ht) (u t)
        (smoothMulH1ComplDirichlet q (riemannianVolumeDensitySmoothMap (g t) q) z) +
          inner ℝ (f t) (H1ComplDirichletToLp q z)) :
    let F := Lp.uncurry ℝ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
      (((chartRestrictionLp q α hΩ.measurableSet hΩc
        (hΩs.trans (image_mono interior_subset)) 2).compLpL 2 (timeMeasure T)) f)
    ∀ Df : Fin (Module.finrank ℝ EuN) → Lp ℝ 2 ((timeMeasure T).prod (volume.restrict Ω)),
      (∀ k, ∀ᵐ t ∂timeMeasure T, DeGiorgi.HasWeakPartialDeriv k (fun z => Df k (t, z))
        (fun z => F (t, z)) Ω) →
    let μ₀ := (timeMeasure T).restrict (Icc a b)
    ∀ H₀ : Fin (Module.finrank ℝ EuN) → Fin (Module.finrank ℝ EuN) →
        Lp ℝ 2 (μ₀.prod (volume.restrict Ω₀)),
      (∀ i j, ∀ᵐ t ∂μ₀, DeGiorgi.HasWeakPartialDeriv j
        (fun z => H₀ i j (t, z))
        (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (u t)) Ω₀) →
      ∃ K : Fin (Module.finrank ℝ EuN) → Fin (Module.finrank ℝ EuN) →
          Fin (Module.finrank ℝ EuN) → Lp ℝ 2 (μ₀.prod (volume.restrict Ω₀)),
        ∀ i j k, ∀ᵐ t ∂μ₀, DeGiorgi.HasWeakPartialDeriv k
          (fun z => K i j k (t, z)) (fun z => H₀ i j (t, z)) Ω₀ := by
  intro F Df hDf μ₀ H₀ hH₀
  classical
  let G : MetricConnectionFamilyOn (I := I_hs) (M := M) D :=
    { metric := g
      connection := fun t => leviCivitaConnectionOfMetric (g t)
      metricCompatible := fun t => leviCivitaConnectionOfMetric_isMetricCompatible (g t) }
  have hΩ₀c : IsCompact (closure Ω₀) :=
    hΩc.of_isClosed_subset isClosed_closure (hΩ₀Ω.trans subset_closure)
  obtain ⟨Ω₁, hΩ₁, hΩ₀₁, hΩ₁Ω, hΩ₁c⟩ :=
    exists_open_between_and_isCompact_closure hΩ₀c hΩ hΩ₀Ω
  have hΩ₁s := hΩ₁Ω.trans (subset_closure.trans hΩs)
  obtain ⟨δ, η, _, _, hη, _, _, hηone, hηs⟩ :=
    exists_smooth_cutoff_with_neighborhood hΩ₀c hΩ₁ hΩ₀₁
  have hηone' : ∀ z ∈ Ω₀, η z = 1 := fun z hz =>
    hηone z (Metric.self_subset_cthickening (closure Ω₀) (subset_closure hz))
  let s₀ := a / 2
  let s₁ := (b + T) / 2
  have hs₀ : 0 < s₀ := by dsimp [s₀]; linarith
  have hs₁ : s₁ < T := by dsimp [s₁]; linarith
  have hs₀a : s₀ < a := by dsimp [s₀]; linarith
  have hbs₁ : b < s₁ := by dsimp [s₁]; linarith
  have hs₀₁ : s₀ < s₁ := lt_of_lt_of_le hs₀a (hab.trans hbs₁.le)
  have hI : Icc s₀ s₁ ⊆ Icc (0 : ℝ) T := Icc_subset_Icc hs₀.le hs₁.le
  have htarget : Icc a b ⊆ Icc s₀ s₁ := Icc_subset_Icc hs₀a.le hbs₁.le
  let μ := (timeMeasure T).restrict (Icc s₀ s₁)
  let ν := μ.prod (volume.restrict Ω₁)
  have hμ : μ = volume.restrict (Icc s₀ s₁) :=
    timeMeasure_restrict_Icc_eq_volume_restrict_Icc hI
  have hsub : Ω₁ ⊆ Ω := subset_closure.trans hΩ₁Ω
  have hν : ν ≤ (timeMeasure T).prod (volume.restrict Ω) :=
    Measure.prod_mono Measure.restrict_le_self (Measure.restrict_mono hsub le_rfl)
  have hD (k) : MemLp (Df k) 2 ν := (Lp.memLp (Df k)).mono_measure hν
  let Df₁ := fun k => (hD k).toLp (Df k)
  have hDf₁ (k) : ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv k
      (fun z => Df₁ k (t, z)) (fun z => F (t, z)) Ω₁ := by
    have hcoe : Df₁ k =ᵐ[ν] Df k := (hD k).coeFn_toLp
    filter_upwards [ae_restrict_of_ae (s := Icc s₀ s₁) (hDf k),
      Measure.ae_ae_of_ae_prod hcoe] with t ht he
    exact (DeGiorgi.HasWeakPartialDeriv.restrict hΩ₁ hsub ht).congr_ae
      Filter.EventuallyEq.rfl (Filter.EventuallyEq.symm he)
  obtain ⟨H, hH, _, B, _, _, hpacket⟩ :=
    exists_timeH1_cutoff_gradient_scalar_source_of_heat_timeH1 hG hT hreg q hCg hequiv Cv
      hCv0 hCvtop hvol α hΩ hΩc hΩs hΩ₁ hΩ₁Ω hs₀ hs₁ hs₀₁ u f w hwmass hwderiv
      hη hηs Df₁ hDf₁
  choose v w' ℓ β f' hrep hmass hderiv hweak hβ hpair hf hsource using hpacket
  have hμ₀ : μ₀ = volume.restrict (Icc a b) :=
    timeMeasure_restrict_Icc_eq_volume_restrict_Icc
      (Icc_subset_Icc ha.le hb.le)
  have hμrestrict : (volume.restrict (Icc s₀ s₁)).restrict (Icc a b) = μ₀ := by
    rw [Measure.restrict_restrict_of_subset htarget, hμ₀]
  have hμrestrict' : μ.restrict (Icc a b) = μ₀ := by
    rw [hμ, hμrestrict]
  have hKexist (i) : ∃ K : Fin (Module.finrank ℝ EuN) →
        Fin (Module.finrank ℝ EuN) → Lp ℝ 2 (μ₀.prod (volume.restrict Ω₀)),
      ∀ j k, ∀ᵐ t ∂μ₀, DeGiorgi.HasWeakPartialDeriv k
        (fun z => K j k (t, z))
        (dirichletLocalWeakPartialLp q α hΩ₁ hΩ₁c hΩ₁s j (v i t)) Ω₀ := by
    have hex := exists_local_dirichlet_second_weak_derivative_of_timeH1_of_measure_eq_volume
      (G := G) hG hs₀₁.le (hI.trans hreg) q α hΩ₁ hΩ₁c hΩ₁s hs₀a hbs₁ hμ
      (v i) (f' i) (ℓ i) (β i) (w' i) (hmass i) (hderiv i) (hpair i)
      (hsource i) hΩ₀ hΩ₀₁
    rw [hμrestrict] at hex
    obtain ⟨K, hK, _⟩ := hex
    exact ⟨K, hK⟩
  choose K hK using hKexist
  have hsub₀₁ : Ω₀ ⊆ Ω₁ := subset_closure.trans hΩ₀₁
  have hsub₁ : Ω₁ ⊆ Ω := subset_closure.trans hΩ₁Ω
  have hμle : μ₀ ≤ μ := by
    rw [← hμrestrict']
    exact Measure.restrict_le_self
  have halign (i j) : ∀ᵐ t ∂μ₀,
      (dirichletLocalWeakPartialLp q α hΩ₁ hΩ₁c hΩ₁s j (v i t) : EuStd → ℝ)
        =ᵐ[volume.restrict Ω₀] fun z => H₀ i j (t, z) := by
    apply ae_dirichletLocalWeakPartialLp_eq_of_chartPullback_mul_eq_one q α
      hΩ₁ hΩ₁c hΩ₁s hΩ₀ hsub₀₁ (fun t => v i t)
      (fun t => dirichletLocalWeakPartialLp q α hΩ₁ hΩ₁c hΩ₁s i (u t)) j (fun t z => H₀ i j (t, z))
      hηone' ((hrep i).filter_mono (ae_mono hμle))
      (((Lp.memLp (H₀ i j)).prodMk_left (by norm_num)).mono
        (fun _ ht => ht.locallyIntegrable (by norm_num)))
    filter_upwards [hH₀ i j] with t ht
    exact hasWeakPartialDeriv_congr_ae hΩ₀ j
      ((dirichletLocalWeakPartialLp_restrict_ae q α hΩ hΩc hΩs
        hΩ₁ hΩ₁c hΩ₁s hsub₁ i (u t)).filter_mono
          (ae_mono (Measure.restrict_mono hsub₀₁ le_rfl))) ht
  refine ⟨K, ?_⟩
  intro i j k
  filter_upwards [hK i j k, halign i j] with t ht he
  exact hasWeakPartialDeriv_congr_ae hΩ₀ k he ht

end DifferentialGeometry.Analysis.Parabolic.Dirichlet
