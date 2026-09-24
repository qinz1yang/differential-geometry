import DifferentialGeometry.Analysis.Parabolic.Dirichlet.HeatHessianEquation
import DifferentialGeometry.Analysis.Parabolic.MetricDivergenceRegularity
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.TimeMeasureRestrict
import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative.Basic

noncomputable section

open Filter Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet

open DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
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

theorem exists_local_fourth_weak_derivative_of_heat_timeH1
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
    ∀ DDf : Fin (Module.finrank ℝ EuN) → Fin (Module.finrank ℝ EuN) →
        Lp ℝ 2 ((timeMeasure T).prod (volume.restrict Ω)),
      (∀ i j, ∀ᵐ t ∂timeMeasure T, DeGiorgi.HasWeakPartialDeriv j
        (fun z => DDf i j (t, z)) (fun z => Df i (t, z)) Ω) →
    let μ₀ := (timeMeasure T).restrict (Icc a b)
    ∀ H₀ : Fin (Module.finrank ℝ EuN) → Fin (Module.finrank ℝ EuN) →
        Lp ℝ 2 (μ₀.prod (volume.restrict Ω₀)),
      (∀ i j, ∀ᵐ t ∂μ₀, DeGiorgi.HasWeakPartialDeriv j
        (fun z => H₀ i j (t, z))
        (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (u t)) Ω₀) →
      ∀ K₀ : Fin (Module.finrank ℝ EuN) → Fin (Module.finrank ℝ EuN) →
          Fin (Module.finrank ℝ EuN) → Lp ℝ 2 (μ₀.prod (volume.restrict Ω₀)),
        (∀ i j k, ∀ᵐ t ∂μ₀, DeGiorgi.HasWeakPartialDeriv k
          (fun z => K₀ i j k (t, z)) (fun z => H₀ i j (t, z)) Ω₀) →
        ∃ L : Fin (Module.finrank ℝ EuN) → Fin (Module.finrank ℝ EuN) →
            Fin (Module.finrank ℝ EuN) → Fin (Module.finrank ℝ EuN) →
            Lp ℝ 2 (μ₀.prod (volume.restrict Ω₀)),
          ∀ i j k l, ∀ᵐ t ∂μ₀, DeGiorgi.HasWeakPartialDeriv l
            (fun z => L i j k l (t, z)) (fun z => K₀ i j k (t, z)) Ω₀ := by
  intro F Df hDf DDf hDDf μ₀ H₀ hH₀ K₀ hK₀
  classical
  have hΩ₀c : IsCompact (closure Ω₀) :=
    hΩc.of_isClosed_subset isClosed_closure (hΩ₀Ω.trans subset_closure)
  obtain ⟨Ω₁, hΩ₁, hΩ₀₁, hΩ₁Ω, hΩ₁c⟩ :=
    exists_open_between_and_isCompact_closure hΩ₀c hΩ hΩ₀Ω
  have hΩ₁s := hΩ₁Ω.trans (subset_closure.trans hΩs)
  let s₀ := a / 2
  let s₁ := (b + T) / 2
  have hs₀ : 0 < s₀ := by dsimp [s₀]; linarith
  have hs₁ : s₁ < T := by dsimp [s₁]; linarith
  have hs₀a : s₀ < a := by dsimp [s₀]; linarith
  have hbs₁ : b < s₁ := by dsimp [s₁]; linarith
  have hs₀₁ : s₀ < s₁ := lt_of_lt_of_le hs₀a (hab.trans hbs₁.le)
  have hI : Icc s₀ s₁ ⊆ Icc (0 : ℝ) T :=
    Icc_subset_Icc hs₀.le hs₁.le
  have htarget : Icc a b ⊆ Icc s₀ s₁ :=
    Icc_subset_Icc hs₀a.le hbs₁.le
  let μ := (timeMeasure T).restrict (Icc s₀ s₁)
  have hμ : μ = volume.restrict (Icc s₀ s₁) :=
    timeMeasure_restrict_Icc_eq_volume_restrict_Icc hI
  let ν := μ.prod (volume.restrict Ω₁)
  have hsub : Ω₁ ⊆ Ω := subset_closure.trans hΩ₁Ω
  have hν : ν ≤ (timeMeasure T).prod (volume.restrict Ω) :=
    Measure.prod_mono Measure.restrict_le_self (Measure.restrict_mono hsub le_rfl)
  have hDD (i j) : MemLp (DDf i j) 2 ν := (Lp.memLp (DDf i j)).mono_measure hν
  let DDf₁ := fun i j => (hDD i j).toLp (DDf i j)
  have hDDf₁ (i j) : ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv j
      (fun z => DDf₁ i j (t, z)) (fun z => Df i (t, z)) Ω₁ := by
    have hcoe : DDf₁ i j =ᵐ[ν] DDf i j := (hDD i j).coeFn_toLp
    filter_upwards [ae_restrict_of_ae (s := Icc s₀ s₁) (hDDf i j),
      Measure.ae_ae_of_ae_prod hcoe] with t ht he
    exact (DeGiorgi.HasWeakPartialDeriv.restrict hΩ₁ hsub ht).congr_ae
      Filter.EventuallyEq.rfl (Filter.EventuallyEq.symm he)
  have hex := exists_lp_weak_hessian_equation_of_heat_timeH1
    hG hT hreg q hCg hequiv Cv hCv0 hCvtop hvol α hΩ hΩc hΩs
    hΩ₁ hΩ₁Ω hs₀ hs₁ hs₀₁.le u f w hwmass hwderiv Df hDf DDf₁ hDDf₁
  let H := hex.choose
  let K := hex.choose_spec.choose
  let S := hex.choose_spec.choose_spec.choose
  have hp := hex.choose_spec.choose_spec.choose_spec
  have hH := hp.1
  have hK := hp.2.2.1
  have hS := hp.2.2.2.2
  have hμ₀ : μ₀ = volume.restrict (Icc a b) :=
    timeMeasure_restrict_Icc_eq_volume_restrict_Icc
      (Icc_subset_Icc ha.le hb.le)
  have hμrestrict : (volume.restrict (Icc s₀ s₁)).restrict (Icc a b) = μ₀ := by
    rw [Measure.restrict_restrict_of_subset htarget, hμ₀]
  have hμrestrict' : μ.restrict (Icc a b) = μ₀ := by
    rw [hμ, hμrestrict]
  have hLexist (i j) : ∃ L : Fin (Module.finrank ℝ EuN) →
        Fin (Module.finrank ℝ EuN) → Lp ℝ 2 (μ₀.prod (volume.restrict Ω₀)),
      ∀ k l, ∀ᵐ t ∂μ₀, DeGiorgi.HasWeakPartialDeriv l
        (fun z => L k l (t, z)) (fun z => K i j k (t, z)) Ω₀ := by
    have hregular := exists_local_second_weak_derivative_of_metric_divergence_equation
      hG hs₀₁ (hI.trans hreg) α hΩ₁ hΩ₁c hΩ₁s hΩ₀ hΩ₀₁ hs₀a hbs₁
    dsimp only at hregular
    rw [← hμ] at hregular
    have hregularH := hregular (H i j) (S i j) (K i j) (hK i j) (hS i j)
    rw [hμrestrict'] at hregularH
    obtain ⟨L, hL, _, _⟩ := hregularH
    exact ⟨L, hL⟩
  choose L hL using hLexist
  have hsub₀₁ : Ω₀ ⊆ Ω₁ := subset_closure.trans hΩ₀₁
  have hμle : μ₀ ≤ μ := by
    rw [← hμrestrict']
    exact Measure.restrict_le_self
  have hHeq (i j) : ∀ᵐ t ∂μ₀,
      (fun z => H i j (t, z)) =ᵐ[volume.restrict Ω₀] fun z => H₀ i j (t, z) := by
    filter_upwards [(hH i j).filter_mono (ae_mono hμle), hH₀ i j,
      ((Lp.memLp (H i j)).prodMk_left (by norm_num)).filter_mono (ae_mono hμle),
      (Lp.memLp (H₀ i j)).prodMk_left (by norm_num)] with t ht ha hm hm₀
    exact DeGiorgi.HasWeakPartialDeriv.ae_eq hΩ₀
      (DeGiorgi.HasWeakPartialDeriv.restrict hΩ₀ hsub₀₁ ht) ha
      ((hm.mono_measure (Measure.restrict_mono hsub₀₁ le_rfl)).locallyIntegrable (by norm_num))
      (hm₀.locallyIntegrable (by norm_num))
  have halign (i j k) : ∀ᵐ t ∂μ₀,
      (fun z => K i j k (t, z)) =ᵐ[volume.restrict Ω₀] fun z => K₀ i j k (t, z) := by
    filter_upwards [(hK i j k).filter_mono (ae_mono hμle), hK₀ i j k, hHeq i j,
      ((Lp.memLp (K i j k)).prodMk_left (by norm_num)).filter_mono (ae_mono hμle),
      (Lp.memLp (K₀ i j k)).prodMk_left (by norm_num)] with t ht ha he hm hm₀
    have ht' := hasWeakPartialDeriv_congr_ae hΩ₀ k he
      (DeGiorgi.HasWeakPartialDeriv.restrict hΩ₀ hsub₀₁ ht)
    exact DeGiorgi.HasWeakPartialDeriv.ae_eq hΩ₀ ht' ha
      ((hm.mono_measure (Measure.restrict_mono hsub₀₁ le_rfl)).locallyIntegrable (by norm_num))
      (hm₀.locallyIntegrable (by norm_num))
  refine ⟨L, ?_⟩
  intro i j k l
  filter_upwards [hL i j k l, halign i j k] with t ht he
  exact hasWeakPartialDeriv_congr_ae hΩ₀ l he ht

end DifferentialGeometry.Analysis.Parabolic.Dirichlet
