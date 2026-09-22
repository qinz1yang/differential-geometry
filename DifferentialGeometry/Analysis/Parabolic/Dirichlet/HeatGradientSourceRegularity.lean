import DifferentialGeometry.Analysis.Parabolic.Dirichlet.HeatMixedTimeSpatialRegularity
import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakPartialSource
import DifferentialGeometry.Analysis.Integration.Lp.SpatialDerivative

noncomputable section

open Filter Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet

open DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
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

theorem exists_spatial_weak_derivative_gradient_source_of_heat_timeH1
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
    let μ := (timeMeasure T).restrict (Icc a b)
    let ν := μ.prod (volume.restrict Ω₀)
    let ρ := fun p : ℝ × EuStd => densityOnEuclid (I := I_hs) (g p.1) α p.2
    let A := fun i j (p : ℝ × EuStd) => weightedInvGramOnEuclid (I := I_hs) (g p.1) α i j p.2
    let U := dirichletLocalSpacetimeLp q α hΩ.measurableSet hΩc
      (hΩs.trans (image_mono interior_subset)) (timeMeasure T) u
    let V := fun i => dirichletLocalSpacetimeWeakPartialLp q α hΩ hΩc hΩs (timeMeasure T) i u
    let c := fun p : ℝ × EuStd => ρ p * ((1 / 2 : ℝ) * traceTimeDerivMetric (I := I_hs) g p.1
      ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm p.2)))
    ∀ DDf : Fin (Module.finrank ℝ EuN) → Fin (Module.finrank ℝ EuN) → Lp ℝ 2 ν,
      (∀ i j, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv j
        (fun z => DDf i j (t, z)) (fun z => Df i (t, z)) Ω₀) →
    ∀ R : Lp ℝ 2 ν,
      (∀ φ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Ioo a b ×ˢ Ω₀ →
        (∫ p, U p * fderiv ℝ φ p (1, 0) ∂ν) = -∫ p, R p * φ p ∂ν) →
    ∀ H : Fin (Module.finrank ℝ EuN) → Fin (Module.finrank ℝ EuN) → Lp ℝ 2 ν,
      (∀ i j, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv j (fun z => H i j (t, z))
        (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (u t)) Ω₀) →
    ∀ Q : Fin (Module.finrank ℝ EuN) → Lp ℝ 2 ν,
      (∀ k, Q k =ᵐ[ν] fun p =>
        (c p * V k p + fderiv ℝ c p (0, EuclideanSpace.single k 1) * U p +
          (ρ p * Df k p + fderiv ℝ ρ p (0, EuclideanSpace.single k 1) * F p)) +
        (∑ i, ∑ j, (fderiv ℝ (A i j) p (0, EuclideanSpace.single k 1) * H i j p +
          fderiv ℝ (fun z => fderiv ℝ (A i j) z (0, EuclideanSpace.single k 1)) p
            (0, EuclideanSpace.single j 1) * V i p)) -
        (fderiv ℝ ρ p (0, EuclideanSpace.single k 1) * R p +
          fderiv ℝ (fun z => fderiv ℝ ρ z (0, EuclideanSpace.single k 1)) p (1, 0) * U p)) →
      ∃ DQ : Fin (Module.finrank ℝ EuN) → Fin (Module.finrank ℝ EuN) → Lp ℝ 2 ν,
        (∀ k j, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv j
          (fun z => DQ k j (t, z)) (fun z => Q k (t, z)) Ω₀) ∧
        (∀ k, ∀ᵐ t ∂μ, MemWkp 1 2 (fun z => Q k (t, z)) Ω₀) ∧
        ∀ k, MemLp (fun t => (iteratedWeakSobolevNorm 1 2
          (fun z => Q k (t, z)) Ω₀).toReal) 2 μ := by
  intro F Df hDf μ ν ρ A U V c DDf hDDf R hR H hH Q hQ
  classical
  let G : MetricConnectionFamilyOn (I := I_hs) (M := M) D :=
    { metric := g
      connection := fun t => leviCivitaConnectionOfMetric (g t)
      metricCompatible := fun t => leviCivitaConnectionOfMetric_isMetricCompatible (g t) }
  obtain ⟨K, hK⟩ := exists_local_third_weak_derivative_of_heat_timeH1
    hG hT hreg q hCg hequiv Cv hCv0 hCvtop hvol α hΩ hΩc hΩs
    hΩ₀ hΩ₀Ω ha hb hab u f w hwmass hwderiv Df hDf H hH
  obtain ⟨DR, hDR, _, _⟩ := exists_spatial_weak_derivative_time_derivative_of_heat_timeH1
    hG hT hreg q hCg hequiv Cv hCv0 hCvtop hvol α hΩ hΩc hΩs
    hΩ₀ hΩ₀Ω ha hb hab u f w hwmass hwderiv Df hDf R hR
  have hsub : Ω₀ ⊆ Ω := subset_closure.trans hΩ₀Ω
  have hmeasure : ν ≤ (timeMeasure T).prod (volume.restrict Ω) :=
    Measure.prod_mono Measure.restrict_le_self (Measure.restrict_mono hsub le_rfl)
  have hU : MemLp U 2 ν := (Lp.memLp U).mono_measure hmeasure
  have hV (i) : MemLp (V i) 2 ν := (Lp.memLp (V i)).mono_measure hmeasure
  have hF : MemLp F 2 ν := (Lp.memLp F).mono_measure hmeasure
  have hD (i) : MemLp (Df i) 2 ν := (Lp.memLp (Df i)).mono_measure hmeasure
  let U₀ := hU.toLp U
  let V₀ := fun i => (hV i).toLp (V i)
  let F₀ := hF.toLp F
  let Df₀ := fun i => (hD i).toLp (Df i)
  have hU₀ : U₀ =ᵐ[ν] U := hU.coeFn_toLp
  have hV₀ (i) : V₀ i =ᵐ[ν] V i := (hV i).coeFn_toLp
  have hF₀ : F₀ =ᵐ[ν] F := hF.coeFn_toLp
  have hDf₀ (i) : Df₀ i =ᵐ[ν] Df i := (hD i).coeFn_toLp
  have hVweak (i k) : ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv k
      (fun z => H i k (t, z)) (fun z => V₀ i (t, z)) Ω₀ := by
    have hVi := ae_restrict_of_ae (s := Icc a b)
      (dirichletLocalSpacetimeWeakPartialLp_coeFn q α hΩ hΩc hΩs (timeMeasure T) i u)
    filter_upwards [hH i k, Measure.ae_ae_of_ae_prod (hV₀ i), hVi] with t ht he hv
    change (fun z => V₀ i (t, z)) =ᵐ[volume.restrict Ω₀] (fun z => V i (t, z)) at he
    exact hasWeakPartialDeriv_congr_ae hΩ₀ k
      (Filter.EventuallyEq.symm
        (he.trans (hv.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))))) ht
  have hFweak (k) : ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv k
      (fun z => Df₀ k (t, z)) (fun z => F₀ (t, z)) Ω₀ := by
    filter_upwards [ae_restrict_of_ae (s := Icc a b) (hDf k),
      Measure.ae_ae_of_ae_prod hF₀, Measure.ae_ae_of_ae_prod (hDf₀ k)] with t ht hf hd
    exact (DeGiorgi.HasWeakPartialDeriv.restrict hΩ₀ hsub ht).congr_ae
      (Filter.EventuallyEq.symm hf) (Filter.EventuallyEq.symm hd)
  have hUweak (k) : ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv k
      (fun z => V₀ k (t, z)) (fun z => U₀ (t, z)) Ω₀ := by
    filter_upwards [ae_restrict_of_ae (s := Icc a b)
      (hasWeakPartialDeriv_dirichletLocalSpacetimeWeakPartialLp q α hΩ hΩc hΩs (timeMeasure T) k u),
      Measure.ae_ae_of_ae_prod hU₀, Measure.ae_ae_of_ae_prod (hV₀ k)] with t ht hu hv
    exact (DeGiorgi.HasWeakPartialDeriv.restrict hΩ₀ hsub ht).congr_ae
      (Filter.EventuallyEq.symm hu) (Filter.EventuallyEq.symm hv)
  have hDweak (i j) : ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv j
      (fun z => DDf i j (t, z)) (fun z => Df₀ i (t, z)) Ω₀ := by
    filter_upwards [hDDf i j, Measure.ae_ae_of_ae_prod (hDf₀ i)] with t ht hd
    exact ht.congr_ae (Filter.EventuallyEq.symm hd) Filter.EventuallyEq.rfl
  let W := toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target
  have hW : IsOpen W := (toEuclidean (E := EuN)).isOpenMap _ isOpen_interior
  have hΩ₀c : IsCompact (closure Ω₀) :=
    hΩc.of_isClosed_subset isClosed_closure (hΩ₀Ω.trans subset_closure)
  have hΩ₀W : closure Ω₀ ⊆ W := hΩ₀Ω.trans (subset_closure.trans hΩs)
  have hρ : ContDiffOn ℝ ∞ ρ (D.regular ×ˢ W) :=
    (densityOnEuclid_family_contDiffOn (G := G) hG Subset.rfl α).mono
      (prod_mono Subset.rfl (image_mono interior_subset))
  have hA (i j) : ContDiffOn ℝ ∞ (A i j) (D.regular ×ˢ W) :=
    weightedInvGramOnEuclid_family_contDiffOn (G := G) hG Subset.rfl α Subset.rfl i j
  have hc : ContDiffOn ℝ ∞ c (D.regular ×ˢ W) :=
    hρ.mul (contDiffOn_const.mul
      (traceTimeDerivMetric_comp_chartInverse_contDiffOn (G := G) hG Subset.rfl α Subset.rfl))
  have hd {b : ℝ × EuStd → ℝ} (hb : ContDiffOn ℝ ∞ b (D.regular ×ˢ W))
      (v : ℝ × EuStd) : ContDiffOn ℝ ∞ (fun p => fderiv ℝ b p v) (D.regular ×ˢ W) :=
    (hb.fderiv_of_isOpen (m := ∞) (D.regular_isOpen.prod hW) (by simp)).clm_apply contDiffOn_const
  have hbound (c : ℝ × EuStd → ℝ) (hc : ContDiffOn ℝ ∞ c (D.regular ×ˢ W)) :
      MemLp c ∞ ν ∧ ∀ k, MemLp (fun p =>
        fderiv ℝ (fun z => c (p.1, z)) p.2 (EuclideanSpace.single k 1)) ∞ ν := by
    have hc' := DifferentialGeometry.Analysis.memLp_top_and_spatial_fderiv_of_contDiffOn
      D.regular_isOpen isCompact_Icc hreg hW hΩ₀.measurableSet hΩ₀c hΩ₀W
      (A := fun t z => c (t, z)) (hc.of_le (by simp)) (volume.prod volume)
    rw [← Measure.prod_restrict] at hc'
    refine ⟨hc'.1.mono_measure (Measure.prod_mono Measure.restrict_le_self le_rfl), ?_⟩
    intro k
    exact (hc'.2 (EuclideanSpace.single k 1)).mono_measure
      (Measure.prod_mono Measure.restrict_le_self le_rfl)
  have hsmooth (c : ℝ × EuStd → ℝ) (hc : ContDiffOn ℝ ∞ c (D.regular ×ˢ W)) :
      ∀ᵐ t ∂μ, ContDiffOn ℝ ∞ (fun z => c (t, z)) Ω₀ := by
    filter_upwards [ae_restrict_of_ae (s := Icc a b)
      (ae_restrict_mem (μ := volume) measurableSet_Icc)] with t ht
    exact hc.comp (contDiffOn_const.prodMk contDiffOn_id)
      (fun z hz => ⟨hreg ht, hΩ₀W (subset_closure hz)⟩)
  let ι := ((Fin (Module.finrank ℝ EuN) × Fin (Module.finrank ℝ EuN)) × Bool) ⊕
    ((Bool × Bool) ⊕ Bool)
  let Y : Fin (Module.finrank ℝ EuN) → ι → Lp ℝ 2 ν := fun k =>
    Sum.elim (fun s => if s.2 then V₀ s.1.1 else H s.1.1 s.1.2)
      (Sum.elim (fun s => if s.1 then (if s.2 then U₀ else R) else
        (if s.2 then U₀ else V₀ k)) (fun b => if b then F₀ else Df₀ k))
  let DY : Fin (Module.finrank ℝ EuN) → ι → Fin (Module.finrank ℝ EuN) → Lp ℝ 2 ν := fun k =>
    Sum.elim (fun s j => if s.2 then H s.1.1 j else K s.1.1 s.1.2 j)
      (Sum.elim (fun s j => if s.1 then (if s.2 then V₀ j else DR j) else
        (if s.2 then V₀ j else H k j)) (fun b j => if b then Df₀ j else DDf k j))
  let B : Fin (Module.finrank ℝ EuN) → ι → ℝ × EuStd → ℝ := fun k =>
    Sum.elim (fun s p => if s.2 then
      fderiv ℝ (fun z => fderiv ℝ (A s.1.1 s.1.2) z (0, EuclideanSpace.single k 1)) p
        (0, EuclideanSpace.single s.1.2 1)
      else fderiv ℝ (A s.1.1 s.1.2) p (0, EuclideanSpace.single k 1))
      (Sum.elim (fun s p => if s.1 then
        (if s.2 then -fderiv ℝ (fun z => fderiv ℝ ρ z (0, EuclideanSpace.single k 1)) p (1, 0)
          else -fderiv ℝ ρ p (0, EuclideanSpace.single k 1)) else
        (if s.2 then fderiv ℝ c p (0, EuclideanSpace.single k 1) else c p))
        (fun b p => if b then fderiv ℝ ρ p (0, EuclideanSpace.single k 1) else ρ p))
  have hB (k s) : ContDiffOn ℝ ∞ (B k s) (D.regular ×ˢ W) := by
    rcases s with ⟨⟨i, j⟩, b⟩ | (⟨b, c⟩ | b)
    · cases b
      · exact hd (hA i j) _
      · exact hd (hd (hA i j) _) _
    · cases b <;> cases c
      · exact hc
      · exact hd hc _
      · exact (hd hρ _).neg
      · exact (hd (hd hρ _) _).neg
    · cases b
      · exact hρ
      · exact hd hρ _
  have hY (k s j) : ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv j
      (fun z => DY k s j (t, z)) (fun z => Y k s (t, z)) Ω₀ := by
    rcases s with ⟨⟨i, l⟩, b⟩ | (⟨b, c⟩ | b)
    · cases b
      · exact hK i l j
      · exact hVweak i j
    · cases b <;> cases c
      · exact hVweak k j
      · exact hUweak j
      · exact hDR j
      · exact hUweak j
    · cases b
      · exact hDweak k j
      · exact hFweak j
  have hQsum (k) : Q k =ᵐ[ν] fun p => ∑ s, B k s p * Y k s p := by
    filter_upwards [hQ k, hU₀, hF₀, ae_all_iff.mpr hV₀, hDf₀ k] with p hp hu hf hv hdf
    change Q k p = ∑ s : ((Fin (Module.finrank ℝ EuN) × Fin (Module.finrank ℝ EuN)) × Bool) ⊕
      ((Bool × Bool) ⊕ Bool), B k s p * Y k s p
    simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_bool,
      B, Y, Sum.elim_inl, Sum.elim_inr, Bool.false_eq_true, ↓reduceIte]
    simp_rw [hu, hf, hv, hdf]
    rw [hp]
    simp only [Finset.sum_add_distrib]
    ring
  have hex (k) := exists_lp_spatial_weak_partials_of_ae_eq_finite_sum hΩ₀ (Q k) (Y k) (DY k) (B k)
    (fun s => (hbound _ (hB k s)).1) (fun s j => (hbound _ (hB k s)).2 j)
    (fun s => hsmooth _ (hB k s)) (hY k) (hQsum k)
  choose DQ hDQ hformula hnorm hW1 hWnorm using hex
  exact ⟨DQ, hDQ, hW1, hWnorm⟩

theorem exists_lp_weak_gradient_equation_with_source_spatial_derivative_of_heat_timeH1
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
    let μ := (timeMeasure T).restrict (Icc a b)
    let ν := μ.prod (volume.restrict Ω₀)
    let ρ := fun p : ℝ × EuStd => densityOnEuclid (I := I_hs) (g p.1) α p.2
    let A := fun i j (p : ℝ × EuStd) => weightedInvGramOnEuclid (I := I_hs) (g p.1) α i j p.2
    let U := dirichletLocalSpacetimeLp q α hΩ.measurableSet hΩc
      (hΩs.trans (image_mono interior_subset)) (timeMeasure T) u
    let V := fun i => dirichletLocalSpacetimeWeakPartialLp q α hΩ hΩc hΩs (timeMeasure T) i u
    let c := fun p : ℝ × EuStd => ρ p * ((1 / 2 : ℝ) * traceTimeDerivMetric (I := I_hs) g p.1
      ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm p.2)))
    ∀ DDf : Fin (Module.finrank ℝ EuN) → Fin (Module.finrank ℝ EuN) → Lp ℝ 2 ν,
      (∀ i j, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv j
        (fun z => DDf i j (t, z)) (fun z => Df i (t, z)) Ω₀) →
    ∃ R : Lp ℝ 2 ν,
      ∃ H : Fin (Module.finrank ℝ EuN) → Fin (Module.finrank ℝ EuN) → Lp ℝ 2 ν,
      ∃ Q : Fin (Module.finrank ℝ EuN) → Lp ℝ 2 ν,
      (∀ φ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Ioo a b ×ˢ Ω₀ →
        (∫ p, U p * fderiv ℝ φ p (1, 0) ∂ν) = -∫ p, R p * φ p ∂ν) ∧
      (∀ i k, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv k (fun z => H i k (t, z))
        (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (u t)) Ω₀) ∧
      (∀ i k, H i k = H k i) ∧
      (∀ k, Q k =ᵐ[ν] fun p =>
        (c p * V k p + fderiv ℝ c p (0, EuclideanSpace.single k 1) * U p +
          (ρ p * Df k p + fderiv ℝ ρ p (0, EuclideanSpace.single k 1) * F p)) +
        (∑ i, ∑ j, (fderiv ℝ (A i j) p (0, EuclideanSpace.single k 1) * H i j p +
          fderiv ℝ (fun z => fderiv ℝ (A i j) z (0, EuclideanSpace.single k 1)) p
            (0, EuclideanSpace.single j 1) * V i p)) -
        (fderiv ℝ ρ p (0, EuclideanSpace.single k 1) * R p +
          fderiv ℝ (fun z => fderiv ℝ ρ z (0, EuclideanSpace.single k 1)) p (1, 0) * U p)) ∧
      (∀ k (φ : ℝ × EuStd → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Ioo a b ×ˢ Ω₀ →
        (∫ p, ρ p * V k p * fderiv ℝ φ p (1, 0) ∂ν) =
          (∑ i, ∑ j, ∫ p, A i j p * H k i p *
            fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂ν) - ∫ p, Q k p * φ p ∂ν) ∧
      ∃ DQ : Fin (Module.finrank ℝ EuN) → Fin (Module.finrank ℝ EuN) → Lp ℝ 2 ν,
        (∀ k j, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv j
          (fun z => DQ k j (t, z)) (fun z => Q k (t, z)) Ω₀) ∧
        (∀ k, ∀ᵐ t ∂μ, MemWkp 1 2 (fun z => Q k (t, z)) Ω₀) ∧
        ∀ k, MemLp (fun t => (iteratedWeakSobolevNorm 1 2
          (fun z => Q k (t, z)) Ω₀).toReal) 2 μ := by
  intro F Df hDf μ ν ρ A U V c DDf hDDf
  have hsub : Ω₀ ⊆ Ω := subset_closure.trans hΩ₀Ω
  have hmeasure : ν ≤ (timeMeasure T).prod (volume.restrict Ω) :=
    Measure.prod_mono Measure.restrict_le_self (Measure.restrict_mono hsub le_rfl)
  have hD (k) : MemLp (Df k) 2 ν := (Lp.memLp (Df k)).mono_measure hmeasure
  let Df₀ := fun k => (hD k).toLp (Df k)
  have hDf₀ (k) : Df₀ k =ᵐ[ν] Df k := (hD k).coeFn_toLp
  have hweak (k) : ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv k
      (fun z => Df₀ k (t, z)) (fun z => F (t, z)) Ω₀ := by
    filter_upwards [ae_restrict_of_ae (s := Icc a b) (hDf k),
      Measure.ae_ae_of_ae_prod (hDf₀ k)] with t ht hd
    exact (DeGiorgi.HasWeakPartialDeriv.restrict hΩ₀ hsub ht).congr_ae
      Filter.EventuallyEq.rfl (Filter.EventuallyEq.symm hd)
  obtain ⟨R, H, Q, hR, hH, hsym, hQ, hgrad⟩ := exists_lp_weak_gradient_equation_of_heat_timeH1
    hG hT hreg q hCg hequiv Cv hCv0 hCvtop hvol α hΩ hΩc hΩs
    hΩ₀ hΩ₀Ω ha hb u f w hwmass hwderiv Df₀ hweak
  have hQouter (k) : Q k =ᵐ[ν] fun p =>
        (c p * V k p + fderiv ℝ c p (0, EuclideanSpace.single k 1) * U p +
          (ρ p * Df k p + fderiv ℝ ρ p (0, EuclideanSpace.single k 1) * F p)) +
        (∑ i, ∑ j, (fderiv ℝ (A i j) p (0, EuclideanSpace.single k 1) * H i j p +
          fderiv ℝ (fun z => fderiv ℝ (A i j) z (0, EuclideanSpace.single k 1)) p
            (0, EuclideanSpace.single j 1) * V i p)) -
        (fderiv ℝ ρ p (0, EuclideanSpace.single k 1) * R p +
          fderiv ℝ (fun z => fderiv ℝ ρ z (0, EuclideanSpace.single k 1)) p (1, 0) * U p) := by
    filter_upwards [hQ k, hDf₀ k] with p hp hd
    simpa only [hd] using hp
  have hsource := exists_spatial_weak_derivative_gradient_source_of_heat_timeH1
    hG hT hreg q hCg hequiv Cv hCv0 hCvtop hvol α hΩ hΩc hΩs
    hΩ₀ hΩ₀Ω ha hb hab u f w hwmass hwderiv Df hDf DDf hDDf R hR H hH Q hQouter
  exact ⟨R, H, Q, hR, hH, hsym, hQouter, hgrad, hsource⟩

end DifferentialGeometry.Analysis.Parabolic.Dirichlet
