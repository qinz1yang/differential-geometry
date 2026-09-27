import DifferentialGeometry.Analysis.Parabolic.Dirichlet.HeatFourthWeakDerivative
import DifferentialGeometry.Analysis.Calculus.IteratedDerivative.SpaceJets
import DifferentialGeometry.Analysis.Parabolic.Dirichlet.HeatTimeRegularity
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

theorem exists_second_spatial_weak_derivative_time_derivative_of_heat_timeH1
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
    let μ := (timeMeasure T).restrict (Icc a b)
    let ν := μ.prod (volume.restrict Ω₀)
    let U := dirichletLocalSpacetimeLp q α hΩ.measurableSet hΩc
      (hΩs.trans (image_mono interior_subset)) (timeMeasure T) u
    ∀ R : Lp ℝ 2 ν,
      (∀ φ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Ioo a b ×ˢ Ω₀ →
        (∫ p, U p * fderiv ℝ φ p (1, 0) ∂ν) = -∫ p, R p * φ p ∂ν) →
      ∃ DR : Fin (Module.finrank ℝ EuN) → Lp ℝ 2 ν,
        ∃ DDR : Fin (Module.finrank ℝ EuN) → Fin (Module.finrank ℝ EuN) → Lp ℝ 2 ν,
        (∀ k, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv k
          (fun x => DR k (t, x)) (fun x => R (t, x)) Ω₀) ∧
        (∀ k l, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv l
          (fun x => DDR k l (t, x)) (fun x => DR k (t, x)) Ω₀) ∧
        (∀ᵐ t ∂μ, MemWkp 2 2 (fun x => R (t, x)) Ω₀) ∧
        MemLp (fun t => (iteratedWeakSobolevNorm 2 2 (fun x => R (t, x)) Ω₀).toReal) 2 μ := by
  intro F Df hDf DDf hDDf μ ν U R hR
  classical
  let G : MetricConnectionFamilyOn (I := I_hs) (M := M) D :=
    { metric := g
      connection := fun t => leviCivitaConnectionOfMetric (g t)
      metricCompatible := fun t => leviCivitaConnectionOfMetric_isMetricCompatible (g t) }
  have hΩ₀c : IsCompact (closure Ω₀) :=
    hΩc.of_isClosed_subset isClosed_closure (hΩ₀Ω.trans subset_closure)
  obtain ⟨H, hH, _⟩ := exists_local_second_weak_derivative_of_heat_timeH1
    hG hT hreg q hCg hequiv Cv hCv0 hCvtop hvol α hΩ hΩc hΩs
    hΩ₀ hΩ₀c hΩ₀Ω ha hb u f w hwmass hwderiv
  obtain ⟨K, hK⟩ := exists_local_third_weak_derivative_of_heat_timeH1
    hG hT hreg q hCg hequiv Cv hCv0 hCvtop hvol α hΩ hΩc hΩs
    hΩ₀ hΩ₀Ω ha hb hab u f w hwmass hwderiv Df hDf H hH
  obtain ⟨L, hL⟩ := exists_local_fourth_weak_derivative_of_heat_timeH1
    hG hT hreg q hCg hequiv Cv hCv0 hCvtop hvol α hΩ hΩc hΩs
    hΩ₀ hΩ₀Ω ha hb hab u f w hwmass hwderiv Df hDf DDf hDDf H hH K hK
  have hsub : Ω₀ ⊆ Ω := subset_closure.trans hΩ₀Ω
  have hformula := weak_time_derivative_eq_source_of_heat_timeH1
    hG hT hreg q hCg hequiv Cv hCv0 hCvtop hvol α hΩ hΩc hΩs
    hΩ₀ hsub ha hb u f w hwmass hwderiv H hH R hR
  let V := fun i => dirichletLocalSpacetimeWeakPartialLp q α hΩ hΩc hΩs (timeMeasure T) i u
  have hmeasure : ν ≤ (timeMeasure T).prod (volume.restrict Ω) :=
    Measure.prod_mono Measure.restrict_le_self (Measure.restrict_mono hsub le_rfl)
  have hV (i) : MemLp (V i) 2 ν := (Lp.memLp (V i)).mono_measure hmeasure
  have hF : MemLp F 2 ν := (Lp.memLp F).mono_measure hmeasure
  have hD (i) : MemLp (Df i) 2 ν := (Lp.memLp (Df i)).mono_measure hmeasure
  have hDD (i j) : MemLp (DDf i j) 2 ν := (Lp.memLp (DDf i j)).mono_measure hmeasure
  let DDf₀ := fun i j => (hDD i j).toLp (DDf i j)
  have hDDf₀ (i j) : DDf₀ i j =ᵐ[ν] DDf i j := (hDD i j).coeFn_toLp
  let V₀ := fun i => (hV i).toLp (V i)
  let F₀ := hF.toLp F
  let Df₀ := fun i => (hD i).toLp (Df i)
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
  have hDfweak (i k) : ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv k
      (fun z => DDf₀ i k (t, z)) (fun z => Df₀ i (t, z)) Ω₀ := by
    filter_upwards [ae_restrict_of_ae (s := Icc a b) (hDDf i k),
      Measure.ae_ae_of_ae_prod (hDf₀ i), Measure.ae_ae_of_ae_prod (hDDf₀ i k)] with t ht hf hd
    exact (DeGiorgi.HasWeakPartialDeriv.restrict hΩ₀ hsub ht).congr_ae
      (Filter.EventuallyEq.symm hf) (Filter.EventuallyEq.symm hd)
  let W := toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target
  have hW : IsOpen W := (toEuclidean (E := EuN)).isOpenMap _ isOpen_interior
  have hΩ₀W : closure Ω₀ ⊆ W := hΩ₀Ω.trans (subset_closure.trans hΩs)
  let ρ := fun (p : ℝ × EuStd) => densityOnEuclid (g p.1) α p.2
  let A := fun i j (p : ℝ × EuStd) => weightedInvGramOnEuclid (g p.1) α i j p.2
  let P := fun i j p => (ρ p)⁻¹ * A i j p
  let Q := fun i (p : ℝ × EuStd) =>
    ∑ j, (ρ p)⁻¹ * fderiv ℝ (fun z => A i j (p.1, z)) p.2 (EuclideanSpace.single j 1)
  have hρ : ContDiffOn ℝ ∞ (fun p => (ρ p)⁻¹) (D.regular ×ˢ W) :=
    ((densityOnEuclid_family_contDiffOn (G := G) hG Subset.rfl α).mono
      (prod_mono Subset.rfl (image_mono interior_subset))).inv
        (fun p hp => (densityOnEuclid_pos (g p.1) α ((image_mono interior_subset) hp.2)).ne')
  have hP (i j) : ContDiffOn ℝ ∞ (P i j) (D.regular ×ˢ W) :=
    hρ.mul (weightedInvGramOnEuclid_family_contDiffOn (G := G) hG Subset.rfl α Subset.rfl i j)
  have hQ (i) : ContDiffOn ℝ ∞ (Q i) (D.regular ×ˢ W) := by
    apply ContDiffOn.sum
    intro j _
    exact hρ.mul ((weightedInvGramOnEuclid_family_fderiv_contDiffOn
      (G := G) hG Subset.rfl α hW Subset.rfl i j).clm_apply contDiffOn_const)
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
  let ι := (Fin (Module.finrank ℝ EuN) × Fin (Module.finrank ℝ EuN)) ⊕
    (Fin (Module.finrank ℝ EuN) ⊕ Unit)
  let Y : ι → Lp ℝ 2 ν := Sum.elim (fun ij => H ij.1 ij.2) (Sum.elim V₀ (fun _ => F₀))
  let DY : ι → Fin (Module.finrank ℝ EuN) → Lp ℝ 2 ν :=
    Sum.elim (fun ij k => K ij.1 ij.2 k) (Sum.elim (fun i k => H i k) (fun _ k => Df₀ k))
  let DDY : ι → Fin (Module.finrank ℝ EuN) → Fin (Module.finrank ℝ EuN) → Lp ℝ 2 ν :=
    Sum.elim (fun ij k l => L ij.1 ij.2 k l) (Sum.elim (fun i k l => K i k l) (fun _ k l => DDf₀ k l))
  let B : ι → ℝ × EuStd → ℝ :=
    Sum.elim (fun ij => P ij.1 ij.2) (Sum.elim Q (fun _ _ => 1))
  have hBreg (i) : ContDiffOn ℝ ∞ (B i) (D.regular ×ˢ W) := by
    rcases i with ⟨i, j⟩ | (i | i)
    · exact hP i j
    · exact hQ i
    · exact contDiffOn_const
  have hDBreg (i k) : ContDiffOn ℝ ∞ (fun p : ℝ × EuStd =>
      fderiv ℝ (fun z => B i (p.1, z)) p.2 (EuclideanSpace.single k 1)) (D.regular ×ˢ W) :=
    (DifferentialGeometry.Analysis.spatialFDeriv_contDiffOn
      (G := fun t z => B i (t, z)) D.regular_isOpen.uniqueDiffOn hW (hBreg i)).clm_apply
        contDiffOn_const
  have hB (i) : MemLp (B i) ∞ ν := (hbound _ (hBreg i)).1
  have hDB (i k) : MemLp (fun p => fderiv ℝ (fun z => B i (p.1, z)) p.2
      (EuclideanSpace.single k 1)) ∞ ν := (hbound _ (hBreg i)).2 k
  have hDDB (i k l) : MemLp (fun p => fderiv ℝ
      (fun z => fderiv ℝ (fun y => B i (p.1, y)) z (EuclideanSpace.single k 1)) p.2
        (EuclideanSpace.single l 1)) ∞ ν := (hbound _ (hDBreg i k)).2 l
  have hBs (i) : ∀ᵐ t ∂μ, ContDiffOn ℝ ∞ (fun z => B i (t, z)) Ω₀ :=
    hsmooth _ (hBreg i)
  have hDBs (i k) : ∀ᵐ t ∂μ, ContDiffOn ℝ ∞
      (fun z => fderiv ℝ (fun y => B i (t, y)) z (EuclideanSpace.single k 1)) Ω₀ :=
    hsmooth _ (hDBreg i k)
  have hY (i k) : ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv k
      (fun z => DY i k (t, z)) (fun z => Y i (t, z)) Ω₀ := by
    rcases i with ⟨i, j⟩ | (i | i)
    · exact hK i j k
    · exact hVweak i k
    · exact hFweak k
  have hDY (i k l) : ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv l
      (fun z => DDY i k l (t, z)) (fun z => DY i k (t, z)) Ω₀ := by
    rcases i with ⟨i, j⟩ | (i | i)
    · exact hL i j k l
    · exact hK i k l
    · exact hDfweak k l
  have hRsum : R =ᵐ[ν] fun p => ∑ i, B i p * Y i p := by
    filter_upwards [hformula, hF₀, ae_all_iff.mpr hV₀] with p hp hf hv
    change R p = ∑ i : (Fin (Module.finrank ℝ EuN) × Fin (Module.finrank ℝ EuN)) ⊕
      (Fin (Module.finrank ℝ EuN) ⊕ Unit), B i p * Y i p
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
    change R p = (∑ ij : Fin (Module.finrank ℝ EuN) × Fin (Module.finrank ℝ EuN),
        P ij.1 ij.2 p * H ij.1 ij.2 p) + ((∑ i, Q i p * V₀ i p) + ∑ _ : Unit, 1 * F₀ p)
    simp only [Fintype.sum_prod_type, one_mul, Fintype.sum_unique]
    rw [hf]
    simp_rw [hv]
    rw [hp]
    change (ρ p)⁻¹ * (∑ i, ∑ j, (A i j p * H i j p +
      fderiv ℝ (fun z => A i j (p.1, z)) p.2 (EuclideanSpace.single j 1) * V i p)) + F p = _
    simp only [P, Q, Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_mul, mul_add, mul_assoc, add_assoc]
  obtain ⟨DR, hDR, _, _, DDR, hDDR, _, _⟩ :=
    exists_lp_second_spatial_weak_partials_of_ae_eq_finite_sum hΩ₀ (fun _ : Unit => R)
      (fun _ => Y) (fun _ => DY) (fun _ => DDY) (fun _ => B)
      (fun _ => hB) (fun _ => hDB) (fun _ => hDDB) (fun _ => hBs) (fun _ => hDBs)
      (fun _ => hY) (fun _ => hDY) (fun _ => hRsum)
  have hDRreg (k) := ae_memWkp_one_and_memLp_wkpNorm_of_weak_partials
    hΩ₀ (by norm_num : (1 : ℝ≥0∞) ≤ 2) (by norm_num) (Lp.memLp (DR () k))
    (fun l => Lp.memLp (DDR () k l)) (hDDR () k)
  have hRreg := ae_memWkp_succ_and_memLp_wkpNorm_of_weak_partials
    hΩ₀ (by norm_num : (1 : ℝ≥0∞) ≤ 2) (by norm_num) (Lp.memLp R)
    (fun k => (hDRreg k).1) (fun k => (hDRreg k).2) (hDR ())
  exact ⟨DR (), DDR (), hDR (), hDDR (), hRreg.1, hRreg.2⟩

end DifferentialGeometry.Analysis.Parabolic.Dirichlet
