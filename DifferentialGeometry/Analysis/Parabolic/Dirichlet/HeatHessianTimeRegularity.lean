import DifferentialGeometry.Analysis.Parabolic.Dirichlet.HeatTimeDerivativeHessian
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.TimeWeakDerivativeProduct

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

theorem exists_timeH1_hessian_of_heat_timeH1
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
    {a b : ℝ} (ha : 0 < a) (hb : b < T) (hab : a < b)
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
    ∀ H : Fin (Module.finrank ℝ EuN) → Fin (Module.finrank ℝ EuN) →
        Lp ℝ 2 (μ.prod (volume.restrict Ω₀)),
      (∀ i j, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv j (fun x => H i j (t, x))
        (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (u t)) Ω₀) →
      ∀ i j, ∃ v : timeH1 (Lp ℝ 2 (volume.restrict Ω₀)) (b - a),
        ∀ᵐ s ∂timeMeasure (b - a),
          (v.toFun s : EuStd → ℝ) =ᵐ[volume.restrict Ω₀] fun x => H i j (a + s, x) := by
  intro F Df hDf DDf hDDf
  have hI : Icc a b ⊆ Icc (0 : ℝ) T := Icc_subset_Icc ha.le hb.le
  have hμ : (timeMeasure T).restrict (Icc a b) = volume.restrict (Icc a b) :=
    Measure.restrict_restrict_of_subset hI
  dsimp only
  rw [hμ]
  intro H hH
  let μ := volume.restrict (Icc a b)
  let ν := μ.prod (volume.restrict Ω₀)
  have hμle : μ ≤ timeMeasure T := by
    change volume.restrict (Icc a b) ≤ timeMeasure T
    rw [← hμ]
    exact Measure.restrict_le_self
  have hsub : Ω₀ ⊆ Ω := subset_closure.trans hΩ₀Ω
  have hmeasure : ν ≤ (timeMeasure T).prod (volume.restrict Ω) :=
    Measure.prod_mono hμle (Measure.restrict_mono hsub le_rfl)
  have hsource := exists_local_lp_weak_time_deriv_of_heat_timeH1
    hG hT hreg q hCg hequiv Cv hCv0 hCvtop hvol α hΩ hΩc hΩs
    hΩ₀ hΩ₀Ω ha hb u f w hwmass hwderiv
  dsimp only at hsource
  rw [hμ] at hsource
  obtain ⟨R, hR⟩ := hsource
  have hsecond := exists_second_spatial_weak_derivative_time_derivative_of_heat_timeH1
    hG hT hreg q hCg hequiv Cv hCv0 hCvtop hvol α hΩ hΩc hΩs
    hΩ₀ hΩ₀Ω ha hb hab.le u f w hwmass hwderiv Df hDf DDf hDDf
  dsimp only at hsecond
  rw [hμ] at hsecond
  obtain ⟨DR, DDR, hDR, hDDR, _, _⟩ := hsecond R hR
  let U := dirichletLocalSpacetimeLp q α hΩ.measurableSet hΩc
    (hΩs.trans (image_mono interior_subset)) (timeMeasure T) u
  let V := fun i => dirichletLocalSpacetimeWeakPartialLp q α hΩ hΩc hΩs (timeMeasure T) i u
  have hU : MemLp U 2 ν := (Lp.memLp U).mono_measure hmeasure
  have hV (i) : MemLp (V i) 2 ν := (Lp.memLp (V i)).mono_measure hmeasure
  let U₀ := hU.toLp U
  let V₀ := fun i => (hV i).toLp (V i)
  have hU₀ : U₀ =ᵐ[ν] U := hU.coeFn_toLp
  have hV₀ (i) : V₀ i =ᵐ[ν] V i := (hV i).coeFn_toLp
  have hfirst (i) : ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv i
      (fun x => V₀ i (t, x)) (fun x => U₀ (t, x)) Ω₀ := by
    filter_upwards [(hasWeakPartialDeriv_dirichletLocalSpacetimeWeakPartialLp q α
      hΩ hΩc hΩs (timeMeasure T) i u).filter_mono (ae_mono hμle),
      Measure.ae_ae_of_ae_prod hU₀, Measure.ae_ae_of_ae_prod (hV₀ i)] with t ht hu hv
    exact (ht.restrict hΩ₀ hsub).congr_ae
      (Filter.EventuallyEq.symm hu) (Filter.EventuallyEq.symm hv)
  have hsecondH (i j) : ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv j
      (fun x => H i j (t, x)) (fun x => V₀ i (t, x)) Ω₀ := by
    have hVi := (dirichletLocalSpacetimeWeakPartialLp_coeFn q α
      hΩ hΩc hΩs (timeMeasure T) i u).filter_mono (ae_mono hμle)
    filter_upwards [hH i j, Measure.ae_ae_of_ae_prod (hV₀ i), hVi] with t ht hv he
    exact hasWeakPartialDeriv_congr_ae hΩ₀ j
      (Filter.EventuallyEq.symm
        (Filter.EventuallyEq.trans hv
        (he.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))))) ht
  let A : ∀ m : ℕ, (Fin m → Fin (Module.finrank ℝ EuN)) → Lp ℝ 2 ν
    | 0, _ => U₀
    | 1, α => V₀ (α 0)
    | 2, α => H (α 1) (α 0)
    | _ + 3, _ => 0
  let B : ∀ m : ℕ, (Fin m → Fin (Module.finrank ℝ EuN)) → Lp ℝ 2 ν
    | 0, _ => R
    | 1, α => DR (α 0)
    | 2, α => DDR (α 1) (α 0)
    | _ + 3, _ => 0
  have hAweak : ∀ m < 2, ∀ α i, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv i
      (fun x => A (m + 1) (Fin.cons i α) (t, x)) (fun x => A m α (t, x)) Ω₀ := by
    intro m hm α i
    interval_cases m
    · simpa only [A, Fin.cons_zero] using hfirst i
    · simpa only [A, Fin.cons_zero, Fin.cons_one] using hsecondH (α 0) i
  have hBweak : ∀ m < 2, ∀ α i, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv i
      (fun x => B (m + 1) (Fin.cons i α) (t, x)) (fun x => B m α (t, x)) Ω₀ := by
    intro m hm α i
    interval_cases m
    · simpa only [B, Fin.cons_zero] using hDR i
    · simpa only [B, Fin.cons_zero, Fin.cons_one] using hDDR (α 0) i
  have hroot : ∀ φ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b ×ˢ Ω₀ →
      (∫ p, A 0 (fun i => Fin.elim0 i) p * fderiv ℝ φ p (1, 0) ∂ν) =
        -∫ p, B 0 (fun i => Fin.elim0 i) p * φ p ∂ν := by
    intro φ hφ hφc hφs
    refine (integral_congr_ae ?_).trans (hR φ hφ hφc hφs)
    filter_upwards [hU₀] with p hp
    exact congrArg (fun z => z * fderiv ℝ φ p (1, 0)) hp
  intro i j
  obtain ⟨v, hv⟩ := exists_timeH1_of_finite_weak_partial_trees hab hΩ₀ 2 A B
    hAweak hBweak hroot 2 le_rfl (Fin.cons j (Fin.cons i (fun k => Fin.elim0 k)))
  refine ⟨v, ?_⟩
  filter_upwards [hv] with s hs
  simpa only [A, Fin.cons_zero, Fin.cons_one] using hs.1

end DifferentialGeometry.Analysis.Parabolic.Dirichlet
