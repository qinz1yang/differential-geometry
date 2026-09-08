import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.TimeH1IntegrationByParts
import DifferentialGeometry.Analysis.Parabolic.Dirichlet.WeakEquationChart
import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletLocalWeakForm
import DifferentialGeometry.Analysis.Integration.Lp.Product

noncomputable section

open Bundle Filter Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet

open DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Measure

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]

private local instance : MeasurableSpace (EuclideanSpace ℝ (Fin n)) := borel _
private local instance : BorelSpace (EuclideanSpace ℝ (Fin n)) := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "I_hs" => modelWithCornersEuclideanHalfSpace n
local notation "EuN" => EuclideanSpace ℝ (Fin n)
local notation "EuStd" => EuclideanSpace ℝ (Fin (Module.finrank ℝ EuN))

private local instance : MeasurableSpace EuStd :=
  WithLp.measurableSpace 2 ((i : Fin (Module.finrank ℝ EuN)) → ℝ)

def dirichletLocalSpacetimeLp
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : MeasurableSet Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' (extChartAt I_hs α).target)
    {Z : Type*} [MeasurableSpace Z] (μ : Measure Z) :
    Lp (H1ComplDirichlet q) 2 μ →L[ℝ] Lp ℝ 2 (μ.prod (volume.restrict Ω)) :=
  (Lp.uncurry ℝ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)).toContinuousLinearMap.comp
    (((chartRestrictionLp q α hΩ hΩc hΩs 2).comp (H1ComplDirichletToLp q)).compLpL 2 μ)

def dirichletLocalSpacetimeWeakPartialLp
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    {Z : Type*} [MeasurableSpace Z] (μ : Measure Z) (i : Fin (Module.finrank ℝ EuN)) :
    Lp (H1ComplDirichlet q) 2 μ →L[ℝ] Lp ℝ 2 (μ.prod (volume.restrict Ω)) :=
  (Lp.uncurry ℝ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)).toContinuousLinearMap.comp
    ((dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i).compLpL 2 μ)

theorem dirichletLocalSpacetimeLp_coeFn
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : MeasurableSet Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' (extChartAt I_hs α).target)
    {Z : Type*} [MeasurableSpace Z] (μ : Measure Z) (u : Lp (H1ComplDirichlet q) 2 μ) :
    ∀ᵐ t ∂μ, (fun z => dirichletLocalSpacetimeLp q α hΩ hΩc hΩs μ u (t, z)) =ᵐ[volume.restrict Ω]
      fun z => H1ComplDirichletToLp q (u t)
        ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z)) := by
  let R := (chartRestrictionLp q α hΩ hΩc hΩs 2).comp (H1ComplDirichletToLp q)
  filter_upwards [Lp.uncurry_compLpL_coeFn (𝕜 := ℝ) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) R u]
    with t ht
  exact ht.trans (chartRestrictionLp_coeFn q α hΩ hΩc hΩs 2 (H1ComplDirichletToLp q (u t)))

theorem dirichletLocalSpacetimeWeakPartialLp_coeFn
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    {Z : Type*} [MeasurableSpace Z] (μ : Measure Z) (i : Fin (Module.finrank ℝ EuN))
    (u : Lp (H1ComplDirichlet q) 2 μ) :
    ∀ᵐ t ∂μ,
      (fun z => dirichletLocalSpacetimeWeakPartialLp q α hΩ hΩc hΩs μ i u (t, z))
        =ᵐ[volume.restrict Ω] (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (u t) : EuStd → ℝ) :=
  Lp.uncurry_compLpL_coeFn (𝕜 := ℝ) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
    (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i) u

theorem hasWeakPartialDeriv_dirichletLocalSpacetimeWeakPartialLp
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    {Z : Type*} [MeasurableSpace Z] (μ : Measure Z) (i : Fin (Module.finrank ℝ EuN))
    (u : Lp (H1ComplDirichlet q) 2 μ) :
    ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv i
      (fun z => dirichletLocalSpacetimeWeakPartialLp q α hΩ hΩc hΩs μ i u (t, z))
      (fun z => dirichletLocalSpacetimeLp q α hΩ.measurableSet hΩc
        (hΩs.trans (image_mono interior_subset)) μ u (t, z)) Ω := by
  filter_upwards [dirichletLocalSpacetimeLp_coeFn q α hΩ.measurableSet hΩc
    (hΩs.trans (image_mono interior_subset)) μ u,
    dirichletLocalSpacetimeWeakPartialLp_coeFn q α hΩ hΩc hΩs μ i u] with t ht₁ ht₂
  have hw := hasWeakPartialDeriv_dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (u t)
  intro ψ hψ hψc hψs
  have hv :
      (∫ z in Ω, dirichletLocalSpacetimeLp q α hΩ.measurableSet hΩc
          (hΩs.trans (image_mono interior_subset)) μ u (t, z) *
        fderiv ℝ ψ z (EuclideanSpace.single i 1)) =
      ∫ z in Ω, H1ComplDirichletToLp q (u t)
        ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z)) *
          fderiv ℝ ψ z (EuclideanSpace.single i 1) := by
    apply integral_congr_ae
    filter_upwards [ht₁] with z hz
    rw [hz]
  rw [hv, hw ψ hψ hψc hψs]
  congr 1
  apply integral_congr_ae
  filter_upwards [ht₂] with z hz
  rw [hz]

theorem IsWeakEvolutionSolution.exists_timeH1_integral_local_adjoint
    {q : SmoothRiemannianMetric I_hs M}
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I_hs) (M := M) D}
    {hG : MetricFamilySmoothOn (I := I_hs) (M := M) D G.metric}
    {T : ℝ} {hT : 0 ≤ T} {hreg : Icc (0 : ℝ) T ⊆ D.regular}
    {X : ℝ → Cₛ^∞⟮I_hs; EuN, (TangentSpace I_hs : M → Type _)⟯}
    {a : ℝ → ℝ} {Bx Bv : ℝ}
    {hX : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : M, (G.metric t).inner x (X t x) (X t x) ≤ Bx}
    {htrace : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : M,
      |traceTimeDerivMetric (I := I_hs) G.metric t x| ≤ Bv}
    {f₀ : Lp ℝ 2 (riemannianVolumeMeasure (I := I_hs) (M := M) q)}
    {u : timeL2 (H1ComplDirichlet q) T}
    (hu : IsWeakEvolutionSolution hG hT hreg X a Bx Bv hX htrace f₀ u)
    (α : M) {Ω : Set EuStd}
    (hΩs : Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (ψ : EuStd → ℝ)
    (hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_cpt : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ Ω) :
    let e := toEuclidean (E := EuN)
    let x := fun z : EuStd => (extChartAt I_hs α).symm (e.symm z)
    let ρ := fun t z => chartDensityOnE (I := I_hs) (G.metric t) α (e.symm z)
    let A := fun t i j z => chartInvGramOnE (I := I_hs) (G.metric t) α i j (e.symm z)
    let B := fun t i z => chartCoeffOnE (I := I_hs) α (X t) i (e.symm z)
    ∃ w : timeH1 ℝ T,
      w.init = ∫ z in Ω, ρ 0 z * (f₀ (x z) * ψ z) ∧
      (fun t => ∫ z in Ω, ρ t z * (H1ComplDirichletToLp q (u t) (x z) * ψ z))
        =ᵐ[timeMeasure T] w.toFun ∧
      w.deriv =ᵐ[timeMeasure T] fun t =>
        (∫ z in Ω, ρ t z *
          ((1 / 2 : ℝ) * traceTimeDerivMetric (I := I_hs) G.metric t (x z) *
            (H1ComplDirichletToLp q (u t) (x z) * ψ z))) +
        ∫ z in Ω, ρ t z * H1ComplDirichletToLp q (u t) (x z) *
          ((∑ i : Fin (Module.finrank ℝ EuN),
            fderiv ℝ (fun z' : EuStd =>
              (∑ j : Fin (Module.finrank ℝ EuN),
                A t i j z' * fderiv ℝ ψ z' (EuclideanSpace.single j 1)) * ρ t z') z
                (EuclideanSpace.single i 1)) / ρ t z -
            (∑ i : Fin (Module.finrank ℝ EuN), B t i z *
              fderiv ℝ ψ z (EuclideanSpace.single i 1)) -
            localDivergence (I := I_hs) (G.metric t) α (X t) (x z) * ψ z - a t * ψ z) := by
  intro e x ρ A B
  let S := e '' interior (extChartAt I_hs α).target
  have hS : IsOpen S := e.toHomeomorph.isOpenMap _ isOpen_interior
  have hrestrict (F : EuStd → ℝ) (hF : ∀ z, z ∉ tsupport ψ → F z = 0) :
      (∫ z in S, F z) = ∫ z in Ω, F z :=
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hS.measurableSet hΩs
      (fun z hz => hF z (fun h => hz.2 (hψ_supp h)))
  have hm (t : ℝ) (F c : EuStd → ℝ) :
      (∫ z in S, ρ t z * (c z * (F z * ψ z))) =
        ∫ z in Ω, ρ t z * (c z * (F z * ψ z)) := by
    apply hrestrict
    intro z hz
    rw [image_eq_zero_of_notMem_tsupport hz]
    ring
  have hm₀ (t : ℝ) (F : EuStd → ℝ) :
      (∫ z in S, ρ t z * (F z * ψ z)) = ∫ z in Ω, ρ t z * (F z * ψ z) := by
    simpa only [one_mul] using hm t F (fun _ => 1)
  have ha (t : ℝ) :
      (∫ z in S, ρ t z * H1ComplDirichletToLp q (u t) (x z) *
        ((∑ i, fderiv ℝ (fun z' : EuStd =>
            (∑ j, A t i j z' * fderiv ℝ ψ z' (EuclideanSpace.single j 1)) * ρ t z') z
            (EuclideanSpace.single i 1)) / ρ t z -
          (∑ i, B t i z * fderiv ℝ ψ z (EuclideanSpace.single i 1)) -
          localDivergence (I := I_hs) (G.metric t) α (X t) (x z) * ψ z - a t * ψ z)) =
      ∫ z in Ω, ρ t z * H1ComplDirichletToLp q (u t) (x z) *
        ((∑ i, fderiv ℝ (fun z' : EuStd =>
            (∑ j, A t i j z' * fderiv ℝ ψ z' (EuclideanSpace.single j 1)) * ρ t z') z
            (EuclideanSpace.single i 1)) / ρ t z -
          (∑ i, B t i z * fderiv ℝ ψ z (EuclideanSpace.single i 1)) -
          localDivergence (I := I_hs) (G.metric t) α (X t) (x z) * ψ z - a t * ψ z) :=
    Sobolev.Euclidean.integral_adjoint_eq_integral_of_tsupport_subset hS.measurableSet hΩs hψ_supp
      (fun z => H1ComplDirichletToLp q (u t) (x z)) (ρ t)
      (fun z => localDivergence (I := I_hs) (G.metric t) α (X t) (x z))
      (fun _ => a t) (A t) (B t)
  obtain ⟨w, hw₀, hwm, hwd⟩ := hu.exists_timeH1_integral_euclidean α ψ
    hψ_smooth hψ_cpt (hψ_supp.trans hΩs)
  refine ⟨w, hw₀.trans (hm₀ 0 (fun z => f₀ (x z))), ?_, ?_⟩
  · filter_upwards [hwm] with t ht
    exact (hm₀ t (fun z => H1ComplDirichletToLp q (u t) (x z))).symm.trans ht
  · filter_upwards [hwd] with t ht
    rw [ht, ha]
    congr 1
    exact hm t (fun z => H1ComplDirichletToLp q (u t) (x z))
      (fun z => (1 / 2 : ℝ) * traceTimeDerivMetric (I := I_hs) G.metric t (x z))

theorem IsWeakEvolutionSolution.exists_timeH1_integral_local
    {q : SmoothRiemannianMetric I_hs M}
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I_hs) (M := M) D}
    {hG : MetricFamilySmoothOn (I := I_hs) (M := M) D G.metric}
    {T : ℝ} {hT : 0 ≤ T} {hreg : Icc (0 : ℝ) T ⊆ D.regular}
    {X : ℝ → Cₛ^∞⟮I_hs; EuN, (TangentSpace I_hs : M → Type _)⟯}
    {a : ℝ → ℝ} {Bx Bv : ℝ}
    {hX : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : M, (G.metric t).inner x (X t x) (X t x) ≤ Bx}
    {htrace : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : M,
      |traceTimeDerivMetric (I := I_hs) G.metric t x| ≤ Bv}
    {f₀ : Lp ℝ 2 (riemannianVolumeMeasure (I := I_hs) (M := M) q)}
    {u : timeL2 (H1ComplDirichlet q) T}
    (hu : IsWeakEvolutionSolution hG hT hreg X a Bx Bv hX htrace f₀ u)
    (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (ψ : EuStd → ℝ)
    (hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_cpt : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ Ω) :
    let e := toEuclidean (E := EuN)
    let x := fun z : EuStd => (extChartAt I_hs α).symm (e.symm z)
    let ρ := fun t z => chartDensityOnE (I := I_hs) (G.metric t) α (e.symm z)
    let A := fun t i j z => chartInvGramOnE (I := I_hs) (G.metric t) α i j (e.symm z)
    let B := fun t i z => chartCoeffOnE (I := I_hs) α (X t) i (e.symm z)
    ∃ w : timeH1 ℝ T,
      w.init = ∫ z in Ω, ρ 0 z * (f₀ (x z) * ψ z) ∧
      (fun t => ∫ z in Ω, ρ t z * (H1ComplDirichletToLp q (u t) (x z) * ψ z))
        =ᵐ[timeMeasure T] w.toFun ∧
      w.deriv =ᵐ[timeMeasure T] fun t =>
        (∫ z in Ω, ρ t z *
          ((1 / 2 : ℝ) * traceTimeDerivMetric (I := I_hs) G.metric t (x z) *
            (H1ComplDirichletToLp q (u t) (x z) * ψ z))) -
        (∑ i : Fin (Module.finrank ℝ EuN), ∫ z in Ω,
          dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (u t) z *
            ((∑ j : Fin (Module.finrank ℝ EuN), A t i j z *
              fderiv ℝ ψ z (EuclideanSpace.single j 1)) * ρ t z - B t i z * ρ t z * ψ z)) -
        ∫ z in Ω, ρ t z * H1ComplDirichletToLp q (u t) (x z) * (a t * ψ z) := by
  intro e x ρ A B
  obtain ⟨w, hw₀, hwm, hwd⟩ := hu.exists_timeH1_integral_local_adjoint α
    (subset_closure.trans hΩs) ψ hψ_smooth hψ_cpt hψ_supp
  refine ⟨w, hw₀, hwm, ?_⟩
  filter_upwards [hwd] with t ht
  rw [ht, integral_chart_adjoint_sub_potential_eq_neg_sum_integral q (G.metric t) α
    hΩ hΩc hΩs (X t) (u t) continuousOn_const hψ_smooth hψ_cpt hψ_supp]
  ring

theorem IsWeakEvolutionSolution.exists_timeH1_integral_spacetime
    {q : SmoothRiemannianMetric I_hs M}
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I_hs) (M := M) D}
    {hG : MetricFamilySmoothOn (I := I_hs) (M := M) D G.metric}
    {T : ℝ} {hT : 0 ≤ T} {hreg : Icc (0 : ℝ) T ⊆ D.regular}
    {X : ℝ → Cₛ^∞⟮I_hs; EuN, (TangentSpace I_hs : M → Type _)⟯}
    {a : ℝ → ℝ} {Bx Bv : ℝ}
    {hX : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : M, (G.metric t).inner x (X t x) (X t x) ≤ Bx}
    {htrace : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : M,
      |traceTimeDerivMetric (I := I_hs) G.metric t x| ≤ Bv}
    {f₀ : Lp ℝ 2 (riemannianVolumeMeasure (I := I_hs) (M := M) q)}
    {u : timeL2 (H1ComplDirichlet q) T}
    (hu : IsWeakEvolutionSolution hG hT hreg X a Bx Bv hX htrace f₀ u)
    (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (ψ : EuStd → ℝ)
    (hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_cpt : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ Ω) :
    let e := toEuclidean (E := EuN)
    let x := fun z : EuStd => (extChartAt I_hs α).symm (e.symm z)
    let ρ := fun t z => chartDensityOnE (I := I_hs) (G.metric t) α (e.symm z)
    let A := fun t i j z => chartInvGramOnE (I := I_hs) (G.metric t) α i j (e.symm z)
    let B := fun t i z => chartCoeffOnE (I := I_hs) α (X t) i (e.symm z)
    let U := dirichletLocalSpacetimeLp q α hΩ.measurableSet hΩc
      (hΩs.trans (image_mono interior_subset)) (timeMeasure T) u
    let DU := fun i => dirichletLocalSpacetimeWeakPartialLp q α hΩ hΩc hΩs (timeMeasure T) i u
    ∃ w : timeH1 ℝ T,
      w.init = ∫ z in Ω, ρ 0 z * (f₀ (x z) * ψ z) ∧
      (fun t => ∫ z in Ω, ρ t z * (U (t, z) * ψ z))
        =ᵐ[timeMeasure T] w.toFun ∧
      w.deriv =ᵐ[timeMeasure T] fun t =>
        (∫ z in Ω, ρ t z *
          ((1 / 2 : ℝ) * traceTimeDerivMetric (I := I_hs) G.metric t (x z) *
            (U (t, z) * ψ z))) -
        (∑ i : Fin (Module.finrank ℝ EuN), ∫ z in Ω,
          DU i (t, z) *
            ((∑ j : Fin (Module.finrank ℝ EuN), A t i j z *
              fderiv ℝ ψ z (EuclideanSpace.single j 1)) * ρ t z - B t i z * ρ t z * ψ z)) -
        ∫ z in Ω, ρ t z * U (t, z) * (a t * ψ z) := by
  intro e x ρ A B U DU
  obtain ⟨w, hw₀, hwm, hwd⟩ := hu.exists_timeH1_integral_local α hΩ hΩc hΩs ψ
    hψ_smooth hψ_cpt hψ_supp
  have hv := dirichletLocalSpacetimeLp_coeFn q α hΩ.measurableSet hΩc
    (hΩs.trans (image_mono interior_subset)) (timeMeasure T) u
  have hD : ∀ᵐ t ∂timeMeasure T, ∀ i : Fin (Module.finrank ℝ EuN),
      (fun z => DU i (t, z)) =ᵐ[volume.restrict Ω]
        (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (u t) : EuStd → ℝ) :=
    ae_all_iff.mpr (fun i => dirichletLocalSpacetimeWeakPartialLp_coeFn q α hΩ hΩc hΩs
      (timeMeasure T) i u)
  refine ⟨w, hw₀, ?_, ?_⟩
  · filter_upwards [hwm, hv] with t ht htval
    rw [← ht]
    apply integral_congr_ae
    filter_upwards [htval] with z hz
    rw [hz]
  · filter_upwards [hwd, hv, hD] with t ht htval htderiv
    rw [ht]
    apply congrArg₂ (fun a b : ℝ => a - b)
    · apply congrArg₂ (fun a b : ℝ => a - b)
      · apply integral_congr_ae
        filter_upwards [htval] with z hz
        rw [hz]
      · apply Finset.sum_congr rfl
        intro i _
        apply integral_congr_ae
        filter_upwards [htderiv i] with z hz
        rw [hz]
    · apply integral_congr_ae
      filter_upwards [htval] with z hz
      rw [hz]

theorem IsWeakEvolutionSolution.integral_time_test
    {q : SmoothRiemannianMetric I_hs M}
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I_hs) (M := M) D}
    {hG : MetricFamilySmoothOn (I := I_hs) (M := M) D G.metric}
    {T : ℝ} {hT : 0 ≤ T} {hreg : Icc (0 : ℝ) T ⊆ D.regular}
    {X : ℝ → Cₛ^∞⟮I_hs; EuN, (TangentSpace I_hs : M → Type _)⟯}
    {a : ℝ → ℝ} {Bx Bv : ℝ}
    {hX : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : M, (G.metric t).inner x (X t x) (X t x) ≤ Bx}
    {htrace : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : M,
      |traceTimeDerivMetric (I := I_hs) G.metric t x| ≤ Bv}
    {f₀ : Lp ℝ 2 (riemannianVolumeMeasure (I := I_hs) (M := M) q)}
    {u : timeL2 (H1ComplDirichlet q) T}
    (hu : IsWeakEvolutionSolution hG hT hreg X a Bx Bv hX htrace f₀ u)
    (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (ψ : EuStd → ℝ)
    (hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_cpt : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ Ω) {η : ℝ → ℝ}
    (hη : ContDiffOn ℝ 1 η (Icc (0 : ℝ) T)) (hηT : η T = 0) :
    let e := toEuclidean (E := EuN)
    let x := fun z : EuStd => (extChartAt I_hs α).symm (e.symm z)
    let ρ := fun t z => chartDensityOnE (I := I_hs) (G.metric t) α (e.symm z)
    let A := fun t i j z => chartInvGramOnE (I := I_hs) (G.metric t) α i j (e.symm z)
    let B := fun t i z => chartCoeffOnE (I := I_hs) α (X t) i (e.symm z)
    let U := dirichletLocalSpacetimeLp q α hΩ.measurableSet hΩc
      (hΩs.trans (image_mono interior_subset)) (timeMeasure T) u
    let DU := fun i => dirichletLocalSpacetimeWeakPartialLp q α hΩ hΩc hΩs (timeMeasure T) i u;
    -(∫ t, _root_.deriv η t * (∫ z in Ω, ρ t z * (U (t, z) * ψ z)) ∂timeMeasure T) -
      η 0 * (∫ z in Ω, ρ 0 z * (f₀ (x z) * ψ z)) =
        ∫ t, η t * ((∫ z in Ω, ρ t z *
          ((1 / 2 : ℝ) * traceTimeDerivMetric (I := I_hs) G.metric t (x z) *
            (U (t, z) * ψ z))) -
        (∑ i : Fin (Module.finrank ℝ EuN), ∫ z in Ω,
          DU i (t, z) *
            ((∑ j : Fin (Module.finrank ℝ EuN), A t i j z *
              fderiv ℝ ψ z (EuclideanSpace.single j 1)) * ρ t z - B t i z * ρ t z * ψ z)) -
        ∫ z in Ω, ρ t z * U (t, z) * (a t * ψ z)) ∂timeMeasure T := by
  intro e x ρ A B U DU
  obtain ⟨w, hw₀, hwm, hwd⟩ := hu.exists_timeH1_integral_spacetime α hΩ hΩc hΩs ψ
    hψ_smooth hψ_cpt hψ_supp
  let m := fun t => ∫ z in Ω, ρ t z * (U (t, z) * ψ z)
  let I₀ := ∫ z in Ω, ρ 0 z * (f₀ (x z) * ψ z)
  let F := fun t => (∫ z in Ω, ρ t z *
          ((1 / 2 : ℝ) * traceTimeDerivMetric (I := I_hs) G.metric t (x z) *
            (U (t, z) * ψ z))) -
        (∑ i : Fin (Module.finrank ℝ EuN), ∫ z in Ω,
          DU i (t, z) *
            ((∑ j : Fin (Module.finrank ℝ EuN), A t i j z *
              fderiv ℝ ψ z (EuclideanSpace.single j 1)) * ρ t z - B t i z * ρ t z * ψ z)) -
        ∫ z in Ω, ρ t z * U (t, z) * (a t * ψ z)
  change -(∫ t, _root_.deriv η t * m t ∂timeMeasure T) - η 0 * I₀ =
    ∫ t, η t * F t ∂timeMeasure T
  have hm : (∫ t, w.toFun t * _root_.deriv η t ∂timeMeasure T) =
      ∫ t, _root_.deriv η t * m t ∂timeMeasure T := by
    apply integral_congr_ae
    filter_upwards [hwm] with t ht
    rw [← ht]
    exact mul_comm _ _
  have hd : (∫ t, η t * w.deriv t ∂timeMeasure T) =
      ∫ t, η t * F t ∂timeMeasure T := by
    apply integral_congr_ae
    filter_upwards [hwd] with t ht
    rw [ht]
  have hzero : w.toFun 0 = I₀ := by
    rw [timeH1.toFun_apply, intervalIntegral.integral_same, add_zero]
    exact hw₀
  have hb : w.toFun T * η T - w.toFun 0 * η 0 = -η 0 * I₀ := by
    rw [hηT, hzero]
    ring
  have hi := w.integral_mul_deriv_add_deriv_mul hT hη
  rw [hb, hm, hd] at hi
  linarith

theorem IsWeakEvolutionSolution.integral_local_adjoint_test
    {q : SmoothRiemannianMetric I_hs M}
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I_hs) (M := M) D}
    {hG : MetricFamilySmoothOn (I := I_hs) (M := M) D G.metric}
    {T : ℝ} {hT : 0 ≤ T} {hreg : Icc (0 : ℝ) T ⊆ D.regular}
    {X : ℝ → Cₛ^∞⟮I_hs; EuclideanSpace ℝ (Fin n),
      (TangentSpace I_hs : M → Type _)⟯}
    (hXcont : ContinuousOn
      (fun p : ℝ × M ↦
        (TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p.2 (X p.1 p.2) :
          TangentBundle I_hs M))
      (Icc (0 : ℝ) T ×ˢ (Set.univ : Set M)))
    {a : ℝ → ℝ} (hacont : ContinuousOn a (Icc (0 : ℝ) T))
    {Bx Bv : ℝ}
    {hX : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : M,
      (G.metric t).inner x (X t x) (X t x) ≤ Bx}
    {htrace : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : M,
      |traceTimeDerivMetric (I := I_hs) G.metric t x| ≤ Bv}
    {f₀ : Lp ℝ 2
      (riemannianVolumeMeasure (I := I_hs) (M := M) q)}
    {u : timeL2 (H1ComplDirichlet q) T}
    (hu : IsWeakEvolutionSolution hG hT hreg X a Bx Bv
      hX htrace f₀ u)
    (α : M) {Ω : Set EuStd}
    (hΩs : Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    {φ : ℝ × EuStd → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφi : tsupport φ ⊆ univ ×ˢ Ω)
    (hφT : ∀ y, φ (T, y) = 0) :
    let e := toEuclidean (E := EuN)
    let x := fun z : EuStd => (extChartAt I_hs α).symm (e.symm z)
    let ρ := fun t z => chartDensityOnE (I := I_hs) (G.metric t) α (e.symm z)
    let A := fun t i j z => chartInvGramOnE (I := I_hs) (G.metric t) α i j (e.symm z)
    let B := fun t i z => chartCoeffOnE (I := I_hs) α (X t) i (e.symm z)
    (∫ t, ∫ z in Ω, ρ t z *
      (H1ComplDirichletToLp q (u t) (x z) * fderiv ℝ φ (t, z) (1, 0)) ∂volume ∂timeMeasure T) +
    (∫ t, (∫ z in Ω, ρ t z *
        ((1 / 2 : ℝ) * traceTimeDerivMetric (I := I_hs) G.metric t (x z) *
          (H1ComplDirichletToLp q (u t) (x z) * φ (t, z)))) +
      ∫ z in Ω, ρ t z * H1ComplDirichletToLp q (u t) (x z) *
        ((∑ i : Fin (Module.finrank ℝ EuN),
          fderiv ℝ (fun z' : EuStd =>
            (∑ j : Fin (Module.finrank ℝ EuN), A t i j z' *
              fderiv ℝ (fun y => φ (t, y)) z' (EuclideanSpace.single j 1)) * ρ t z') z
              (EuclideanSpace.single i 1)) / ρ t z -
          (∑ i : Fin (Module.finrank ℝ EuN), B t i z *
            fderiv ℝ (fun y => φ (t, y)) z (EuclideanSpace.single i 1)) -
          localDivergence (I := I_hs) (G.metric t) α (X t) (x z) * φ (t, z) - a t * φ (t, z))
      ∂volume ∂timeMeasure T) =
      -(∫ z in Ω, ρ 0 z * (f₀ (x z) * φ (0, z))) := by
  intro e x ρ A B
  let S := e '' interior (extChartAt I_hs α).target
  have hS : IsOpen S := e.toHomeomorph.isOpenMap _ isOpen_interior
  have hs {ψ : ℝ × EuStd → ℝ} (hψ : tsupport ψ ⊆ tsupport φ) (t : ℝ) :
      tsupport (fun z => ψ (t, z)) ⊆ Ω := by
    have h := tsupport_comp_subset_preimage ψ (f := fun z : EuStd => (t, z))
      (continuous_const.prodMk continuous_id)
    exact h.trans fun z hz => (hφi (hψ hz)).2
  have hm (ψ : EuStd → ℝ) (hψ : tsupport ψ ⊆ Ω) (t : ℝ) (F c : EuStd → ℝ) :
      (∫ z in S, ρ t z * (c z * (F z * ψ z))) =
        ∫ z in Ω, ρ t z * (c z * (F z * ψ z)) := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hS.measurableSet hΩs
    intro z hz
    rw [image_eq_zero_of_notMem_tsupport (fun h => hz.2 (hψ h))]
    ring
  have hm₀ (ψ : EuStd → ℝ) (hψ : tsupport ψ ⊆ Ω) (t : ℝ) (F : EuStd → ℝ) :
      (∫ z in S, ρ t z * (F z * ψ z)) = ∫ z in Ω, ρ t z * (F z * ψ z) := by
    simpa only [one_mul] using hm ψ hψ t F (fun _ => 1)
  have h := hu.integral_euclidean_test hXcont hacont α hφ hφc
    (hφi.trans (Set.prod_mono Subset.rfl hΩs)) hφT
  refine (congrArg₂ (fun a b : ℝ => a + b) ?_ ?_).trans
    (h.trans (congrArg Neg.neg ?_))
  · apply integral_congr_ae
    filter_upwards [] with t
    exact (hm₀ (fun z => fderiv ℝ φ (t, z) (1, 0))
      (hs (tsupport_fderiv_apply_subset ℝ (1, 0)) t) t
      (fun z => H1ComplDirichletToLp q (u t) (x z))).symm
  · apply integral_congr_ae
    filter_upwards [] with t
    apply congrArg₂ (fun a b : ℝ => a + b)
    · exact (hm (fun z => φ (t, z)) (hs Subset.rfl t) t
        (fun z => H1ComplDirichletToLp q (u t) (x z))
        (fun z => (1 / 2 : ℝ) * traceTimeDerivMetric (I := I_hs) G.metric t (x z))).symm
    · exact (Sobolev.Euclidean.integral_adjoint_eq_integral_of_tsupport_subset hS.measurableSet hΩs (hs Subset.rfl t)
        (fun z => H1ComplDirichletToLp q (u t) (x z)) (ρ t)
        (fun z => localDivergence (I := I_hs) (G.metric t) α (X t) (x z))
        (fun _ => a t) (A t) (B t)).symm
  · exact hm₀ (fun z => φ (0, z)) (hs Subset.rfl 0) 0 (fun z => f₀ (x z))

theorem IsWeakEvolutionSolution.integral_local_test
    {q : SmoothRiemannianMetric I_hs M}
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I_hs) (M := M) D}
    {hG : MetricFamilySmoothOn (I := I_hs) (M := M) D G.metric}
    {T : ℝ} {hT : 0 ≤ T} {hreg : Icc (0 : ℝ) T ⊆ D.regular}
    {X : ℝ → Cₛ^∞⟮I_hs; EuclideanSpace ℝ (Fin n),
      (TangentSpace I_hs : M → Type _)⟯}
    (hXcont : ContinuousOn
      (fun p : ℝ × M ↦
        (TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p.2 (X p.1 p.2) :
          TangentBundle I_hs M))
      (Icc (0 : ℝ) T ×ˢ (Set.univ : Set M)))
    {a : ℝ → ℝ} (hacont : ContinuousOn a (Icc (0 : ℝ) T))
    {Bx Bv : ℝ}
    {hX : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : M,
      (G.metric t).inner x (X t x) (X t x) ≤ Bx}
    {htrace : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : M,
      |traceTimeDerivMetric (I := I_hs) G.metric t x| ≤ Bv}
    {f₀ : Lp ℝ 2
      (riemannianVolumeMeasure (I := I_hs) (M := M) q)}
    {u : timeL2 (H1ComplDirichlet q) T}
    (hu : IsWeakEvolutionSolution hG hT hreg X a Bx Bv
      hX htrace f₀ u)
    (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    {φ : ℝ × EuStd → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφi : tsupport φ ⊆ univ ×ˢ Ω)
    (hφT : ∀ y, φ (T, y) = 0) :
    let e := toEuclidean (E := EuN)
    let x := fun z : EuStd => (extChartAt I_hs α).symm (e.symm z)
    let ρ := fun t z => chartDensityOnE (I := I_hs) (G.metric t) α (e.symm z)
    let A := fun t i j z => chartInvGramOnE (I := I_hs) (G.metric t) α i j (e.symm z)
    let B := fun t i z => chartCoeffOnE (I := I_hs) α (X t) i (e.symm z)
    let U := dirichletLocalSpacetimeLp q α hΩ.measurableSet hΩc
      (hΩs.trans (image_mono interior_subset)) (timeMeasure T) u
    let DU := fun i => dirichletLocalSpacetimeWeakPartialLp q α hΩ hΩc hΩs (timeMeasure T) i u
    (∫ t, ∫ z in Ω, ρ t z * (U (t, z) * fderiv ℝ φ (t, z) (1, 0)) ∂volume ∂timeMeasure T) +
    (∫ t, (∫ z in Ω, ρ t z *
        ((1 / 2 : ℝ) * traceTimeDerivMetric (I := I_hs) G.metric t (x z) *
          (U (t, z) * φ (t, z)))) -
      (∑ i : Fin (Module.finrank ℝ EuN), ∫ z in Ω, DU i (t, z) *
        ((∑ j : Fin (Module.finrank ℝ EuN), A t i j z *
          fderiv ℝ (fun y => φ (t, y)) z (EuclideanSpace.single j 1)) * ρ t z -
            B t i z * ρ t z * φ (t, z))) -
      (∫ z in Ω, ρ t z * U (t, z) * (a t * φ (t, z))) ∂timeMeasure T) =
      -(∫ z in Ω, ρ 0 z * (f₀ (x z) * φ (0, z))) := by
  intro e x ρ A B U DU
  have hs (t : ℝ) : tsupport (fun z => φ (t, z)) ⊆ Ω := by
    have h := tsupport_comp_subset_preimage φ (f := fun z : EuStd => (t, z))
      (continuous_const.prodMk continuous_id)
    exact h.trans fun z hz => (hφi hz).2
  have hsc (t : ℝ) : HasCompactSupport (fun z => φ (t, z)) :=
    hΩc.of_isClosed_subset (isClosed_tsupport _) ((hs t).trans subset_closure)
  have hss (t : ℝ) : ContDiff ℝ ∞ (fun z => φ (t, z)) :=
    hφ.comp (contDiff_const.prodMk contDiff_id)
  have h := hu.integral_local_adjoint_test hXcont hacont α
    (subset_closure.trans hΩs) hφ hφc hφi hφT
  have hv := dirichletLocalSpacetimeLp_coeFn q α hΩ.measurableSet hΩc
    (hΩs.trans (image_mono interior_subset)) (timeMeasure T) u
  have hD : ∀ᵐ t ∂timeMeasure T, ∀ i : Fin (Module.finrank ℝ EuN),
      (fun z => DU i (t, z)) =ᵐ[volume.restrict Ω]
        (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (u t) : EuStd → ℝ) :=
    ae_all_iff.mpr (fun i => dirichletLocalSpacetimeWeakPartialLp_coeFn q α hΩ hΩc hΩs
      (timeMeasure T) i u)
  refine (congrArg₂ (fun a b : ℝ => a + b) ?_ ?_).trans h
  · apply integral_congr_ae
    filter_upwards [hv] with t ht
    apply integral_congr_ae
    filter_upwards [ht] with z hz
    rw [hz]
  · apply integral_congr_ae
    filter_upwards [hv, hD] with t ht htD
    rw [integral_chart_adjoint_sub_potential_eq_neg_sum_integral q (G.metric t) α
      hΩ hΩc hΩs (X t) (u t) continuousOn_const (hss t) (hsc t) (hs t)]
    have hm :
        (∫ z in Ω, ρ t z *
          ((1 / 2 : ℝ) * traceTimeDerivMetric (I := I_hs) G.metric t (x z) *
            (U (t, z) * φ (t, z)))) =
        ∫ z in Ω, ρ t z *
          ((1 / 2 : ℝ) * traceTimeDerivMetric (I := I_hs) G.metric t (x z) *
            (H1ComplDirichletToLp q (u t) (x z) * φ (t, z))) := by
      apply integral_congr_ae
      filter_upwards [ht] with z hz
      rw [hz]
    have hp : (∫ z in Ω, ρ t z * U (t, z) * (a t * φ (t, z))) =
        ∫ z in Ω, ρ t z * H1ComplDirichletToLp q (u t) (x z) * (a t * φ (t, z)) := by
      apply integral_congr_ae
      filter_upwards [ht] with z hz
      rw [hz]
    have hflux :
        (∑ i : Fin (Module.finrank ℝ EuN), ∫ z in Ω, DU i (t, z) *
          ((∑ j : Fin (Module.finrank ℝ EuN), A t i j z *
            fderiv ℝ (fun y => φ (t, y)) z (EuclideanSpace.single j 1)) * ρ t z -
              B t i z * ρ t z * φ (t, z))) =
        ∑ i : Fin (Module.finrank ℝ EuN), ∫ z in Ω,
          dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (u t) z *
            ((∑ j : Fin (Module.finrank ℝ EuN), A t i j z *
              fderiv ℝ (fun y => φ (t, y)) z (EuclideanSpace.single j 1)) * ρ t z -
                B t i z * ρ t z * φ (t, z)) := by
      apply Finset.sum_congr rfl
      intro i _
      apply integral_congr_ae
      filter_upwards [htD i] with z hz
      rw [hz]
    rw [hm, hp, hflux]
    ring

end DifferentialGeometry.Analysis.Parabolic.Dirichlet
