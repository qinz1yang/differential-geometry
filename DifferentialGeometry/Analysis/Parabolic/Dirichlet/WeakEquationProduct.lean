import DifferentialGeometry.Analysis.Parabolic.Dirichlet.WeakEquationLocal
import DifferentialGeometry.Analysis.Parabolic.Dirichlet.LocalCoefficients
import Mathlib.MeasureTheory.Function.LpSeminorm.Prod
import DifferentialGeometry.Analysis.Integration.Integral.Prod

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

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "I_hs" => modelWithCornersEuclideanHalfSpace n
local notation "EuN" => EuclideanSpace ℝ (Fin n)
local notation "EuStd" => EuclideanSpace ℝ (Fin (Module.finrank ℝ EuN))

private local instance : MeasurableSpace EuStd :=
  WithLp.measurableSpace 2 ((i : Fin (Module.finrank ℝ EuN)) → ℝ)

open DifferentialGeometry.Analysis.Laplacian.MetricExtension

omit [T2Space M] [CompactSpace M] in
private theorem local_spacetime_weak_form_terms_memLp
    {D : RealTimeInterval} {G : MetricConnectionFamilyOn (I := I_hs) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I_hs) (M := M) D G.metric)
    {T : ℝ} (hreg : Icc (0 : ℝ) T ⊆ D.regular)
    (X : ℝ → Cₛ^∞⟮I_hs; EuN, (TangentSpace I_hs : M → Type _)⟯)
    (α : M)
    (hX : ContinuousOn (fun p : ℝ × M => TotalSpace.mk' EuN p.2 (X p.1 p.2))
      (Icc (0 : ℝ) T ×ˢ (trivializationAt EuN (TangentSpace I_hs) α).baseSet))
    {a : ℝ → ℝ} (ha : ContinuousOn a (Icc (0 : ℝ) T))
    {Ω : Set EuStd} (hΩ : MeasurableSet Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ chartTargetEuclid (I := I_hs) α)
    (φ : ℝ × EuStd → ℝ) (hφ : ContDiff ℝ 1 φ)
    (U : Lp ℝ 2 ((timeMeasure T).prod (volume.restrict Ω)))
    (DU : Fin (Module.finrank ℝ EuN) → Lp ℝ 2 ((timeMeasure T).prod (volume.restrict Ω))) :
    let e := toEuclidean (E := EuN)
    let x := fun z : EuStd => (extChartAt I_hs α).symm (e.symm z)
    let ρ := fun t z => chartDensityOnE (I := I_hs) (G.metric t) α (e.symm z)
    let A := fun t i j z => chartInvGramOnE (I := I_hs) (G.metric t) α i j (e.symm z)
    let B := fun t i z => chartCoeffOnE (I := I_hs) α (X t) i (e.symm z)
    let μ := (timeMeasure T).prod (volume.restrict Ω)
    MemLp (fun p => ρ p.1 p.2 * (U p * φ p)) 2 μ ∧
    MemLp (fun p => ρ p.1 p.2 * (U p * fderiv ℝ φ p (1, 0))) 2 μ ∧
    MemLp (fun p => ρ p.1 p.2 * ((1 / 2 : ℝ) *
      traceTimeDerivMetric (I := I_hs) G.metric p.1 (x p.2) * (U p * φ p))) 2 μ ∧
    (∀ i, MemLp (fun p => DU i p *
      ((∑ j : Fin (Module.finrank ℝ EuN), A p.1 i j p.2 *
        fderiv ℝ (fun z => φ (p.1, z)) p.2 (EuclideanSpace.single j 1)) * ρ p.1 p.2 -
        B p.1 i p.2 * ρ p.1 p.2 * φ p)) 2 μ) ∧
    MemLp (fun p => ρ p.1 p.2 * U p * (a p.1 * φ p)) 2 μ := by
  intro e x ρ A B μ
  have hρ : MemLp (fun p : ℝ × EuStd => ρ p.1 p.2) ∞ μ := by
    have h := densityOnEuclid_family_memLp_top hG isCompact_Icc hreg α
      hΩ hΩc hΩs ((volume : Measure ℝ).prod (volume : Measure EuStd))
    simp only [← MeasureTheory.Measure.prod_restrict] at h
    exact h
  have hA (i j : Fin (Module.finrank ℝ EuN)) :
      MemLp (fun p : ℝ × EuStd => A p.1 i j p.2) ∞ μ := by
    have h := invGramOnEuclid_family_memLp_top hG isCompact_Icc hreg α
      hΩ hΩc hΩs i j ((volume : Measure ℝ).prod (volume : Measure EuStd))
    simp only [← MeasureTheory.Measure.prod_restrict] at h
    exact h
  have hB (i : Fin (Module.finrank ℝ EuN)) :
      MemLp (fun p : ℝ × EuStd => B p.1 i p.2) ∞ μ := by
    have h := chartCoeffOnE_comp_toEuclidean_symm_family_memLp_top X isCompact_Icc
      measurableSet_Icc α hX
      hΩ hΩc hΩs i ((volume : Measure ℝ).prod (volume : Measure EuStd))
    simp only [← MeasureTheory.Measure.prod_restrict] at h
    exact h
  have hτ : MemLp (fun p : ℝ × EuStd =>
      traceTimeDerivMetric (I := I_hs) G.metric p.1 (x p.2)) ∞ μ := by
    have h := traceTimeDerivMetric_comp_chartInverse_memLp_top hG isCompact_Icc hreg α
      hΩ hΩc hΩs ((volume : Measure ℝ).prod (volume : Measure EuStd))
    simp only [← MeasureTheory.Measure.prod_restrict] at h
    exact h
  have hlift (f : ℝ × EuStd → ℝ)
      (hf : ContinuousOn f (Icc (0 : ℝ) T ×ˢ closure Ω)) : MemLp f ∞ μ := by
    have h := hf.memLp_top_of_subset_isCompact (isCompact_Icc.prod hΩc)
      (measurableSet_Icc.prod hΩ) (Set.prod_mono Subset.rfl subset_closure)
      (μ := (volume : Measure ℝ).prod (volume : Measure EuStd))
    simpa only [μ, timeMeasure, ← MeasureTheory.Measure.prod_restrict] using h
  have hφp := hlift φ hφ.continuous.continuousOn
  have hφt := hlift (fun p => fderiv ℝ φ p (1, 0))
    (((hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const).continuousOn)
  have hφd (j : Fin (Module.finrank ℝ EuN)) : MemLp
      (fun p : ℝ × EuStd => fderiv ℝ (fun z => φ (p.1, z)) p.2
        (EuclideanSpace.single j 1)) ∞ μ := by
    apply hlift
    have hf : ContDiff ℝ 1 (fun p : (ℝ × EuStd) × EuStd => φ (p.1.1, p.2)) :=
      hφ.comp (contDiff_fst.fst.prodMk contDiff_snd)
    have hd : ContDiff ℝ 0
        (fun p : ℝ × EuStd => fderiv ℝ (fun z => φ (p.1, z)) p.2) :=
      hf.fderiv contDiff_snd (by norm_num)
    exact (hd.continuous.clm_apply continuous_const).continuousOn
  have hap : MemLp (fun p : ℝ × EuStd => a p.1) ∞ μ :=
    hlift _ (ha.comp continuous_fst.continuousOn (fun _ hp => hp.1))
  have hUφ : MemLp (fun p : ℝ × EuStd => U p * φ p) 2 μ :=
    MemLp.mul' (p := 2) (q := ∞) (r := 2) hφp (Lp.memLp U)
  have hUφt : MemLp (fun p : ℝ × EuStd => U p * fderiv ℝ φ p (1, 0)) 2 μ :=
    MemLp.mul' (p := 2) (q := ∞) (r := 2) hφt (Lp.memLp U)
  refine ⟨MemLp.mul' (r := 2) hUφ hρ, MemLp.mul' (r := 2) hUφt hρ, ?_, ?_, ?_⟩
  · exact MemLp.mul' (r := 2) (MemLp.mul' (r := 2) hUφ (hτ.const_mul (1 / 2 : ℝ))) hρ
  · intro i
    have hsum : MemLp (fun p : ℝ × EuStd =>
        ∑ j : Fin (Module.finrank ℝ EuN),
          A p.1 i j p.2 * fderiv ℝ (fun z => φ (p.1, z)) p.2 (EuclideanSpace.single j 1)) ∞ μ := by
      exact memLp_finsetSum Finset.univ fun j _ =>
        MemLp.mul' (p := ∞) (q := ∞) (r := ∞) (hφd j) (hA i j)
    have hf : MemLp (fun p : ℝ × EuStd =>
        (∑ j : Fin (Module.finrank ℝ EuN),
          A p.1 i j p.2 * fderiv ℝ (fun z => φ (p.1, z)) p.2 (EuclideanSpace.single j 1)) * ρ p.1 p.2 -
          B p.1 i p.2 * ρ p.1 p.2 * φ p) ∞ μ :=
      (MemLp.mul' (r := ∞) hρ hsum).sub
        (MemLp.mul' (r := ∞) hφp (MemLp.mul' (r := ∞) hρ (hB i)))
    exact MemLp.mul' (p := 2) (q := ∞) (r := 2) hf (Lp.memLp (DU i))
  · exact MemLp.mul' (p := 2) (q := ∞) (r := 2)
      (MemLp.mul' (r := ∞) hφp hap) (MemLp.mul' (r := 2) (Lp.memLp U) hρ)

theorem IsWeakEvolutionSolution.integral_product_test
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
    (α : M)
    (hXcont : ContinuousOn (fun p : ℝ × M => TotalSpace.mk' EuN p.2 (X p.1 p.2))
      (Icc (0 : ℝ) T ×ˢ (trivializationAt EuN (TangentSpace I_hs) α).baseSet))
    (hacont : ContinuousOn a (Icc (0 : ℝ) T))
    {Ω : Set EuStd}
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
    -(∫ p, _root_.deriv η p.1 * (ρ p.1 p.2 * (U p * ψ p.2))
      ∂((timeMeasure T).prod (volume.restrict Ω))) -
      η 0 * (∫ z in Ω, ρ 0 z * (f₀ (x z) * ψ z)) =
    ∫ p, η p.1 * (ρ p.1 p.2 *
        ((1 / 2 : ℝ) * traceTimeDerivMetric (I := I_hs) G.metric p.1 (x p.2) *
          (U p * ψ p.2)) -
      (∑ i : Fin (Module.finrank ℝ EuN), DU i p *
        ((∑ j : Fin (Module.finrank ℝ EuN), A p.1 i j p.2 *
          fderiv ℝ ψ p.2 (EuclideanSpace.single j 1)) * ρ p.1 p.2 -
          B p.1 i p.2 * ρ p.1 p.2 * ψ p.2)) -
      ρ p.1 p.2 * U p * (a p.1 * ψ p.2))
      ∂((timeMeasure T).prod (volume.restrict Ω)) := by
  intro e x ρ A B U DU
  let μ := timeMeasure T
  let ν := (volume : Measure EuStd).restrict Ω
  let : IsFiniteMeasure ν := by
    refine ⟨?_⟩
    change (volume.restrict Ω : Measure EuStd) univ < ⊤
    rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ, univ_inter]
    exact (measure_mono subset_closure).trans_lt hΩc.measure_lt_top
  let Q := fun p : ℝ × EuStd => ρ p.1 p.2 * (U p * ψ p.2)
  let F₁ := fun p : ℝ × EuStd => ρ p.1 p.2 *
    ((1 / 2 : ℝ) * traceTimeDerivMetric (I := I_hs) G.metric p.1 (x p.2) * (U p * ψ p.2))
  let F₂ := fun i (p : ℝ × EuStd) => DU i p *
    ((∑ j : Fin (Module.finrank ℝ EuN), A p.1 i j p.2 *
      fderiv ℝ ψ p.2 (EuclideanSpace.single j 1)) * ρ p.1 p.2 -
      B p.1 i p.2 * ρ p.1 p.2 * ψ p.2)
  let F₃ := fun p : ℝ × EuStd => ρ p.1 p.2 * U p * (a p.1 * ψ p.2)
  let R := fun p => F₁ p - (∑ i, F₂ i p) - F₃ p
  let I₀ := ∫ z in Ω, ρ 0 z * (f₀ (x z) * ψ z)
  change -(∫ p, _root_.deriv η p.1 * Q p ∂μ.prod ν) - η 0 * I₀ =
    ∫ p, η p.1 * R p ∂μ.prod ν
  obtain ⟨hQ, _, h₁, h₂, h₃⟩ := local_spacetime_weak_form_terms_memLp hG hreg X α hXcont hacont
    hΩ.measurableSet hΩc (hΩs.trans (image_mono interior_subset)) (fun p => ψ p.2)
    ((hψ_smooth.of_le (by simp)).comp contDiff_snd) U DU
  have hF₁ : Integrable F₁ (μ.prod ν) := h₁.integrable (by norm_num)
  have hF₂ : ∀ i, Integrable (F₂ i) (μ.prod ν) := fun i => (h₂ i).integrable (by norm_num)
  have hF₃ : Integrable F₃ (μ.prod ν) := h₃.integrable (by norm_num)
  have hsum : Integrable (fun p => ∑ i, F₂ i p) (μ.prod ν) :=
    integrable_finsetSum Finset.univ fun i _ => hF₂ i
  have hR : Integrable R (μ.prod ν) := (hF₁.sub hsum).sub hF₃
  have hηp : MemLp (fun p : ℝ × EuStd => η p.1) ∞ (μ.prod ν) := by
    have h : MemLp η ∞ μ :=
      hη.continuousOn.memLp_top_of_isCompact isCompact_Icc measurableSet_Icc
    exact h.comp_fst ν
  have hηd : MemLp (_root_.deriv η) 2 μ :=
    MemLp.ae_eq (timeH1.deriv_ofContDiffOn hT η hη)
      (Lp.memLp (timeH1.ofContDiffOn hT η hη).deriv)
  have hmass : Integrable (fun p : ℝ × EuStd => _root_.deriv η p.1 * Q p) (μ.prod ν) :=
    (hηd.comp_fst ν).integrable_mul hQ
  have hrhs : Integrable (fun p : ℝ × EuStd => η p.1 * R p) (μ.prod ν) :=
    hR.mul_of_top_right hηp
  have hm : (∫ p, _root_.deriv η p.1 * Q p ∂μ.prod ν) =
      ∫ t, _root_.deriv η t * (∫ z, Q (t, z) ∂ν) ∂μ := by
    rw [integral_prod _ hmass]
    simp only [integral_const_mul]
  have h₂ae : ∀ᵐ t ∂μ, ∀ i, Integrable (fun z => F₂ i (t, z)) ν :=
    ae_all_iff.mpr fun i => (hF₂ i).prod_right_ae
  have hr : (∫ p, η p.1 * R p ∂μ.prod ν) =
      ∫ t, η t * ((∫ z, F₁ (t, z) ∂ν) - (∑ i, ∫ z, F₂ i (t, z) ∂ν) -
        ∫ z, F₃ (t, z) ∂ν) ∂μ := by
    rw [integral_prod _ hrhs]
    apply integral_congr_ae
    filter_upwards [hF₁.prod_right_ae, h₂ae, hF₃.prod_right_ae] with t ht₁ ht₂ ht₃
    rw [integral_const_mul]
    congr 1
    have hs : Integrable (fun z => ∑ i, F₂ i (t, z)) ν :=
      integrable_finsetSum Finset.univ fun i _ => ht₂ i
    change (∫ z, F₁ (t, z) - (∑ i, F₂ i (t, z)) - F₃ (t, z) ∂ν) = _
    have hsub : Integrable (fun z => F₁ (t, z) - (∑ i, F₂ i (t, z))) ν := ht₁.sub hs
    rw [integral_sub hsub ht₃, integral_sub ht₁ hs,
      integral_finsetSum Finset.univ (fun i _ => ht₂ i)]
  have ht := hu.integral_time_test α hΩ hΩc hΩs ψ hψ_smooth hψ_cpt hψ_supp hη hηT
  change -(∫ t, _root_.deriv η t * (∫ z, Q (t, z) ∂ν) ∂μ) - η 0 * I₀ =
    ∫ t, η t * ((∫ z, F₁ (t, z) ∂ν) - (∑ i, ∫ z, F₂ i (t, z) ∂ν) -
      ∫ z, F₃ (t, z) ∂ν) ∂μ at ht
  rw [hm, hr]
  exact ht

theorem IsWeakEvolutionSolution.integral_spacetime_test
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
    (∫ p, ρ p.1 p.2 * (U p * fderiv ℝ φ p (1, 0)) +
      (ρ p.1 p.2 * ((1 / 2 : ℝ) * traceTimeDerivMetric (I := I_hs) G.metric p.1 (x p.2) *
          (U p * φ p)) -
        (∑ i : Fin (Module.finrank ℝ EuN), DU i p *
          ((∑ j : Fin (Module.finrank ℝ EuN), A p.1 i j p.2 *
            fderiv ℝ (fun y => φ (p.1, y)) p.2 (EuclideanSpace.single j 1)) * ρ p.1 p.2 -
              B p.1 i p.2 * ρ p.1 p.2 * φ p)) -
        ρ p.1 p.2 * U p * (a p.1 * φ p))
      ∂((timeMeasure T).prod (volume.restrict Ω))) =
      -(∫ z in Ω, ρ 0 z * (f₀ (x z) * φ (0, z))) := by
  intro e x ρ A B U DU
  let μ := timeMeasure T
  let ν := (volume : Measure EuStd).restrict Ω
  let : IsFiniteMeasure ν := by
    refine ⟨?_⟩
    change (volume.restrict Ω : Measure EuStd) univ < ⊤
    rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ, univ_inter]
    exact (measure_mono subset_closure).trans_lt hΩc.measure_lt_top
  let F₀ := fun p : ℝ × EuStd => ρ p.1 p.2 * (U p * fderiv ℝ φ p (1, 0))
  let F₁ := fun p : ℝ × EuStd => ρ p.1 p.2 *
    ((1 / 2 : ℝ) * traceTimeDerivMetric (I := I_hs) G.metric p.1 (x p.2) * (U p * φ p))
  let F₂ := fun i (p : ℝ × EuStd) => DU i p *
    ((∑ j : Fin (Module.finrank ℝ EuN), A p.1 i j p.2 *
      fderiv ℝ (fun y => φ (p.1, y)) p.2 (EuclideanSpace.single j 1)) * ρ p.1 p.2 -
      B p.1 i p.2 * ρ p.1 p.2 * φ p)
  let F₃ := fun p : ℝ × EuStd => ρ p.1 p.2 * U p * (a p.1 * φ p)
  let R := fun p => F₁ p - (∑ i, F₂ i p) - F₃ p
  change (∫ p, F₀ p + R p ∂μ.prod ν) = _
  obtain ⟨_, h₀, h₁, h₂, h₃⟩ := local_spacetime_weak_form_terms_memLp hG hreg X α
    (hXcont.mono (Set.prod_mono Subset.rfl (subset_univ _))) hacont
    hΩ.measurableSet hΩc (hΩs.trans (image_mono interior_subset)) φ
    (hφ.of_le (by simp)) U DU
  have hF₀ : Integrable F₀ (μ.prod ν) := h₀.integrable (by norm_num)
  have hF₁ : Integrable F₁ (μ.prod ν) := h₁.integrable (by norm_num)
  have hF₂ : ∀ i, Integrable (F₂ i) (μ.prod ν) := fun i => (h₂ i).integrable (by norm_num)
  have hF₃ : Integrable F₃ (μ.prod ν) := h₃.integrable (by norm_num)
  have hsum : Integrable (fun p => ∑ i, F₂ i p) (μ.prod ν) :=
    integrable_finsetSum Finset.univ fun i _ => hF₂ i
  have hR : Integrable R (μ.prod ν) := (hF₁.sub hsum).sub hF₃
  have h₂ae : ∀ᵐ t ∂μ, ∀ i, Integrable (fun z => F₂ i (t, z)) ν :=
    ae_all_iff.mpr fun i => (hF₂ i).prod_right_ae
  have hr : (∫ p, R p ∂μ.prod ν) =
      ∫ t, (∫ z, F₁ (t, z) ∂ν) - (∑ i, ∫ z, F₂ i (t, z) ∂ν) -
        (∫ z, F₃ (t, z) ∂ν) ∂μ := by
    rw [integral_prod _ hR]
    apply integral_congr_ae
    filter_upwards [hF₁.prod_right_ae, h₂ae, hF₃.prod_right_ae] with t ht₁ ht₂ ht₃
    have hs : Integrable (fun z => ∑ i, F₂ i (t, z)) ν :=
      integrable_finsetSum Finset.univ fun i _ => ht₂ i
    change (∫ z, F₁ (t, z) - (∑ i, F₂ i (t, z)) - F₃ (t, z) ∂ν) = _
    have hsub : Integrable (fun z => F₁ (t, z) - (∑ i, F₂ i (t, z))) ν := ht₁.sub hs
    rw [integral_sub hsub ht₃, integral_sub ht₁ hs,
      integral_finsetSum Finset.univ (fun i _ => ht₂ i)]
  rw [integral_add hF₀ hR, integral_prod _ hF₀, hr]
  exact hu.integral_local_test hXcont hacont α hΩ hΩc hΩs hφ hφc hφi hφT

private theorem fderiv_spatial_slice_apply
    {d : ℕ} {φ : ℝ × EuclideanSpace ℝ (Fin d) → ℝ}
    (hφ : Differentiable ℝ φ) (t : ℝ) (x v : EuclideanSpace ℝ (Fin d)) :
    fderiv ℝ (fun y => φ (t, y)) x v = fderiv ℝ φ (t, x) (0, v) := by
  have h := (hφ (t, x)).hasFDerivAt.comp x
    ((hasFDerivAt_const t x).prodMk (hasFDerivAt_id x))
  exact congrArg (fun L => L v) h.fderiv


theorem IsWeakEvolutionSolution.integral_spacetime_test_interior
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
    {Ω₀ : Set EuStd} (hΩ₀ : MeasurableSet Ω₀) (hΩ₀Ω : Ω₀ ⊆ Ω)
    {t₀ t₁ : ℝ} (ht₀ : 0 < t₀) (ht₁ : t₁ < T)
    (hφi : tsupport φ ⊆ Ioo t₀ t₁ ×ˢ Ω₀) :
    let e := toEuclidean (E := EuN)
    let x := fun z : EuStd => (extChartAt I_hs α).symm (e.symm z)
    let ρ := fun t z => chartDensityOnE (I := I_hs) (G.metric t) α (e.symm z)
    let A := fun t i j z => chartInvGramOnE (I := I_hs) (G.metric t) α i j (e.symm z)
    let B := fun t i z => chartCoeffOnE (I := I_hs) α (X t) i (e.symm z)
    let U := dirichletLocalSpacetimeLp q α hΩ.measurableSet hΩc
      (hΩs.trans (image_mono interior_subset)) (timeMeasure T) u
    let DU := fun i => dirichletLocalSpacetimeWeakPartialLp q α hΩ hΩc hΩs (timeMeasure T) i u
    (∫ p, ρ p.1 p.2 * (U p * fderiv ℝ φ p (1, 0)) +
      (ρ p.1 p.2 * ((1 / 2 : ℝ) * traceTimeDerivMetric (I := I_hs) G.metric p.1 (x p.2) *
          (U p * φ p)) -
        (∑ i : Fin (Module.finrank ℝ EuN), DU i p *
          ((∑ j : Fin (Module.finrank ℝ EuN), A p.1 i j p.2 *
            fderiv ℝ (fun y => φ (p.1, y)) p.2 (EuclideanSpace.single j 1)) * ρ p.1 p.2 -
              B p.1 i p.2 * ρ p.1 p.2 * φ p)) -
        ρ p.1 p.2 * U p * (a p.1 * φ p))
      ∂(((timeMeasure T).restrict (Icc t₀ t₁)).prod (volume.restrict Ω₀))) = 0 := by
  intro e x ρ A B U DU
  have hφouter : tsupport φ ⊆ univ ×ˢ Ω :=
    hφi.trans (Set.prod_mono (subset_univ _) hΩ₀Ω)
  have hφ0 (z) : φ (0, z) = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro h
    exact (not_lt_of_ge ht₀.le) (hφi h).1.1
  have hφT (z) : φ (T, z) = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro h
    exact (not_lt_of_ge ht₁.le) (hφi h).1.2
  have hw := hu.integral_spacetime_test hXcont hacont α hΩ hΩc hΩs hφ hφc hφouter hφT
  simp only [hφ0, mul_zero, integral_zero, neg_zero] at hw
  let f := fun p : ℝ × EuStd => ρ p.1 p.2 * (U p * fderiv ℝ φ p (1, 0)) +
      (ρ p.1 p.2 * ((1 / 2 : ℝ) * traceTimeDerivMetric (I := I_hs) G.metric p.1 (x p.2) *
          (U p * φ p)) -
        (∑ i : Fin (Module.finrank ℝ EuN), DU i p *
          ((∑ j : Fin (Module.finrank ℝ EuN), A p.1 i j p.2 *
            fderiv ℝ (fun y => φ (p.1, y)) p.2 (EuclideanSpace.single j 1)) * ρ p.1 p.2 -
              B p.1 i p.2 * ρ p.1 p.2 * φ p)) -
        ρ p.1 p.2 * U p * (a p.1 * φ p))
  have hf : ∀ p, p ∉ Icc t₀ t₁ ×ˢ Ω₀ → f p = 0 := by
    intro p hp
    have hz : p ∉ tsupport φ := fun h => hp ⟨⟨(hφi h).1.1.le, (hφi h).1.2.le⟩, (hφi h).2⟩
    have hφz : φ p = 0 := image_eq_zero_of_notMem_tsupport hz
    have hdz (v : ℝ × EuStd) : fderiv ℝ φ p v = 0 :=
      image_eq_zero_of_notMem_tsupport (f := fun q => fderiv ℝ φ q v)
        (fun h => hz (tsupport_fderiv_apply_subset ℝ v h))
    dsimp only [f]
    simp only [fderiv_spatial_slice_apply (hφ.differentiable (by norm_num)), hφz, hdz,
      mul_zero, zero_mul, Finset.sum_const_zero, sub_zero, add_zero]
  have hloc := integral_eq_integral_restrict_prod_of_support_subset
    (μ := timeMeasure T) (ν := volume) hΩ₀ hΩ₀Ω hf
  exact hloc.symm.trans hw


private theorem weak_form_integrand_eq
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (ρ U dtφ φ τ a : ℝ) (DU B : ι → ℝ) (A : ι → κ → ℝ) (dφ : κ → ℝ) :
    ρ * (U * dtφ) +
      (ρ * ((1 / 2 : ℝ) * τ * (U * φ)) -
        (∑ i, DU i * ((∑ j, A i j * dφ j) * ρ - B i * ρ * φ)) -
        ρ * U * (a * φ)) =
    ρ * U * dtφ + ((∑ i, ρ * B i * DU i) + ρ * ((1 / 2 : ℝ) * τ - a) * U) * φ -
      ∑ i, ∑ j, ρ * A i j * DU i * dφ j := by
  have hq : (∑ i, DU i * (∑ j, A i j * dφ j) * ρ) =
      ∑ i, ∑ j, ρ * A i j * DU i * dφ j := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hb : (∑ i, DU i * (B i * ρ * φ)) = (∑ i, ρ * B i * DU i) * φ := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  simp only [mul_sub, Finset.sum_sub_distrib]
  have hq' : (∑ i, DU i * ((∑ j, A i j * dφ j) * ρ)) =
      ∑ i, ∑ j, ρ * A i j * DU i * dφ j := by
    simpa only [mul_assoc] using hq
  rw [hq', hb]
  ring

theorem IsWeakEvolutionSolution.integral_spacetime_test_divergence
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
    {Ω₀ : Set EuStd} (hΩ₀ : MeasurableSet Ω₀) (hΩ₀Ω : Ω₀ ⊆ Ω)
    {t₀ t₁ : ℝ} (ht₀ : 0 < t₀) (ht₁ : t₁ < T)
    (hφi : tsupport φ ⊆ Ioo t₀ t₁ ×ˢ Ω₀) :
    let x := fun z : EuStd => (extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z)
    let ρ := fun (p : ℝ × EuStd) => densityOnEuclid (I := I_hs) (G.metric p.1) α p.2
    let A := fun i j (p : ℝ × EuStd) =>
      weightedInvGramOnEuclid (I := I_hs) (G.metric p.1) α i j p.2
    let B := fun i (p : ℝ × EuStd) =>
      chartCoeffOnE (I := I_hs) α (X p.1) i ((toEuclidean (E := EuN)).symm p.2)
    let U := dirichletLocalSpacetimeLp q α hΩ.measurableSet hΩc
      (hΩs.trans (image_mono interior_subset)) (timeMeasure T) u
    let V := fun i => dirichletLocalSpacetimeWeakPartialLp q α hΩ hΩc hΩs (timeMeasure T) i u
    let L := fun p => (∑ i, ρ p * B i p * V i p) +
      ρ p * ((1 / 2 : ℝ) * traceTimeDerivMetric (I := I_hs) G.metric p.1 (x p.2) - a p.1) * U p
    let ν := (((timeMeasure T).restrict (Icc t₀ t₁)).prod (volume.restrict Ω₀))
    (∫ p, ρ p * U p * fderiv ℝ φ p (1, 0) ∂ν) =
      (∑ i, ∑ j, ∫ p, A i j p * V i p *
        fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂ν) - ∫ p, L p * φ p ∂ν := by
  intro x ρ A B U V L ν
  let Q := fun i j p => A i j p * V i p * fderiv ℝ φ p (0, EuclideanSpace.single j 1)
  let f := fun p : ℝ × EuStd => ρ p * (U p * fderiv ℝ φ p (1, 0)) +
      (ρ p * ((1 / 2 : ℝ) * traceTimeDerivMetric (I := I_hs) G.metric p.1 (x p.2) *
          (U p * φ p)) -
        (∑ i : Fin (Module.finrank ℝ EuN), V i p *
          ((∑ j : Fin (Module.finrank ℝ EuN), invGramOnEuclid (I := I_hs) (G.metric p.1) α i j p.2 *
            fderiv ℝ (fun y => φ (p.1, y)) p.2 (EuclideanSpace.single j 1)) * ρ p -
              B i p * ρ p * φ p)) -
        ρ p * U p * (a p.1 * φ p))
  have hmeasure : ν ≤ (timeMeasure T).prod (volume.restrict Ω) :=
    Measure.prod_mono Measure.restrict_le_self (Measure.restrict_mono hΩ₀Ω le_rfl)
  let : IsFiniteMeasure (volume.restrict Ω₀) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply MeasurableSet.univ, univ_inter]
    exact (measure_mono (hΩ₀Ω.trans subset_closure)).trans_lt hΩc.measure_lt_top
  obtain ⟨_, h₀, h₁, h₂, h₃⟩ := local_spacetime_weak_form_terms_memLp hG hreg X α
    (hXcont.mono (Set.prod_mono Subset.rfl (subset_univ _))) hacont
    hΩ.measurableSet hΩc (hΩs.trans (image_mono interior_subset)) φ
    (hφ.of_le (by simp)) U V
  have htime : Integrable (fun p => ρ p * U p * fderiv ℝ φ p (1, 0)) ν := by
    simpa only [ρ, densityOnEuclid, chartDensityOnE, mul_assoc] using (h₀.mono_measure hmeasure).integrable (by norm_num)
  have hf : Integrable f ν :=
    ((h₀.add ((h₁.sub (memLp_finsetSum Finset.univ (fun i _ => h₂ i))).sub h₃)).mono_measure
      hmeasure).integrable (by norm_num)
  have hA (i j) : MemLp (A i j) ∞ ν := by
    have hb := weightedInvGramOnEuclid_family_memLp_top hG isCompact_Icc hreg α
      hΩ.measurableSet hΩc (hΩs.trans (image_mono interior_subset)) i j (volume.prod volume)
    rw [← Measure.prod_restrict] at hb
    exact hb.mono_measure hmeasure
  have hQ (i j) : Integrable (Q i j) ν := by
    have hd : MemLp (fun p => fderiv ℝ φ p (0, EuclideanSpace.single j 1)) ∞ ν :=
      ((hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const).memLp_top_of_hasCompactSupport
        (hφc.fderiv_apply ℝ (0, EuclideanSpace.single j 1)) ν
    exact (hd.mul (r := 2) (((Lp.memLp (V i)).mono_measure hmeasure).mul (r := 2) (hA i j))).integrable
      (by norm_num)
  have hQsum : Integrable (fun p => ∑ i, ∑ j, Q i j p) ν :=
    integrable_finsetSum Finset.univ fun i _ => integrable_finsetSum Finset.univ fun j _ => hQ i j
  have heq (p) : f p = ρ p * U p * fderiv ℝ φ p (1, 0) + L p * φ p - ∑ i, ∑ j, Q i j p := by
    dsimp only [f, L, Q, ρ, A, B, U, V, x]
    rw [weak_form_integrand_eq]
    simp only [fderiv_spatial_slice_apply (hφ.differentiable (by norm_num))]
    rfl
  have hL : Integrable (fun p => L p * φ p) ν := by
    refine ((hf.add hQsum).sub htime).congr (Filter.Eventually.of_forall fun p => ?_)
    change f p + (∑ i, ∑ j, Q i j p) - ρ p * U p * fderiv ℝ φ p (1, 0) = L p * φ p
    rw [heq]
    ring
  have hw := hu.integral_spacetime_test_interior hXcont hacont α hΩ hΩc hΩs hφ hφc
    hΩ₀ hΩ₀Ω ht₀ ht₁ hφi
  change (∫ p, f p ∂ν) = 0 at hw
  simp_rw [heq] at hw
  have htimeL : Integrable (fun p => ρ p * U p * fderiv ℝ φ p (1, 0) + L p * φ p) ν := htime.add hL
  rw [integral_sub htimeL hQsum, integral_add htime hL,
    integral_finsetSum Finset.univ (fun i _ => integrable_finsetSum Finset.univ (fun j _ => hQ i j))] at hw
  have hsum : (∑ i, ∫ p, ∑ j, Q i j p ∂ν) = ∑ i, ∑ j, ∫ p, Q i j p ∂ν := by
    apply Finset.sum_congr rfl
    intro i hi
    exact integral_finsetSum Finset.univ (fun j _ => hQ i j)
  rw [hsum] at hw
  linarith

end DifferentialGeometry.Analysis.Parabolic.Dirichlet
