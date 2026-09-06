import DifferentialGeometry.Analysis.Parabolic.Dirichlet.WeakEquationLocal
import DifferentialGeometry.Analysis.Parabolic.Dirichlet.LocalCoefficients
import Mathlib.MeasureTheory.Function.LpSeminorm.Prod
import Mathlib.MeasureTheory.Integral.Prod

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
private theorem local_weakForm_terms_memLp
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
    (ψ : EuStd → ℝ) (hψ : ContDiff ℝ 1 ψ)
    (U : Lp ℝ 2 ((timeMeasure T).prod (volume.restrict Ω)))
    (DU : Fin (Module.finrank ℝ EuN) → Lp ℝ 2 ((timeMeasure T).prod (volume.restrict Ω))) :
    let e := toEuclidean (E := EuN)
    let x := fun z : EuStd => (extChartAt I_hs α).symm (e.symm z)
    let ρ := fun t z => chartDensityOnE (I := I_hs) (G.metric t) α (e.symm z)
    let A := fun t i j z => chartInvGramOnE (I := I_hs) (G.metric t) α i j (e.symm z)
    let B := fun t i z => chartCoeffOnE (I := I_hs) α (X t) i (e.symm z)
    let μ := (timeMeasure T).prod (volume.restrict Ω)
    MemLp (fun p => ρ p.1 p.2 * (U p * ψ p.2)) 2 μ ∧
    MemLp (fun p => ρ p.1 p.2 * ((1 / 2 : ℝ) *
      traceTimeDerivMetric (I := I_hs) G.metric p.1 (x p.2) * (U p * ψ p.2))) 2 μ ∧
    (∀ i, MemLp (fun p => DU i p *
      ((∑ j : Fin (Module.finrank ℝ EuN), A p.1 i j p.2 *
        fderiv ℝ ψ p.2 (EuclideanSpace.single j 1)) * ρ p.1 p.2 -
        B p.1 i p.2 * ρ p.1 p.2 * ψ p.2)) 2 μ) ∧
    MemLp (fun p => ρ p.1 p.2 * U p * (a p.1 * ψ p.2)) 2 μ := by
  intro e x ρ A B μ
  let : IsFiniteMeasure (volume.restrict Ω : Measure EuStd) := by
    refine ⟨?_⟩
    rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ, univ_inter]
    exact (measure_mono subset_closure).trans_lt hΩc.measure_lt_top
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
  have hlift (f : EuStd → ℝ) (hf : ContinuousOn f (closure Ω)) :
      MemLp (fun p : ℝ × EuStd => f p.2) ∞ μ := by
    have h : MemLp f ∞ (volume.restrict Ω) :=
      hf.memLp_top_of_subset_isCompact hΩc hΩ subset_closure
    exact h.comp_snd (timeMeasure T)
  have hψp := hlift ψ hψ.continuous.continuousOn
  have hψd (j : Fin (Module.finrank ℝ EuN)) := hlift
    (fun z => fderiv ℝ ψ z (EuclideanSpace.single j 1))
    (((hψ.continuous_fderiv (by norm_num)).clm_apply continuous_const).continuousOn)
  have hap : MemLp (fun p : ℝ × EuStd => a p.1) ∞ μ := by
    have h : MemLp a ∞ (timeMeasure T) :=
      ha.memLp_top_of_isCompact isCompact_Icc measurableSet_Icc
    exact h.comp_fst (volume.restrict Ω)
  have hUψ : MemLp (fun p : ℝ × EuStd => U p * ψ p.2) 2 μ :=
    MemLp.mul' (p := 2) (q := ∞) (r := 2) hψp (Lp.memLp U)
  refine ⟨MemLp.mul' (r := 2) hUψ hρ, ?_, ?_, ?_⟩
  · exact MemLp.mul' (r := 2) (MemLp.mul' (r := 2) hUψ (hτ.const_mul (1 / 2 : ℝ))) hρ
  · intro i
    have hsum : MemLp (fun p : ℝ × EuStd =>
        ∑ j : Fin (Module.finrank ℝ EuN),
          A p.1 i j p.2 * fderiv ℝ ψ p.2 (EuclideanSpace.single j 1)) ∞ μ := by
      exact memLp_finsetSum Finset.univ fun j _ =>
        MemLp.mul' (p := ∞) (q := ∞) (r := ∞) (hψd j) (hA i j)
    have hf : MemLp (fun p : ℝ × EuStd =>
        (∑ j : Fin (Module.finrank ℝ EuN),
          A p.1 i j p.2 * fderiv ℝ ψ p.2 (EuclideanSpace.single j 1)) * ρ p.1 p.2 -
          B p.1 i p.2 * ρ p.1 p.2 * ψ p.2) ∞ μ :=
      (MemLp.mul' (r := ∞) hρ hsum).sub
        (MemLp.mul' (r := ∞) hψp (MemLp.mul' (r := ∞) hρ (hB i)))
    exact MemLp.mul' (p := 2) (q := ∞) (r := 2) hf (Lp.memLp (DU i))
  · exact MemLp.mul' (p := 2) (q := ∞) (r := 2)
      (MemLp.mul' (r := ∞) hψp hap) (MemLp.mul' (r := 2) (Lp.memLp U) hρ)

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
  obtain ⟨hQ, h₁, h₂, h₃⟩ := local_weakForm_terms_memLp hG hreg X α hXcont hacont
    hΩ.measurableSet hΩc (hΩs.trans (image_mono interior_subset)) ψ
    (hψ_smooth.of_le (by simp)) U DU
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

end DifferentialGeometry.Analysis.Parabolic.Dirichlet
