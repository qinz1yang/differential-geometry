import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletLocalSobolev
import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDivergence
import DifferentialGeometry.Geometry.Operator.HessianTraceChartGramRegularity
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.LocalFormula

noncomputable section

open Manifold MeasureTheory Set
open scoped Manifold Topology ContDiff ENNReal

namespace DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet

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

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.DivergenceTheorem

theorem integral_chart_diffusion_eq_neg_sum_integral
    (q h : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (u : H1ComplDirichlet q) {ψ : EuStd → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) (hψs : tsupport ψ ⊆ Ω) :
    let e := toEuclidean (E := EuN)
    let ρ := fun z => chartDensityOnE (I := I_hs) h α (e.symm z)
    let C := fun i j z => ρ z * chartInvGramOnE (I := I_hs) h α i j (e.symm z)
    (∫ z in Ω, H1ComplDirichletToLp q u ((extChartAt I_hs α).symm (e.symm z)) *
      ∑ i, fderiv ℝ (fun y => ∑ j, C i j y * fderiv ℝ ψ y (EuclideanSpace.single j 1)) z
        (EuclideanSpace.single i 1)) =
      -∑ i, ∫ z in Ω, dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i u z *
        ∑ j, C i j z * fderiv ℝ ψ z (EuclideanSpace.single j 1) := by
  intro e ρ C
  have hy {z : EuStd} (hz : z ∈ Ω) : e.symm z ∈ (extChartAt I_hs α).target := by
    obtain ⟨y, hy, he⟩ := hΩs (subset_closure hz)
    subst z
    exact interior_subset (by simpa only [e, ContinuousLinearEquiv.symm_apply_apply] using hy)
  have hC (i j : Fin (Module.finrank ℝ EuN)) :
      ContDiffOn ℝ (⊤ : ℕ∞) (C i j) Ω := by
    exact ((chartDensityOnE_contDiffOn (I := I_hs) h α).comp e.symm.contDiff.contDiffOn
      (fun _ hz => hy hz)).mul
        ((chartInvGramOnE_contDiffOn (I := I_hs) h α i j).comp e.symm.contDiff.contDiffOn
          (fun _ hz => hy hz))
  have hval : MemLp (fun z => H1ComplDirichletToLp q u
      ((extChartAt I_hs α).symm (e.symm z))) 2 (volume.restrict Ω) := by
    have ht := hΩs.trans (image_mono interior_subset)
    exact (Lp.memLp (chartRestrictionLp q α hΩ.measurableSet hΩc ht 2
      (H1ComplDirichletToLp q u))).ae_eq
      (chartRestrictionLp_coeFn q α hΩ.measurableSet hΩc ht 2 (H1ComplDirichletToLp q u))
  exact DifferentialGeometry.Analysis.Sobolev.Euclidean.integral_mul_sum_fderiv_mul_eq_neg_sum_integral
    hΩ (hval.locallyIntegrable (by norm_num))
    (fun i => hasWeakPartialDeriv_dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i u)
    hC hψ hψc hψs

theorem integral_chart_adjoint_eq_neg_sum_integral
    (q h : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (X : Cₛ^∞⟮I_hs; EuN, (TangentSpace I_hs : M → Type _)⟯)
    (u : H1ComplDirichlet q) {ψ : EuStd → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) (hψs : tsupport ψ ⊆ Ω) :
    let e := toEuclidean (E := EuN)
    let ρ := fun z => chartDensityOnE (I := I_hs) h α (e.symm z)
    let A := fun i j z => chartInvGramOnE (I := I_hs) h α i j (e.symm z)
    let B := fun i z => chartCoeffOnE (I := I_hs) α X i (e.symm z)
    let v := fun z => H1ComplDirichletToLp q u ((extChartAt I_hs α).symm (e.symm z))
    (∫ z in Ω, ρ z * v z *
      ((∑ i, fderiv ℝ (fun y => (∑ j, A i j y *
          fderiv ℝ ψ y (EuclideanSpace.single j 1)) * ρ y) z (EuclideanSpace.single i 1)) / ρ z -
        (∑ i, B i z * fderiv ℝ ψ z (EuclideanSpace.single i 1)) -
        localDivergence (I := I_hs) h α X ((extChartAt I_hs α).symm (e.symm z)) * ψ z)) =
      -∑ i, ∫ z in Ω, dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i u z *
        ((∑ j, A i j z * fderiv ℝ ψ z (EuclideanSpace.single j 1)) * ρ z -
          B i z * ρ z * ψ z) := by
  intro e ρ A B v
  let C := fun i j z => A i j z * ρ z
  let V := fun i z => B i z * ρ z
  have hy {z : EuStd} (hz : z ∈ Ω) : e.symm z ∈ (extChartAt I_hs α).target := by
    obtain ⟨y, hy, he⟩ := hΩs (subset_closure hz)
    subst z
    exact interior_subset (by simpa only [e, ContinuousLinearEquiv.symm_apply_apply] using hy)
  have hρ : ContDiffOn ℝ (⊤ : ℕ∞) ρ Ω :=
    (chartDensityOnE_contDiffOn (I := I_hs) h α).comp e.symm.contDiff.contDiffOn (fun _ hz => hy hz)
  have hC (i j : Fin (Module.finrank ℝ EuN)) :
      ContDiffOn ℝ (⊤ : ℕ∞) (C i j) Ω :=
    ((chartInvGramOnE_contDiffOn (I := I_hs) h α i j).comp e.symm.contDiff.contDiffOn
      (fun _ hz => hy hz)).mul hρ
  have hV (i : Fin (Module.finrank ℝ EuN)) : ContDiffOn ℝ (⊤ : ℕ∞) (V i) Ω :=
    ((chartCoeffOnE_contDiffOn (I := I_hs) α X i).comp e.symm.contDiff.contDiffOn
      (fun _ hz => hy hz)).mul hρ
  have hval : MemLp v 2 (volume.restrict Ω) := by
    have ht := hΩs.trans (image_mono interior_subset)
    exact (Lp.memLp (chartRestrictionLp q α hΩ.measurableSet hΩc ht 2
      (H1ComplDirichletToLp q u))).ae_eq
      (chartRestrictionLp_coeFn q α hΩ.measurableSet hΩc ht 2 (H1ComplDirichletToLp q u))
  have hP (i : Fin (Module.finrank ℝ EuN)) :
      (fun y => (∑ j, A i j y * fderiv ℝ ψ y (EuclideanSpace.single j 1)) * ρ y) =
        fun y => ∑ j, C i j y * fderiv ℝ ψ y (EuclideanSpace.single j 1) := by
    funext y
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    dsimp only [C]
    ring
  have hdiv {z : EuStd} (hz : z ∈ Ω) :
      localDivergence (I := I_hs) h α X ((extChartAt I_hs α).symm (e.symm z)) =
        (∑ i, fderiv ℝ (V i) z (EuclideanSpace.single i 1)) / ρ z := by
    simpa only [e, ContinuousLinearEquiv.apply_symm_apply] using
      localDivergence_eq_sum_fderiv h α X (hy hz)
  have heq (z : EuStd) :
      (∑ i, V i z * fderiv ℝ ψ z (EuclideanSpace.single i 1)) =
        ρ z * ∑ i, B i z * fderiv ℝ ψ z (EuclideanSpace.single i 1) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [V]
    ring
  calc
    _ = ∫ z in Ω, v z *
        ((∑ i, fderiv ℝ (fun y => ∑ j, C i j y *
            fderiv ℝ ψ y (EuclideanSpace.single j 1)) z (EuclideanSpace.single i 1)) -
          (∑ i, V i z * fderiv ℝ ψ z (EuclideanSpace.single i 1)) -
          (∑ i, fderiv ℝ (V i) z (EuclideanSpace.single i 1)) * ψ z) := by
      apply setIntegral_congr_fun hΩ.measurableSet
      intro z hz
      have hn : ρ z ≠ 0 := by
        apply ne_of_gt
        apply chartDensity_pos (I := I_hs) h α
        rw [trivializationAt_baseSet_eq_chartAt_source,
          ← extChartAt_source_eq_chartAt_source (I := I_hs)]
        exact (extChartAt I_hs α).map_target (hy hz)
      simp only [hP, hdiv hz, heq z]
      field_simp [hn]
    _ = -∑ i, ∫ z in Ω, dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i u z *
        ((∑ j, C i j z * fderiv ℝ ψ z (EuclideanSpace.single j 1)) - V i z * ψ z) :=
      DifferentialGeometry.Analysis.Sobolev.Euclidean.integral_mul_sum_fderiv_sub_mul_eq_neg_sum_integral
        hΩ (hval.locallyIntegrable (by norm_num))
        (fun i => hasWeakPartialDeriv_dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i u)
        hC hV hψ hψc hψs
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      apply integral_congr_ae
      filter_upwards [] with z
      rw [← congrFun (hP i) z]

theorem integrable_chart_adjoint
    (q h : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (X : Cₛ^∞⟮I_hs; EuN, (TangentSpace I_hs : M → Type _)⟯)
    (u : H1ComplDirichlet q) {ψ : EuStd → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) (hψs : tsupport ψ ⊆ Ω) :
    let e := toEuclidean (E := EuN)
    let ρ := fun z => chartDensityOnE (I := I_hs) h α (e.symm z)
    let A := fun i j z => chartInvGramOnE (I := I_hs) h α i j (e.symm z)
    let B := fun i z => chartCoeffOnE (I := I_hs) α X i (e.symm z)
    let v := fun z => H1ComplDirichletToLp q u ((extChartAt I_hs α).symm (e.symm z))
    Integrable (fun z => ρ z * v z *
      ((∑ i, fderiv ℝ (fun y => (∑ j, A i j y *
          fderiv ℝ ψ y (EuclideanSpace.single j 1)) * ρ y) z (EuclideanSpace.single i 1)) / ρ z -
        (∑ i, B i z * fderiv ℝ ψ z (EuclideanSpace.single i 1)) -
        localDivergence (I := I_hs) h α X ((extChartAt I_hs α).symm (e.symm z)) * ψ z))
      (volume.restrict Ω) := by
  intro e ρ A B v
  let C := fun i j z => A i j z * ρ z
  let V := fun i z => B i z * ρ z
  have hy {z : EuStd} (hz : z ∈ Ω) : e.symm z ∈ (extChartAt I_hs α).target := by
    obtain ⟨y, hy, he⟩ := hΩs (subset_closure hz)
    subst z
    exact interior_subset (by simpa only [e, ContinuousLinearEquiv.symm_apply_apply] using hy)
  have hρ : ContDiffOn ℝ (⊤ : ℕ∞) ρ Ω :=
    (chartDensityOnE_contDiffOn (I := I_hs) h α).comp e.symm.contDiff.contDiffOn (fun _ hz => hy hz)
  have hC (i j : Fin (Module.finrank ℝ EuN)) :
      ContDiffOn ℝ (⊤ : ℕ∞) (C i j) Ω :=
    ((chartInvGramOnE_contDiffOn (I := I_hs) h α i j).comp e.symm.contDiff.contDiffOn
      (fun _ hz => hy hz)).mul hρ
  have hV (i : Fin (Module.finrank ℝ EuN)) : ContDiffOn ℝ (⊤ : ℕ∞) (V i) Ω :=
    ((chartCoeffOnE_contDiffOn (I := I_hs) α X i).comp e.symm.contDiff.contDiffOn
      (fun _ hz => hy hz)).mul hρ
  have hval : MemLp v 2 (volume.restrict Ω) := by
    have ht := hΩs.trans (image_mono interior_subset)
    exact (Lp.memLp (chartRestrictionLp q α hΩ.measurableSet hΩc ht 2
      (H1ComplDirichletToLp q u))).ae_eq
      (chartRestrictionLp_coeFn q α hΩ.measurableSet hΩc ht 2 (H1ComplDirichletToLp q u))
  have hP (i : Fin (Module.finrank ℝ EuN)) :
      (fun y => (∑ j, A i j y * fderiv ℝ ψ y (EuclideanSpace.single j 1)) * ρ y) =
        fun y => ∑ j, C i j y * fderiv ℝ ψ y (EuclideanSpace.single j 1) := by
    funext y
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    dsimp only [C]
    ring
  have hdiv {z : EuStd} (hz : z ∈ Ω) :
      localDivergence (I := I_hs) h α X ((extChartAt I_hs α).symm (e.symm z)) =
        (∑ i, fderiv ℝ (V i) z (EuclideanSpace.single i 1)) / ρ z := by
    simpa only [e, ContinuousLinearEquiv.apply_symm_apply] using
      localDivergence_eq_sum_fderiv h α X (hy hz)
  have heq (z : EuStd) :
      (∑ i, V i z * fderiv ℝ ψ z (EuclideanSpace.single i 1)) =
        ρ z * ∑ i, B i z * fderiv ℝ ψ z (EuclideanSpace.single i 1) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [V]
    ring
  apply (DifferentialGeometry.Analysis.Sobolev.Euclidean.integrable_mul_sum_fderiv_sub_mul
    hΩ (hval.locallyIntegrable (by norm_num)) hC hV hψ hψc hψs).congr
  filter_upwards [ae_restrict_mem hΩ.measurableSet] with z hz
  have hn : ρ z ≠ 0 := by
    apply ne_of_gt
    apply chartDensity_pos (I := I_hs) h α
    rw [trivializationAt_baseSet_eq_chartAt_source,
      ← extChartAt_source_eq_chartAt_source (I := I_hs)]
    exact (extChartAt I_hs α).map_target (hy hz)
  simp only [hP, hdiv hz, heq z]
  field_simp [hn]

end DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
