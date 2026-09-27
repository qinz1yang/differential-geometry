import DifferentialGeometry.Analysis.Parabolic.ClosedCell.PullbackRegularity
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Chart
import DifferentialGeometry.Geometry.Metric.Pullback.Coefficients
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Topology.MetricSpace.Lipschitz

noncomputable section

open Filter Manifold MeasureTheory Set
open scoped ContDiff Manifold Matrix

private def euclideanDimensionCast {n k : ℕ} (h : n = k) :
    EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin k) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (finCongr h)

private theorem euclideanDimensionCast_eq_cast {n k : ℕ} (h : n = k)
    (x : EuclideanSpace ℝ (Fin n)) :
    euclideanDimensionCast h x =
      cast (congrArg (fun r => EuclideanSpace ℝ (Fin r)) h) x := by
  subst k
  ext i
  rfl

namespace DifferentialGeometry.Analysis.Parabolic

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

local notation "V" => EuclideanSpace ℝ (Fin (m + 1))
local notation "W" => EuclideanSpace ℝ (Fin (Module.finrank ℝ V))
local notation "Z" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

omit [FiniteDimensional ℝ E] in
private def closedCellEuclideanCast (hdim : Module.finrank ℝ E = m + 1) :
    W ≃ₗᵢ[ℝ] Z :=
  euclideanDimensionCast (by simpa only [finrank_euclideanSpace_fin] using hdim.symm)

private def closedCellCoordinateToModel (hdim : Module.finrank ℝ E = m + 1) :
    W ≃L[ℝ] E :=
  (closedCellEuclideanCast hdim).toContinuousLinearEquiv.trans (toEuclidean (E := E)).symm

private theorem closedCellCoordinateToModel_apply
    (hdim : Module.finrank ℝ E = m + 1) (y : W) :
    closedCellCoordinateToModel hdim y =
      (toEuclidean (E := E)).symm (closedCellEuclideanCast hdim y) := rfl

private theorem closedCellCoordinateToModel_comp_cast_symm
    (hdim : Module.finrank ℝ E = m + 1) (y : Z) :
    closedCellCoordinateToModel hdim ((closedCellEuclideanCast hdim).symm y) =
      (toEuclidean (E := E)).symm y := by
  rw [closedCellCoordinateToModel_apply, LinearIsometryEquiv.apply_symm_apply]

end DifferentialGeometry.Analysis.Parabolic

namespace DifferentialGeometry.Analysis.Parabolic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private theorem pullback_metric_weak_equation_dimension_cast
    {n k : ℕ} (h : n = k) (g : ℝ → SmoothRiemannianMetric I M)
    (Ψ : EuclideanSpace ℝ (Fin k) → M)
    (Ω : Set (EuclideanSpace ℝ (Fin k))) (u : ℝ × EuclideanSpace ℝ (Fin k) → ℝ)
    (a b : ℝ) :
    let Q : ℝ × EuclideanSpace ℝ (Fin k) → Matrix (Fin k) (Fin k) ℝ :=
      fun q => Matrix.of (fun i j => Geometry.pullbackMetricCoefficients (g q.1) Ψ q.2
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1))
    (∀ φ : ℝ × EuclideanSpace ℝ (Fin k) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Set.Ioo a b ×ˢ Ω →
      (∫ q, Real.sqrt (Q q).det * u q * fderiv ℝ φ q (1, 0)
        ∂(volume.restrict (Set.Icc a b)).prod (volume.restrict Ω)) =
        ∑ j, ∫ q, (∑ i, (Real.sqrt (Q q).det * (Q q)⁻¹ i j) *
          fderiv ℝ (fun y => u (q.1, y)) q.2 (EuclideanSpace.single i 1)) *
          fderiv ℝ φ q (0, EuclideanSpace.single j 1)
            ∂(volume.restrict (Set.Icc a b)).prod (volume.restrict Ω)) →
    let e := euclideanDimensionCast h
    let Ψ' : EuclideanSpace ℝ (Fin n) → M := fun y => Ψ (e y)
    let Q' : ℝ × EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ :=
      fun q => Matrix.of (fun i j => Geometry.pullbackMetricCoefficients (g q.1) Ψ' q.2
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1))
    ∀ φ : ℝ × EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Set.Ioo a b ×ˢ (e ⁻¹' Ω) →
      (∫ q, Real.sqrt (Q' q).det * u (q.1, e q.2) * fderiv ℝ φ q (1, 0)
        ∂(volume.restrict (Set.Icc a b)).prod (volume.restrict (e ⁻¹' Ω))) =
        ∑ j, ∫ q, (∑ i, (Real.sqrt (Q' q).det * (Q' q)⁻¹ i j) *
          fderiv ℝ (fun y => u (q.1, e y)) q.2 (EuclideanSpace.single i 1)) *
          fderiv ℝ φ q (0, EuclideanSpace.single j 1)
            ∂(volume.restrict (Set.Icc a b)).prod (volume.restrict (e ⁻¹' Ω)) := by
  intro Q hweak e Ψ' Q'
  subst k
  have he : ⇑(euclideanDimensionCast (rfl : n = n)) = id := by
    funext x
    exact euclideanDimensionCast_eq_cast rfl x
  simpa only [Q, e, Ψ', Q', he, id_eq, Prod.mk.eta, Set.preimage_id_eq] using hweak

end DifferentialGeometry.Analysis.Parabolic

namespace DifferentialGeometry.Analysis.Parabolic

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

local notation "V" => EuclideanSpace ℝ (Fin (m + 1))
local notation "W" => EuclideanSpace ℝ (Fin (Module.finrank ℝ V))

private local instance : T2Space V := inferInstance

private def inverseChartOnEuclidean (L : W ≃L[ℝ] E) (α : M) :
    PartialDiffeomorph 𝓘(ℝ, V) I V M ∞ :=
  ((toEuclidean (E := V)).trans L).toDiffeomorph.toPartialDiffeomorph.trans
    (DifferentialGeometry.PartialDiffeomorph.extChartAt I ∞ α).symm

private theorem inverseChartOnEuclidean_apply (L : W ≃L[ℝ] E) (α : M) (z : V) :
    inverseChartOnEuclidean (m := m) (I := I) L α z =
      (extChartAt I α).symm (L (toEuclidean (E := V) z)) := rfl

private theorem inverseChartOnEuclidean_comp_toEuclidean_symm
    (L : W ≃L[ℝ] E) (α : M) (y : W) :
    inverseChartOnEuclidean (m := m) (I := I) L α ((toEuclidean (E := V)).symm y) =
      (extChartAt I α).symm (L y) := by
  rw [inverseChartOnEuclidean_apply (m := m) (I := I), ContinuousLinearEquiv.apply_symm_apply]

private theorem inverseChartOnEuclidean_source (L : W ≃L[ℝ] E) (α : M) :
    (inverseChartOnEuclidean (m := m) (I := I) L α).source =
      (fun z : V => L (toEuclidean (E := V) z)) ⁻¹' (extChartAt I α).target := by
  ext z
  change (z ∈ (Set.univ : Set V) ∧
    L (toEuclidean (E := V) z) ∈ (extChartAt I α).target) ↔
      L (toEuclidean (E := V) z) ∈ (extChartAt I α).target
  simp only [mem_univ, true_and]

private theorem exists_closedBall_subset_inverseChartOnEuclidean_source
    (L : W ≃L[ℝ] E) (α : M) {y : W}
    (hy : L y ∈ (extChartAt I α).target) :
    ∃ r : ℝ, 0 < r ∧ Metric.closedBall ((toEuclidean (E := V)).symm y) r ⊆
      (inverseChartOnEuclidean (m := m) (I := I) L α).source := by
  have hmem : (toEuclidean (E := V)).symm y ∈
      (inverseChartOnEuclidean (m := m) (I := I) L α).source := by
    rw [inverseChartOnEuclidean_source (m := m) (I := I)]
    change L (toEuclidean (E := V) ((toEuclidean (E := V)).symm y)) ∈
      (extChartAt I α).target
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using hy
  obtain ⟨r, hr, hball⟩ :=
    Metric.isOpen_iff.mp (inverseChartOnEuclidean (m := m) (I := I) L α).open_source _ hmem
  exact ⟨r / 2, half_pos hr,
    (Metric.closedBall_subset_ball (half_lt_self hr)).trans hball⟩

end DifferentialGeometry.Analysis.Parabolic

private theorem integral_mul_fderiv_prod_restrict_eq_of_tsupport_subset
    {n : ℕ} {Ω Ω₁ : Set (EuclideanSpace ℝ (Fin n))} (hΩ₁Ω : Ω₁ ⊆ Ω)
    {a b : ℝ} {φ : ℝ × EuclideanSpace ℝ (Fin n) → ℝ}
    (hsupport : tsupport φ ⊆ Set.Ioo a b ×ˢ Ω₁)
    (A : ℝ × EuclideanSpace ℝ (Fin n) → ℝ)
    (v : ℝ × EuclideanSpace ℝ (Fin n)) :
    (∫ q, A q * fderiv ℝ φ q v
      ∂(volume.restrict (Set.Icc a b)).prod (volume.restrict Ω)) =
      ∫ q, A q * fderiv ℝ φ q v
        ∂(volume.restrict (Set.Icc a b)).prod (volume.restrict Ω₁) := by
  have hzero (q : ℝ × EuclideanSpace ℝ (Fin n))
      (hq : q ∉ Set.Icc a b ×ˢ Ω₁) : A q * fderiv ℝ φ q v = 0 := by
    have hqφ : q ∉ tsupport φ := by
      intro hqφ
      exact hq ⟨Set.Ioo_subset_Icc_self (hsupport hqφ).1, (hsupport hqφ).2⟩
    rw [fderiv_of_notMem_tsupport ℝ hqφ, zero_apply, mul_zero]
  rw [Measure.prod_restrict, Measure.prod_restrict]
  calc
    (∫ q in Set.Icc a b ×ˢ Ω, A q * fderiv ℝ φ q v ∂volume.prod volume) =
        ∫ q, A q * fderiv ℝ φ q v ∂volume.prod volume := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro q hq
      apply hzero q
      intro hq₁
      exact hq ⟨hq₁.1, hΩ₁Ω hq₁.2⟩
    _ = ∫ q in Set.Icc a b ×ˢ Ω₁, A q * fderiv ℝ φ q v ∂volume.prod volume :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero hzero).symm

private theorem weighted_weak_equation_mono_spatial_domain
    {n : ℕ} {Ω Ω₁ : Set (EuclideanSpace ℝ (Fin n))} (hΩ₁Ω : Ω₁ ⊆ Ω)
    (Q : ℝ × EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ)
    (u : ℝ × EuclideanSpace ℝ (Fin n) → ℝ) (a b : ℝ)
    (hweak : ∀ φ : ℝ × EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Set.Ioo a b ×ˢ Ω →
      (∫ q, Real.sqrt (Q q).det * u q * fderiv ℝ φ q (1, 0)
        ∂(volume.restrict (Set.Icc a b)).prod (volume.restrict Ω)) =
        ∑ j, ∫ q, (∑ i, (Real.sqrt (Q q).det * (Q q)⁻¹ i j) *
          fderiv ℝ (fun y => u (q.1, y)) q.2 (EuclideanSpace.single i 1)) *
          fderiv ℝ φ q (0, EuclideanSpace.single j 1)
            ∂(volume.restrict (Set.Icc a b)).prod (volume.restrict Ω)) :
    ∀ φ : ℝ × EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Set.Ioo a b ×ˢ Ω₁ →
      (∫ q, Real.sqrt (Q q).det * u q * fderiv ℝ φ q (1, 0)
        ∂(volume.restrict (Set.Icc a b)).prod (volume.restrict Ω₁)) =
        ∑ j, ∫ q, (∑ i, (Real.sqrt (Q q).det * (Q q)⁻¹ i j) *
          fderiv ℝ (fun y => u (q.1, y)) q.2 (EuclideanSpace.single i 1)) *
          fderiv ℝ φ q (0, EuclideanSpace.single j 1)
            ∂(volume.restrict (Set.Icc a b)).prod (volume.restrict Ω₁) := by
  intro φ hφ hcompact hsupport
  have hsupportΩ : tsupport φ ⊆ Set.Ioo a b ×ˢ Ω := by
    intro q hq
    exact ⟨(hsupport hq).1, hΩ₁Ω (hsupport hq).2⟩
  calc
    (∫ q, Real.sqrt (Q q).det * u q * fderiv ℝ φ q (1, 0)
      ∂(volume.restrict (Set.Icc a b)).prod (volume.restrict Ω₁)) =
        ∫ q, Real.sqrt (Q q).det * u q * fderiv ℝ φ q (1, 0)
          ∂(volume.restrict (Set.Icc a b)).prod (volume.restrict Ω) :=
      (integral_mul_fderiv_prod_restrict_eq_of_tsupport_subset hΩ₁Ω hsupport
        (fun q => Real.sqrt (Q q).det * u q) (1, 0)).symm
    _ = ∑ j, ∫ q, (∑ i, (Real.sqrt (Q q).det * (Q q)⁻¹ i j) *
        fderiv ℝ (fun y => u (q.1, y)) q.2 (EuclideanSpace.single i 1)) *
        fderiv ℝ φ q (0, EuclideanSpace.single j 1)
          ∂(volume.restrict (Set.Icc a b)).prod (volume.restrict Ω) :=
      hweak φ hφ hcompact hsupportΩ
    _ = ∑ j, ∫ q, (∑ i, (Real.sqrt (Q q).det * (Q q)⁻¹ i j) *
        fderiv ℝ (fun y => u (q.1, y)) q.2 (EuclideanSpace.single i 1)) *
        fderiv ℝ φ q (0, EuclideanSpace.single j 1)
          ∂(volume.restrict (Set.Icc a b)).prod (volume.restrict Ω₁) := by
      apply Finset.sum_congr rfl
      intro j _
      exact integral_mul_fderiv_prod_restrict_eq_of_tsupport_subset hΩ₁Ω hsupport
        (fun q => ∑ i, (Real.sqrt (Q q).det * (Q q)⁻¹ i j) *
          fderiv ℝ (fun y => u (q.1, y)) q.2 (EuclideanSpace.single i 1))
        (0, EuclideanSpace.single j 1)

namespace DifferentialGeometry.Analysis.Parabolic

open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

local notation "V" => EuclideanSpace ℝ (Fin (m + 1))
local notation "W" => EuclideanSpace ℝ (Fin (Module.finrank ℝ V))
local notation "Z" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

private local instance : T2Space V := inferInstance

private theorem locallyLipschitzOn_prod_dimension_cast
    {n k : ℕ} (h : n = k) (Ω : Set (EuclideanSpace ℝ (Fin k)))
    (u : ℝ × EuclideanSpace ℝ (Fin k) → ℝ) (a b : ℝ)
    (hu : LocallyLipschitzOn (Icc a b ×ˢ Ω) u) :
    LocallyLipschitzOn (Icc a b ×ˢ ((euclideanDimensionCast h) ⁻¹' Ω))
      (fun q => u (q.1, euclideanDimensionCast h q.2)) := by
  subst k
  have he : ⇑(euclideanDimensionCast (rfl : n = n)) = id := by
    funext x
    exact euclideanDimensionCast_eq_cast rfl x
  simpa only [he, id_eq, Prod.mk.eta, preimage_id_eq] using hu

theorem contDiffAt_of_locallyLipschitzOn_inverse_chart_metric_weak_equation
    (hdim : Module.finrank ℝ E = m + 1)
    (D : RealTimeInterval) (g : ℝ → SmoothRiemannianMetric I M)
    (hg : MetricFamilySmoothOn D g) (α : M)
    (Ω : Set Z) (hΩ : IsOpen Ω) {a b : ℝ} (hreg : Icc a b ⊆ D.regular) :
    let Ψ : Z → M := fun y => (extChartAt I α).symm ((toEuclidean (E := E)).symm y)
    let Q : ℝ × Z → Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
      fun q => Matrix.of (fun i j => pullbackMetricCoefficients (g q.1) Ψ q.2
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1))
    ∀ (u : ℝ × Z → ℝ), LocallyLipschitzOn (Icc a b ×ˢ Ω) u →
      (∀ φ : ℝ × Z → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Ioo a b ×ˢ Ω →
        (∫ q, Real.sqrt (Q q).det * u q * fderiv ℝ φ q (1, 0)
          ∂(volume.restrict (Icc a b)).prod (volume.restrict Ω)) =
          ∑ j, ∫ q, (∑ i, (Real.sqrt (Q q).det * (Q q)⁻¹ i j) *
            fderiv ℝ (fun y => u (q.1, y)) q.2 (EuclideanSpace.single i 1)) *
            fderiv ℝ φ q (0, EuclideanSpace.single j 1)
              ∂(volume.restrict (Icc a b)).prod (volume.restrict Ω)) →
      ∀ {t : ℝ}, t ∈ Ioo a b → ∀ {y : Z}, y ∈ Ω →
        (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target →
        ContDiffAt ℝ (⊤ : ℕ∞) u (t, y) := by
  intro Ψ Q u hu hweak t ht y hy hychart
  have hcast : Module.finrank ℝ V = Module.finrank ℝ E := by
    simpa only [finrank_euclideanSpace_fin] using hdim.symm
  let e := closedCellEuclideanCast hdim
  let L := closedCellCoordinateToModel hdim
  let Φ := inverseChartOnEuclidean (m := m) (I := I) L α
  let w : W := e.symm y
  let c : V := (toEuclidean (E := V)).symm w
  let ΩW : Set W := e ⁻¹' Ω
  let uW : ℝ × W → ℝ := fun q => u (q.1, e q.2)
  let ΨW : W → M := fun z => Ψ (e z)
  let QW : ℝ × W → Matrix (Fin (Module.finrank ℝ V)) (Fin (Module.finrank ℝ V)) ℝ :=
    fun q => Matrix.of (fun i j => pullbackMetricCoefficients (g q.1) ΨW q.2
      (EuclideanSpace.single i 1) (EuclideanSpace.single j 1))
  have hΩW : IsOpen ΩW := hΩ.preimage e.continuous
  have hwΩ : w ∈ ΩW := by
    change e (e.symm y) ∈ Ω
    simpa only [LinearIsometryEquiv.apply_symm_apply] using hy
  have htarget : L w ∈ (extChartAt I α).target := by
    change closedCellCoordinateToModel hdim ((closedCellEuclideanCast hdim).symm y) ∈
      (extChartAt I α).target
    simpa only [closedCellCoordinateToModel_comp_cast_symm] using hychart
  obtain ⟨r, hr, hsource⟩ :=
    exists_closedBall_subset_inverseChartOnEuclidean_source (m := m) (I := I) L α htarget
  have hsource' : Metric.closedBall c r ⊆ Φ.source := hsource
  have hballOpen : IsOpen ((toEuclidean (E := V)) '' Metric.ball c r) :=
    (toEuclidean (E := V)).toHomeomorph.isOpenMap _ Metric.isOpen_ball
  have hwball : w ∈ (toEuclidean (E := V)) '' Metric.ball c r := by
    refine ⟨c, Metric.mem_ball_self hr, ?_⟩
    exact ContinuousLinearEquiv.apply_symm_apply _ w
  obtain ⟨δ, hδ, hδball⟩ :=
    Metric.isOpen_iff.mp (hΩW.inter hballOpen) w ⟨hwΩ, hwball⟩
  let B : Set W := Metric.ball w (δ / 2)
  have hBsmall : closure B ⊆ Metric.ball w δ :=
    Metric.closure_ball_subset_closedBall.trans (Metric.closedBall_subset_ball (half_lt_self hδ))
  have hBΩ : closure B ⊆ ΩW := fun _ hz => (hδball (hBsmall hz)).1
  have hBball : closure B ⊆ (toEuclidean (E := V)) '' Metric.ball c r :=
    fun _ hz => (hδball (hBsmall hz)).2
  have hBc : IsCompact (closure B) :=
    (isCompact_closedBall w (δ / 2)).of_isClosed_subset isClosed_closure
      Metric.closure_ball_subset_closedBall
  have huW : LocallyLipschitzOn (Icc a b ×ˢ ΩW) uW :=
    locallyLipschitzOn_prod_dimension_cast hcast Ω u a b hu
  have huB : LocallyLipschitzOn (Icc a b ×ˢ closure B) uW :=
    huW.mono (fun _ hq => ⟨hq.1, hBΩ hq.2⟩)
  have hweakW := pullback_metric_weak_equation_dimension_cast hcast g Ψ Ω u a b hweak
  have hweakB := weighted_weak_equation_mono_spatial_domain
    (fun z hz => hBΩ (subset_closure hz)) QW uW a b hweakW
  have hΨW : (fun z : W => Φ ((toEuclidean (E := V)).symm z)) = ΨW := by
    funext z
    rw [inverseChartOnEuclidean_comp_toEuclidean_symm]
    rfl
  let a' := (a + t) / 2
  let b' := (t + b) / 2
  have haa : a < a' := by dsimp [a']; linarith [ht.1]
  have hbb : b' < b := by dsimp [b']; linarith [ht.2]
  let B₀ : Set W := Metric.ball w (δ / 4)
  have hB₀B : closure B₀ ⊆ B := by
    apply Metric.closure_ball_subset_closedBall.trans
    exact Metric.closedBall_subset_ball (by linarith)
  have hs := contDiffOn_of_locallyLipschitzOn_pullback_metric_weak_equation
    D g hg Φ c hr hsource' (ht.1.trans ht.2) hreg B Metric.isOpen_ball hBc hBball
    uW huB (by simpa only [hΨW] using hweakB) haa hbb Metric.isOpen_ball hB₀B
  have ht' : t ∈ Ioo a' b' := by
    constructor
    · dsimp [a']; linarith [ht.1]
    · dsimp [b']; linarith [ht.2]
  have hw₀ : w ∈ B₀ := Metric.mem_ball_self (by positivity)
  have hsAt : ContDiffAt ℝ (⊤ : ℕ∞) uW (t, w) :=
    hs.contDiffAt ((isOpen_Ioo.prod Metric.isOpen_ball).mem_nhds ⟨ht', hw₀⟩)
  have hback : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun q : ℝ × Z => (q.1, e.symm q.2)) (t, y) :=
    contDiffAt_fst.prodMk
      (e.symm.toContinuousLinearEquiv.contDiff.contDiffAt.comp (t, y) contDiffAt_snd)
  have hout := hsAt.comp (t, y) hback
  simpa only [Function.comp_def, uW, LinearIsometryEquiv.apply_symm_apply,
    Prod.mk.eta] using hout

theorem contDiffOn_of_locallyLipschitzOn_inverse_chart_metric_weak_equation
    (hdim : Module.finrank ℝ E = m + 1)
    (D : RealTimeInterval) (g : ℝ → SmoothRiemannianMetric I M)
    (hg : MetricFamilySmoothOn D g) (α : M)
    (Ω : Set Z) (hΩ : IsOpen Ω)
    (hΩtarget : ∀ y ∈ Ω, (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target)
    {a b : ℝ} (hreg : Icc a b ⊆ D.regular) :
    let Ψ : Z → M := fun y => (extChartAt I α).symm ((toEuclidean (E := E)).symm y)
    let Q : ℝ × Z → Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
      fun q => Matrix.of (fun i j => pullbackMetricCoefficients (g q.1) Ψ q.2
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1))
    ∀ (u : ℝ × Z → ℝ), LocallyLipschitzOn (Icc a b ×ˢ Ω) u →
      (∀ φ : ℝ × Z → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Ioo a b ×ˢ Ω →
        (∫ q, Real.sqrt (Q q).det * u q * fderiv ℝ φ q (1, 0)
          ∂(volume.restrict (Icc a b)).prod (volume.restrict Ω)) =
          ∑ j, ∫ q, (∑ i, (Real.sqrt (Q q).det * (Q q)⁻¹ i j) *
            fderiv ℝ (fun y => u (q.1, y)) q.2 (EuclideanSpace.single i 1)) *
            fderiv ℝ φ q (0, EuclideanSpace.single j 1)
              ∂(volume.restrict (Icc a b)).prod (volume.restrict Ω)) →
      ContDiffOn ℝ (⊤ : ℕ∞) u (Ioo a b ×ˢ Ω) := by
  intro Ψ Q u hu hweak q hq
  exact (contDiffAt_of_locallyLipschitzOn_inverse_chart_metric_weak_equation
    hdim D g hg α Ω hΩ hreg u hu hweak hq.1 hq.2 (hΩtarget q.2 hq.2)).contDiffWithinAt

end DifferentialGeometry.Analysis.Parabolic
