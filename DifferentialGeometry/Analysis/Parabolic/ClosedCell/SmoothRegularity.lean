import DifferentialGeometry.Analysis.Parabolic.ClosedCell.TimeDerivatives
import DifferentialGeometry.Analysis.Sobolev.Euclidean.SpacetimeRegularity

noncomputable section

open Filter Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold Matrix Topology

namespace DifferentialGeometry.Analysis.Parabolic

open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Topology
open DifferentialGeometry.Topology.Handle
open DifferentialGeometry.Analysis.Sobolev.Euclidean
  (contDiffOn_of_continuousOn_finite_time_weak_partial_trees)

private local instance (m : ℕ) :
    ChartedSpace (EuclideanHalfSpace (m + 1)) (ClosedCell (m + 1)) :=
  closedCellChartedSpaceSucc m

private local instance (m : ℕ) :
    IsManifold (𝓡∂ (m + 1)) ∞ (ClosedCell (m + 1)) :=
  closedCellIsManifold m

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

local notation "V" => EuclideanSpace ℝ (Fin (m + 1))
local notation "W" => EuclideanSpace ℝ (Fin (Module.finrank ℝ V))

private local instance : T2Space V := inferInstance

private local instance : MeasurableSpace W :=
  WithLp.measurableSpace 2 ((i : Fin (Module.finrank ℝ V)) → ℝ)

theorem contDiffOn_closedCell_of_continuousOn_weighted_weak_equation
    (D : RealTimeInterval) (g : ℝ → SmoothRiemannianMetric I M)
    (hg : MetricFamilySmoothOn D g)
    (Φ : PartialDiffeomorph (𝓡 (m + 1)) I V M ∞)
    (c : V) {r : ℝ} (hr : 0 < r)
    (hsource : Metric.closedBall c r ⊆ Φ.source)
    (α : ClosedCell (m + 1)) (hα : ‖α.val‖ < 1)
    {a b : ℝ} (hab : a < b) (hreg : Icc a b ⊆ D.regular)
    (Ω : Set W) (hΩ : IsOpen Ω) :
    let z : W := (toEuclidean (E := V)) c -
      r • (toEuclidean (E := V)) (EuclideanSpace.basisFun (Fin (m + 1)) ℝ 0)
    let Ψ : W → M := fun y => Φ ((toEuclidean (E := V)).symm y)
    let Q : ℝ × W → Matrix (Fin (Module.finrank ℝ V)) (Fin (Module.finrank ℝ V)) ℝ :=
      fun q => Matrix.of (fun i j => pullbackMetricCoefficients (g q.1) Ψ q.2
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1))
    let Ωh := (fun x => z + r • x) ⁻¹' Ω
    IsCompact (closure Ωh) →
    closure Ωh ⊆ toEuclidean (E := V) '' interior (extChartAt (𝓡∂ (m + 1)) α).target →
    ∀ (U : Lp ℝ 2 ((volume.restrict (Icc a b)).prod (volume.restrict Ω)))
      (K : Fin (Module.finrank ℝ V) →
        Lp ℝ 2 ((volume.restrict (Icc a b)).prod (volume.restrict Ω)))
      (u : ℝ × W → ℝ),
      (U =ᵐ[(volume.restrict (Icc a b)).prod (volume.restrict Ω)] u) →
      ContinuousOn u (Ioo a b ×ˢ Ω) →
      (∀ i, ∀ᵐ t ∂volume.restrict (Icc a b), DeGiorgi.HasWeakPartialDeriv i
        (fun x => K i (t, x)) (fun x => U (t, x)) Ω) →
      (∀ φ : ℝ × W → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Ioo a b ×ˢ Ω →
        (∫ q, Real.sqrt (Q q).det * U q * fderiv ℝ φ q (1, 0)
          ∂(volume.restrict (Icc a b)).prod (volume.restrict Ω)) =
          ∑ j, ∫ q, (∑ i, (Real.sqrt (Q q).det * (Q q)⁻¹ i j) * K i q) *
            fderiv ℝ φ q (0, EuclideanSpace.single j 1)
              ∂(volume.restrict (Icc a b)).prod (volume.restrict Ω)) →
      ∀ {a' b' : ℝ}, a < a' → b' < b → ∀ {Ω₀ : Set W},
        IsOpen Ω₀ → closure Ω₀ ⊆ Ωh →
        ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℝ × W => u (q.1, z + r • q.2))
          (Ioo a' b' ×ˢ Ω₀) := by
  intro z Ψ Q Ωh hΩhc hΩhs U K u hU hu hspatial hweak a' b' haa hbb Ω₀ hΩ₀ hΩ₀Ω
  let ν := (volume.restrict (Icc a' b')).prod (volume.restrict Ω₀)
  let νh := (volume.restrict (Icc a b)).prod (volume.restrict Ωh)
  have hν : ν ≤ νh := Measure.prod_mono
    (Measure.restrict_mono (Icc_subset_Icc haa.le hbb.le) le_rfl)
    (Measure.restrict_mono (subset_closure.trans hΩ₀Ω) le_rfl)
  have hmap := quasiMeasurePreserving_prod_add_smul_restrict
    (volume.restrict (Icc a b)) volume z hr.ne' Ω
  have hUlocal : (fun q : ℝ × W => U (q.1, z + r • q.2)) =ᵐ[ν]
      fun q => u (q.1, z + r • q.2) :=
    (hmap.ae hU).filter_mono (ae_mono hν)
  have hulocal : ContinuousOn (fun q : ℝ × W => u (q.1, z + r • q.2))
      (Ioo a' b' ×ˢ Ω₀) := by
    apply hu.comp (by fun_prop)
    intro q hq
    exact ⟨⟨haa.trans hq.1.1, hq.1.2.trans hbb⟩, hΩ₀Ω (subset_closure hq.2)⟩
  rw [contDiffOn_infty]
  intro s
  let L := s + Module.finrank ℝ V + 2
  have hLs : (s : ℝ) + (Module.finrank ℝ V + 1 : ℝ) / 2 < L := by
    dsimp [L]
    push_cast
    have hn : (0 : ℝ) ≤ Module.finrank ℝ V := Nat.cast_nonneg _
    linarith
  obtain ⟨X, hXroot, _, hXspace, _, hXtime⟩ := exists_closedCell_time_weak_partial_trees
    L L D g hg Φ c hr hsource α hα hab hreg Ω hΩ hΩhc hΩhs U K hspatial hweak
    haa hbb hΩ₀ hΩ₀Ω
  let Y : Fin (L + 1) → ∀ n : ℕ, (Fin n → Fin (Module.finrank ℝ V)) → Lp ℝ 2 ν :=
    fun j => X j.castSucc
  apply contDiffOn_of_continuousOn_finite_time_weak_partial_trees
    hΩ₀ hLs (fun q => u (q.1, z + r • q.2)) hulocal Y
  · exact hXroot.trans hUlocal
  · intro j n hjn β i
    exact hXspace j.castSucc n (by dsimp [L] at *; omega) β i
  · intro j n hjn β φ hφ hφc hφs
    have h := hXtime j.castSucc n (by dsimp [L] at *; omega) β φ hφ hφc hφs
    simpa only [Y, Fin.castSucc_succ] using h

theorem contDiffOn_affineImage_of_continuousOn_weighted_weak_equation
    (D : RealTimeInterval) (g : ℝ → SmoothRiemannianMetric I M)
    (hg : MetricFamilySmoothOn D g)
    (Φ : PartialDiffeomorph (𝓡 (m + 1)) I V M ∞)
    (c : V) {r : ℝ} (hr : 0 < r)
    (hsource : Metric.closedBall c r ⊆ Φ.source)
    (α : ClosedCell (m + 1)) (hα : ‖α.val‖ < 1)
    {a b : ℝ} (hab : a < b) (hreg : Icc a b ⊆ D.regular)
    (Ω : Set W) (hΩ : IsOpen Ω) :
    let z : W := (toEuclidean (E := V)) c -
      r • (toEuclidean (E := V)) (EuclideanSpace.basisFun (Fin (m + 1)) ℝ 0)
    let Ψ : W → M := fun y => Φ ((toEuclidean (E := V)).symm y)
    let Q : ℝ × W → Matrix (Fin (Module.finrank ℝ V)) (Fin (Module.finrank ℝ V)) ℝ :=
      fun q => Matrix.of (fun i j => pullbackMetricCoefficients (g q.1) Ψ q.2
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1))
    let Ωh := (fun x => z + r • x) ⁻¹' Ω
    IsCompact (closure Ωh) →
    closure Ωh ⊆ toEuclidean (E := V) '' interior (extChartAt (𝓡∂ (m + 1)) α).target →
    ∀ (U : Lp ℝ 2 ((volume.restrict (Icc a b)).prod (volume.restrict Ω)))
      (K : Fin (Module.finrank ℝ V) →
        Lp ℝ 2 ((volume.restrict (Icc a b)).prod (volume.restrict Ω)))
      (u : ℝ × W → ℝ),
      (U =ᵐ[(volume.restrict (Icc a b)).prod (volume.restrict Ω)] u) →
      ContinuousOn u (Ioo a b ×ˢ Ω) →
      (∀ i, ∀ᵐ t ∂volume.restrict (Icc a b), DeGiorgi.HasWeakPartialDeriv i
        (fun x => K i (t, x)) (fun x => U (t, x)) Ω) →
      (∀ φ : ℝ × W → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Ioo a b ×ˢ Ω →
        (∫ q, Real.sqrt (Q q).det * U q * fderiv ℝ φ q (1, 0)
          ∂(volume.restrict (Icc a b)).prod (volume.restrict Ω)) =
          ∑ j, ∫ q, (∑ i, (Real.sqrt (Q q).det * (Q q)⁻¹ i j) * K i q) *
            fderiv ℝ φ q (0, EuclideanSpace.single j 1)
              ∂(volume.restrict (Icc a b)).prod (volume.restrict Ω)) →
      ∀ {a' b' : ℝ}, a < a' → b' < b → ∀ {Ω₀ : Set W},
        IsOpen Ω₀ → closure Ω₀ ⊆ Ωh →
        ContDiffOn ℝ (⊤ : ℕ∞) u
          (Ioo a' b' ×ˢ ((fun x : W => z + r • x) '' Ω₀)) := by
  intro z Ψ Q Ωh hΩhc hΩhs U K u hU hu hspatial hweak a' b' haa hbb Ω₀ hΩ₀ hΩ₀Ω
  have hs := contDiffOn_closedCell_of_continuousOn_weighted_weak_equation
    D g hg Φ c hr hsource α hα hab hreg Ω hΩ hΩhc hΩhs U K u hU hu hspatial hweak
    haa hbb hΩ₀ hΩ₀Ω
  let B : ℝ × W → ℝ × W := fun q => (q.1, r⁻¹ • (q.2 - z))
  have hB : ContDiff ℝ (⊤ : ℕ∞) B := by fun_prop
  have hmaps : MapsTo B (Ioo a' b' ×ˢ ((fun x : W => z + r • x) '' Ω₀))
      (Ioo a' b' ×ˢ Ω₀) := by
    rintro q ⟨ht, x, hx, heq⟩
    refine ⟨ht, ?_⟩
    change r⁻¹ • (q.2 - z) ∈ Ω₀
    rw [← heq, add_sub_cancel_left, inv_smul_smul₀ hr.ne']
    exact hx
  have hcomp := hs.comp hB.contDiffOn hmaps
  have heq : (fun q : ℝ × W => u (q.1, z + r • q.2)) ∘ B = u := by
    funext q
    dsimp [B]
    rw [smul_inv_smul₀ hr.ne', add_sub_cancel]
  rwa [heq] at hcomp

end DifferentialGeometry.Analysis.Parabolic
