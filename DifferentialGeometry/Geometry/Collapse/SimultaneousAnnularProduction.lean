import DifferentialGeometry.Geometry.Collapse.AnnularAdaptedCoordinates
import DifferentialGeometry.Geometry.Collapse.DistanceSmoothing.RadialFunction

/-!
# One produced radial smoothing on every annular normalized ball

The LC67 function is chosen once before all shell points and rescalings. Every adapted
coordinate uses that same function and the original distance coordinate of the same cone.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Metric
open scoped Topology ContDiff Manifold ENNReal
open GC.MetricGeometry
open DifferentialGeometry
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Operator

namespace DifferentialGeometry.Geometry.Collapse

universe u v

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

section Alignment

variable {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem simultaneousMetricAlignment (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g) :
    ∀ a b : M, riemannianEDistOf g a b = ENNReal.ofReal (dist a b) := by
  intro a b
  rw [riemannianEDistOf_eq_riemannianEDist g hEnorm,
    ← IsRiemannianManifold.out (I := I), edist_dist]

end Alignment

theorem exists_simultaneous_annular_radial_production {β ζ : ℝ}
    (hβ : 0 < β) (hβζ : β < ζ) (hζone : ζ < 1) :
    ∃ ε δstar Λstar : ℝ, 0 < ε ∧ ε < 1 / 4 ∧ 0 < δstar ∧ 0 < Λstar ∧
      ∀ (M : Type u) [m : MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
        [SigmaCompactSpace M] [CompleteSpace M] [ConnectedSpace M]
        [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
        [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
        (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g) (p : M),
      (∀ y ∈ ball p 400, SectionalBoundedBelowAt g y (-((1 / 60) ^ 2))) →
      ∀ (C : Type v) [MetricSpace C] (o : C), RadialConeData o →
      ∀ {δ : ℝ}, KleinerLottApprox p o δ → δ < δstar →
      ∀ e : ℝ, 0 < e → e < 1 / 40 →
      ∃ η : M → ℝ, LipschitzWith (Real.toNNReal (1 + ε)) η ∧
        (∃ O : Set M, IsOpen O ∧ {x : M | 3 / 40 ≤ dist x p ∧ dist x p ≤ 11} ⊆ O ∧
          ContMDiffOn I 𝓘(ℝ, ℝ) ∞ η O) ∧
        (∀ x, |η x - infDist x {p}| < e) ∧
        (∀ x, x ∉ {x : M | 1 / 20 < dist x p ∧ dist x p < 20} → η x = infDist x {p}) ∧
        (∀ x y, |(η x - infDist x {p}) - (η y - infDist y {p})| ≤ ε * dist x y) ∧
        (∀ x, 0 ≤ η x) ∧ η p = 0 ∧
        (∀ q ∈ {x : M | 1 / 10 ≤ dist x p ∧ dist x p ≤ 10},
          1 - ε ≤ Real.sqrt (g.inner q (gradFun g η q) (gradFun g η q)) ∧
            Real.sqrt (g.inner q (gradFun g η q) (gradFun g η q)) ≤ 1 + ε) ∧
        (∀ x, η x ∈ Icc (1 / 5 : ℝ) 2 → 1 / 5 - e < dist x p ∧ dist x p < 2 + e) ∧
        η ⁻¹' Icc (1 / 5 : ℝ) 2 ⊆ {x : M | 1 / 10 ≤ dist x p ∧ dist x p ≤ 10} ∧
        (∃ O' : Set M, IsOpen O' ∧ η ⁻¹' Icc (1 / 5 : ℝ) 2 ⊆ O' ∧
          ContMDiffOn I 𝓘(ℝ, ℝ) ∞ η O' ∧ ∀ q ∈ O', gradFun g η q ≠ 0) ∧
      ∀ q : M, 1 / 10 ≤ dist p q → dist p q ≤ 10 →
      ∀ (lam : ℝ) (hlam : 0 < lam), Λstar ≤ lam →
      let hmetric := simultaneousMetricAlignment g hEnorm
      let := m.rescale lam hlam
      letI := (m.rescale_completeSpace_iff lam hlam).mpr inferInstance
      letI := radialScaledBundle g lam hlam
      letI := radialScaledContinuous g lam hlam
      letI := radialScaledManifold (m := m) g hmetric lam hlam
      let h := scaleMetric (lam ^ 2) (pow_pos hlam 2) g
      let ψ := fun x => lam * (η x - η q)
      ∃ hEnorm : IsMetricNorm h,
        ∃ (Z : Type) (mZ : MetricSpace Z), letI := mZ
          ∃ (z : Z) (α : KleinerLottApprox q (WithLp.toLp 2 ((0 : ℝ), z)) β),
          (∀ x, (α.toFun x).fst = lam *
            (@dist M m.toDist p x - @dist M m.toDist p q)) ∧
          ContMDiffOn I 𝓘(ℝ, ℝ) ∞ ψ (ball q 1) ∧ ψ q = 0 ∧
          (∀ x ∈ ball q 1, ∀ y ∈ ball q 1, |ψ x - ψ y| ≤ (1 + ζ) * dist x y) ∧
          (∀ x ∈ ball q 1, infDist (ψ x) (Ioo (-1 : ℝ) 1) ≤ ζ) ∧
          (∀ t ∈ Ioo (-1 : ℝ) 1, infDist t (ψ '' ball q 1) ≤ ζ) ∧
          ∀ x ∈ ball q 1, ∀ y ∈ ball q ζ⁻¹, 1 < dist x y →
            ∀ w : TangentSpace I x, h.inner x w w = 1 →
            intrinsicGeodesic h hEnorm x w (dist x y) = y →
            |mvfderiv (I := I) ψ x w -
              ((α.toFun y).fst - (α.toFun x).fst) / dist x y| < ζ := by
  obtain ⟨ε, δ₀, Λstar, hε, hεquarter, hδ₀, hΛstar, hadapt⟩ :=
    exists_prescribed_annular_adapted_parameters (I := I) hβ hβζ hζone
  refine ⟨ε, min δ₀ (radialSmoothingConeError (ε / 4)), Λstar, hε, hεquarter,
    lt_min hδ₀ (radialSmoothingConeError_pos (by positivity)), hΛstar, ?_⟩
  intro M m cM sM scM cmM coM rM rmM crM g hEnorm p hsec C mC o H δ φ hδ e he heforty
  obtain ⟨η, hLip, ⟨O, hO, hbuffer, hη⟩, hclose, hout, herr,
    hnonneg, hzero, hgrad, hlevel, hsublevel, hregular⟩ :=
    exists_buffered_radialFunction_of_kleinerLottApprox g hEnorm φ H hsec hε
      (by linarith) (hδ.trans_le (min_le_right _ _)) he heforty
  refine ⟨η, hLip, ⟨O, hO, hbuffer, hη⟩, hclose, hout, herr, hnonneg,
    hzero, hgrad, hlevel, hsublevel, hregular, ?_⟩
  intro q hqlo hqhi lam hlam hΛ
  exact hadapt M g (simultaneousMetricAlignment g hEnorm) p hsec C o H φ
    (hδ.trans_le (min_le_left _ _)) η (hη.mono hbuffer)
    (by intro x y; simpa only [Metric.infDist_singleton, dist_comm x p, dist_comm y p]
        using herr x y) q hqlo hqhi lam hlam hΛ

end DifferentialGeometry.Geometry.Collapse
