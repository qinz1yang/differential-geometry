import DifferentialGeometry.Geometry.Collapse.SplittingCompatibility.RawReferenceScale
import DifferentialGeometry.Geometry.Collapse.SplittingCompatibility.RiemannianUniformCompatibility
import DifferentialGeometry.Geometry.Collapse.SplittingCompatibility.CoisometryAlignment

/-!
Original splitting coordinates at different physical scales are compared in the reference
metric by one coisometry. The curvature and exclusion parameter is chosen before the displacement
bound, and only the later raw quality depends on that bound. Translation is exactly the scaled
original coordinate at the reference centre.
-/

set_option autoImplicit false

noncomputable section

open Set Metric DifferentialGeometry
open DifferentialGeometry.Geometry.Riemannian
open scoped Manifold ContDiff

namespace GC.MetricGeometry

universe u uE uH

variable {E : Type uE} [normE : NormedAddCommGroup E] [spaceE : NormedSpace ℝ E]
    [finiteE : FiniteDimensional ℝ E] {H : Type uH} [topH : TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} [boundaryI : I.Boundaryless]

theorem exists_scaled_raw_coisometry_parameter_riemannian {j k : ℕ}
    (hj : 1 ≤ j) (hjk : j ≤ k) (hkn : k ≤ Module.finrank ℝ E)
    {τ ν a : ℝ} (hτ : 0 < τ) (hτone : τ < 1) (hν : 0 < ν) (hνone : ν < 1)
    (ha0 : 0 < a) (ha : 20 * (j : ℝ) * τ ≤ a) (ha2 : 2 * a ≤ τ⁻¹) :
    ∃ σ : ℝ, 0 < σ ∧ σ < 1 ∧ ∀ C : ℝ, 0 ≤ C → ∃ η : ℝ, 0 < η ∧
    ∀ (M : Type u) [mM : MetricSpace M] [_chartsM : ChartedSpace H M]
      [_smoothM : IsManifold I ∞ M] [_sigmaM : SigmaCompactSpace M] [_completeM : CompleteSpace M]
      (g : SmoothRiemannianMetric I M),
      (∀ x y, riemannianEDistOf g x y = ENNReal.ofReal (dist x y)) → ∀ p : M,
      (∀ y ∈ ball p σ⁻¹, SectionalBoundedBelowAt g y (-σ)) →
      (¬ ∃ (W : Type u) (mW : MetricSpace W), letI _residualExclusionMetric := mW
        ∃ w : W, Nonempty (KleinerLottApprox p
          (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin (k + 1))), w)) ν)) →
      ∀ (A B : Type u) [_mA : MetricSpace A] [_mB : MetricSpace B] (q : A) (b : B)
        (p' : M) {ε₁ ε₂ c : ℝ} (hc : 0 < c),
      (1 / 2 : ℝ) ≤ c → c ≤ 2 → dist p p' ≤ C → ε₁ ≤ η → 3 * ε₂ ≤ σ →
      ∀ (φ : @KleinerLottApprox M (WithLp 2 (EuclideanSpace ℝ (Fin j) × A))
          (mM.rescale c⁻¹ (inv_pos.mpr hc)) inferInstance p' (WithLp.toLp 2 (0, q)) ε₁)
        (ψ : KleinerLottApprox p (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin k)), b)) ε₂),
      let raw := @KleinerLottApprox.toFun M (WithLp 2 (EuclideanSpace ℝ (Fin j) × A))
        (mM.rescale c⁻¹ (inv_pos.mpr hc)) inferInstance p' (WithLp.toLp 2 (0, q)) ε₁ φ
      ∃ Λ : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin j),
      Λ.comp (ContinuousLinearMap.adjoint Λ) = ContinuousLinearMap.id ℝ _ ∧
      ∀ x ∈ ball p τ⁻¹, ‖(ψ.toFun x).fst‖ ≤ a →
        ‖c • (raw x).fst - Λ (ψ.toFun x).fst - c • (raw p).fst‖ ≤
          2 * (1 + 24 * j) * τ := by
  obtain ⟨σ, hσ, hσone, hprop⟩ :=
    exists_splitting_compatibility_parameter_riemannian.{u} (I := I) hj hjk hkn hτ hτone hν hνone
  refine ⟨σ, hσ, hσone, fun C hC =>
    ⟨rawScaleQuality σ (2 * C), rawScaleQuality_pos hσ (by positivity), ?_⟩⟩
  intro M mM chartsM smoothM sigmaM completeM g hmetric p hsec hno
    A B mA mB q b p' ε₁ ε₂ c hc hcmin hcmax hp hε₁ hε₂ φ ψ
  obtain ⟨Φ, hΦ⟩ := exists_reference_scaled_raw_splitting hc φ p hcmin hcmax hσ hσone
    C hC hp hε₁
  let raw := @KleinerLottApprox.toFun M (WithLp 2 (EuclideanSpace ℝ (Fin j) × A))
    (mM.rescale c⁻¹ (inv_pos.mpr hc)) inferInstance p' (WithLp.toLp 2 (0, q)) ε₁ φ
  let scaledResidualMetric : MetricSpace A := mA.rescale c hc
  let Ψ := ψ.weaken hε₂ hσone
  obtain ⟨Λ, d, hΛ, hal⟩ := exists_coisometry_alignment_of_splittingCompatible Φ Ψ
    (hprop M g hmetric p hsec hno A B (raw p).snd b Φ Ψ) ha0 ha ha2
  have hΦp : (Φ.toFun p).fst = 0 := by
    exact congrArg WithLp.fst Φ.basepoint
  have hΨp : (Ψ.toFun p).fst = 0 := by
    exact congrArg WithLp.fst Ψ.basepoint
  have hd : ‖d‖ ≤ (1 + 24 * j) * τ := by
    have hh := hal p (mem_ball_self (inv_pos.mpr hτ)) (by rw [hΨp]; simp [ha0.le])
    simpa only [hΦp, hΨp, map_zero, sub_self, zero_sub, norm_neg] using hh
  refine ⟨Λ, hΛ, fun x hx hxa => ?_⟩
  have hmain : ‖(Φ.toFun x).fst - Λ (Ψ.toFun x).fst‖ ≤ 2 * (1 + 24 * j) * τ := by
    calc
      _ = ‖((Φ.toFun x).fst - Λ (Ψ.toFun x).fst - d) + d‖ := by rw [sub_add_cancel]
      _ ≤ ‖(Φ.toFun x).fst - Λ (Ψ.toFun x).fst - d‖ + ‖d‖ := norm_add_le _ _
      _ ≤ (1 + 24 * j) * τ + (1 + 24 * j) * τ := add_le_add (hal x hx hxa) hd
      _ = _ := by ring
  have hcoord := congrArg WithLp.fst (hΦ x)
  change (Φ.toFun x).fst = c • ((raw x).fst - (raw p).fst) at hcoord
  rw [smul_sub] at hcoord
  change ‖c • (raw x).fst - Λ (ψ.toFun x).fst - c • (raw p).fst‖ ≤ _
  change ‖(Φ.toFun x).fst - Λ (ψ.toFun x).fst‖ ≤ _ at hmain
  rw [hcoord] at hmain
  convert hmain using 2
  abel

end GC.MetricGeometry
