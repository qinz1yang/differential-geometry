import DifferentialGeometry.Geometry.Metric.Cfs15StageOutputBlendBLOC
import DifferentialGeometry.Geometry.Metric.Cfs15StageOutputLocalityBLOCApplications
import DifferentialGeometry.Analysis.Calculus.Cutoff.Ball

/-!
# Consumers of the BCG04 / BCG05 blend step: explicit three-stage chains

The stage `Ψ z = z + ψ z • (a z − z)` with `Q = ⊤`, the ambient nearest map `a` of a flat stage
output and the smooth cutoff `ψ = ballCutoff x₀ (1/4) (1/2)` (closed support inside `B(x₀, 1)`,
`x₀` the centre of the cloud). Three successive stages `g₁ = Ψ u`, `g₂ = Ψ g₁`, `g₃ = Ψ g₂`:

* `flat_chain3_kernel_BLOC`: on the flat cloud in `L ≤ ker J`, `J u = 0` gives
  `J g₁ = J g₂ = J g₃ = 0` exactly and `J ≡ 0` on the segment `[u, g₃]`;
* `affineFlat_chain3_scalar_BLOC`: on the translated flat cloud with `L ≤ ker v`, `v q = 1`,
  `v u = 1` gives `v g₁ = v g₂ = v g₃ = 1` and `v ≡ 1` on `[u, g₃]`;
* explicit `ℝ²` instances on the first axis (`plane_chain3_kernel_BLOC`, input `t e₀`) and on the
  line `e₁ + ℝ e₀` (`plane_chain3_scalar_BLOC`, input `e₁ + t e₀`), second coordinate.
-/

set_option autoImplicit false

noncomputable section

open Set Metric
open DifferentialGeometry.Analysis

namespace GC.MetricGeometry

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The explicit stage map: `Q = ⊤`, smoothing map `a`, cutoff `ballCutoff x₀ (1/4) (1/2)`. -/
def explicitStage_BLOC (a : H → H) (x₀ : H) : H → H :=
  adjustmentMap (⊤ : Submodule ℝ H) (fun y => (⊤ : Submodule ℝ H).starProjection (a y))
    (ballCutoff x₀ (1 / 4) (1 / 2))

/-- The closed support of the explicit cutoff lies in `B(x₀, 1)`. -/
theorem explicitStage_tsupport_BLOC (x₀ z : H) (hz : z ∈ tsupport (ballCutoff x₀ (1 / 4) (1 / 2))) :
    (⊤ : Submodule ℝ H).starProjection z ∈ ball x₀ 1 := by
  rw [Submodule.starProjection_eq_self_iff.mpr Submodule.mem_top]
  have h := ballCutoff_tsupport_subset_closedBall (center := x₀) (r := 1 / 4) (R := 1 / 2)
    (by norm_num) (by norm_num) hz
  rw [mem_closedBall] at h
  rw [mem_ball]
  linarith

theorem top_orthogonal_le_ker_BLOC {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (J : H →L[ℝ] F) : (⊤ : Submodule ℝ H)ᗮ ≤ LinearMap.ker (J : H →ₗ[ℝ] F) := by
  rw [Submodule.top_orthogonal_eq_bot]
  exact bot_le

/-- **Three explicit stages on the flat cloud keep `J = 0` exactly** (BCG04's induction): for the
flat output on `L ∩ B̄(0, 1)` with `L ≤ ker J` and an input with `J u = 0`, the three stage outputs
and the whole segment `[u, g₃]` lie in `ker J`. -/
theorem flat_chain3_kernel_BLOC [FiniteDimensional ℝ H] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {k K : ℕ}
    {ε cw : ℝ} (L : Submodule ℝ H)
    (O : Cfs15StageOutput k K ε cw ((L : Set H) ∩ closedBall 0 1) (L : Set H) (fun _ => 1)
      (fun _ => L)) (J : H →L[ℝ] F) (hLJ : L ≤ LinearMap.ker (J : H →ₗ[ℝ] F)) (u : H)
    (hu : J u = 0) :
    J (explicitStage_BLOC O.ambient 0 u) = 0 ∧
    J (explicitStage_BLOC O.ambient 0 (explicitStage_BLOC O.ambient 0 u)) = 0 ∧
    J (explicitStage_BLOC O.ambient 0 (explicitStage_BLOC O.ambient 0
      (explicitStage_BLOC O.ambient 0 u))) = 0 ∧
    ∀ q ∈ segment ℝ u (explicitStage_BLOC O.ambient 0 (explicitStage_BLOC O.ambient 0
      (explicitStage_BLOC O.ambient 0 u))), J q = 0 := by
  have h0 : (0 : H) ∈ (L : Set H) ∩ closedBall 0 1 := ⟨L.zero_mem, mem_closedBall_self zero_le_one⟩
  have hst : ∀ z, z ∈ tsupport (ballCutoff (0 : H) (1 / 4) (1 / 2)) →
      (0 : H) ∈ (L : Set H) ∩ closedBall 0 1 ∧ (⊤ : Submodule ℝ H).starProjection z ∈ ball 0 1 ∧
      ∀ i ∈ O.I, (closedBall i (80 * ε⁻¹ * 1) ∩ ball 0 (8 * ε⁻¹ * 1)).Nonempty →
        J i = 0 ∧ L ≤ LinearMap.ker (J : H →ₗ[ℝ] F) :=
    fun z hz => ⟨h0, explicitStage_tsupport_BLOC 0 z hz,
      fun i hi _ => ⟨hLJ (O.I_subset hi).1, hLJ⟩⟩
  have h := cfs15_chain3_level_BLOC O O O ⊤ ⊤ ⊤ J (top_orthogonal_le_ker_BLOC J)
    (top_orthogonal_le_ker_BLOC J) (top_orthogonal_le_ker_BLOC J) (ballCutoff (0 : H) (1 / 4) (1 / 2))
    (ballCutoff (0 : H) (1 / 4) (1 / 2)) (ballCutoff (0 : H) (1 / 4) (1 / 2)) u 0 0 0 hu
    (hst u) (hst _) (hst _)
  exact ⟨h.1, h.2.1, h.2.2, segment_level_BLOC J hu h.2.2⟩

/-- **Three explicit stages on the translated flat cloud keep the scalar marker `= 1`** (BCG05's
induction): `L ≤ ker v`, `v q = 1`, `v u = 1` give `v g₁ = v g₂ = v g₃ = 1` and `v ≡ 1` on
`[u, g₃]`. -/
theorem affineFlat_chain3_scalar_BLOC [FiniteDimensional ℝ H] {k K : ℕ} {ε cw : ℝ} (L : Submodule ℝ H) (q : H)
    (O : Cfs15StageOutput k K ε cw ((AffineSubspace.mk' q L : Set H) ∩ closedBall q 1)
      (AffineSubspace.mk' q L : Set H) (fun _ => 1) (fun _ => L)) (v : H →L[ℝ] ℝ)
    (hLv : L ≤ LinearMap.ker (v : H →ₗ[ℝ] ℝ)) (hq : v q = 1) (u : H) (hu : v u = 1) :
    v (explicitStage_BLOC O.ambient q u) = 1 ∧
    v (explicitStage_BLOC O.ambient q (explicitStage_BLOC O.ambient q u)) = 1 ∧
    v (explicitStage_BLOC O.ambient q (explicitStage_BLOC O.ambient q
      (explicitStage_BLOC O.ambient q u))) = 1 ∧
    ∀ w ∈ segment ℝ u (explicitStage_BLOC O.ambient q (explicitStage_BLOC O.ambient q
      (explicitStage_BLOC O.ambient q u))), v w = 1 := by
  have hval : ∀ y ∈ (AffineSubspace.mk' q L : Set H), v y = 1 := fun y hy => by
    have hyq : y - q ∈ L := by
      have := AffineSubspace.mem_mk'.mp hy
      rwa [vsub_eq_sub] at this
    have h0 : v (y - q) = 0 := hLv hyq
    rw [map_sub, hq, sub_eq_zero] at h0
    exact h0
  have hq0 : q ∈ (AffineSubspace.mk' q L : Set H) ∩ closedBall q 1 :=
    ⟨AffineSubspace.self_mem_mk' q L, mem_closedBall_self zero_le_one⟩
  have hst : ∀ z, z ∈ tsupport (ballCutoff q (1 / 4) (1 / 2)) →
      q ∈ (AffineSubspace.mk' q L : Set H) ∩ closedBall q 1 ∧
      (⊤ : Submodule ℝ H).starProjection z ∈ ball q 1 ∧
      ∀ i ∈ O.I, (closedBall i (80 * ε⁻¹ * 1) ∩ ball q (8 * ε⁻¹ * 1)).Nonempty →
        v i = 1 ∧ L ≤ LinearMap.ker (v : H →ₗ[ℝ] ℝ) :=
    fun z hz => ⟨hq0, explicitStage_tsupport_BLOC q z hz,
      fun i hi _ => ⟨hval i (O.I_subset hi).1, hLv⟩⟩
  have h := cfs15_chain3_level_BLOC O O O ⊤ ⊤ ⊤ v (top_orthogonal_le_ker_BLOC v)
    (top_orthogonal_le_ker_BLOC v) (top_orthogonal_le_ker_BLOC v) (ballCutoff q (1 / 4) (1 / 2))
    (ballCutoff q (1 / 4) (1 / 2)) (ballCutoff q (1 / 4) (1 / 2)) u q q q hu
    (hst u) (hst _) (hst _)
  exact ⟨h.1, h.2.1, h.2.2, segment_level_BLOC v hu h.2.2⟩

/-- **Explicit `ℝ²` chain (BCG04 form).** The flat output on the first axis: for every input
`t e₀`, the second coordinates of `g₁, g₂, g₃` vanish exactly. -/
theorem plane_chain3_kernel_BLOC (K : ℕ) (ε : ℝ) (hε : 0 < ε) (hεsmall : ε ≤ 1 / 10) :
    ∃ cw : ℝ, 0 ≤ cw ∧ ∃ O : Cfs15StageOutput 1 K ε cw
        ((planeAxisZero_BLOC : Set (EuclideanSpace ℝ (Fin 2))) ∩ closedBall 0 1)
        (planeAxisZero_BLOC : Set (EuclideanSpace ℝ (Fin 2))) (fun _ => 1)
        (fun _ => planeAxisZero_BLOC),
      ∀ t : ℝ,
        EuclideanSpace.proj (1 : Fin 2)
            (explicitStage_BLOC O.ambient 0 (t • EuclideanSpace.single (0 : Fin 2) (1 : ℝ))) = 0 ∧
        EuclideanSpace.proj (1 : Fin 2) (explicitStage_BLOC O.ambient 0
            (explicitStage_BLOC O.ambient 0 (t • EuclideanSpace.single (0 : Fin 2) (1 : ℝ))))
          = 0 ∧
        EuclideanSpace.proj (1 : Fin 2) (explicitStage_BLOC O.ambient 0
            (explicitStage_BLOC O.ambient 0 (explicitStage_BLOC O.ambient 0
              (t • EuclideanSpace.single (0 : Fin 2) (1 : ℝ))))) = 0 := by
  obtain ⟨cw, hcw, h⟩ := exists_cfs15StageOutput_flat_C15.{0} 1 K ε hε hεsmall
  obtain ⟨O⟩ := h (EuclideanSpace ℝ (Fin 2)) planeAxisZero_BLOC finrank_planeAxisZero_BLOC
  refine ⟨cw, hcw, O, fun t => ?_⟩
  have h' := flat_chain3_kernel_BLOC planeAxisZero_BLOC O (EuclideanSpace.proj (1 : Fin 2))
    planeAxisZero_le_ker_BLOC (t • EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) (by simp)
  exact ⟨h'.1, h'.2.1, h'.2.2.1⟩

/-- **Explicit `ℝ²` chain (BCG05 form).** The translated flat output on the line `e₁ + ℝ e₀`: for
every input `e₁ + t e₀`, the second coordinates of `g₁, g₂, g₃` are exactly `1`. -/
theorem plane_chain3_scalar_BLOC (K : ℕ) (ε : ℝ) (hε : 0 < ε) (hεsmall : ε ≤ 1 / 10) :
    ∃ cw : ℝ, 0 ≤ cw ∧ ∃ O : Cfs15StageOutput 1 K ε cw
        ((AffineSubspace.mk' (EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) planeAxisZero_BLOC :
            Set (EuclideanSpace ℝ (Fin 2))) ∩
          closedBall (EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) 1)
        (AffineSubspace.mk' (EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) planeAxisZero_BLOC :
          Set (EuclideanSpace ℝ (Fin 2))) (fun _ => 1) (fun _ => planeAxisZero_BLOC),
      ∀ t : ℝ,
        EuclideanSpace.proj (1 : Fin 2) (explicitStage_BLOC O.ambient
            (EuclideanSpace.single (1 : Fin 2) (1 : ℝ))
            (EuclideanSpace.single (1 : Fin 2) (1 : ℝ) +
              t • EuclideanSpace.single (0 : Fin 2) (1 : ℝ))) = 1 ∧
        EuclideanSpace.proj (1 : Fin 2) (explicitStage_BLOC O.ambient
            (EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) (explicitStage_BLOC O.ambient
              (EuclideanSpace.single (1 : Fin 2) (1 : ℝ))
              (EuclideanSpace.single (1 : Fin 2) (1 : ℝ) +
                t • EuclideanSpace.single (0 : Fin 2) (1 : ℝ)))) = 1 ∧
        EuclideanSpace.proj (1 : Fin 2) (explicitStage_BLOC O.ambient
            (EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) (explicitStage_BLOC O.ambient
              (EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) (explicitStage_BLOC O.ambient
                (EuclideanSpace.single (1 : Fin 2) (1 : ℝ))
                (EuclideanSpace.single (1 : Fin 2) (1 : ℝ) +
                  t • EuclideanSpace.single (0 : Fin 2) (1 : ℝ))))) = 1 := by
  obtain ⟨cw, hcw, h⟩ := exists_cfs15StageOutput_affineFlat_BLOC.{0} 1 K ε hε hεsmall
  obtain ⟨O⟩ := h (EuclideanSpace ℝ (Fin 2)) planeAxisZero_BLOC
    (EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) finrank_planeAxisZero_BLOC
  refine ⟨cw, hcw, O, fun t => ?_⟩
  have h' := affineFlat_chain3_scalar_BLOC planeAxisZero_BLOC _ O (EuclideanSpace.proj (1 : Fin 2))
    planeAxisZero_le_ker_BLOC (by simp)
    (EuclideanSpace.single (1 : Fin 2) (1 : ℝ) + t • EuclideanSpace.single (0 : Fin 2) (1 : ℝ))
    (by simp)
  exact ⟨h'.1, h'.2.1, h'.2.2.1⟩

end GC.MetricGeometry
