import DifferentialGeometry.Geometry.Curvature.Surface.PeriodicGaussBonnetBinding

/-!
# Periodic Gauss–Bonnet: consumers

Concrete uses of the SF5 package.

* A constant positive symmetric coefficient field on a plane is flat: its connection-form
  potentials vanish, so the divergence identity gives `K √D = 0`; the periodic kernel then gives
  `K = 0` on every pair.
* LFR17's torus clause, contrapositive form: a `C²` metric on a surface diffeomorphic to `ℝ²/ℤ²`
  with `K ≥ 0` has no plane of positive curvature.
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Function
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
/-- The connection-form potential `P` of a constant field vanishes. -/
theorem surfaceConnectionP_const (B₀ : E →L[ℝ] E →L[ℝ] ℝ) (v₁ v₂ y : E) :
    surfaceConnectionP (fun _ => B₀) v₁ v₂ y = 0 := by
  simp [surfaceConnectionP]

omit [FiniteDimensional ℝ E] in
/-- The connection-form potential `Q` of a constant field vanishes. -/
theorem surfaceConnectionQ_const (B₀ : E →L[ℝ] E →L[ℝ] ℝ) (v₁ v₂ y : E) :
    surfaceConnectionQ (fun _ => B₀) v₁ v₂ y = 0 := by
  simp [surfaceConnectionQ]

/-- **Consumer of the divergence identity and of the periodic kernel.** A constant positive
symmetric coefficient field on a plane has vanishing chart curvature on every pair. -/
theorem coefficientSectional_const_eq_zero (hE : Module.finrank ℝ E = 2)
    (B₀ : E →L[ℝ] E →L[ℝ] ℝ) (hsymm : ∀ u v, B₀ u v = B₀ v u)
    (hpos : ∀ v, v ≠ 0 → 0 < B₀ v v) (y u v : E) :
    coefficientSectional (fun _ => B₀) y u v = 0 := by
  let e := Module.finBasisOfFinrankEq ℝ E hE
  have hli : LinearIndependent ℝ ![e 0, e 1] := by
    have h := e.linearIndependent
    convert h using 1
    ext i
    fin_cases i <;> rfl
  have hb : ContDiff ℝ 2 (fun _ : E => B₀) := contDiff_const
  have hflat : ∀ z, coefficientSectional (fun _ => B₀) z (e 0) (e 1) = 0 := by
    intro z
    have hid := coefficientSectional_mul_sqrt_eq_fderiv_sub hE hb (fun _ => hsymm)
      (fun _ => hpos) hli z
    have hP : surfaceConnectionP (fun _ : E => B₀) (e 0) (e 1) = fun _ => 0 :=
      funext (surfaceConnectionP_const B₀ (e 0) (e 1))
    have hQ : surfaceConnectionQ (fun _ : E => B₀) (e 0) (e 1) = fun _ => 0 :=
      funext (surfaceConnectionQ_const B₀ (e 0) (e 1))
    simp only [hP, hQ, fderiv_fun_const, Pi.zero_apply, _root_.zero_apply, sub_self] at hid
    have hW := Real.sqrt_pos.mpr
      (surfaceGramDet_pos (b := fun _ : E => B₀) (fun _ => hsymm) (fun _ => hpos) hli z)
    exact (mul_eq_zero.mp hid).resolve_right hW.ne'
  exact coefficientSectional_eq_zero_of_periodic_of_nonneg hE hb (fun _ => hsymm)
    (fun _ => hpos) hli (fun _ => rfl) (fun _ => rfl) (fun z => (hflat z).ge) y u v

end DifferentialGeometry.Analysis

namespace Bundle.ContMDiffRiemannianMetric

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] {n : ℕ∞ω}

/-- **LFR17's torus clause, contrapositive form.** A `C²` metric with `K ≥ 0` on a surface
diffeomorphic to `ℝ²/ℤ²` has no plane of positive sectional curvature. -/
theorem not_exists_sectionalCurvature_pos_of_diffeomorph_addCircle_prod
    (hE : Module.finrank ℝ E = 2)
    (k : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) (hn : (2 : ℕ∞ω) ≤ n)
    (Φ : (AddCircle (1 : ℝ) × AddCircle (1 : ℝ)) ≃ₘ⟮𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ), I⟯ M)
    (hK : ∀ x v w, 0 ≤ k.sectionalCurvature x v w) :
    ¬∃ (x : M) (v w : TangentSpace I x), 0 < k.sectionalCurvature x v w := by
  rintro ⟨x, v, w, hpos⟩
  have h0 := sectionalCurvature_eq_zero_of_diffeomorph_addCircle_prod hE k hn Φ hK x v w
  exact hpos.ne' h0

end Bundle.ContMDiffRiemannianMetric
