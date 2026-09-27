import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardSolution

set_option autoImplicit false
noncomputable section
open Set DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff ENNReal
namespace DifferentialGeometry.PDE.RicciFlow
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

def IsUniformStandardLifetime (τ : ℝ) : Prop :=
  0 < τ ∧ ∀ θ : ℝ, 0 ≤ θ → θ < τ →
    (∀ S : StandardSolution, ENNReal.ofReal θ < S.val.lifetime) ∧
    ∃ K : ℝ, 0 ≤ K ∧ ∀ S : StandardSolution, ∀ t ∈ Icc 0 θ, ∀ x : E3,
      Real.sqrt (normSq0S (S.val.metric t) x 4 (metricRm04 (S.val.metric t) x)) ≤ K

def uniformStandardLifetime : ℝ≥0∞ :=
  ⨆ τ : {τ : ℝ // IsUniformStandardLifetime τ}, ENNReal.ofReal τ.val

theorem IsUniformStandardLifetime.mono {τ τ' : ℝ} (h : IsUniformStandardLifetime τ)
    (hτ' : 0 < τ') (hle : τ' ≤ τ) : IsUniformStandardLifetime τ' :=
  ⟨hτ', fun θ hθ hθτ => h.2 θ hθ (hθτ.trans_le hle)⟩

theorem le_uniformStandardLifetime (τ : ℝ) (hτ : IsUniformStandardLifetime τ) :
    ENNReal.ofReal τ ≤ uniformStandardLifetime :=
  le_iSup (fun r : {r : ℝ // IsUniformStandardLifetime r} => ENNReal.ofReal r.val) ⟨τ, hτ⟩

theorem uniformStandardLifetime_slab (θ : ℝ) (hθ : 0 ≤ θ)
    (hlt : ENNReal.ofReal θ < uniformStandardLifetime) :
    (∀ S : StandardSolution, ENNReal.ofReal θ < S.val.lifetime) ∧
    ∃ K : ℝ, 0 ≤ K ∧ ∀ S : StandardSolution, ∀ t ∈ Icc 0 θ, ∀ x : E3,
      Real.sqrt (normSq0S (S.val.metric t) x 4 (metricRm04 (S.val.metric t) x)) ≤ K := by
  obtain ⟨τ, hτ⟩ := lt_iSup_iff.mp hlt
  exact τ.property.2 θ hθ ((ENNReal.ofReal_lt_ofReal_iff τ.property.1).mp hτ)

theorem uniformStandardLifetime_le_lifetime (S : StandardSolution) :
    uniformStandardLifetime ≤ S.val.lifetime := by
  by_contra hn
  obtain ⟨θ, hθ, hST, hθT⟩ := ENNReal.lt_iff_exists_real_btwn.mp (lt_of_not_ge hn)
  exact (not_lt_of_gt hST) ((uniformStandardLifetime_slab θ hθ hθT).1 S)

theorem isUniformStandardLifetime_iff (τ : ℝ) :
    IsUniformStandardLifetime τ ↔ 0 < τ ∧ ENNReal.ofReal τ ≤ uniformStandardLifetime := by
  constructor
  · intro h
    exact ⟨h.1, le_uniformStandardLifetime τ h⟩
  · rintro ⟨hτ, hle⟩
    refine ⟨hτ, ?_⟩
    intro θ hθ hθτ
    exact uniformStandardLifetime_slab θ hθ
      (((ENNReal.ofReal_lt_ofReal_iff hτ).mpr hθτ).trans_le hle)

theorem uniformStandardLifetime_pos_iff :
    0 < uniformStandardLifetime ↔ ∃ τ : ℝ, IsUniformStandardLifetime τ := by
  constructor
  · intro h
    obtain ⟨τ, _⟩ := lt_iSup_iff.mp h
    exact ⟨τ.val, τ.property⟩
  · rintro ⟨τ, hτ⟩
    exact (ENNReal.ofReal_pos.mpr hτ.1).trans_le (le_uniformStandardLifetime τ hτ)
end DifferentialGeometry.PDE.RicciFlow
