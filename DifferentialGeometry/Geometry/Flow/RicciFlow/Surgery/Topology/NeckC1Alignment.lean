import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ChartTailHornBridge
import DifferentialGeometry.Geometry.Metric.CylinderAxial
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CylinderAxialNormalization
import DifferentialGeometry.Topology.Manifold.OpenSubtype

set_option autoImplicit false

noncomputable section

open Set Bundle Manifold Function
open DifferentialGeometry DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

private local instance : Fact (Module.finrank ℝ ThreeSpace = 2 + 1) := ⟨by simp [ThreeSpace]⟩

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold ThreeModel ∞ M] [T2Space M]

def NormalizedNeck.normalizedAxial {g : SmoothRiemannianMetric ThreeModel M} {δ : ℝ} {k : ℕ}
    (N : NormalizedNeck g δ k) (x : neckBuffer δ) : ℝ :=
  (Real.sqrt N.scale)⁻¹ * x.1.2

def cylinderAxialAlignment {δ : ℝ}
    (gD : SmoothRiemannianMetric NeckCylinderModel (neckBuffer δ)) (A : Set (neckBuffer δ))
    (Φ : neckBuffer δ → NeckCylinder) (lam σ c C : ℝ) : Prop :=
  (σ = 1 ∨ σ = -1) ∧
  (∀ x ∈ A, |x.1.2 - σ * lam * (Φ x).2 - c| ≤ C) ∧
  (∀ x ∈ A, ∀ V : TangentSpace NeckCylinderModel x,
    |V.2 - σ * lam * (mfderiv NeckCylinderModel NeckCylinderModel Φ x V).2| ≤
      C * Real.sqrt (gD.inner x V V))

def neckOverlapC1Bound {g : SmoothRiemannianMetric ThreeModel M}
    {δ₁ δ₂ : ℝ} {k₁ k₂ : ℕ}
    (N₁ : NormalizedNeck g δ₁ k₁) (N₂ : NormalizedNeck g δ₂ k₂)
    (Φ : neckBuffer δ₁ → neckBuffer δ₂) (A₁ : Set (neckBuffer δ₁))
    (σ c C : ℝ) : Prop :=
  cylinderAxialAlignment N₁.normalizedMetric A₁ (fun x => (Φ x).1)
    (Real.sqrt (N₁.scale / N₂.scale)) σ c C

omit [T2Space M] in
theorem neckOverlapC1Bound_mono {g : SmoothRiemannianMetric ThreeModel M} {δ₁ δ₂ : ℝ}
    {k₁ k₂ : ℕ} {N₁ : NormalizedNeck g δ₁ k₁} {N₂ : NormalizedNeck g δ₂ k₂}
    {Φ : neckBuffer δ₁ → neckBuffer δ₂} {A₁ : Set (neckBuffer δ₁)} {σ c C C' : ℝ}
    (h : neckOverlapC1Bound N₁ N₂ Φ A₁ σ c C) (hCC : C ≤ C') :
    neckOverlapC1Bound N₁ N₂ Φ A₁ σ c C' := by
  obtain ⟨hσ, h0, h1⟩ := h
  refine ⟨hσ, fun x hx => (h0 x hx).trans hCC, fun x hx V => ?_⟩
  exact (h1 x hx V).trans (mul_le_mul_of_nonneg_right hCC (Real.sqrt_nonneg _))

theorem mfderiv_subtypeVal_comp_opens {δ : ℝ} (Φ : NeckCylinder → NeckCylinder)
    (hΦ : ∀ x : neckBuffer δ, MDifferentiableAt NeckCylinderModel NeckCylinderModel Φ x.1)
    (x : neckBuffer δ) (V : TangentSpace NeckCylinderModel x) :
    mfderiv NeckCylinderModel NeckCylinderModel (Φ ∘ Subtype.val) x V =
      mfderiv NeckCylinderModel NeckCylinderModel Φ x.1 V := by
  have hval : MDifferentiableAt NeckCylinderModel NeckCylinderModel
      (Subtype.val : neckBuffer δ → NeckCylinder) x :=
    (hasMFDerivAt_subtype_val (I := NeckCylinderModel) (neckBuffer δ) x).mdifferentiableAt
  have hcomp := mfderiv_comp_apply (x := x) (f := (Subtype.val : neckBuffer δ → NeckCylinder))
    (g := Φ) (hΦ x) hval V
  simpa only [mfderiv_subtype_val_apply] using hcomp

theorem cylinderAxialAlignment_axialDiffeomorph {δ : ℝ} (A : Set (neckBuffer δ))
    (a σ : ℝ) (hσ : σ ^ 2 = 1) :
    cylinderAxialAlignment (roundCylinderMetric.restrictOpen (neckBuffer δ)) A
      ((Geometry.Metric.cylinderAxialDiffeomorph (I := 𝓡 2) a σ hσ) ∘ Subtype.val)
      1 σ (-(σ * a)) 0 := by
  have hd : ∀ x : neckBuffer δ, MDifferentiableAt NeckCylinderModel NeckCylinderModel
      (Geometry.Metric.cylinderAxialDiffeomorph (I := 𝓡 2) a σ hσ) x.1 := fun x =>
    (Geometry.Metric.cylinderAxialDiffeomorph (I := 𝓡 2) a σ hσ).contMDiff_toFun
      |>.mdifferentiableAt (by simp)
  have hσmul : σ * σ = 1 := by rw [← sq, hσ]
  refine ⟨?_, ?_, ?_⟩
  · rcases sq_eq_one_iff.mp hσ with h | h <;> simp [h]
  · intro x _
    have h2 : x.1.2 - σ * 1 *
        (((Geometry.Metric.cylinderAxialDiffeomorph (I := 𝓡 2) a σ hσ) ∘ Subtype.val :
          neckBuffer δ → NeckCylinder) x).2 - (-(σ * a)) = 0 := by
      simp only [Function.comp_apply, Geometry.Metric.cylinderAxialDiffeomorph_apply]
      have key : σ * (σ * x.1.2) = x.1.2 := by rw [← mul_assoc, hσmul, one_mul]
      calc x.1.2 - σ * 1 * (a + σ * x.1.2) - (-(σ * a))
          = x.1.2 - (σ * a + σ * (σ * x.1.2)) + σ * a := by ring
        _ = x.1.2 - (σ * a + x.1.2) + σ * a := by rw [key]
        _ = 0 := by ring
    rw [h2, abs_zero]
  · intro x _ V
    have hmf : (mfderiv NeckCylinderModel NeckCylinderModel
        ((Geometry.Metric.cylinderAxialDiffeomorph (I := 𝓡 2) a σ hσ) ∘ Subtype.val) x V).2 =
        σ * V.2 := by
      rw [mfderiv_subtypeVal_comp_opens _ hd x V]
      exact congrArg Prod.snd
        (Geometry.Metric.cylinderAxialDiffeomorph_mfderiv (I := 𝓡 2) a σ hσ x.1 V)
    rw [hmf]
    have hzero : V.2 - σ * 1 * (σ * V.2) = 0 := by
      have key : σ * (σ * V.2) = V.2 := by rw [← mul_assoc, hσmul, one_mul]
      calc V.2 - σ * 1 * (σ * V.2) = V.2 - σ * (σ * V.2) := by ring
        _ = V.2 - V.2 := by rw [key]
        _ = 0 := by ring
    rw [hzero, abs_zero, zero_mul]

theorem cylinderAxialAlignment_axialScale {δ : ℝ} (A : Set (neckBuffer δ))
    {R : ℝ} (hR : ∀ x ∈ A, |x.1.2| ≤ R) (c₀ : ℝ) (hc₀ : c₀ ≠ 0) :
    cylinderAxialAlignment (roundCylinderMetric.restrictOpen (neckBuffer δ)) A
      ((Perelman.KappaSolutions.cylinderAxialScale c₀ hc₀) ∘ Subtype.val) 1 1 0
      (|c₀ - 1| * max 1 R) := by
  have hd : ∀ x : neckBuffer δ, MDifferentiableAt NeckCylinderModel NeckCylinderModel
      (Perelman.KappaSolutions.cylinderAxialScale c₀ hc₀) x.1 := fun x =>
    (Perelman.KappaSolutions.cylinderAxialScale c₀ hc₀).contMDiff_toFun
      |>.mdifferentiableAt (by simp)
  refine ⟨Or.inl rfl, ?_, ?_⟩
  · intro x hx
    have h2 : x.1.2 - 1 * 1 *
        (((Perelman.KappaSolutions.cylinderAxialScale c₀ hc₀) ∘ Subtype.val :
          neckBuffer δ → NeckCylinder) x).2 - 0 = (1 - c₀) * x.1.2 := by
      simp only [Function.comp_apply, Perelman.KappaSolutions.cylinderAxialScale_apply]
      ring
    rw [h2, abs_mul, abs_sub_comm (1 : ℝ) c₀]
    exact mul_le_mul_of_nonneg_left ((hR x hx).trans (le_max_right _ _)) (abs_nonneg _)
  · intro x hx V
    have hmf : (mfderiv NeckCylinderModel NeckCylinderModel
        ((Perelman.KappaSolutions.cylinderAxialScale c₀ hc₀) ∘ Subtype.val) x V).2 =
        c₀ * V.2 := by
      rw [mfderiv_subtypeVal_comp_opens _ hd x V]
      exact congrArg Prod.snd
        (Perelman.KappaSolutions.cylinderAxialScale_mfderiv c₀ hc₀ x.1 V)
    have h2 : V.2 - 1 * 1 * (c₀ * V.2) = (1 - c₀) * V.2 := by ring
    rw [hmf, h2, abs_mul, abs_sub_comm (1 : ℝ) c₀]
    have hV : |V.2| ≤ Real.sqrt (roundCylinderMetric.inner x.1 V V) := by
      have hval : roundCylinderMetric.inner x.1 V V =
          2 * inner ℝ (dIncl (E := ThreeSpace) (n := 2) x.1.1 V.1)
            (dIncl (E := ThreeSpace) (n := 2) x.1.1 V.1) + V.2 * V.2 := by
        rw [roundCylinderMetric_eq_geometry]
        exact Geometry.Metric.roundCylinderMetric_inner x.1 V V
      rw [hval]
      have hnn : 0 ≤ 2 * inner ℝ (dIncl (E := ThreeSpace) (n := 2) x.1.1 V.1)
          (dIncl (E := ThreeSpace) (n := 2) x.1.1 V.1) := by
        have hpos := real_inner_self_nonneg
          (x := dIncl (E := ThreeSpace) (n := 2) x.1.1 V.1)
        linarith
      have hsq : V.2 * V.2 ≤ 2 * inner ℝ (dIncl (E := ThreeSpace) (n := 2) x.1.1 V.1)
          (dIncl (E := ThreeSpace) (n := 2) x.1.1 V.1) + V.2 * V.2 := by linarith
      calc |V.2| = Real.sqrt (V.2 ^ 2) := (Real.sqrt_sq_eq_abs V.2).symm
        _ = Real.sqrt (V.2 * V.2) := by rw [sq]
        _ ≤ Real.sqrt (2 * inner ℝ (dIncl (E := ThreeSpace) (n := 2) x.1.1 V.1)
              (dIncl (E := ThreeSpace) (n := 2) x.1.1 V.1) + V.2 * V.2) :=
            Real.sqrt_le_sqrt hsq
    have hm : |c₀ - 1| ≤ (|c₀ - 1| * max 1 R) := by
      conv_lhs => rw [← mul_one |c₀ - 1|]
      exact mul_le_mul_of_nonneg_left (le_max_left (1 : ℝ) R) (abs_nonneg _)
    calc |c₀ - 1| * |V.2|
        ≤ |c₀ - 1| * Real.sqrt (roundCylinderMetric.inner x.1 V V) :=
          mul_le_mul_of_nonneg_left hV (abs_nonneg _)
      _ ≤ (|c₀ - 1| * max 1 R) * Real.sqrt (roundCylinderMetric.inner x.1 V V) :=
          mul_le_mul_of_nonneg_right hm (Real.sqrt_nonneg _)

theorem not_cylinderAxialAlignment_axialScale_zero {δ : ℝ} (A : Set (neckBuffer δ))
    {c₀ : ℝ} (hc₀ : c₀ ≠ 0) (hc₁ : c₀ ≠ 1) (hne : ∃ x ∈ A, x.1.2 ≠ 0) :
    ¬ cylinderAxialAlignment (roundCylinderMetric.restrictOpen (neckBuffer δ)) A
      ((Perelman.KappaSolutions.cylinderAxialScale c₀ hc₀) ∘ Subtype.val) 1 1 0 0 := by
  rintro ⟨-, h0, -⟩
  obtain ⟨x, hx, hxne⟩ := hne
  have h := h0 x hx
  have h3 : x.1.2 - 1 * 1 *
      (((Perelman.KappaSolutions.cylinderAxialScale c₀ hc₀) ∘ Subtype.val :
        neckBuffer δ → NeckCylinder) x).2 - 0 = x.1.2 * (1 - c₀) := by
    simp only [Function.comp_apply, Perelman.KappaSolutions.cylinderAxialScale_apply]
    ring
  rw [h3, abs_nonpos_iff] at h
  have hc : (1 : ℝ) - c₀ ≠ 0 := sub_ne_zero.mpr (Ne.symm hc₁)
  rcases mul_eq_zero.mp h with h' | h'
  · exact hxne h'
  · exact absurd h' hc

omit [T2Space M] in
theorem neckOverlapC1Bound_self {g : SmoothRiemannianMetric ThreeModel M} {δ : ℝ} {k : ℕ}
    (N : NormalizedNeck g δ k) (A₁ : Set (neckBuffer δ)) :
    neckOverlapC1Bound N N id A₁ 1 0 0 := by
  have hlam : Real.sqrt (N.scale / N.scale) = 1 := by
    rw [div_self (ne_of_gt N.scale_pos), Real.sqrt_one]
  rw [neckOverlapC1Bound, hlam]
  refine ⟨Or.inl rfl, ?_, ?_⟩
  · intro x _
    simp
  · intro x _ V
    have hfun : (fun y : neckBuffer δ => ((id y : neckBuffer δ) : NeckCylinder)) =
        (Subtype.val : neckBuffer δ → NeckCylinder) := rfl
    have hval : (mfderiv NeckCylinderModel NeckCylinderModel
        (fun y : neckBuffer δ => ((id y : neckBuffer δ) : NeckCylinder)) x V).2 = V.2 := by
      rw [hfun, mfderiv_subtype_val_apply (I := NeckCylinderModel) (neckBuffer δ) x V]
    rw [hval]
    simp

omit [T2Space M] in
theorem NormalizedNeck.normalizedMetric_inner_of_common_chart
    {g : SmoothRiemannianMetric ThreeModel M} {δ₁ δ₂ : ℝ} {k₁ k₂ : ℕ}
    (N₁ : NormalizedNeck g δ₁ k₁) (N₂ : NormalizedNeck g δ₂ k₂)
    {x₁ : neckBuffer δ₁} {x₂ : neckBuffer δ₂}
    (hcommon : N₂.chart x₂ = N₁.chart x₁)
    (V₁ W₁ : TangentSpace NeckCylinderModel x₁)
    (V₂ W₂ : TangentSpace NeckCylinderModel x₂)
    (hV : mfderiv NeckCylinderModel ThreeModel (N₂.chart : neckBuffer δ₂ → M) x₂ V₂ =
      mfderiv NeckCylinderModel ThreeModel (N₁.chart : neckBuffer δ₁ → M) x₁ V₁)
    (hW : mfderiv NeckCylinderModel ThreeModel (N₂.chart : neckBuffer δ₂ → M) x₂ W₂ =
      mfderiv NeckCylinderModel ThreeModel (N₁.chart : neckBuffer δ₁ → M) x₁ W₁) :
    N₂.normalizedMetric.inner x₂ V₂ W₂ =
      (N₂.scale / N₁.scale) * N₁.normalizedMetric.inner x₁ V₁ W₁ := by
  rw [N₂.normalized_inner, N₁.normalized_inner, hV, hW, hcommon]
  rw [← mul_assoc, div_mul_cancel₀ _ (ne_of_gt N₁.scale_pos)]

theorem NormalizedNeck.normalizedMetric_inner_ratio_sub_one_le
    {g : SmoothRiemannianMetric ThreeModel M} {δ₁ δ₂ : ℝ} {k₁ k₂ : ℕ}
    (N₁ : NormalizedNeck g δ₁ k₁) (N₂ : NormalizedNeck g δ₂ k₂)
    (hk₁ : 2 ≤ k₁) (hk₂ : 2 ≤ k₂) (hd₁ : δ₁ ≤ 1 / 2) (hd₂ : δ₂ ≤ 1 / 2)
    {x₁ : neckBuffer δ₁} {x₂ : neckBuffer δ₂}
    (hx₁ : x₁ ∈ neckClosedTest δ₁) (hx₂ : x₂ ∈ neckClosedTest δ₂)
    (hcommon : N₂.chart x₂ = N₁.chart x₁)
    (hsmall : 4323 * max δ₁ δ₂ ≤ 1 / 2)
    (V₁ W₁ : TangentSpace NeckCylinderModel x₁)
    (V₂ W₂ : TangentSpace NeckCylinderModel x₂)
    (hV : mfderiv NeckCylinderModel ThreeModel (N₂.chart : neckBuffer δ₂ → M) x₂ V₂ =
      mfderiv NeckCylinderModel ThreeModel (N₁.chart : neckBuffer δ₁ → M) x₁ V₁)
    (hW : mfderiv NeckCylinderModel ThreeModel (N₂.chart : neckBuffer δ₂ → M) x₂ W₂ =
      mfderiv NeckCylinderModel ThreeModel (N₁.chart : neckBuffer δ₁ → M) x₁ W₁)
    (hne : N₂.normalizedMetric.inner x₂ V₂ W₂ ≠ 0) :
    |N₁.normalizedMetric.inner x₁ V₁ W₁
        / N₂.normalizedMetric.inner x₂ V₂ W₂ - 1| ≤ 17292 * max δ₁ δ₂ := by
  have hhom := NormalizedNeck.normalizedMetric_inner_of_common_chart N₁ N₂ hcommon
    V₁ W₁ V₂ W₂ hV hW
  have hratio := NormalizedNeck.scale_ratio_of_common_point N₁ N₂ hk₁ hk₂ hd₁ hd₂
    hx₁ hx₂ hcommon.symm hsmall
  rw [hhom]
  have hinner₁ : N₁.normalizedMetric.inner x₁ V₁ W₁ ≠ 0 := by
    intro h0
    exact hne (by rw [hhom, h0, mul_zero])
  have hdiv : N₁.normalizedMetric.inner x₁ V₁ W₁ /
      (N₂.scale / N₁.scale * N₁.normalizedMetric.inner x₁ V₁ W₁) =
      N₁.scale / N₂.scale := by
    field_simp
  rw [hdiv]
  exact hratio

theorem NormalizedNeck.abs_sqrt_scale_ratio_sub_one_le
    {g : SmoothRiemannianMetric ThreeModel M} {δ₁ δ₂ : ℝ} {k₁ k₂ : ℕ}
    (N₁ : NormalizedNeck g δ₁ k₁) (N₂ : NormalizedNeck g δ₂ k₂)
    (hk₁ : 2 ≤ k₁) (hk₂ : 2 ≤ k₂) (hd₁ : δ₁ ≤ 1 / 2) (hd₂ : δ₂ ≤ 1 / 2)
    {x₁ : neckBuffer δ₁} {x₂ : neckBuffer δ₂}
    (hx₁ : x₁ ∈ neckClosedTest δ₁) (hx₂ : x₂ ∈ neckClosedTest δ₂)
    (hcommon : N₁.chart x₁ = N₂.chart x₂)
    (hsmall : 4323 * max δ₁ δ₂ ≤ 1 / 2) :
    |Real.sqrt (N₁.scale / N₂.scale) - 1| ≤ 17292 * max δ₁ δ₂ := by
  have hratio := NormalizedNeck.scale_ratio_of_common_point N₁ N₂ hk₁ hk₂ hd₁ hd₂
    hx₁ hx₂ hcommon hsmall
  have hpos : 0 ≤ Real.sqrt (N₁.scale / N₂.scale) := Real.sqrt_nonneg _
  have hsq : Real.sqrt (N₁.scale / N₂.scale) * Real.sqrt (N₁.scale / N₂.scale) =
      N₁.scale / N₂.scale := by
    rw [← sq, Real.sq_sqrt (le_of_lt (div_pos N₁.scale_pos N₂.scale_pos))]
  rw [← hsq] at hratio
  have hfac : Real.sqrt (N₁.scale / N₂.scale) * Real.sqrt (N₁.scale / N₂.scale) - 1 =
      (Real.sqrt (N₁.scale / N₂.scale) - 1) * (Real.sqrt (N₁.scale / N₂.scale) + 1) := by
    ring
  rw [hfac, abs_mul] at hratio
  have hge : 1 ≤ |Real.sqrt (N₁.scale / N₂.scale) + 1| := by
    rw [abs_of_nonneg (by linarith)]
    linarith
  nlinarith [abs_nonneg (Real.sqrt (N₁.scale / N₂.scale) - 1), hratio, hge]

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
