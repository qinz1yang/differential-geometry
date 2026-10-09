/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import DifferentialGeometry.Geometry.Conformal.Euclidean.BoundaryRealization
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Boundary.RescalingCompactness
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Dynamics.FrameRecurrence
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Dynamics.MovingFrameTensor

noncomputable section

open Set Filter MeasureTheory
open DifferentialGeometry.ProjectiveOrthogonalGroup
open scoped Topology

namespace DifferentialGeometry.RecurrentBoundaryRigidity

open HyperbolicBoundary Horospherical EuclideanBoundary GeodesicFlow
open BoundaryChartAction BoundaryChartConformal MovingFrameTensor
open LorentzGenerators DifferentialGeometry.HomogeneousSpaceMeasure RecurrentFrames

variable {m : ℕ}

local instance : MulAction (IsometryGroup m) (BoundaryH (m + 1)) :=
  poBoundaryMulAction (by omega)
local instance : ContinuousSMul (IsometryGroup m) (BoundaryH (m + 1)) :=
  ⟨continuous_po_boundary (by omega)⟩

theorem tendsto_rescaled_at_zero (F : Horizontal m → Horizontal m)
    {A : Horizontal m →L[ℝ] Horizontal m} (hF : HasFDerivAt F A 0)
    {k : ℕ → ℕ} (hk : StrictMono k) (x : Horizontal m) :
    Tendsto (fun j => Real.exp (k j : ℝ) •
      (F (Real.exp (-(k j : ℝ)) • x) - F 0)) atTop (𝓝 (A x)) := by
  have ht : Tendsto (fun j => Real.exp (-(k j : ℝ))) atTop (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_natCast_atTop_atTop.comp hk.tendsto_atTop),
      Eventually.of_forall (fun j => Real.exp_pos _)⟩
  simpa only [Function.comp_def, zero_add, Real.exp_neg, inv_inv] using
    (hF.hasLineDerivAt x).tendsto_slope_zero_right.comp ht

theorem exists_mobius_of_ae_conformal (hm : 1 ≤ m)
    (Γ : Subgroup (IsometryGroup m)) (disc : IsDiscrete (SetLike.coe Γ))
    (ν : Measure (FrameQuotient Γ)) [IsFiniteMeasure ν]
    (hright : ∀ g : IsometryGroup m, MeasurePreserving (right Γ g) ν ν)
    (hnull : ∀ U : Set (FrameQuotient Γ), MeasurableSet U →
      (ν U = 0 ↔ volume (DifferentialGeometry.HomogeneousSpaceMeasure.projection Γ ⁻¹' U) = 0))
    (ψ : BoundaryH (m + 1) ≃ₜ BoundaryH (m + 1))
    (ρ : Γ → IsometryGroup m) (F : Horizontal m → Horizontal m)
    (hFchart : ∀ x, embed (F x) = ψ (embed x))
    (heq : ∀ (γ : Γ) (ξ : BoundaryH (m + 1)),
      ψ ((γ : IsometryGroup m) • ξ) = ρ γ • ψ ξ)
    (hdiff : ∀ᵐ x ∂(volume : Measure (Horizontal m)), DifferentiableAt ℝ F x)
    (hconf : ∀ᵐ x ∂(volume : Measure (Horizontal m)), IsConformalMap (fderiv ℝ F x)) :
    ∃ a : IsometryGroup m, ∀ ξ : BoundaryH (m + 1), ψ ξ = a • ξ := by
  let : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  let P : IsometryGroup m → Prop := fun g =>
    g ∈ finiteFrames ∧ DifferentiableAt ℝ F (chartAction g 0) ∧
      IsConformalMap (fderiv ℝ F (chartAction g 0))
  have hP : ∀ᵐ g ∂(volume : Measure (IsometryGroup m)), P g := by
    filter_upwards [ae_finiteFrames, quasiMeasurePreserving_framePoint.ae hdiff,
      quasiMeasurePreserving_framePoint.ae hconf] with g hg hd hc
    exact ⟨hg, hd, hc⟩
  obtain ⟨g, s₀, k, γ, hg, hk, hs⟩ :=
    exists_compact_return_sequence hm Γ disc ν hright hnull P hP
  let A : Horizontal m →L[ℝ] Horizontal m :=
    (fderiv ℝ F (chartAction g 0)).comp (fderiv ℝ (chartAction g) 0)
  let H : Horizontal m → Horizontal m := fun x => F (chartAction g x)
  have hH : HasFDerivAt H A 0 :=
    hg.2.1.hasFDerivAt.comp 0 (differentiableAt_chartAction g hg.1).hasFDerivAt
  have hA : IsConformalMap A := hg.2.2.comp (isConformalMap_fderiv_chartAction g hg.1)
  obtain ⟨r, hr⟩ := DifferentialGeometry.LiouvilleBoundary.realizedByPo_similarity_of_isConformalMap hA (0 : Horizontal m)
  have hrE (x : Horizontal m) : r • embed x = embed (A x) := by
    have h := hr (DifferentialGeometry.LiouvilleBoundary.eucEquiv x)
    simp only [ContinuousLinearEquiv.symm_apply_apply, add_zero] at h
    exact h
  let y : Horizontal m := H 0
  let s : ℕ → IsometryGroup m :=
    fun j => (γ j : IsometryGroup m) * g * GeodesicFlow.diagonal (-(k j : ℝ))
  let b : ℕ → IsometryGroup m := fun j =>
    GeodesicFlow.diagonal (k j : ℝ) * translation (fun i => (-y) i) * (ρ (γ j))⁻¹
  apply BoundaryBlowupCompactness.exists_mobius_of_normalized_limit hm ψ r (s := s) (b := b) hs
  intro x
  have ht : Tendsto (fun j => Real.exp (-(k j : ℝ))) atTop (𝓝 (0 : ℝ)) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_natCast_atTop_atTop.comp hk.tendsto_atTop)
  have hx : ∀ᶠ j in atTop, Real.exp (-(k j : ℝ)) • x ∈ chartDomain g := by
    have htx : Tendsto (fun j => Real.exp (-(k j : ℝ)) • x) atTop (𝓝 0) := by
      simpa only [zero_smul] using ht.smul_const x
    exact htx ((isOpen_chartDomain g).mem_nhds hg.1)
  have hdiag (t : ℝ) (z : Horizontal m) :
      GeodesicFlow.diagonal t • embed z = embed (Real.exp t • z) :=
    diagonal_horo t (fun i => z i)
  have he : (fun j => b j • ψ (s j • embed x)) =ᶠ[atTop]
      (fun j => embed (Real.exp (k j : ℝ) • (H (Real.exp (-(k j : ℝ)) • x) - y))) := by
    filter_upwards [hx] with j hj
    simp only [b, s, mul_smul]
    rw [heq (γ j), inv_smul_smul, hdiag,
      ← embed_chartAction g hj, ← hFchart]
    rw [BoundaryMeasure.translation_embed, hdiag]
    simp only [H, sub_eq_add_neg]
  have hlimit := continuous_embed.tendsto (A x) |>.comp (tendsto_rescaled_at_zero H hH hk x)
  have hlimit' : Tendsto (fun j => embed (Real.exp (k j : ℝ) •
      (H (Real.exp (-(k j : ℝ)) • x) - y))) atTop (𝓝 (r • embed x)) := by
    rw [hrE]
    exact hlimit
  exact hlimit'.congr' he.symm

end DifferentialGeometry.RecurrentBoundaryRigidity
