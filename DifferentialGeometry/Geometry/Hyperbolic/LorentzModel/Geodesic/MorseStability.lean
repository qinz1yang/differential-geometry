/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Boundary.Extension
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Geodesic.Projection

open DifferentialGeometry.ProjectiveOrthogonalGroup Filter

namespace DifferentialGeometry.MorseStability

open DifferentialGeometry.Hyperbolic DifferentialGeometry.HyperbolicFaithful DifferentialGeometry.HyperbolicBoundary
open DifferentialGeometry.BoundaryTopology DifferentialGeometry.HyperbolicConvexity DifferentialGeometry.GromovBoundary
open DifferentialGeometry.AsymptoticRays DifferentialGeometry.GeodesicProjection DifferentialGeometry.BoundaryExtension

variable {n : ℕ}

def OnSegment (x y w : HUpper n) : Prop := dist x w + dist w y = dist x y

theorem onSegment_geodFromTo {x y : HUpper n} (hd : x ≠ y) {t : ℝ} (ht0 : 0 ≤ t)
    (htT : t ≤ dist x y) : OnSegment x y (geodFromTo x y hd t) := by
  have hwx : dist x (geodFromTo x y hd t) = t := by
    have h1 : dist (geodFromTo x y hd 0) (geodFromTo x y hd t) = |0 - t| :=
      dist_geodFromTo hd 0 t
    rw [geodFromTo_zero hd, zero_sub, abs_neg, abs_of_nonneg ht0] at h1
    exact h1
  have hwy : dist (geodFromTo x y hd t) y = dist x y - t := by
    have h1 : dist (geodFromTo x y hd t) (geodFromTo x y hd (dist x y)) = |t - dist x y| :=
      dist_geodFromTo hd t _
    rw [geodFromTo_dist hd, abs_of_nonpos (by linarith : t - dist x y ≤ 0)] at h1
    linarith [h1]
  unfold OnSegment
  rw [hwx, hwy]
  ring

theorem isQuasiGeodesic_image_ray {K C : ℝ} {Φ : HUpper n → HUpper n}
    (hΦ : PseudoIsometry.IsPseudoIsometry K C Φ) (o : HUpper n) (ξ : BoundaryH n)
    (s t : ℝ) :
    K⁻¹ * |s - t| - C ≤ dist (Φ (rayTo o ξ s)) (Φ (rayTo o ξ t))
      ∧ dist (Φ (rayTo o ξ s)) (Φ (rayTo o ξ t)) ≤ K * |s - t| + C := by
  have hdist : dist (rayTo o ξ s) (rayTo o ξ t) = |s - t| := dist_rayTo o ξ s t
  constructor
  · have h := hΦ.lower (rayTo o ξ s) (rayTo o ξ t)
    rw [hdist] at h; exact h
  · have h := hΦ.upper (rayTo o ξ s) (rayTo o ξ t)
    rw [hdist] at h; exact h

theorem sdot_eTime_left (v : LorVec n) : sdot (eTime : LorVec n) v = 0 := by
  unfold sdot
  exact Finset.sum_eq_zero fun i _ => by rw [eTime_apply_inl, zero_mul]

theorem lorB_eTime_boundary (ξ : BoundaryH n) : lorB (eTime : LorVec n) ξ.val = -1 := by
  change sdot (eTime : LorVec n) ξ.val - tc eTime * tc ξ.val = -1
  rw [sdot_eTime_left, tc_eTime, ξ.tc_eq]
  norm_num

theorem dirTo_basepointH (ξ : BoundaryH n) : dirTo basepointH ξ = spatialEmbed (spatial ξ) := by
  have hlor : lorB basepointH.val ξ.val = -1 := by
    change lorB (eTime : LorVec n) ξ.val = -1
    exact lorB_eTime_boundary ξ
  have hval : ξ.val = eTime + spatialEmbed (spatial ξ) := by
    funext a
    rcases a with i | k
    · rw [Pi.add_apply, eTime_apply_inl, spatialEmbed_inl, spatial_apply, zero_add]
    · have hk0 : k = 0 := Subsingleton.elim k 0
      subst hk0
      rw [Pi.add_apply, eTime_apply_inr, spatialEmbed_inr, add_zero]
      exact ξ.tc_eq
  unfold dirTo
  rw [hlor]
  have h1 : ((-(-1))⁻¹ : ℝ) = 1 := by norm_num
  rw [h1, one_smul]
  change ξ.val + (-1 : ℝ) • (eTime : LorVec n) = spatialEmbed (spatial ξ)
  rw [hval, neg_one_smul]
  abel

theorem rayTo_basepointH_eq_geodesicRay (ξ : BoundaryH n) (t : ℝ) :
    rayTo basepointH ξ t = geodesicRay ξ t := by
  apply HUpper.ext
  have h : (basepointH.val : LorVec n) = eTime := rfl
  change Real.cosh t • (basepointH.val : LorVec n) + Real.sinh t • dirTo basepointH ξ
    = Real.cosh t • eTime + Real.sinh t • spatialEmbed (spatial ξ)
  rw [h, dirTo_basepointH]

theorem gromovCauchy_image_ray_of_onSegment_tendsto {K C : ℝ} {Φ : HUpper n → HUpper n}
    (hΦ : PseudoIsometry.IsPseudoIsometry K C Φ) {o : HUpper n} {ξ : BoundaryH n}
    (hseg : ∀ M : ℝ, ∃ N : ℕ, ∀ s ≥ N, ∀ t ≥ N, ∀ w : HUpper n,
      OnSegment (Φ (rayTo o ξ (s : ℝ))) (Φ (rayTo o ξ (t : ℝ))) w → M ≤ dist (Φ o) w) :
    GromovCauchy o (fun m : ℕ => Φ (rayTo o ξ (m : ℝ))) := by
  have hdiv0 : Tendsto (fun m : ℕ => dist o (rayTo o ξ (m : ℝ))) atTop atTop := by
    have heq : (fun m : ℕ => dist o (rayTo o ξ (m : ℝ))) = fun m : ℕ => (m : ℝ) := by
      funext m
      rw [dist_rayTo_self, abs_of_nonneg (Nat.cast_nonneg m)]
    rw [heq]
    exact tendsto_natCast_atTop_atTop
  have hdiv : Tendsto (fun m : ℕ => dist (Φ o) (Φ (rayTo o ξ (m : ℝ)))) atTop atTop :=
    tendsto_atTop_of_isPseudoIsometry hΦ hdiv0
  have hdivB : ∀ B : ℝ, ∃ N : ℕ, ∀ m ≥ N, B ≤ dist (Φ o) (Φ (rayTo o ξ (m : ℝ))) :=
    fun B => Filter.eventually_atTop.mp (hdiv.eventually (Filter.eventually_ge_atTop B))
  have hgrom : ∀ R : ℝ, ∃ N : ℕ, ∀ m ≥ N, ∀ k ≥ N,
      R ≤ gromovProduct (Φ o) (Φ (rayTo o ξ (m : ℝ))) (Φ (rayTo o ξ (k : ℝ))) := by
    intro R
    obtain ⟨N₁, hN₁⟩ := hseg (R + Real.log 2)
    obtain ⟨N₂, hN₂⟩ := hdivB (R + Real.log 2)
    refine ⟨max N₁ N₂, fun s hs t ht => ?_⟩
    have hsN₁ : s ≥ N₁ := le_trans (le_max_left _ _) hs
    have htN₁ : t ≥ N₁ := le_trans (le_max_left _ _) ht
    have hsN₂ : s ≥ N₂ := le_trans (le_max_right _ _) hs
    by_cases hst : Φ (rayTo o ξ (s : ℝ)) = Φ (rayTo o ξ (t : ℝ))
    · have e : gromovProduct (Φ o) (Φ (rayTo o ξ (s : ℝ))) (Φ (rayTo o ξ (t : ℝ)))
          = dist (Φ o) (Φ (rayTo o ξ (s : ℝ))) := by
        rw [hst]
        unfold gromovProduct
        rw [dist_self]
        ring
      rw [e]
      have h := hN₂ s hsN₂
      linarith [h, Real.log_nonneg one_le_two]
    · have h := gromovProduct_ge_of_forall_dist_ge (Φ o) _ _ hst
        (fun τ hτ0 hτT => hN₁ s hsN₁ t htN₁ _ (onSegment_geodFromTo hst hτ0 hτT))
      linarith [h, Real.log_nonneg one_le_two]
  have hGC : GromovCauchy (Φ o) (fun m : ℕ => Φ (rayTo o ξ (m : ℝ))) := ⟨hdiv, hgrom⟩
  exact hGC.of_basepoint o

theorem exists_equivariant_boundary_extension_of_onSegment_tendsto
    {Γ Λ : Subgroup (PO n 1)} {f : Γ ≃* Λ} {K C : ℝ} {Φ : HUpper n → HUpper n}
    (hΦ : PseudoIsometry.IsPseudoIsometry K C Φ) (hn : 1 ≤ n)
    (hf : PseudoIsometry.IsFEquivariant f hn Φ)
    (hseg : ∀ (o : HUpper n) (ξ : BoundaryH n) (M : ℝ), ∃ N : ℕ, ∀ s ≥ N, ∀ t ≥ N,
      ∀ w : HUpper n,
      OnSegment (Φ (rayTo o ξ (s : ℝ))) (Φ (rayTo o ξ (t : ℝ))) w → M ≤ dist (Φ o) w) :
    ∃ φ : BoundaryH n → BoundaryH n,
      (∀ (γ : Γ) (ξ : BoundaryH n),
        φ ((poBoundaryMulAction hn).smul (γ : PO n 1) ξ)
          = (poBoundaryMulAction hn).smul (f γ : PO n 1) (φ ξ))
      ∧ (∀ ξ : BoundaryH n,
          ConvergesToBoundary (fun m : ℕ => Φ (geodesicRay ξ (m : ℝ))) (φ ξ)) := by
  have hGC : ∀ (o : HUpper n) (ξ : BoundaryH n),
      GromovCauchy o (fun m : ℕ => Φ (rayTo o ξ (m : ℝ))) :=
    fun o ξ => gromovCauchy_image_ray_of_onSegment_tendsto hΦ (hseg o ξ)
  refine ⟨bExt hGC, fun γ ξ => bExt_equivariant hΦ hGC hn hf γ ξ, fun ξ => ?_⟩
  have h := bExt_spec hGC ξ
  have h2 : (fun m : ℕ => Φ (rayTo basepointH ξ (m : ℝ)))
      = (fun m : ℕ => Φ (geodesicRay ξ (m : ℝ))) := by
    funext m
    rw [rayTo_basepointH_eq_geodesicRay]
  rwa [h2] at h

end DifferentialGeometry.MorseStability
