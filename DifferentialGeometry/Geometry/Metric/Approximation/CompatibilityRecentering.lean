import DifferentialGeometry.Geometry.Metric.Approximation.NormalizedSplittingRecentering
import DifferentialGeometry.Geometry.Metric.Approximation.DirectedSplittingCompatibility

set_option autoImplicit false

namespace GC.MetricGeometry

open Set Metric

private theorem product_change_bound
    {U V A B : Type*} [MetricSpace A] [MetricSpace B]
    (f f' : U → A) (g g' : V → B) (u₀ : U) (v₀ : V) (a : A) (b : B)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hf : ∀ u, dist (f' u) (f u) ≤ dist (f u₀) a)
    (hg : ∀ v, dist (g' v) (g v) ≤ dist (g v₀) b)
    (hbase : dist (WithLp.toLp 2 (f u₀, g v₀)) (WithLp.toLp 2 (a, b)) ≤ ε)
    (u : U) (v : V) :
    dist (WithLp.toLp 2 (f' u, g' v)) (WithLp.toLp 2 (f u, g v)) ≤ ε := by
  have h₁ := WithLp.prod_dist_sq_eq_add_sq (WithLp.toLp 2 (f' u, g' v))
    (WithLp.toLp 2 (f u, g v))
  have h₂ := WithLp.prod_dist_sq_eq_add_sq (WithLp.toLp 2 (f u₀, g v₀))
    (WithLp.toLp 2 (a, b))
  simp only [WithLp.toLp_fst, WithLp.toLp_snd] at h₁ h₂
  have hfsq := (sq_le_sq₀ dist_nonneg dist_nonneg).mpr (hf u)
  have hgsq := (sq_le_sq₀ dist_nonneg dist_nonneg).mpr (hg v)
  have hbsq := (sq_le_sq₀ dist_nonneg hε).mpr hbase
  apply (sq_le_sq₀ dist_nonneg hε).mp
  linarith

private theorem recenter_original_ball_guard {ε δ C : ℝ}
    (hε : 0 < ε) (hδ : 0 < δ) (hC : 0 ≤ C)
    (hbound : ε ≤ recenterTolerance δ (C + 1)) :
    C + δ⁻¹ < ε⁻¹ := by
  have hi : 0 < δ⁻¹ := inv_pos.mpr hδ
  have hR : 0 < C + 1 + δ⁻¹ + 2 := by linarith
  have heR : ε ≤ (100 * (C + 1 + δ⁻¹ + 2))⁻¹ := by
    simpa only [one_div] using hbound.trans (min_le_right _ _)
  have hh := (inv_le_inv₀ (by positivity : 0 < (100 * (C + 1 + δ⁻¹ + 2))⁻¹) hε).mpr heR
  rw [inv_inv] at hh
  linarith

end GC.MetricGeometry

namespace GC.MetricGeometry

open Set Metric

variable {X A B : Type*} [MetricSpace X] [MetricSpace A] [MetricSpace B]
variable {p c : X} {a : A} {b : B} {j k : ℕ} {ε δ C : ℝ}

theorem exists_recentered_splitting_compatibility_witnesses
    (φ : KleinerLottApprox p (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin j)), a)) ε)
    (ψ : KleinerLottApprox p (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin k)), b)) ε)
    (Q : EuclideanSpace ℝ (Fin k) ≃ₗᵢ[ℝ]
      WithLp 2 (EuclideanSpace ℝ (Fin j) × EuclideanSpace ℝ (Fin (k - j))))
    (E : KleinerLottApprox (0 : EuclideanSpace ℝ (Fin j)) 0 ε)
    (F : KleinerLottApprox
      (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin (k - j))), b)) a ε)
    (hcomp : ∀ x ∈ ball p ε⁻¹,
      dist (WithLp.toLp 2 (E.toFun (Q (ψ.toFun x).fst).fst,
        F.toFun (WithLp.toLp 2 ((Q (ψ.toFun x).fst).snd, (ψ.toFun x).snd))))
        (φ.toFun x) ≤ ε)
    (hδ : 0 < δ) (hδone : δ < 1) (hC : 0 ≤ C)
    (hε : ε ≤ recenterTolerance δ (C + 1)) (hc : dist p c ≤ C) :
    ∃ (Ec : KleinerLottApprox (0 : EuclideanSpace ℝ (Fin j)) 0 δ)
      (Fc : KleinerLottApprox
        (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin (k - j))), (ψ.toFun c).snd))
        (φ.toFun c).snd δ),
      ∀ x ∈ ball c δ⁻¹,
        dist (WithLp.toLp 2
          (Ec.toFun (Q ((ψ.toFun x).fst - (ψ.toFun c).fst)).fst,
            Fc.toFun (WithLp.toLp 2 ((Q ((ψ.toFun x).fst - (ψ.toFun c).fst)).snd,
              (ψ.toFun x).snd))))
          (WithLp.toLp 2 ((φ.toFun x).fst - (φ.toFun c).fst, (φ.toFun x).snd)) < δ := by
  have hC1 : 0 ≤ C + 1 := by linarith
  have hi : 0 < δ⁻¹ := inv_pos.mpr hδ
  have hguard := recenter_original_ball_guard φ.error_pos hδ hC hε
  have hc' : dist c p ≤ C := by simpa only [dist_comm] using hc
  have hcold : c ∈ ball p ε⁻¹ := by change dist c p < ε⁻¹; linarith
  let tc := (Q (ψ.toFun c).fst).fst
  let sc := (Q (ψ.toFun c).fst).snd
  let rc := WithLp.toLp 2 (sc, (ψ.toFun c).snd)
  let uc := (φ.toFun c).fst
  let zc := (φ.toFun c).snd
  let L := (IsometryEquiv.withLpProdCongr 2 Q.toIsometryEquiv (IsometryEquiv.refl B)).trans
    (IsometryEquiv.withLpProdAssoc 2 (EuclideanSpace ℝ (Fin j))
      (EuclideanSpace ℝ (Fin (k - j))) B)
  have hLbase : L (WithLp.toLp 2 (0, b)) = WithLp.toLp 2 (0, WithLp.toLp 2 (0, b)) := by
    change WithLp.toLp 2 ((Q 0).fst, WithLp.toLp 2 ((Q 0).snd, b)) = _
    rw [map_zero]
    rfl
  have hrad := (abs_le.mp (ψ.radial_error c hcold)).2
  have htc : dist (0 : EuclideanSpace ℝ (Fin j)) tc ≤ C + 1 := by
    have hh := WithLp.dist_fst_le (L (ψ.toFun c)) (L (WithLp.toLp 2 (0, b)))
    rw [L.dist_eq, hLbase] at hh
    change dist tc 0 ≤ _ at hh
    rw [dist_comm 0 tc]
    linarith [ψ.error_lt_one]
  have hrc : dist (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin (k - j))), b)) rc ≤ C + 1 := by
    have hh := WithLp.dist_snd_le (L (ψ.toFun c)) (L (WithLp.toLp 2 (0, b)))
    rw [L.dist_eq, hLbase] at hh
    change dist rc (WithLp.toLp 2 (0, b)) ≤ _ at hh
    rw [dist_comm]
    linarith [ψ.error_lt_one]
  have hcenter := hcomp c hcold
  have hE : dist (E.toFun tc) uc ≤ ε :=
    (WithLp.dist_fst_le _ _).trans hcenter
  have hF : dist (F.toFun rc) zc ≤ ε :=
    (WithLp.dist_snd_le _ _).trans hcenter
  let Er := E.recenterWithTarget tc uc hδ hδone hC1 hε htc hE
  let Fr := F.recenterWithTarget rc zc hδ hδone hC1 hε hrc hF
  let addT : EuclideanSpace ℝ (Fin j) ≃ᵢ EuclideanSpace ℝ (Fin j) :=
    IsometryEquiv.addRight tc
  have hAddT : addT 0 = tc := by change 0 + tc = tc; exact zero_add tc
  let Ec : KleinerLottApprox (0 : EuclideanSpace ℝ (Fin j))
      (0 : EuclideanSpace ℝ (Fin j)) δ :=
    (Er.comapSourceIsometryAt addT 0 hAddT).mapTargetIsometryAt
      (IsometryEquiv.subRight uc) 0 (by change uc - uc = 0; exact sub_self uc)
  have hEc (t : EuclideanSpace ℝ (Fin j)) : Ec.toFun t = Er.toFun (t + tc) - uc := rfl
  let addS : WithLp 2 (EuclideanSpace ℝ (Fin (k - j)) × B) ≃ᵢ
      WithLp 2 (EuclideanSpace ℝ (Fin (k - j)) × B) :=
    IsometryEquiv.withLpProdCongr 2 (IsometryEquiv.addRight sc) (IsometryEquiv.refl B)
  have hAddS : addS (WithLp.toLp 2 (0, (ψ.toFun c).snd)) = rc := by
    change WithLp.toLp 2 (0 + sc, (ψ.toFun c).snd) = _
    rw [zero_add]
  let Fc := Fr.comapSourceIsometryAt addS (WithLp.toLp 2 (0, (ψ.toFun c).snd)) hAddS
  have hFc (s : EuclideanSpace ℝ (Fin (k - j))) (v : B) :
      Fc.toFun (WithLp.toLp 2 (s, v)) = Fr.toFun (WithLp.toLp 2 (s + sc, v)) := rfl
  have hrepair (t : EuclideanSpace ℝ (Fin j)) (r : WithLp 2 (EuclideanSpace ℝ (Fin (k - j)) × B)) :
      dist (WithLp.toLp 2 (Er.toFun t, Fr.toFun r))
        (WithLp.toLp 2 (E.toFun t, F.toFun r)) ≤ ε := by
    apply product_change_bound E.toFun Er.toFun F.toFun Fr.toFun tc rc uc zc φ.error_pos.le
    · exact E.recenterWithTarget_dist_le tc uc hδ hδone hC1 hε htc hE
    · exact F.recenterWithTarget_dist_le rc zc hδ hδone hC1 hε hrc hF
    · exact hcenter
  refine ⟨Ec, Fc, ?_⟩
  intro x hx
  have hxold : x ∈ ball p ε⁻¹ := by
    have ht := dist_triangle x c p
    change dist x p < ε⁻¹
    have hxc : dist x c < δ⁻¹ := hx
    linarith
  rw [hEc, hFc]
  simp only [map_sub, WithLp.sub_fst, WithLp.sub_snd]
  change dist (WithLp.toLp 2
      (Er.toFun (((Q (ψ.toFun x).fst).fst - tc) + tc) - uc,
        Fr.toFun (WithLp.toLp 2 (((Q (ψ.toFun x).fst).snd - sc) + sc, (ψ.toFun x).snd))))
    (WithLp.toLp 2 ((φ.toFun x).fst - uc, (φ.toFun x).snd)) < δ
  rw [sub_add_cancel, sub_add_cancel]
  let T := IsometryEquiv.withLpProdCongr 2 (IsometryEquiv.subRight uc) (IsometryEquiv.refl A)
  change dist (T (WithLp.toLp 2 (Er.toFun (Q (ψ.toFun x).fst).fst,
      Fr.toFun (WithLp.toLp 2 ((Q (ψ.toFun x).fst).snd, (ψ.toFun x).snd)))))
    (T (φ.toFun x)) < δ
  rw [T.dist_eq]
  have ht := dist_triangle
    (WithLp.toLp 2 (Er.toFun (Q (ψ.toFun x).fst).fst,
      Fr.toFun (WithLp.toLp 2 ((Q (ψ.toFun x).fst).snd, (ψ.toFun x).snd))))
    (WithLp.toLp 2 (E.toFun (Q (ψ.toFun x).fst).fst,
      F.toFun (WithLp.toLp 2 ((Q (ψ.toFun x).fst).snd, (ψ.toFun x).snd)))) (φ.toFun x)
  have heδ : ε ≤ δ / 100 := hε.trans (min_le_left _ _)
  linarith [hrepair (Q (ψ.toFun x).fst).fst
    (WithLp.toLp 2 ((Q (ψ.toFun x).fst).snd, (ψ.toFun x).snd)), hcomp x hxold]

end GC.MetricGeometry

namespace GC.MetricGeometry

open Set Metric

variable {X A B : Type*} [MetricSpace X] [MetricSpace A] [MetricSpace B]
variable {p : X} {a : A} {b : B} {j k : ℕ} {ε δ C : ℝ}

theorem SplittingCompatible.recenterEuclidean
    {φ : KleinerLottApprox p (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin j)), a)) ε}
    {ψ : KleinerLottApprox p (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin k)), b)) ε}
    (hcomp : SplittingCompatible φ ψ ε) (c : X)
    (hδ : 0 < δ) (hδone : δ < 1) (hC : 0 ≤ C)
    (hε : ε ≤ recenterTolerance δ (C + 1)) (hc : dist p c ≤ C) :
    SplittingCompatible
      (φ.recenterEuclidean c hδ hδone (hC.trans (le_add_of_nonneg_right zero_le_one))
        hε (hc.trans (le_add_of_nonneg_right zero_le_one)))
      (ψ.recenterEuclidean c hδ hδone (hC.trans (le_add_of_nonneg_right zero_le_one))
        hε (hc.trans (le_add_of_nonneg_right zero_le_one))) δ := by
  obtain ⟨hjk, Q, E, F, hcompat⟩ := hcomp
  obtain ⟨Ec, Fc, hnew⟩ := exists_recentered_splitting_compatibility_witnesses
    φ ψ Q E F hcompat hδ hδone hC hε hc
  refine ⟨hjk, Q, Ec, Fc, ?_⟩
  intro x hx
  simpa only [KleinerLottApprox.recenterEuclidean_apply,
    WithLp.toLp_fst, WithLp.toLp_snd] using (hnew x hx).le

end GC.MetricGeometry
