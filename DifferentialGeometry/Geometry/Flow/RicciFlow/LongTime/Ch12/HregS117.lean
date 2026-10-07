import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedGeom_S117
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedPieces_S107
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HimproveEvent_S107

set_option autoImplicit false

/-!
# CH12-S117 / G1b: `hreg` (regular-time step of `himprove`), the LTF03 seed argument

`hreg_S117` : at a regular time `s ∈ [t, 2t]` with `Weak η` on `[t, s]`, `Weak (η/2)` holds at `s`.
Proof: lift of the survival at `s` (`exists_lift_of_surv_S93`), `(1/4) h ≤ s⁻¹ φ^*g_s ≤ 3 h` on `B = ball (2R)`
(`metric_compare_S107`), the geometry of `f = ψ_{last} ∘ φ` near the base point (`seed_geom_S117`), the seed
`(sectional ≥ -(a₀²)⁻¹, volume ≥ v a₀³)` at `p' = f o` (`sectional_seed_S107`) and the K-level LTF03 threshold `hK`
on `B_{gb}(p', 4R)` (tracked points of `x ∈ B` are exactly `f x`, `tracked_unique_S70`).
-/

noncomputable section

open Set Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Geometry.Curvature
  DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Geometry.Hyperbolic
  DifferentialGeometry.Geometry.Collapse GC.LongTime
open scoped Manifold ContDiff Topology ENNReal

namespace GC.LongTime.Ch12

universe u

theorem hreg_S117 (H : FiniteVolumeHyperbolicModel.{u}) (K : ObservedHistory.{u})
    (j0 : Fin (K.eventCount + 1)) (J : H.Carrier → (K.stage j0).Carrier) {R η t a₀ v T' : ℝ}
    (hR : 0 < R) (hη1 : η ≤ 1) (ht0 : 0 < t) (h2t : 2 * t ≤ K.horizon)
    (hj0 : actS_S70 K t = j0) (ha₀ : 0 < a₀) (ha₀R : a₀ ≤ R / 8) (ha₀1 : 189 * a₀ ^ 2 ≤ 1)
    (hv : ENNReal.ofReal (v * a₀ ^ 3) ≤
      ENNReal.ofReal (1 / 8) * ballVolume H.metric H.basepoint (a₀ / 2))
    (hJ : ContMDiffOn ThreeModel ThreeModel ∞ J (riemannianBallOf H.metric H.basepoint (2 * R)))
    (hJinj : Set.InjOn J (riemannianBallOf H.metric H.basepoint (2 * R)))
    (hck : ∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * R),
      ckErr_S45 H (K.stageMetric j0 t) t⁻¹ J 0 p < 1 / 2)
    (hTt : T' ≤ t)
    (hK : ∀ s' : ℝ, T' ≤ s' → ∀ hs' : 0 < s', s' ≤ K.horizon → K.time (actS_S70 K s') < s' →
      ∀ p' : (K.stage (actS_S70 K s')).Carrier,
        (∀ q ∈ riemannianBallOf
            (scaleMetric s'⁻¹ (inv_pos.mpr hs') (K.stageMetric (actS_S70 K s') s')) p' a₀,
          SectionalBoundedBelowAt
            (scaleMetric s'⁻¹ (inv_pos.mpr hs') (K.stageMetric (actS_S70 K s') s')) q
            (-(a₀ ^ 2)⁻¹)) →
        ENNReal.ofReal (v * a₀ ^ 3) ≤
          ballVolume (scaleMetric s'⁻¹ (inv_pos.mpr hs') (K.stageMetric (actS_S70 K s') s')) p' a₀ →
        ∀ q ∈ riemannianBallOf
            (scaleMetric s'⁻¹ (inv_pos.mpr hs') (K.stageMetric (actS_S70 K s') s')) p' (4 * R),
          ∀ V : TangentSpace ThreeModel q,
            |2 * s' * ricciTensor (K.stageMetric (actS_S70 K s') s') q V V +
                (K.stageMetric (actS_S70 K s') s').inner q V V| ≤
              (η / 2) * (K.stageMetric (actS_S70 K s') s').inner q V V) :
    ∀ s ∈ Icc t (2 * t), K.time (actS_S70 K s) < s →
      (∀ r ∈ Icc t s,
        WeakAt_S85 K j0 J (riemannianBallOf H.metric H.basepoint (2 * R)) η r) →
      WeakAt_S85 K j0 J (riemannianBallOf H.metric H.basepoint (2 * R)) (η / 2) s := by
  intro s hs hreg hW
  have hBopen : IsOpen (riemannianBallOf H.metric H.basepoint (2 * R)) :=
    isOpen_riemannianBallOf_S61 H _
  have hs0 : 0 < s := ht0.trans_le hs.1
  have hsh : s ≤ K.horizon := hs.2.trans h2t
  have hnon : (riemannianBallOf H.metric H.basepoint (2 * R)).Nonempty := by
    refine ⟨H.basepoint, ?_⟩
    change riemannianEDistOf H.metric H.basepoint H.basepoint < _
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr (mul_pos two_pos hR)
  have hWs := hW s ⟨hs.1, le_rfl⟩
  obtain ⟨hle, φ, hφ, hφall⟩ := exists_lift_of_surv_S93 H K j0 J
    ⟨riemannianBallOf H.metric H.basepoint (2 * R), hBopen⟩ hJ hnon hWs.1
  have hcmp := metric_compare_S107 H K j0 J ht0 hs.1 hs.2 hsh hη1 hj0 (last := actS_S70 K s) rfl hle
    hBopen (fun r hr => (hW r hr).2) φ hφ (fun p hp => (hφall p hp).1) hck
  -- the map `f = ψ_last ∘ φ` into the active stage and the normalised metric
  let f : H.Carrier → (K.stage (actS_S70 K s)).Carrier := fun p => (φ p).val
  let gb := scaleMetric s⁻¹ (inv_pos.mpr hs0) (K.stageMetric (actS_S70 K s) s)
  have hdf : ∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * R), ∀ w : TangentSpace (𝓡 3) p,
      mfderiv (𝓡 3) (𝓡 3) f p w = mfderiv (𝓡 3) (𝓡 3) φ p w := by
    intro p hp w
    have hφd : MDifferentiableAt (𝓡 3) (𝓡 3) φ p :=
      (hφ.contMDiffAt (hBopen.mem_nhds hp)).mdifferentiableAt (by decide)
    have hval := (hasMFDerivAt_subtype_val (I := 𝓡 3) (K.backwardSurvivorDomain j0 (actS_S70 K s) hle)
      (φ p)).mdifferentiableAt
    have hc : mfderiv (𝓡 3) (𝓡 3) f p =
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : K.backwardSurvivorDomain j0 (actS_S70 K s) hle → _)
          (φ p)).comp (mfderiv (𝓡 3) (𝓡 3) φ p) := mfderiv_comp p hval hφd
    rw [hc]
    simp only [ContinuousLinearMap.comp_apply, mfderiv_subtype_val_apply]
    rfl
  have hgb : ∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * R), ∀ w : TangentSpace (𝓡 3) p,
      gb.inner (f p) (mfderiv (𝓡 3) (𝓡 3) f p w) (mfderiv (𝓡 3) (𝓡 3) f p w) =
        s⁻¹ * (K.stageMetric (actS_S70 K s) s).inner (φ p).val
          (mfderiv ThreeModel ThreeModel φ p w) (mfderiv ThreeModel ThreeModel φ p w) := by
    intro p hp w
    rw [hdf p hp w]
    exact scaleMetric_inner _ _ _ _ _ _
  have hlow : ∀ p ∈ ((⟨riemannianBallOf H.metric H.basepoint (2 * R), hBopen⟩ :
      TopologicalSpace.Opens H.Carrier) : Set H.Carrier), ∀ w : TangentSpace (𝓡 3) p,
      (1 / 4 : ℝ) * H.metric.inner p w w ≤
        gb.inner (f p) (mfderiv (𝓡 3) (𝓡 3) f p w) (mfderiv (𝓡 3) (𝓡 3) f p w) := by
    intro p hp w
    rw [hgb p hp w]
    exact (hcmp p hp w).1
  have hup : ∀ p ∈ ((⟨riemannianBallOf H.metric H.basepoint (2 * R), hBopen⟩ :
      TopologicalSpace.Opens H.Carrier) : Set H.Carrier), ∀ w : TangentSpace (𝓡 3) p,
      gb.inner (f p) (mfderiv (𝓡 3) (𝓡 3) f p w) (mfderiv (𝓡 3) (𝓡 3) f p w) ≤
        3 * H.metric.inner p w w := by
    intro p hp w
    rw [hgb p hp w]
    exact (hcmp p hp w).2
  have hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f (riemannianBallOf H.metric H.basepoint (2 * R)) :=
    contMDiff_subtype_val.comp_contMDiffOn hφ
  have hinj : Set.InjOn f (riemannianBallOf H.metric H.basepoint (2 * R)) := by
    intro p hp q hq hpq
    have h1 : φ p = φ q := Subtype.ext hpq
    exact hJinj hp hq (by rw [← (hφall p hp).1, ← (hφall q hq).1, h1])
  obtain ⟨hcov, hvol, hlip⟩ := seed_geom_S117 H gb f
    ⟨riemannianBallOf H.metric H.basepoint (2 * R), hBopen⟩ hf hinj hlow hup ha₀ ha₀R subset_rfl
  -- the seed at `p' = f o`
  have hsect : ∀ q ∈ riemannianBallOf gb (f H.basepoint) a₀,
      SectionalBoundedBelowAt gb q (-(a₀ ^ 2)⁻¹) := by
    intro q hq
    obtain ⟨p, hp, rfl⟩ := hcov hq
    exact sectional_seed_S107 K (actS_S70 K s) hs0 hη1 (f p)
      (fun V => hWs.2 hle p hp (φ p).val (hφall p hp).2 V) ha₀ ha₀1
  have hK3 := hK s (hTt.trans hs.1) hs0 hsh hreg (f H.basepoint) hsect (hv.trans hvol)
  refine ⟨⟨hle, fun x hx => ⟨_, (hφall x hx).2⟩⟩, ?_⟩
  intro h' x hx z hz V
  have hzf : z = f x := tracked_unique_S70 K h' J x hz (hφall x hx).2
  subst hzf
  exact hK3 (f x) (hlip x hx) V

end GC.LongTime.Ch12
