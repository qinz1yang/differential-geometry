import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.BallCollar_S82
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CompleteGeodesic_S92
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CurveTransfer_S92
import DifferentialGeometry.Geometry.Geodesic.ParallelNormal

set_option autoImplicit false

/-!
# CH12-S92 / G3: `hCollar` for the concentric ball levels (K2)
-/

noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Geodesic DifferentialGeometry.Geometry.Riemannian.Variation
open Set TopologicalSpace Manifold Filter
open scoped Manifold ContDiff Topology
universe u
namespace GC.LongTime.Ch12

/-- the geodesic part: `γ` stays in `ballLevel j` and carries parallel orthonormal frames. -/
theorem hgeo_S92 (H : FiniteVolumeHyperbolicModel.{u}) (U : Opens H.Carrier) {R : ℝ} (hR : 0 < R)
    (hU : ∀ y : H.Carrier, y ∈ riemannianBallOf H.metric H.basepoint (2 * R) → y ∈ U) (k : ℕ) :
    ∀ j < k, ∀ x ∈ ballLevel_S82 H U R k (j + 1),
      ∀ e : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) → TangentSpace (𝓡 3) x,
      (∀ i m, (H.metric.restrictOpen U).inner x (e i) (e m) = if i = m then 1 else 0) →
      ∀ a : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))),
        ∃ (γ : ℝ → U) (hγ0 : γ 0 = x)
          (P : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) → (r : ℝ) → TangentSpace (𝓡 3) (γ r)),
          (∀ i, P i 0 = hγ0.symm ▸ e i) ∧
          (∀ s ∈ Icc (0 : ℝ) (R / (k + 1)), γ s ∈ ballLevel_S82 H U R k j ∧
            ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 3) 2 γ s ∧
            HasGeodesicEquationAt (I := 𝓡 3) (H.metric.restrictOpen U) γ s ∧
            (∀ i, DifferentiableAt ℝ (chartRepAt (I := 𝓡 3) γ (P i) s) s) ∧
            (∀ i, covDerivAlong (I := 𝓡 3) (H.metric.restrictOpen U) γ (P i) s = 0) ∧
            (∀ i m, (H.metric.restrictOpen U).inner (γ s) (P i s) (P m s) = if i = m then 1 else 0) ∧
            (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ s) (1 : ℝ) = P a s) := by
  classical
  intro j hj x hx e he a
  set ρ : ℝ := R / ((k : ℝ) + 1) with hρdef
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hρ : 0 < ρ := by positivity
  have hkρ : ((k : ℝ) + 1) * ρ = R := by rw [hρdef]; field_simp
  have hjk : ((j : ℝ) + 1) ≤ k := by exact_mod_cast hj
  have hv : H.metric.inner (x : H.Carrier) (e a) (e a) = 1 := by
    exact (he a a).trans (by simp)
  obtain ⟨Γ, hΓsm, hΓgeo, hΓ0, hΓv, hdist⟩ := exists_complete_unit_geodesic_S92 (I := 𝓡 3)
    H.metric H.complete (x : H.Carrier) (e a) hv
  -- ball membership along Γ
  have hbd : ∀ s ∈ Icc (0 : ℝ) ρ,
      Γ s ∈ riemannianBallOf H.metric H.basepoint (2 * R - j * ρ) := by
    intro s hs
    have hx' : riemannianEDistOf (I := 𝓡 3) H.metric H.basepoint (x : H.Carrier) <
        ENNReal.ofReal (2 * R - ((j + 1 : ℕ) : ℝ) * ρ) := hx
    have hr1 : 0 ≤ 2 * R - ((j + 1 : ℕ) : ℝ) * ρ := by
      push_cast; nlinarith
    have h2 := hdist s hs.1
    have hne : riemannianEDistOf (I := 𝓡 3) H.metric (x : H.Carrier) (Γ s) ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top h2
    have h3 : riemannianEDistOf (I := 𝓡 3) H.metric H.basepoint (Γ s) <
        ENNReal.ofReal (2 * R - ((j + 1 : ℕ) : ℝ) * ρ) + ENNReal.ofReal s :=
      calc _ ≤ riemannianEDistOf (I := 𝓡 3) H.metric H.basepoint (x : H.Carrier) +
            riemannianEDistOf (I := 𝓡 3) H.metric (x : H.Carrier) (Γ s) :=
          riemannianEDistOf_triangle (I := 𝓡 3) H.metric _ _ _
        _ < _ := ENNReal.add_lt_add_of_lt_of_le hne hx' h2
    rw [← ENNReal.ofReal_add hr1 hs.1] at h3
    refine h3.trans_le (ENNReal.ofReal_le_ofReal ?_)
    push_cast; nlinarith [hs.2]
  have hΓU : ∀ s ∈ Icc (0 : ℝ) ρ, Γ s ∈ U := by
    intro s hs
    refine hU _ (riemannianBallOf_mono H.metric H.basepoint ?_ (hbd s hs))
    have : (0 : ℝ) ≤ j * ρ := by positivity
    linarith
  have hxU : (x : H.Carrier) ∈ U := x.2
  let γ : ℝ → U := fun s => if h : Γ s ∈ U then ⟨Γ s, h⟩ else x
  have hval : ∀ s, Γ s ∈ U → (γ s : H.Carrier) = Γ s := fun s h => by simp [γ, h]
  have hW : IsOpen {s : ℝ | Γ s ∈ U} := U.isOpen.preimage hΓsm.continuous
  have hev : ∀ s, Γ s ∈ U → (fun r => (γ r : H.Carrier)) =ᶠ[𝓝 s] Γ := fun s hs =>
    Filter.eventually_of_mem (hW.mem_nhds hs) (fun r hr => hval r hr)
  have hγ0 : γ 0 = x := Subtype.ext (by rw [hval 0 (by rw [hΓ0]; exact hxU), hΓ0])
  have hγcont : ∀ s, Γ s ∈ U → ContinuousAt γ s := fun s hs =>
    (Topology.IsInducing.subtypeVal.continuousAt_iff).mpr
      (hΓsm.continuous.continuousAt.congr (hev s hs).symm)
  have hgeoOn : IsGeodesicOn (I := 𝓡 3) (H.metric.restrictOpen U) γ {s : ℝ | Γ s ∈ U} :=
    (geodesicOn_open_iff (I := 𝓡 3) H.metric U γ _).mpr fun t ht =>
      hasGeodesicEquationAt_congr_S92 (hev t ht) (hΓgeo t)
  have hγsm : ∀ s, Γ s ∈ U → ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 3) ∞ γ s := fun s hs =>
    DifferentialGeometry.Geometry.contMDiffAt_of_isGeodesicAt (DifferentialGeometry.Geometry.isGeodesicAt_of_isGeodesicOn (H.metric.restrictOpen U)
      (hW.mem_nhds hs) hgeoOn (fun t ht => (hγcont t ht).continuousWithinAt))
  -- parallel frames along Γ
  have hex := fun i => parallelTransport_section_contMDiffOn_Ioo H.metric Γ hΓsm hρ
    (e i : TangentSpace (𝓡 3) (Γ 0))
  choose δ hδ V hV0 hVdiff hVpar _hVsm using hex
  have hIcc : ∀ i, Icc (0 : ℝ) ρ ⊆ Ioo (-δ i) (ρ + δ i) := fun i t ht =>
    ⟨by linarith [ht.1, hδ i], by linarith [ht.2, hδ i]⟩
  have hΓ2 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 3) (2 : ℕ∞) Γ := hΓsm.of_le (by exact_mod_cast le_top)
  have hinner : ∀ i m, ∀ t ∈ Icc (0 : ℝ) ρ,
      H.metric.inner (Γ t) (V i t) (V m t) = if i = m then 1 else 0 := by
    intro i m t ht
    have h := parallel_transport_preserves_inner_product H.metric Γ (N := 2) le_rfl hΓ2
      (V i) (V m) (fun s hs => hVdiff i s (hIcc i hs)) (fun s hs => hVdiff m s (hIcc m hs))
      (fun s hs => hVpar i s (hIcc i hs)) (fun s hs => hVpar m s (hIcc m hs)) t ht
    rw [h, hV0 i, hV0 m]
    have e0 := he i m
    have gen : ∀ (q : H.Carrier) (hq : Γ 0 = q) (w w' : EuclideanSpace ℝ (Fin 3)),
        H.metric.inner (Γ 0) w w' = H.metric.inner q w w' := by
      intro q hq w w'; subst hq; rfl
    exact (gen _ hΓ0 (e i) (e m)).trans e0
  -- the velocity is the parallel field `V a`
  have hVa : ∀ t ∈ Icc (0 : ℝ) ρ, V a t = mfderiv 𝓘(ℝ, ℝ) (𝓡 3) Γ t (1 : ℝ) := by
    have hV0' : V a 0 = mfderiv 𝓘(ℝ, ℝ) (𝓡 3) Γ 0 (1 : ℝ) := (hV0 a).trans hΓv.symm
    have h1 := parallel_field_eq_section H.metric Γ hΓ2 hρ (V a) (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) Γ 0 1)
      hV0' (fun s hs => hVdiff a s (hIcc a hs)) (fun s hs => hVpar a s (hIcc a hs))
    have h2 := parallelTransportSection_velocity H.metric Γ hΓsm hρ (fun t _ => hΓgeo t)
    intro t ht
    exact (h1 t ht).trans (h2 t ht)
  refine ⟨γ, hγ0, fun i r => V i r, fun i => ?_, fun s hs => ?_⟩
  · have key : ∀ (y z : U) (h : y = z) (w : TangentSpace (𝓡 3) y),
        (h ▸ w : TangentSpace (𝓡 3) z) = w := by
      intro y z h w; subst h; rfl
    rw [key]
    exact hV0 i
  have hsU : Γ s ∈ U := hΓU s hs
  have hs0 : s ∈ Ioo (-δ a) (ρ + δ a) := hIcc a hs
  refine ⟨?_, (hγsm s hsU).of_le (by norm_num), ?_, ?_, ?_, ?_, ?_⟩
  · change (γ s : H.Carrier) ∈ riemannianBallOf H.metric H.basepoint (2 * R - ((j : ℕ) : ℝ) * (R / (k + 1)))
    rw [hval s hsU]
    exact hbd s hs
  · exact hgeoOn.hasGeodesicEquationAt hsU
  · intro i
    exact ((chartRepAt_open_S92 U γ (fun r => V i r) s (hγcont s hsU)).trans
      (chartRepAt_congr_S92 (hev s hsU) (Filter.Eventually.of_forall fun _ => rfl))).differentiableAt_iff.mpr
      (hVdiff i s (hIcc i hs))
  · intro i
    have h1 := DifferentialGeometry.Geometry.covDerivAlong_restrictOpen H.metric U γ (fun r => V i r) s (hγcont s hsU)
    have h2 := covDerivAlong_congr_S92 (g := H.metric) (γ := Γ) (γ' := Subtype.val ∘ γ)
      (V := V i) (V' := fun r => V i r) (hev s hsU) (Filter.Eventually.of_forall fun _ => rfl)
    exact h1.trans (h2.trans (hVpar i s (hIcc i hs)))
  · intro i m
    have h := hinner i m s hs
    have gen : ∀ (a b : H.Carrier) (hab : a = b) (w w' : EuclideanSpace ℝ (Fin 3)),
        H.metric.inner a w w' = H.metric.inner b w w' := by
      intro a b hab w w'; subst hab; rfl
    exact (gen _ _ (hval s hsU) _ _).trans h
  · have hmd : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 3) γ s := (hγsm s hsU).mdifferentiableAt (by simp)
    have hc := mfderiv_comp (I := 𝓘(ℝ, ℝ)) (I' := 𝓡 3) (I'' := 𝓡 3) s
      (hasMFDerivAt_subtype_val (I := 𝓡 3) U (γ s)).mdifferentiableAt hmd
    have hΓ' : mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (Subtype.val ∘ γ) s = mfderiv 𝓘(ℝ, ℝ) (𝓡 3) Γ s :=
      (hev s hsU).mfderiv_eq
    have h3 : mfderiv 𝓘(ℝ, ℝ) (𝓡 3) Γ s (1 : ℝ) = mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ s (1 : ℝ) := by
      rw [← hΓ', hc]
      exact mfderiv_subtype_val_apply (I := 𝓡 3) U (γ s) _
    exact h3.symm.trans (hVa s hs).symm

/-- **hCollar** of [FROZEN v2] CH12-S75 for `K := ballLevel_S82 H U R k`, `Nord := k`, `ℓ := R/(k+1)`. -/
theorem hCollar_S92 (H : FiniteVolumeHyperbolicModel.{u}) (U : Opens H.Carrier) {R : ℝ} (hR : 0 < R)
    (hU : ∀ y : H.Carrier, y ∈ riemannianBallOf H.metric H.basepoint (2 * R) → y ∈ U) (k : ℕ) :
    ∀ j < k, 0 < R / ((k : ℝ) + 1) ∧ ∀ x ∈ ballLevel_S82 H U R k (j + 1),
      ∀ e : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) → TangentSpace (𝓡 3) x,
      (∀ i m, (H.metric.restrictOpen U).inner x (e i) (e m) = if i = m then 1 else 0) →
      ∀ a : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))),
        ∃ (γ : ℝ → U) (hγ0 : γ 0 = x)
          (P : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) → (r : ℝ) → TangentSpace (𝓡 3) (γ r)),
          (∀ i, P i 0 = hγ0.symm ▸ e i) ∧
          (∀ s ∈ Icc (0 : ℝ) (R / ((k : ℝ) + 1)), γ s ∈ ballLevel_S82 H U R k j ∧
            ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 3) 2 γ s ∧
            HasGeodesicEquationAt (I := 𝓡 3) (H.metric.restrictOpen U) γ s ∧
            (∀ i, DifferentiableAt ℝ (chartRepAt (I := 𝓡 3) γ (P i) s) s) ∧
            (∀ i, covDerivAlong (I := 𝓡 3) (H.metric.restrictOpen U) γ (P i) s = 0) ∧
            (∀ i m, (H.metric.restrictOpen U).inner (γ s) (P i s) (P m s) = if i = m then 1 else 0) ∧
            (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ s) (1 : ℝ) = P a s) :=
  fun j hj => ⟨by positivity, hgeo_S92 H U hR hU k j hj⟩

end GC.LongTime.Ch12
