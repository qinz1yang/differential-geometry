import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.PreparedCapWindowGeometry
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.WindowCurvatureBounds

set_option autoImplicit false
noncomputable section
open Set Function Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff ENNReal NNReal
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
universe u uE uH uM

theorem exists_uniform_prepared_incoming_cap_closedBall_curvature_derivative_bound
    (N : ℕ) (D r eps : ℝ) (C : ℝ≥0)
    (heps : 0 < eps) (hepssmall : eps ≤ 1 / 1000)
    (hr : StandardCap.transitionEnd + eps⁻¹ + 1 < r)
    (hfit : 64 * (r + eps⁻¹) < D) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ (
      ∀ {E : Type uE} {H : Type uH} {M : Type uM} {N : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
        [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
        [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
        [TopologicalSpace N] [ChartedSpace ThreeSpace N] [IsManifold ThreeModel ∞ N]
        [T2Space N]
        {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}
        {d : normalizedDatum g x₀ δ k} {A : ℝ} {hA : 0 < A} {D : ℝ}
        {m : ℕ} {ε : ℝ} (w : StandardCap.CanonicalStaticInsertionWitness d A hA D m ε),
        ε ≤ 1 / 2 → 2 ≤ m →
        ∀ (h : SmoothRiemannianMetric ThreeModel N) (J : standardCapWindow D → N),
        IsSmoothEmbedding ThreeModel ThreeModel ∞ J →
        ∀ q : ℝ, 0 < q →
        (∀ x v z, w.windowMetric.inner x v z =
          q * h.inner (J x) (mfderiv ThreeModel ThreeModel J x v)
            (mfderiv ThreeModel ThreeModel J x z)) →
        ∀ x : standardCapWindow D, ‖x.val‖ < D →
          |metricScalarAt h (J x)| ≤ C₀ * q) ∧
    ∃ η ε₀ δ₀ B : ℝ, 1 ≤ B ∧ 0 < η ∧ 0 < ε₀ ∧ ε₀ ≤ 1 / 2 ∧ 0 < δ₀ ∧
      ∀ {E : Type uE} {H : Type uH} {M : Type uM} [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
        [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
        [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
        {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}
        {d : normalizedDatum g x₀ δ k} {A : ℝ} {hA : 0 < A} {Dbig : ℝ} {m : ℕ} {ζ : ℝ}
        (w : StandardCap.CanonicalStaticInsertionWitness d A hA Dbig m ζ)
        (hmargin : D + 1 ≤ Dbig),
      max ⌈eps⁻¹⌉₊ N + 2 ≤ m → ζ ≤ ε₀ →
      let inc : standardCapWindow D → standardCapWindow Dbig := TopologicalSpace.Opens.inclusion
        (show standardCapWindow D ≤ standardCapWindow Dbig from by
          intro x hx
          change ‖x‖ < Dbig + 1
          change ‖x‖ < D + 1 at hx
          linarith only [hx, hmargin]);
      ∀ (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
        (s : ℝ) (G : (H.stage last).IncomingSlab (H.time last) s) (L : G.TerminalLimitMetric),
      G.flow.base.metric (H.time last) = H.initialMetric last →
      ∀ (Jbig : standardCapWindow Dbig → (H.stage first).Carrier),
      IsSmoothEmbedding ThreeModel ThreeModel ∞ Jbig →
      let J := Jbig ∘ inc;
      ∀ (q q₀ a₀ : ℝ) (hq : 0 < q), 0 < q₀ → q₀ ≤ C₀ * q → 1 ≤ a₀ * q →
      (∀ x (v z : TangentSpace ThreeModel x), w.windowMetric.inner x v z =
        q * (H.initialMetric first).inner (Jbig x) (mfderiv ThreeModel ThreeModel Jbig x v)
          (mfderiv ThreeModel ThreeModel Jbig x z)) →
      ∀ (parameters : CutoffParameters) (records : ∀ j : Fin H.eventCount, GeometricCutoffRecord H j parameters),
      (∀ x, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ x) →
      (∀ x, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) x) →
      (∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last → ∀ b, (records j).delta b ≤ δ₀) →
      (∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last →
        ∀ x : (H.stage j.castSucc).Carrier, ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
          q₀ < (H.event j).incoming.flow.scalar t x →
          |derivWithin (fun v => (H.event j).incoming.flow.scalar v x) (Iic t) t| ≤
            C * (H.event j).incoming.flow.scalar t x ^ 2) →
      (∀ x : (H.stage last).Carrier, ∀ t ∈ Ioo (H.time last) s,
        q₀ < G.flow.scalar t x →
        |derivWithin (fun v => G.flow.scalar v x) (Iic t) t| ≤ C * G.flow.scalar t x ^ 2) →
      q * (s - H.time first) ≤ η →
      ∀ (z : standardCapWindow D) (x : G.terminalRegularOpen)
        (A : BackwardPointTrace H first last hle x.val),
        A.point first le_rfl hle = J z →
      ∃ Ξ : standardCapWindow D → H.backwardSurvivorIncomingDomain first last hle G,
        IsSmoothEmbedding ThreeModel ThreeModel ∞ Ξ ∧
        (∀ y, H.backwardSurvivorMap first last hle first le_rfl hle (Ξ y).val = J y) ∧
        H.backwardSurvivorIncomingMap first last hle G (Ξ z) = x ∧
        (∀ y : standardCapWindow D, ‖y.val‖ < D → ∀ v : TangentSpace ThreeModel y,
          (1/4:ℝ)*StandardCap.metric.inner y.val v v ≤
            (scaleMetric q hq L.metric).inner (H.backwardSurvivorIncomingMap first last hle G (Ξ y))
              (mfderiv ThreeModel ThreeModel (H.backwardSurvivorIncomingMap first last hle G ∘ Ξ) y v)
              (mfderiv ThreeModel ThreeModel (H.backwardSurvivorIncomingMap first last hle G ∘ Ξ) y v) ∧
          (scaleMetric q hq L.metric).inner (H.backwardSurvivorIncomingMap first last hle G (Ξ y))
              (mfderiv ThreeModel ThreeModel (H.backwardSurvivorIncomingMap first last hle G ∘ Ξ) y v)
              (mfderiv ThreeModel ThreeModel (H.backwardSurvivorIncomingMap first last hle G ∘ Ξ) y v) ≤
            4*StandardCap.metric.inner y.val v v) ∧
        (∀ j ≤ N, ∀ y : standardCapWindow D, ‖y.val‖ ≤ r →
          curvDerivNormSq j L.metric (H.backwardSurvivorIncomingMap first last hle G (Ξ y)) ≤
            q^(j+2)*B) ∧
        ∀ (Q Cscale d ρ : ℝ) (hQ : 0 < Q),
          0 < Cscale → q ≤ Cscale * Q → 0 ≤ d → 0 ≤ ρ →
          ∀ y : G.terminalRegularOpen,
            riemannianEDistOf L.metric x y ≤ ENNReal.ofReal (d / Real.sqrt Q) →
            2 * ‖z.val‖ + (d + ρ) * Real.sqrt Cscale < r / 2 →
            ∀ p ∈ riemannianClosedBallOf L.metric y (ρ / Real.sqrt Q), ∀ j ≤ N,
              curvDerivNormSq j (scaleMetric Q hQ L.metric) p ≤ Cscale ^ (j+2) * B ∧
              curvDerivNorm j (scaleMetric Q hQ L.metric) p ≤ Real.sqrt (Cscale ^ (j+2) * B) := by
  obtain ⟨C₀,hC₀,hscalar,η,ε₀,δ₀,B,hB,hη,hε₀,hεhalf,hδ₀,hprepared⟩ :=
    exists_uniform_prepared_incoming_cap_curvature_derivative_bound N D r eps C
      heps hepssmall hr hfit
  refine ⟨C₀,hC₀,hscalar,η,ε₀,δ₀,B,hB,hη,hε₀,hεhalf,hδ₀,?_⟩
  intro E H0 M _ _ _ _ _ I _ _ _ _ _ g x₀ δ k d A hA Dbig m ζ w hmargin hm hζ
    inc H first last hle s G L hinit Jbig hJbig J q q₀ a₀ hq hq₀ hq₀Q haq hzero
    parameters records hfixed hlower hδ hderiv hfinal htime z x Atrace hanchor
  obtain ⟨Ξ,hΞ,hbirth,hpoint,hmetric,hjets⟩ :=
    hprepared w hmargin hm hζ H first last hle s G L hinit Jbig hJbig
      q q₀ a₀ hq hq₀ hq₀Q haq hzero parameters records hfixed hlower hδ hderiv hfinal
      htime z x Atrace hanchor
  refine ⟨Ξ,hΞ,hbirth,hpoint,hmetric,hjets,?_⟩
  intro Q Cscale d ρ hQ hCscale hscale hd hρ y hnear hreserve
  let Φ := H.backwardSurvivorIncomingMap first last hle G ∘ Ξ
  have hlocal : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Φ :=
    isLocalDiffeomorph_comp (H.backwardSurvivorIncomingMap_isLocalDiffeomorph first last hle G)
      (fun p => Perelman.KappaSolutions.immersionAt_isLocalDiffeomorphAt_of_finrank_eq rfl
        (hΞ.isImmersion.isImmersionAt p))
  have hinj : Injective Φ :=
    (H.backwardSurvivorIncomingMap_injective first last hle G).comp hΞ.isEmbedding.injective
  have hrpos : 0 < r := by linarith [StandardCap.transitionEnd_pos, inv_pos.mpr heps]
  have hrD : r < D := by linarith [inv_pos.mpr heps]
  let gap := r / 2 - (2 * ‖z.val‖ + (d + ρ) * Real.sqrt Cscale)
  have hgap : 0 < gap := sub_pos.mpr hreserve
  have hsqrt : 0 < Real.sqrt Cscale := Real.sqrt_pos.mpr hCscale
  let ρcapture := ρ + gap / (2 * Real.sqrt Cscale)
  have hρcapture : ρ < ρcapture := by
    exact lt_add_of_pos_right _ (div_pos hgap (mul_pos (by norm_num) hsqrt))
  have hquot : gap / (2 * Real.sqrt Cscale) * Real.sqrt Cscale = gap / 2 := by
    field_simp
  have houter : 2 * ‖z.val‖ + (d + ρcapture) * Real.sqrt Cscale ≤ r / 2 := by
    dsimp only [ρcapture]
    dsimp only [gap] at hquot
    nlinarith [hquot]
  have hinner : 2 * ‖z.val‖ + d * Real.sqrt Cscale < r / 2 := by
    nlinarith [mul_nonneg hρ hsqrt.le]
  have hanchorRadius : ‖z.val‖ < r := by
    nlinarith [mul_nonneg hd hsqrt.le, norm_nonneg z.val]
  obtain ⟨_,hball⟩ := StandardCap.curvature_derivative_bound_near_window_anchor L.metric
    hrpos (le_refl r) (by linarith) hq hQ hCscale (by linarith only [hB]) hscale hd
    (hρ.trans hρcapture.le) Φ hlocal hinj
    (fun p hp => hmetric p (hp.trans_lt hrD)) N hjets z (le_refl _) hanchorRadius y
    (by simpa only [Φ, Function.comp_apply, hpoint] using hnear) hinner houter
  intro p hp j hj
  have hmem : p ∈ riemannianBallOf L.metric y (ρcapture / Real.sqrt Q) :=
    hp.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (div_pos (hρ.trans_lt hρcapture)
      (Real.sqrt_pos.mpr hQ))).mpr ((div_lt_div_iff_of_pos_right (Real.sqrt_pos.mpr hQ)).mpr hρcapture))
  have hb := hball p hmem j hj
  exact ⟨hb,Real.sqrt_le_sqrt hb⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
