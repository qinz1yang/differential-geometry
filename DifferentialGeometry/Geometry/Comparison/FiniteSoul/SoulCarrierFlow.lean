import DifferentialGeometry.Geometry.Comparison.FiniteSoul.SoulCarrier
import DifferentialGeometry.External.TauCeti.Geometry.Manifold.IntegralCurve.Flow
import DifferentialGeometry.Geometry.Collapse.SublevelCore.PointNormalFlowRadius

/-!
# LFR47: the same soul flow is a smooth `Flow` in the new carrier; the radius shift
(lane CMS3-CARRIER2, group G4c)

Blueprint master207A, LFR47: "The soul, its normal bundle with induced fiber norm, the actual
normal-flow map and its bounded field `V` are smooth in this carrier ... Its complete flow, norm
bound and point-direction inequalities are the same ones as before." Review dispositions D6/D9:
the SAME `φ` as a smooth `Flow` (ODE uniqueness for `Xhat`, TauCeti's maximal flow), and the radius
shift `du(W) = 1` through NB-INST's generic lemmas.

* `contMDiff_uncurry_of_isMIntegralCurve`: global integral curves of a smooth field on a
  finite-dimensional boundaryless Hausdorff manifold form a jointly smooth map (they are the
  maximal flow, TauCeti `contMDiffOn_maximalIntegralCurve`);
* `mfderiv_symm_apply_of_lift`, `isMIntegralCurve_conj`: if `de ∘ Xhat = X ∘ e`, the conjugate
  `e⁻¹ ∘ φ_t ∘ e` of a flow of `X` has integral curves of `Xhat`;
* `exists_smooth_carrierFlow`: for LFR46's `(X, φ, e)` the flow `y ↦ φ_t y` on the points of the
  transported carrier is a `Flow` that is jointly SMOOTH there. Its generator `W` is a smooth field
  that reads as `X` through the identity transition. The ray identity holds for
  `TransportedCarrier.diffeomorph`, and the fibre radius has `du(W) = 1` beyond `ℓ`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter Function
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.FiniteSoul

open DifferentialGeometry.Topology (TransportedCarrier)

section GlobalFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [BoundarylessManifold I M]

/-- **Global integral curves of a smooth field form a jointly smooth map** (they are the maximal
flow of the field). -/
theorem contMDiff_uncurry_of_isMIntegralCurve {v : (x : M) → TangentSpace I x}
    (hv : ContMDiff I I.tangent ∞ (fun y => (⟨y, v y⟩ : TangentBundle I M)))
    (ψ : ℝ → M → M) (hψ0 : ∀ x, ψ 0 x = x) (hψ : ∀ x, IsMIntegralCurve (fun t => ψ t x) v) :
    ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => ψ q.1 q.2) := by
  have hv1 : ContMDiff I I.tangent 1 (fun y => (⟨y, v y⟩ : TangentBundle I M)) :=
    hv.of_le (by simp)
  have hdom : ∀ x, maximalIntegralCurveInterval v x = univ := fun x =>
    (maximalIntegralCurveInterval_eq_univ_iff hv1).mpr ⟨fun t => ψ t x, hψ0 x, hψ x⟩
  have heq : ∀ x t, maximalIntegralCurve v x t = ψ t x := by
    intro x t
    have habs := abs_nonneg t
    exact ((hψ x).isMIntegralCurveOn (Ioo (-(|t| + 1)) (|t| + 1))).eqOn_maximalIntegralCurve hv1
      ⟨by linarith, by linarith⟩ (hψ0 x) ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩
  have hflow := TauCeti.contMDiffOn_maximalIntegralCurve (I := I) (v := v) (n := ⊤) le_top hv
  have hdomU : TauCeti.maximalIntegralCurveFlowDomain v = univ := by
    ext p
    simp [TauCeti.mem_maximalIntegralCurveFlowDomain, hdom]
  rw [hdomU, contMDiffOn_univ] at hflow
  have hswap : ContMDiff (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, ℝ)) ∞ (fun q : ℝ × M => (q.2, q.1)) :=
    contMDiff_snd.prodMk contMDiff_fst
  exact (hflow.comp hswap).congr fun q => (heq q.2 q.1).symm

end GlobalFlow

section Conjugate

variable {EP : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP]
  {HP : Type*} [TopologicalSpace HP] {IP : ModelWithCorners ℝ EP HP}
  {P : Type*} [TopologicalSpace P] [ChartedSpace HP P]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- If `de ∘ Xhat = X ∘ e` for a differentiable diffeomorphism `e`, then
`d(e⁻¹) ∘ X = Xhat ∘ e⁻¹`. -/
theorem mfderiv_symm_apply_of_lift {k : ℕ∞ω} (e : P ≃ₘ^k⟮IP, I⟯ M) (hk : k ≠ 0)
    {Xhat : (z : P) → TangentSpace IP z} {X : (x : M) → TangentSpace I x}
    (hlift : ∀ z, mfderiv IP I e z (Xhat z) = X (e z)) (y : M) :
    mfderiv I IP e.symm y (X y) = Xhat (e.symm y) := by
  obtain ⟨w, rfl⟩ : ∃ w, e w = y := ⟨e.symm y, e.apply_symm_apply y⟩
  rw [← hlift w]
  refine (mfderiv_comp_apply w (e.symm.mdifferentiable hk (e w)) (e.mdifferentiable hk w)
    (Xhat w)).symm.trans ?_
  have hid : (⇑e.symm ∘ ⇑e) = id := funext e.symm_apply_apply
  rw [hid, mfderiv_id, ContinuousLinearMap.id_apply, e.symm_apply_apply]

/-- **The conjugate of a flow of `X` has integral curves of the lift `Xhat`.** -/
theorem isMIntegralCurve_conj {k : ℕ∞ω} (e : P ≃ₘ^k⟮IP, I⟯ M) (hk : k ≠ 0)
    {Xhat : (z : P) → TangentSpace IP z} {X : (x : M) → TangentSpace I x}
    (hlift : ∀ z, mfderiv IP I e z (Xhat z) = X (e z)) (φ : ℝ → M → M)
    (hφ : ∀ x, IsMIntegralCurve (fun t => φ t x) X) (z : P) :
    IsMIntegralCurve (fun t => e.symm (φ t (e z))) Xhat := by
  intro t
  have h1 := (e.symm.mdifferentiable hk (φ t (e z))).hasMFDerivAt.comp t (hφ (e z) t)
  have hd : ((1 : ℝ →L[ℝ] ℝ).smulRight (Xhat (e.symm (φ t (e z)))) : ℝ →L[ℝ] EP) =
      (mfderiv I IP e.symm (φ t (e z))).comp ((1 : ℝ →L[ℝ] ℝ).smulRight (X (φ t (e z)))) := by
    refine ContinuousLinearMap.ext_ring ?_
    change (1 : ℝ →L[ℝ] ℝ) 1 • Xhat (e.symm (φ t (e z))) =
      mfderiv I IP e.symm (φ t (e z)) ((1 : ℝ →L[ℝ] ℝ) 1 • X (φ t (e z)))
    rw [one_apply_eq_self, one_smul, one_smul, mfderiv_symm_apply_of_lift e hk hlift]
  exact h1.congr_mfderiv hd.symm

end Conjugate

section Carrier

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]

/-- `3 ≤ r` makes the `C^{r−2}` order nonzero. -/
theorem sub_two_ne_zero_of_three_le {r : ℕ∞} (hr : 3 ≤ r) : ((r - 2 : ℕ∞) : ℕ∞ω) ≠ 0 := by
  intro h0
  rw [WithTop.coe_eq_zero, tsub_eq_zero_iff_le] at h0
  exact absurd (hr.trans h0) (by decide)

/-- **LFR47, the same soul flow in the new carrier.** For LFR46's field `X` (ray identification
with profile `prof`, `X = 0` on the zero section), its complete flow `φ` and the `C^{r−2}`
diffeomorphism `e` with the ray identity, the flow `y ↦ φ_t y` on the points of the carrier
transported along `e` is a `Flow` that is jointly smooth there. Its generator `W` is a smooth field
which reads as `X` through the identity transition. The ray identity holds for the smooth
diffeomorphism `TransportedCarrier.diffeomorph`, and the fibre radius `u` has `du(W) = 1` on
`{u > ℓ}`. -/
theorem exists_smooth_carrierFlow {r : ℕ∞}
    {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [FiniteDimensional ℝ EB]
    {B : Type*} [TopologicalSpace B] [ChartedSpace EB B] [IsManifold 𝓘(ℝ, EB) ∞ B]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {V : B → Type*} [TopologicalSpace (TotalSpace F V)] [∀ s, NormedAddCommGroup (V s)]
    [∀ s, InnerProductSpace ℝ (V s)] [FiberBundle F V] [VectorBundle ℝ F V]
    [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, EB)] [IsContMDiffRiemannianBundle 𝓘(ℝ, EB) ∞ F V]
    (hr : 3 ≤ r)
    (e : TotalSpace F V ≃ₘ^((r - 2 : ℕ∞) : ℕ∞ω)⟮𝓘(ℝ, EB).prod 𝓘(ℝ, F), I⟯ M)
    (X : (x : M) → TangentSpace I x) {δ : ℝ} (hδ : 0 < δ) (prof : ℝ → ℝ)
    (hprof : ContDiff ℝ ∞ prof) (hprof0 : ∀ τ ≤ δ, prof τ = 0) (hXS : ∀ s : B, X (e ⟨s, 0⟩) = 0)
    (hXray : ∀ (s : B) (w : V s), ‖w‖ = 1 → ∀ τ : ℝ, 0 < τ → ∃ Y : TangentSpace I (e ⟨s, τ • w⟩),
      HasMFDerivAt 𝓘(ℝ, ℝ) I (fun t : ℝ => e ⟨s, t • w⟩) τ ((1 : ℝ →L[ℝ] ℝ).smulRight Y) ∧
        X (e ⟨s, τ • w⟩) = prof τ • Y)
    (φ : ℝ → M → M) (hφ0 : ∀ x, φ 0 x = x) (hφadd : ∀ s t x, φ (s + t) x = φ s (φ t x))
    (hφX : ∀ t x, HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s => φ s x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (X (φ t x))))
    {ℓ : ℝ} (hℓ : 0 ≤ ℓ)
    (hray : ∀ (s : B) (w : V s), ‖w‖ = 1 → ∀ t : ℝ, ℓ < t →
      e ⟨s, t • w⟩ = φ (t - ℓ) (e ⟨s, ℓ • w⟩)) :
    ∃ (ϕ : Flow ℝ (TransportedCarrier e.toHomeomorph))
      (W : (y : TransportedCarrier e.toHomeomorph) → TangentSpace (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) y),
      (∀ t y, (ϕ t y).point = φ t y.point) ∧
      ContMDiff (𝓘(ℝ, ℝ).prod (𝓘(ℝ, EB).prod 𝓘(ℝ, F))) (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) ∞
        (fun q : ℝ × TransportedCarrier e.toHomeomorph => ϕ q.1 q.2) ∧
      ContMDiff (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) (𝓘(ℝ, EB).prod 𝓘(ℝ, F)).tangent ∞
        (fun y => (⟨y, W y⟩ :
          TangentBundle (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) (TransportedCarrier e.toHomeomorph))) ∧
      (∀ y, mfderiv (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) I (TransportedCarrier.identity e) y (W y) =
        X y.point) ∧
      (∀ t y, HasMFDerivAt 𝓘(ℝ, ℝ) (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) (fun s => ϕ s y) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (W (ϕ t y)))) ∧
      (∀ (s : B) (w : V s), ‖w‖ = 1 → ∀ t : ℝ, ℓ < t →
        TransportedCarrier.diffeomorph (IX := 𝓘(ℝ, EB).prod 𝓘(ℝ, F)) e.toHomeomorph ⟨s, t • w⟩ =
          ϕ (t - ℓ)
            (TransportedCarrier.diffeomorph (IX := 𝓘(ℝ, EB).prod 𝓘(ℝ, F)) e.toHomeomorph
              ⟨s, ℓ • w⟩)) ∧
      ∀ y, ℓ < ‖((TransportedCarrier.diffeomorph (IX := 𝓘(ℝ, EB).prod 𝓘(ℝ, F))
          e.toHomeomorph).symm y).2‖ →
        mvfderiv (I := 𝓘(ℝ, EB).prod 𝓘(ℝ, F))
          (fun y' => ‖((TransportedCarrier.diffeomorph (IX := 𝓘(ℝ, EB).prod 𝓘(ℝ, F))
            e.toHomeomorph).symm y').2‖) y (W y) = 1 := by
  set D := TransportedCarrier.diffeomorph (IX := (𝓘(ℝ, EB).prod 𝓘(ℝ, F))) e.toHomeomorph with hD
  have hk : ((r - 2 : ℕ∞) : ℕ∞ω) ≠ 0 := sub_two_ne_zero_of_three_le hr
  have hT2 : T2Space (TotalSpace F V) := e.toHomeomorph.isEmbedding.t2Space
  have hXs := contMDiff_carrierRadialField (IB := 𝓘(ℝ, EB)) (F := F) (V := V) hδ hprof hprof0
  have hlift : ∀ z, mfderiv (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) I e z (carrierRadialField 𝓘(ℝ, EB) prof z) =
      X (e z) :=
    mfderiv_carrierRadialField (e.mdifferentiable hk) X prof hXS hXray
  let ψ : ℝ → TotalSpace F V → TotalSpace F V := fun t z => e.symm (φ t (e z))
  have hψ0 : ∀ z, ψ 0 z = z := fun z => by
    change e.symm (φ 0 (e z)) = z
    rw [hφ0, e.symm_apply_apply]
  have hψ : ∀ z, IsMIntegralCurve (fun t => ψ t z) (carrierRadialField 𝓘(ℝ, EB) prof) :=
    isMIntegralCurve_conj e hk hlift φ fun x t => hφX t x
  have hψs : ContMDiff (𝓘(ℝ, ℝ).prod (𝓘(ℝ, EB).prod 𝓘(ℝ, F))) (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) ∞
      (fun q : ℝ × TotalSpace F V => ψ q.1 q.2) :=
    contMDiff_uncurry_of_isMIntegralCurve hXs ψ hψ0 hψ
  have hΦ : ∀ t (y : TransportedCarrier e.toHomeomorph),
      D (ψ t (D.symm y)) = (⟨φ t y.point⟩ : TransportedCarrier e.toHomeomorph) := by
    intro t y
    change (⟨e (e.symm (φ t (e (e.symm y.point))))⟩ : TransportedCarrier e.toHomeomorph) =
      ⟨φ t y.point⟩
    rw [e.apply_symm_apply, e.apply_symm_apply]
  have hΦs : ContMDiff (𝓘(ℝ, ℝ).prod (𝓘(ℝ, EB).prod 𝓘(ℝ, F))) (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) ∞
      (fun q : ℝ × TransportedCarrier e.toHomeomorph => D (ψ q.1 (D.symm q.2))) :=
    D.contMDiff.comp (hψs.comp (contMDiff_fst.prodMk (D.symm.contMDiff.comp contMDiff_snd)))
  let ϕ : Flow ℝ (TransportedCarrier e.toHomeomorph) :=
    { toFun := fun t y => ⟨φ t y.point⟩
      cont' := hΦs.continuous.congr fun q => hΦ q.1 q.2
      map_add' := fun t₁ t₂ y => by
        change (⟨φ (t₁ + t₂) y.point⟩ : TransportedCarrier e.toHomeomorph) =
          ⟨φ t₁ (φ t₂ y.point)⟩
        rw [hφadd]
      map_zero' := fun y => by
        change (⟨φ 0 y.point⟩ : TransportedCarrier e.toHomeomorph) = y
        rw [hφ0] }
  have hϕ : ∀ t y, ϕ t y = D (ψ t (D.symm y)) := fun t y => (hΦ t y).symm
  let W : (y : TransportedCarrier e.toHomeomorph) → TangentSpace (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) y :=
    fun y => mfderiv (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) D (D.symm y)
      (carrierRadialField 𝓘(ℝ, EB) prof (D.symm y))
  have hWD : ∀ u, W (D u) = mfderiv (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) D u
      (carrierRadialField 𝓘(ℝ, EB) prof u) := by
    intro u
    change mfderiv (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) D (D.symm (D u))
      (carrierRadialField 𝓘(ℝ, EB) prof (D.symm (D u))) = _
    rw [D.symm_apply_apply]
  have hgen : ∀ t y, HasMFDerivAt 𝓘(ℝ, ℝ) (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) (fun s => ϕ s y) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (W (ϕ t y))) := by
    intro t y
    have h1 := (D.mdifferentiable (by simp) (ψ t (D.symm y))).hasMFDerivAt.comp t
      (hψ (D.symm y) t)
    have key : HasMFDerivAt 𝓘(ℝ, ℝ) (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) (D ∘ fun s => ψ s (D.symm y)) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (W (ϕ t y))) := by
      rw [hϕ t y, hWD]
      refine h1.congr_mfderiv (ContinuousLinearMap.ext_ring ?_)
      change mfderiv (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) D (ψ t (D.symm y))
          ((1 : ℝ →L[ℝ] ℝ) 1 • carrierRadialField 𝓘(ℝ, EB) prof (ψ t (D.symm y))) =
        (1 : ℝ →L[ℝ] ℝ) 1 • mfderiv (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) D
          (ψ t (D.symm y)) (carrierRadialField 𝓘(ℝ, EB) prof (ψ t (D.symm y)))
      rw [one_apply_eq_self, one_smul, one_smul]
    exact key.congr_of_eventuallyEq (Eventually.of_forall fun s => hϕ s y)
  have hrayD : ∀ (s : B) (w : V s), ‖w‖ = 1 → ∀ t : ℝ, ℓ < t →
      D ⟨s, t • w⟩ = ϕ (t - ℓ) (D ⟨s, ℓ • w⟩) := by
    intro s w hw t ht
    change (⟨e ⟨s, t • w⟩⟩ : TransportedCarrier e.toHomeomorph) = ⟨φ (t - ℓ) (e ⟨s, ℓ • w⟩)⟩
    rw [hray s w hw t ht]
  refine ⟨ϕ, W, fun t y => rfl, hΦs.congr fun q => hϕ q.1 q.2, ?_, ?_, hgen, hrayD, ?_⟩
  · have h := ((D.contMDiff.contMDiff_tangentMap (m := ∞) (by simp)).comp hXs).comp
      D.symm.contMDiff
    refine h.congr fun y => ?_
    change (⟨y, W y⟩ : TangentBundle (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) (TransportedCarrier e.toHomeomorph)) =
      ⟨D (D.symm y), W y⟩
    exact congrArg (fun b => (⟨b, W y⟩ :
      TangentBundle (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) (TransportedCarrier e.toHomeomorph)))
      (D.apply_symm_apply y).symm
  · intro y
    obtain ⟨u, rfl⟩ : ∃ u, D u = y := ⟨D.symm y, D.apply_symm_apply y⟩
    rw [hWD u, ← mfderiv_comp_apply u ((TransportedCarrier.identity e).mdifferentiable hk (D u))
      (D.mdifferentiable (by simp) u)]
    exact hlift u
  · intro y hy
    have hW0 : ∀ x, HasMFDerivAt 𝓘(ℝ, ℝ) (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) (fun t => ϕ t x) 0
        ((1 : ℝ →L[ℝ] ℝ).smulRight (W x)) := by
      intro x
      have h := hgen 0 x
      rwa [Flow.map_zero_apply] at h
    exact DifferentialGeometry.Geometry.Collapse.mvfderiv_discCoreRadius_eq_one_of_ray D hℓ hrayD
      W hW0 hy

end Carrier

end DifferentialGeometry.Geometry.FiniteSoul
