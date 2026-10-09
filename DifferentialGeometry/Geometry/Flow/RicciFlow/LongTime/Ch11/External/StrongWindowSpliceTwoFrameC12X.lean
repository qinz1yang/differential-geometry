import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.StrongWindowSpliceAffineC12X

/-!
# Splice: strong neck from two frames (C12X, S16 `hwin` far branch; O-C12X-S16H G4e3)

The flow `S` is read in one tube `W` (open in a neck buffer) through `Ψ : W → M`, in two
normalizations: before the surgery time `t₀` by `r⁻²` (`v ∈ [-θ, 0]`) and after it by `q`
(`τ ∈ [0, τt]`), close in each to the shrinking cylinder (its own reference).  With
`|q r² - 1|` and the closeness small, the point `Ψ u` at time `t = t₀ + τt / q` is the center
of a strong `ε`-neck (`exists_strongNeck_of_two_frames_C12X`): the target embedding is
`Ψ ∘ A`, `A z = (z.1, u + λ z.2)` with `λ = (R / q)^{-1/2}`; the scalar estimate makes the time
shift small and the axial mismatch is `c = q r²` (G4c2).
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

private local instance s16h_sphereDim6 : Fact (Module.finrank ℝ ThreeSpace = 2 + 1) :=
  ⟨by simp [ThreeSpace]⟩

universe u

/-- **Exact frame identity for the flow.**  For `f = Ψ ∘ A`, the normalized pullback at target
time `s` is `A^*(κ · Ψ^*(Q₀ · S(T')))` when `R = κ Q₀` and `t + s / R = T'`. -/
theorem strongNeckNormalizedMetric_eq_affine_C12X {M : Type u} [TopologicalSpace M]
    [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M] {D : RealTimeInterval}
    (S : SolutionOn (I := I3) (M := M) D) {ε δ uc lam : ℝ} {hlam : lam ≠ 0}
    {W : TopologicalSpace.Opens (neckBuffer δ)}
    {hW : ∀ z : spatialNeckBuffer ε, ∃ h : s16hAffine_C12X uc lam hlam z.val ∈ neckBuffer δ,
      (⟨s16hAffine_C12X uc lam hlam z.val, h⟩ : neckBuffer δ) ∈ W}
    (Ψ : W → M) (hΨ : IsLocalDiffeomorph NeckCylinderModel I3 ∞ Ψ)
    (f : C(spatialNeckBuffer ε, M))
    (hf : _root_.Manifold.IsSmoothEmbedding SpatialNeckCylinderModel I3 ∞ f)
    (hfΨ : ∀ z, f z = Ψ (affineInto_C12X ε δ uc lam hlam W hW z))
    (x₀ : M) (t : ℝ) (hQ : 0 < S.scalar t x₀) {Q₀ κ T' s : ℝ} (hQ₀ : 0 < Q₀) (hκ : 0 < κ)
    (hR : S.scalar t x₀ = κ * Q₀) (htime : t + s / S.scalar t x₀ = T') :
    strongNeckNormalizedMetric S x₀ t hQ hf s =
      localPullMetric (scaleMetric κ hκ (localPullMetric (scaleMetric Q₀ hQ₀
        (S.base.metric T')) Ψ hΨ)) (affineInto_C12X ε δ uc lam hlam W hW)
        affineInto_C12X_isLocalDiffeomorph := by
  apply SmoothRiemannianMetric.ext_inner
  intro z a b
  let A := affineInto_C12X ε δ uc lam hlam W hW
  have hA : MDifferentiableAt SpatialNeckCylinderModel NeckCylinderModel A z :=
    (affineInto_C12X_isLocalDiffeomorph (hW := hW) z).mdifferentiableAt (by decide)
  have hΨd : MDifferentiableAt NeckCylinderModel I3 Ψ (A z) :=
    (hΨ (A z)).mdifferentiableAt (by decide)
  have hfun : (f : spatialNeckBuffer ε → M) = Ψ ∘ A := funext hfΨ
  have hd (c : TangentSpace SpatialNeckCylinderModel z) :
      mfderiv SpatialNeckCylinderModel I3 f z c =
        mfderiv NeckCylinderModel I3 Ψ (A z) (mfderiv SpatialNeckCylinderModel NeckCylinderModel
          A z c) := by
    rw [hfun]
    exact mfderiv_comp_apply z hΨd hA c
  rw [strongNeckNormalizedMetric_inner, localPullMetric_inner, scaleMetric_inner,
    localPullMetric_inner, scaleMetric_inner, htime, hd a, hd b, hfΨ z]
  rw [hR]
  ring

/-- One frame at one target time: if the target metric is `A^*(κ · G)` and the model is
`A^*(κ · cylW v)`, closeness of `G` to `cylW v` on the band transfers with factor `√(κ⁻¹ ^ m)`. -/
private theorem s16h_frame_close {ε δ uc lam η : ℝ} {hlam : lam ≠ 0}
    {W : TopologicalSpace.Opens (neckBuffer δ)}
    {hW : ∀ z : spatialNeckBuffer ε, ∃ h : s16hAffine_C12X uc lam hlam z.val ∈ neckBuffer δ,
      (⟨s16hAffine_C12X uc lam hlam z.val, h⟩ : neckBuffer δ) ∈ W}
    (G C : SmoothRiemannianMetric NeckCylinderModel W) {κ : ℝ} (hκ : 0 < κ)
    (T Cyl : SmoothRiemannianMetric SpatialNeckCylinderModel (spatialNeckBuffer ε))
    (hT : T = localPullMetric (scaleMetric κ hκ G) (affineInto_C12X ε δ uc lam hlam W hW)
      affineInto_C12X_isLocalDiffeomorph)
    (hC : Cyl = localPullMetric (scaleMetric κ hκ C) (affineInto_C12X ε δ uc lam hlam W hW)
      affineInto_C12X_isLocalDiffeomorph)
    (m : ℕ) (x : spatialNeckBuffer ε)
    (hcl : metricDerivNorm m G C C (affineInto_C12X ε δ uc lam hlam W hW x) ≤ η) :
    metricDerivNorm m T Cyl Cyl x ≤ Real.sqrt (κ⁻¹ ^ m) * η := by
  subst hT hC
  rw [metricDerivNorm_frame_C12X]
  exact mul_le_mul_of_nonneg_left hcl (Real.sqrt_nonneg _)

private theorem s16h_small_arith {η δ₂ K κ a b : ℝ} {p : ℕ} (hη : 0 < η) (hK : 0 < K)
    (hηδ : η * (2 ^ p * (4 * K + 8)) ≤ δ₂) (hκ0 : 0 ≤ κ) (hκ : κ ≤ K + 1) (ha : |a| ≤ η)
    (hb : |b| ≤ η) : |a - κ * b| < δ₂ ∧ |b| < δ₂ ∧ |a| < δ₂ := by
  have h2p : (1 : ℝ) ≤ 2 ^ p := one_le_pow₀ (by norm_num)
  have hkey : (K + 2) * η < δ₂ := by
    have h1 : (K + 2) * η < (4 * K + 8) * η := by nlinarith
    have h2 : (4 * K + 8) * η ≤ η * (2 ^ p * (4 * K + 8)) := by nlinarith
    linarith
  have hηK : η ≤ (K + 2) * η := by nlinarith
  have hab : |a - κ * b| ≤ |a| + κ * |b| := by
    calc |a - κ * b| ≤ |a| + |κ * b| := abs_sub _ _
      _ = |a| + κ * |b| := by rw [abs_mul, abs_of_nonneg hκ0]
  have hκb : κ * |b| ≤ (K + 1) * η := mul_le_mul hκ hb (abs_nonneg _) (by linarith)
  refine ⟨?_, ?_, ?_⟩
  · linarith
  · linarith
  · linarith

set_option maxHeartbeats 400000 in
-- the pre/post case analysis elaborates two explicit frame identities (200000 times out)
/-- **Strong neck from two frames.**  See the module docstring. -/
theorem exists_strongNeck_of_two_frames_C12X {ε μ Θ : ℝ} (hε : 0 < ε) (hε11 : ε < 1 / 11)
    (hμ : 0 < μ) (hΘ : Θ < 1) :
    ∃ η : ℝ, 0 < η ∧ ∃ p : ℕ, ∀ {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
      [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M] {D : RealTimeInterval}
      (S : SolutionOn (I := I3) (M := M) D), IsSolutionOn S →
      ∀ {δ : ℝ} (W : TopologicalSpace.Opens (neckBuffer δ)) (Ψ : W → M)
        (hΨ : IsLocalDiffeomorph NeckCylinderModel I3 ∞ Ψ), Function.Injective Ψ →
      ∀ (t₀ r q τt θ : ℝ) (hr : 0 < r) (hq : 0 < q) (u : W), τt ∈ Icc 0 Θ →
      |q * r ^ 2 - 1| ≤ η →
      (∀ x : NeckCylinder, |x.2 - ((u : neckBuffer δ) : NeckCylinder).2| ≤ 2 * (ε⁻¹ + 1) →
        ∃ h : x ∈ neckBuffer δ, (⟨x, h⟩ : neckBuffer δ) ∈ W) →
      (∀ v ∈ Icc (-θ) 0, ∀ m ≤ p, ∀ w : W,
        |((w : neckBuffer δ) : NeckCylinder).2 - ((u : neckBuffer δ) : NeckCylinder).2| ≤
          2 * (ε⁻¹ + 1) →
        metricDerivNorm m (localPullMetric (scaleMetric (r ^ 2)⁻¹ (inv_pos.mpr (pow_pos hr 2))
          (S.base.metric (t₀ + r ^ 2 * v))) Ψ hΨ)
          (((cylFam_C12X v).restrictOpen (neckBuffer δ)).restrictOpen W)
          (((cylFam_C12X v).restrictOpen (neckBuffer δ)).restrictOpen W) w ≤ η) →
      (∀ τ ∈ Icc 0 τt, ∀ m ≤ p, ∀ w : W,
        |((w : neckBuffer δ) : NeckCylinder).2 - ((u : neckBuffer δ) : NeckCylinder).2| ≤
          2 * (ε⁻¹ + 1) →
        metricDerivNorm m (localPullMetric (scaleMetric q hq (S.base.metric (t₀ + τ / q))) Ψ hΨ)
          (((cylFam_C12X τ).restrictOpen (neckBuffer δ)).restrictOpen W)
          (((cylFam_C12X τ).restrictOpen (neckBuffer δ)).restrictOpen W) w ≤ η) →
      0 < S.scalar (t₀ + τt / q) (Ψ u) →
      |q⁻¹ * S.scalar (t₀ + τt / q) (Ψ u) - (1 - τt)⁻¹| ≤ η →
      Icc (t₀ + τt / q - (1 + μ) * (S.scalar (t₀ + τt / q) (Ψ u))⁻¹) (t₀ + τt / q) ⊆
          D.carrier →
      Ioo (t₀ + τt / q - (1 + μ) * (S.scalar (t₀ + τt / q) (Ψ u))⁻¹) (t₀ + τt / q) ⊆
          D.regular →
      t₀ - θ * r ^ 2 ≤ t₀ + τt / q - (S.scalar (t₀ + τt / q) (Ψ u))⁻¹ →
      Nonempty (StrongNeck S ε (Ψ u) (t₀ + τt / q)) := by
  obtain ⟨δ₂, hδ₂, p₂, hG⟩ := exists_strongNeck_of_cyl2_close_C12X.{u} hε hε11 hμ
  have h1Θ : 0 < 1 - Θ := by linarith
  set K : ℝ := (1 - Θ)⁻¹ with hKdef
  have hK0 : 0 < K := inv_pos.mpr h1Θ
  set η : ℝ := min (1 / 8) (δ₂ / (2 ^ p₂ * (4 * K + 8))) with hηdef
  have hη : 0 < η := lt_min (by norm_num) (by positivity)
  have hη8 : η ≤ 1 / 8 := min_le_left _ _
  have hηδ : η * (2 ^ p₂ * (4 * K + 8)) ≤ δ₂ := by
    have := min_le_right (1 / 8 : ℝ) (δ₂ / (2 ^ p₂ * (4 * K + 8)))
    rw [← hηdef, le_div_iff₀ (by positivity)] at this
    exact this
  refine ⟨η, hη, p₂, ?_⟩
  intro M _ _ _ _ _ D S hS δ W Ψ hΨ hinj t₀ r q τt θ hr hq u hτt hqr hband hpre hpost hQ
    hscal hwin hreg hθd
  set t := t₀ + τt / q with htdef
  set R := S.scalar t (Ψ u) with hRdef
  have h1τ : 0 < 1 - τt := by linarith [hτt.2]
  have hinvτ1 : 1 ≤ (1 - τt)⁻¹ := one_le_inv₀ h1τ |>.mpr (by linarith [hτt.1])
  have hinvτK : (1 - τt)⁻¹ ≤ K := inv_anti₀ h1Θ (by linarith [hτt.2])
  set κ := q⁻¹ * R with hκdef
  have hsc := abs_le.mp hscal
  have hκlo : 7 / 8 ≤ κ := by linarith [hsc.1]
  have hκhi : κ ≤ K + 1 := by linarith [hsc.2]
  have hκ : 0 < κ := by linarith
  have hRq : R = κ * q := by rw [hκdef]; field_simp
  -- the stretch `λ = κ^{-1/2}`
  set lam : ℝ := (Real.sqrt κ)⁻¹ with hlamdef
  have hsq : 0 < Real.sqrt κ := Real.sqrt_pos.mpr hκ
  have hlam0 : 0 < lam := inv_pos.mpr hsq
  have hlam : lam ≠ 0 := hlam0.ne'
  have hlam2 : κ * lam ^ 2 = 1 := by
    rw [hlamdef, inv_pow, Real.sq_sqrt hκ.le, mul_inv_cancel₀ hκ.ne']
  have hlam_le : lam ≤ 2 := by
    rw [hlamdef, inv_le_comm₀ hsq (by norm_num)]
    rw [show (2 : ℝ)⁻¹ = Real.sqrt (1 / 4) by
      rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]; norm_num]
    exact Real.sqrt_le_sqrt (by linarith)
  set uc : ℝ := ((u : neckBuffer δ) : NeckCylinder).2 with hucdef
  have hWA : ∀ z : spatialNeckBuffer ε, ∃ h : s16hAffine_C12X uc lam hlam z.val ∈ neckBuffer δ,
      (⟨s16hAffine_C12X uc lam hlam z.val, h⟩ : neckBuffer δ) ∈ W := by
    intro z
    apply hband
    have hz := z.2
    change -ε⁻¹ - 1 < z.val.2 ∧ z.val.2 < ε⁻¹ + 1 at hz
    change |uc + lam * z.val.2 - uc| ≤ 2 * (ε⁻¹ + 1)
    rw [add_sub_cancel_left, abs_mul, abs_of_pos hlam0]
    have hza : |z.val.2| ≤ ε⁻¹ + 1 := abs_le.mpr ⟨by linarith [hz.1], hz.2.le⟩
    exact mul_le_mul hlam_le hza (abs_nonneg _) (by norm_num)
  have hbandA : ∀ x : spatialNeckBuffer ε,
      |((affineInto_C12X ε δ uc lam hlam W hWA x : neckBuffer δ) : NeckCylinder).2 - uc| ≤
        2 * (ε⁻¹ + 1) := by
    intro z
    have hz := z.2
    change -ε⁻¹ - 1 < z.val.2 ∧ z.val.2 < ε⁻¹ + 1 at hz
    change |uc + lam * z.val.2 - uc| ≤ 2 * (ε⁻¹ + 1)
    rw [add_sub_cancel_left, abs_mul, abs_of_pos hlam0]
    have hza : |z.val.2| ≤ ε⁻¹ + 1 := abs_le.mpr ⟨by linarith [hz.1], hz.2.le⟩
    exact mul_le_mul hlam_le hza (abs_nonneg _) (by norm_num)
  let A := affineInto_C12X ε δ uc lam hlam W hWA
  have hAloc : IsLocalDiffeomorph SpatialNeckCylinderModel NeckCylinderModel ∞ A :=
    affineInto_C12X_isLocalDiffeomorph
  have hfloc : IsLocalDiffeomorph SpatialNeckCylinderModel I3 ∞ (Ψ ∘ A) :=
    DifferentialGeometry.isLocalDiffeomorph_comp hΨ hAloc
  have hAinj : Function.Injective A := by
    intro z₁ z₂ h
    have h' : s16hAffine_C12X uc lam hlam z₁.val = s16hAffine_C12X uc lam hlam z₂.val :=
      congrArg (fun w : W => ((w : neckBuffer δ) : NeckCylinder)) h
    exact Subtype.ext ((s16hAffine_C12X uc lam hlam).injective h')
  let f : C(spatialNeckBuffer ε, M) := ⟨Ψ ∘ A, hfloc.contMDiff.continuous⟩
  have hf : _root_.Manifold.IsSmoothEmbedding SpatialNeckCylinderModel I3 ∞ f :=
    DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_of_isLocalDiffeomorph_of_injective
      hfloc (hinj.comp hAinj)
  set yStar : SpatialNeckSphere := ((u : neckBuffer δ) : NeckCylinder).1 with hyStar
  have hcenter : A (spatialNeckCentralPoint ε hε yStar) = u := by
    apply Subtype.ext
    apply Subtype.ext
    change s16hAffine_C12X uc lam hlam (yStar, 0) = ((u : neckBuffer δ) : NeckCylinder)
    simp only [s16hAffine_C12X_apply, mul_zero, add_zero]
    rfl
  have hx₀ : f (spatialNeckCentralPoint ε hε yStar) = Ψ u := by
    change Ψ (A _) = Ψ u
    rw [hcenter]
  have he0 : |1 - κ * (1 - τt)| ≤ η := by
    have heq : 1 - κ * (1 - τt) = (1 - τt) * ((1 - τt)⁻¹ - κ) := by
      field_simp
    rw [heq, abs_mul, abs_of_pos h1τ]
    have h1 : |(1 - τt)⁻¹ - κ| ≤ η := by rw [abs_sub_comm]; exact hscal
    calc (1 - τt) * |(1 - τt)⁻¹ - κ| ≤ 1 * |(1 - τt)⁻¹ - κ| :=
          mul_le_mul_of_nonneg_right (by linarith [hτt.1]) (abs_nonneg _)
      _ ≤ η := by rw [one_mul]; exact h1
  have hfac : ∀ κ' : ℝ, 1 / 2 ≤ κ' → ∀ m ≤ p₂, Real.sqrt (κ'⁻¹ ^ m) * η < δ₂ := by
    intro κ' hκ' m hm
    have hκ'0 : 0 < κ' := by linarith
    have hinv : κ'⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ hκ'0 (by norm_num)]
      linarith
    have hpow : κ'⁻¹ ^ m ≤ 2 ^ p₂ :=
      (pow_le_pow_left₀ (inv_nonneg.mpr hκ'0.le) hinv m).trans
        (pow_le_pow_right₀ (by norm_num) hm)
    have h2p : (1 : ℝ) ≤ 2 ^ p₂ := one_le_pow₀ (by norm_num)
    have hsqrt : Real.sqrt (κ'⁻¹ ^ m) ≤ 2 ^ p₂ := by
      rw [Real.sqrt_le_left (by positivity)]
      calc κ'⁻¹ ^ m ≤ 2 ^ p₂ := hpow
        _ ≤ (2 ^ p₂) ^ 2 := by nlinarith [h2p]
    have hpos : 0 < 2 ^ p₂ * (4 * K + 8) := by positivity
    calc Real.sqrt (κ'⁻¹ ^ m) * η ≤ 2 ^ p₂ * η := mul_le_mul_of_nonneg_right hsqrt hη.le
      _ < η * (2 ^ p₂ * (4 * K + 8)) := by
          have h2 : (0 : ℝ) < 2 ^ p₂ * η := by positivity
          have h3 : (0 : ℝ) < 4 * K + 7 := by linarith
          nlinarith [mul_pos h2 h3]
      _ ≤ δ₂ := hηδ
  let e : ℝ → ℝ := fun s => if t + s / R < t₀ then 1 - κ * (1 - τt) - κ * (q * r ^ 2 - 1)
    else 1 - κ * (1 - τt)
  let c : ℝ → ℝ := fun s => if t + s / R < t₀ then q * r ^ 2 else 1
  have hR0 : 0 < R := hQ
  refine hG S hS t yStar f hf (Ψ u) hx₀ hQ hwin hreg e c ?_ ?_
  · intro s _
    have hsm := s16h_small_arith (p := p₂) hη hK0 hηδ hκ.le hκhi he0 hqr
    by_cases hp : t + s / R < t₀
    · simp only [e, c, hp, ↓reduceIte]
      exact ⟨hsm.1, hsm.2.1⟩
    · simp only [e, c, hp, ↓reduceIte, sub_self, abs_zero]
      exact ⟨hsm.2.2, hδ₂⟩
  · intro s hs m hm x
    by_cases hp : t + s / R < t₀
    · -- before the surgery: the `r⁻²` frame
      set v := (t + s / R - t₀) / r ^ 2 with hvdef
      have hr2 : 0 < r ^ 2 := pow_pos hr 2
      have hsR : -R⁻¹ ≤ s / R := by
        rw [div_eq_mul_inv]
        nlinarith [hs.1, inv_pos.mpr hR0]
      have hv : v ∈ Icc (-θ) 0 := by
        constructor
        · rw [hvdef, le_div_iff₀ hr2]
          linarith [hθd, hsR]
        · rw [hvdef]
          exact (div_neg_of_neg_of_pos (by linarith) hr2).le
      have hv1 : v < 1 := by linarith [hv.2]
      have hT' : t + s / R = t₀ + r ^ 2 * v := by
        rw [hvdef]
        field_simp
        ring
      set κf := R * r ^ 2 with hκfdef
      have hκf : 0 < κf := by positivity
      have hRκ : R = κf * (r ^ 2)⁻¹ := by
        rw [hκfdef]
        field_simp
      have hid := strongNeckNormalizedMetric_eq_affine_C12X S Ψ hΨ f hf (fun _ => rfl) (Ψ u) t
        hQ (inv_pos.mpr hr2) hκf hRκ hT'
      have hσ' : 1 - κf * (1 - v) < 1 := by
        have h := mul_pos hκf (show (0 : ℝ) < 1 - v by linarith [hv.2])
        linarith
      have hc' : 0 < κf * lam ^ 2 := by positivity
      have hcyl := localPull_affine_cylFam_C12X (hW := hWA) hκf hv1 hσ' hc'
      have hse : s + e s = 1 - κf * (1 - v) := by
        simp only [e, hp, ↓reduceIte]
        rw [hκfdef, hvdef, hRq, htdef]
        field_simp
        ring
      have hcs : c s = κf * lam ^ 2 := by
        simp only [c, hp, ↓reduceIte]
        rw [hκfdef, hRq]
        have : κ * q * r ^ 2 * lam ^ 2 = q * r ^ 2 * (κ * lam ^ 2) := by ring
        rw [this, hlam2, mul_one]
      rw [hse, hcs]
      have hκfge : 1 / 2 ≤ κf := by
        have hq2 : 7 / 8 ≤ q * r ^ 2 := by linarith [(abs_le.mp hqr).1, hη8]
        have hprod : (7 / 8 : ℝ) * (7 / 8) ≤ κ * (q * r ^ 2) :=
          mul_le_mul hκlo hq2 (by norm_num) hκ.le
        have heqκ : κf = κ * (q * r ^ 2) := by rw [hκfdef, hRq]; ring
        rw [heqκ]
        linarith
      have hcl := s16h_frame_close (hW := hWA) _ _ hκf _ _ hid hcyl.symm m x
        (hpre v hv m (hm.trans le_rfl) (A x) (hbandA x))
      exact hcl.trans_lt (hfac κf hκfge m hm)
    · -- after the surgery: the `q` frame
      set τ := q * (t + s / R - t₀) with hτdef
      have hsR0 : s / R ≤ 0 := div_nonpos_of_nonpos_of_nonneg hs.2 hR0.le
      have hτ : τ ∈ Icc 0 τt := by
        constructor
        · rw [hτdef]
          exact mul_nonneg hq.le (by linarith)
        · rw [hτdef, htdef]
          have : q * (t₀ + τt / q + s / R - t₀) = τt + q * (s / R) := by
            field_simp
            ring
          rw [this]
          have hneg : q * (s / R) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hq.le hsR0
          linarith
      have hτ1 : τ < 1 := by linarith [hτ.2, hτt.2]
      have hT' : t + s / R = t₀ + τ / q := by
        rw [hτdef]
        field_simp
        ring
      have hid := strongNeckNormalizedMetric_eq_affine_C12X S Ψ hΨ f hf (fun _ => rfl) (Ψ u) t
        hQ hq hκ hRq hT'
      have hσ' : 1 - κ * (1 - τ) < 1 := by
        have h := mul_pos hκ (show (0 : ℝ) < 1 - τ by linarith)
        linarith
      have hc' : 0 < κ * lam ^ 2 := by positivity
      have hcyl := localPull_affine_cylFam_C12X (hW := hWA) hκ hτ1 hσ' hc'
      have hse : s + e s = 1 - κ * (1 - τ) := by
        simp only [e, hp, ↓reduceIte]
        rw [hτdef, htdef, hκdef]
        field_simp
        ring
      have hcs : c s = κ * lam ^ 2 := by
        simp only [c, hp, ↓reduceIte]
        rw [hlam2]
      rw [hse, hcs]
      have hcl := s16h_frame_close (hW := hWA) _ _ hκ _ _ hid hcyl.symm m x
        (hpost τ hτ m (hm.trans le_rfl) (A x) (hbandA x))
      exact hcl.trans_lt (hfac κ (by linarith) m hm)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
