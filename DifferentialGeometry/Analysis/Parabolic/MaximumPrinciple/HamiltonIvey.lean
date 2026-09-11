import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.FirstContact
import DifferentialGeometry.Geometry.Curvature.DimensionThree.HamiltonIvey.Region
import DifferentialGeometry.Analysis.Parabolic.CurvatureOperatorLocalized
import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.LogarithmicBarrier

noncomputable section
open Bundle CovariantDerivative Filter Set
open DifferentialGeometry
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature.DimensionThree
open DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff Topology InnerProductSpace
namespace DifferentialGeometry.Analysis.Parabolic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  [IsContMDiffRiemannianBundle I ∞ F V]

theorem cutoff_hamilton_ivey_inequality_of_compact_support
    [BoundarylessManifold I M]
    [VectorBundle ℝ E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) ℝ)
    (cov : ℝ → CovariantDerivative I F V)
    [∀ t, ContMDiffCovariantDerivative (cov t) ∞] (hcov : ∀ t, (cov t).IsMetricCompatible)
    {T : ℝ}
    (A : ℝ → Cₛ^∞⟮I; F →L[ℝ] F, (fun x : M => V x →L[ℝ] V x)⟯)
    (X : ℝ → (y : M) → TangentSpace I y)
    (hGconn : ∀ t ∈ Ioc 0 T, G.connection t = LeviCivita (I := I) (G.metric t))
    (hdim : ∀ x, Module.finrank ℝ (V x) = 3)
    (hPDE : ∀ t ∈ Ioc 0 T, ∀ x,
      letI : FiniteDimensional ℝ (V x) := VectorBundle.finiteDimensional ℝ F V x
      HasDerivWithinAt (fun s => A s x)
        (rawBundleEndomorphismConnLap (I := I) (G.metric t) (cov t) (fun y => A t y) x +
          HomConnectionGen.homBundleCovariantDerivativeGen I M F V F V (cov t) (cov t)
            (fun y => A t y) x (X t x) +
          (curvatureOperatorReactionEndomorphism3 (A t x).toLinearMap).toContinuousLinearMap)
        (Icc 0 t) t)
    (hA : ∀ t ∈ Icc 0 T, ∀ x, (A t x).toLinearMap.IsSymmetric)
    (χ : ℝ → M → ℝ) {K : Set M} (hK : IsCompact K)
    (hχ : ContinuousOn (fun p : ℝ × M => χ p.1 p.2) (Icc 0 T ×ˢ K))
    (hr : ContinuousOn (fun p : ℝ × M => LinearMap.trace ℝ (V p.2) (A p.1 p.2).toLinearMap)
      (Icc 0 T ×ˢ K))
    (hQ : ContinuousOn (fun p : ℝ × M =>
      max (-(⨅ w : {w : V p.2 // w ≠ 0}, (A p.1 p.2).rayleighQuotient w)) 0)
      (Icc 0 T ×ˢ K))
    (hχrange : ∀ t ∈ Icc 0 T, ∀ x, 0 ≤ χ t x ∧ χ t x ≤ 1)
    (hχsupport : ∀ t ∈ Icc 0 T, ∀ x, x ∉ K → χ t x = 0)
    (hscalar : ∀ t ∈ Ioc 0 T, ∀ x,
      -3 ≤ t * LinearMap.trace ℝ (V x) (A t x).toLinearMap)
    {δ ε : ℝ} (hδ : 0 ≤ δ) (hε : 0 ≤ ε) (herror : T * (δ + 2 * ε) < 1)
    (hcutoff : ∀ t ∈ Ioc 0 T, ∀ x, 0 < χ t x → ∃ φ : ℝ → M → ℝ,
      (∀ᶠ p in 𝓝[Icc 0 t ×ˢ (Set.univ : Set M)] (t, x), φ p.1 p.2 ≤ χ p.1 p.2) ∧
      φ t x = χ t x ∧
      DifferentiableWithinAt ℝ (fun s => φ s x) (Icc 0 t) t ∧
      (∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) (φ t) y) ∧
      MDiffAt (T% fun y => gradientFun (I := I) (G.metric t) (φ t) y) x ∧
      parabolicOperatorWithDrift (I := I) G t X φ t x ≤ δ ∧
      (G.metric t).inner x (gradientAt (I := I) G t (φ t) x)
        (gradientAt (I := I) G t (φ t) x) ≤ ε * φ t x) :
    ∀ t ∈ Icc 0 T, ∀ x,
      (t * χ t x * max (-(⨅ w : {w : V x // w ≠ 0}, (A t x).rayleighQuotient w)) 0) *
        (Real.log (t * χ t x * max (-(⨅ w : {w : V x // w ≠ 0},
          (A t x).rayleighQuotient w)) 0) - 3) ≤
      t * χ t x * LinearMap.trace ℝ (V x) (A t x).toLinearMap := by
  let r : ℝ → M → ℝ := fun s y => LinearMap.trace ℝ (V y) (A s y).toLinearMap
  let Q : ℝ → M → ℝ := fun s y => max (-(⨅ w : {w : V y // w ≠ 0},
    (A s y).rayleighQuotient w)) 0
  let z : ℝ → M → ℝ := fun s y => s * χ s y * Q s y
  have hznonneg (s : ℝ) (hs : s ∈ Icc 0 T) (y : M) : 0 ≤ z s y :=
    mul_nonneg (mul_nonneg hs.1 (hχrange s hs y).1) (le_max_right _ _)
  have heigen (s : ℝ) (y : M) : -3 * Q s y ≤ r s y := by
    let : FiniteDimensional ℝ (V y) := VectorBundle.finiteDimensional ℝ F V y
    have h := (A s y).finrank_mul_iInf_rayleighQuotient_le_re_trace
    rw [hdim y] at h
    simp only [Nat.cast_ofNat, RCLike.re_to_real] at h
    dsimp only [Q, r]
    nlinarith [le_max_left (-(⨅ w : {w : V y // w ≠ 0}, (A s y).rayleighQuotient w)) 0]
  have hscaled (s : ℝ) (hs : s ∈ Icc 0 T) (y : M) : -3 * z s y ≤ s * χ s y * r s y := by
    have h := mul_le_mul_of_nonneg_left (heigen s y) (mul_nonneg hs.1 (hχrange s hs y).1)
    dsimp only [z]
    nlinarith
  have hscalarscaled (s : ℝ) (hs : s ∈ Ioc 0 T) (y : M) : -3 ≤ s * χ s y * r s y := by
    have h := mul_le_mul_of_nonneg_left (hscalar s hs y) (hχrange s ⟨hs.1.le, hs.2⟩ y).1
    have hχone := (hχrange s ⟨hs.1.le, hs.2⟩ y).2
    dsimp only [r] at *
    nlinarith
  have hzcontinuous : ContinuousOn (fun p : ℝ × M => z p.1 p.2) (Icc 0 T ×ˢ K) :=
    (continuous_fst.continuousOn.mul hχ).mul hQ
  have hperturb (η : ℝ) (hη : 0 < η) : ∀ s ∈ Icc 0 T, ∀ y,
      z s y * (Real.log (z s y) - 3 - η) ≤ s * χ s y * r s y := by
    let f : ℝ → M → ℝ := fun s y => s * χ s y * r s y -
      z s y * (Real.log (z s y) - 3 - η)
    have hfcontinuous : ContinuousOn (fun p : ℝ × M => f p.1 p.2) (Icc 0 T ×ˢ K) := by
      have hlog : ContinuousOn (fun p : ℝ × M => z p.1 p.2 * Real.log (z p.1 p.2))
          (Icc 0 T ×ˢ K) := Real.continuous_mul_log.comp_continuousOn hzcontinuous
      have hfun : (fun p : ℝ × M => f p.1 p.2) =
          fun p => p.1 * χ p.1 p.2 * r p.1 p.2 -
            (z p.1 p.2 * Real.log (z p.1 p.2) - (3 + η) * z p.1 p.2) := by
        funext p
        dsimp only [f]
        ring
      rw [hfun]
      exact ((continuous_fst.continuousOn.mul hχ).mul hr).sub
        (hlog.sub (continuousOn_const.mul hzcontinuous))
    by_contra! hfail
    have hfail' : ∃ s ∈ Icc 0 T, ∃ y ∈ K, f s y < 0 := by
      obtain ⟨s, hs, y, hy⟩ := hfail
      refine ⟨s, hs, y, ?_, ?_⟩
      · by_contra hout
        have hz0 : z s y = 0 := by dsimp only [z]; rw [hχsupport s hs y hout]; ring
        rw [hz0, hχsupport s hs y hout] at hy
        simp at hy
      · dsimp only [f]
        linarith
    obtain ⟨s, hs, y, hy, hz1, hfzero, hnonneg⟩ := exists_first_zero_on_compact_superlevel
      (f := f) (z := z) 1 hK hfcontinuous hzcontinuous
      (by intro y hy; simp [z])
      (by intro s hs y hy; simp [f, z, hχsupport s hs y hy])
      (by
        intro s hs y hy hz1
        exact hamilton_ivey_perturbed_defect_nonneg_of_le_one
          (hznonneg s hs y) hz1 hη.le (hscaled s hs y))
      (by intro s hs y hy hz1; dsimp only [f]; rw [hz1]; have he := hscaled s hs y; rw [hz1] at he; simp only [Real.log_one] at *; nlinarith)
      hfail'
    have hsmem : s ∈ Icc 0 T := ⟨hs.1.le, hs.2⟩
    have hχpos : 0 < χ s y := by
      by_contra! hn
      have hz0 : z s y = 0 := by dsimp only [z]; rw [le_antisymm hn (hχrange s hsmem y).1]; ring
      rw [hz0] at hz1
      norm_num at hz1
    have hQpos : 0 < Q s y := by
      by_contra! hn
      have hz0 : z s y = 0 := by dsimp only [z]; rw [le_antisymm hn (le_max_right _ _)]; ring
      rw [hz0] at hz1
      norm_num at hz1
    have hneg : (⨅ w : {w : V y // w ≠ 0}, (A s y).rayleighQuotient w) < 0 := by
      by_contra! hn
      have heq : Q s y = 0 := max_eq_right (neg_nonpos.mpr hn)
      rw [heq] at hQpos
      exact (lt_irrefl _ hQpos).elim
    have hQeq : Q s y = -(⨅ w : {w : V y // w ≠ 0}, (A s y).rayleighQuotient w) :=
      max_eq_left (neg_nonneg.mpr hneg.le)
    have hcontact : s * χ s y * r s y = z s y * (Real.log (z s y) - 3 - η) := by
      dsimp only [f] at hfzero
      linarith
    have hslopeCore := hamilton_ivey_perturbed_boundary_slope_pos
      (lt_trans zero_lt_one hz1) hη (hscaled s hsmem y) (hscalarscaled s hs y) hcontact
    obtain ⟨φ, hφχ, hφeq, hφtime, hφspace, hφgrad, hφpar, hφsq⟩ := hcutoff s hs y hχpos
    let c : ℝ → ℝ := fun q => Real.log q - 3 - η
    let θ : ℝ → M → ℝ := fun q w => χ q w * r q w -
      (χ q w * Q q w) * (Real.log (χ q w * Q q w) + c q)
    have hlink (q : ℝ) (hq : 0 < q) (w : M) : f q w = q * θ q w := by
      by_cases hQzero : χ q w * Q q w = 0
      · dsimp only [f, θ, z, c]
        rw [show q * χ q w * Q q w = q * (χ q w * Q q w) by ring, hQzero]
        ring
      · have hzq : z q w = q * (χ q w * Q q w) := by dsimp only [z]; ring
        dsimp only [f, θ, c]
        rw [hzq, Real.log_mul hq.ne' hQzero]
        ring
    have hθzero : θ s y = 0 := by
      have h := hlink s hs.1 y
      rw [hfzero] at h
      exact (mul_eq_zero.mp h.symm).resolve_left hs.1.ne'
    have hθtime : IsLocalMinOn (fun q => θ q y) (Icc 0 s) s := by
      have hpos : ∀ᶠ q in 𝓝[Icc 0 s] s, 0 < q :=
        (eventually_gt_nhds hs.1).filter_mono inf_le_left
      filter_upwards [self_mem_nhdsWithin, hpos] with q hq hqpos
      rw [hθzero]
      have h := hnonneg q hq y
      rw [hlink q hqpos y] at h
      exact nonneg_of_mul_nonneg_right h hqpos
    have hθspace : IsLocalMin (θ s) y := by
      filter_upwards [] with w
      rw [hθzero]
      have h := hnonneg s ⟨hs.1.le, le_rfl⟩ w
      rw [hlink s hs.1 w] at h
      exact nonneg_of_mul_nonneg_right h hs.1
    have hlogsplit : Real.log (z s y) = Real.log s + Real.log (χ s y * Q s y) := by
      rw [show z s y = s * (χ s y * Q s y) by dsimp only [z]; ring,
        Real.log_mul hs.1.ne' (mul_pos hχpos hQpos).ne']
    have hslope : 0 < Real.log (χ s y * (-(⨅ w : {w : V y // w ≠ 0},
        (A s y).rayleighQuotient w))) + c s + 1 := by
      rw [← hQeq]
      dsimp only [c]
      linarith [hslopeCore.2]
    have hbd : r s y = (-(⨅ w : {w : V y // w ≠ 0}, (A s y).rayleighQuotient w)) *
        (Real.log (χ s y * (-(⨅ w : {w : V y // w ≠ 0},
          (A s y).rayleighQuotient w))) + c s) := by
      rw [← hQeq]
      dsimp only [θ] at hθzero
      have h : χ s y * (r s y - Q s y * (Real.log (χ s y * Q s y) + c s)) = 0 := by
        nlinarith only [hθzero]
      have heq := (mul_eq_zero.mp h).resolve_left hχpos.ne'
      linarith
    have hd : HasDerivAt c s⁻¹ s := ((Real.hasDerivAt_log hs.1.ne').sub_const 3).sub_const η
    have hbound := cutoff_hamilton_ivey_bound_at_time_and_space_min G (cov s) (hcov s) hs.1
      A y X (hGconn s hs) (hdim y) (hPDE s hs y) (hA s hsmem y) hneg χ φ c hφχ hφeq hχpos
      hφtime hφspace hφgrad hd.differentiableAt.differentiableWithinAt hslope hbd
      hθtime hθspace hφpar hφsq
    rw [hd.hasDerivWithinAt.derivWithin ((uniqueDiffOn_Icc hs.1).uniqueDiffWithinAt ⟨hs.1.le, le_rfl⟩),
      hφeq, ← hQeq] at hbound
    have hscaledbound := mul_le_mul_of_nonneg_left hbound hs.1.le
    have hcancel : s * (χ s y * s⁻¹) = χ s y := by field_simp [hs.1.ne']
    have htimebound := mul_le_mul_of_nonneg_right hs.2 (show 0 ≤ δ + 2 * ε by positivity)
    have hzbound : z s y < 2 := by
      dsimp only [z]
      nlinarith [hscaledbound, htimebound, (hχrange s hsmem y).2, herror]
    linarith [hslopeCore.1]
  intro s hs y
  change z s y * (Real.log (z s y) - 3) ≤ s * χ s y * r s y
  by_contra! hfail
  have hzpos : 0 < z s y := by
    by_contra! hn
    have hz0 : z s y = 0 := le_antisymm hn (hznonneg s hs y)
    have hlow := hscaled s hs y
    rw [hz0] at hlow hfail
    simp only [mul_zero, zero_mul] at hlow hfail
    linarith
  let η := (z s y * (Real.log (z s y) - 3) - s * χ s y * r s y) / (2 * z s y)
  have hη : 0 < η := div_pos (sub_pos.mpr hfail) (mul_pos (by norm_num) hzpos)
  have hpert := hperturb η hη s hs y
  have hηeq : η * (2 * z s y) = z s y * (Real.log (z s y) - 3) - s * χ s y * r s y := by
    exact div_mul_cancel₀ _ (mul_pos (by norm_num) hzpos).ne'
  nlinarith [hpert, hηeq]


theorem hamilton_ivey_inequality_of_compactly_supported_cutoff
    [BoundarylessManifold I M]
    [VectorBundle ℝ E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) ℝ)
    (cov : ℝ → CovariantDerivative I F V)
    [∀ t, ContMDiffCovariantDerivative (cov t) ∞] (hcov : ∀ t, (cov t).IsMetricCompatible)
    {T : ℝ}
    (A : ℝ → Cₛ^∞⟮I; F →L[ℝ] F, (fun x : M => V x →L[ℝ] V x)⟯)
    (X : ℝ → (y : M) → TangentSpace I y)
    (hGconn : ∀ t ∈ Ioc 0 T, G.connection t = LeviCivita (I := I) (G.metric t))
    (hdim : ∀ x, Module.finrank ℝ (V x) = 3)
    (hPDE : ∀ t ∈ Ioc 0 T, ∀ x,
      letI : FiniteDimensional ℝ (V x) := VectorBundle.finiteDimensional ℝ F V x
      HasDerivWithinAt (fun s => A s x)
        (rawBundleEndomorphismConnLap (I := I) (G.metric t) (cov t) (fun y => A t y) x +
          HomConnectionGen.homBundleCovariantDerivativeGen I M F V F V (cov t) (cov t)
            (fun y => A t y) x (X t x) +
          (curvatureOperatorReactionEndomorphism3 (A t x).toLinearMap).toContinuousLinearMap)
        (Icc 0 t) t)
    (hA : ∀ t ∈ Icc 0 T, ∀ x, (A t x).toLinearMap.IsSymmetric)
    (χ : ℝ → M → ℝ) {K : Set M} (hK : IsCompact K)
    (hχ : ContinuousOn (fun p : ℝ × M => χ p.1 p.2) (Icc 0 T ×ˢ K))
    (hr : ContinuousOn (fun p : ℝ × M => LinearMap.trace ℝ (V p.2) (A p.1 p.2).toLinearMap)
      (Icc 0 T ×ˢ K))
    (hQ : ContinuousOn (fun p : ℝ × M =>
      max (-(⨅ w : {w : V p.2 // w ≠ 0}, (A p.1 p.2).rayleighQuotient w)) 0)
      (Icc 0 T ×ˢ K))
    (hχrange : ∀ t ∈ Icc 0 T, ∀ x, 0 ≤ χ t x ∧ χ t x ≤ 1)
    (hχsupport : ∀ t ∈ Icc 0 T, ∀ x, x ∉ K → χ t x = 0)
    (hscalar : ∀ t ∈ Ioc 0 T, ∀ x,
      -3 ≤ t * LinearMap.trace ℝ (V x) (A t x).toLinearMap)
    {δ ε : ℝ} (hδ : 0 ≤ δ) (hε : 0 ≤ ε) (herror : T * (δ + 2 * ε) < 1)
    (hcutoff : ∀ t ∈ Ioc 0 T, ∀ x, 0 < χ t x → ∃ φ : ℝ → M → ℝ,
      (∀ᶠ p in 𝓝[Icc 0 t ×ˢ (Set.univ : Set M)] (t, x), φ p.1 p.2 ≤ χ p.1 p.2) ∧
      φ t x = χ t x ∧
      DifferentiableWithinAt ℝ (fun s => φ s x) (Icc 0 t) t ∧
      (∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) (φ t) y) ∧
      MDiffAt (T% fun y => gradientFun (I := I) (G.metric t) (φ t) y) x ∧
      parabolicOperatorWithDrift (I := I) G t X φ t x ≤ δ ∧
      (G.metric t).inner x (gradientAt (I := I) G t (φ t) x)
        (gradientAt (I := I) G t (φ t) x) ≤ ε * φ t x)
    {t : ℝ} (ht : t ∈ Ioc 0 T) (x : M) (hχone : χ t x = 1)
    (hneg : (⨅ w : {w : V x // w ≠ 0}, (A t x).rayleighQuotient w) < 0) :
    (-(⨅ w : {w : V x // w ≠ 0}, (A t x).rayleighQuotient w)) *
        (Real.log (t * (-(⨅ w : {w : V x // w ≠ 0},
          (A t x).rayleighQuotient w))) - 3) ≤
      LinearMap.trace ℝ (V x) (A t x).toLinearMap := by
  have h := cutoff_hamilton_ivey_inequality_of_compact_support G cov hcov A X hGconn hdim
    hPDE hA χ hK hχ hr hQ hχrange hχsupport hscalar hδ hε herror hcutoff
    t ⟨ht.1.le, ht.2⟩ x
  rw [hχone, mul_one, max_eq_left (neg_nonneg.mpr hneg.le)] at h
  have hscaled : t * ((-(⨅ w : {w : V x // w ≠ 0}, (A t x).rayleighQuotient w)) *
      (Real.log (t * (-(⨅ w : {w : V x // w ≠ 0}, (A t x).rayleighQuotient w))) - 3)) ≤
      t * LinearMap.trace ℝ (V x) (A t x).toLinearMap := by
    simpa only [mul_assoc] using h
  exact (mul_le_mul_iff_right₀ ht.1).mp hscaled

end DifferentialGeometry.Analysis.Parabolic
