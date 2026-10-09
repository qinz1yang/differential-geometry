import DifferentialGeometry.Geometry.MinimalSurface.Plateau.TracePhaseAnnulus.RelativePasting
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.TracePhaseAnnulus
import DifferentialGeometry.Geometry.Metric.LoopLipschitz
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.TracePhaseAnnulus.RelativeArea

noncomputable section
open Bundle Manifold Set Metric DifferentialGeometry
open DifferentialGeometry.Analysis DifferentialGeometry.Topology
open scoped Bundle Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.Geometry

private theorem periodic_smooth_displacement_lipschitz {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f 1) :
    ∃ L : ℝ≥0, LipschitzWith L hp.lift := by
  have hderiv := hf.continuous_deriv (by simp)
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Icc (-1 : ℝ) 2)).exists_bound_of_continuousOn
    hderiv.continuousOn
  refine ⟨NNReal.mk (max 0 C) (le_max_left _ _), ?_⟩
  apply LipschitzWith.of_dist_le_mul
  intro x y
  obtain ⟨a, d, ha0, ha1, hd0, hd1, hay, hadx, hdist⟩ := exists_short_circle_lifts x y
  have ha : a ∈ Icc (-1 : ℝ) 2 := by constructor <;> linarith
  have had : a + d ∈ Icc (-1 : ℝ) 2 := by constructor <;> linarith
  have hconv : Convex ℝ (Icc (-1 : ℝ) 2) := convex_Icc _ _
  have hb := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun x _ => hf.differentiable (by simp) x)
    (fun x hx => (hC x hx).trans (le_max_right 0 C)) hconv ha had
  have hx : hp.lift x = f (a + d) := by rw [← hadx]; rfl
  have hy : hp.lift y = f a := by rw [← hay]; rfl
  rw [hx, hy, hdist, dist_eq_norm]
  simpa only [NNReal.coe_mk, add_sub_cancel_left, Real.norm_eq_abs] using hb

private theorem relative_phase_glue {Q : Type*} {u : ℂ → Q} {γ : loopCircle → Q}
    {ρ : ℝ → ℝ} {δ R : loopCircle → ℝ}
    (hδ : ∀ t : ℝ, δ (t : loopCircle) = ρ t - t)
    (htrace : ∀ t : ℝ, u (AddCircle.toCircle (t : loopCircle) : ℂ) = γ (ρ t : loopCircle))
    (hlo : ∀ θ, 1 / 2 ≤ R θ) (hhi : ∀ θ, R θ ≤ 1)
    (hcompat : ∀ θ, 2 * (1 - R θ) * δ θ = δ θ) (z : ℂ)
    (hz : ‖z‖ = R (polarAnnulusCoordinates z).2) :
    u (radialProfileInv R z) = tracePhaseAnnulusStrip γ δ (polarAnnulusCoordinates z) := by
  let θ := (polarAnnulusCoordinates z).2
  have hpos : 0 < R θ := lt_of_lt_of_le (by norm_num) (hlo θ)
  have hcircle : (AddCircle.toCircle θ : ℂ) = (radialDirection z : ℂ) := by
    change (AddCircle.toCircle ((AddCircle.homeomorphCircle (T := (1 : ℝ))
      one_ne_zero).symm (radialDirection z)) : ℂ) = _
    rw [← AddCircle.homeomorphCircle_apply one_ne_zero, Homeomorph.apply_symm_apply]
  have hΦ : radialProfileInv R z = (AddCircle.toCircle θ : ℂ) := by
    calc
      _ = (R θ)⁻¹ • z := rfl
      _ = (R θ)⁻¹ • (‖z‖ • (radialDirection z : ℂ)) :=
        congrArg (fun w : ℂ => (R θ)⁻¹ • w) (radialDirection_reconstruct z).symm
      _ = (radialDirection z : ℂ) := by
        rw [smul_smul, hz, inv_mul_cancel₀ hpos.ne', one_smul]
      _ = _ := hcircle.symm
  have hp : (polarAnnulusCoordinates z).1 ∈ Icc (0 : ℝ) 1 := by
    change 0 ≤ 2 * ‖z‖ - 1 ∧ 2 * ‖z‖ - 1 ≤ 1
    rw [hz]
    constructor <;> linarith [hlo θ, hhi θ]
  rw [hΦ, tracePhaseAnnulusStrip_eq_of_mem hp]
  obtain ⟨t, ht⟩ := QuotientAddGroup.mk_surjective θ
  rw [← ht, htrace]
  unfold tracePhaseAnnulus
  change γ (ρ t : loopCircle) = γ (θ + (((1 - (2 * ‖z‖ - 1)) * δ θ : ℝ) : loopCircle))
  have hc : (1 - (2 * ‖z‖ - 1)) * δ θ = δ θ := by
    rw [hz]
    convert hcompat θ using 1
    ring
  rw [hc, ← ht, hδ, ← AddCircle.coe_add]
  congr 2
  ring

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T3Space M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [FiniteDimensional ℝ E] in
private theorem relativeDiskAnnulus_riemannian_lipschitz
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {R : loopCircle → ℝ} {u : ℂ → M} {H : ℝ × loopCircle → M}
    {Kr Ku Kh : ℝ≥0} (hR : LipschitzWith Kr R) (hlo : ∀ θ, 1 / 2 ≤ R θ)
    (hu : ∀ z w, riemannianEDistOf g (u z) (u w) ≤ (Ku : ℝ≥0∞) * edist z w)
    (hH : ∀ p q, riemannianEDistOf g (H p) (H q) ≤ (Kh : ℝ≥0∞) * edist p q)
    (hglue : ∀ z, ‖z‖ = R (polarAnnulusCoordinates z).2 →
      u (radialProfileInv R z) = H (polarAnnulusCoordinates z)) :
    ∃ K : ℝ≥0, ∀ z w,
      riemannianEDistOf g (relativeDiskAnnulus R u H z) (relativeDiskAnnulus R u H w) ≤
        (K : ℝ≥0∞) * edist z w := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace 𝓘(ℝ, E) : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let : PseudoEMetricSpace M := PseudoEMetricSpace.ofRiemannianMetric 𝓘(ℝ, E) M
  have hu' : LipschitzWith Ku u := hu
  have hH' : LipschitzWith Kh H := hH
  exact ⟨_, relativeDiskAnnulus_lipschitz hR hlo hu' hH' hglue⟩

omit [T3Space M] in
private theorem relative_phase_range
    {v : C(closedDisk, M)} {γ : loopCircle → M} {ρ : ℝ → ℝ}
    (hm : Monotone ρ) (hp : ∀ t, ρ (t + 1) = ρ t + 1) (hc : Continuous ρ)
    (htrace : ∀ t : ℝ, diskTrace v (t : loopCircle) = γ (ρ t : loopCircle))
    {R δ : loopCircle → ℝ} (hlo : ∀ θ, 1 / 2 ≤ R θ) (hhi : ∀ θ, R θ ≤ 1) :
    range (fun z : closedDisk => relativeDiskAnnulus R (diskExtension v)
      (tracePhaseAnnulusStrip γ δ) z) = range v := by
  have hpos (θ : loopCircle) : 0 < R θ := lt_of_lt_of_le (by norm_num) (hlo θ)
  let f : CircleDeg1Lift := ⟨⟨ρ, hm⟩, hp⟩
  have hsurj : Function.Surjective f := f.continuous_iff_surjective.mp hc
  have hγrange (θ : loopCircle) : γ θ ∈ range v := by
    obtain ⟨s, rfl⟩ := QuotientAddGroup.mk_surjective θ
    obtain ⟨t, ht⟩ := hsurj s
    refine ⟨diskBoundary (t : loopCircle), ?_⟩
    change diskTrace v (t : loopCircle) = γ (s : loopCircle)
    rw [htrace]
    exact congrArg (fun x : ℝ => γ (x : loopCircle)) ht
  apply Subset.antisymm
  · rintro y ⟨z, rfl⟩
    change (if ‖(z : ℂ)‖ ≤ R (polarAnnulusCoordinates z).2 then
      diskExtension v (radialProfileInv R z) else
      tracePhaseAnnulusStrip γ δ (polarAnnulusCoordinates z)) ∈ range v
    split_ifs
    · exact ⟨diskRetraction (radialProfileInv R z), rfl⟩
    · exact hγrange _
  · rintro y ⟨z, rfl⟩
    have hz : ‖(z : ℂ)‖ ≤ 1 := mem_closedBall_zero_iff.mp z.property
    have hΨ : ‖radialProfile R z‖ ≤ 1 := by
      rw [norm_radialProfile hpos]
      exact (mul_le_mul (hhi _) hz (norm_nonneg _) (by norm_num)).trans_eq (one_mul 1)
    let w : closedDisk := ⟨radialProfile R z, mem_closedBall_zero_iff.mpr hΨ⟩
    refine ⟨w, ?_⟩
    change relativeDiskAnnulus R (diskExtension v) (tracePhaseAnnulusStrip γ δ)
      (radialProfile R z) = v z
    rw [relativeDiskAnnulus_inner]
    · rw [radialProfileInv_radialProfile hpos, diskExtension_coe]
    · rw [norm_radialProfile hpos, radialProfile_parameter hpos]
      exact (mul_le_mul_of_nonneg_left hz (hpos _).le).trans_eq (mul_one _)

omit [FiniteDimensional ℝ E] in
private theorem exists_relative_phase_filling_of_radius
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {v : C(closedDisk, M)} {γ : freeLoop M} {ρ : ℝ → ℝ}
    (hm : Monotone ρ) (hp : ∀ t, ρ (t + 1) = ρ t + 1) (hc : Continuous ρ)
    (htrace : ∀ t : ℝ, diskTrace v (t : loopCircle) = γ (ρ t : loopCircle))
    {R δ : loopCircle → ℝ} {Kr Ku Kh : ℝ≥0} (hR : LipschitzWith Kr R)
    (hlo : ∀ θ, 1 / 2 ≤ R θ) (hhi : ∀ θ, R θ ≤ 1)
    (hδ : ∀ t : ℝ, δ (t : loopCircle) = ρ t - t)
    (hcompat : ∀ θ, 2 * (1 - R θ) * δ θ = δ θ)
    (hu : ∀ z w : closedDisk, riemannianEDistOf g (v z) (v w) ≤ (Ku : ℝ≥0∞) * edist z w)
    (hH : ∀ p q, riemannianEDistOf g (tracePhaseAnnulusStrip γ δ p)
      (tracePhaseAnnulusStrip γ δ q) ≤ (Kh : ℝ≥0∞) * edist p q)
    {s η : ℝ} (hsector : ∀ t : ℝ, |t - s| < η → R (t : loopCircle) = 1) :
    ∃ dFill : C(closedDisk, M), ∃ K : ℝ≥0,
      (∀ z : closedDisk, dFill z = relativeDiskAnnulus R (diskExtension v)
        (tracePhaseAnnulusStrip γ δ) z) ∧
      (∀ z w : ℂ, riemannianEDistOf g
        (relativeDiskAnnulus R (diskExtension v) (tracePhaseAnnulusStrip γ δ) z)
        (relativeDiskAnnulus R (diskExtension v) (tracePhaseAnnulusStrip γ δ) w) ≤
          (K : ℝ≥0∞) * edist z w) ∧
      diskTrace dFill = γ ∧ range dFill = range v ∧
      (∀ z w : closedDisk, riemannianEDistOf g (dFill z) (dFill w) ≤
        (K : ℝ≥0∞) * edist z w) ∧
      (∀ t : ℝ, |t - s| < η → ∀ r ∈ Icc (1 / 2 : ℝ) 1,
        diskExtension dFill (r • (diskBoundary (t : loopCircle) : ℂ)) =
          diskExtension v (r • (diskBoundary (t : loopCircle) : ℂ))) := by
  let H := tracePhaseAnnulusStrip γ δ
  let F := relativeDiskAnnulus R (diskExtension v) H
  have htr (t : ℝ) : diskExtension v (AddCircle.toCircle (t : loopCircle) : ℂ) =
      γ (ρ t : loopCircle) := (diskExtension_coe v (diskBoundary (t : loopCircle))).trans (htrace t)
  have hglue := relative_phase_glue hδ htr hlo hhi hcompat
  obtain ⟨K, hK⟩ := relativeDiskAnnulus_riemannian_lipschitz g hR hlo
    (diskExtension_riemannian_lipschitz g hu) hH hglue
  have hF : Continuous F := continuous_of_riemannian_lipschitz g hK
  let dFill : C(closedDisk, M) := ⟨fun z => F z, hF.comp continuous_subtype_val⟩
  refine ⟨dFill, K, (fun _ => rfl), hK, ?_, ?_, ?_, ?_⟩
  · ext θ
    exact (relativeDiskAnnulus_boundary R (diskExtension v) H hhi hglue θ).trans
      (tracePhaseAnnulusStrip_one θ)
  · exact relative_phase_range hm hp hc htrace hlo hhi
  · exact fun z w => hK z w
  · intro t ht r hr
    have hrpos : 0 < r := lt_of_lt_of_le (by norm_num) hr.1
    let z : closedDisk := ⟨r • (diskBoundary (t : loopCircle) : ℂ), by
      apply mem_closedBall_zero_iff.mpr
      change ‖r • (AddCircle.toCircle (t : loopCircle) : ℂ)‖ ≤ 1
      simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos hrpos, Circle.norm_coe, mul_one] using hr.2⟩
    change diskExtension dFill (z : ℂ) = diskExtension v (z : ℂ)
    rw [diskExtension_coe]
    exact relativeDiskAnnulus_eq_on_sector (diskExtension v) H (hsector t ht) hrpos hr.2

omit [FiniteDimensional ℝ E] in
/-- Construct the literal relative annulus and its continuous disk. The area
identity is a separate change-of-variables theorem for this same construction. -/
theorem exists_relative_phase_filling_data
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {v : C(closedDisk, M)} {γ : freeLoop M} {Ku : ℝ≥0}
    (hu : ∀ z w : closedDisk, riemannianEDistOf g (v z) (v w) ≤ (Ku : ℝ≥0∞) * edist z w)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (fun t : ℝ => γ (t : loopCircle)))
    {ρ : ℝ → ℝ} (hρ : ContDiff ℝ ∞ ρ) (hm : Monotone ρ)
    (hp : ∀ t, ρ (t + 1) = ρ t + 1)
    (htrace : ∀ t : ℝ, diskTrace v (t : loopCircle) = γ (ρ t : loopCircle))
    {s ε : ℝ} (hε : 0 < ε) (hlocal : ∀ t : ℝ, |t - s| < ε → ρ t = t) :
    ∃ R δ : loopCircle → ℝ, ∃ Kr Kh : ℝ≥0, ∃ dFill : C(closedDisk, M), ∃ K : ℝ≥0,
      LipschitzWith Kr R ∧ (∀ θ, 1 / 2 ≤ R θ) ∧ (∀ θ, R θ ≤ 1) ∧
      (∀ t : ℝ, δ (t : loopCircle) = ρ t - t) ∧
      (∀ p q, riemannianEDistOf g (tracePhaseAnnulusStrip γ δ p)
        (tracePhaseAnnulusStrip γ δ q) ≤ (Kh : ℝ≥0∞) * edist p q) ∧
      cylinderArea g (tracePhaseAnnulusStrip γ δ) = 0 ∧
      (∀ z : closedDisk, dFill z = relativeDiskAnnulus R (diskExtension v)
        (tracePhaseAnnulusStrip γ δ) z) ∧
      (∀ z w : ℂ, riemannianEDistOf g
        (relativeDiskAnnulus R (diskExtension v) (tracePhaseAnnulusStrip γ δ) z)
        (relativeDiskAnnulus R (diskExtension v) (tracePhaseAnnulusStrip γ δ) w) ≤
          (K : ℝ≥0∞) * edist z w) ∧
      diskTrace dFill = γ ∧ range dFill = range v ∧
      (∀ z w : closedDisk, riemannianEDistOf g (dFill z) (dFill w) ≤
        (K : ℝ≥0∞) * edist z w) ∧
      (∀ t : ℝ, |t - s| < ε / 4 → ∀ r ∈ Icc (1 / 2 : ℝ) 1,
        diskExtension dFill (r • (diskBoundary (t : loopCircle) : ℂ)) =
          diskExtension v (r • (diskBoundary (t : loopCircle) : ℂ))) := by
  have hper : Function.Periodic (fun t : ℝ => ρ t - t) 1 := by
    intro t
    change ρ (t + 1) - (t + 1) = ρ t - t
    rw [hp]
    ring
  let δ : loopCircle → ℝ := hper.lift
  have hδ (t : ℝ) : δ (t : loopCircle) = ρ t - t := hper.lift_coe t
  obtain ⟨Lδ, hδL⟩ := periodic_smooth_displacement_lipschitz (hρ.sub contDiff_id) hper
  obtain ⟨R, ⟨Kr, hR⟩, hbounds, hcompat, hsector⟩ := exists_relative_phase_radius hδ hε hlocal
  have hlo (θ : loopCircle) := (hbounds θ).1
  have hhi (θ : loopCircle) := (hbounds θ).2
  obtain ⟨Lγ, hγL⟩ := exists_riemannian_lipschitz_freeLoop_of_contMDiff g (hγ.of_le (by simp))
  obtain ⟨C, hC⟩ := tracePhaseAnnulus_lipschitzOn_strip g hγL hδL
  obtain ⟨Kh, hH⟩ := tracePhaseAnnulusStrip_lipschitz_of_strip g hC
  obtain ⟨dFill, K, hd, hF, ht, hrange, hLip, hsec⟩ :=
    exists_relative_phase_filling_of_radius g hm hp hρ.continuous htrace hR hlo hhi hδ
      hcompat hu hH hsector
  exact ⟨R, δ, Kr, Kh, dFill, K, hR, hlo, hhi, hδ, hH,
    cylinderArea_tracePhaseAnnulusStrip_eq_zero g hγ hρ hδ, hd, hF, ht, hrange, hLip, hsec⟩


/-- Correct the whole boundary phase at zero area cost, using the same disk and
original metric and retaining a genuine inward sector pointwise. -/
theorem exists_relative_phase_correction
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {v : C(closedDisk, M)} {γ : freeLoop M} {Ku : ℝ≥0}
    (hu : ∀ z w : closedDisk, riemannianEDistOf g (v z) (v w) ≤ (Ku : ℝ≥0∞) * edist z w)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (fun t : ℝ => γ (t : loopCircle)))
    {ρ : ℝ → ℝ} (hρ : ContDiff ℝ ∞ ρ) (hm : Monotone ρ)
    (hp : ∀ t, ρ (t + 1) = ρ t + 1)
    (htrace : ∀ t : ℝ, diskTrace v (t : loopCircle) = γ (ρ t : loopCircle))
    {s ε : ℝ} (hε : 0 < ε) (hlocal : ∀ t : ℝ, |t - s| < ε → ρ t = t) :
    ∃ dFill : C(closedDisk, M), ∃ K : ℝ≥0, ∃ η : ℝ,
      0 < η ∧ η < ε ∧ diskTrace dFill = γ ∧
      riemannianDiskArea g dFill = riemannianDiskArea g v ∧ range dFill = range v ∧
      (∀ z w : closedDisk, riemannianEDistOf g (dFill z) (dFill w) ≤
        (K : ℝ≥0∞) * edist z w) ∧
      (∀ t : ℝ, |t - s| < η → ∀ r ∈ Icc (1 / 2 : ℝ) 1,
        diskExtension dFill (r • (diskBoundary (t : loopCircle) : ℂ)) =
          diskExtension v (r • (diskBoundary (t : loopCircle) : ℂ))) := by
  obtain ⟨R, δ, Kr, Kh, dFill, K, hR, hlo, hhi, hδ, hH, _hzero, hd, hF,
      htraceFill, hrange, hLip, hsector⟩ :=
    exists_relative_phase_filling_data g hu hγ hρ hm hp htrace hε hlocal
  let F := relativeDiskAnnulus R (diskExtension v) (tracePhaseAnnulusStrip γ δ)
  have htr (t : ℝ) : diskExtension v (AddCircle.toCircle (t : loopCircle) : ℂ) =
      γ (ρ t : loopCircle) :=
    (diskExtension_coe v (diskBoundary (t : loopCircle))).trans (htrace t)
  have hinner (z : ℂ) (hz : ‖z‖ ≤ R (polarAnnulusCoordinates z).2) :
      F z = diskExtension v (radialProfileInv R z) :=
    relativeDiskAnnulus_inner R (diskExtension v) (tracePhaseAnnulusStrip γ δ) hz
  have houter (z : ℂ) (hz : ¬ ‖z‖ ≤ R (polarAnnulusCoordinates z).2) :
      F z = tracePhaseAnnulusStrip γ δ (polarAnnulusCoordinates z) := ite_eq_right hz
  have hareaF : riemannianArea g F (closedBall (0 : ℂ) 1) = riemannianDiskArea g v :=
    riemannianArea_relative_tracePhase_pasting g (diskExtension_riemannian_lipschitz g hu)
      hF hR hlo hhi hγ hρ hδ htr hH hinner houter
  have harea : riemannianDiskArea g dFill = riemannianDiskArea g v := by
    calc
      _ = riemannianArea g F (closedBall (0 : ℂ) 1) := by
        apply riemannianArea_congr_on_closedBall g
        intro z hz
        exact (diskExtension_coe dFill ⟨z, hz⟩).trans (hd ⟨z, hz⟩)
      _ = _ := hareaF
  exact ⟨dFill, K, ε / 4, by positivity, by linarith, htraceFill, harea, hrange, hLip, hsector⟩

end DifferentialGeometry.Geometry
