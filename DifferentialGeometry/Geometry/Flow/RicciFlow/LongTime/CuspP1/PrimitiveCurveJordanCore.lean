import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.PrimitiveCurveJordanHomotopy
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.PrimitiveCurveJordanPlane

set_option autoImplicit false
noncomputable section
open Set Metric Schoenflies DifferentialGeometry.Topology DifferentialGeometry.Topology.PlanarJordan
namespace GC.LongTime.CuspP1

/-- A bijective continuous circle-valued loop has lift degree `±1`. -/
theorem exists_lift_of_bijective_CPP2 (u₀ : C(loopCircle, Circle)) (hb : Function.Bijective u₀) :
    ∃ (F : ℝ → ℝ) (n : ℤ), Continuous F ∧ (n = 1 ∨ n = -1) ∧
      (∀ t : ℝ, u₀ (t : loopCircle) = Circle.exp (2 * Real.pi * F t)) ∧
      ∀ t, F (t + 1) = F t + n := by
  let φ : loopCircle ≃ₜ Circle := AddCircle.homeomorphCircle (one_ne_zero : (1 : ℝ) ≠ 0)
  let e : loopCircle ≃ₜ Circle := u₀.continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective u₀ hb)
  let ρ : loopCircle ≃ₜ loopCircle := e.trans φ.symm
  have hρ : ∀ θ, φ (ρ θ) = u₀ θ := fun θ => φ.apply_symm_apply (u₀ θ)
  rcases circleHomeomorph_affineLift_or_neg ρ with ⟨Fa, hp, -, hFa⟩ | ⟨Fa, hp, -, hFa⟩
  · refine ⟨Fa, 1, Fa.continuous, Or.inl rfl, fun t => ?_, fun t => by simpa using hp t⟩
    rw [← hρ, hFa, affineCircleMap_coe, coe_mk_eq_exp_CPP2]
  · refine ⟨fun t => - Fa t, -1, Fa.continuous.neg, Or.inr rfl, fun t => ?_,
      fun t => by simp [hp t]; ring⟩
    have h1 : ρ (t : loopCircle) = ((-Fa t : ℝ) : loopCircle) := by
      rw [hFa]
      simp only [affineCircleMap_coe, AddCircle.coe_neg]
    rw [← hρ, h1, coe_mk_eq_exp_CPP2]

private def sphereCircle_CPP2 : sphere (0 : Plane) 1 ≃ₜ Circle :=
  (planeHomeo_CPP2.subtype (p := fun z : ℂ => z ∈ sphere (0 : ℂ) 1)
    (q := fun z : Plane => z ∈ sphere (0 : Plane) 1) fun z => by
      rw [mem_sphere_zero_iff_norm, mem_sphere_zero_iff_norm, planeHomeo_norm_CPP2]).symm

theorem sphereCircle_coe_CPP2 (z : sphere (0 : Plane) 1) :
    ((sphereCircle_CPP2 z : Circle) : ℂ) = planeHomeo_CPP2.symm (z : Plane) := rfl

/-- The loop is a nonvanishing embedded loop in the plane whose complement-of-the-origin direction
has lift-degree `n`, `0 ∈ outside`: then `n = 0`. -/
theorem degree_zero_of_outside_CPP2 (Ω : loopCircle → Plane) (hΩc : Continuous Ω)
    (hinj : Function.Injective Ω) (hne : ∀ θ, Ω θ ≠ 0)
    (hout : (0 : Plane) ∉ inside (range Ω))
    (F : ℝ → ℝ) (hF : Continuous F) (n : ℤ)
    (hlift : ∀ t : ℝ, dirOf_CPP2 (planeHomeo_CPP2.symm (Ω (t : loopCircle))) =
      Circle.exp (2 * Real.pi * F t))
    (hshift : ∀ t, F (t + 1) = F t + n) : n = 0 := by
  let φ : loopCircle ≃ₜ Circle := AddCircle.homeomorphCircle (one_ne_zero : (1 : ℝ) ≠ 0)
  let sph : loopCircle ≃ₜ sphere (0 : Plane) 1 := φ.trans sphereCircle_CPP2.symm
  have hΩemb : Topology.IsEmbedding Ω := (hΩc.isClosedEmbedding hinj).isEmbedding
  have hemb : Topology.IsEmbedding (fun z : sphere (0 : Plane) 1 => Ω (sph.symm z)) := by
    refine (Continuous.isClosedEmbedding (hΩc.comp sph.symm.continuous) ?_).isEmbedding
    exact hinj.comp sph.symm.injective
  obtain ⟨Fp, hFp⟩ := exists_homeomorph_extending_circle_embedding hemb
  have hΩFp : ∀ θ, Ω θ = Fp (sph θ) := fun θ => by
    rw [hFp]; simp
  have hsph1 : ∀ z : sphere (0 : Plane) 1, ‖(z : Plane)‖ = 1 := fun z => by
    simp
  have hnot : ∀ x : Plane, ‖x‖ ≤ 1 → Fp x ≠ 0 := by
    intro x hx h0
    rcases hx.lt_or_eq with hlt | heq
    · have hxin : x ∈ inside (sphere (0 : Plane) 1) := by
        rw [inside_sphere_CPP2 one_pos]; simpa using hlt
      have himg : Fp '' sphere (0 : Plane) 1 = range Ω := by
        ext y
        constructor
        · rintro ⟨z, hz, rfl⟩
          refine ⟨sph.symm ⟨z, hz⟩, ?_⟩
          rw [hΩFp]; simp
        · rintro ⟨θ, rfl⟩
          exact ⟨sph θ, (sph θ).2, (hΩFp θ).symm⟩
      apply hout
      have h1 : (0 : Plane) ∈ Fp '' inside (sphere (0 : Plane) 1) := ⟨x, hxin, h0⟩
      rwa [image_inside, himg] at h1
    · have hxs : x ∈ sphere (0 : Plane) 1 := by simpa using heq
      have := hFp ⟨x, hxs⟩
      change Fp x = Ω (sph.symm ⟨x, hxs⟩) at this
      exact hne _ (this ▸ h0)
  -- homotopy to a constant loop
  let H : unitInterval × ℝ → ℂ := fun st =>
    planeHomeo_CPP2.symm (Fp ((st.1 : ℝ) • (sph (st.2 : loopCircle) : Plane)))
  have hHc : Continuous H := by
    refine planeHomeo_CPP2.symm.continuous.comp (Fp.continuous.comp ?_)
    exact (continuous_subtype_val.comp continuous_fst).smul
      (continuous_subtype_val.comp (sph.continuous.comp
        ((AddCircle.continuous_mk' (1 : ℝ)).comp continuous_snd)))
  have hHne : ∀ st, H st ≠ 0 := by
    intro st h0
    have h1 : Fp ((st.1 : ℝ) • (sph (st.2 : loopCircle) : Plane)) = 0 := by
      have := congrArg planeHomeo_CPP2 h0
      simpa [H, planeHomeo_zero_CPP2] using this
    refine hnot _ ?_ h1
    rw [norm_smul, hsph1, mul_one, Real.norm_eq_abs, abs_of_nonneg st.1.2.1]
    exact st.1.2.2
  have hG : Continuous (fun st => dirOf_CPP2 (H st)) := continuous_dirOf_comp_CPP2 hHc hHne
  have hper : ∀ (s : unitInterval) (t : ℝ), dirOf_CPP2 (H (s, t + 1)) = dirOf_CPP2 (H (s, t)) := by
    intro s t
    simp only [H, AddCircle.coe_add_period]
  have hl₁ : ∀ t : ℝ, dirOf_CPP2 (H (1, t)) = Circle.exp (2 * Real.pi * F t) := by
    intro t
    rw [← hlift t]
    congr 1
    simp only [H, Set.Icc.coe_one, one_smul]
    rw [← hΩFp]
  obtain ⟨x0, hx0⟩ : ∃ x0 : ℝ, dirOf_CPP2 (planeHomeo_CPP2.symm (Fp 0)) =
      Circle.exp (2 * Real.pi * x0) := by
    refine ⟨Complex.arg (dirOf_CPP2 (planeHomeo_CPP2.symm (Fp 0))) / (2 * Real.pi), ?_⟩
    rw [show 2 * Real.pi * (Complex.arg (dirOf_CPP2 (planeHomeo_CPP2.symm (Fp 0))) /
      (2 * Real.pi)) = Complex.arg (dirOf_CPP2 (planeHomeo_CPP2.symm (Fp 0))) by
        field_simp]
    exact (Circle.exp_arg _).symm
  have hl₀ : ∀ t : ℝ, dirOf_CPP2 (H (0, t)) = Circle.exp (2 * Real.pi * x0) := by
    intro t
    rw [← hx0]
    simp [H]
  have := degree_eq_of_homotopy_CPP2 (fun st => dirOf_CPP2 (H st)) hG hper (fun _ => x0) F
    continuous_const hF 0 n hl₀ hl₁ (fun t => by simp) hshift
  exact this.symm

/-- `0 ∈ inside`: the degree is `±1`. -/
theorem degree_pm_one_of_inside_CPP2 (Ω : loopCircle → Plane) (hΩc : Continuous Ω)
    (hinj : Function.Injective Ω)
    (hin : (0 : Plane) ∈ inside (range Ω))
    (F : ℝ → ℝ) (hF : Continuous F) (n : ℤ)
    (hlift : ∀ t : ℝ, dirOf_CPP2 (planeHomeo_CPP2.symm (Ω (t : loopCircle))) =
      Circle.exp (2 * Real.pi * F t))
    (hshift : ∀ t, F (t + 1) = F t + n) : n = 1 ∨ n = -1 := by
  have hΩemb : Topology.IsEmbedding Ω := (hΩc.isClosedEmbedding hinj).isEmbedding
  have hC : IsJordanCurve (range Ω) :=
    isJordanCurve_range_of_isEmbedding_addCircle one_ne_zero hΩemb
  have hsep := jordan_curve_theorem hC
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hsep.isOpen_inside 0 hin
  have hr : 0 < ε / 2 := half_pos hε
  have hS := isJordanCurve_sphere_CPP2 hr
  have hball' : ball (0 : Plane) (ε / 2) ⊆ inside (range Ω) :=
    (ball_subset_ball (by linarith)).trans hball
  have hnest : closure (inside (sphere (0 : Plane) (ε / 2))) ⊆ inside (range Ω) := by
    rw [closure_inside_sphere_CPP2 hr]
    intro x hx
    apply hball
    rw [mem_ball_zero_iff]
    have := mem_closedBall_zero_iff.mp hx
    linarith
  obtain ⟨P, hP0, hP1⟩ := Homeomorph.exists_homeomorph_jordan_annulus hS hC hnest
  have hCsub : range Ω ⊆ closure (inside (range Ω)) := by
    intro x hx
    have hfr := hsep.frontier_closure_inside
    rw [← hfr] at hx
    have := frontier_subset_closure hx
    rwa [closure_closure] at this
  have hmem : ∀ θ, Ω θ ∈ closure (inside (range Ω)) \ inside (sphere (0 : Plane) (ε / 2)) := by
    intro θ
    refine ⟨hCsub ⟨θ, rfl⟩, fun hh => ?_⟩
    rw [inside_sphere_CPP2 hr] at hh
    exact (hball' hh).1 ⟨θ, rfl⟩
  let A : loopCircle → ↥(closure (inside (range Ω)) \ inside (sphere (0 : Plane) (ε / 2))) :=
    fun θ => ⟨Ω θ, hmem θ⟩
  have hAc : Continuous A := hΩc.subtype_mk _
  let Ψ : loopCircle → unitInterval × loopCircle := fun θ => P.symm (A θ)
  have hΨc : Continuous Ψ := P.symm.continuous.comp hAc
  have hΨeq : ∀ θ, Ψ θ = (1, (Ψ θ).2) := by
    intro θ
    have hx : Ω θ ∈ range (fun a => (P (1, a) : Plane)) := by
      rw [hP1]; exact ⟨θ, rfl⟩
    obtain ⟨a, ha⟩ := hx
    have hPa : P (1, a) = A θ := Subtype.ext ha
    have : Ψ θ = (1, a) := by
      change P.symm (A θ) = _
      rw [← hPa]; exact P.symm_apply_apply _
    rw [this]
  let ψ : loopCircle → loopCircle := fun θ => (Ψ θ).2
  have hψc : Continuous ψ := continuous_snd.comp hΨc
  have hPψ : ∀ θ, (P (1, ψ θ) : Plane) = Ω θ := by
    intro θ
    have h1 : P (Ψ θ) = A θ := P.apply_symm_apply _
    rw [hΨeq θ] at h1
    exact congrArg Subtype.val h1
  have hψinj : Function.Injective ψ := by
    intro θ θ' h
    apply hinj
    rw [← hPψ θ, ← hPψ θ', h]
  have hψsurj : Function.Surjective ψ := by
    intro a
    have hx : (P (1, a) : Plane) ∈ range Ω := by
      have h : (P (1, a) : Plane) ∈ range (fun a => (P (1, a) : Plane)) := ⟨a, rfl⟩
      rwa [hP1] at h
    obtain ⟨θ, hθ⟩ := hx
    refine ⟨θ, ?_⟩
    have : P (1, ψ θ) = P (1, a) := Subtype.ext ((hPψ θ).trans hθ)
    exact (Prod.mk.inj (P.injective this)).2
  have h0S : (0 : Plane) ∈ inside (sphere (0 : Plane) (ε / 2)) := by
    rw [inside_sphere_CPP2 hr]; exact mem_ball_self hr
  have hPne : ∀ q : unitInterval × loopCircle, planeHomeo_CPP2.symm (P q : Plane) ≠ 0 := by
    intro q
    apply planeHomeo_symm_ne_zero_CPP2
    intro h0
    exact (P q).2.2 (by rw [h0]; exact h0S)
  let Ω₀ : loopCircle → Plane := fun θ => (P (0, ψ θ) : Plane)
  have hΩ₀mem : ∀ θ, ‖Ω₀ θ‖ = ε / 2 := by
    intro θ
    have : Ω₀ θ ∈ sphere (0 : Plane) (ε / 2) := by
      rw [← hP0]; exact ⟨ψ θ, rfl⟩
    simpa using this
  have hΩ₀range : range Ω₀ = sphere (0 : Plane) (ε / 2) := by
    rw [← hP0]
    exact hψsurj.range_comp (fun a => (P (0, a) : Plane))
  let u₀ : C(loopCircle, Circle) := ⟨fun θ => dirOf_CPP2 (planeHomeo_CPP2.symm (Ω₀ θ)), by
    refine continuous_dirOf_comp_CPP2 ?_ (fun θ => hPne _)
    exact planeHomeo_CPP2.symm.continuous.comp
      (continuous_subtype_val.comp (P.continuous.comp
        (continuous_const.prodMk hψc)))⟩
  have hw : ∀ θ, ‖planeHomeo_CPP2.symm (Ω₀ θ)‖ = ε / 2 := by
    intro θ
    rw [← planeHomeo_norm_CPP2, planeHomeo_CPP2.apply_symm_apply, hΩ₀mem]
  have hu₀ : ∀ θ, (u₀ θ : ℂ) = planeHomeo_CPP2.symm (Ω₀ θ) / ((ε / 2 : ℝ) : ℂ) := by
    intro θ
    change (dirOf_CPP2 _ : ℂ) = _
    rw [coe_dirOf_CPP2 (hPne _), hw]
  have hu₀b : Function.Bijective u₀ := by
    constructor
    · intro θ θ' h
      have h1 : (u₀ θ : ℂ) = u₀ θ' := congrArg Subtype.val h
      rw [hu₀, hu₀] at h1
      have hrc : ((ε / 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
      have h2 := (div_left_inj' hrc).mp h1
      have h3 : Ω₀ θ = Ω₀ θ' := planeHomeo_CPP2.symm.injective h2
      have h4 : P (0, ψ θ) = P (0, ψ θ') := Subtype.ext h3
      exact hψinj (Prod.mk.inj (P.injective h4)).2
    · intro c
      have hx : planeHomeo_CPP2 (((ε / 2 : ℝ) : ℂ) * c) ∈ range Ω₀ := by
        rw [hΩ₀range, mem_sphere_zero_iff_norm, planeHomeo_norm_CPP2, norm_mul,
          Complex.norm_real, Circle.norm_coe, mul_one, Real.norm_of_nonneg hr.le]
      obtain ⟨θ, hθ⟩ := hx
      refine ⟨θ, ?_⟩
      change dirOf_CPP2 (planeHomeo_CPP2.symm (Ω₀ θ)) = c
      rw [hθ, planeHomeo_CPP2.symm_apply_apply]
      exact dirOf_mul_CPP2 hr c
  obtain ⟨F₀, n₀, hF₀c, hn₀, hl₀', hs₀⟩ := exists_lift_of_bijective_CPP2 u₀ hu₀b
  let H : unitInterval × ℝ → ℂ := fun st =>
    planeHomeo_CPP2.symm (P (st.1, ψ (st.2 : loopCircle)) : Plane)
  have hHc : Continuous H := by
    refine planeHomeo_CPP2.symm.continuous.comp (continuous_subtype_val.comp (P.continuous.comp ?_))
    exact continuous_fst.prodMk (hψc.comp ((AddCircle.continuous_mk' (1 : ℝ)).comp continuous_snd))
  have hG : Continuous (fun st => dirOf_CPP2 (H st)) :=
    continuous_dirOf_comp_CPP2 hHc (fun st => hPne _)
  have hper : ∀ (s : unitInterval) (t : ℝ), dirOf_CPP2 (H (s, t + 1)) = dirOf_CPP2 (H (s, t)) := by
    intro s t
    simp only [H, AddCircle.coe_add_period]
  have hl₀ : ∀ t : ℝ, dirOf_CPP2 (H (0, t)) = Circle.exp (2 * Real.pi * F₀ t) := by
    intro t
    rw [← hl₀' t]
    rfl
  have hl₁ : ∀ t : ℝ, dirOf_CPP2 (H (1, t)) = Circle.exp (2 * Real.pi * F t) := by
    intro t
    rw [← hlift t]
    simp only [H, hPψ]
  have := degree_eq_of_homotopy_CPP2 (fun st => dirOf_CPP2 (H st)) hG hper F₀ F hF₀c hF n₀ n
    hl₀ hl₁ hs₀ hshift
  rw [← this]
  exact hn₀

/-- **Core.**  An injective loop `(u, h) : S¹ → Circle × ℝ` (an embedded circle in the open annulus)
has `u` of lift-degree `-1`, `0` or `1`. -/
theorem degree_cases_of_embedded_annulus_CPP2
    (u : C(loopCircle, Circle)) (h : C(loopCircle, ℝ))
    (hinj : Function.Injective fun θ => (u θ, h θ))
    (F : ℝ → ℝ) (hF : Continuous F) (n : ℤ)
    (hlift : ∀ t : ℝ, u (t : loopCircle) = Circle.exp (2 * Real.pi * F t))
    (hshift : ∀ t, F (t + 1) = F t + n) : n = -1 ∨ n = 0 ∨ n = 1 := by
  let Ωc : loopCircle → ℂ := fun θ => (Real.exp (h θ) : ℂ) * (u θ : ℂ)
  have hΩc : Continuous Ωc :=
    (Complex.continuous_ofReal.comp (Real.continuous_exp.comp h.continuous)).mul
      (continuous_subtype_val.comp u.continuous)
  have hdir : ∀ θ, dirOf_CPP2 (Ωc θ) = u θ := fun θ => dirOf_mul_CPP2 (Real.exp_pos _) _
  have hne : ∀ θ, Ωc θ ≠ 0 := fun θ =>
    mul_ne_zero (by exact_mod_cast (Real.exp_pos _).ne') (u θ).coe_ne_zero
  let Ω : loopCircle → Plane := fun θ => planeHomeo_CPP2 (Ωc θ)
  have hΩcont : Continuous Ω := planeHomeo_CPP2.continuous.comp hΩc
  have hnorm : ∀ θ, ‖Ωc θ‖ = Real.exp (h θ) := by
    intro θ
    rw [norm_mul, Complex.norm_real, Circle.norm_coe, mul_one, Real.norm_of_nonneg (Real.exp_pos _).le]
  have hinjΩ : Function.Injective Ω := by
    intro θ θ' hθ
    have h1 : Ωc θ = Ωc θ' := planeHomeo_CPP2.injective hθ
    have h2 : h θ = h θ' := by
      have := congrArg norm h1
      rw [hnorm, hnorm] at this
      exact Real.exp_injective this
    have h3 : u θ = u θ' := by
      apply Circle.ext
      have h4 : (Real.exp (h θ) : ℂ) ≠ 0 := by exact_mod_cast (Real.exp_pos _).ne'
      have h5 : (Real.exp (h θ) : ℂ) * (u θ : ℂ) = (Real.exp (h θ) : ℂ) * (u θ' : ℂ) := by
        have := h1
        simp only [Ωc, ← h2] at this
        exact this
      exact mul_left_cancel₀ h4 h5
    exact hinj (Prod.ext h3 h2)
  have hΩne : ∀ θ, Ω θ ≠ 0 := by
    intro θ h0
    apply hne θ
    apply planeHomeo_CPP2.injective
    rw [planeHomeo_zero_CPP2]
    exact h0
  have hlift' : ∀ t : ℝ, dirOf_CPP2 (planeHomeo_CPP2.symm (Ω (t : loopCircle))) =
      Circle.exp (2 * Real.pi * F t) := by
    intro t
    simp only [Ω, planeHomeo_CPP2.symm_apply_apply]
    rw [hdir, hlift]
  by_cases hin : (0 : Plane) ∈ inside (range Ω)
  · rcases degree_pm_one_of_inside_CPP2 Ω hΩcont hinjΩ hin F hF n hlift' hshift with h1 | h1
    · exact Or.inr (Or.inr h1)
    · exact Or.inl h1
  · exact Or.inr (Or.inl (degree_zero_of_outside_CPP2 Ω hΩcont hinjΩ hΩne hin F hF n hlift' hshift))

end GC.LongTime.CuspP1
