/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/
import DifferentialGeometry.Geometry.Curvature.Nonnegative
import DifferentialGeometry.Geometry.Metric.Comparison.CurveEnergy
import DifferentialGeometry.Geometry.Comparison.Variation.RadialEndpoint
import DifferentialGeometry.Geometry.Comparison.Toponogov.ConnectorSmooth
import DifferentialGeometry.Geometry.Comparison.Toponogov.ConvexityBridge
import DifferentialGeometry.Geometry.Comparison.Toponogov.RiemannianComparisonAngle
import DifferentialGeometry.Geometry.Comparison.Toponogov.SupportAlgebra

set_option autoImplicit false

noncomputable section

open Bundle Filter Function Manifold MeasureTheory Set
open scoped ENNReal Manifold ContDiff Topology
open DifferentialGeometry

namespace DifferentialGeometry.Toponogov

open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.Variation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [T2Space (TangentBundle I M)]
  [SigmaCompactSpace M] [BoundarylessManifold I M]

def squaredRiemannianDistanceDefect (g : SmoothRiemannianMetric I M)
    (p : M) (β : ℝ → M) (r : ℝ) : ℝ :=
  r ^ 2 - riemannianDistance (I := I) g p (β r) ^ 2

omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
    [I.Boundaryless] [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
    [BoundarylessManifold I M] in
private theorem riemannianEDistOf_toReal_sq_le_curveEnergy_of_contMDiffOn
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M} {a b : ℝ} (hab : a ≤ b)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc a b))
    (hE : IntegrableOn (fun t : ℝ => g.inner (γ t)
      (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))
      (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))) (Icc a b) (MeasureTheory.volume)) :
    (riemannianEDistOf (I := I) g (γ a) (γ b)).toReal ^ 2 ≤
      (b - a) * curveEnergy (I := I) g γ a b := by
  have hENN := edistOf_le_energy (I := I) g hab hγ hE
  have hright : ENNReal.ofReal (Real.sqrt (b - a) *
      Real.sqrt (curveEnergy (I := I) g γ a b)) ≠ (⊤ : ℝ≥0∞) := ENNReal.ofReal_ne_top
  have hleft : riemannianEDistOf (I := I) g (γ a) (γ b) ≠ (⊤ : ℝ≥0∞) :=
    ne_top_of_le_ne_top hright hENN
  have hreal := (ENNReal.toReal_le_toReal hleft hright).2 hENN
  rw [ENNReal.toReal_ofReal
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))] at hreal
  have hlen : 0 ≤ b - a := sub_nonneg.mpr hab
  have henergy : 0 ≤ curveEnergy (I := I) g γ a b := by
    apply intervalIntegral.integral_nonneg hab
    intro t _ht
    let v := mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)
    rcases eq_or_ne v 0 with hv | hv
    · simp only [v, hv, map_zero]
      exact le_rfl
    · exact (g.pos (γ t) v hv).le
  have hsquare := (sq_le_sq₀ ENNReal.toReal_nonneg
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).2 hreal
  calc
    (riemannianEDistOf (I := I) g (γ a) (γ b)).toReal ^ 2 ≤
        (Real.sqrt (b - a) * Real.sqrt (curveEnergy (I := I) g γ a b)) ^ 2 := hsquare
    _ = (b - a) * curveEnergy (I := I) g γ a b := by
      rw [mul_pow, Real.sq_sqrt hlen, Real.sq_sqrt henergy]

omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
    [I.Boundaryless] [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
    [BoundarylessManifold I M] in
private theorem inner_congr_of_base_eq (g : SmoothRiemannianMetric I M) {a b : M}
    {v w : TangentSpace I a} {v' w' : TangentSpace I b}
    (hab : a = b) (hv : v = v') (hw : w = w') :
    g.inner a v w = g.inner b v' w' := by
  subst hab
  rw [hv, hw]

omit [NeZero (Module.finrank ℝ E)] [T2Space (TangentBundle I M)]
    [SigmaCompactSpace M] in
theorem exists_squaredDistanceLowerSupport_of_positive
    (g : SmoothRiemannianMetric I M)
    (hsec : HasNonnegativeSectionalCurvature (I := I) g)
    (p : M) (β γ : ℝ → M) (J : Set ℝ) (r₀ L : ℝ)
    (hJ : r₀ ∈ interior J) (hL : 0 < L)
    (hγsmooth : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ)
    (hγgeo : IsGeodesicOn (I := I) g γ (Icc 0 L))
    (hγunit : ∀ t ∈ Icc (0 : ℝ) L,
      g.inner (γ t)
        (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))
        (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)) = 1)
    (hγ0 : γ 0 = p) (hγL : γ L = β r₀)
    (hdist : riemannianDistance (I := I) g p (β r₀) = L)
    (vL : TangentSpace I (γ L))
    (hvLunit : g.inner (γ L) vL vL = 1)
    (hβgeo : IsGeodesicAt (I := I) g (fun s : ℝ ↦ β (r₀ + s)) 0)
    (hβvel : (mfderiv 𝓘(ℝ, ℝ) I
      (fun s : ℝ ↦ β (r₀ + s)) 0 (1 : ℝ) : E) = vL) :
    ∃ S : LowerSupportAt
        (squaredRiemannianDistanceDefect (I := I) g p β) J r₀,
      S.supportDeriv r₀ =
        2 * r₀ - 2 * L * g.inner (γ L)
          (mfderiv 𝓘(ℝ, ℝ) I γ L (1 : ℝ))
          vL ∧
      ∃ C : C2LowerSupportAt
          (squaredRiemannianDistanceDefect (I := I) g p β) J r₀,
        deriv C.support r₀ =
          2 * r₀ - 2 * L * g.inner (γ L)
            (mfderiv 𝓘(ℝ, ℝ) I γ L (1 : ℝ)) vL := by
  classical
  let β' : ℝ → M := fun s : ℝ => β (r₀ + s)
  have hβ'0 : β' 0 = γ L := by
    simp only [β', add_zero]
    exact hγL.symm
  obtain ⟨D⟩ := exists_radialEndpointVariation (I := I) g γ β' L hL hγsmooth hγgeo
    hγunit vL hvLunit hβgeo hβ'0 hβvel
  let E : ℝ → ℝ := fun σ : ℝ => curveEnergy (I := I) g (fun t : ℝ => D.variation σ t) 0 L
  let energy : ℝ → ℝ := fun r : ℝ => E (r - r₀)
  have hE_deriv : ∀ σ : ℝ, HasDerivAt E
      (∫ t in (0 : ℝ)..L, firstEnergyDensity (I := I) g D.variation σ t) σ :=
    fun σ => curveEnergy_hasDerivAt (I := I) g D.variation D.smooth 0 L σ
  have hE_deriv2 : ∀ σ : ℝ, HasDerivAt (deriv E)
      (∫ t in (0 : ℝ)..L, secondEnergyDensity (I := I) g D.variation σ t) σ :=
    fun σ => curveEnergy_deriv_hasDerivAt (I := I) g D.variation D.smooth 0 L σ
  have hE_deriv' : ∀ σ : ℝ, HasDerivAt E (deriv E σ) σ :=
    fun σ => (hE_deriv σ).congr_deriv (hE_deriv σ).deriv.symm
  have hE_deriv2'' : ∀ σ : ℝ, HasDerivAt (deriv E) (deriv (deriv E) σ) σ :=
    fun σ => (hE_deriv2 σ).congr_deriv (hE_deriv2 σ).deriv.symm
  have hE_deriv2' : HasDerivAt (deriv E) (deriv (deriv E) 0) 0 := hE_deriv2'' 0
  have hderiv2E : deriv (deriv E) = fun σ : ℝ => ∫ t in (0 : ℝ)..L,
      secondEnergyDensity (I := I) g D.variation σ t :=
    funext fun σ => (hE_deriv2 σ).deriv
  have hcont2 : Continuous (deriv (deriv E)) := by
    rw [hderiv2E]
    refine continuous_iff_continuousAt.mpr fun σ => ?_
    have hcd : ContDiffOn ℝ 1 (fun p : ℝ × ℝ =>
        secondEnergyDensity (I := I) g D.variation p.1 p.2) (Set.univ ×ˢ Set.univ) :=
      ((secondEnergyDensity_contDiff (I := I) (M := M) g D.variation D.smooth).contDiffOn).of_le
        (by norm_num)
    exact (DifferentialGeometry.Analysis.Calculus.hasFDerivAt_paramInt
      (fun σ t : ℝ => secondEnergyDensity (I := I) g D.variation σ t)
      Set.univ isOpen_univ 0 L Set.univ isOpen_univ (by simp) σ (by simp) hcd).continuousAt
  have hE_contDiffOn : ContDiffOn ℝ 2 E Set.univ := by
    change ContDiffOn ℝ ((1 : WithTop ℕ∞) + 1) E Set.univ
    rw [contDiffOn_succ_iff_deriv_of_isOpen (s := Set.univ) isOpen_univ]
    refine ⟨fun x _ => (hE_deriv x).differentiableAt.differentiableWithinAt, ?_, ?_⟩
    · intro h
      exact absurd h (by simp)
    · rw [contDiffOn_one_iff_derivWithin uniqueDiffOn_univ]
      refine ⟨fun x _ => (hE_deriv2 x).differentiableAt.differentiableWithinAt, ?_⟩
      rw [derivWithin_univ]
      exact hcont2.continuousOn
  have henergy_contDiff : ContDiff ℝ 2 energy := by
    have hcomp : ContDiff ℝ 2 (fun r : ℝ => E (r - r₀)) :=
      (contDiffOn_univ.mp hE_contDiffOn).comp (contDiff_id.sub contDiff_const)
    simpa only [energy] using hcomp
  have hE0 : deriv E 0 = 2 * g.inner (γ L)
      (mfderiv 𝓘(ℝ, ℝ) I γ L (1 : ℝ)) vL := by
    have hfirst := firstVariation_curveEnergy_geodesic_fixedInitial (I := I) g
      (fun t : ℝ => D.variation 0 t) D.variation L D.smooth hL D.centralGeodesic
      (fun _ => rfl) D.fixedInitial D.centralUnitSpeed
    have hbaseL : D.variation 0 L = γ L := by
      rw [D.central L, D.agrees L ⟨hL.le, le_rfl⟩]
    have hbaseGerm : (fun t : ℝ => D.variation 0 t) =ᶠ[𝓝 L] γ := by
      filter_upwards [D.agreesGerm L ⟨hL.le, le_rfl⟩] with t ht
      rw [D.central t, ht]
    have hvelbase : mfderiv 𝓘(ℝ, ℝ) I (fun t : ℝ => D.variation 0 t) L (1 : ℝ) =
        mfderiv 𝓘(ℝ, ℝ) I γ L (1 : ℝ) := by
      rw [hbaseGerm.mfderiv_eq]
      rfl
    have hvelterm : mfderiv 𝓘(ℝ, ℝ) I (fun u : ℝ => D.variation u L) 0 (1 : ℝ) = vL := by
      rw [D.terminalGerm.mfderiv_eq]
      exact hβvel
    have hinner := inner_congr_of_base_eq (I := I) g hbaseL hvelterm hvelbase
    rw [← g.symm (γ L) (mfderiv 𝓘(ℝ, ℝ) I γ L (1 : ℝ)) vL] at hinner
    change deriv (fun s : ℝ => curveEnergy (I := I) g (fun t : ℝ => D.variation s t) 0 L) 0 = _
    rw [hfirst.deriv, hinner]
  have henergy_r₀ : energy r₀ = L := by
    have hcurve : energy r₀ = curveEnergy (I := I) g (fun t : ℝ => D.variation 0 t) 0 L := by
      simp only [energy, E, sub_self]
    rw [hcurve, curveEnergy_slice_eq_integral_speedSq]
    have hInt : (∫ t in (0 : ℝ)..L, speedSq (I := I) g D.variation 0 t) =
        ∫ _t in (0 : ℝ)..L, (1 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le hL.le] at ht
      simpa only [speedSq] using D.centralUnitSpeed t ht
    rw [hInt, intervalIntegral.integral_const]
    ring
  have hslice_smooth : ∀ σ : ℝ, ContMDiffOn 𝓘(ℝ, ℝ) I 1
      (fun t : ℝ => D.variation σ t) (Icc (0 : ℝ) L) := by
    intro σ
    have h : ContMDiff 𝓘(ℝ, ℝ) I 8 (fun t : ℝ => D.variation σ t) :=
      (D.smooth : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I 8
        (fun p : ℝ × ℝ => D.variation p.1 p.2)).comp
        (contMDiff_const.prodMk contMDiff_id)
    exact h.contMDiffOn.of_le (by norm_num)
  have hV_bound : ∀ r : ℝ, D.variation (r - r₀) L = β r →
      riemannianDistance (I := I) g p (β r) ^ 2 ≤ L * energy r := by
    intro r hr
    have hc0 : (fun t : ℝ => D.variation (r - r₀) t) 0 = p := by
      change D.variation (r - r₀) 0 = p
      rw [D.fixedInitial (r - r₀), D.central 0, D.agrees 0 ⟨le_rfl, hL.le⟩, hγ0]
    have hbound := riemannianEDistOf_toReal_sq_le_curveEnergy_of_contMDiffOn (I := I) g
      (γ := fun t : ℝ => D.variation (r - r₀) t) hL.le (hslice_smooth (r - r₀))
      (integrableOn_inner_mfderiv_self_of_contMDiffOn (I := I) g (hslice_smooth (r - r₀)))
    have hbound' : (riemannianEDistOf (I := I) g p (β r)).toReal ^ 2 ≤
        (L - 0) * curveEnergy (I := I) g
          (fun t : ℝ => D.variation (r - r₀) t) 0 L := by
      simpa only [hc0, hr] using hbound
    change (riemannianEDistOf (I := I) g p (β r)).toReal ^ 2 ≤ L * energy r
    simpa only [sub_zero, energy, E] using hbound'
  have hgerm_nhds : {r : ℝ | D.variation (r - r₀) L = β r} ∈ 𝓝 r₀ := by
    have htend : Tendsto (fun r : ℝ => r - r₀) (𝓝 r₀) (𝓝 0) := by
      have h : Tendsto (fun r : ℝ => r - r₀) (𝓝 r₀) (𝓝 (r₀ - r₀)) :=
        tendsto_id.sub_const r₀
      simpa using h
    have hg := D.terminalGerm.comp_tendsto htend
    filter_upwards [hg] with r hr
    simp only [Function.comp_apply] at hr
    rw [hr]
    change β (r₀ + (r - r₀)) = β r
    congr 1
    ring
  have hU : interior J ∩ {r : ℝ | D.variation (r - r₀) L = β r} ∈ 𝓝 r₀ :=
    inter_mem (isOpen_interior.mem_nhds hJ) hgerm_nhds
  have hUJ : interior J ∩ {r : ℝ | D.variation (r - r₀) L = β r} ⊆ J :=
    fun _ hr => interior_subset hr.1
  have hmajor : ∀ r ∈ interior J ∩ {r : ℝ | D.variation (r - r₀) L = β r},
      riemannianDistance (I := I) g p (β r) ^ 2 ≤ L * energy r :=
    fun r hr => hV_bound r hr.2
  have hcontact : riemannianDistance (I := I) g p (β r₀) ^ 2 = L * energy r₀ := by
    rw [hdist, henergy_r₀]
    ring
  have henergy_deriv : ∀ r ∈ interior J ∩ {r : ℝ | D.variation (r - r₀) L = β r},
      HasDerivAt energy (deriv E (r - r₀)) r := by
    intro r _
    exact (hE_deriv' (r - r₀)).comp_sub_const r r₀
  have henergy_deriv2 : HasDerivAt (fun r : ℝ => deriv E (r - r₀))
      (deriv (deriv E) 0) r₀ := by
    have h := (hE_deriv2'' (r₀ - r₀)).comp_sub_const r₀ r₀
    rw [sub_self] at h
    exact h
  have hsecond : L * deriv (deriv E) 0 ≤ 2 := by
    have hbound := RadialEndpointVariation.secondVariation_half_energy_le_inv (I := I) D hL (by
      intro t _
      let R := (Curvature.riemannOp (Connection.LeviCivita (I := I) g) (D.variation 0 t))
        (D.parallelField t)
        (mfderiv 𝓘(ℝ, ℝ) I (fun u : ℝ => D.variation 0 u) t (1 : ℝ))
        (mfderiv 𝓘(ℝ, ℝ) I (fun u : ℝ => D.variation 0 u) t (1 : ℝ))
      have hnn : 0 ≤ g.inner (D.variation 0 t) (D.parallelField t) R :=
        riemann_contraction_nonneg (I := I) (M := M) hsec (D.variation 0 t)
          (D.parallelField t)
          (mfderiv 𝓘(ℝ, ℝ) I (fun u : ℝ => D.variation 0 u) t (1 : ℝ))
      change 0 ≤ g.inner (D.variation 0 t) R (D.parallelField t)
      rw [g.symm (D.variation 0 t) R (D.parallelField t)]
      exact hnn)
    have hhalf : deriv (deriv (fun r : ℝ => (1 / 2 : ℝ) * E r)) 0 =
        (1 / 2 : ℝ) * deriv (deriv E) 0 := by
      have h1 : deriv (fun r : ℝ => (1 / 2 : ℝ) * E r) =
          fun r : ℝ => (1 / 2 : ℝ) * deriv E r := by
        funext r
        exact deriv_const_mul (c := (1 / 2 : ℝ)) ((hE_deriv' r).differentiableAt)
      rw [h1]
      exact deriv_const_mul (c := (1 / 2 : ℝ)) ((hE_deriv2' ).differentiableAt)
    rw [hhalf] at hbound
    have h2 : deriv (deriv E) 0 ≤ 2 / L := by
      have h := mul_le_mul_of_nonneg_left hbound (by norm_num : (0 : ℝ) ≤ 2)
      have hd : (2 : ℝ) * ((1 / 2 : ℝ) * deriv (deriv E) 0) = deriv (deriv E) 0 := by
        ring
      have hR : (2 : ℝ) * (1 / L) = 2 / L := by ring
      linarith
    have h3 := mul_le_mul_of_nonneg_left h2 hL.le
    have h4 : L * (2 / L) = 2 := by
      field_simp
    linarith
  obtain ⟨a₁, b₁, hcenter₁, hsub₁⟩ :=
    mem_nhds_iff_exists_Ioo_subset.mp (isOpen_interior.mem_nhds hJ)
  obtain ⟨a₂, b₂, hcenter₂, hsub₂⟩ := mem_nhds_iff_exists_Ioo_subset.mp hgerm_nhds
  let left : ℝ := max a₁ a₂
  let right : ℝ := min b₁ b₂
  have hcenter : r₀ ∈ Ioo left right :=
    ⟨max_lt hcenter₁.1 hcenter₂.1, lt_min hcenter₁.2 hcenter₂.2⟩
  have hsubJ : Ioo left right ⊆ J := by
    intro r hr
    exact interior_subset (hsub₁ ⟨lt_of_le_of_lt (le_max_left _ _) hr.1,
      lt_of_lt_of_le hr.2 (min_le_left _ _)⟩)
  have hsubV : Ioo left right ⊆ {r : ℝ | D.variation (r - r₀) L = β r} := by
    intro r hr
    exact hsub₂ ⟨lt_of_le_of_lt (le_max_right _ _) hr.1,
      lt_of_lt_of_le hr.2 (min_le_right _ _)⟩
  have hsupport_le : ∀ y ∈ Ioo left right,
      y ^ 2 - L * energy y ≤ (squaredRiemannianDistanceDefect (I := I) g p β) y := by
    intro y hy
    have hy' := hV_bound y (hsubV hy)
    unfold squaredRiemannianDistanceDefect
    linarith
  have hsupport_eq : r₀ ^ 2 - L * energy r₀ =
      (squaredRiemannianDistanceDefect (I := I) g p β) r₀ := by
    unfold squaredRiemannianDistanceDefect
    rw [henergy_r₀, hdist]
    ring
  have hsupport_contDiff : ContDiffOn ℝ 2 (fun r : ℝ => r ^ 2 - L * energy r)
      (Ioo left right) := by
    have h2 : ContDiff ℝ 2 (fun r : ℝ => L * energy r) := by
      simpa only [smul_eq_mul] using
        ContDiff.const_smul (𝕜 := ℝ) (n := 2) (f := energy) L henergy_contDiff
    exact ((contDiff_id.pow 2).sub h2).contDiffOn
  have hsupport_deriv : deriv (fun r : ℝ => r ^ 2 - L * energy r) =
      fun r : ℝ => 2 * r - L * deriv E (r - r₀) := by
    funext x
    have hd : DifferentiableAt ℝ energy x :=
      (differentiableAt_comp_sub_const (f := E) (a := x) (b := r₀)).mpr
        (hE_deriv' (x - r₀)).differentiableAt
    have hcomp : deriv energy x = deriv E (x - r₀) := by
      simpa only [energy] using deriv_comp_sub_const (f := E) (a := r₀) (x := x)
    rw [show deriv (fun r : ℝ => r ^ 2 - L * energy r) x
        = deriv (fun r : ℝ => r ^ 2) x - deriv (fun r : ℝ => L * energy r) x
        from deriv_sub (differentiableAt_id.pow 2) (hd.const_mul L)]
    rw [deriv_pow_field (x := x) 2, deriv_const_mul (c := L) hd, hcomp]
    ring
  have hsupport_deriv2 : deriv (deriv (fun r : ℝ => r ^ 2 - L * energy r)) r₀ =
      2 - L * deriv (deriv E) 0 := by
    rw [hsupport_deriv]
    have hd2 : DifferentiableAt ℝ (fun r : ℝ => deriv E (r - r₀)) r₀ :=
      (differentiableAt_comp_sub_const (f := deriv E) (a := r₀) (b := r₀)).mpr
        (by simpa only [sub_self] using (hE_deriv2'' 0).differentiableAt)
    rw [show deriv (fun r : ℝ => 2 * r - L * deriv E (r - r₀)) r₀
        = deriv (fun r : ℝ => 2 * r) r₀
          - deriv (fun r : ℝ => L * deriv E (r - r₀)) r₀
        from deriv_sub (differentiableAt_id.const_mul 2) (hd2.const_mul L)]
    have hlin : deriv (fun r : ℝ => 2 * r) r₀ = 2 := by
      simp
    have hcomp2 : deriv (fun r : ℝ => deriv E (r - r₀)) r₀ = deriv (deriv E) 0 := by
      rw [deriv_comp_sub_const, sub_self]
    rw [hlin, deriv_const_mul (c := L) hd2, hcomp2]
  have hsupport_second_nonneg :
      0 ≤ deriv (deriv (fun r : ℝ => r ^ 2 - L * energy r)) r₀ := by
    rw [hsupport_deriv2]
    linarith
  let S : LowerSupportAt (squaredRiemannianDistanceDefect (I := I) g p β) J r₀ :=
    lowerSupportAt_sq_sub_sq_of_energy
      (distance := fun r : ℝ => riemannianDistance (I := I) g p (β r))
      (energy := energy) (energyDeriv := fun r : ℝ => deriv E (r - r₀))
      (energySecond := deriv (deriv E) 0) (L := L) hU hUJ hmajor hcontact henergy_deriv
      henergy_deriv2 hsecond
  have hSval : S.supportDeriv r₀ = 2 * r₀ - L * deriv E (r₀ - r₀) := rfl
  have hS : S.supportDeriv r₀ = 2 * r₀ - 2 * L * g.inner (γ L)
      (mfderiv 𝓘(ℝ, ℝ) I γ L (1 : ℝ)) vL := by
    rw [hSval]
    simp only [sub_self]
    rw [hE0]
    ring
  let C : C2LowerSupportAt (squaredRiemannianDistanceDefect (I := I) g p β) J r₀ :=
    { left := left
      right := right
      center_mem := hcenter
      interval_subset := hsubJ
      support := fun r : ℝ => r ^ 2 - L * energy r
      contDiffOn_support := hsupport_contDiff
      support_le := hsupport_le
      support_eq := hsupport_eq
      secondDeriv_nonneg := hsupport_second_nonneg }
  refine ⟨S, hS, C, ?_⟩
  change deriv (fun r : ℝ => r ^ 2 - L * energy r) r₀ = _
  rw [hsupport_deriv]
  simp only [sub_self]
  rw [hE0]
  ring

omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
    [I.Boundaryless] [T2Space M] [T2Space (TangentBundle I M)]
    [SigmaCompactSpace M] [BoundarylessManifold I M] in
theorem exists_squaredDistanceLowerSupport_of_zero
    (g : SmoothRiemannianMetric I M) (p : M) (β : ℝ → M)
    (J : Set ℝ) (r₀ : ℝ) (hJ : r₀ ∈ interior J)
    (hzero : riemannianDistance (I := I) g p (β r₀) = 0)
    (hlocal : ∀ᶠ r in 𝓝 r₀,
      riemannianDistance (I := I) g p (β r) ≤ |r - r₀|) :
    ∃ S : LowerSupportAt
        (squaredRiemannianDistanceDefect (I := I) g p β) J r₀,
      S.supportDeriv r₀ = 2 * r₀ ∧ S.supportSecondDeriv = 0 ∧
        ∃ C : C2LowerSupportAt
            (squaredRiemannianDistanceDefect (I := I) g p β) J r₀,
          deriv C.support r₀ = 2 * r₀ ∧
            deriv (deriv C.support) r₀ = 0 := by
  have hJnhds : J ∈ 𝓝 r₀ := mem_interior_iff_mem_nhds.mp hJ
  let U : Set ℝ :=
    {r | riemannianDistance (I := I) g p (β r) ≤ |r - r₀|} ∩ J
  have hU : U ∈ 𝓝 r₀ := inter_mem hlocal hJnhds
  have hUJ : U ⊆ J := inter_subset_right
  let S := lowerSupportAt_sq_sub_sq_of_zero hU hUJ
    (fun r _hr ↦ ENNReal.toReal_nonneg)
    (fun _r hr ↦ hr.1) hzero
  obtain ⟨left, right, hcenter, hinterval⟩ :=
    mem_nhds_iff_exists_Ioo_subset.mp hU
  let C : C2LowerSupportAt
      (squaredRiemannianDistanceDefect (I := I) g p β) J r₀ :=
    { left := left
      right := right
      center_mem := hcenter
      interval_subset := fun r hr ↦ hUJ (hinterval hr)
      support := fun r ↦ 2 * r₀ * r - r₀ ^ 2
      contDiffOn_support :=
        ((contDiff_const.mul contDiff_id).sub contDiff_const).contDiffOn
      support_le := by
        intro r hr
        unfold squaredRiemannianDistanceDefect
        have hdistNonneg :
            0 ≤ riemannianDistance (I := I) g p (β r) := ENNReal.toReal_nonneg
        have hdistLe := (hinterval hr).1
        have hsq : riemannianDistance (I := I) g p (β r) ^ 2 ≤
            |r - r₀| ^ 2 :=
          (sq_le_sq₀ hdistNonneg (abs_nonneg _)).2 hdistLe
        rw [sq_abs] at hsq
        nlinarith
      support_eq := by
        unfold squaredRiemannianDistanceDefect
        rw [hzero]
        ring
      secondDeriv_nonneg := by
        simp }
  exact ⟨S, by simp [S, lowerSupportAt_sq_sub_sq_of_zero],
    by simp [S, lowerSupportAt_sq_sub_sq_of_zero], C, by simp [C], by simp [C]⟩

end DifferentialGeometry.Toponogov
