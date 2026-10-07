import DifferentialGeometry.Geometry.Exponential.Smoothness.Domain
import DifferentialGeometry.Geometry.Exponential.Smoothness.AtZero.Derivative
import DifferentialGeometry.Bundle.FiberBundleHausdorff

set_option autoImplicit false

noncomputable section

open Bundle Filter Set
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.Geometry.Riemannian.Variation

open DifferentialGeometry.Analysis
open DifferentialGeometry.Analysis.ODE
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]

/-- A single smooth exponential surrogate near a compact part of the zero section.
The construction uses a compactly supported geodesic vector field, so it does not
require a complete metric on the carrier (in particular on a survivor collar). -/
theorem exists_compact_exponential
    (g : SmoothRiemannianMetric I M) (C : Set M) (hC : IsCompact C) :
    ∃ (F : TangentBundle I M → M) (U : Set (TangentBundle I M)),
      ContMDiff I.tangent I ∞ F ∧ IsOpen U ∧
      (∀ p, F (⟨p, (0 : E)⟩ : TangentBundle I M) = p) ∧
      (∀ p ∈ C, (⟨p, (0 : E)⟩ : TangentBundle I M) ∈ U) ∧
      ∀ z ∈ U, z.snd ∈ expDomain (I := I) g z.proj ∧
        F z = expMap (I := I) g z.proj z.snd := by
  classical
  let zero : M → TangentBundle I M := fun p => ⟨p, (0 : E)⟩
  have hzero : ContMDiff I I.tangent ∞ zero :=
    contMDiff_zeroSection ℝ (TangentSpace I)
  let K : Set (TangentBundle I M) := zero '' C
  have hK : IsCompact K := hC.image hzero.continuous
  obtain ⟨χ, hχ, hχc, hχone⟩ := exists_bump_nhds (I := I.tangent) hK
  change {z : TangentBundle I M | χ z = 1} ∈ 𝓝ˢ K at hχone
  obtain ⟨O, hOopen, hKO, hOχ⟩ := mem_nhdsSet_iff_exists.mp hχone
  let X : (z : TangentBundle I M) → TangentSpace I.tangent z :=
    fun z => χ z • geodesicVectorField (I := I) g z
  have hX : ContMDiff I.tangent I.tangent.tangent ∞
      (fun z : TangentBundle I M =>
        (⟨z, X z⟩ : TangentBundle I.tangent (TangentBundle I M))) :=
    hχ.smul_section (contMDiff_geodesicVectorField (I := I) g)
  have hXc : IsCompact (tsupport X) := by
    change HasCompactSupport (χ • geodesicVectorField (I := I) g)
    exact hχc.smul_right
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let hcomplete : ∀ z : TangentBundle I M,
      ∃ c : ℝ → TangentBundle I M, c 0 = z ∧ IsMIntegralCurve c X :=
    exists_globalIntegralCurve_of_compactSupport
      (I := I.tangent) (M := TangentBundle I M) X hX hXc
  have hflow : ContMDiff (𝓘(ℝ, ℝ).prod I.tangent) I.tangent ∞
      (fun z : ℝ × TangentBundle I M => curveAt X hcomplete z.2 z.1) :=
    contMDiff_curveAt X hX hcomplete
  have hstationary (p : M) (s : ℝ) :
      curveAt X hcomplete (zero p) s = zero p := by
    have hXzero : X (zero p) = 0 := by
      simp only [X, zero, geodesicVectorField_zero_section]
      exact smul_zero _
    have hconst : IsMIntegralCurve (fun _ : ℝ => zero p) X := by
      intro t
      rw [hXzero, ContinuousLinearMap.smulRight_zero]
      exact hasMFDerivAt_const (c := zero p) (x := t)
        (I := 𝓘(ℝ, ℝ)) (I' := I.tangent)
    have heq := integralCurve_eq_of_agree_zero X (hX.of_le (by norm_num))
      (curveAt_integralCurve X hcomplete (zero p)) hconst (by rw [curveAt_zero])
    exact congrFun heq s
  let W : Set (ℝ × TangentBundle I M) :=
    (fun z : ℝ × TangentBundle I M => curveAt X hcomplete z.2 z.1) ⁻¹' O
  have hWopen : IsOpen W := hOopen.preimage hflow.continuous
  have hslice : Icc (-1 : ℝ) 2 ×ˢ K ⊆ W := by
    rintro ⟨s, z⟩ ⟨_, ⟨p, hp, rfl⟩⟩
    change curveAt X hcomplete (zero p) s ∈ O
    rw [hstationary]
    exact hKO ⟨p, hp, rfl⟩
  obtain ⟨A, U, _hAopen, hUopen, hsegA, hKU, hAU⟩ :=
    generalized_tube_lemma (isCompact_Icc : IsCompact (Icc (-1 : ℝ) 2))
      hK hWopen hslice
  let F : TangentBundle I M → M := fun z => (curveAt X hcomplete z 1).proj
  have hF : ContMDiff I.tangent I ∞ F :=
    (contMDiff_proj (TangentSpace I)).comp
      (hflow.comp (contMDiff_const.prodMk contMDiff_id))
  refine ⟨F, U, hF, hUopen, ?_, ?_, ?_⟩
  · intro p
    change (curveAt X hcomplete (zero p) 1).proj = p
    rw [hstationary]
  · intro p hp
    exact hKU ⟨p, hp, rfl⟩
  · intro z hz
    let c : ℝ → TangentBundle I M := curveAt X hcomplete z
    have hc : IsMIntegralCurveOn c (geodesicVectorField (I := I) g)
        (Ioo (-1 : ℝ) 2) := by
      intro s hs
      have hcsO : c s ∈ O := by
        change (s, z) ∈ W
        exact hAU ⟨hsegA (Ioo_subset_Icc_self hs), hz⟩
      have hχs : χ (c s) = 1 := hOχ hcsO
      have hd := (curveAt_integralCurve X hcomplete z).isMIntegralCurveOn
        (Ioo (-1 : ℝ) 2) s hs
      simpa only [c, X, hχs, one_smul] using hd
    have hgeo : IsGeodesicOnWithInitial (I := I) g
        (projectCurve (I := I) c) (Ioo (-1 : ℝ) 2) z.proj z.snd := by
      refine ⟨c, (fun _ => rfl), ?_, hc⟩
      simp only [c, curveAt_zero]
    have hdom : z.snd ∈ expDomain (I := I) g z.proj := by
      change HasGeodesicAt (I := I) g z.proj z.snd 1
      exact ⟨projectCurve (I := I) c, Ioo (-1 : ℝ) 2, isOpen_Ioo,
        isPreconnected_Ioo, by norm_num, by norm_num, hgeo⟩
    have heq := maximalGeodesic_eqOn (I := I) g isOpen_Ioo isPreconnected_Ioo
      (by norm_num : (0 : ℝ) ∈ Ioo (-1 : ℝ) 2) hgeo
    refine ⟨hdom, ?_⟩
    change (c 1).proj = maximalGeodesic g z.proj z.snd 1
    exact (heq (by norm_num : (1 : ℝ) ∈ Ioo (-1 : ℝ) 2)).symm

end DifferentialGeometry.Geometry.Riemannian.Variation
