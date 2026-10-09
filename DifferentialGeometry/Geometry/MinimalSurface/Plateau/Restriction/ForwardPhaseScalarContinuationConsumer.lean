/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Restriction.ForwardPhaseGraphCauchyConsumer
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Restriction.TwoDiskGraphDifference
import DifferentialGeometry.Analysis.Elliptic.Planar.IsothermalPrincipal
import DifferentialGeometry.Analysis.Elliptic.Planar.BoundaryCauchyUniqueness
import DifferentialGeometry.Analysis.Calculus.Inverse.SmoothLocalInverse
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Restriction
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Topology.OpenPartialHomeomorph.Continuity

noncomputable section

open Set Filter Function Manifold DifferentialGeometry
open DifferentialGeometry.Topology DifferentialGeometry.Geometry DifferentialGeometry.Analysis
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Geometry.ImmersedDiskDivergence.Within
open DifferentialGeometry.Geometry.ImmersedDiskDivergence.HalfDisk
open scoped Topology ContDiff Manifold NNReal ENNReal ComplexConjugate

namespace DifferentialGeometry.Geometry.IMS03ConsumerAudit

private theorem scalar_mem_closure_inter_of_mem_open
    {S U : Set ℂ} (hU : IsOpen U) {x : ℂ}
    (hxU : x ∈ U) (hxS : x ∈ closure S) : x ∈ closure (S ∩ U) := by
  apply mem_closure_iff.mpr
  intro V hV hxV
  obtain ⟨y, hyV, hyS⟩ := mem_closure_iff.mp hxS (V ∩ U) (hV.inter hU) ⟨hxV, hxU⟩
  exact ⟨y, hyV.1, hyS, hyV.2⟩

private theorem scalar_mem_frontier_inter_open_iff
    {S U : Set ℂ} (hS : IsOpen S) (hU : IsOpen U) {x : ℂ}
    (hxU : x ∈ U) : x ∈ frontier (S ∩ U) ↔ x ∈ frontier S := by
  rw [(hS.inter hU).frontier_eq, hS.frontier_eq]
  constructor
  · intro hx
    exact ⟨closure_mono inter_subset_left hx.1, fun hxS => hx.2 ⟨hxS, hxU⟩⟩
  · intro hx
    exact ⟨scalar_mem_closure_inter_of_mem_open hU hxU hx.1,
      fun hxSU => hx.2 hxSU.1⟩

/-- Local continuation for the actual scalar operator on its given regular side.
The chart is selected from the principal matrix only. The equation is used only
on `S ∩ eIso.source`, and both original-side approach facts are retained. -/
private theorem scalar_continuation_from_regular_side
    {O S : Set ℂ} (hO : IsOpen O) (hS : IsOpen S) (hSO : S ⊆ O)
    {y0 : ℂ} (hy0 : y0 ∈ O) (hy0S : y0 ∈ closure S)
    (hy0Other : y0 ∈ closure (interior Sᶜ))
    (Aop : ℂ → Matrix (Fin 2) (Fin 2) ℝ) (beta : ℂ → Fin 2 → ℝ)
    (c w : ℂ → ℝ)
    (hAop : ∀ i j, ContDiffOn ℝ ∞ (fun y => Aop y i j) O)
    (hbeta : ∀ i, ContDiffOn ℝ ∞ (fun y => beta y i) O)
    (hc : ContDiffOn ℝ ∞ c O) (hw : ContDiffOn ℝ ∞ w O)
    (hpos : ∀ y ∈ O, (Aop y).PosDef)
    (hpde : ∀ y ∈ S, planarScalarOperator Aop beta c w y = 0)
    (hzero : ∀ y ∈ O ∩ frontier S, w y = 0 ∧ fderiv ℝ w y = 0)
    (hcurve : ∀ y ∈ O ∩ frontier S, ∃ (γ : ℝ → ℂ) (τ : ℂ),
      γ 0 = y ∧ HasDerivAt γ τ 0 ∧ τ ≠ 0 ∧
        ∀ᶠ t in 𝓝 0, γ t ∈ O ∩ frontier S) :
    ∃ (eIso : OpenPartialHomeomorph ℂ ℂ) (lam : ℂ → ℝ),
      y0 ∈ eIso.source ∧ eIso.source ⊆ O ∧ eIso y0 = 0 ∧
      ContDiffOn ℝ ∞ eIso eIso.source ∧
      ContDiffOn ℝ ∞ eIso.symm eIso.target ∧
      ContDiffOn ℝ ∞ lam eIso.source ∧ (∀ y ∈ eIso.source, 0 < lam y) ∧
      (∀ y ∈ eIso.source, ∀ H : ℂ →L[ℝ] ℂ →L[ℝ] ℝ,
        (∑ i : Fin 2, ∑ j : Fin 2, Aop y i j *
          H (fderiv ℝ eIso y ((![1, Complex.I] : Fin 2 → ℂ) i))
            (fderiv ℝ eIso y ((![1, Complex.I] : Fin 2 → ℂ) j))) =
          lam y * (H 1 1 + H Complex.I Complex.I)) ∧
      y0 ∈ closure (S ∩ eIso.source) ∧
      y0 ∈ closure (interior (S ∩ eIso.source)ᶜ) ∧
      ∃ T : Set ℂ, IsOpen T ∧ y0 ∈ T ∧ T ⊆ eIso.source ∧
        (∀ y ∈ T ∩ closure (S ∩ eIso.source), w y = 0 ∧ fderiv ℝ w y = 0) ∧
        ∃ K : Set ℂ, K = T ∩ (S ∩ eIso.source) ∧ IsOpen K ∧ K.Nonempty ∧
          K ⊆ S ∩ eIso.source ∧ K ⊆ O ∧
          ∀ y ∈ K, w y = 0 ∧ fderiv ℝ w y = 0 := by
  obtain ⟨eIso, lam, hyIso, hIsoO, hIso0, hIso, hIsoInv, hlam, hlampos, hprincipal⟩ :=
    exists_local_scalar_principal_coordinates_of_posDef hO Aop hAop hpos hy0
  have hSiso : IsOpen (S ∩ eIso.source) := hS.inter eIso.open_source
  have hzeroIso : ∀ y ∈ eIso.source ∩ frontier (S ∩ eIso.source),
      w y = 0 ∧ fderiv ℝ w y = 0 := by
    intro y hy
    exact hzero y ⟨hIsoO hy.1,
      (scalar_mem_frontier_inter_open_iff hS eIso.open_source hy.1).mp hy.2⟩
  have hcurveIso : ∀ y ∈ eIso.source ∩ frontier (S ∩ eIso.source),
      ∃ (γ : ℝ → ℂ) (τ : ℂ), γ 0 = y ∧ HasDerivAt γ τ 0 ∧ τ ≠ 0 ∧
        ∀ᶠ t in 𝓝 0, γ t ∈ eIso.source ∩ frontier (S ∩ eIso.source) := by
    intro y hy
    obtain ⟨γ, τ, hγ0, hγd, hτ, hγfront⟩ := hcurve y ⟨hIsoO hy.1,
      (scalar_mem_frontier_inter_open_iff hS eIso.open_source hy.1).mp hy.2⟩
    refine ⟨γ, τ, hγ0, hγd, hτ, ?_⟩
    have hγU : ∀ᶠ t in 𝓝 (0 : ℝ), γ t ∈ eIso.source :=
      hγd.continuousAt.eventually (by
        simpa only [hγ0] using eIso.open_source.eventually_mem hy.1)
    filter_upwards [hγfront, hγU] with t ht htU
    exact ⟨htU,
      (scalar_mem_frontier_inter_open_iff hS eIso.open_source htU).mpr ht.2⟩
  have hySiso : y0 ∈ closure (S ∩ eIso.source) :=
    scalar_mem_closure_inter_of_mem_open eIso.open_source hyIso hy0S
  have hcompl : Sᶜ ⊆ (S ∩ eIso.source)ᶜ := by
    intro y hy hyS
    exact hy hyS.1
  have hyOtherIso : y0 ∈ closure (interior (S ∩ eIso.source)ᶜ) :=
    closure_mono (interior_mono hcompl) hy0Other
  obtain ⟨_, _, _, _, T, hT, hyT, hTIso, hTzero⟩ :=
    planar_boundary_cauchy_zero_germ_on_regular_side_in_same_isothermal_coordinates
      Aop beta c w eIso lam (S ∩ eIso.source) hSiso inter_subset_right
      (fun i j => (hAop i j).mono hIsoO) (fun i => (hbeta i).mono hIsoO)
      (hc.mono hIsoO) (hw.mono hIsoO) (fun y hy => hpos y (hIsoO hy))
      (fun y hy => hpde y hy.1) hzeroIso hcurveIso
      hIso hIsoInv hlam hlampos hprincipal hyIso hyOtherIso
  refine ⟨eIso, lam, hyIso, hIsoO, hIso0, hIso, hIsoInv, hlam, hlampos,
    hprincipal, hySiso, hyOtherIso, T, hT, hyT, hTIso, hTzero,
    T ∩ (S ∩ eIso.source), rfl, hT.inter hSiso, ?_, inter_subset_right, ?_, ?_⟩
  · exact mem_closure_iff.mp hySiso T hT hyT
  · intro y hy
    exact hSO hy.2.1
  · intro y hy
    exact hTzero y ⟨hy.1, subset_closure hy.2⟩

private theorem exists_section_localInverse_of_projected_rightInverse
    {J s : ℂ → ℂ} {K : Set ℂ} (hK : IsOpen K)
    (hs : ContDiffOn ℝ ∞ s K) (hright : ∀ y ∈ K, J (s y) = y)
    {y : ℂ} (hy : y ∈ K) (hJ : DifferentiableAt ℝ J (s y)) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ,
      y ∈ e.source ∧ e.source ⊆ K ∧ (e : ℂ → ℂ) = s ∧
        ContDiffOn ℝ ∞ e.symm e.target := by
  have hsd : DifferentiableAt ℝ s y :=
    (hs.contDiffAt (hK.mem_nhds hy)).differentiableAt (by simp)
  have hnear : J ∘ s =ᶠ[𝓝 y] id := by
    filter_upwards [hK.mem_nhds hy] with z hz using hright z hz
  have hder : (fderiv ℝ J (s y)).comp (fderiv ℝ s y) =
      ContinuousLinearMap.id ℝ ℂ := by
    rw [← fderiv_comp y hJ hsd, hnear.fderiv_eq, fderiv_id]
  have hleft (v : ℂ) : fderiv ℝ J (s y) (fderiv ℝ s y v) = v :=
    congrArg (fun L : ℂ →L[ℝ] ℂ => L v) hder
  have hinj : Function.Injective (fderiv ℝ s y) := by
    intro v w hvw
    calc
      v = fderiv ℝ J (s y) (fderiv ℝ s y v) := (hleft v).symm
      _ = fderiv ℝ J (s y) (fderiv ℝ s y w) := congrArg (fderiv ℝ J (s y)) hvw
      _ = w := hleft w
  have hbij : Function.Bijective (fderiv ℝ s y) :=
    ⟨hinj, (LinearMap.injective_iff_surjective
      (f := (fderiv ℝ s y).toLinearMap)).mp hinj⟩
  let L : ℂ ≃L[ℝ] ℂ :=
    (LinearEquiv.ofBijective (fderiv ℝ s y).toLinearMap hbij).toContinuousLinearEquiv
  have hL : (L : ℂ →L[ℝ] ℂ) = fderiv ℝ s y := by
    ext v
    rfl
  exact DifferentialGeometry.Analysis.exists_smooth_localInverse hK hs hy L
    (by rw [hL]; exact hsd.hasFDerivAt)

private theorem actual_subdisk_image_germ_of_projected_sections
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M]
    {G : SmoothRiemannianMetric 𝓘(ℝ, E) M} {γ : freeLoop M}
    {q aOrig : C(closedDisk, M)} (hq : IsMorreyDisk G γ q)
    (QOriginal A : ℂ → M)
    (hQOriginal : SmoothDiskExtension (E := E) q QOriginal)
    (hA : SmoothDiskExtension (E := E) aOrig A)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) (p : M) (P : E →L[ℝ] ℂ)
    {O K : Set ℂ} (hK : IsOpen K) (hKnonempty : K.Nonempty) (hKO : K ⊆ O)
    (rOuter rAlt : ℂ → ℂ)
    (hrOuter : ContDiffOn ℝ ∞ rOuter O) (hrAlt : ContDiffOn ℝ ∞ rAlt O)
    (hchartOuter : ∀ y ∈ O, QOriginal (rOuter y) ∈ (chartAt E p).source)
    (hchartAlt : ∀ y ∈ O, A (rAlt y) ∈ (chartAt E p).source)
    (hrightOuter : ∀ y ∈ O, P (extChartAt 𝓘(ℝ, E) p (QOriginal (rOuter y))) = y)
    (hrightAlt : ∀ y ∈ O, P (extChartAt 𝓘(ℝ, E) p (A (rAlt y))) = y)
    (hmapsOuter : MapsTo rOuter K (Metric.ball (0 : ℂ) r ∩ Metric.ball (0 : ℂ) 1))
    (hmapsAlt : MapsTo rAlt K (Metric.ball (0 : ℂ) 1))
    (hmapsR2 : MapsTo (fun y => r⁻¹ • rOuter y) K (Metric.ball (0 : ℂ) 1))
    (hvalues : ∀ y ∈ K, QOriginal (rOuter y) = A (rAlt y)) :
    ∃ yStar ∈ K,
      rOuter yStar ∈ Metric.ball (0 : ℂ) r ∧
      r⁻¹ • rOuter yStar ∈ Metric.ball (0 : ℂ) 1 ∧
      rAlt yStar ∈ Metric.ball (0 : ℂ) 1 ∧
      diskExtension (affineSubdisk q 0 r) (r⁻¹ • rOuter yStar) =
        diskExtension aOrig (rAlt yStar) ∧
      Filter.map (diskExtension (affineSubdisk q 0 r)) (𝓝 (r⁻¹ • rOuter yStar)) =
        Filter.map (diskExtension aOrig) (𝓝 (rAlt yStar)) := by
  obtain ⟨yStar, hyStar⟩ := hKnonempty
  let R2 : ℂ → ℂ := fun y => r⁻¹ • rOuter y
  let JOuter : ℂ → ℂ := fun z => P (extChartAt 𝓘(ℝ, E) p (QOriginal z))
  let JAlt : ℂ → ℂ := fun z => P (extChartAt 𝓘(ℝ, E) p (A z))
  let J2 : ℂ → ℂ := JOuter ∘ (fun z : ℂ => r • z)
  have hscale (y : ℂ) : r • R2 y = rOuter y := smul_inv_smul₀ hr.ne' (rOuter y)
  have hR2 : ContDiffOn ℝ ∞ R2 K :=
    (contDiffOn_const (c := r⁻¹)).smul (hrOuter.mono hKO)
  have hAlt : ContDiffOn ℝ ∞ rAlt K := hrAlt.mono hKO
  obtain ⟨NQ, hNQ, hDNQ, hQNQ⟩ := hQOriginal.2
  obtain ⟨NA, hNA, hDNA, hANA⟩ := hA.2
  have hQAt : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ QOriginal (rOuter yStar) :=
    hQNQ.contMDiffAt
      (hNQ.mem_nhds (hDNQ (Metric.ball_subset_closedBall (hmapsOuter hyStar).2)))
  have hAAt : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ A (rAlt yStar) :=
    hANA.contMDiffAt
      (hNA.mem_nhds (hDNA (Metric.ball_subset_closedBall (hmapsAlt hyStar))))
  have hXQ : ContDiffAt ℝ ∞
      (fun z => extChartAt 𝓘(ℝ, E) p (QOriginal z)) (rOuter yStar) :=
    ((contMDiffAt_extChartAt' (I := 𝓘(ℝ, E)) (n := ∞)
      (hchartOuter yStar (hKO hyStar))).comp (rOuter yStar) hQAt).contDiffAt
  have hXA : ContDiffAt ℝ ∞
      (fun z => extChartAt 𝓘(ℝ, E) p (A z)) (rAlt yStar) :=
    ((contMDiffAt_extChartAt' (I := 𝓘(ℝ, E)) (n := ∞)
      (hchartAlt yStar (hKO hyStar))).comp (rAlt yStar) hAAt).contDiffAt
  have hJOuter : DifferentiableAt ℝ JOuter (rOuter yStar) :=
    (P.contDiff.contDiffAt.comp (rOuter yStar) hXQ).differentiableAt (by simp)
  have hJAlt : DifferentiableAt ℝ JAlt (rAlt yStar) :=
    (P.contDiff.contDiffAt.comp (rAlt yStar) hXA).differentiableAt (by simp)
  have hJ2 : DifferentiableAt ℝ J2 (R2 yStar) := by
    apply DifferentiableAt.comp (R2 yStar) ?_
      ((contDiff_const_smul r : ContDiff ℝ ∞ (fun z : ℂ => r • z)).differentiable
        (by simp)).differentiableAt
    simpa only [hscale] using hJOuter
  have hright2 : ∀ y ∈ K, J2 (R2 y) = y := by
    intro y hy
    change JOuter (r • R2 y) = y
    rw [hscale]
    exact hrightOuter y (hKO hy)
  obtain ⟨e2, hy2, _, he2, _⟩ :=
    exists_section_localInverse_of_projected_rightInverse hK hR2 hright2 hyStar hJ2
  obtain ⟨eA, hyA, _, heA, _⟩ :=
    exists_section_localInverse_of_projected_rightInverse hK hAlt
      (fun y hy => hrightAlt y (hKO hy)) hyStar hJAlt
  have hmap2 : Filter.map R2 (𝓝 yStar) = 𝓝 (R2 yStar) := by
    simpa only [he2] using e2.map_nhds_eq hy2
  have hmapA : Filter.map rAlt (𝓝 yStar) = 𝓝 (rAlt yStar) := by
    simpa only [heA] using eA.map_nhds_eq hyA
  let Q2 : ℂ → M := fun z => diskExtension q ((0 : ℂ) + r • z)
  have hQ2 : SmoothDiskExtension (E := E) (affineSubdisk q 0 r) Q2 :=
    hq.smoothDiskExtension_affineSubdisk 0 r hr.le (by simpa only [norm_zero, zero_add] using hr1)
  have hvalues2 (y : ℂ) (hy : y ∈ K) : Q2 (R2 y) = A (rAlt y) := by
    change diskExtension q (0 + r • R2 y) = A (rAlt y)
    rw [zero_add, hscale]
    exact (hQOriginal.eventuallyEq_diskExtension (hmapsOuter hy).2).eq_of_nhds.symm.trans
      (hvalues y hy)
  have hnear : Q2 ∘ R2 =ᶠ[𝓝 yStar] A ∘ rAlt := by
    filter_upwards [hK.mem_nhds hyStar] with y hy using hvalues2 y hy
  have h2near := hQ2.eventuallyEq_diskExtension (hmapsR2 hyStar)
  have hAnear := hA.eventuallyEq_diskExtension (hmapsAlt hyStar)
  refine ⟨yStar, hyStar, (hmapsOuter hyStar).1, hmapsR2 hyStar, hmapsAlt hyStar, ?_, ?_⟩
  · exact h2near.eq_of_nhds.symm.trans ((hvalues2 yStar hyStar).trans hAnear.eq_of_nhds)
  · calc
      Filter.map (diskExtension (affineSubdisk q 0 r)) (𝓝 (R2 yStar)) =
          Filter.map Q2 (𝓝 (R2 yStar)) := (Filter.map_congr h2near).symm
      _ = Filter.map (Q2 ∘ R2) (𝓝 yStar) := by rw [← Filter.map_map, hmap2]
      _ = Filter.map (A ∘ rAlt) (𝓝 yStar) := Filter.map_congr hnear
      _ = Filter.map A (𝓝 (rAlt yStar)) := by rw [← Filter.map_map, hmapA]
      _ = Filter.map (diskExtension aOrig) (𝓝 (rAlt yStar)) := Filter.map_congr hAnear

private theorem scalar_graph_decomposition
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : E →L[ℝ] ℂ) (eta : E →L[ℝ] ℝ) (lift : ℂ → E) (N : E)
    (hsplit : ∀ v : E, v = lift (P v) + (eta v) • N)
    (x0 X : E) (y : ℂ) (hPX : P X = y) :
    X = x0 + lift (y - P x0) + (eta (X - x0)) • N := by
  have hs := hsplit (X - x0)
  rw [map_sub, hPX] at hs
  calc
    X = x0 + (X - x0) := by abel
    _ = x0 + (lift (y - P x0) + (eta (X - x0)) • N) := congrArg (x0 + ·) hs
    _ = x0 + lift (y - P x0) + (eta (X - x0)) • N := (add_assoc _ _ _).symm

/-- The fixed original Morrey pair and the once-chosen forward seam give a scalar
elliptic equation only on the retained graph side. One principal-coordinate chart
and regular-side uniqueness yield a nonempty open coincidence patch and an image
germ of the literal proper subdisk and the original alternative disk. -/
theorem actual_morrey_forward_phase_scalar_continuation
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]
    (G : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {γ : freeLoop M} {q : C(closedDisk, M)} (hq : IsMorreyDisk G γ q)
    (aOrig : C(closedDisk, M)) {r b : ℝ}
    (hr : 0 < r) (hrb : r < b) (hb : b < 1)
    (hd3 : Module.finrank ℝ E = 3)
    (haOrig : IsMorreyDisk G (diskTrace (affineSubdisk q 0 r)) aOrig)
    (QOriginal A : ℂ → M)
    (hQOriginal : SmoothDiskExtension (E := E) q QOriginal)
    (hA : SmoothDiskExtension (E := E) aOrig A)
    (ψ : ℝ → ℝ) (aForward : C(closedDisk, M)) (φ : ℝ ≃ₜ ℝ)
    (hφ : ContDiff ℝ ∞ (fun t : ℝ => φ t))
    (hp : ∀ t : ℝ, φ (t + 1) = φ t + 1)
    (D : ℂ → ℂ)
    (hbranch : (D = id ∧ aForward = aOrig ∧ ∀ t : ℝ, φ t = ψ t) ∨
      (D = conj ∧ aForward = aOrig.comp ⟨diskReflection, diskReflection.continuous⟩ ∧
        ∀ t : ℝ, φ t = ψ (-t)))
    (F : C(closedDisk, M)) {L : ℝ≥0}
    (hFLip : ∀ z w, riemannianEDistOf G (F z) (F w) ≤ (L : ℝ≥0∞) * edist z w)
    (hFtrace : diskTrace F = diskTrace q)
    (hFarea : riemannianDiskArea G F = riemannianDiskArea G q)
    (t₀ α : ℝ) (χ : PartialDiffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ℂ ℂ ∞)
    (hseam :
      t₀ ∈ Ioo (0 : ℝ) 1 ∧ 0 < deriv φ t₀ ∧ 0 < α ∧
      (∀ z : ℂ, χ z = r • Complex.diskBoundaryChart
        (diskBoundary (t₀ : loopCircle) : ℂ) (by simp [diskBoundary]) (α • z)) ∧
      Metric.closedBall (0 : ℂ) 1 ⊆ χ.source ∧
      (∀ z ∈ Metric.closedBall (0 : ℂ) 1, r / 2 < ‖χ z‖ ∧ ‖χ z‖ < b) ∧
      χ '' Metric.closedBall (0 : ℂ) 1 ⊆ Metric.ball (0 : ℂ) 1 ∧
      let H := ForwardPhaseAnnulus.map r b hφ hp
      let ψAlt : ℂ → ℂ := fun z => (r⁻¹ : ℝ) • χ z
      let ψOuter : ℂ → ℂ := H ∘ χ ∘ conj
      let UAlt : ℂ → M := A ∘ (D ∘ ψAlt)
      let UOuter : ℂ → M := QOriginal ∘ ψOuter
      χ 0 = r • (diskBoundary (t₀ : loopCircle) : ℂ) ∧
      ψAlt 0 = (diskBoundary (t₀ : loopCircle) : ℂ) ∧
      ψOuter 0 = r • (diskBoundary (φ t₀ : loopCircle) : ℂ) ∧
      ContDiffOn ℝ ∞ ψAlt (Metric.ball (0 : ℂ) 1) ∧
      ContDiffOn ℝ ∞ ψOuter (Metric.ball (0 : ℂ) 1) ∧
      (∀ z ∈ (openHalfDisk 0 (1 / 4) : Set ℂ), Bijective (fderiv ℝ ψAlt z)) ∧
      (∀ z ∈ (openHalfDisk 0 (1 / 4) : Set ℂ), Bijective (fderiv ℝ ψOuter z)) ∧
      MapsTo ψAlt (closedHalfDisk 0 (1 / 4)) (Metric.closedBall (0 : ℂ) 1) ∧
      MapsTo ψAlt (openHalfDisk 0 (1 / 4)) (Metric.ball (0 : ℂ) 1) ∧
      MapsTo ψOuter (closedHalfDisk 0 (1 / 4)) (Metric.ball (0 : ℂ) 1) ∧
      (∀ z ∈ (openHalfDisk 0 (1 / 4) : Set ℂ), r < ‖ψOuter z‖ ∧ ‖ψOuter z‖ < b) ∧
      ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ UAlt (Metric.ball (0 : ℂ) 1) ∧
      ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ UOuter (Metric.ball (0 : ℂ) 1) ∧
      (∀ z ∈ closedHalfDisk 0 (1 / 4), Injective
        (mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) UAlt (closedHalfDisk 0 (1 / 4)) z)) ∧
      (∀ z ∈ closedHalfDisk 0 (1 / 4), Injective
        (mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) UOuter (closedHalfDisk 0 (1 / 4)) z)) ∧
      EqOn (diskExtension F ∘ χ) UAlt (closedHalfDisk 0 (1 / 4)) ∧
      EqOn (diskExtension F ∘ χ ∘ conj) UOuter (closedHalfDisk 0 (1 / 4)) ∧
      (∀ s ∈ Icc (-(1 / 4) : ℝ) (1 / 4), UAlt (s : ℂ) = UOuter (s : ℂ))) :
    let H := ForwardPhaseAnnulus.map r b hφ hp
    let ψAlt : ℂ → ℂ := fun z => (r⁻¹ : ℝ) • χ z
    let ψOuter : ℂ → ℂ := H ∘ χ ∘ conj
    let UAlt : ℂ → M := A ∘ (D ∘ ψAlt)
    let UOuter : ℂ → M := QOriginal ∘ ψOuter
    let aOriginal := ψOuter 0
    let p := QOriginal aOriginal
    let B : Fin (Module.finrank ℝ E) → ℂ := fun i =>
      chartComplexGradient p QOriginal i aOriginal
    let Qg := chartGramBilin G p (QOriginal aOriginal)
    let P := chartLeadingPlaneProjection G p (QOriginal aOriginal) B
    let lift : ℂ → E := fun w => (chartModelBasis E).equivFunL.symm
      (fun i => (2 : ℝ) * (w * B i).re)
    ∃ N : E, Qg N N = 1 ∧ P N = 0 ∧
      (∀ v : E, v = lift (P v) + (Qg N v) • N) ∧
      ∃ (eOuter eAlt : OpenPartialHomeomorph ℂ ℂ) (O : Set ℂ),
        (0 : ℂ) ∈ eOuter.source ∧ (0 : ℂ) ∈ eAlt.source ∧
        eOuter.source ⊆ Metric.ball (0 : ℂ) 1 ∧
        eAlt.source ⊆ Metric.ball (0 : ℂ) 1 ∧
        (eOuter : ℂ → ℂ) = (fun z => P (extChartAt 𝓘(ℝ, E) p (UOuter z))) ∧
        (eAlt : ℂ → ℂ) = (fun z => P (extChartAt 𝓘(ℝ, E) p (UAlt z))) ∧
        ContDiffOn ℝ ∞ eOuter.symm eOuter.target ∧
        ContDiffOn ℝ ∞ eAlt.symm eAlt.target ∧
        IsOpen O ∧ eOuter 0 ∈ O ∧ O ⊆ eOuter.target ∩ eAlt.target ∧
        let rOuter := ψOuter ∘ eOuter.symm
        let rAlt := D ∘ ψAlt ∘ eAlt.symm
        let hOuter : ℂ → ℝ := fun y => Qg N
          (extChartAt 𝓘(ℝ, E) p (QOriginal (rOuter y)) - extChartAt 𝓘(ℝ, E) p p)
        let hAlt : ℂ → ℝ := fun y => Qg N
          (extChartAt 𝓘(ℝ, E) p (A (rAlt y)) - extChartAt 𝓘(ℝ, E) p p)
        let S := O ∩ eAlt '' (eAlt.source ∩ {z : ℂ | 0 < z.im})
        ContDiffOn ℝ ∞ hOuter O ∧ ContDiffOn ℝ ∞ hAlt O ∧
        ContDiffOn ℝ ∞ rOuter O ∧ ContDiffOn ℝ ∞ rAlt O ∧
        (∀ y ∈ O, QOriginal (rOuter y) ∈ (chartAt E p).source) ∧
        (∀ y ∈ O, A (rAlt y) ∈ (chartAt E p).source) ∧
        (∀ y ∈ O, P (extChartAt 𝓘(ℝ, E) p (QOriginal (rOuter y))) = y) ∧
        (∀ y ∈ O, P (extChartAt 𝓘(ℝ, E) p (A (rAlt y))) = y) ∧
        (∀ y ∈ O, ∀ t ∈ Icc (0 : ℝ) 1,
          (1 - t) • extChartAt 𝓘(ℝ, E) p (A (rAlt y)) +
            t • extChartAt 𝓘(ℝ, E) p (QOriginal (rOuter y)) ∈
              (extChartAt 𝓘(ℝ, E) p).target) ∧
        IsOpen S ∧ S ⊆ O ∧ S.Nonempty ∧
        eOuter 0 ∈ closure S ∩ closure (interior Sᶜ) ∧
        O ∩ frontier S = {y | y ∈ O ∧ (eAlt.symm y).im = 0} ∧
        (∀ y ∈ O ∩ frontier S, ∃ t : ℝ, |t| < 1 / 16 ∧
          eAlt.symm y = (t : ℂ) ∧ eOuter.symm y = (t : ℂ)) ∧
        (∀ y ∈ O ∩ frontier S, hOuter y = hAlt y ∧
          fderiv ℝ hOuter y = fderiv ℝ hAlt y) ∧
        (∀ y ∈ O ∩ frontier S, ∃ (γ : ℝ → ℂ) (τ : ℂ),
          γ 0 = y ∧ HasDerivAt γ τ 0 ∧ τ ≠ 0 ∧
            ∀ᶠ t in 𝓝 0, γ t ∈ O ∩ frontier S) ∧
        MapsTo rAlt S (Metric.ball (0 : ℂ) 1) ∧
        MapsTo rOuter S (Metric.ball (0 : ℂ) r) ∧
        MapsTo rOuter S (Metric.ball (0 : ℂ) 1) ∧
        MapsTo (fun y => (r⁻¹ : ℝ) • rOuter y) S (Metric.ball (0 : ℂ) 1) ∧
        let w : ℂ → ℝ := hOuter - hAlt
        ∃ (Aop : ℂ → Matrix (Fin 2) (Fin 2) ℝ) (beta : ℂ → Fin 2 → ℝ) (c : ℂ → ℝ),
          (∀ i j, ContDiffOn ℝ ∞ (fun y => Aop y i j) O) ∧
          (∀ y ∈ O, (Aop y).PosDef) ∧
          (∀ i, ContDiffOn ℝ ∞ (fun y => beta y i) O) ∧ ContDiffOn ℝ ∞ c O ∧
          (∀ y ∈ S, planarScalarOperator Aop beta c w y = 0) ∧
          ∃ (eIso : OpenPartialHomeomorph ℂ ℂ) (lam : ℂ → ℝ),
            eOuter 0 ∈ eIso.source ∧ eIso.source ⊆ O ∧ eIso (eOuter 0) = 0 ∧
            ContDiffOn ℝ ∞ eIso eIso.source ∧
            ContDiffOn ℝ ∞ eIso.symm eIso.target ∧
            ContDiffOn ℝ ∞ lam eIso.source ∧ (∀ y ∈ eIso.source, 0 < lam y) ∧
            (∀ y ∈ eIso.source, ∀ Hess : ℂ →L[ℝ] ℂ →L[ℝ] ℝ,
              (∑ i : Fin 2, ∑ j : Fin 2, Aop y i j *
                Hess (fderiv ℝ eIso y ((![1, Complex.I] : Fin 2 → ℂ) i))
                  (fderiv ℝ eIso y ((![1, Complex.I] : Fin 2 → ℂ) j))) =
                lam y * (Hess 1 1 + Hess Complex.I Complex.I)) ∧
            eOuter 0 ∈ closure (S ∩ eIso.source) ∧
            eOuter 0 ∈ closure (interior (S ∩ eIso.source)ᶜ) ∧
            ∃ T : Set ℂ, IsOpen T ∧ eOuter 0 ∈ T ∧ T ⊆ eIso.source ∧
              (∀ y ∈ T ∩ closure (S ∩ eIso.source), w y = 0 ∧ fderiv ℝ w y = 0) ∧
              ∃ K : Set ℂ, K = T ∩ (S ∩ eIso.source) ∧ IsOpen K ∧ K.Nonempty ∧
                K ⊆ S ∩ eIso.source ∧ K ⊆ O ∧
                (∀ y ∈ K, w y = 0 ∧ fderiv ℝ w y = 0) ∧
                (∀ y ∈ K, QOriginal (rOuter y) = A (rAlt y)) ∧
                ∃ yStar ∈ K,
                  rOuter yStar ∈ Metric.ball (0 : ℂ) r ∧
                  (r⁻¹ : ℝ) • rOuter yStar ∈ Metric.ball (0 : ℂ) 1 ∧
                  rAlt yStar ∈ Metric.ball (0 : ℂ) 1 ∧
                  diskExtension (affineSubdisk q 0 r) ((r⁻¹ : ℝ) • rOuter yStar) =
                    diskExtension aOrig (rAlt yStar) ∧
                  Filter.map (diskExtension (affineSubdisk q 0 r))
                      (𝓝 ((r⁻¹ : ℝ) • rOuter yStar)) =
                    Filter.map (diskExtension aOrig) (𝓝 (rAlt yStar)) := by
  intro H ψAlt ψOuter UAlt UOuter aOriginal p B Qg P lift
  have hdata := actual_morrey_forward_phase_graph_cauchy_data G hq aOrig hr hrb hb hd3
    haOrig QOriginal A hQOriginal hA ψ aForward φ hφ hp D hbranch F hFLip hFtrace hFarea
    t₀ α χ hseam
  rcases hdata with ⟨N, hNN, hPN, hsplit, eOuter, eAlt, O, h0eOuter, h0eAlt,
    heOuterBall, heAltBall, heOuter, heAlt, hInvOuter, hInvAlt, hO, hy0, hOt, hrest⟩
  let rOuter := ψOuter ∘ eOuter.symm
  let rAlt := D ∘ ψAlt ∘ eAlt.symm
  let x0 := extChartAt 𝓘(ℝ, E) p p
  let hOuter : ℂ → ℝ := fun y => Qg N
    (extChartAt 𝓘(ℝ, E) p (QOriginal (rOuter y)) - x0)
  let hAlt : ℂ → ℝ := fun y => Qg N
    (extChartAt 𝓘(ℝ, E) p (A (rAlt y)) - x0)
  let S := O ∩ eAlt '' (eAlt.source ∩ {z : ℂ | 0 < z.im})
  let w : ℂ → ℝ := hOuter - hAlt
  rcases hrest with ⟨hhOuter, hhAlt, hrOuter, hrAlt, hchartOuter, hchartAlt,
    hrightOuter, hrightAlt, hsegment, hS, hSO, hSne, happroach, hfront,
    hparameters, hjets, hcurve, hInner, hProper, hUnit, hScaled⟩
  have hbase : A (D (ψAlt 0)) = QOriginal aOriginal := by
    have hs := hseam
    dsimp only at hs
    rcases hs with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, _, _, htrace⟩
    exact htrace 0 (by constructor <;> norm_num)
  have hOuterGraph (y : ℂ) (hy : y ∈ O) :
      extChartAt 𝓘(ℝ, E) p (QOriginal (rOuter y)) =
        x0 + lift (y - P x0) + hOuter y • N :=
    scalar_graph_decomposition P (Qg N) lift N hsplit x0 _ y (hrightOuter y hy)
  have hAltGraph (y : ℂ) (hy : y ∈ O) :
      extChartAt 𝓘(ℝ, E) p (A (rAlt y)) =
        x0 + lift (y - P x0) + hAlt y • N :=
    scalar_graph_decomposition P (Qg N) lift N hsplit x0 _ y (hrightAlt y hy)
  have hsegmentGraph : ∀ y ∈ O, ∀ t ∈ Icc (0 : ℝ) 1,
      (1 - t) • (x0 + lift (y - P x0) + hAlt y • N) +
        t • (x0 + lift (y - P x0) + hOuter y • N) ∈
          (extChartAt 𝓘(ℝ, E) p).target := by
    intro y hy t ht
    rw [← hAltGraph y hy, ← hOuterGraph y hy]
    exact hsegment y hy t ht
  obtain ⟨Aop, beta, c, hAop, hpos, hbeta, hc, hpdeRaw⟩ :=
    IMS03Embeddedness.actual_two_morrey_graph_height_difference_on hq haOrig
      QOriginal A hQOriginal hA aOriginal (D (ψAlt 0)) hbase p B N hNN hPN hsplit
      hO hS hSO hSne rOuter rAlt (hrOuter.mono hSO) (hrAlt.mono hSO)
      hUnit hInner (fun y hy => hchartOuter y (hSO hy))
      (fun y hy => hchartAlt y (hSO hy))
      (fun y hy => hrightOuter y (hSO hy)) (fun y hy => hrightAlt y (hSO hy))
      hhOuter hhAlt hsegmentGraph
  have hw : ContDiffOn ℝ ∞ w O := hhOuter.sub hhAlt
  have hpde : ∀ y ∈ S, planarScalarOperator Aop beta c w y = 0 := by
    intro y hy
    exact hpdeRaw y hy
  have hzero : ∀ y ∈ O ∩ frontier S, w y = 0 ∧ fderiv ℝ w y = 0 := by
    intro y hy
    obtain ⟨hvalue, hderiv⟩ := hjets y hy
    refine ⟨sub_eq_zero.mpr hvalue, ?_⟩
    change fderiv ℝ (hOuter - hAlt) y = 0
    rw [fderiv_sub
      ((hhOuter.contDiffAt (hO.mem_nhds hy.1)).differentiableAt (by simp))
      ((hhAlt.contDiffAt (hO.mem_nhds hy.1)).differentiableAt (by simp)),
      hderiv, sub_self]
  obtain ⟨eIso, lam, hyIso, hIsoO, hIso0, hIso, hIsoInv, hlam, hlamPos, hprincipal,
      hIsoApproach, hIsoOther, T, hT, hyT, hTIso, hTzero,
      K, hKeq, hK, hKne, hKside, hKO, hKzero⟩ :=
    scalar_continuation_from_regular_side hO hS hSO hy0 happroach.1 happroach.2
      Aop beta c w hAop hbeta hc hw hpos hpde hzero hcurve
  have hKS : K ⊆ S := hKside.trans inter_subset_left
  have hvalues : ∀ y ∈ K, QOriginal (rOuter y) = A (rAlt y) := by
    intro y hy
    have hh : hOuter y = hAlt y := sub_eq_zero.mp (hKzero y hy).1
    apply (extChartAt 𝓘(ℝ, E) p).injOn
    · simpa only [extChartAt_source] using hchartOuter y (hKO hy)
    · simpa only [extChartAt_source] using hchartAlt y (hKO hy)
    · rw [hOuterGraph y (hKO hy), hAltGraph y (hKO hy), hh]
  have hgerm := actual_subdisk_image_germ_of_projected_sections hq QOriginal A
    hQOriginal hA hr (hrb.trans hb) p P hK hKne hKO rOuter rAlt hrOuter hrAlt
    hchartOuter hchartAlt hrightOuter hrightAlt
    (fun y hy => ⟨hProper (hKS hy), hUnit (hKS hy)⟩)
    (fun y hy => hInner (hKS hy)) (fun y hy => hScaled (hKS hy)) hvalues
  exact ⟨N, hNN, hPN, hsplit, eOuter, eAlt, O, h0eOuter, h0eAlt, heOuterBall, heAltBall,
    heOuter, heAlt, hInvOuter, hInvAlt, hO, hy0, hOt,
    hhOuter, hhAlt, hrOuter, hrAlt, hchartOuter, hchartAlt, hrightOuter, hrightAlt,
    hsegment, hS, hSO, hSne, happroach, hfront, hparameters, hjets, hcurve,
    hInner, hProper, hUnit, hScaled, Aop, beta, c, hAop, hpos, hbeta, hc, hpde,
    eIso, lam, hyIso, hIsoO, hIso0, hIso, hIsoInv, hlam, hlamPos, hprincipal,
    hIsoApproach, hIsoOther, T, hT, hyT, hTIso, hTzero,
    K, hKeq, hK, hKne, hKside, hKO, hKzero, hvalues, hgerm⟩

end DifferentialGeometry.Geometry.IMS03ConsumerAudit
