/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Analysis.Calculus.Interpolation.FiniteClosedCover
import DifferentialGeometry.Analysis.Integration.Measure.SmoothNullImage
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.SmoothExtension
import DifferentialGeometry.Geometry.Measure.Area.LocalReparametrization
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Boundary
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

set_option autoImplicit false
noncomputable section

open Set Filter Bundle Manifold MeasureTheory DifferentialGeometry
open DifferentialGeometry.Geometry DifferentialGeometry.Topology
open scoped Topology ContDiff Manifold NNReal ENNReal

namespace DifferentialGeometry.Geometry

private theorem chart_disk_properties
    (e : PartialDiffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ℂ ℂ 1)
    (hsrc : Metric.closedBall (0 : ℂ) 1 ⊆ e.source) :
    let K := e '' Metric.closedBall (0 : ℂ) 1
    IsCompact K ∧
      e '' Metric.ball (0 : ℂ) 1 = interior K ∧
      e '' Metric.sphere (0 : ℂ) 1 = frontier K ∧
      volume (frontier K) = 0 ∧
      ∃ A B : ℝ≥0, LipschitzOnWith A e (Metric.closedBall (0 : ℂ) 1) ∧
        LipschitzOnWith B e.symm K := by
  dsimp only
  let K := e '' Metric.closedBall (0 : ℂ) 1
  have hK : IsCompact K := (isCompact_closedBall (0 : ℂ) 1).image_of_continuousOn
    (e.contMDiffOn_toFun.continuousOn.mono hsrc)
  have htarget : K ⊆ e.target := by
    rintro _ ⟨z, hz, rfl⟩
    exact e.map_source' (hsrc hz)
  have himage : e.toOpenPartialHomeomorph.IsImage
      (Metric.closedBall (0 : ℂ) 1) K := by
    apply OpenPartialHomeomorph.IsImage.of_image_eq
    change e '' (e.source ∩ Metric.closedBall (0 : ℂ) 1) = e.target ∩ K
    rw [inter_eq_right.mpr hsrc, inter_eq_right.mpr htarget]
  have hinterior : e '' Metric.ball (0 : ℂ) 1 = interior K := by
    have h := himage.interior.image_eq
    change e '' (e.source ∩ interior (Metric.closedBall (0 : ℂ) 1)) =
      e.target ∩ interior K at h
    rw [inter_eq_right.mpr (interior_subset.trans hsrc),
      inter_eq_right.mpr (interior_subset.trans htarget),
      interior_closedBall (0 : ℂ) one_ne_zero] at h
    exact h
  have hfrontier : e '' Metric.sphere (0 : ℂ) 1 = frontier K := by
    simpa only [frontier_closedBall (0 : ℂ) one_ne_zero] using
      e.image_frontier_of_isCompact (isCompact_closedBall (0 : ℂ) 1) hsrc
  have he : ContDiffOn ℝ 1 e e.source :=
    contMDiffOn_iff_contDiffOn.mp e.contMDiffOn_toFun
  have hei : ContDiffOn ℝ 1 e.symm e.target :=
    contMDiffOn_iff_contDiffOn.mp e.symm.contMDiffOn_toFun
  have hnull : volume (frontier K) = 0 := by
    rw [← hfrontier]
    exact DifferentialGeometry.Analysis.volume_image_sphere_eq_zero_of_contDiffOn
      e.open_source he 0 1 (Metric.sphere_subset_closedBall.trans hsrc)
  obtain ⟨A, hA⟩ := he.exists_lipschitzOnWith_of_isCompact e.open_source
    (isCompact_closedBall (0 : ℂ) 1) hsrc
  obtain ⟨B, hB⟩ := hei.exists_lipschitzOnWith_of_isCompact e.open_target hK htarget
  exact ⟨hK, hinterior, hfrontier, hnull, A, B, hA, hB⟩

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
/-- Replace the second actual interior source subdisk by a copy of the first.
The source charts and their common boundary trace are geometric inputs; the
replacement disk, its metric Lipschitz bound, exact original trace, exterior
range, and subtraction/addition formula for its actual area are constructed.
The two subdisks may overlap. This does not construct the paired boundary loops
from a self-intersection, or assert that the copied area is automatically smaller. -/
theorem exists_paired_subdisk_replacement
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (u : C(closedDisk, M))
    {Uext : ℂ → M} (hUext : SmoothDiskExtension (E := E) u Uext)
    (e₁ e₂ : PartialDiffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ℂ ℂ 1)
    (hsrc₁ : Metric.closedBall (0 : ℂ) 1 ⊆ e₁.source)
    (hsrc₂ : Metric.closedBall (0 : ℂ) 1 ⊆ e₂.source)
    (hinside₁ : e₁ '' Metric.closedBall (0 : ℂ) 1 ⊆ Metric.ball (0 : ℂ) 1)
    (hinside₂ : e₂ '' Metric.closedBall (0 : ℂ) 1 ⊆ Metric.ball (0 : ℂ) 1)
    (hboundary : ∀ z ∈ Metric.sphere (0 : ℂ) 1,
      diskExtension u (e₁ z) = diskExtension u (e₂ z))
    {W : Set M} (huW : Set.range u ⊆ W) :
    let K₁ := e₁ '' Metric.closedBall (0 : ℂ) 1
    let K₂ := e₂ '' Metric.closedBall (0 : ℂ) 1
    let φ := (e₁ : ℂ → ℂ) ∘ e₂.symm
    ∃ (v : C(closedDisk, M)) (L : ℝ≥0),
      (∀ z w : closedDisk, riemannianEDistOf g (v z) (v w) ≤
        (L : ℝ≥0∞) * edist z w) ∧
      diskTrace v = diskTrace u ∧ Set.range v ⊆ W ∧
      (∀ z : closedDisk, (z : ℂ) ∈ K₂ → v z = diskExtension u (φ z)) ∧
      (∀ z : closedDisk, (z : ℂ) ∉ interior K₂ → v z = u z) ∧
      riemannianDiskArea g v = riemannianDiskArea g u -
        riemannianArea g (diskExtension u) K₂ + riemannianArea g (diskExtension u) K₁ ∧
      (riemannianArea g (diskExtension u) K₁ ≤ riemannianArea g (diskExtension u) K₂ →
        riemannianDiskArea g v ≤ riemannianDiskArea g u) := by
  classical
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨g.toRiemannianMetric⟩
  have : IsContinuousRiemannianBundle E (TangentSpace 𝓘(ℝ, E) : M → Type _) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  let : PseudoEMetricSpace M := .ofRiemannianMetric 𝓘(ℝ, E) M
  let U := diskExtension u
  let K₁ := e₁ '' Metric.closedBall (0 : ℂ) 1
  let K₂ := e₂ '' Metric.closedBall (0 : ℂ) 1
  let φ : ℂ → ℂ := (e₁ : ℂ → ℂ) ∘ e₂.symm
  let ψ : ℂ → ℂ := (e₂ : ℂ → ℂ) ∘ e₁.symm
  obtain ⟨_, hint₁, _, hnull₁, A₁, B₁, hA₁, hB₁⟩ :=
    chart_disk_properties e₁ hsrc₁
  obtain ⟨hK₂, hint₂, hfront₂, hnull₂, A₂, B₂, hA₂, hB₂⟩ :=
    chart_disk_properties e₂ hsrc₂
  have hinv₁ : MapsTo e₁.symm K₁ (Metric.closedBall (0 : ℂ) 1) := by
    rintro _ ⟨z, hz, rfl⟩
    have hi : e₁.symm (e₁ z) = z := e₁.toPartialEquiv.left_inv (hsrc₁ hz)
    simpa only [hi] using hz
  have hinv₂ : MapsTo e₂.symm K₂ (Metric.closedBall (0 : ℂ) 1) := by
    rintro _ ⟨z, hz, rfl⟩
    have hi : e₂.symm (e₂ z) = z := e₂.toPartialEquiv.left_inv (hsrc₂ hz)
    simpa only [hi] using hz
  have hφe₂ (z : ℂ) (hz : z ∈ Metric.closedBall (0 : ℂ) 1) : φ (e₂ z) = e₁ z := by
    change e₁ (e₂.symm (e₂ z)) = e₁ z
    exact congrArg (e₁ : ℂ → ℂ) (e₂.toPartialEquiv.left_inv (hsrc₂ hz))
  have hψe₁ (z : ℂ) (hz : z ∈ Metric.closedBall (0 : ℂ) 1) : ψ (e₁ z) = e₂ z := by
    change e₂ (e₁.symm (e₁ z)) = e₂ z
    exact congrArg (e₂ : ℂ → ℂ) (e₁.toPartialEquiv.left_inv (hsrc₁ hz))
  have hφmaps : MapsTo φ K₂ K₁ := by
    rintro _ ⟨z, hz, rfl⟩
    rw [hφe₂ z hz]
    exact mem_image_of_mem e₁ hz
  have hψφ (z : ℂ) (hz : z ∈ K₂) : ψ (φ z) = z := by
    obtain ⟨x, hx, rfl⟩ := hz
    rw [hφe₂ x hx, hψe₁ x hx]
  have hφLip : LipschitzOnWith (A₁ * B₂) φ K₂ := hA₁.comp hB₂ hinv₂
  have hψLip : LipschitzOnWith (A₂ * B₁) ψ K₁ := hA₂.comp hB₁ hinv₁
  have hφlower : ∀ x ∈ K₂, ∀ y ∈ K₂,
      edist x y ≤ ((A₂ * B₁ : ℝ≥0) : ℝ≥0∞) * edist (φ x) (φ y) := by
    intro x hx y hy
    simpa only [hψφ x hx, hψφ y hy] using hψLip (hφmaps hx) (hφmaps hy)
  have hφinterior : φ '' interior K₂ = interior K₁ := by
    rw [← hint₂, ← hint₁]
    ext y
    constructor
    · rintro ⟨x, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨z, hz, (hφe₂ z (Metric.ball_subset_closedBall hz)).symm⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨e₂ z, mem_image_of_mem e₂ hz, hφe₂ z (Metric.ball_subset_closedBall hz)⟩
  have hmatch : EqOn (U ∘ φ) U (frontier K₂) := by
    intro x hx
    rw [← hfront₂] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    change U (φ (e₂ z)) = U (e₂ z)
    rw [hφe₂ z (Metric.sphere_subset_closedBall hz)]
    exact hboundary z hz
  obtain ⟨C, hC⟩ := hUext.lipschitz g
  have hULip : LipschitzWith C U := diskExtension_riemannian_lipschitz g hC
  have hcopiedLip : LipschitzOnWith (C * (A₁ * B₂)) (U ∘ φ) K₂ :=
    hULip.comp_lipschitzOnWith hφLip
  let F : ℂ → M := K₂.piecewise (U ∘ φ) U
  have hFinner : EqOn F (U ∘ φ) K₂ := fun _ hz => piecewise_eq_of_mem _ _ _ hz
  have hFouter : EqOn F U (interior K₂)ᶜ := by
    intro z hz
    by_cases hzK : z ∈ K₂
    · exact (hFinner hzK).trans (hmatch ((mem_frontier_iff_notMem_interior hzK).mpr hz))
    · exact piecewise_eq_of_notMem _ _ _ hzK
  let cells : Bool → Set ℂ := fun b => if b then (interior K₂)ᶜ else K₂
  let constants : Bool → ℝ≥0 := fun b => if b then C else C * (A₁ * B₂)
  have hcellsClosed : ∀ b, IsClosed ((Subtype.val : closedDisk → ℂ) ⁻¹' cells b) := by
    intro b
    cases b
    · exact hK₂.isClosed.preimage continuous_subtype_val
    · exact isOpen_interior.isClosed_compl.preimage continuous_subtype_val
  have hcover : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, ∃ b, z ∈ cells b := by
    intro z _
    by_cases hz : z ∈ K₂
    · exact ⟨false, hz⟩
    · exact ⟨true, fun hi => hz (interior_subset hi)⟩
  have hcellLip : ∀ b, LipschitzOnWith (constants b) F
      (Metric.closedBall (0 : ℂ) 1 ∩ cells b) := by
    intro b
    cases b
    · intro x hx y hy
      rw [hFinner hx.2, hFinner hy.2]
      exact hcopiedLip hx.2 hy.2
    · intro x hx y hy
      rw [hFouter hx.2, hFouter hy.2]
      exact hULip x y
  have hFLip : LipschitzOnWith (Finset.univ.sup constants) F
      (Metric.closedBall (0 : ℂ) 1) :=
    DifferentialGeometry.Analysis.lipschitzOnWith_of_finite_closed_cover
      (convex_closedBall (0 : ℂ) 1) cells hcellsClosed hcover constants hcellLip
  let v : C(closedDisk, M) := ⟨fun z => F z, hFLip.to_restrict.continuous⟩
  have hvLip : ∀ z w : closedDisk, riemannianEDistOf g (v z) (v w) ≤
      ((Finset.univ.sup constants : ℝ≥0) : ℝ≥0∞) * edist z w :=
    fun z w => hFLip z.property w.property
  have hvinner (z : closedDisk) (hz : (z : ℂ) ∈ K₂) : v z = U (φ z) :=
    hFinner hz
  have hvouter (z : closedDisk) (hz : (z : ℂ) ∉ interior K₂) : v z = u z :=
    (hFouter hz).trans (diskExtension_coe u z)
  have hvtrace : diskTrace v = diskTrace u := by
    ext θ
    change v (diskBoundary θ) = u (diskBoundary θ)
    apply hvouter
    intro hz
    have hin := hinside₂ (interior_subset hz)
    have hn : ‖(diskBoundary θ : ℂ)‖ < 1 := by
      simpa only [Metric.mem_ball, dist_zero_right] using hin
    have heq : ‖((diskBoundary θ : closedDisk) : ℂ)‖ = 1 := Circle.norm_coe _
    exact (not_lt_of_ge heq.ge) hn
  have hvW : Set.range v ⊆ W := by
    rintro _ ⟨z, rfl⟩
    by_cases hz : (z : ℂ) ∈ K₂
    · rw [hvinner z hz]
      let q : closedDisk := ⟨φ z, Metric.ball_subset_closedBall (hinside₁ (hφmaps hz))⟩
      have heq : U (φ z) = u q := diskExtension_coe u q
      rw [heq]
      exact huW (mem_range_self q)
    · rw [hvouter z (fun hi => hz (interior_subset hi))]
      exact huW (mem_range_self z)
  have hK₂D : K₂ ⊆ Metric.closedBall (0 : ℂ) 1 :=
    hinside₂.trans Metric.ball_subset_closedBall
  have hclosedInterior (f : ℂ → M) (K : Set ℂ) (hnull : volume (frontier K) = 0) :
      riemannianArea g f K = riemannianArea g f (interior K) := by
    exact setIntegral_congr_set (interior_ae_eq_of_null_frontier hnull).symm
  have hinsArea : riemannianArea g (diskExtension v) K₂ = riemannianArea g U K₁ := by
    calc
      _ = riemannianArea g (diskExtension v) (interior K₂) :=
        hclosedInterior _ _ hnull₂
      _ = riemannianArea g (U ∘ φ) (interior K₂) := by
        apply riemannianArea_congr_on_open g isOpen_interior
        intro z hz
        let q : closedDisk := ⟨z, hK₂D (interior_subset hz)⟩
        exact (diskExtension_coe v q).trans (hvinner q (interior_subset hz))
      _ = riemannianArea g U (φ '' interior K₂) :=
        riemannianArea_precomp_on g hULip isOpen_interior
          (hφLip.mono interior_subset)
          (fun x hx y hy => hφlower x (interior_subset hx) y (interior_subset hy))
      _ = riemannianArea g U (interior K₁) := by rw [hφinterior]
      _ = riemannianArea g U K₁ := (hclosedInterior _ _ hnull₁).symm
  have hiu : IntegrableOn (riemannianAreaDensity g U) (Metric.closedBall (0 : ℂ) 1) :=
    integrable_riemannianDiskAreaDensity g hC
  have hiv : IntegrableOn (riemannianAreaDensity g (diskExtension v))
      (Metric.closedBall (0 : ℂ) 1) := integrable_riemannianDiskAreaDensity g hvLip
  have houtArea :
      (∫ z in Metric.closedBall (0 : ℂ) 1 \ K₂,
        riemannianAreaDensity g (diskExtension v) z) =
      ∫ z in Metric.closedBall (0 : ℂ) 1 \ K₂, riemannianAreaDensity g U z := by
    have hzint : ∀ᵐ z ∂volume.restrict (Metric.closedBall (0 : ℂ) 1 \ K₂),
        z ∈ Metric.ball (0 : ℂ) 1 :=
      ae_restrict_of_ae_restrict_of_subset sdiff_subset ae_disk_interior
    apply integral_congr_ae
    filter_upwards [hzint,
      ae_restrict_mem (measurableSet_closedBall.diff hK₂.measurableSet)] with z hz hzd
    apply riemannianAreaDensity_congr g
    filter_upwards [(Metric.isOpen_ball.inter hK₂.isClosed.isOpen_compl).mem_nhds
      ⟨hz, hzd.2⟩] with y hy
    let q : closedDisk := ⟨y, Metric.ball_subset_closedBall hy.1⟩
    exact (diskExtension_coe v q).trans
      ((hvouter q (fun hi => hy.2 (interior_subset hi))).trans (diskExtension_coe u q).symm)
  have harea : riemannianDiskArea g v = riemannianDiskArea g u -
      riemannianArea g U K₂ + riemannianArea g U K₁ := by
    have hsu := setIntegral_sdiff hK₂.measurableSet hiu hK₂D
    have hsv := setIntegral_sdiff hK₂.measurableSet hiv hK₂D
    change (∫ z in K₂, riemannianAreaDensity g (diskExtension v) z) =
      (∫ z in K₁, riemannianAreaDensity g U z) at hinsArea
    rw [houtArea, hinsArea, hsu] at hsv
    change (∫ z in Metric.closedBall (0 : ℂ) 1, riemannianAreaDensity g (diskExtension v) z) =
      (∫ z in Metric.closedBall (0 : ℂ) 1, riemannianAreaDensity g U z) -
      (∫ z in K₂, riemannianAreaDensity g U z) + ∫ z in K₁, riemannianAreaDensity g U z
    linarith
  refine ⟨v, Finset.univ.sup constants, hvLip, hvtrace, hvW, hvinner, hvouter, harea, ?_⟩
  intro horder
  linarith [harea]

end DifferentialGeometry.Geometry
