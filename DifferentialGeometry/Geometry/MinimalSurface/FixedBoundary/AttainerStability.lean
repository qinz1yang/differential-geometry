import DifferentialGeometry.Geometry.Submanifold.NormalBundle.UnitNormal
import DifferentialGeometry.Geometry.MinimalSurface.Stability.EveryAreaMinimizer
import DifferentialGeometry.Topology.Diffeomorph.Flow
import Mathlib.Analysis.Convex.Contractible
import DifferentialGeometry.Topology.Manifold.EmbeddedHypersurface.CompactSectionExtension
import DifferentialGeometry.Bundle.Section
import DifferentialGeometry.Geometry.MinimalSurface.ExteriorDiskArea
import DifferentialGeometry.Topology.Manifold.ImmersionCriterion
import DifferentialGeometry.Topology.Manifold.OpenSubtype
import DifferentialGeometry.Topology.Manifold.EmbeddedHypersurface.LocalAmbientSectionExtension
import DifferentialGeometry.Geometry.MinimalSurface.Curvature.DiskStationarity
import DifferentialGeometry.Geometry.MinimalSurface.Curvature.DiskJacobiPotential
import DifferentialGeometry.Geometry.Metric.Coordinates.InnerExpansion
import DifferentialGeometry.Geometry.Measure.Area.NormalSecondIntegral
import DifferentialGeometry.Analysis.Calculus.SecondDerivative.Minimum
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.Global.IntegrationByParts
import DifferentialGeometry.Geometry.Operator.Gradient.NormSquared
import DifferentialGeometry.Geometry.MinimalSurface.Curvature.DiskFullJacobiPotential

set_option autoImplicit false
noncomputable section

local notation "diskInterior" =>
  TopologicalSpace.Opens.mk (Metric.ball (0 : ℂ) 1) Metric.isOpen_ball

section

open DifferentialGeometry DifferentialGeometry.Topology Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.MinimalSurface



open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.MinimalSurface

/-- The original exterior disk supplies a normal atlas on its actual open
interior. Its smooth extension is used on the same complex plane, and embedding
is asserted only on the original closed disk. -/
private theorem exists_actual_disk_interior_normalAtlas
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    {W : Set M} {γ : freeLoop M} {u : C(closedDisk, M)}
    (hu : isExteriorSpanningDisk W γ u) :
    ∃ U : ℂ → M, SmoothDiskExtension (E := EuclideanSpace ℝ (Fin 3)) u U ∧
      (∀ z ∈ Metric.closedBall (0 : ℂ) 1,
        Function.Injective (mfderiv 𝓘(ℝ, ℂ) (𝓡 3) U z)) ∧
      _root_.Topology.IsEmbedding (fun z : closedDisk => U z) ∧
      Nonempty (SmoothEmbeddingRealNormalAtlas 𝓘(ℝ, ℂ) (𝓡 3) ∞
        (fun z : diskInterior => U z)) ∧
      ∀ z : diskInterior, U z ∈ interior W := by
  obtain ⟨htrace, hfrontier, hemb, hrange, hint, U, hU, himm⟩ := hu
  have hembK : _root_.Topology.IsEmbedding (fun z : closedDisk => U z) := by
    rw [show (fun z : closedDisk => U z) = u from funext hU.1]
    exact hemb
  have hembD : _root_.Topology.IsEmbedding (fun z : diskInterior => U z) :=
    hembK.comp (_root_.Topology.IsEmbedding.inclusion Metric.ball_subset_closedBall)
  obtain ⟨N, _, hDN, hUs⟩ := hU.2
  have hsm : ContMDiff 𝓘(ℝ, ℂ) (𝓡 3) ∞ (fun z : diskInterior => U z) :=
    hUs.comp_contMDiff contMDiff_subtype_val
      (fun z => hDN (Metric.ball_subset_closedBall z.property))
  have hinj : ∀ z : diskInterior, Function.Injective
      (mfderiv 𝓘(ℝ, ℂ) (𝓡 3) (fun w : diskInterior => U w) z) := by
    intro z
    rw [DifferentialGeometry.mfderiv_restrict_open]
    exact himm z (Metric.ball_subset_closedBall z.property)
  have hImm : _root_.Manifold.IsImmersion 𝓘(ℝ, ℂ) (𝓡 3) ∞
      (fun z : diskInterior => U z) :=
    DifferentialGeometry.Topology.Manifold.isImmersion_of_injective_mfderiv
      (by simp) hsm hinj
  let : Nonempty diskInterior := ⟨⟨0, by
    change (0 : ℂ) ∈ Metric.ball (0 : ℂ) 1
    simp⟩⟩
  have hcodim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) =
      Module.finrank ℝ ℂ + 1 := by simp
  let C := smoothEmbeddingRealNormalAtlasOfIsImmersionOfComplement hembD
    (isImmersionOfComplement_real_of_finrank_succ hcodim hImm)
  refine ⟨U, hU, himm, hembK, ⟨C⟩, ?_⟩
  intro z
  let zK : closedDisk := ⟨z, Metric.ball_subset_closedBall z.property⟩
  change U (zK : ℂ) ∈ interior W
  rw [hU.1 zK]
  apply hint zK
  change ‖(z : ℂ)‖ < 1
  have hz : (z : ℂ) ∈ Metric.ball (0 : ℂ) 1 := z.property
  simpa only [Metric.mem_ball, dist_zero_right] using hz

end DifferentialGeometry.Geometry.MinimalSurface


namespace DifferentialGeometry.Geometry.MinimalSurface

open Bundle
open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.MinimalSurface
open scoped _root_.Topology

/-- Every compactly supported smooth along-disk test is realized by an ambient
field supported in the actual exterior interior, with exact zero boundary values. -/
private theorem exists_actual_disk_test_ambientExtension
    {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    {W : Set M} {γ : freeLoop M} {u : C(closedDisk, M)}
    (hu : isExteriorSpanningDisk W γ u) :
    ∃ U : ℂ → M, SmoothDiskExtension (E := EuclideanSpace ℝ (Fin 3)) u U ∧
      (∀ z ∈ Metric.closedBall (0 : ℂ) 1,
        Function.Injective (mfderiv 𝓘(ℝ, ℂ) (𝓡 3) U z)) ∧
      ∀ (ν : ∀ z : diskInterior, TangentSpace (𝓡 3) (U z)),
        ContMDiff 𝓘(ℝ, ℂ) (𝓡 3).tangent ∞
          (fun z : diskInterior => (⟨U z, ν z⟩ : TangentBundle (𝓡 3) M)) →
        ∀ (φ : diskInterior → ℝ), ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) ∞ φ →
          HasCompactSupport φ →
          ∃ X : ∀ a : M, TangentSpace (𝓡 3) a,
            ContMDiff (𝓡 3) (𝓡 3).tangent ∞
              (fun a => (⟨a, X a⟩ : TangentBundle (𝓡 3) M)) ∧
            HasCompactSupport X ∧ tsupport X ⊆ interior W ∧
            (∀ z : diskInterior,
              X (u ⟨z, Metric.ball_subset_closedBall z.property⟩) = φ z • ν z) ∧
            ∀ z : closedDisk, ‖(z : ℂ)‖ = 1 → X (u z) = 0 := by
  obtain ⟨U, hU, hiU, hemb, ⟨C⟩, hint⟩ :=
    exists_actual_disk_interior_normalAtlas hu
  refine ⟨U, hU, hiU, ?_⟩
  intro ν hν φ hφ hφc
  have hsub : closure {z : diskInterior | φ z • ν z ≠ 0} ⊆ tsupport φ := by
    apply closure_mono
    intro z hz hzφ
    exact hz (by simp only [hzφ, zero_smul])
  have hcompact : IsCompact (closure {z : diskInterior | φ z • ν z ≠ 0}) :=
    hφc.of_isClosed_subset isClosed_closure hsub
  obtain ⟨X, hX, hXc, hXO, hXi, hXb⟩ :=
    SmoothEmbeddingRealNormalAtlas.exists_ambientSection_on_compact_domain
      (I := 𝓘(ℝ, ℂ)) (J := 𝓡 3)
      (isCompact_closedBall (0 : ℂ) 1) diskInterior Metric.ball_subset_closedBall
      hemb C (fun z => φ z • ν z) (hφ.smul_bundle hν) hcompact
      isOpen_interior (fun z _ => hint z)
  refine ⟨X, hX, hXc, hXO, ?_, ?_⟩
  · intro z
    rw [← hU.1 ⟨z, Metric.ball_subset_closedBall z.property⟩]
    exact hXi z
  · intro z hz
    rw [← hU.1 z]
    apply hXb z
    refine ⟨z.property, ?_⟩
    change (z : ℂ) ∉ Metric.ball (0 : ℂ) 1
    simp only [Metric.mem_ball, dist_zero_right, hz, lt_self_iff_false, not_false_eq_true]

end DifferentialGeometry.Geometry.MinimalSurface


namespace DifferentialGeometry.Geometry.MinimalSurface

open Bundle
open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.MinimalSurface
open scoped _root_.Topology

/-- Contractibility of the actual complex disk coorients its actual normal atlas. -/
private theorem exists_transverse_disk_field
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    {U : ℂ → M}
    (C : SmoothEmbeddingRealNormalAtlas 𝓘(ℝ, ℂ) (𝓡 3) ∞
      (fun z : diskInterior => U z)) :
    ∃ V : ∀ z : diskInterior, TangentSpace (𝓡 3) (U z),
      ContMDiff 𝓘(ℝ, ℂ) (𝓡 3).tangent ∞
        (fun z : diskInterior => (⟨U z, V z⟩ : TangentBundle (𝓡 3) M)) ∧
      ∀ z : diskInterior,
        V z ∉ (mfderiv 𝓘(ℝ, ℂ) (𝓡 3) (fun w : diskInterior => U w) z).range := by
  let z₀ : diskInterior := ⟨0, by simp⟩
  let : ContractibleSpace diskInterior :=
    (convex_ball (0 : ℂ) 1).contractibleSpace ⟨0, by simp⟩
  let : SimplyConnectedSpace diskInterior := inferInstance
  let : LocallyPathConnectedSpace diskInterior :=
    ChartedSpace.locallyPathConnectedSpace ℂ diskInterior
  let : LocallyCompactSpace diskInterior :=
    (diskInterior : TopologicalSpace.Opens ℂ).isOpen.locallyCompactSpace
  let : SigmaCompactSpace diskInterior := inferInstance
  obtain ⟨Cplus⟩ := C.nonempty_coorientedAtlas z₀ false
  obtain ⟨V, _, htrans⟩ := Cplus.exists_contMDiff_transverseSection (m := ⊤) (by simp)
  have hV : ContMDiff 𝓘(ℝ, ℂ) (𝓡 3).tangent ∞
      (fun z : diskInterior => (⟨U z, V z⟩ : TangentBundle (𝓡 3) M)) := by
    intro z
    apply Bundle.contMDiffAt_totalSpace.mpr
    refine ⟨C.contMDiff z, ?_⟩
    exact (Bundle.contMDiffAt_totalSpace.mp (V.contMDiff z)).2
  exact ⟨V, hV, htrans⟩

/-- Every actual immersed exterior disk has a smooth unit normal for the original
metric and any fixed smooth extension of that same disk. Ambient orientation is unnecessary. -/
theorem isExteriorSpanningDisk.exists_unit_normal
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    (g : SmoothRiemannianMetric (𝓡 3) M)
    {W : Set M} {γ : freeLoop M} {u : C(closedDisk, M)}
    (hu : isExteriorSpanningDisk W γ u) {U : ℂ → M}
    (hU : SmoothDiskExtension (E := EuclideanSpace ℝ (Fin 3)) u U) :
    ∃ ν : ∀ z : diskInterior, TangentSpace (𝓡 3) (U z),
      ContMDiff 𝓘(ℝ, ℂ) (𝓡 3).tangent ∞
        (fun z : diskInterior => (⟨U z, ν z⟩ : TangentBundle (𝓡 3) M)) ∧
      (∀ z : diskInterior, g.inner (U z) (ν z) (ν z) = 1) ∧
      ∀ (z : diskInterior) (v : ℂ),
        g.inner (U z) (ν z)
          (mfderiv 𝓘(ℝ, ℂ) (𝓡 3) (fun w : diskInterior => U w) z v) = 0 := by
  obtain ⟨U₀, hU₀, himm₀⟩ := hu.2.2.2.2.2
  have hembK : _root_.Topology.IsEmbedding (fun z : closedDisk => U z) := by
    rw [show (fun z : closedDisk => U z) = u from funext hU.1]
    exact hu.2.2.1
  have hembD : _root_.Topology.IsEmbedding (fun z : diskInterior => U z) :=
    hembK.comp (_root_.Topology.IsEmbedding.inclusion Metric.ball_subset_closedBall)
  obtain ⟨N, _, hDN, hUs⟩ := hU.2
  have hsm : ContMDiff 𝓘(ℝ, ℂ) (𝓡 3) ∞ (fun z : diskInterior => U z) :=
    hUs.comp_contMDiff contMDiff_subtype_val
      (fun z => hDN (Metric.ball_subset_closedBall z.property))
  have hinj : ∀ z : diskInterior, Function.Injective
      (mfderiv 𝓘(ℝ, ℂ) (𝓡 3) (fun w : diskInterior => U w) z) := by
    intro z
    have heq : U =ᶠ[𝓝 (z : ℂ)] U₀ :=
      (hU.eventuallyEq_diskExtension z.property).trans
        (hU₀.eventuallyEq_diskExtension z.property).symm
    rw [DifferentialGeometry.mfderiv_restrict_open, heq.mfderiv_eq]
    exact himm₀ z (Metric.ball_subset_closedBall z.property)
  have hImm : _root_.Manifold.IsImmersion 𝓘(ℝ, ℂ) (𝓡 3) ∞
      (fun z : diskInterior => U z) :=
    DifferentialGeometry.Topology.Manifold.isImmersion_of_injective_mfderiv
      (by simp) hsm hinj
  let : Nonempty diskInterior := ⟨⟨0, by simp⟩⟩
  let C := smoothEmbeddingRealNormalAtlasOfIsImmersionOfComplement hembD
    (isImmersionOfComplement_real_of_finrank_succ (by simp) hImm)
  obtain ⟨V, hV, htrans⟩ := exists_transverse_disk_field C
  exact exists_contMDiff_unit_normal_of_transverse g hsm hinj V hV htrans

end DifferentialGeometry.Geometry.MinimalSurface


namespace DifferentialGeometry.Geometry.MinimalSurface

open Bundle Filter DifferentialGeometry.Geometry.MinimalSurface
open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.MinimalSurface
open scoped _root_.Topology

/-- Every attaining exterior disk has a genuine metric unit normal whose compact
scalar tests are realized by admissible ambient flows of the original disk.
The disk and its normal are fixed before the scalar test is chosen. -/
theorem exists_normal_test_flows_of_attains_leastExteriorDiskArea
    {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    (g : SmoothRiemannianMetric (𝓡 3) M)
    {W : Set M} {γ : freeLoop M} {u : C(closedDisk, M)}
    (hu : isExteriorSpanningDisk W γ u)
    (harea : riemannianDiskArea g u = leastExteriorDiskArea g W γ) :
    ∃ U : ℂ → M, SmoothDiskExtension (E := EuclideanSpace ℝ (Fin 3)) u U ∧
      (∀ z ∈ Metric.closedBall (0 : ℂ) 1,
        Function.Injective (mfderiv 𝓘(ℝ, ℂ) (𝓡 3) U z)) ∧
        ∃ ν : ∀ z : diskInterior, TangentSpace (𝓡 3) (U z),
          ContMDiff 𝓘(ℝ, ℂ) (𝓡 3).tangent ∞
            (fun z : diskInterior => (⟨U z, ν z⟩ : TangentBundle (𝓡 3) M)) ∧
          (∀ z : diskInterior, g.inner (U z) (ν z) (ν z) = 1) ∧
          (∀ (z : diskInterior) (a : ℂ),
            g.inner (U z) (ν z)
              (mfderiv 𝓘(ℝ, ℂ) (𝓡 3) (fun w : diskInterior => U w) z a) = 0) ∧
          ∀ (φ : diskInterior → ℝ), ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) ∞ φ →
            HasCompactSupport φ →
            ∃ (X : ∀ a : M, TangentSpace (𝓡 3) a)
              (hX : ContMDiff (𝓡 3) (𝓡 3).tangent ∞
                (fun a => (⟨a, X a⟩ : TangentBundle (𝓡 3) M)))
              (hXc : HasCompactSupport X),
              tsupport X ⊆ interior W ∧
              let Φ := Diffeomorph.compactSupportFlow X hX hXc
              let v : ℝ → C(closedDisk, M) := fun t =>
                (⟨Φ t, (Φ t).continuous⟩ : C(M, M)).comp u
              ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 3) ∞
                (fun p : ℝ × M => Φ p.1 p.2) ∧
              Φ 0 = Diffeomorph.refl (𝓡 3) M ∞ ∧
              (∀ z : diskInterior,
                HasMFDerivAt 𝓘(ℝ, ℝ) (𝓡 3)
                  (fun t => Φ t (u ⟨z, Metric.ball_subset_closedBall z.property⟩)) 0
                  ((1 : ℝ →L[ℝ] ℝ).smulRight (φ z • ν z))) ∧
              (∀ t : ℝ, isExteriorSpanningDisk W γ (v t)) ∧
              IsLocalMin (fun t => riemannianDiskArea g (v t)) 0 := by
  obtain ⟨U, hU, hiU, hrealize⟩ :=
    exists_actual_disk_test_ambientExtension hu
  obtain ⟨ν, hν, hunit, hnormal⟩ :=
    isExteriorSpanningDisk.exists_unit_normal g hu hU
  refine ⟨U, hU, hiU, ν, hν, hunit, hnormal, ?_⟩
  intro φ hφ hφc
  obtain ⟨X, hX, hXc, hXO, hXi, _⟩ := hrealize ν hν φ hφ hφc
  refine ⟨X, hX, hXc, hXO, ?_⟩
  let Φ := Diffeomorph.compactSupportFlow X hX hXc
  let v : ℝ → C(closedDisk, M) := fun t =>
    (⟨Φ t, (Φ t).continuous⟩ : C(M, M)).comp u
  have hcenter : ∀ z : closedDisk, Φ 0 (u z) = u z := by
    intro z
    exact DFunLike.congr_fun (Diffeomorph.compactSupportFlow_zero X hX hXc) (u z)
  have hfix (t : ℝ) : EqOn (Φ t) id (interior W)ᶜ :=
    (Diffeomorph.compactSupportFlow_eqOn_compl_tsupport X hX hXc t).1.mono
      (compl_subset_compl.mpr hXO)
  refine ⟨Diffeomorph.contMDiff_compactSupportFlow X hX hXc,
    Diffeomorph.compactSupportFlow_zero X hX hXc, ?_, ?_, ?_⟩
  · intro z
    let zK : closedDisk := ⟨z, Metric.ball_subset_closedBall z.property⟩
    have hcurve := Diffeomorph.isMIntegralCurve_compactSupportFlow X hX hXc (u zK) 0
    change HasMFDerivAt 𝓘(ℝ, ℝ) (𝓡 3) (fun t => Φ t (u zK)) 0
      ((1 : ℝ →L[ℝ] ℝ).smulRight (X (Φ 0 (u zK)))) at hcurve
    rw [hcenter zK, hXi z] at hcurve
    exact hcurve
  · intro t
    exact hu.comp_diffeomorph_of_eqOn_compl_interior (Φ t) (hfix t)
  · exact isLocalMin_area_comp_diffeomorph_of_attains_leastExteriorDiskArea
      g hu harea Φ hcenter (Filter.Eventually.of_forall hfix)

end DifferentialGeometry.Geometry.MinimalSurface

end

section

open Bundle Filter Manifold Set MeasureTheory DifferentialGeometry
open DifferentialGeometry.Geometry DifferentialGeometry.Topology
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff _root_.Topology BigOperators

namespace DifferentialGeometry.Geometry.MinimalSurface

local notation "D" => TopologicalSpace.Opens.mk (Metric.ball (0 : ℂ) 1) Metric.isOpen_ball

private local instance : MeasurableSpace D := borel D
private local instance : BorelSpace D := ⟨rfl⟩
private local instance : LocallyCompactSpace D :=
  (D : TopologicalSpace.Opens ℂ).isOpen.locallyCompactSpace
private local instance : SigmaCompactSpace D := by infer_instance

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M] [T2Space M]

private theorem original_disk_zero_mean_curvature_and_jacobi_potential_of_all_normal_flow_localMin
    (g : SmoothRiemannianMetric (𝓡 3) M)
    (u : C(closedDisk, M)) (U : ℂ → M)
    (hExt : SmoothDiskExtension (E := EuclideanSpace ℝ (Fin 3)) u U)
    (hImm : ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) (𝓡 3) U z))
    (ν : ∀ q : D, TangentSpace (𝓡 3) (U q))
    (hν : Continuous
      (fun q : D => (⟨U q, ν q⟩ : TangentBundle (𝓡 3) M)))
    (hunit : ∀ q : D, g.inner (U q) (ν q) (ν q) = 1)
    (hnormal : ∀ (q : D) (v : ℂ),
      g.inner (U q) (ν q)
        (mfderiv 𝓘(ℝ, ℂ) (𝓡 3) (fun p : D => U p) q v) = 0)
    (hflows : ∀ (φ : D → ℝ),
      ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) ∞ φ → HasCompactSupport φ →
      ∃ (X : ∀ x : M, TangentSpace (𝓡 3) x)
        (hX : ContMDiff (𝓡 3) ((𝓡 3).prod (𝓡 3)) ∞
          (fun x : M => (⟨x, X x⟩ : TangentBundle (𝓡 3) M)))
        (hXc : HasCompactSupport X),
        (∀ q : D,
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 3)
            (fun t => Diffeomorph.compactSupportFlow X hX hXc t (U q)) 0 (1 : ℝ) : EuclideanSpace ℝ (Fin 3)) =
              φ q • ν q) ∧
        IsLocalMin (fun t => riemannianDiskArea g
          ((⟨Diffeomorph.compactSupportFlow X hX hXc t,
            (Diffeomorph.compactSupportFlow X hX hXc t).contMDiff.continuous⟩ : C(M, M)).comp u)) 0) :
    ∃ (hUD : ContMDiff 𝓘(ℝ, ℂ) (𝓡 3) ∞ (fun q : D => U q))
      (hiD : ∀ q : D, Function.Injective
        (mfderiv 𝓘(ℝ, ℂ) (𝓡 3) (fun p : D => U p) q)),
    let f : D → M := fun q => U q
    let gD := g.pullback f hUD hiD
    ∀ (q : D) (b : Module.Basis (Fin 2) ℝ (TangentSpace 𝓘(ℝ, ℂ) q)),
      (∀ i j, gD.inner q (b i) (b j) = if i = j then 1 else 0) →
      (∑ i : Fin 2, secondFundamentalFormAmbientAt gD g f q (b i) (b i)) = 0 ∧
      (let P : Fin 2 → TangentSpace (𝓡 3) (U q) := fun i =>
        mfderiv 𝓘(ℝ, ℂ) (𝓡 3) U q (b i)
       let II := secondFundamentalFormAmbientAt gD g f q
       ((∑ i : Fin 2, g.inner (U q)
           ((riemannOp (LeviCivita g) (U q)) (ν q) (P i) (P i)) (ν q)) +
         ∑ i : Fin 2, ∑ j : Fin 2,
           g.inner (U q) (II (b i) (b j)) (II (b i) (b j))) =
         (metricScalarAt g (U q) +
           ∑ i : Fin 2, ∑ j : Fin 2,
             g.inner (U q) (II (b i) (b j)) (II (b i) (b j))) / 2 -
           metricScalarAt gD q / 2) := by
  classical
  have hExtCopy := hExt
  obtain ⟨_, s, _, hDs, hUs⟩ := hExtCopy
  have hUD : ContMDiff 𝓘(ℝ, ℂ) (𝓡 3) ∞ (fun q : D => U q) :=
    hUs.comp_contMDiff contMDiff_subtype_val
      (fun q => hDs (Metric.ball_subset_closedBall q.property))
  have hiD : ∀ q : D, Function.Injective
      (mfderiv 𝓘(ℝ, ℂ) (𝓡 3) (fun p : D => U p) q) := by
    intro q
    rw [DifferentialGeometry.mfderiv_restrict_open]
    exact hImm q (Metric.ball_subset_closedBall q.property)
  let f : D → M := fun q => U q
  let gD := g.pullback f hUD hiD
  have hscalar :=
    SmoothDiskExtension.normal_scalar_trace_eq_zero_of_all_normal_flow_localMin
      g u U hExt hImm hUD hiD ν hν hnormal hflows
  have hmetric (x : D) (v w : TangentSpace 𝓘(ℝ, ℂ) x) :
      g.inner (f x) (mfderiv 𝓘(ℝ, ℂ) (𝓡 3) f x v)
        (mfderiv 𝓘(ℝ, ℂ) (𝓡 3) f x w) = gD.inner x v w := rfl
  refine ⟨hUD, hiD, ?_⟩
  dsimp only
  intro q b hb
  let II := secondFundamentalFormAmbientAt gD g f q
  let S : TangentSpace (𝓡 3) (U q) := ∑ i : Fin 2, II (b i) (b i)
  have hnormalTrace : g.inner (U q) (ν q) S = 0 := by
    change g.inner (U q) (ν q) (∑ i : Fin 2, II (b i) (b i)) = 0
    rw [map_sum]
    have htrace := normal_scalar_secondFundamentalForm_disk_trace_eq_sum_orthonormal
      D g U hUD hiD q (ν q) b hb
    exact htrace.2.symm.trans (hscalar q)
  have htangentTrace (i : Fin 2) :
      g.inner (U q) (mfderiv 𝓘(ℝ, ℂ) (𝓡 3) f q (b i)) S = 0 := by
    change g.inner (U q) (mfderiv 𝓘(ℝ, ℂ) (𝓡 3) f q (b i))
      (∑ j : Fin 2, II (b j) (b j)) = 0
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro j _
    rw [g.symm (U q) (mfderiv 𝓘(ℝ, ℂ) (𝓡 3) f q (b i)) (II (b j) (b j))]
    exact secondFundamentalFormAmbientAt_inner_mfderiv_eq_zero_of_inner_map
      (gN := gD) (gM := g) (iota := f) hUD hmetric q (b j) (b j) (b i)
  let frame : Option (Fin 2) → TangentSpace (𝓡 3) (U q) :=
    fun i => i.elim (ν q) (fun j => mfderiv 𝓘(ℝ, ℂ) (𝓡 3) f q (b j))
  have hframe : ∀ i j, g.inner (U q) (frame i) (frame j) =
      if i = j then (1 : ℝ) else 0 := by
    intro i j
    cases i with
    | none =>
      cases j with
      | none =>
        change g.inner (U q) (ν q) (ν q) = 1
        exact hunit q
      | some j =>
        change g.inner (U q) (ν q) (mfderiv 𝓘(ℝ, ℂ) (𝓡 3) f q (b j)) = 0
        exact hnormal q (b j)
    | some i =>
      cases j with
      | none =>
        change g.inner (U q) (mfderiv 𝓘(ℝ, ℂ) (𝓡 3) f q (b i)) (ν q) = 0
        exact (g.symm (U q) _ _).trans (hnormal q (b i))
      | some j =>
        have hpair : g.inner (U q)
            (mfderiv 𝓘(ℝ, ℂ) (𝓡 3) f q (b i))
            (mfderiv 𝓘(ℝ, ℂ) (𝓡 3) f q (b j)) = if i = j then 1 else 0 := hb i j
        simpa only [frame, Option.elim_some, Option.some.injEq] using hpair
  have hcard : Fintype.card (Option (Fin 2)) =
      Module.finrank ℝ (TangentSpace (𝓡 3) (U q)) := by
    change Fintype.card (Option (Fin 2)) = Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))
    simp only [Fintype.card_option, Fintype.card_fin, finrank_euclideanSpace_fin]
  have hcoeff (i : Option (Fin 2)) : g.inner (U q) (frame i) S = 0 := by
    cases i with
    | none => exact hnormalTrace
    | some i => exact htangentTrace i
  have hmean : S = 0 := by
    rw [DifferentialGeometry.Geometry.Riemannian.expand_orthonormal
      g (U q) hcard frame hframe S]
    simp only [hcoeff, zero_smul, Finset.sum_const_zero]
  refine ⟨hmean, ?_⟩
  exact normal_jacobi_coefficient_eq_scalar_gauss_of_zero_mean_curvature_complex
    D g finrank_euclideanSpace_fin U hUD hiD q (ν q) (hunit q) (hnormal q) b hb hmean

end DifferentialGeometry.Geometry.MinimalSurface

end

section

open Bundle Filter Manifold Set MeasureTheory DifferentialGeometry
open DifferentialGeometry.Geometry DifferentialGeometry.Topology
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff _root_.Topology BigOperators

local notation "D" => TopologicalSpace.Opens.mk (Metric.ball (0 : ℂ) 1) Metric.isOpen_ball

private local instance : MeasurableSpace D := borel D
private local instance : BorelSpace D := ⟨rfl⟩
private local instance : LocallyCompactSpace D :=
  (D : TopologicalSpace.Opens ℂ).isOpen.locallyCompactSpace
private local instance : SigmaCompactSpace D := by infer_instance

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]

namespace DifferentialGeometry.Geometry.MinimalSurface

private theorem original_disk_jacobi_stability_of_all_normal_flow_localMin
    (g : SmoothRiemannianMetric (𝓡 3) M)
    (u : C(closedDisk, M)) (U : ℂ → M)
    (hExt : SmoothDiskExtension (E := EuclideanSpace ℝ (Fin 3)) u U)
    (hImm : ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) (𝓡 3) U z))
    (ν : ∀ q : D, TangentSpace (𝓡 3) (U q))
    (hν : ContMDiff 𝓘(ℝ, ℂ) ((𝓡 3).tangent) ∞
      (fun q : D => (⟨U q, ν q⟩ : TangentBundle (𝓡 3) M)))
    (hunit : ∀ q : D, g.inner (U q) (ν q) (ν q) = 1)
    (hnormal : ∀ (q : D) (v : ℂ), g.inner (U q) (ν q)
      (mfderiv 𝓘(ℝ, ℂ) (𝓡 3) (fun p : D => U p) q v) = 0)
    (hflows : ∀ (φ : D → ℝ),
      ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) ∞ φ → HasCompactSupport φ →
      ∃ (X : ∀ x : M, TangentSpace (𝓡 3) x)
        (hX : ContMDiff (𝓡 3) ((𝓡 3).prod (𝓡 3)) ∞
          (fun x : M => (⟨x, X x⟩ : TangentBundle (𝓡 3) M)))
        (hXc : HasCompactSupport X),
        (∀ q : D,
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 3)
            (fun t => Diffeomorph.compactSupportFlow X hX hXc t (U q)) 0 (1 : ℝ) : EuclideanSpace ℝ (Fin 3)) =
              φ q • ν q) ∧
        IsLocalMin (fun t => riemannianDiskArea g
          ((⟨Diffeomorph.compactSupportFlow X hX hXc t,
            (Diffeomorph.compactSupportFlow X hX hXc t).contMDiff.continuous⟩ : C(M, M)).comp u)) 0) :
    ∃ (hUD : ContMDiff 𝓘(ℝ, ℂ) (𝓡 3) ∞ (fun q : D => U q))
      (hiD : ∀ q : D, Function.Injective
        (mfderiv 𝓘(ℝ, ℂ) (𝓡 3) (fun p : D => U p) q)),
    let gD := g.pullback (fun q : D => U q) hUD hiD
    let μ := riemannianVolumeMeasure (I := 𝓘(ℝ, ℂ)) (M := D) gD
    (∀ (q : D) (b : Module.Basis (Fin 2) ℝ (TangentSpace 𝓘(ℝ, ℂ) q)),
      (∀ i j, gD.inner q (b i) (b j) = if i = j then 1 else 0) →
        ∑ i : Fin 2, secondFundamentalFormAmbientAt gD g
          (fun p : D => U p) q (b i) (b i) = 0) ∧
    let W : D → ℝ := fun q => scalarCurv gD q / 2 - scalarCurv g (U q) / 2
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) ∞ W ∧
    ∀ (φ : D → ℝ), ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) ∞ φ → HasCompactSupport φ →
      let Q : D → ℝ := fun q =>
        gD.inner q (gradFun gD φ q) (gradFun gD φ q) + W q * φ q ^ 2
      Integrable Q μ ∧ (0 ≤ ∫ q : D, Q q ∂μ) ∧
      ∃ (X : ∀ x : M, TangentSpace (𝓡 3) x)
        (hX : ContMDiff (𝓡 3) ((𝓡 3).prod (𝓡 3)) ∞
          (fun x : M => (⟨x, X x⟩ : TangentBundle (𝓡 3) M)))
        (hXc : HasCompactSupport X),
        (∀ q : D,
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 3)
            (fun t => Diffeomorph.compactSupportFlow X hX hXc t (U q)) 0 (1 : ℝ) :
              EuclideanSpace ℝ (Fin 3)) = φ q • ν q) ∧
      let L : ℝ → ℝ := fun t => riemannianDiskArea g
        ((⟨Diffeomorph.compactSupportFlow X hX hXc t,
          (Diffeomorph.compactSupportFlow X hX hXc t).contMDiff.continuous⟩ : C(M, M)).comp u)
      IsLocalMin L 0 ∧ HasDerivAt L 0 0 ∧
      ∀ (b : ∀ q : D, Module.Basis (Fin 2) ℝ (TangentSpace 𝓘(ℝ, ℂ) q)),
        (∀ (q : D) (i j : Fin 2),
          gD.inner q (b q i) (b q j) = if i = j then 1 else 0) →
      let J : D → ℝ := fun q =>
        let II := secondFundamentalFormAmbientAt gD g (fun p : D => U p) q
        gD.inner q (gradFun gD φ q) (gradFun gD φ q) +
          (metricScalarAt gD q / 2 -
            (metricScalarAt g (U q) +
              ∑ i : Fin 2, ∑ j : Fin 2,
                g.inner (U q) (II (b q i) (b q j)) (II (b q i) (b q j))) / 2) * φ q ^ 2
      Integrable J μ ∧ HasDerivAt (deriv L) (∫ q : D, J q ∂μ) 0 ∧
        (0 ≤ ∫ q : D, J q ∂μ) := by
  classical
  obtain ⟨hUD, hiD, hstationary⟩ :=
    original_disk_zero_mean_curvature_and_jacobi_potential_of_all_normal_flow_localMin
      g u U hExt hImm ν hν.continuous hunit hnormal hflows
  let gD := g.pullback (fun q : D => U q) hUD hiD
  let μ := riemannianVolumeMeasure (I := 𝓘(ℝ, ℂ)) (M := D) gD
  have hmean : ∀ (q : D) (b : Module.Basis (Fin 2) ℝ (TangentSpace 𝓘(ℝ, ℂ) q)),
      (∀ i j, gD.inner q (b i) (b j) = if i = j then 1 else 0) →
      (∑ i : Fin 2, secondFundamentalFormAmbientAt gD g
        (fun p : D => U p) q (b i) (b i)) = 0 := by
    intro q b hb
    exact (hstationary q b hb).1
  refine ⟨hUD, hiD, hmean, ?_⟩
  let W : D → ℝ := fun q => scalarCurv gD q / 2 - scalarCurv g (U q) / 2
  have hW : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) ∞ W :=
    ((scalarCurv_contMDiff gD).div_const 2).sub
      (((scalarCurv_contMDiff g).comp hUD).div_const 2)
  refine ⟨hW, ?_⟩
  intro φ hφ hφc
  let Q : D → ℝ := fun q =>
    gD.inner q (gradFun gD φ q) (gradFun gD φ q) + W q * φ q ^ 2
  have hQc : Continuous Q :=
    (normGradSqFun_continuous gD hφ).add (hW.continuous.mul (hφ.continuous.pow 2))
  have hQcs : HasCompactSupport Q := by
    apply hφc.of_isClosed_subset (isClosed_tsupport _)
    apply closure_minimal ?_ (isClosed_tsupport φ)
    intro q hq
    by_contra hnot
    have hφq : φ q = 0 := by
      by_contra hne
      exact hnot (subset_tsupport φ hne)
    have hgrad : gradFun gD φ q = 0 := by
      by_contra hne
      exact hnot (support_gradFun_subset gD φ hne)
    apply hq
    change gD.inner q (gradFun gD φ q) (gradFun gD φ q) + W q * φ q ^ 2 = 0
    rw [hgrad, hφq, map_zero,
      zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero]
  have hQint : Integrable Q μ :=
    DifferentialGeometry.Integral.DivergenceTheorem.Continuous.integrable_of_hasCompactSupport_riemannianVolumeMeasure
      gD hQc hQcs
  obtain ⟨X, hX, hXc, hvelocity, hmin⟩ := hflows φ hφ hφc
  let L : ℝ → ℝ := fun t => riemannianDiskArea g
    ((⟨Diffeomorph.compactSupportFlow X hX hXc t,
      (Diffeomorph.compactSupportFlow X hX hXc t).contMDiff.continuous⟩ : C(M, M)).comp u)
  let J (b : ∀ q : D, Module.Basis (Fin 2) ℝ (TangentSpace 𝓘(ℝ, ℂ) q)) : D → ℝ := fun q =>
    let II := secondFundamentalFormAmbientAt gD g (fun p : D => U p) q
    gD.inner q (gradFun gD φ q) (gradFun gD φ q) +
      (metricScalarAt gD q / 2 -
        (metricScalarAt g (U q) +
          ∑ i : Fin 2, ∑ j : Fin 2,
            g.inner (U q) (II (b q i) (b q j)) (II (b q i) (b q j))) / 2) * φ q ^ 2
  have hvariation
      (b : ∀ q : D, Module.Basis (Fin 2) ℝ (TangentSpace 𝓘(ℝ, ℂ) q))
      (hb : ∀ (q : D) (i j : Fin 2),
        gD.inner q (b q i) (b q j) = if i = j then 1 else 0) :
      Integrable (J b) μ ∧ HasDerivAt L 0 0 ∧
        HasDerivAt (deriv L) (∫ q : D, J b q ∂μ) 0 :=
    SmoothDiskExtension.hasDerivAt_deriv_diskArea_normal_compactSupportFlow
      g u U hExt hImm hUD hiD ν hν hunit hnormal hmean φ hφ hφc X hX hXc hvelocity b hb
  have hnonneg
      (b : ∀ q : D, Module.Basis (Fin 2) ℝ (TangentSpace 𝓘(ℝ, ℂ) q))
      (hb : ∀ (q : D) (i j : Fin 2),
        gD.inner q (b q i) (b q j) = if i = j then 1 else 0) :
      0 ≤ ∫ q : D, J b q ∂μ := by
    rw [← (hvariation b hb).2.2.deriv]
    exact DifferentialGeometry.Analysis.second_deriv_nonneg_of_isLocalMin
      hmin (hvariation b hb).2.1.continuousAt
  have hex (q : D) :
      ∃ b : Module.Basis (Fin 2) ℝ (TangentSpace 𝓘(ℝ, ℂ) q),
        ∀ i j, gD.inner q (b i) (b j) = if i = j then 1 else 0 := by
    obtain ⟨b, hb⟩ := DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis gD q
    have hdim : Module.finrank ℝ (TangentSpace 𝓘(ℝ, ℂ) q) = 2 := by
      change Module.finrank ℝ ℂ = 2
      rw [Module.finrank_eq_card_basis Complex.basisOneI, Fintype.card_fin]
    let e := finCongr hdim
    refine ⟨b.reindex e, ?_⟩
    intro i j
    rw [Module.Basis.reindex_apply, Module.Basis.reindex_apply, hb]
    simp only [Equiv.apply_eq_iff_eq]
  let b₀ : ∀ q : D, Module.Basis (Fin 2) ℝ (TangentSpace 𝓘(ℝ, ℂ) q) :=
    fun q => (hex q).choose
  have hb₀ : ∀ (q : D) (i j : Fin 2),
      gD.inner q (b₀ q i) (b₀ q j) = if i = j then 1 else 0 :=
    fun q => (hex q).choose_spec
  have hJle (q : D) : J b₀ q ≤ Q q := by
    let II := secondFundamentalFormAmbientAt gD g (fun p : D => U p) q
    let S : ℝ := ∑ i : Fin 2, ∑ j : Fin 2,
      g.inner (U q) (II (b₀ q i) (b₀ q j)) (II (b₀ q i) (b₀ q j))
    have hS : 0 ≤ S := by
      apply Finset.sum_nonneg
      intro i _
      apply Finset.sum_nonneg
      intro j _
      by_cases hz : II (b₀ q i) (b₀ q j) = 0
      · simpa only [hz, map_zero, zero_apply] using (le_rfl : (0 : ℝ) ≤ 0)
      · exact le_of_lt (g.pos (U q) _ hz)
    change gD.inner q (gradFun gD φ q) (gradFun gD φ q) +
        (metricScalarAt gD q / 2 - (metricScalarAt g (U q) + S) / 2) * φ q ^ 2 ≤
      gD.inner q (gradFun gD φ q) (gradFun gD φ q) +
        (scalarCurv gD q / 2 - scalarCurv g (U q) / 2) * φ q ^ 2
    rw [metricScalar_eq_scal, metricScalar_eq_scal]
    have hcoefficient : scalarCurv gD q / 2 - (scalarCurv g (U q) + S) / 2 ≤
        scalarCurv gD q / 2 - scalarCurv g (U q) / 2 := by
      linarith only [hS]
    exact _root_.add_le_add
      (le_refl (gD.inner q (gradFun gD φ q) (gradFun gD φ q)))
      (mul_le_mul_of_nonneg_right hcoefficient (sq_nonneg (φ q)))
  have hQnonneg : 0 ≤ ∫ q : D, Q q ∂μ :=
    le_trans (hnonneg b₀ hb₀) (integral_mono (hvariation b₀ hb₀).1 hQint hJle)
  refine ⟨hQint, hQnonneg, X, hX, hXc, hvelocity, hmin, (hvariation b₀ hb₀).2.1, ?_⟩
  intro b hb
  exact ⟨(hvariation b hb).1, (hvariation b hb).2.2, hnonneg b hb⟩

end DifferentialGeometry.Geometry.MinimalSurface

end

section

open Bundle Filter Manifold Set MeasureTheory DifferentialGeometry
open DifferentialGeometry.Geometry DifferentialGeometry.Topology
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.MinimalSurface
open scoped Manifold ContDiff _root_.Topology BigOperators

local notation "D" => TopologicalSpace.Opens.mk (Metric.ball (0 : ℂ) 1) Metric.isOpen_ball

private local instance : MeasurableSpace D := borel D
private local instance : BorelSpace D := ⟨rfl⟩
private local instance : LocallyCompactSpace D :=
  (D : TopologicalSpace.Opens ℂ).isOpen.locallyCompactSpace
private local instance : SigmaCompactSpace D := by infer_instance

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]

namespace DifferentialGeometry.Geometry.MinimalSurface

/-- Every disk attaining the literal exterior disk infimum is two-sided and minimal,
and satisfies the original induced-metric Jacobi inequality for every compactly
supported smooth normal test, realized by an admissible ambient flow of that disk. -/
theorem every_area_attaining_exterior_disk_jacobi_form
    (g : SmoothRiemannianMetric (𝓡 3) M) (W : Set M) (γ : freeLoop M) :
    ∀ (u : C(closedDisk, M)), isExteriorSpanningDisk W γ u →
      riemannianDiskArea g u = leastExteriorDiskArea g W γ →
    ∃ (U : ℂ → M), SmoothDiskExtension (E := EuclideanSpace ℝ (Fin 3)) u U ∧
      (∀ z ∈ Metric.closedBall (0 : ℂ) 1,
        Function.Injective (mfderiv 𝓘(ℝ, ℂ) (𝓡 3) U z)) ∧
    ∃ (ν : ∀ q : D, TangentSpace (𝓡 3) (U q)),
      ContMDiff 𝓘(ℝ, ℂ) ((𝓡 3).tangent) ∞
        (fun q : D => (⟨U q, ν q⟩ : TangentBundle (𝓡 3) M)) ∧
      (∀ q : D, g.inner (U q) (ν q) (ν q) = 1) ∧
      (∀ (q : D) (a : ℂ), g.inner (U q) (ν q)
        (mfderiv 𝓘(ℝ, ℂ) (𝓡 3) (fun p : D => U p) q a) = 0) ∧
    ∃ (hUD : ContMDiff 𝓘(ℝ, ℂ) (𝓡 3) ∞ (fun q : D => U q))
      (hiD : ∀ q : D, Function.Injective
        (mfderiv 𝓘(ℝ, ℂ) (𝓡 3) (fun p : D => U p) q)),
    let gD := g.pullback (fun q : D => U q) hUD hiD
    let μ := riemannianVolumeMeasure (I := 𝓘(ℝ, ℂ)) (M := D) gD
    (∀ (q : D) (b : Module.Basis (Fin 2) ℝ (TangentSpace 𝓘(ℝ, ℂ) q)),
      (∀ i j, gD.inner q (b i) (b j) = if i = j then 1 else 0) →
        ∑ i : Fin 2, secondFundamentalFormAmbientAt gD g
          (fun p : D => U p) q (b i) (b i) = 0) ∧
    let V : D → ℝ := fun q => scalarCurv gD q / 2 - scalarCurv g (U q) / 2
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) ∞ V ∧
    ∀ (φ : D → ℝ), ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) ∞ φ → HasCompactSupport φ →
      let Q : D → ℝ := fun q =>
        gD.inner q (gradFun gD φ q) (gradFun gD φ q) + V q * φ q ^ 2
      Integrable Q μ ∧ (0 ≤ ∫ q : D, Q q ∂μ) ∧
      ∃ (X : ∀ x : M, TangentSpace (𝓡 3) x)
        (hX : ContMDiff (𝓡 3) ((𝓡 3).tangent) ∞
          (fun x : M => (⟨x, X x⟩ : TangentBundle (𝓡 3) M)))
        (hXc : HasCompactSupport X),
        tsupport X ⊆ interior W ∧
      let Φ := Diffeomorph.compactSupportFlow X hX hXc
      let v : ℝ → C(closedDisk, M) := fun t =>
        (⟨Φ t, (Φ t).continuous⟩ : C(M, M)).comp u
      let L : ℝ → ℝ := fun t => riemannianDiskArea g (v t)
      ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 3) ∞
        (fun p : ℝ × M => Φ p.1 p.2) ∧
      Φ 0 = Diffeomorph.refl (𝓡 3) M ∞ ∧
      (∀ q : D, HasMFDerivAt 𝓘(ℝ, ℝ) (𝓡 3)
        (fun t => Φ t (u ⟨q, Metric.ball_subset_closedBall q.property⟩)) 0
        ((1 : ℝ →L[ℝ] ℝ).smulRight (φ q • ν q))) ∧
      (∀ q : D,
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (fun t => Φ t (U q)) 0 (1 : ℝ) :
          EuclideanSpace ℝ (Fin 3)) = φ q • ν q) ∧
      (∀ t : ℝ, isExteriorSpanningDisk W γ (v t)) ∧
      IsLocalMin L 0 ∧ HasDerivAt L 0 0 ∧
      ∀ (b : ∀ q : D, Module.Basis (Fin 2) ℝ (TangentSpace 𝓘(ℝ, ℂ) q)),
        (∀ (q : D) (i j : Fin 2),
          gD.inner q (b q i) (b q j) = if i = j then 1 else 0) →
      let J : D → ℝ := fun q =>
        let II := secondFundamentalFormAmbientAt gD g (fun p : D => U p) q
        gD.inner q (gradFun gD φ q) (gradFun gD φ q) +
          (metricScalarAt gD q / 2 -
            (metricScalarAt g (U q) +
              ∑ i : Fin 2, ∑ j : Fin 2,
                g.inner (U q) (II (b q i) (b q j)) (II (b q i) (b q j))) / 2) * φ q ^ 2
      Integrable J μ ∧ HasDerivAt (deriv L) (∫ q : D, J q ∂μ) 0 ∧
        (0 ≤ ∫ q : D, J q ∂μ) := by
  classical
  intro u hu harea
  obtain ⟨U, hExt, hImm, ν, hν, hunit, hnormal, hparentFlows⟩ :=
    exists_normal_test_flows_of_attains_leastExteriorDiskArea g hu harea
  have hvelocity_of_parent
      (φ : D → ℝ) (X : ∀ x : M, TangentSpace (𝓡 3) x)
      (hX : ContMDiff (𝓡 3) ((𝓡 3).tangent) ∞
        (fun x : M => (⟨x, X x⟩ : TangentBundle (𝓡 3) M)))
      (hXc : HasCompactSupport X)
      (hderiv : ∀ q : D, HasMFDerivAt 𝓘(ℝ, ℝ) (𝓡 3)
        (fun t => Diffeomorph.compactSupportFlow X hX hXc t
          (u ⟨q, Metric.ball_subset_closedBall q.property⟩)) 0
        ((1 : ℝ →L[ℝ] ℝ).smulRight (φ q • ν q))) :
      ∀ q : D,
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 3)
          (fun t => Diffeomorph.compactSupportFlow X hX hXc t (U q)) 0 (1 : ℝ) :
            EuclideanSpace ℝ (Fin 3)) = φ q • ν q := by
    intro q
    let zK : closedDisk := ⟨q, Metric.ball_subset_closedBall q.property⟩
    have hcurve :
        (fun t => Diffeomorph.compactSupportFlow X hX hXc t (U q)) =
        (fun t => Diffeomorph.compactSupportFlow X hX hXc t (u zK)) := by
      funext t
      exact congrArg (Diffeomorph.compactSupportFlow X hX hXc t) (hExt.1 zK)
    change @Eq (EuclideanSpace ℝ (Fin 3))
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 3)
        (fun t => Diffeomorph.compactSupportFlow X hX hXc t (U q)) 0 (1 : ℝ))
      (φ q • ν q)
    have hv : @Eq (EuclideanSpace ℝ (Fin 3))
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 3)
          (fun t => Diffeomorph.compactSupportFlow X hX hXc t (u zK)) 0 (1 : ℝ))
        ((1 : ℝ) • (φ q • ν q)) := by
      exact congrArg (fun K : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 3) => K (1 : ℝ))
        (hderiv q).mfderiv
    have heval : @Eq (EuclideanSpace ℝ (Fin 3))
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 3)
          (fun t => Diffeomorph.compactSupportFlow X hX hXc t (U q)) 0 (1 : ℝ))
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 3)
          (fun t => Diffeomorph.compactSupportFlow X hX hXc t (u zK)) 0 (1 : ℝ)) :=
      congrArg (fun curve : ℝ → M =>
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) curve 0 (1 : ℝ) : EuclideanSpace ℝ (Fin 3))) hcurve
    have hv_one : @Eq (EuclideanSpace ℝ (Fin 3))
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 3)
          (fun t => Diffeomorph.compactSupportFlow X hX hXc t (u zK)) 0 (1 : ℝ))
        (φ q • ν q) := by
      simpa only [one_smul] using hv
    exact @Eq.trans (EuclideanSpace ℝ (Fin 3)) _ _ _ heval hv_one
  have hflows : ∀ (φ : D → ℝ),
      ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) ∞ φ → HasCompactSupport φ →
      ∃ (X : ∀ x : M, TangentSpace (𝓡 3) x)
        (hX : ContMDiff (𝓡 3) ((𝓡 3).prod (𝓡 3)) ∞
          (fun x : M => (⟨x, X x⟩ : TangentBundle (𝓡 3) M)))
        (hXc : HasCompactSupport X),
        (∀ q : D,
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 3)
            (fun t => Diffeomorph.compactSupportFlow X hX hXc t (U q)) 0 (1 : ℝ) :
              EuclideanSpace ℝ (Fin 3)) = φ q • ν q) ∧
        IsLocalMin (fun t => riemannianDiskArea g
          ((⟨Diffeomorph.compactSupportFlow X hX hXc t,
            (Diffeomorph.compactSupportFlow X hX hXc t).contMDiff.continuous⟩ :
              C(M, M)).comp u)) 0 := by
    intro φ hφ hφc
    obtain ⟨X, hX, hXc, _, _, _, hderiv, _, hmin⟩ := hparentFlows φ hφ hφc
    exact ⟨X, hX, hXc, hvelocity_of_parent φ X hX hXc hderiv, hmin⟩
  obtain ⟨hUD, hiD, hmean, hV, hscalar⟩ :=
    original_disk_jacobi_stability_of_all_normal_flow_localMin
      g u U hExt hImm ν hν hunit hnormal hflows
  let gD := g.pullback (fun q : D => U q) hUD hiD
  let μ := riemannianVolumeMeasure (I := 𝓘(ℝ, ℂ)) (M := D) gD
  have hex (q : D) :
      ∃ b : Module.Basis (Fin 2) ℝ (TangentSpace 𝓘(ℝ, ℂ) q),
        ∀ i j, gD.inner q (b i) (b j) = if i = j then 1 else 0 := by
    obtain ⟨b, hb⟩ := DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis gD q
    have hdim : Module.finrank ℝ (TangentSpace 𝓘(ℝ, ℂ) q) = 2 := by
      change Module.finrank ℝ ℂ = 2
      rw [Module.finrank_eq_card_basis Complex.basisOneI, Fintype.card_fin]
    let e := finCongr hdim
    refine ⟨b.reindex e, ?_⟩
    intro i j
    rw [Module.Basis.reindex_apply, Module.Basis.reindex_apply, hb]
    simp only [Equiv.apply_eq_iff_eq]
  let b₀ : ∀ q : D, Module.Basis (Fin 2) ℝ (TangentSpace 𝓘(ℝ, ℂ) q) :=
    fun q => (hex q).choose
  have hb₀ : ∀ (q : D) (i j : Fin 2),
      gD.inner q (b₀ q i) (b₀ q j) = if i = j then 1 else 0 :=
    fun q => (hex q).choose_spec
  refine ⟨U, hExt, hImm, ν, hν, hunit, hnormal, hUD, hiD, hmean, hV, ?_⟩
  intro φ hφ hφc
  have hQ := hscalar φ hφ hφc
  refine ⟨hQ.1, hQ.2.1, ?_⟩
  obtain ⟨X, hX, hXc, hsupport, hjoint, hzero, hderiv, hadmissible, hmin⟩ :=
    hparentFlows φ hφ hφc
  have hvelocity := hvelocity_of_parent φ X hX hXc hderiv
  let Φ := Diffeomorph.compactSupportFlow X hX hXc
  let L : ℝ → ℝ := fun t => riemannianDiskArea g
    ((⟨Φ t, (Φ t).continuous⟩ : C(M, M)).comp u)
  let J (b : ∀ q : D, Module.Basis (Fin 2) ℝ (TangentSpace 𝓘(ℝ, ℂ) q)) : D → ℝ := fun q =>
    let II := secondFundamentalFormAmbientAt gD g (fun p : D => U p) q
    gD.inner q (gradFun gD φ q) (gradFun gD φ q) +
      (metricScalarAt gD q / 2 -
        (metricScalarAt g (U q) +
          ∑ i : Fin 2, ∑ j : Fin 2,
            g.inner (U q) (II (b q i) (b q j)) (II (b q i) (b q j))) / 2) * φ q ^ 2
  have hvariation
      (b : ∀ q : D, Module.Basis (Fin 2) ℝ (TangentSpace 𝓘(ℝ, ℂ) q))
      (hb : ∀ (q : D) (i j : Fin 2),
        gD.inner q (b q i) (b q j) = if i = j then 1 else 0) :
      Integrable (J b) μ ∧ HasDerivAt L 0 0 ∧
        HasDerivAt (deriv L) (∫ q : D, J b q ∂μ) 0 :=
    SmoothDiskExtension.hasDerivAt_deriv_diskArea_normal_compactSupportFlow
      g u U hExt hImm hUD hiD ν hν hunit hnormal hmean φ hφ hφc X hX hXc hvelocity b hb
  refine ⟨X, hX, hXc, hsupport, hjoint, hzero, hderiv, hvelocity, hadmissible,
    hmin, (hvariation b₀ hb₀).2.1, ?_⟩
  intro b hb
  have hv := hvariation b hb
  refine ⟨hv.1, hv.2.2, ?_⟩
  rw [← hv.2.2.deriv]
  exact DifferentialGeometry.Analysis.second_deriv_nonneg_of_isLocalMin
    hmin hv.2.1.continuousAt

end DifferentialGeometry.Geometry.MinimalSurface

end

section

open Bundle Filter Manifold Set MeasureTheory DifferentialGeometry
open DifferentialGeometry.Geometry DifferentialGeometry.Topology
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.MinimalSurface
open scoped Manifold ContDiff _root_.Topology BigOperators

local notation "D" => TopologicalSpace.Opens.mk (Metric.ball (0 : ℂ) 1) Metric.isOpen_ball

private local instance : MeasurableSpace D := borel D
private local instance : BorelSpace D := ⟨rfl⟩
private local instance : LocallyCompactSpace D :=
  (D : TopologicalSpace.Opens ℂ).isOpen.locallyCompactSpace
private local instance : SigmaCompactSpace D := by infer_instance

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]

namespace DifferentialGeometry.Geometry.MinimalSurface

/-- Every exterior area attainer has a smooth global unit normal, zero mean
curvature, and a smooth full Jacobi potential for its original induced metric.
Its Jacobi quadratic form is nonnegative on every compactly supported smooth test. -/
theorem every_area_attaining_exterior_disk_smooth_full_jacobi_potential
    (g : SmoothRiemannianMetric (𝓡 3) M) (W : Set M) (γ : freeLoop M) :
    ∀ (u : C(closedDisk, M)), isExteriorSpanningDisk W γ u →
      riemannianDiskArea g u = leastExteriorDiskArea g W γ →
    ∃ (U : ℂ → M), SmoothDiskExtension (E := EuclideanSpace ℝ (Fin 3)) u U ∧
      (∀ z ∈ Metric.closedBall (0 : ℂ) 1,
        Function.Injective (mfderiv 𝓘(ℝ, ℂ) (𝓡 3) U z)) ∧
    ∃ (ν : ∀ q : D, TangentSpace (𝓡 3) (U q)),
      ContMDiff 𝓘(ℝ, ℂ) ((𝓡 3).tangent) ∞
        (fun q : D => (⟨U q, ν q⟩ : TangentBundle (𝓡 3) M)) ∧
      (∀ q : D, g.inner (U q) (ν q) (ν q) = 1) ∧
      (∀ (q : D) (a : ℂ), g.inner (U q) (ν q)
        (mfderiv 𝓘(ℝ, ℂ) (𝓡 3) (fun p : D => U p) q a) = 0) ∧
    ∃ (hUD : ContMDiff 𝓘(ℝ, ℂ) (𝓡 3) ∞ (fun q : D => U q))
      (hiD : ∀ q : D, Function.Injective
        (mfderiv 𝓘(ℝ, ℂ) (𝓡 3) (fun p : D => U p) q)),
    let gD := g.pullback (fun q : D => U q) hUD hiD
    let μ := riemannianVolumeMeasure (I := 𝓘(ℝ, ℂ)) (M := D) gD
    (∀ (q : D) (b : Module.Basis (Fin 2) ℝ (TangentSpace 𝓘(ℝ, ℂ) q)),
      (∀ i j, gD.inner q (b i) (b j) = if i = j then 1 else 0) →
        ∑ i : Fin 2, secondFundamentalFormAmbientAt gD g
          (fun p : D => U p) q (b i) (b i) = 0) ∧
    ∃ VJ : C^∞⟮𝓘(ℝ, ℂ), D; ℝ⟯,
      (∀ q : D, VJ q = scalarCurv gD q - scalarCurv g (U q) +
        ricciTensor g (U q) (ν q) (ν q)) ∧
      (∀ (q : D) (b : Module.Basis (Fin 2) ℝ (TangentSpace 𝓘(ℝ, ℂ) q)),
        (∀ i j, gD.inner q (b i) (b j) = if i = j then 1 else 0) →
        let II := secondFundamentalFormAmbientAt gD g (fun p : D => U p) q
        VJ q = metricScalarAt gD q / 2 -
          (metricScalarAt g (U q) +
            ∑ i : Fin 2, ∑ j : Fin 2,
              g.inner (U q) (II (b i) (b j)) (II (b i) (b j))) / 2) ∧
      (∀ q : D, VJ q ≤ scalarCurv gD q / 2 - scalarCurv g (U q) / 2) ∧
      (∀ (φ : D → ℝ), ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) ∞ φ → HasCompactSupport φ →
        let QJ : D → ℝ := fun q =>
          gD.inner q (gradFun gD φ q) (gradFun gD φ q) + VJ q * φ q ^ 2
        Integrable QJ μ ∧ 0 ≤ ∫ q : D, QJ q ∂μ) := by
  classical
  intro u hu harea
  obtain ⟨U, hExt, hImm, ν, hν, hunit, hnormal, hUD, hiD, hmean, _, hfull⟩ :=
    every_area_attaining_exterior_disk_jacobi_form g W γ u hu harea
  let gD := g.pullback (fun q : D => U q) hUD hiD
  let μ := riemannianVolumeMeasure (I := 𝓘(ℝ, ℂ)) (M := D) gD
  obtain ⟨VJ, hformula, hcoeff, hbound⟩ :=
    exists_smooth_full_jacobi_potential_of_zero_mean_curvature_complex
      D g (by simp) U hUD hiD ν hν hunit hnormal hmean
  have hex (q : D) :
      ∃ b : Module.Basis (Fin 2) ℝ (TangentSpace 𝓘(ℝ, ℂ) q),
        ∀ i j, gD.inner q (b i) (b j) = if i = j then 1 else 0 := by
    obtain ⟨b, hb⟩ := DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis gD q
    have hdim : Module.finrank ℝ (TangentSpace 𝓘(ℝ, ℂ) q) = 2 := by
      change Module.finrank ℝ ℂ = 2
      rw [Module.finrank_eq_card_basis Complex.basisOneI, Fintype.card_fin]
    let e := finCongr hdim
    refine ⟨b.reindex e, ?_⟩
    intro i j
    rw [Module.Basis.reindex_apply, Module.Basis.reindex_apply, hb]
    simp only [Equiv.apply_eq_iff_eq]
  let b₀ : ∀ q : D, Module.Basis (Fin 2) ℝ (TangentSpace 𝓘(ℝ, ℂ) q) :=
    fun q => (hex q).choose
  have hb₀ : ∀ (q : D) (i j : Fin 2),
      gD.inner q (b₀ q i) (b₀ q j) = if i = j then 1 else 0 :=
    fun q => (hex q).choose_spec
  refine ⟨U, hExt, hImm, ν, hν, hunit, hnormal, hUD, hiD, hmean,
    VJ, hformula, hcoeff, hbound, ?_⟩
  intro φ hφ hφc
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hJ⟩ := (hfull φ hφ hφc).2.2
  let J : D → ℝ := fun q =>
    let II := secondFundamentalFormAmbientAt gD g (fun p : D => U p) q
    gD.inner q (gradFun gD φ q) (gradFun gD φ q) +
      (metricScalarAt gD q / 2 -
        (metricScalarAt g (U q) +
          ∑ i : Fin 2, ∑ j : Fin 2,
            g.inner (U q) (II (b₀ q i) (b₀ q j)) (II (b₀ q i) (b₀ q j))) / 2) * φ q ^ 2
  have hv := hJ b₀ hb₀
  have heq : (fun q : D =>
      gD.inner q (gradFun gD φ q) (gradFun gD φ q) + VJ q * φ q ^ 2) = J := by
    funext q
    exact congrArg (fun c : ℝ =>
      gD.inner q (gradFun gD φ q) (gradFun gD φ q) + c * φ q ^ 2)
      (hcoeff q (b₀ q) (hb₀ q))
  change Integrable
    (fun q : D => gD.inner q (gradFun gD φ q) (gradFun gD φ q) + VJ q * φ q ^ 2) μ ∧
      0 ≤ ∫ q : D,
        (gD.inner q (gradFun gD φ q) (gradFun gD φ q) + VJ q * φ q ^ 2) ∂μ
  rw [heq]
  exact ⟨hv.1, hv.2.2⟩

end DifferentialGeometry.Geometry.MinimalSurface

end
