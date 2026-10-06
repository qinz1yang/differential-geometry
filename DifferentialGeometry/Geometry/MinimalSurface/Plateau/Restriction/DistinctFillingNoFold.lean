import DifferentialGeometry.Geometry.MinimalSurface.Plateau.ReplacementFold
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Restriction

set_option autoImplicit false
noncomputable section
open Set Filter Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Geometry DifferentialGeometry.Topology
open DifferentialGeometry.Geometry.ImmersedDiskDivergence.Within
open DifferentialGeometry.Geometry.ImmersedDiskDivergence.HalfDisk
open scoped Topology Manifold ContDiff NNReal ENNReal ComplexConjugate

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]

/-- The original and alternative actual Morrey disks yield equal patch area
by their two minimizations. A separate synchronized filling retains that area
and its literal local reparameterization to the alternative disk. Its actual
pasted seam has zero conormal sum in the same metric and exterior. -/
theorem IMS03Embeddedness.ConsumerAudit.actual_distinct_morrey_filling_has_no_regular_fold
    (U : TopologicalSpace.Opens M)
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) U} {γ : freeLoop U} {u : C(closedDisk, U)}
    (hu : IsMorreyDisk g γ u) (d qAlt : C(closedDisk, U)) {L C CAlt : ℝ≥0}
    (huLip : ∀ z w, riemannianEDistOf g (u z) (u w) ≤ (L : ℝ≥0∞) * edist z w)
    (hdLip : ∀ z w, riemannianEDistOf g (d z) (d w) ≤ (C : ℝ≥0∞) * edist z w)
    (e : PartialDiffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ℂ ℂ 1)
    (hsrc : Metric.closedBall (0 : ℂ) 1 ⊆ e.source)
    (hinside : e '' Metric.closedBall (0 : ℂ) 1 ⊆ Metric.ball (0 : ℂ) 1)
    (hboundary : ∀ z ∈ Metric.sphere (0 : ℂ) 1,
      diskExtension d z = diskExtension u (e z))
    (hqAlt : IsMorreyDisk g (diskTrace (diskThroughSourceChart u e hsrc)) qAlt)
    (hqAltLip : ∀ z w, riemannianEDistOf g (qAlt z) (qAlt w) ≤ (CAlt : ℝ≥0∞) * edist z w)
    (hSubSmooth : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞
      (fun t : ℝ => diskTrace (diskThroughSourceChart u e hsrc) (t : loopCircle)))
    (hSubImmersed : ∀ t : ℝ, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E)
      (fun s : ℝ => diskTrace (diskThroughSourceChart u e hsrc) (s : loopCircle)) t 1 ≠ 0)
    (hfillArea : riemannianDiskArea g d = riemannianDiskArea g qAlt)
    {W : Set U} (huW : Set.range u ⊆ W) (hdW : Set.range d ⊆ W)
    (χ : PartialDiffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ℂ ℂ ∞)
    (hχsrc : Metric.closedBall (0 : ℂ) 1 ⊆ χ.source)
    (hχinside : χ '' Metric.closedBall (0 : ℂ) 1 ⊆ Metric.ball (0 : ℂ) 1)
    {R : ℝ} (hR : 0 < R) (hRunit : R < 1)
    (hinner : MapsTo χ (closedHalfDisk 0 R) (e '' Metric.closedBall (0 : ℂ) 1))
    (houter : ∀ z ∈ closedHalfDisk 0 R,
      χ (conj z) ∉ interior (e '' Metric.closedBall (0 : ℂ) 1))
    (hFinner : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 1
      (diskExtension d ∘ e.symm ∘ χ) (closedHalfDisk 0 R))
    (hiInner : ∀ z ∈ closedHalfDisk 0 R, Function.Injective
      (mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension d ∘ e.symm ∘ χ)
        (closedHalfDisk 0 R) z))
    (hiOuter : ∀ z ∈ closedHalfDisk 0 R, Function.Injective
      (mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u ∘ χ ∘ conj)
        (closedHalfDisk 0 R) z))
    (ψAlt : ℂ → ℂ)
    (hψAlt : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ ψAlt (openHalfDisk 0 R))
    (hmapsAlt : MapsTo ψAlt (openHalfDisk 0 R) (Metric.ball (0 : ℂ) 1))
    (hbijAlt : ∀ z ∈ (openHalfDisk 0 R : Set ℂ), Function.Bijective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ψAlt z))
    (heqAlt : EqOn (diskExtension d ∘ e.symm ∘ χ)
      (diskExtension qAlt ∘ ψAlt) (openHalfDisk 0 R))
    (hpW : diskExtension d (e.symm (χ 0)) ∈ interior W) :
    riemannianDiskArea g d =
      riemannianArea g (diskExtension u) (e '' Metric.closedBall (0 : ℂ) 1) ∧
    inwardConormalWithin g (diskExtension d ∘ e.symm ∘ χ) (closedHalfDisk 0 R) 0 +
      tangentSpaceCast 𝓘(ℝ, E) ((diskExtension u ∘ χ ∘ conj) 0)
        ((diskExtension d ∘ e.symm ∘ χ) 0)
        (inwardConormalWithin g (diskExtension u ∘ χ ∘ conj) (closedHalfDisk 0 R) 0) = 0 := by
  obtain ⟨K, hrestrictionLip⟩ := diskThroughSourceChart_lipschitz g u huLip e le_rfl hsrc
  have hAltLe : riemannianDiskArea g qAlt ≤
      riemannianDiskArea g (diskThroughSourceChart u e hsrc) :=
    hqAlt.minimizesLipschitz _ (DiskWeakJordanTrace.of_diskTrace_eq rfl) ⟨K, hrestrictionLip⟩
  have hRestrictionLe : riemannianDiskArea g (diskThroughSourceChart u e hsrc) ≤
      riemannianDiskArea g qAlt :=
    hu.minimizesLipschitz_diskThroughSourceChart huLip e le_rfl hsrc hinside
      hSubSmooth hSubImmersed qAlt hqAlt.trace ⟨CAlt, hqAltLip⟩
  have hAltArea : riemannianDiskArea g qAlt =
      riemannianDiskArea g (diskThroughSourceChart u e hsrc) :=
    le_antisymm hAltLe hRestrictionLe
  have harea : riemannianDiskArea g d =
      riemannianArea g (diskExtension u) (e '' Metric.closedBall (0 : ℂ) 1) :=
    hfillArea.trans (hAltArea.trans
      (riemannianDiskArea_diskThroughSourceChart g u huLip e le_rfl hsrc))
  refine ⟨harea, ?_⟩
  exact hu.sourceChart_replacement_conormal_sum_eq_zero d qAlt huLip hdLip e hsrc hinside
    hboundary harea huW hdW χ hχsrc hχinside hR hRunit hinner houter hFinner hiInner hiOuter
    hqAlt.smoothInterior hqAlt.conformal hqAlt.harmonic ψAlt hψAlt hmapsAlt hbijAlt heqAlt hpW
