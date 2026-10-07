import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Cusps.HyperbolicTruncation
import DifferentialGeometry.Geometry.Hyperbolic.TruncationInterior

noncomputable section

open Set
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.CuspTruncation.FiniteCuspTruncation

open ProjectiveOrthogonalGroup (PO)
open Hyperbolic (HUpper)
open CuspCrossSections (endStabilizer)

variable {m : ℕ}

private local instance (Δ : Subgroup (PO (m + 1) 1)) : MulAction Δ (HUpper (m + 1)) :=
  EquivariantMap.subAction (Nat.le_add_left 1 m) Δ

private local instance (Δ : Subgroup (PO (m + 1) 1)) : ContinuousConstSMul Δ (HUpper (m + 1)) :=
  ⟨fun γ => (HyperbolicAction.contMDiff_po_smul m ∞ (γ : PO (m + 1) 1)).continuous⟩

private local instance (Δ : Subgroup (PO (m + 1) 1)) :
    ContMDiffConstSMul 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) ∞ Δ (HUpper (m + 1)) :=
  ⟨fun γ => HyperbolicAction.contMDiff_po_smul m ∞ (γ : PO (m + 1) 1)⟩

variable {Γ : Subgroup (PO (m + 1) 1)} [DiscreteTopology Γ]
  [IsCancelSMul Γ (HUpper (m + 1))] {r : ℝ}
  (D : FiniteCuspTruncation (Nat.le_add_left 1 m) Γ r) (ξ : D.centers)

local notation "hΓ" => (isDiscrete_iff_discreteTopology.mpr (inferInstance : DiscreteTopology Γ))
local notation "P" => endStabilizer (Nat.le_add_left 1 m) Γ (Set.singleton ξ.val)
local notation "QΓ" => MulAction.orbitRel.Quotient Γ (HUpper (m + 1))
local notation "πΓ" => Quotient.mk (MulAction.orbitRel Γ (HUpper (m + 1)))
local notation "πP" => Quotient.mk (MulAction.orbitRel P (HUpper (m + 1)))
local notation "S" => (πP '' Busemann.horosphere ξ.val (D.level ξ))
local notation "I" => 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1)))
local notation "K" => 𝓘(ℝ, Fin m → ℝ)
local notation "J" => ModelWithCorners.prod K 𝓘(ℝ, ℝ)

private local instance : ProperlyDiscontinuousSMul Γ (HUpper (m + 1)) :=
  OrbifoldCompactness.properlyDiscontinuous_subAction (Nat.le_add_left 1 m) Γ hΓ

private local instance : IsCancelSMul P (HUpper (m + 1)) :=
  EquivariantMap.isCancelSMul_subAction (Nat.le_add_left 1 m) (show P ≤ Γ from inf_le_left)

private local instance : ChartedSpace (Fin m → ℝ) S := D.horosphereQuotientChartedSpace hΓ ξ

private theorem exists_horoball_interior_chart :
    ∃ χ : PartialDiffeomorph I J
        QΓ (S × ℝ) ∞,
      χ.source = D.horoballCylinderMap hΓ ξ '' {p | 0 < p.2.val} ∧
      χ.target = {p | 0 < p.2} ∧
      ∀ p : S × Ici (0 : ℝ), 0 < p.2.val →
        χ (D.horoballCylinderMap hΓ ξ p) = (p.1, p.2.val) := by
  obtain ⟨A, hsource, heq, _⟩ := D.exists_partialDiffeomorph_horoballCylinderMap ξ
  let B := Topology.PartialDiffeomorph.restrict A {z | 0 < z.2}
    (isOpen_lt continuous_const continuous_snd)
  have hBs : B.source = {z | 0 < z.2} := by
    ext z
    change (z ∈ A.source ∧ 0 < z.2) ↔ 0 < z.2
    exact ⟨And.right, fun hz => ⟨hsource z.1 z.2 hz.le, hz⟩⟩
  have hBt : B.target = D.horoballCylinderMap hΓ ξ '' {p | 0 < p.2.val} := by
    ext y
    constructor
    · intro hy
      have hzmem := B.map_target' hy
      rw [hBs] at hzmem
      have hz : 0 < (B.symm y).2 := hzmem
      let p : S × Ici (0 : ℝ) := ((B.symm y).1, ⟨(B.symm y).2, hz.le⟩)
      refine ⟨p, hz, ?_⟩
      exact (heq p).trans (B.right_inv' hy)
    · rintro ⟨p, hp, rfl⟩
      rw [heq p]
      exact B.map_source' (hBs.symm ▸ hp)
  refine ⟨B.symm, hBt, hBs, ?_⟩
  intro p hp
  rw [heq p]
  exact B.left_inv' (hBs.symm ▸ hp)

omit ξ in
private theorem exists_diffeomorph_interior_retained_quotient
    (R : D.centers → ℝ) (hR : ∀ ξ, 0 < R ξ) :
    let U : TopologicalSpace.Opens QΓ :=
      ⟨interior (Topology.cylindricalCore (fun ξ => D.horoballCylinderMap hΓ ξ) R),
        isOpen_interior⟩
    ∃ f : Diffeomorph I I U QΓ ∞,
      (∀ x : U, x.val ∈ Topology.cylindricalCore
        (fun ξ => D.horoballCylinderMap hΓ ξ) (fun ξ => R ξ / 2) → f x = x.val) ∧
      ∀ y ∈ Topology.cylindricalCore
        (fun ξ => D.horoballCylinderMap hΓ ξ) (fun ξ => R ξ / 2), (f.symm y).val = y := by
  classical
  let C (ξ : D.centers) : Type :=
    (Quotient.mk (MulAction.orbitRel (endStabilizer (Nat.le_add_left 1 m) Γ {ξ.val})
      (HUpper (m + 1)))) '' Busemann.horosphere ξ.val (D.level ξ)
  let : Finite D.centers := D.finite_centers
  let : ∀ ξ : D.centers, ChartedSpace (Fin m → ℝ) (C ξ) := fun ξ =>
    D.horosphereQuotientChartedSpace hΓ ξ
  choose χ hχs hχt hχe using fun ξ => exists_horoball_interior_chart D ξ
  exact Topology.exists_diffeomorph_interior_cylindricalCore
    (fun ξ => D.horoballCylinderMap hΓ ξ)
    (D.horoballCylinderMap_isClosedEmbedding hΓ)
    (D.pairwise_disjoint_range_horoballCylinderMap hΓ) χ hχs hχt hχe R hR

omit ξ in
private theorem exists_diffeomorph_interior_retained_image
    {F G N : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace G] [TopologicalSpace N] [ChartedSpace G N]
    {L : ModelWithCorners ℝ F G} (e : QΓ ≃ₜ N)
    (he : IsLocalDiffeomorph I L ∞ (e ∘ πΓ))
    (R : D.centers → ℝ) (hR : ∀ ξ, 0 < R ξ) :
    let U : TopologicalSpace.Opens N :=
      ⟨interior (e '' Topology.cylindricalCore
        (fun ξ => D.horoballCylinderMap hΓ ξ) R), isOpen_interior⟩
    ∃ f : Diffeomorph L L U N ∞,
      (∀ x : U, x.val ∈ e '' Topology.cylindricalCore
        (fun ξ => D.horoballCylinderMap hΓ ξ) (fun ξ => R ξ / 2) → f x = x.val) ∧
      ∀ y ∈ e '' Topology.cylindricalCore
        (fun ξ => D.horoballCylinderMap hΓ ξ) (fun ξ => R ξ / 2), (f.symm y).val = y := by
  have hπ := MulAction.isLocalDiffeomorph_quotientMk_of_properlyDiscontinuousSMul
    (G := Γ) (M := HUpper (m + 1)) (n := ∞) I
  have he' : IsLocalDiffeomorph I L ∞ e := by
    intro q
    obtain ⟨p, rfl⟩ := Quotient.mk_surjective q
    exact DifferentialGeometry.isLocalDiffeomorphAt_of_comp (he p) (hπ p)
  let E := he'.diffeomorphOfBijective e.bijective
  let U : TopologicalSpace.Opens QΓ :=
    ⟨interior (Topology.cylindricalCore (fun ξ => D.horoballCylinderMap hΓ ξ) R),
      isOpen_interior⟩
  let restriction := DifferentialGeometry.PartialDiffeomorph.toOpensDiffeo
    E.toPartialDiffeomorph (U := U) (subset_univ _)
  let V : TopologicalSpace.Opens N :=
    ⟨(E : QΓ → N) '' (U : Set QΓ), DifferentialGeometry.image_opens_isOpen
      E.toPartialDiffeomorph (subset_univ _)⟩
  have hV : V = (⟨interior (e '' Topology.cylindricalCore
      (fun ξ => D.horoballCylinderMap hΓ ξ) R), isOpen_interior⟩ :
        TopologicalSpace.Opens N) := by
    apply SetLike.coe_injective
    exact e.image_interior _
  obtain ⟨ψ, hψ, hψi⟩ := exists_diffeomorph_interior_retained_quotient D R hR
  let f : Diffeomorph L L V N ∞ := restriction.symm.trans (ψ.trans E)
  have hretained (y : N)
      (hy : y ∈ e '' Topology.cylindricalCore
        (fun ξ => D.horoballCylinderMap hΓ ξ) (fun ξ => R ξ / 2)) :
      E.symm y ∈ Topology.cylindricalCore
        (fun ξ => D.horoballCylinderMap hΓ ξ) (fun ξ => R ξ / 2) := by
    obtain ⟨q, hq, rfl⟩ := hy
    change E.symm (E q) ∈ _
    simpa only [E.symm_apply_apply] using hq
  have hf (x : V)
      (hx : x.val ∈ e '' Topology.cylindricalCore
        (fun ξ => D.horoballCylinderMap hΓ ξ) (fun ξ => R ξ / 2)) : f x = x.val := by
    have hs : (restriction.symm x).val = E.symm x.val := rfl
    have hfix := hψ (restriction.symm x) (hs.symm ▸ hretained x hx)
    change E (ψ (restriction.symm x)) = x.val
    rw [hfix, hs, E.apply_symm_apply]
  have hfi (y : N)
      (hy : y ∈ e '' Topology.cylindricalCore
        (fun ξ => D.horoballCylinderMap hΓ ξ) (fun ξ => R ξ / 2)) : (f.symm y).val = y := by
    change E ((ψ.symm (E.symm y)).val) = y
    rw [hψi (E.symm y) (hretained y hy), E.apply_symm_apply]
  dsimp only
  rw [← hV]
  exact ⟨f, hf, hfi⟩


end DifferentialGeometry.CuspTruncation.FiniteCuspTruncation

namespace DifferentialGeometry.CuspTruncation.FiniteCuspTruncation

open ProjectiveOrthogonalGroup (PO)
open Hyperbolic (HUpper)
open CuspCrossSections (endStabilizer)
open Horospherical (Horizontal)
open HorosphereProjection (quotientHorosphereCoordinates)
open Geometry.Hyperbolic
open GC.Endpoint

private local instance {m : ℕ} (Δ : Subgroup (PO (m + 1) 1)) :
    MulAction Δ (HUpper (m + 1)) :=
  EquivariantMap.subAction (Nat.le_add_left 1 m) Δ

private local instance {m : ℕ} (Δ : Subgroup (PO (m + 1) 1)) :
    ContinuousConstSMul Δ (HUpper (m + 1)) :=
  ⟨fun γ => (HyperbolicAction.contMDiff_po_smul m ∞ (γ : PO (m + 1) 1)).continuous⟩

private local instance {m : ℕ} (Δ : Subgroup (PO (m + 1) 1)) :
    ContMDiffConstSMul 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) ∞ Δ (HUpper (m + 1)) :=
  ⟨fun γ => HyperbolicAction.contMDiff_po_smul m ∞ (γ : PO (m + 1) 1)⟩

variable {Γ : Subgroup (PO (2 + 1) 1)} [DiscreteTopology Γ]
  [IsCancelSMul Γ (HUpper (2 + 1))] {r : ℝ}
  (D : FiniteCuspTruncation (Nat.le_add_left 1 2) Γ r)

local notation "hΓ" => (isDiscrete_iff_discreteTopology.mpr (inferInstance : DiscreteTopology Γ))
local notation "QΓ" => MulAction.orbitRel.Quotient Γ (HUpper (2 + 1))
local notation "πΓ" => Quotient.mk (MulAction.orbitRel Γ (HUpper (2 + 1)))
local notation "S" ξ =>
  (Quotient.mk (MulAction.orbitRel
    (endStabilizer (Nat.le_add_left 1 2) Γ (Set.singleton (Subtype.val ξ))) (HUpper (2 + 1)))) ''
      Busemann.horosphere (Subtype.val ξ) (D.level ξ)

private local instance (ξ : D.centers) :
    IsCancelSMul (endStabilizer (Nat.le_add_left 1 2) Γ (Set.singleton ξ.val)) (HUpper (2 + 1)) :=
  EquivariantMap.isCancelSMul_subAction (Nat.le_add_left 1 2)
    (show endStabilizer (Nat.le_add_left 1 2) Γ (Set.singleton ξ.val) ≤ Γ from inf_le_left)

private local instance (ξ : D.centers) : ChartedSpace (Fin 2 → ℝ) (S ξ) :=
  D.horosphereQuotientChartedSpace hΓ ξ

private local instance {H : FiniteVolumeHyperbolicModel} (Tr : HyperbolicTruncation H) :
    BoundarylessManifold Tr.core.model Tr.core.interior :=
  DifferentialGeometry.Manifold.boundarylessManifold_intrinsicInterior Tr.core.model ∞ (by simp)

private local instance {H : FiniteVolumeHyperbolicModel} (Tr : HyperbolicTruncation H) :
    SigmaCompactSpace Tr.core.interior :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen Tr.core.model Tr.core.interior.isOpen)

private theorem exists_diffeomorph_interior_retained_core
    (H : FiniteVolumeHyperbolicModel) (e : QΓ ≃ₜ H.Carrier)
    (he : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (e ∘ πΓ))
    (R : D.centers → ℝ) (hR : ∀ ξ, 0 < R ξ)
    (Tr : HyperbolicTruncation H)
    (hcore : range Tr.inclusion = e '' Topology.cylindricalCore
      (fun ξ => D.horoballCylinderMap hΓ ξ) R) :
    ∃ ψ : Tr.core.interior ≃ₘ⟮Tr.core.model, 𝓡 3⟯ H.Carrier,
      (∀ x, Tr.inclusion x.val ∈ e '' Topology.cylindricalCore
        (fun ξ => D.horoballCylinderMap hΓ ξ) (fun ξ => R ξ / 2) →
          ψ x = Tr.inclusion x.val) ∧
      ∀ y ∈ e '' Topology.cylindricalCore
        (fun ξ => D.horoballCylinderMap hΓ ξ) (fun ξ => R ξ / 2),
          Tr.inclusion ((ψ.symm y).val) = y := by
  let A : Tr.core.interior ≃ₘ⟮Tr.core.model, 𝓡 3⟯
      (⟨interior (range Tr.inclusion), isOpen_interior⟩ : TopologicalSpace.Opens H.Carrier) :=
    Tr.embedding.interiorDiffeomorph rfl
  have hA (x : Tr.core.interior) : (A x).val = Tr.inclusion x.val :=
    Tr.embedding.interiorDiffeomorph_apply_val rfl x
  have hAi (y : (⟨interior (range Tr.inclusion), isOpen_interior⟩ :
      TopologicalSpace.Opens H.Carrier)) : Tr.inclusion ((A.symm y).val) = y.val :=
    Tr.embedding.interiorDiffeomorph_symm_apply rfl y
  have hU : (⟨interior (range Tr.inclusion), isOpen_interior⟩ : TopologicalSpace.Opens H.Carrier) =
      ⟨interior (e '' Topology.cylindricalCore
        (fun ξ => D.horoballCylinderMap hΓ ξ) R), isOpen_interior⟩ := by
    apply SetLike.coe_injective
    exact congrArg interior hcore
  have h := exists_diffeomorph_interior_retained_image D e he R hR
  dsimp only at h
  rw [← hU] at h
  obtain ⟨ψ, hψ, hψi⟩ := h
  refine ⟨A.trans ψ, ?_, ?_⟩
  · intro x hx
    change ψ (A x) = Tr.inclusion x.val
    rw [hψ (A x) (by rw [hA]; exact hx), hA]
  · intro y hy
    change Tr.inclusion ((A.symm (ψ.symm y)).val) = y
    rw [hAi, hψi y hy]

private theorem exists_complete_metric_interior_retained_core
    (H : FiniteVolumeHyperbolicModel) (e : QΓ ≃ₜ H.Carrier)
    (he : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (e ∘ πΓ))
    (R : D.centers → ℝ) (hR : ∀ ξ, 0 < R ξ)
    (Tr : HyperbolicTruncation H)
    (hcore : range Tr.inclusion = e '' Topology.cylindricalCore
      (fun ξ => D.horoballCylinderMap hΓ ξ) R) :
    let _ := DifferentialGeometry.Manifold.interiorChartedSpace Tr.core.model ∞ (M := Tr.core.interior)
    let _ := DifferentialGeometry.Manifold.interiorIsManifold Tr.core.model ∞ (M := Tr.core.interior)
    ∃ ψ : Tr.core.interior ≃ₘ⟮𝓡 3, 𝓡 3⟯ H.Carrier,
      let g := Diffeomorph.pullbackMetric H.metric ψ
      RiemannianMetricComplete g ∧
      hasConstantSectionalCurvature g (-(1 / 4 : ℝ)) ∧
      Integral.Measure.riemannianVolumeMeasure (𝓡 3) Tr.core.interior g univ =
        Integral.Measure.riemannianVolumeMeasure (𝓡 3) H.Carrier H.metric univ ∧
      (∀ x y : Tr.core.interior,
        riemannianEDistOf g x y = riemannianEDistOf H.metric (ψ x) (ψ y)) ∧
      (∀ x, Tr.inclusion x.val ∈ e '' Topology.cylindricalCore
        (fun ξ => D.horoballCylinderMap hΓ ξ) (fun ξ => R ξ / 2) →
          ψ x = Tr.inclusion x.val) ∧
      ∀ y ∈ e '' Topology.cylindricalCore
        (fun ξ => D.horoballCylinderMap hΓ ξ) (fun ξ => R ξ / 2),
          Tr.inclusion ((ψ.symm y).val) = y := by
  obtain ⟨f, hf, hfi⟩ := exists_diffeomorph_interior_retained_core D H e he R hR Tr hcore
  let A := DifferentialGeometry.Manifold.interiorAtlasDiffeomorph Tr.core.model ∞ (M := Tr.core.interior)
  let _ := DifferentialGeometry.Manifold.interiorChartedSpace Tr.core.model ∞ (M := Tr.core.interior)
  let _ := DifferentialGeometry.Manifold.interiorIsManifold Tr.core.model ∞ (M := Tr.core.interior)
  let ψ := A.symm.trans f
  refine ⟨ψ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [Diffeomorph.pullbackMetricCross_eq_pullbackMetric] using
      Geometry.Metric.riemannianMetricComplete_pullbackMetricCross H.complete ψ
  · intro x v w hvw
    rw [Geometry.Riemannian.sectionalCurvature_pullback]
    apply H.curvature
    let L := ψ.mfderivToContinuousLinearEquiv (by simp) x
    have hL : LinearIndependent ℝ (L.toLinearMap ∘ ![v, w]) :=
      hvw.map' L.toLinearMap (LinearMap.ker_eq_bot.mpr L.injective)
    convert hL using 1
    ext i
    fin_cases i <;> rfl
  · let : MeasurableSpace H.Carrier := borel H.Carrier
    let : BorelSpace H.Carrier := ⟨rfl⟩
    let : MeasurableSpace Tr.core.interior := borel Tr.core.interior
    let : BorelSpace Tr.core.interior := ⟨rfl⟩
    rw [Integral.Measure.riemannianVolumeMeasure_pullback]
    exact MeasureTheory.Measure.map_apply_of_aemeasurable ψ.symm.continuous.measurable.aemeasurable
      MeasurableSet.univ |>.trans (by rw [preimage_univ])
  · intro x y
    simpa only [Diffeomorph.pullbackMetricCross_eq_pullbackMetric] using
      Geometry.Metric.edistOf_pullbackMetricCross H.metric ψ x y
  · exact hf
  · exact hfi

theorem exists_hyperbolicTruncation_with_complete_interior_of_translation_lattices
    (H : FiniteVolumeHyperbolicModel) (e : QΓ ≃ₜ H.Carrier)
    (he : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (e ∘ πΓ))
    (hmetric : ∀ (p : HUpper 3) (v w : TangentSpace (𝓡 3) p),
      H.metric.inner ((e ∘ πΓ) p)
        (mfderiv (𝓡 3) (𝓡 3) (e ∘ πΓ) p v)
        (mfderiv (𝓡 3) (𝓡 3) (e ∘ πΓ) p w) =
      4 * Hyperboloid.riemannianMetric.inner ((Hyperboloid.hUpperDiffeomorph 3) p)
        (mfderiv (𝓡 3) (𝓡 3) (Hyperboloid.hUpperDiffeomorph 3) p v)
        (mfderiv (𝓡 3) (𝓡 3) (Hyperboloid.hUpperDiffeomorph 3) p w))
    (a : D.centers → PO 3 1)
    (ha : ∀ ξ, (HyperbolicBoundary.poBoundaryMulAction (Nat.le_add_left 1 2)).smul
      (a ξ) ξ.val = MobiusBoundary.ptInfty)
    (Λ : D.centers → Submodule ℤ (Horizontal 2))
    [∀ ξ, DiscreteTopology (Λ ξ)] [∀ ξ, IsZLattice ℝ (Λ ξ)]
    (hP : ∀ ξ,
      (endStabilizer (Nat.le_add_left 1 2) Γ (Set.singleton ξ.val)).map
          (MulAut.conj (a ξ)).toMonoidHom = TranslationLattices.latticeGroup (Λ ξ))
    (R : D.centers → ℝ) (hR : ∀ ξ, 0 < R ξ) :
    ∃ b : ∀ ξ, Module.Basis (Fin 2) ℤ (Λ ξ),
      ∃ F : ∀ ξ : D.centers, Diffeomorph torusModel 𝓘(ℝ, Fin 2 → ℝ) Torus (S ξ) ∞,
        ∃ hK : IsCompact (e ''
            Topology.cylindricalCore (fun ξ => D.horoballCylinderMap hΓ ξ) R),
          ∃ A : Topology.SmoothBoundaryAtlas (𝓡 3) 3 (e ''
              Topology.cylindricalCore (fun ξ => D.horoballCylinderMap hΓ ξ) R),
            ∃ Tr : HyperbolicTruncation H, ∃ σ : Fin Tr.count ≃ D.centers,
          Tr.core = CompactCarrier.ofBoundaryAtlas A H.orientation hK ∧
          HEq Tr.inclusion
            (⟨Subtype.val, continuous_subtype_val⟩ :
              C((e '' Topology.cylindricalCore
                (fun ξ => D.horoballCylinderMap hΓ ξ) R), H.Carrier)) ∧
          Set.range Tr.inclusion =
              e '' Topology.cylindricalCore (fun ξ => D.horoballCylinderMap hΓ ξ) R ∧
          (∀ (i : Fin Tr.count) (p : CuspHalfSpace), Tr.cuspMap i p =
            e (D.horoballCylinderMap hΓ (σ i)
              (F (σ i) p.1, ⟨R (σ i) + p.2.val 0 / 2,
                add_nonneg (hR (σ i)).le (div_nonneg p.2.property (by norm_num))⟩))) ∧
          (∀ (ξ : D.centers) (t : Fin 2 → ℝ),
            (F ξ (Circle.exp (2 * Real.pi * t 0), Circle.exp (2 * Real.pi * t 1))).val =
              Quotient.mk (MulAction.orbitRel
                (endStabilizer (Nat.le_add_left 1 2) Γ (Set.singleton ξ.val))
                (HUpper (2 + 1)))
                ((HyperbolicAction.poMulAction (Nat.le_add_left 1 2)).smul (a ξ)⁻¹
                  (Horospherical.ofCoords (((b ξ).ofZLatticeBasis ℝ (Λ ξ)).equivFunL.symm t)
                    (Real.exp (Real.log
                      (BusemannCocycle.poConfFactor (Nat.le_add_left 1 2) (a ξ) ξ.val) -
                        D.level ξ)) (Real.exp_pos _)))) ∧
          (∀ (ξ : D.centers) (x : Horizontal 2),
            (F ξ).symm (quotientHorosphereCoordinates
                (endStabilizer (Nat.le_add_left 1 2) Γ (Set.singleton ξ.val))
                ξ.val (D.level ξ) (a ξ) (ha ξ) x) =
              (Circle.exp (2 * Real.pi * ((b ξ).ofZLatticeBasis ℝ (Λ ξ)).equivFunL x 0),
                Circle.exp (2 * Real.pi * ((b ξ).ofZLatticeBasis ℝ (Λ ξ)).equivFunL x 1))) ∧
          (let _ := DifferentialGeometry.Manifold.interiorChartedSpace Tr.core.model ∞ (M := Tr.core.interior)
          let _ := DifferentialGeometry.Manifold.interiorIsManifold Tr.core.model ∞ (M := Tr.core.interior)
          ∃ ψ : Tr.core.interior ≃ₘ⟮𝓡 3, 𝓡 3⟯ H.Carrier,
            let g := Diffeomorph.pullbackMetric H.metric ψ
            RiemannianMetricComplete g ∧
            hasConstantSectionalCurvature g (-(1 / 4 : ℝ)) ∧
            Integral.Measure.riemannianVolumeMeasure (𝓡 3) Tr.core.interior g univ =
              Integral.Measure.riemannianVolumeMeasure (𝓡 3) H.Carrier H.metric univ ∧
            (∀ x y : Tr.core.interior,
              riemannianEDistOf g x y = riemannianEDistOf H.metric (ψ x) (ψ y)) ∧
            (∀ x, Tr.inclusion x.val ∈ e '' Topology.cylindricalCore
              (fun ξ => D.horoballCylinderMap hΓ ξ) (fun ξ => R ξ / 2) →
                ψ x = Tr.inclusion x.val) ∧
            ∀ y ∈ e '' Topology.cylindricalCore
              (fun ξ => D.horoballCylinderMap hΓ ξ) (fun ξ => R ξ / 2),
                Tr.inclusion ((ψ.symm y).val) = y) := by
  obtain ⟨b, F, hK, A, Tr, σ, hcarrier, hinclusion, hcore, hcusp, hF, hFi⟩ :=
    D.exists_hyperbolicTruncation_of_translation_lattices H e he hmetric a ha Λ hP R hR
  exact ⟨b, F, hK, A, Tr, σ, hcarrier, hinclusion, hcore, hcusp, hF, hFi,
    exists_complete_metric_interior_retained_core D H e he R hR Tr hcore⟩

end DifferentialGeometry.CuspTruncation.FiniteCuspTruncation
