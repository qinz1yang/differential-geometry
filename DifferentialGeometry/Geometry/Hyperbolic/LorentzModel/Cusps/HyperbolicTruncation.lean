import DifferentialGeometry.Geometry.Hyperbolic.Truncation
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Cusps.RetainedCore
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Cusps.OutwardMap
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Cusps.Metric
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Cusps.Torus

noncomputable section

open scoped Manifold ContDiff

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

private theorem exists_hyperbolicTruncation_of_horoball_cylinders
    (H : FiniteVolumeHyperbolicModel) (e : QΓ ≃ₜ H.Carrier)
    (he : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (e ∘ πΓ))
    (hmetric : ∀ (p : HUpper 3) (v w : TangentSpace (𝓡 3) p),
      H.metric.inner ((e ∘ πΓ) p)
        (mfderiv (𝓡 3) (𝓡 3) (e ∘ πΓ) p v)
        (mfderiv (𝓡 3) (𝓡 3) (e ∘ πΓ) p w) =
      4 * Hyperboloid.riemannianMetric.inner ((Hyperboloid.hUpperDiffeomorph 3) p)
        (mfderiv (𝓡 3) (𝓡 3) (Hyperboloid.hUpperDiffeomorph 3) p v)
        (mfderiv (𝓡 3) (𝓡 3) (Hyperboloid.hUpperDiffeomorph 3) p w))
    (F : ∀ ξ : D.centers, Diffeomorph torusModel 𝓘(ℝ, Fin 2 → ℝ) Torus (S ξ) ∞)
    (a : D.centers → PO 3 1)
    (ha : ∀ ξ, (HyperbolicBoundary.poBoundaryMulAction (Nat.le_add_left 1 2)).smul
      (a ξ) ξ.val = MobiusBoundary.ptInfty)
    {n : ℕ} (σ : Fin n ≃ D.centers) (R : D.centers → ℝ) (hR : ∀ ξ, 0 < R ξ) :
    ∃ Tr : HyperbolicTruncation H, ∃ hn : Tr.count = n,
      Set.range Tr.inclusion =
        e '' Topology.cylindricalCore (fun ξ => D.horoballCylinderMap hΓ ξ) R ∧
      (∀ (i : Fin n) (p : CuspHalfSpace),
        Tr.cuspMap (Fin.cast hn.symm i) p =
          D.outwardCuspMap hΓ e σ (fun ξ => (F ξ).toHomeomorph) R
            (fun ξ => (hR ξ).le) i p) ∧
      ∃ (hK : IsCompact (e '' Topology.cylindricalCore
          (fun ξ => D.horoballCylinderMap hΓ ξ) R))
        (A : Topology.SmoothBoundaryAtlas (𝓡 3) 3
          (e '' Topology.cylindricalCore (fun ξ => D.horoballCylinderMap hΓ ξ) R)),
        Tr.core = CompactCarrier.ofBoundaryAtlas A H.orientation hK ∧
        HEq Tr.inclusion (⟨Subtype.val, continuous_subtype_val⟩ :
          C((e '' Topology.cylindricalCore (fun ξ => D.horoballCylinderMap hΓ ξ) R),
            H.Carrier)) := by
  classical
  obtain ⟨hK, A, hA, T, hT, hzero, _⟩ :=
    D.exists_boundaryTori_cylindricalCore_image H.orientation e he F σ R hR
  let K := e '' Topology.cylindricalCore (fun ξ => D.horoballCylinderMap hΓ ξ) R
  let C := CompactCarrier.ofBoundaryAtlas A H.orientation hK
  let _ := C.charts
  let _ := C.smooth
  let f := D.outwardCuspMap hΓ e σ (fun ξ => (F ξ).toHomeomorph) R
    (fun ξ => (hR ξ).le)
  choose cusp htorus hwarped using fun i : Fin n =>
    D.exists_hyperbolicCusp_horoballCylinderMap_at_depth (σ i)
      H e he hmetric (F (σ i)) (a (σ i)) (ha (σ i)) (R (σ i)) (hR (σ i))
  let inclusion : C(C.Carrier, H.Carrier) := ⟨Subtype.val, continuous_subtype_val⟩
  have hrange : Set.range inclusion = K := Subtype.range_coe
  let Tr : HyperbolicTruncation H :=
    { core := C
      connected := isConnected_iff_connectedSpace.mp
        (D.isConnected_image_cylindricalCore hΓ e R (fun ξ => (hR ξ).le))
      inclusion := inclusion
      embedding := CompactCarrier.ofBoundaryAtlas_isSmoothEmbedding A H.orientation hK
      interior_image := by
        change IsOpen (Subtype.val '' ((𝓡∂ 3).interior K))
        rw [A.image_interior_subtype_val hA]
        exact isOpen_interior
      count := n
      boundary := T
      boundary_exhausted := hT
      cusp := cusp
      cuspMap := fun i => f i
      cuspEmbedding := fun i =>
        D.isSmoothEmbedding_horoballCylinderMap_at_depth (σ i) e he
          (F (σ i)) (R (σ i)) (hR (σ i))
      cuspIsometry := hwarped
      cusp_zero := by
        intro i x
        change f i (x, halfZero) = (T.torusMap i x).val
        rw [hzero]
        exact D.outwardCuspMap_zero hΓ e σ (fun ξ => (F ξ).toHomeomorph)
          R (fun ξ => (hR ξ).le) i x
      cusp_disjoint := D.pairwise_disjoint_range_outwardCuspMap hΓ e σ
        (fun ξ => (F ξ).toHomeomorph) R (fun ξ => (hR ξ).le)
      intersection := by
        intro i
        rw [hrange]
        exact D.core_inter_range_outwardCuspMap hΓ e σ
          (fun ξ => (F ξ).toHomeomorph) R (fun ξ => (hR ξ).le) i
      exhausts := by
        rw [hrange]
        exact D.core_union_range_outwardCuspMap hΓ e σ
          (fun ξ => (F ξ).toHomeomorph) R (fun ξ => (hR ξ).le) }
  exact ⟨Tr, rfl, hrange, (fun _ _ => rfl), hK, A, rfl, HEq.rfl⟩

theorem exists_hyperbolicTruncation_of_translation_lattices
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
                Circle.exp (2 * Real.pi * ((b ξ).ofZLatticeBasis ℝ (Λ ξ)).equivFunL x 1))) := by
  classical
  choose b F hF hFi using fun ξ : D.centers =>
    D.exists_horosphere_torus_diffeomorph_of_translation_lattice
      ξ (a ξ) (ha ξ) (Λ ξ) (hP ξ)
  let _ : Finite D.centers := D.finite_centers
  let _ := Fintype.ofFinite D.centers
  let σ : Fin (Fintype.card D.centers) ≃ D.centers := (Fintype.equivFin D.centers).symm
  obtain ⟨Tr, hn, hcore, hcusp, hK, A, hcarrier, hinclusion⟩ :=
    D.exists_hyperbolicTruncation_of_horoball_cylinders H e he hmetric F a ha σ R hR
  refine ⟨b, F, hK, A, Tr, (finCongr hn).trans σ, hcarrier, hinclusion, hcore, ?_, hF, hFi⟩
  intro i p
  have h := hcusp (Fin.cast hn i) p
  have hcast : Fin.cast hn.symm (Fin.cast hn i) = i := Fin.ext rfl
  rw [hcast] at h
  exact h

end DifferentialGeometry.CuspTruncation.FiniteCuspTruncation
