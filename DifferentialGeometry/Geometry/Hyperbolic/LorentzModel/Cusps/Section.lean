import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Cusps.CoreBoundary
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Cusps.SmoothGraphChart

noncomputable section

open scoped Manifold ContDiff Topology

private theorem injective_mfderiv_slice_comp
    {E F H H' X Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] [TopologicalSpace H']
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
    [TopologicalSpace X] [ChartedSpace H X] [TopologicalSpace Y] [ChartedSpace H' Y]
    (f : X × ℝ → Y) (hf : IsLocalDiffeomorph (I.prod 𝓘(ℝ, ℝ)) J ∞ f) (c : ℝ) (x : X) :
    Function.Injective (mfderiv I J (fun z => f (z, c)) x) := by
  let s : X → X × ℝ := fun z => (z, c)
  have hs : ContMDiff I (I.prod 𝓘(ℝ, ℝ)) ∞ s := contMDiff_id.prodMk contMDiff_const
  have hsinj : Function.Injective (mfderiv I (I.prod 𝓘(ℝ, ℝ)) s x) := by
    intro v w hvw
    have hc := mfderiv_comp x mdifferentiableAt_fst (hs.mdifferentiableAt (by simp))
    have he : Prod.fst ∘ s = (id : X → X) := rfl
    rw [he, mfderiv_id] at hc
    have hv := congrArg (fun L : E →L[ℝ] E => L v) hc
    have hw := congrArg (fun L : E →L[ℝ] E => L w) hc
    exact hv.trans ((congrArg (mfderiv (I.prod 𝓘(ℝ, ℝ)) I Prod.fst (s x)) hvw).trans hw.symm)
  have hfinj : Function.Injective (mfderiv (I.prod 𝓘(ℝ, ℝ)) J f (s x)) := by
    rw [← hf.mfderivToContinuousLinearEquiv_coe (by simp : (∞ : ℕ∞ω) ≠ 0)]
    exact (hf.mfderivToContinuousLinearEquiv (by simp : (∞ : ℕ∞ω) ≠ 0) (s x)).injective
  change Function.Injective (mfderiv I J (f ∘ s) x)
  rw [mfderiv_comp x (hf.contMDiff.mdifferentiableAt (by simp)) (hs.mdifferentiableAt (by simp))]
  exact hfinj.comp hsinj

namespace DifferentialGeometry.CuspTruncation.FiniteCuspTruncation

open ProjectiveOrthogonalGroup (PO)
open Hyperbolic (HUpper)

variable {n : ℕ} {hn : 1 ≤ n} {Γ : Subgroup (PO n 1)} {r : ℝ}
  (D : FiniteCuspTruncation hn Γ r) (hΓ : IsDiscrete (SetLike.coe Γ)) (ξ : D.centers)

include hΓ in
theorem isCompact_quotient_horosphere_of_compact_core :
    let P := CuspCrossSections.endStabilizer hn Γ (Set.singleton ξ.val)
    letI := EquivariantMap.subAction hn P
    IsCompact ((Quotient.mk (MulAction.orbitRel P (HUpper n))) ''
      Busemann.horosphere ξ.val (D.level ξ)) := by
  let P := CuspCrossSections.endStabilizer hn Γ (Set.singleton ξ.val)
  let _ := EquivariantMap.subAction hn P
  let _ := EquivariantMap.subAction hn Γ
  let S := (Quotient.mk (MulAction.orbitRel P (HUpper n))) '' Busemann.horosphere ξ.val (D.level ξ)
  let C := Topology.cylindricalCore (fun η => D.horoballCylinderMap hΓ η) (fun _ => 0)
  have hC : IsCompact C := by
    dsimp only [C]
    rw [D.cylindricalCore_zero hΓ]
    exact D.isCompact_quotient
  let zero : Set.Ici (0 : ℝ) := ⟨0, by simp⟩
  have hslice : _root_.Topology.IsClosedEmbedding (fun s : S => (s, zero)) :=
    _root_.Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
      (continuous_id.prodMk continuous_const) (fun _ _ h => congrArg Prod.fst h)
      (isClosedMap_prodMk_right zero)
  have he : _root_.Topology.IsClosedEmbedding
      (fun s : S => D.horoballCylinderMap hΓ ξ (s, zero)) :=
    (D.horoballCylinderMap_isClosedEmbedding hΓ ξ).comp hslice
  have hpre : (fun s : S => D.horoballCylinderMap hΓ ξ (s, zero)) ⁻¹' C = Set.univ := by
    apply Set.eq_univ_of_forall
    intro s
    exact (Topology.mem_cylindricalCore_image_iff (fun η => D.horoballCylinderMap hΓ η)
      (fun η => (D.horoballCylinderMap_isClosedEmbedding hΓ η).injective)
      (D.pairwise_disjoint_range_horoballCylinderMap hΓ) (fun _ => 0) ξ (s, zero)).mpr le_rfl
  have hcS : IsCompact (Set.univ : Set S) := hpre ▸ he.isCompact_preimage hC
  exact isCompact_iff_compactSpace.mpr (isCompact_univ_iff.mp hcS)

theorem injective_horoballCylinderMap_slice (d : Set.Ici (0 : ℝ)) :
    let P := CuspCrossSections.endStabilizer hn Γ {ξ.val}
    letI := EquivariantMap.subAction hn P
    Function.Injective (fun s : (Quotient.mk (MulAction.orbitRel P (HUpper n))) ''
      Busemann.horosphere ξ.val (D.level ξ) => D.horoballCylinderMap hΓ ξ (s, d)) := by
  dsimp only
  intro x y hxy
  exact congrArg Prod.fst ((D.horoballCylinderMap_isClosedEmbedding hΓ ξ).injective hxy)

end DifferentialGeometry.CuspTruncation.FiniteCuspTruncation

namespace DifferentialGeometry.CuspTruncation.FiniteCuspTruncation

open ProjectiveOrthogonalGroup (PO)
open Hyperbolic (HUpper)

variable {m : ℕ} {Γ : Subgroup (PO (m + 1) 1)} [DiscreteTopology Γ]
  {r : ℝ} (D : FiniteCuspTruncation (Nat.le_add_left 1 m) Γ r) (ξ : D.centers)

private local instance (Δ : Subgroup (PO (m + 1) 1)) : MulAction Δ (HUpper (m + 1)) :=
  EquivariantMap.subAction (Nat.le_add_left 1 m) Δ

private local instance (Δ : Subgroup (PO (m + 1) 1)) : ContinuousConstSMul Δ (HUpper (m + 1)) :=
  ⟨fun γ => (HyperbolicAction.contMDiff_po_smul m ∞ (γ : PO (m + 1) 1)).continuous⟩

private local instance (Δ : Subgroup (PO (m + 1) 1)) :
    ContMDiffConstSMul 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) ∞ Δ (HUpper (m + 1)) :=
  ⟨fun γ => HyperbolicAction.contMDiff_po_smul m ∞ (γ : PO (m + 1) 1)⟩

variable [IsCancelSMul Γ (HUpper (m + 1))]

local notation "hΓ" => (isDiscrete_iff_discreteTopology.mpr (inferInstance : DiscreteTopology Γ))
local notation "P" => CuspCrossSections.endStabilizer (Nat.le_add_left 1 m) Γ (Set.singleton ξ.val)
local notation "QΓ" => MulAction.orbitRel.Quotient Γ (HUpper (m + 1))
local notation "S" => (Quotient.mk (MulAction.orbitRel P (HUpper (m + 1)))) ''
  Busemann.horosphere ξ.val (D.level ξ)
local notation "I" => 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1)))
local notation "K" => 𝓘(ℝ, Fin m → ℝ)

private local instance : IsCancelSMul P (HUpper (m + 1)) :=
  EquivariantMap.isCancelSMul_subAction (Nat.le_add_left 1 m) (show P ≤ Γ from inf_le_left)

private local instance : ProperlyDiscontinuousSMul Γ (HUpper (m + 1)) :=
  OrbifoldCompactness.properlyDiscontinuous_subAction (Nat.le_add_left 1 m) Γ hΓ

omit [IsCancelSMul Γ (HUpper (m + 1))] in
private theorem slice_eq_graph_chart (d : Set.Ici (0 : ℝ)) (s : S) :
    D.horoballCylinderMap hΓ ξ (s, d) = D.horosphereGraphChart hΓ ξ (s, D.level ξ - d.val) := by
  obtain ⟨s, y, hy, rfl⟩ := s
  rw [D.horoballCylinderMap_apply_mk hΓ ξ y hy d,
    D.horosphereGraphChart_apply_mk hΓ ξ y hy]
  congr 2
  ring

theorem contMDiff_horoballCylinderMap_slice (d : Set.Ici (0 : ℝ)) :
    let _ := D.horosphereQuotientChartedSpace hΓ ξ
    ContMDiff K I ∞ (fun s : S => D.horoballCylinderMap hΓ ξ (s, d)) := by
  let _ := D.horosphereQuotientChartedSpace hΓ ξ
  have hs : ContMDiff K ((K).prod 𝓘(ℝ, ℝ)) ∞ (fun s : S => (s, D.level ξ - d.val)) :=
    contMDiff_id.prodMk contMDiff_const
  have h := (D.isLocalDiffeomorph_horosphereGraphChart ξ).contMDiff.comp hs
  exact h.congr (fun s => slice_eq_graph_chart D ξ d s)

theorem injective_mfderiv_horoballCylinderMap_slice (d : Set.Ici (0 : ℝ)) :
    let _ := D.horosphereQuotientChartedSpace hΓ ξ
    ∀ s : S, Function.Injective
      (mfderiv K I (fun t : S => D.horoballCylinderMap hΓ ξ (t, d)) s) := by
  let _ := D.horosphereQuotientChartedSpace hΓ ξ
  dsimp only
  intro s
  have he : (fun t : S => D.horoballCylinderMap hΓ ξ (t, d)) =
      (fun t : S => D.horosphereGraphChart hΓ ξ (t, D.level ξ - d.val)) :=
    funext (slice_eq_graph_chart D ξ d)
  rw [he]
  exact injective_mfderiv_slice_comp (D.horosphereGraphChart hΓ ξ)
    (D.isLocalDiffeomorph_horosphereGraphChart ξ) (D.level ξ - d.val) s

theorem pathConnectedSpace_quotient_horosphere : PathConnectedSpace S := by
  let _ := D.horosphereQuotientChartedSpace hΓ ξ
  let _ : LocallyPathConnectedSpace S := ChartedSpace.locallyPathConnectedSpace (Fin m → ℝ) S
  let _ : ConnectedSpace S := isConnected_iff_connectedSpace.mp (D.isConnected_quotient_horosphere ξ)
  exact PathConnectedSpace.of_locallyPathConnectedSpace

omit [IsCancelSMul Γ (HUpper (m + 1))] in
theorem height_horoballCylinderMap_slice (d : Set.Ici (0 : ℝ)) (hd : 0 < d.val)
    (height : QΓ → ℝ)
    (htie : ∀ z : HUpper (m + 1), Busemann.busemann ξ.val z < D.level ξ →
      height (Quotient.mk (MulAction.orbitRel Γ (HUpper (m + 1))) z) =
        2 * Busemann.busemann ξ.val z)
    (s : S) : height (D.horoballCylinderMap hΓ ξ (s, d)) = 2 * (D.level ξ - d.val) := by
  obtain ⟨s, z, hz, rfl⟩ := s
  have hlevel : Busemann.busemann ξ.val z = D.level ξ := hz
  have hinside : Busemann.busemann ξ.val (AsymptoticRays.rayTo z ξ.val d.val) < D.level ξ := by
    rw [HorosphereProjection.busemann_rayTo, hlevel]
    linarith
  rw [D.horoballCylinderMap_apply_mk hΓ ξ z hz d, htie _ hinside,
    HorosphereProjection.busemann_rayTo, hlevel]

end DifferentialGeometry.CuspTruncation.FiniteCuspTruncation
